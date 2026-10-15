/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Reduction

/-!
# PoS-NSB: chain growth, chain quality and common prefix with high probability

The PoS-NSB port proves chain growth (`chain_growth_gen`), chain quality (`chain_quality_gen`)
and common prefix (`timed_common_prefix_gen`) for every execution whose lottery satisfies slot
conditions, under the hypotheses that the adversary forges no honest block (`forging_free`) and
that the broadcast blocks have distinct hashes (`collision_free`). This file combines

1. `prob_slotBad_le` (`Prob/Slots.lean`): the random lottery violates the slot conditions with
   probability at most `slotBound`, a sum of Chernoff-Hoeffding tails over the intervals;
2. `prob_ROCollision_le` (`Prob/Hash.lean`): the random oracle has a collision among the first
   `q` queries with probability at most the birthday bound `q (q - 1) / 2 / |Hash|`;
3. `prob_forge_le` (`Prob/Reduction.lean`): the adversary forges an honest block with
   probability at most `∑ᵢ eufAdv (forger P A ν W K i)`, the EUF-CMA advantages of explicit
   adversaries against the signature scheme,

into the statement that chain growth, chain quality and common prefix hold for the first `K`
phases of the real execution except with probability at most the sum of the three terms
(`pos_nsb_security`).

## Hypotheses

* `ProtocolHyp P`: the initial parties are distinct, the lottery map satisfies `LotteryHyp`,
  every tree type follows the longest-chain rule, and the genesis block is honest, of slot at
  most `1`.
* `hTree`: the tree type `Tree` of the honest tree chain follows the longest-chain rule.
* Numbers: `1 ≤ d`, `w ≤ d`, `W + d ≤ n` (the slots from `W` on are honest padding),
  `K + 2 ≤ n` and `K + 1 ≤ Hz` (the first `K` phases stay within slot `K + 1`), and the
  conditions on `ν` of `prob_slotBad_le`.
* `hRO` (random-oracle model): for every seed, the genesis block and the broadcast blocks of the
  first `K` phases of the real execution are among the first `q` queries of the querier
  `next ω.κ ω.ks` to the random oracle `ω.f`.

## Main results

* `good_of_not_bad`: the deterministic step: outside the bad events the three properties hold.
* `pos_nsb_security`: the probability bound.
* `instance_hyps`: a concrete instance (one honest party, no adversarial slots, a trivial
  signature scheme and adversary) satisfying all hypotheses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open scoped ENNReal

section Combine

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {Sch : SigScheme (Block Tx Hash (Fin np))}
  (P : Protocol Tx Hash np) (A : Adversary Tx Hash np n Hz Sch)

/-- The hypotheses on the protocol. -/
structure ProtocolHyp (P : Protocol Tx Hash np) : Prop where
  /-- The initial parties are distinct. -/
  nodup : P.IP.Nodup
  /-- The lottery map has one honest leader in honest slots and corrupt leaders only in
  adversarial slots. -/
  lottery : LotteryHyp P.IP P.lot
  /-- Every tree type follows the longest-chain rule. -/
  longest : ∀ (Pa : Parameters (Fin np)) (Ba : BlockParameters Tx Hash (Fin np)) (p : Fin np),
    letI := Pa; letI := Ba; (P.trees Pa Ba p).LongestChainRule
  /-- The genesis block is honest. -/
  genesis_honest : honest_block P.GB = true
  /-- The genesis block has slot at most `1`. -/
  genesis_slot : P.GB.sl ≤ 1

/-- The tree types of the honest tree chain, for every lottery and hash function. -/
abbrev TreeFamily (Tx Hash : Type) (np : ℕ) :=
  (Pa : Parameters (Fin np)) → (Ba : BlockParameters Tx Hash (Fin np)) →
    @TreeType Tx Hash (Fin np) Pa Ba

variable (Tree : TreeFamily Tx Hash np) (ν : PMF SlotKind) (K d w : ℕ) (ε : ℝ)

/-- **Chain growth** for the first `K` phases of the real execution: from a state at the start
of a slot to a later state at least `d` slots later, the honest tree chain grows by every
`w'` with `w' ≤ (pH - ε) Δt`, where `Δt` is the number of slots in between. -/
def CGGood (ω : Seed Tx Hash np n Hz Sch) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  ∀ j1 j2, j1 ≤ j2 → j2 ≤ K → (sTrace P ω A false j1).progress = .Ready →
    (sTrace P ω A false j1).t_now + d ≤ (sTrace P ω A false j2).t_now →
    ∀ w' : ℕ, (w' : ℝ) ≤ (pH ν - ε) *
        (((sTrace P ω A false j2).t_now - (sTrace P ω A false j1).t_now : ℕ) : ℝ) →
      (honest_tree_chain (Tree (ω.params P) (ω.bparams P)) (sTrace P ω A false j1)).length + w' ≤
        (honest_tree_chain (Tree (ω.params P) (ω.bparams P)) (sTrace P ω A false j2)).length

/-- **Chain quality** for the first `K` phases of the real execution: a fragment
`b_j :: c ++ [b_i]` of the chain of an honest party with `sl b_i + 1 + d ≤ sl b_j` contains at
least `w - 1` honest blocks. -/
def CQGood (ω : Seed Tx Hash np n Hz Sch) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  ∀ j ≤ K, ∀ (p : Fin np) (l : LocalState Tx Hash (Fin np)),
    (sTrace P ω A false j).state_map p = some l → is_honest p = true →
    ∀ (b_j b_i : Block Tx Hash (Fin np)) (c : Chain Tx Hash (Fin np)),
      fragment ([b_j] ++ c ++ [b_i]) (l.tT.bestChain ((sTrace P ω A false j).t_now - 1) l.tree) →
      b_i.sl + 1 + d ≤ b_j.sl → w - 1 ≤ (honest_blocks ([b_j] ++ c ++ [b_i])).length

/-- **Common prefix** for the first `K` phases of the real execution: for honest parties `p1`
in phase `j1` and `p2` in a later phase `j2`, and a slot `k` at least `d` slots before the
current slot of phase `j1`, the blocks of slots at most `k` of the chain of `p1` form a suffix of
the chain of `p2`. -/
def CPGood (ω : Seed Tx Hash np n Hz Sch) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  ∀ j1 j2 (k : ℕ), j1 ≤ j2 → j2 ≤ K → k + d ≤ (sTrace P ω A false j1).t_now →
    ∀ (p1 p2 : Fin np) (l1 l2 : LocalState Tx Hash (Fin np)),
      is_honest p1 = true → is_honest p2 = true →
      (sTrace P ω A false j1).state_map p1 = some l1 →
      (sTrace P ω A false j2).state_map p2 = some l2 →
      prune_time k (l1.tT.bestChain ((sTrace P ω A false j1).t_now - 1) l1.tree) <:+
        l2.tT.bestChain ((sTrace P ω A false j2).t_now - 1) l2.tree

/-- The three properties. -/
def Good (ω : Seed Tx Hash np n Hz Sch) : Prop :=
  CGGood P A Tree ν K d ε ω ∧ CQGood P A K d w ω ∧ CPGood P A K d ω

theorem sTrace_t_now (ω : Seed Tx Hash np n Hz Sch) (ideal : Bool) (j : ℕ) :
    (letI := ω.params P; letI := ω.bparams P; (sTrace P ω A ideal j).t_now) ≤ j + 1 := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec ideal P ω A
  exact runTrace_t_now (Tx := Tx) (Hash := Hash) (Party := Fin np) (AdvState := A.AdvState) j

/-- **Chain growth from the slot condition.** -/
theorem cg_of_not_bad (hP : ProtocolHyp P)
    (hTree : ∀ (Pa : Parameters (Fin np)) (Ba : BlockParameters Tx Hash (Fin np)),
      letI := Pa; letI := Ba; (Tree Pa Ba).LongestChainRule)
    (ω : Seed Tx Hash np n Hz Sch) (hn : K + 2 ≤ n) (hCG : ¬CGBad ν n d ε ω.κ) :
    CGGood P A Tree ν K d ε ω := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  intro j1 j2 hj hj2 hready hdt w' hw'
  have ht2 := sTrace_t_now P A ω false j2
  have hcnt : (pH ν - ε) * (((sTrace P ω A false j2).t_now - (sTrace P ω A false j1).t_now : ℕ) : ℝ)
      ≤ cnt ω.κ .honest (sTrace P ω A false j1).t_now (sTrace P ω A false j2).t_now := by
    by_contra hc
    exact hCG ⟨_, _, by omega, hdt, lt_of_not_ge hc⟩
  refine chain_growth_gen hP.nodup (hTree _ _) (fun p => hP.longest _ _ p) (honestKind ω.κ)
    (lucky_of_kind ω.κ hP.lottery) w' (reach_runTrace j1) (runTrace_reach hj) hready ?_
  rw [honest_count ω.κ _ _ (by omega)]
  exact_mod_cast hw'.trans hcnt

/-- **Chain quality from the slot condition**, in the absence of forgeries and collisions. -/
theorem cq_of_not_bad (hP : ProtocolHyp P) (ω : Seed Tx Hash np n Hz Sch) {W : ℕ}
    (hpad : PaddedFrom W ω.κ) (hWn : W + d ≤ n) (hd : 1 ≤ d) (hwd : w ≤ d)
    (hCQ : ¬CQBad n d w ω.κ) (hforge : ¬Forge P ω A K)
    (hcf : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      collision_free (sTrace P ω A false j)) :
    CQGood P A K d w ω := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec true P ω A
  intro j hj p l hl hh b_j b_i c hfrag hsl
  have heq := sTrace_ideal_eq P ω A hforge j hj
  rw [← heq] at hl hfrag
  have hcf' := hcf j hj
  rw [← heq] at hcf'
  exact chain_quality_gen hP.nodup (fun p => hP.longest _ _ p) hP.genesis_honest (honestKind ω.κ)
    (lucky_of_kind ω.κ hP.lottery) (advKind ω.κ) (adv_of_winner ω.κ hP.lottery)
    (reach_runTrace j) (forging_free_ideal P ω A _) hcf' hl hh hfrag
    (honest_advantage_of_not_CQBad hpad hWn hd (by omega) hwd hCQ)

/-- One more slot at the end of a range adds at most two slots in two steps. -/
theorem p_slots_range_sub_two (Q : ℕ → Bool) (a b : ℕ) (hb : 2 ≤ b) :
    (p_slots_range Q a b).length ≤ (p_slots_range Q a (b - 2)).length + 2 := by
  have h1 := p_slots_range_succ_le Q a (b - 2)
  have h2 := p_slots_range_succ_le Q a (b - 2 + 1)
  rw [show b - 2 + 1 + 1 = b by omega] at h2
  omega

/-- **Common prefix from the slot condition**, in the absence of forgeries and collisions. -/
theorem cp_of_not_bad (hP : ProtocolHyp P) (ω : Seed Tx Hash np n Hz Sch) (hn : K + 2 ≤ n)
    (hd : 1 ≤ d) (hCP : ¬CPBad n d ω.κ) (hforge : ¬Forge P ω A K)
    (hcf : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      collision_free (sTrace P ω A false j)) :
    CPGood P A K d ω := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec true P ω A
  intro j1 j2 k hj hj2 hk p1 p2 l1 l2 hh1 hh2 hl1 hl2
  have heq1 := sTrace_ideal_eq P ω A hforge j1 (by omega)
  have heq2 := sTrace_ideal_eq P ω A hforge j2 hj2
  rw [← heq1] at hk hl1 ⊢
  rw [← heq2] at hl2 ⊢
  have hcf' := hcf j2 hj2
  rw [← heq2] at hcf'
  have ht2 := sTrace_t_now P A ω true j2
  rcases timed_common_prefix_gen hP.nodup (fun p => hP.longest _ _ p) hP.genesis_honest
      (honestKind ω.κ) (super_of_kind ω.κ hP.lottery) (advKind ω.κ) (adv_of_winner ω.κ hP.lottery)
      k (reach_runTrace j1) (runTrace_reach hj) (forging_free_ideal P ω A _) hcf' hh1 hh2 hl1 hl2
    with h | ⟨t1, t2, h1, h2, h3, h4⟩
  · exact h
  · exfalso
    have hgood : 2 * cnt ω.κ .adversarial (t1 + 1) (t2 + 1) + 3 ≤
        cnt ω.κ .honest (t1 + 1) (t2 + 1) := by
      by_contra hc
      exact hCP ⟨t1 + 1, t2 + 1, by simp only [sTrace] at h3 ht2; omega,
        by simp only [sTrace] at h2 hk; omega, by omega⟩
    have h5 := p_slots_range_sub_two (honestKind ω.κ) (t1 + 1) (t2 + 1)
      (by simp only [sTrace] at h2 hk; omega)
    rw [show t2 + 1 - 2 = t2 - 1 by omega, honest_count ω.κ _ _ (by simp only [sTrace] at h3 ht2; omega)] at h5
    rw [adv_count ω.κ _ _ (by simp only [sTrace] at h3 ht2; omega)] at h4
    omega

/-- **Collision freedom from the random oracle.** If the genesis block and the broadcast
blocks of the first `K` phases of the real execution are among the first `q` queries of a
querier to `ω.f`, and these queries have no collision, the hash function `b ↦ ω.f (encB b)` is
injective on the genesis block and the broadcast blocks of every state of the first `K`
phases. -/
theorem cf_of_not_collision (hP : ProtocolHyp P) (ω : Seed Tx Hash np n Hz Sch)
    (hHz : K + 1 ≤ Hz) (q : ℕ) (next : Querier (BlockDom Tx Hash np Hz) Hash)
    (hq : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      ∀ b ∈ block_hist_gb (sTrace P ω A false j), ∃ k < q, query next ω.f k = encB Hz b)
    (hcol : ¬ROCollision next q ω.f) :
    ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P; collision_free (sTrace P ω A false j) := by
  let _ := ω.params P; let _ := ω.bparams P
  intro j hj b hb b' hb' hh
  have hsl : ∀ b'' ∈ block_hist_gb (sTrace P ω A false j), b''.sl ≤ Hz := by
    intro b'' hb''
    rcases List.mem_cons.1 hb'' with rfl | hm
    · have := hP.genesis_slot; simp only [GenesisBlock]; omega
    · simp only [block_history] at hm
      obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hm
      have := sTrace_slots P ω A j m hm'
      have := sTrace_t_now P A ω false j
      omega
  obtain ⟨k, hk, hqk⟩ := hq j hj b hb
  obtain ⟨k', hk', hqk'⟩ := hq j hj b' hb'
  refine encB_inj (hsl b hb) (hsl b' hb') ?_
  by_contra hne
  exact hcol ⟨k, hk, k', hk', by rw [hqk, hqk']; exact hne, by rw [hqk, hqk']; exact hh⟩

/-- **The deterministic step.** Outside the bad events (slot conditions violated, a string not
padded with honest slots, a random-oracle collision, a forgery), chain growth, chain quality
and common prefix hold for the first `K` phases of the real execution. -/
theorem good_of_not_bad (hP : ProtocolHyp P)
    (hTree : ∀ (Pa : Parameters (Fin np)) (Ba : BlockParameters Tx Hash (Fin np)),
      letI := Pa; letI := Ba; (Tree Pa Ba).LongestChainRule)
    (ω : Seed Tx Hash np n Hz Sch) {W : ℕ} (hd : 1 ≤ d) (hwd : w ≤ d) (hWn : W + d ≤ n)
    (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz) (q : ℕ) (next : Querier (BlockDom Tx Hash np Hz) Hash)
    (hq : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      ∀ b ∈ block_hist_gb (sTrace P ω A false j), ∃ k < q, query next ω.f k = encB Hz b)
    (hslot : ¬SlotBad ν n d w ε ω.κ) (hpad : PaddedFrom W ω.κ)
    (hcol : ¬ROCollision next q ω.f) (hforge : ¬Forge P ω A K) :
    Good P A Tree ν K d w ε ω := by
  simp only [SlotBad, not_or] at hslot
  have hcf := cf_of_not_collision P A K hP ω hHz q next hq hcol
  exact ⟨cg_of_not_bad P A Tree ν K d ε hP hTree ω hn hslot.1,
    cq_of_not_bad P A K d w hP ω hpad hWn hd hwd hslot.2.1 hforge hcf,
    cp_of_not_bad P A K d hP ω hn hd hslot.2.2 hforge hcf⟩

end Combine

end CatCryptCore.Consensus.PoSNSB

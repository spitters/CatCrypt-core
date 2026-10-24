/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Collision
public import CatCryptCore.Consensus.PoSNSB.ChainQualityTip

/-!
# PoS-NSB: chain growth, chain quality and common prefix with high probability

The PoS-NSB port proves chain growth (`chain_growth_gen`), chain quality (`chain_quality_gen`),
common prefix (`timed_common_prefix_gen`) and an honest block near the tip (`honest_tip_gen`)
for every execution whose lottery satisfies slot conditions, under the hypotheses that the
adversary forges no honest block (`forging_free`) and that the broadcast blocks have distinct
hashes (`collision_free`). For a keyed hash family `H` (`HashScheme`) with a codec `cd` of the
block domain and a deterministic signature scheme `Sch` (`PSigScheme`), this file combines

1. `prob_slotBad_le` (`Prob/Slots.lean`): the random lottery, which elects the leader of each
   slot independently from `μ`, violates the slot conditions with probability at most
   `slotBound (kindLaw μ)`, a sum of Chernoff-Hoeffding tails over the intervals;
2. `prob_collision_le` (`Prob/Collision.lean`): some state of the first `K` phases is not
   collision free with probability at most `CR_Search_Advantage H (collFinder Sch P A H cd μ W K)`,
   the collision-resistance advantage of an explicit adversary against `H`;
3. `prob_forge_le` (`Prob/Reduction.lean`): the adversary forges an honest block with
   probability at most
   `∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger Sch P A H cd μ W K i))`, the
   EUF-CMA advantages of explicit adversaries against the signature scheme,

into the statement that chain growth, chain quality, common prefix and the honest tip hold for
the first `K` phases of the real execution except with probability at most the sum `posFail`
of the three terms (`pos_nsb_security`).

## Hypotheses

* `ProtocolHyp P`: the initial parties are distinct and contain every honest party, the padding
  leader `P.h0` is honest (`LeaderHyp`), every tree type follows the longest-chain rule, and the
  genesis block is honest, of slot at most `1`.
* `hTree`: the tree type `Tree` of the honest tree chain follows the longest-chain rule.
* Numbers: `w ≤ d`, `W + d ≤ n` (the slots from `W` on are honest padding), `K + 2 ≤ n` and
  `K + 1 ≤ Hz` (the first `K` phases stay within slot `K + 1`), and the conditions on the
  slot-kind distribution `kindLaw μ` of `prob_slotBad_le`, which give `3 ≤ d`.

The adversary carries no hypothesis. The hash function enters through the collision-resistance
advantage of the explicit finder `collFinder Sch P A H cd μ W K` (Thomsen and Spitters, CSF
2021, Remark 1); for the random function `HashScheme.randomFun`,
`collFinder_advantage_randomFun_le` bounds it by the birthday bound.

## Main results

* `tip_of_not_bad`: outside the common-prefix bad event, the chain of every honest party
  contains an honest block within `d + 2` slots of the current slot.
* `good_of_not_bad`: the deterministic step: outside the bad events the four properties hold.
* `posFail`, `pos_nsb_security`: the failure bound and the probability bound.
* `instance_hyps`: a concrete instance (one honest party, no adversarial slots, a trivial
  signature scheme and adversary) satisfying all hypotheses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open scoped ENNReal

section Combine

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] (A : Adversary Tx Hash np n Hz PK Sig)

/-- The hypotheses on the protocol. -/
structure ProtocolHyp (P : Protocol Tx Hash np n Hz) : Prop where
  /-- The initial parties are distinct. -/
  nodup : P.IP.Nodup
  /-- Every honest party is an initial party, and the padding leader is honest. -/
  leader : LeaderHyp P.IP P.h0
  /-- Every tree type follows the longest-chain rule. -/
  longest : ∀ (L : Fin n → Option (Fin np)) (f : BlockDom Tx Hash np Hz → Hash) (p : Fin np),
    letI := leaderParams P.IP P.h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨P.GB, fun b => f (encB Hz b)⟩
    (P.trees L f p).LongestChainRule
  /-- The genesis block is honest. -/
  genesis_honest : honest_block P.GB = true
  /-- The genesis block has slot at most `1`. -/
  genesis_slot : P.GB.sl ≤ 1

/-- The tree types of the honest tree chain, for every leader string and every random
oracle. -/
abbrev TreeFamily (P : Protocol Tx Hash np n Hz) :=
  (L : Fin n → Option (Fin np)) → (f : BlockDom Tx Hash np Hz → Hash) →
    @TreeType Tx Hash (Fin np) (leaderParams P.IP P.h0 L) ⟨P.GB, fun b => f (encB Hz b)⟩

/-- The tree types of the honest tree chain follow the longest-chain rule. -/
def TreeFamily.Longest {P : Protocol Tx Hash np n Hz} (Tree : TreeFamily P) : Prop :=
  ∀ (L : Fin n → Option (Fin np)) (f : BlockDom Tx Hash np Hz → Hash),
    letI := leaderParams P.IP P.h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨P.GB, fun b => f (encB Hz b)⟩
    (Tree L f).LongestChainRule

variable (Tree : TreeFamily P) (ν : PMF SlotKind) (K d w : ℕ) (ε : ℝ)

/-- **Chain growth** for the first `K` phases of the real execution: from a state at the start
of a slot to a later state at least `d` slots later, the honest tree chain grows by every
`w'` with `w' ≤ (pH - ε) Δt`, where `Δt` is the number of slots in between. -/
def CGGood (ω : Seed Tx Hash np n Hz PK SK) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  ∀ j1 j2, j1 ≤ j2 → j2 ≤ K → (sTrace Sch P ω A false j1).progress = .Ready →
    (sTrace Sch P ω A false j1).t_now + d ≤ (sTrace Sch P ω A false j2).t_now →
    ∀ w' : ℕ, (w' : ℝ) ≤ (pH ν - ε) *
        (((sTrace Sch P ω A false j2).t_now - (sTrace Sch P ω A false j1).t_now : ℕ) : ℝ) →
      (honest_tree_chain (Tree ω.L ω.f) (sTrace Sch P ω A false j1)).length + w' ≤
        (honest_tree_chain (Tree ω.L ω.f) (sTrace Sch P ω A false j2)).length

/-- **Chain quality** for the first `K` phases of the real execution: a fragment
`b_j :: c ++ [b_i]` of the chain of an honest party with `sl b_i + 1 + d ≤ sl b_j` contains at
least `w - 1` honest blocks. -/
def CQGood (ω : Seed Tx Hash np n Hz PK SK) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  ∀ j ≤ K, ∀ (p : Fin np) (l : LocalState Tx Hash (Fin np)),
    (sTrace Sch P ω A false j).state_map p = some l → is_honest p = true →
    ∀ (b_j b_i : Block Tx Hash (Fin np)) (c : Chain Tx Hash (Fin np)),
      fragment ([b_j] ++ c ++ [b_i]) (l.tT.bestChain ((sTrace Sch P ω A false j).t_now - 1) l.tree) →
      b_i.sl + 1 + d ≤ b_j.sl → w - 1 ≤ (honest_blocks ([b_j] ++ c ++ [b_i])).length

/-- **Common prefix** for the first `K` phases of the real execution: for honest parties `p1`
in phase `j1` and `p2` in a later phase `j2`, and a slot `k` at least `d` slots before the
current slot of phase `j1`, the blocks of slots at most `k` of the chain of `p1` form a suffix of
the chain of `p2`. -/
def CPGood (ω : Seed Tx Hash np n Hz PK SK) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  ∀ j1 j2 (k : ℕ), j1 ≤ j2 → j2 ≤ K → k + d ≤ (sTrace Sch P ω A false j1).t_now →
    ∀ (p1 p2 : Fin np) (l1 l2 : LocalState Tx Hash (Fin np)),
      is_honest p1 = true → is_honest p2 = true →
      (sTrace Sch P ω A false j1).state_map p1 = some l1 →
      (sTrace Sch P ω A false j2).state_map p2 = some l2 →
      prune_time k (l1.tT.bestChain ((sTrace Sch P ω A false j1).t_now - 1) l1.tree) <:+
        l2.tT.bestChain ((sTrace Sch P ω A false j2).t_now - 1) l2.tree

/-- **An honest block near the tip** for the first `K` phases of the real execution: the chain
of every honest party contains an honest block `b` with `t < sl b + d + 2`, where `t` is the
current slot. -/
def TipGood (ω : Seed Tx Hash np n Hz PK SK) : Prop :=
  letI := ω.params P; letI := ω.bparams P
  ∀ j ≤ K, ∀ (p : Fin np) (l : LocalState Tx Hash (Fin np)),
    (sTrace Sch P ω A false j).state_map p = some l → is_honest p = true →
    ∃ b ∈ l.tT.bestChain ((sTrace Sch P ω A false j).t_now - 1) l.tree, honest_block b = true ∧
      (sTrace Sch P ω A false j).t_now < b.sl + d + 2

/-- The four properties: chain growth, chain quality, common prefix and an honest block near
the tip. -/
def Good (ω : Seed Tx Hash np n Hz PK SK) : Prop :=
  CGGood P Sch A Tree ν K d ε ω ∧ CQGood P Sch A K d w ω ∧ CPGood P Sch A K d ω ∧ TipGood P Sch A K d ω

theorem sTrace_t_now (ω : Seed Tx Hash np n Hz PK SK) (ideal : Bool) (j : ℕ) :
    (letI := ω.params P; letI := ω.bparams P; (sTrace Sch P ω A ideal j).t_now) ≤ j + 1 := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch ideal P ω A
  exact runTrace_t_now (Tx := Tx) (Hash := Hash) (Party := Fin np) (AdvState := A.AdvState) j

/-- **Chain growth from the slot condition.** -/
theorem cg_of_not_bad (hP : ProtocolHyp P)
    (hTree : Tree.Longest)
    (ω : Seed Tx Hash np n Hz PK SK) (hn : K + 2 ≤ n) (hCG : ¬CGBad ν n d ε ω.κ) :
    CGGood P Sch A Tree ν K d ε ω := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch false P ω A
  intro j1 j2 hj hj2 hready hdt w' hw'
  have ht2 := sTrace_t_now P Sch A ω false j2
  have hcnt : (pH ν - ε) * (((sTrace Sch P ω A false j2).t_now - (sTrace Sch P ω A false j1).t_now : ℕ) : ℝ)
      ≤ cnt ω.κ .honest (sTrace Sch P ω A false j1).t_now (sTrace Sch P ω A false j2).t_now := by
    by_contra hc
    exact hCG ⟨_, _, by omega, hdt, lt_of_not_ge hc⟩
  refine chain_growth_gen hP.nodup (hTree _ _) (fun p => hP.longest _ _ p) (honestKind ω.κ)
    (lucky_of_kind ω.L hP.nodup hP.leader) w' (reach_runTrace j1) (runTrace_reach hj) hready ?_
  rw [honest_count ω.κ _ _ (by omega)]
  exact_mod_cast hw'.trans hcnt

/-- **Chain quality from the slot condition**, in the absence of forgeries and collisions. -/
theorem cq_of_not_bad (hP : ProtocolHyp P) (ω : Seed Tx Hash np n Hz PK SK) {W : ℕ}
    (hpad : PaddedFrom W ω.κ) (hWn : W + d ≤ n) (hd : 1 ≤ d) (hwd : w ≤ d)
    (hCQ : ¬CQBad n d w ω.κ) (hforge : ¬Forge Sch P ω A K)
    (hcf : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      collision_free (sTrace Sch P ω A false j)) :
    CQGood P Sch A K d w ω := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch true P ω A
  intro j hj p l hl hh b_j b_i c hfrag hsl
  have heq := sTrace_ideal_eq Sch P ω A hforge j hj
  rw [← heq] at hl hfrag
  have hcf' := hcf j hj
  rw [← heq] at hcf'
  exact chain_quality_gen hP.nodup (fun p => hP.longest _ _ p) hP.genesis_honest (honestKind ω.κ)
    (lucky_of_kind ω.L hP.nodup hP.leader) (advKind ω.κ) (adv_of_winner ω.L hP.leader)
    (reach_runTrace j) (forging_free_ideal Sch P ω A _) hcf' hl hh hfrag
    (honest_advantage_of_not_CQBad hpad hWn hd (by omega) hwd hCQ)

/-- One more slot at the end of a range adds at most two slots in two steps. -/
theorem p_slots_range_sub_two (Q : ℕ → Bool) (a b : ℕ) (hb : 2 ≤ b) :
    (p_slots_range Q a b).length ≤ (p_slots_range Q a (b - 2)).length + 2 := by
  have h1 := p_slots_range_succ_le Q a (b - 2)
  have h2 := p_slots_range_succ_le Q a (b - 2 + 1)
  rw [show b - 2 + 1 + 1 = b by omega] at h2
  omega

/-- **Common prefix from the slot condition**, in the absence of forgeries and collisions. -/
theorem cp_of_not_bad (hP : ProtocolHyp P) (ω : Seed Tx Hash np n Hz PK SK) (hn : K + 2 ≤ n)
    (hd : 1 ≤ d) (hCP : ¬CPBad n d ω.κ) (hforge : ¬Forge Sch P ω A K)
    (hcf : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      collision_free (sTrace Sch P ω A false j)) :
    CPGood P Sch A K d ω := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch true P ω A
  intro j1 j2 k hj hj2 hk p1 p2 l1 l2 hh1 hh2 hl1 hl2
  have heq1 := sTrace_ideal_eq Sch P ω A hforge j1 (by omega)
  have heq2 := sTrace_ideal_eq Sch P ω A hforge j2 hj2
  rw [← heq1] at hk hl1 ⊢
  rw [← heq2] at hl2 ⊢
  have hcf' := hcf j2 hj2
  rw [← heq2] at hcf'
  have ht2 := sTrace_t_now P Sch A ω true j2
  rcases timed_common_prefix_gen hP.nodup (fun p => hP.longest _ _ p) hP.genesis_honest
      (honestKind ω.κ) (super_of_kind ω.L hP.nodup hP.leader) (advKind ω.κ)
      (adv_of_winner ω.L hP.leader)
      k (reach_runTrace j1) (runTrace_reach hj) (forging_free_ideal Sch P ω A _) hcf' hh1 hh2 hl1 hl2
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

/-- Outside the common-prefix bad event, every interval of at least `d` slots within the first
`n` slots has at least `3` more honest than adversarial slots. -/
theorem not_CQBad_three_of_not_CPBad {d : ℕ} {κ : Fin n → SlotKind} (h : ¬CPBad n d κ) :
    ¬CQBad n d 3 κ :=
  fun ⟨a, b, hb, hab, hlt⟩ => h ⟨a, b, hb, hab, by omega⟩

/-- **An honest block near the tip from the slot condition**, in the absence of forgeries and
collisions. -/
theorem tip_of_not_bad (hP : ProtocolHyp P) (ω : Seed Tx Hash np n Hz PK SK) {W : ℕ}
    (hpad : PaddedFrom W ω.κ) (hWn : W + d ≤ n) (hd3 : 3 ≤ d)
    (hCP : ¬CPBad n d ω.κ) (hforge : ¬Forge Sch P ω A K)
    (hcf : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      collision_free (sTrace Sch P ω A false j)) :
    TipGood P Sch A K d ω := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch true P ω A
  intro j hj p l hl hh
  have heq := sTrace_ideal_eq Sch P ω A hforge j hj
  rw [← heq] at hl ⊢
  have hcf' := hcf j hj
  rw [← heq] at hcf'
  exact honest_tip_gen hP.nodup (fun p => hP.longest _ _ p) hP.genesis_honest (honestKind ω.κ)
    (lucky_of_kind ω.L hP.nodup hP.leader) (advKind ω.κ) (adv_of_winner ω.L hP.leader)
    (reach_runTrace j) (forging_free_ideal Sch P ω A _) hcf' hl hh (by norm_num)
    (honest_advantage_of_not_CQBad hpad hWn (by omega) le_rfl hd3
      (not_CQBad_three_of_not_CPBad hCP))

/-- **The deterministic step.** Outside the bad events (slot conditions violated, a string not
padded with honest slots, a state of the first `K` phases that is not collision free, a
forgery), chain growth, chain quality, common prefix and the honest tip hold for the first `K`
phases of the real execution. -/
theorem good_of_not_bad (hP : ProtocolHyp P)
    (hTree : Tree.Longest)
    (ω : Seed Tx Hash np n Hz PK SK) {W : ℕ} (hd3 : 3 ≤ d) (hwd : w ≤ d) (hWn : W + d ≤ n)
    (hn : K + 2 ≤ n)
    (hslot : ¬SlotBad ν n d w ε ω.κ) (hpad : PaddedFrom W ω.κ)
    (hcf : ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      collision_free (sTrace Sch P ω A false j))
    (hforge : ¬Forge Sch P ω A K) :
    Good P Sch A Tree ν K d w ε ω := by
  simp only [SlotBad, not_or] at hslot
  exact ⟨cg_of_not_bad P Sch A Tree ν K d ε hP hTree ω hn hslot.1,
    cq_of_not_bad P Sch A K d w hP ω hpad hWn (by omega) hwd hslot.2.1 hforge hcf,
    cp_of_not_bad P Sch A K d hP ω hn (by omega) hslot.2.2 hforge hcf,
    tip_of_not_bad P Sch A K d hP ω hpad hWn hd3 hslot.2.2 hforge hcf⟩

end Combine

/-! ## The probability bound -/

/-- If every branch of a bind gives an event probability at most `c`, so does the bind. -/
theorem PMF.toOuterMeasure_bind_le {α β : Type*} (p : PMF α) (f : α → PMF β) (s : Set β)
    (c : ℝ≥0∞) (h : ∀ a, (f a).toOuterMeasure s ≤ c) : (p.bind f).toOuterMeasure s ≤ c := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (f a).toOuterMeasure s ≤ ∑' a, p a * c :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _
    _ = c := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

section Bound

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}

/-- An event on the slot kinds has the same probability under `seedDist Sch H cd μ h0` as
under `kindDist (kindLaw μ)`, for an honest padding leader `h0`. -/
theorem seedDist_kind (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
    (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash) (μ : PMF (Option (Fin np)))
    {h0 : Fin np} (hh0 : is_honest h0 = true) (W : ℕ) (E : Set (Fin n → SlotKind)) :
    (seedDist Sch H cd μ h0 W n).toOuterMeasure {ω | ω.κ ∈ E} =
      (kindDist (kindLaw μ) W n).toOuterMeasure E := by
  have : (seedDist Sch H cd μ h0 W n).map Seed.κ = kindDist (kindLaw μ) W n := by
    rw [← leaderDist_map_kinds μ hh0 W n]
    simp only [seedDist, PMF.map_bind, PMF.pure_map, Seed.κ, PMF.bind_const]
    rfl
  rw [← this, PMF.toOuterMeasure_map_apply]
  rfl

/-- The slot kinds from `W` on are honest almost surely. -/
theorem kindDist_padded (ν : PMF SlotKind) (W : ℕ) :
    (kindDist ν W n).toOuterMeasure {κ | ¬PaddedFrom W κ} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro κ hκ hnot
  apply hnot
  intro i hi
  rw [PMF.mem_support_iff, kindDist, PMF.piFin_apply, Finset.prod_ne_zero_iff] at hκ
  have := hκ i (Finset.mem_univ _)
  simp only [slotDist, ite_eq_right (not_lt.2 hi), PMF.pure_apply] at this
  by_contra h
  exact this (ite_eq_right h)

/-- The common-prefix condition `3 ≤ d (pH - 2 pA)` forces `3 ≤ d`. -/
theorem three_le_of_cp (ν : PMF SlotKind) {d : ℕ} (h3 : (3 : ℝ) ≤ d * (pH ν - 2 * pA ν)) :
    3 ≤ d := by
  have hpH : pH ν ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one ν _)
  have hpA : 0 ≤ pA ν := ENNReal.toReal_nonneg
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : (3 : ℝ) ≤ d := by nlinarith
  exact_mod_cast this

variable (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] (A : Adversary Tx Hash np n Hz PK Sig) (Tree : TreeFamily P)

/-- **The failure bound of PoS-NSB**: the Chernoff-Hoeffding bound `slotBound` on the slot
conditions, the collision-resistance advantage against the keyed hash family `H` of the
explicit collision finder `collFinder Sch P A H cd μ W K`, and the sum over the parties `i` of
the EUF-CMA advantages against `Sch` of the explicit forgers
`toEUFAdversary (forger Sch P A H cd μ W K i)`. -/
noncomputable def posFail (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  slotBound (kindLaw μ) n d w ε + CR_Search_Advantage H (collFinder Sch P A H cd μ W K) +
    ∑ i : Fin np,
      eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger Sch P A H cd μ W K i))

/-- **Security of PoS-NSB with signed blocks.** Let the slot leaders of the first `W` slots be
elected independently from `μ` (for the stake-weighted election `stakeElect`, a slot is honest
with probability `φ` times the honest stake fraction, `kindLaw_stakeElect_honest`), let the
hash function be `cd.hashOn k` for a uniform key `k` of the keyed family `H`, and let the
blocks be signed with the deterministic signature scheme `Sch`. Under the hypotheses on the
protocol, the slot-kind distribution `kindLaw μ` and the numbers, chain growth, chain quality,
common prefix and the honest tip hold for the first `K` phases of the real execution except
with probability at most `posFail P Sch A H cd μ W K d w ε`:
`slotBound (kindLaw μ) n d w ε + CR_Search_Advantage H (collFinder …) +
∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger … i))`. -/
theorem pos_nsb_security (hP : ProtocolHyp P)
    (hTree : Tree.Longest) (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ))) :
    (seedDist Sch H cd μ P.h0 W n).toOuterMeasure
        {ω | ¬Good P Sch A Tree (kindLaw μ) K d w ε ω} ≤
      posFail P Sch A H cd μ W K d w ε := by
  unfold posFail
  have hd3 := three_le_of_cp (kindLaw μ) h3
  have hsub : {ω | ¬Good P Sch A Tree (kindLaw μ) K d w ε ω} ⊆
      (({ω | ω.κ ∈ {κ | SlotBad (kindLaw μ) n d w ε κ}} ∪
        {ω | ω.κ ∈ {κ | ¬PaddedFrom W κ}}) ∪
        {ω : Seed Tx Hash np n Hz PK SK | ∃ j ≤ K, letI := ω.params P; letI := ω.bparams P;
          ¬collision_free (sTrace Sch P ω A false j)}) ∪
        {ω | Forge Sch P ω A K} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hc
    obtain ⟨⟨⟨hslot, hpad⟩, hcol⟩, hforge⟩ := hc
    exact hω (good_of_not_bad P Sch A Tree (kindLaw μ) K d w ε hP hTree ω hd3 hwd hWn hn hslot
      (not_not.1 hpad) (fun j hj => by_contra fun h => hcol ⟨j, hj, h⟩) hforge)
  refine (MeasureTheory.OuterMeasure.mono _ hsub).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans
    (add_le_add ?_ (prob_forge_le Sch P A H cd μ W K))
  refine (MeasureTheory.measure_union_le _ _).trans
    (add_le_add ?_ (prob_collision_le Sch P A H cd μ W K hHz hP.genesis_slot))
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  rw [seedDist_kind Sch H cd μ hP.leader.h0_honest, seedDist_kind Sch H cd μ hP.leader.h0_honest,
    kindDist_padded, add_zero]
  exact prob_slotBad_le (kindLaw μ) W n d w hε hγ hw h3

end Bound

/-! ## A tree type with the longest-chain rule -/

section LongestTree

variable {Tx Hash Party : Type} [Parameters Party] [BlockParameters Tx Hash Party]

/-- A valid chain of blocks of `t` with slots at most `s`. -/
def Cand (t : List (Block Tx Hash Party)) (s : Slot) (c : Chain Tx Hash Party) : Prop :=
  valid_chain c ∧ ∀ b ∈ c, b ∈ t ∧ b.sl ≤ s

theorem Cand.length_le {t : List (Block Tx Hash Party)} {s : Slot} {c : Chain Tx Hash Party}
    (h : Cand t s c) : c.length ≤ t.length := by
  have hnd : c.Nodup := h.1.2.2.imp fun hlt heq => by subst heq; exact lt_irrefl _ hlt
  exact (hnd.subperm fun b hb => (h.2 b hb).1).length_le

open Classical in
/-- The length of a longest valid chain of blocks of `t` with slots at most `s`. -/
noncomputable def bestLen (t : List (Block Tx Hash Party)) (s : Slot) : ℕ :=
  Nat.findGreatest (fun k => ∃ c, Cand t s c ∧ c.length = k) t.length

theorem exists_best (hGB : valid_chain [(GenesisBlock : Block Tx Hash Party)])
    (hsl : (GenesisBlock : Block Tx Hash Party).sl = 0) (t : List (Block Tx Hash Party))
    (ht : GenesisBlock ∈ t) (s : Slot) : ∃ c, Cand t s c ∧ c.length = bestLen t s := by
  classical
  have h1 : ∃ c, Cand t s c ∧ c.length = 1 :=
    ⟨[GenesisBlock], ⟨hGB, by simp [ht, hsl]⟩, rfl⟩
  exact Nat.findGreatest_spec (P := fun k => ∃ c, Cand t s c ∧ c.length = k)
    (List.length_pos_of_mem ht) h1

/-- The tree type whose trees are lists of blocks containing the genesis block and whose
chain-selection rule picks a longest valid chain of blocks of the tree with slots at most
`s`. -/
noncomputable def longestTree (hGB : valid_chain [(GenesisBlock : Block Tx Hash Party)])
    (hsl : (GenesisBlock : Block Tx Hash Party).sl = 0) : TreeType Tx Hash Party where
  T := {t : List (Block Tx Hash Party) // GenesisBlock ∈ t}
  extendTree t b := ⟨t.1 ++ [b], List.mem_append_left _ t.2⟩
  bestChain s t := Classical.choose (exists_best hGB hsl t.1 t.2 s)
  allBlocks t := t.1
  tree0 := ⟨[GenesisBlock], List.mem_singleton_self _⟩
  all_tree0 _ := Iff.rfl
  all_extend _ _ _ := Iff.rfl
  best_chain_valid t s := (Classical.choose_spec (exists_best hGB hsl t.1 t.2 s)).1.1
  best_chain_in_all s t b hb := by
    have := (Classical.choose_spec (exists_best hGB hsl t.1 t.2 s)).1.2 b hb
    exact List.mem_filter.2 ⟨this.1, decide_eq_true this.2⟩

/-- `longestTree` follows the longest-chain rule. -/
theorem longestTree_longest (hGB : valid_chain [(GenesisBlock : Block Tx Hash Party)])
    (hsl : (GenesisBlock : Block Tx Hash Party).sl = 0) :
    (longestTree hGB hsl).LongestChainRule := by
  classical
  intro c s t hc hall
  have hcand : Cand t.1 s c := ⟨hc, fun b hb => by
    have := List.mem_filter.1 (hall b hb)
    exact ⟨this.1, by simpa using this.2⟩⟩
  show c.length ≤ (Classical.choose (exists_best hGB hsl t.1 t.2 s)).length
  rw [(Classical.choose_spec (exists_best hGB hsl t.1 t.2 s)).2]
  exact Nat.le_findGreatest hcand.length_le ⟨c, hcand, rfl⟩

end LongestTree

/-! ## A concrete instance -/

namespace Instance

/-- The single party is honest. -/
@[instance_reducible] def corruption : Corruption (Fin 1) := ⟨fun _ => .Honest⟩

attribute [local instance] corruption

/-- The genesis block: slot `0`, baked by the single party. -/
def GB : Block Unit Unit (Fin 1) := ⟨0, (), (), 0⟩

theorem gb_valid (L : Fin 4 → Option (Fin 1)) (f : BlockDom Unit Unit 1 1 → Unit) :
    letI := leaderParams [0] 0 L
    letI : BlockParameters Unit Unit (Fin 1) := ⟨GB, fun b => f (encB 1 b)⟩
    valid_chain [(GenesisBlock : Block Unit Unit (Fin 1))] := by
  refine ⟨?_, rfl, List.pairwise_singleton _ _⟩
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  rfl

/-- The protocol: one party, the longest-chain tree type, `4` slots of lottery and the random
oracle on blocks of slots at most `1`. -/
noncomputable def P : Protocol Unit Unit 1 4 1 where
  IP := [0]
  h0 := 0
  GB := GB
  trees L f _ :=
    letI := leaderParams [0] 0 L
    letI : BlockParameters Unit Unit (Fin 1) := ⟨GB, fun b => f (encB 1 b)⟩
    longestTree (gb_valid L f) rfl
  txSel _ _ := ()

/-- The honest tree chain is selected by the longest-chain tree type. -/
noncomputable def Tree : TreeFamily P := fun L f =>
  letI := leaderParams [0] 0 L
  letI : BlockParameters Unit Unit (Fin 1) := ⟨GB, fun b => f (encB 1 b)⟩
  longestTree (gb_valid L f) rfl

/-- A signature scheme with trivial keys and signatures. -/
noncomputable def Sch : PSigScheme (Block Unit Unit (Fin 1)) Unit Unit Unit where
  KR := Unit
  keygen _ := ((), ())
  sign _ _ := PMF.pure ()
  verify _ _ _ := true

/-- Signing of `Sch` is the point mass at `()`. -/
noncomputable instance : Sch.Deterministic := ⟨fun _ _ => (), fun _ _ => rfl⟩

/-- The adversary that sends no message. -/
def A : Adversary Unit Unit 1 4 1 Unit Unit where
  AdvState := Unit
  st0 := ()
  bake _ _ _ _ _ st := ([], st)
  rcv _ _ _ _ _ _ st := ([], st)

/-- The single party leads every slot. -/
noncomputable def μ : PMF (Option (Fin 1)) := PMF.pure (some 0)

/-- The slot kinds of the election `μ`: every slot is honest. -/
noncomputable def ν : PMF SlotKind := kindLaw μ

/-- The random function on the blocks of the instance. -/
noncomputable abbrev H : HashScheme := HashScheme.randomFun (BlockDom Unit Unit 1 1) Unit

/-- The identity codec of `H`. -/
noncomputable abbrev cd : H.Codec (BlockDom Unit Unit 1 1) Unit := HashScheme.Codec.id H

theorem ν_eq : ν = PMF.pure .honest := by
  simp only [ν, kindLaw, μ, PMF.pure_map]
  rfl

theorem pH_ν : pH ν = 1 := by simp [pH, ν_eq]

theorem pA_ν : pA ν = 0 := by simp [pA, ν_eq]

/-- **Non-vacuity.** The hypotheses of `pos_nsb_security` hold for the instance with
`W = 1`, `K = 0`, `d = 3`, `w = 1` and `ε = 0`. -/
theorem instance_hyps :
    ProtocolHyp P ∧ Tree.Longest ∧ 1 ≤ 3 ∧ 1 + 3 ≤ 4 ∧ 0 + 2 ≤ 4 ∧ 0 + 1 ≤ 1 ∧
      (0 : ℝ) ≤ 0 ∧ 2 * pA ν ≤ pH ν ∧ ((1 : ℕ) : ℝ) ≤ (3 : ℕ) * (pH ν - pA ν) ∧
      (3 : ℝ) ≤ (3 : ℕ) * (pH ν - 2 * pA ν) := by
  have hcor : ∀ p : Fin 1, is_corrupt p = false := fun _ => rfl
  exact ⟨⟨by simp [P], ⟨fun p _ => by simp [P, Fin.fin_one_eq_zero p], rfl⟩,
    fun L f _ =>
      letI := leaderParams [0] 0 L
      letI : BlockParameters Unit Unit (Fin 1) := ⟨GB, fun b => f (encB 1 b)⟩
      longestTree_longest (gb_valid L f) rfl, by decide, by decide⟩,
    fun L f =>
      letI := leaderParams [0] 0 L
      letI : BlockParameters Unit Unit (Fin 1) := ⟨GB, fun b => f (encB 1 b)⟩
      longestTree_longest (gb_valid L f) rfl, by norm_num, by norm_num, by norm_num,
    by norm_num, le_rfl, by rw [pH_ν, pA_ν]; norm_num, by rw [pH_ν, pA_ν]; norm_num,
    by rw [pH_ν, pA_ν]; norm_num⟩

/-- **The instance of the security theorem.** For the instance with the random function `H`,
chain growth, chain quality, common prefix and the honest tip fail with probability at most
`posFail P Sch A H cd μ 1 0 3 1 0`. -/
theorem instance_security :
    (seedDist Sch H cd μ P.h0 1 4).toOuterMeasure {ω | ¬Good P Sch A Tree ν 0 3 1 0 ω} ≤
      posFail P Sch A H cd μ 1 0 3 1 0 := by
  obtain ⟨hP, hT, hwd, hWn, hn, hHz, hε, hγ, hw, h3⟩ := instance_hyps
  exact pos_nsb_security P Sch A Tree hP hT H cd μ 1 0 3 1 0 hwd hWn hn hHz hε hγ hw h3

end Instance

end CatCryptCore.Consensus.PoSNSB

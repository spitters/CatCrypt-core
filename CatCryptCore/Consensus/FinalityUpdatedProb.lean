/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.FinalityUpdated
public import CatCryptCore.Consensus.PoSNSB.Prob

/-!
# Δ-updatedness of Casper FFG over PoS-NSB, with high probability

This file runs the finality layer of `CatCryptCore.Consensus.FinalityUpdated` on the real
execution of PoS-NSB (`CatCryptCore.Consensus.PoSNSB.Prob`) and bounds the probability that
Δ-updatedness fails by the failure bound of `PoSNSB.pos_nsb_security`:

  `slotBound (kindLaw μ) n d w ε + crAdv (collFinder P A H μ W K) + ∑ᵢ eufAdv (forger P A H μ W K i)`,

the Chernoff-Hoeffding bound on the slot conditions, the collision-resistance advantage of the
explicit collision finder `collFinder P A H μ W K` against the keyed hash family `H`, and the
EUF-CMA advantages of the explicit forgers `forger P A H μ W K i` built from the adversary `A`.
The only numeric term is the information-theoretic slot bound; the hash family and the
signature scheme enter through the advantages of explicit adversaries.

## The execution seen by the finality layer

For a seed `ω`, phase `j` of the real execution is `sTrace P ω A false j`:

* `seedNow P A ω j` is its slot `t_now`;
* `seedChain P A ω j p` is the chain that party `p` selects, `bestChain (t_now - 1)` of its
  block tree, and `[]` if `p` has no local state;
* `seedTrace P A K ω` regards a party as honest if it is honest for the corruption map and has
  a local state at every phase up to `K`;
* `seedTree P ω` is the ancestor relation of predecessor hashes under the hash function of `ω`,
  with genesis `P.GB`.

## What is derived and what is assumed

From the event `PoSNSB.Good` (`seed_slotChainHyp`): the monotone clock, chains ordered by
`seedTree` with strictly decreasing slots and containing genesis (from `best_chain_valid`), and
common prefix by slots (`PoSNSB.CPGood`, which is exactly `ChainTrace.SlotCommonPrefix`).
The tip condition (`ChainTrace.SlotTip` with window `σ ≥ d + 2`: the chain of every honest
party has a block in the last `σ` slots) follows from `PoSNSB.TipGood` (`seed_slotTip`), and
chain growth in slot form (`ChainTrace.SlotChainGrowth` with window `σ`) follows from the tip
condition and chain quality `PoSNSB.CQGood` (`seed_slotChainGrowth`): an empty window of
`σ ≥ d` slots would give a fragment of two blocks spanning more than `d + 1` slots, which has
fewer than `w - 1 ≥ 3` honest blocks.

Assumed explicitly in `finality_updated_prob`:

* `hGB : P.GB.sl = 0`: the genesis block has slot `0` (`ProtocolHyp` gives `≤ 1`);
* `hw4 : 4 ≤ w` and `hσd : d + 2 ≤ σ`;
* `hvote`: on every seed, the vote layer (votes cast and received, the honest schedule, and
  the history before it) satisfies `VoteHyp`. PoS-NSB carries no FFG votes, so the vote layer
  is an additional component of the execution, given as functions of the seed.
* `hτ₀`: the honest schedule starts at the earliest slot `τ₀ = (e₀ + 1) E + σ + d`.

## Main results

* `properly_linked_pairwise`: a properly linked chain is ordered by the ancestor relation of
  predecessor hashes.
* `seed_slotChainHyp`: on the event `CPGood`, given slot chain growth and `P.GB.sl = 0`, the
  traces of PoS-NSB satisfy `SlotChainHyp` up to phase `K`.
* `seed_slotTip`: the tip condition with window `σ ≥ d + 2` from `TipGood`.
* `seed_slotChainGrowth`: slot chain growth from `CQGood`, `w ≥ 4`, `σ ≥ d` and the tip
  condition.
* `finality_updated_prob`: Δ-updatedness with lag `3 E + σ + d + Δ` fails with probability at
  most the failure bound of `pos_nsb_security`.
* `seedTrace_honest_of_init`: an honest initial party has a local state at every phase.
* `seed_genesis_checkpoint`: the genesis checkpoint is the epoch-`0` boundary checkpoint of
  every honest chain.
* `finality_updated_prob_genesis`: the same bound when the finality layer starts at genesis
  (no earlier votes, the genesis checkpoint, the honest initial parties `honestInit P`, rounds
  at the phases `genesisRound E σ d r`); the hypotheses on the history before the start are
  derived, and the remaining vote-layer hypotheses are the stake quorum, an honest initial
  party, honest casting of the schedule, delivery within `Δ` after `GST ≤ 2 E + σ + d`,
  `1 ≤ E` and `1 ≤ Δ`. Δ-updatedness with lag `3 E + σ + d + Δ` holds from slot
  `2 E + σ + d + Δ`.
* `Instance.prob_hyps`: the hypotheses of `finality_updated_prob` hold for the concrete
  instance `PoSNSB.Instance` (horizon `K = 0`).
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.Finality

open FFG CatCryptCore.Consensus.PoSNSB
open Parameters BlockParameters Corruption Execution
open scoped ENNReal

/-! ### Properly linked chains -/

section Linked

variable {Tx Hash Party : Type} [BlockParameters Tx Hash Party]

/-- A properly linked chain is ordered by the ancestor relation of predecessor hashes: every
block is reached from every older block of the chain by following predecessor links. -/
theorem properly_linked_pairwise :
    ∀ {c : Chain Tx Hash Party}, properly_linked c →
      c.Pairwise fun b b' => Relation.ReflTransGen (fun x y => linked y x) b' b
  | [], h => h.elim
  | [_], _ => List.pairwise_singleton _ _
  | b :: b' :: bs, h => by
    obtain ⟨hl, h'⟩ := h
    have ih := properly_linked_pairwise h'
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    have step : Relation.ReflTransGen (fun x y => linked y x) b' b :=
      Relation.ReflTransGen.single hl
    rcases List.mem_cons.1 hx with rfl | hx
    · exact step
    · exact (List.rel_of_pairwise_cons ih hx).trans step

end Linked

/-! ### Gaps in chains with decreasing slots -/

/-- In a list whose `f`-values strictly decrease, if some element has `f`-value above `a` and
some element has `f`-value at most `a`, then two adjacent elements `x, y` cross `a`:
`a < f x` and `f y ≤ a`. -/
theorem exists_adjacent_cross {α : Type*} (f : α → ℕ) (a : ℕ) :
    ∀ {L : List α}, L.Pairwise (fun x y => f y < f x) → (∃ x ∈ L, a < f x) →
      (∃ y ∈ L, f y ≤ a) → ∃ s₁ s₃ x y, s₁ ++ [x, y] ++ s₃ = L ∧ a < f x ∧ f y ≤ a
  | [], _, ⟨_, hx, _⟩, _ => absurd hx List.not_mem_nil
  | [b], _, ⟨x, hx, hax⟩, ⟨y, hy, hya⟩ => by
    rw [List.mem_singleton] at hx hy
    subst hx hy
    omega
  | b :: c :: rest, hP, ⟨x, hx, hax⟩, ⟨y, hy, hya⟩ => by
    have hb : a < f b := by
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hax
      · have := List.rel_of_pairwise_cons hP hx'
        omega
    by_cases hc : f c ≤ a
    · exact ⟨[], rest, b, c, rfl, hb, hc⟩
    · have hy' : y ∈ c :: rest := by
        rcases List.mem_cons.1 hy with rfl | hy'
        · omega
        · exact hy'
      obtain ⟨s₁, s₃, x', y', h, h1, h2⟩ :=
        exists_adjacent_cross f a (List.pairwise_cons.1 hP).2
          ⟨c, List.mem_cons_self, by omega⟩ ⟨y, hy', hya⟩
      exact ⟨b :: s₁, s₃, x', y', by rw [← h]; rfl, h1, h2⟩

/-- The tip condition with window `σ`, up to phase `hz`: for honest `p` and phases `j ≤ hz`,
the chain of `p` at `j` contains a block of slot above `now j - σ`. -/
def ChainTrace.SlotTip {Party Blk : Type*} (X : ChainTrace Party Blk) (now : ℕ → ℕ)
    (slot : Blk → ℕ) (σ hz : ℕ) : Prop :=
  ∀ p j, X.honest p → j ≤ hz → ∃ b ∈ X.chain j p, now j < slot b + σ

/-! ### The execution of a seed -/

section Seed

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {Sch : SigScheme (Block Tx Hash (Fin np))}
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz Sch)

/-- The slot of phase `j` of the real execution of `ω`. -/
def seedNow (ω : Seed Tx Hash np n Hz Sch) (j : ℕ) : ℕ :=
  letI := ω.params P; letI := ω.bparams P
  (sTrace P ω A false j).t_now

/-- The chain that party `p` selects at phase `j` of the real execution of `ω`: the best chain
of its block tree up to the previous slot, or `[]` if `p` has no local state. -/
def seedChain (ω : Seed Tx Hash np n Hz Sch) (j : ℕ) (p : Fin np) : Chain Tx Hash (Fin np) :=
  letI := ω.params P; letI := ω.bparams P
  match (sTrace P ω A false j).state_map p with
  | some l => l.tT.bestChain ((sTrace P ω A false j).t_now - 1) l.tree
  | none => []

/-- The real execution of `ω` seen through the chain-selection rule, up to phase `K`: a party
counts as honest if it is honest and has a local state at every phase up to `K`. -/
def seedTrace (K : ℕ) (ω : Seed Tx Hash np n Hz Sch) : ChainTrace (Fin np) (Block Tx Hash (Fin np)) where
  honest p := is_honest p = true ∧
    ∀ j ≤ K, (letI := ω.params P; letI := ω.bparams P; (sTrace P ω A false j).state_map p).isSome
  chain := seedChain P A ω

/-- The block tree of a seed: `a` is an ancestor of `b` if `b` reaches `a` by following
predecessor hashes under the hash function of `ω`; genesis is `P.GB`. -/
def seedTree (ω : Seed Tx Hash np n Hz Sch) : BlockTree (Block Tx Hash (Fin np)) where
  anc := Relation.ReflTransGen fun x y => y.pred = ω.f (encB Hz x)
  genesis := P.GB
  anc_refl _ := Relation.ReflTransGen.refl
  anc_trans := Relation.ReflTransGen.trans

variable {P A}

theorem seedChain_valid {ω : Seed Tx Hash np n Hz Sch} {K j : ℕ} {p : Fin np}
    (hp : (seedTrace P A K ω).honest p) (hj : j ≤ K) :
    letI := ω.params P; letI := ω.bparams P; valid_chain (seedChain P A ω j p) := by
  let _ := ω.params P; let _ := ω.bparams P
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (hp.2 j hj)
  simp only [seedChain, hl]
  exact l.tT.best_chain_valid _ _

/-- **The chain hypotheses from `PoSNSB.Good`.** On a seed with common prefix `CPGood` with
parameter `d` up to phase `K`, if the genesis block has slot `0` and chain growth in slot form with window
`σ` holds, the real execution of PoS-NSB satisfies `SlotChainHyp` up to phase `K`. -/
theorem seed_slotChainHyp (hGB : P.GB.sl = 0) {K d σ : ℕ} {ω : Seed Tx Hash np n Hz Sch}
    (hCP : CPGood P A K d ω)
    (hgrowth : (seedTrace P A K ω).SlotChainGrowth (seedNow P A ω) Block.sl σ K) :
    SlotChainHyp (seedTree P ω) (seedTrace P A K ω) (seedNow P A ω) Block.sl d σ K where
  now_mono j j' h := by
    let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
    exact monotone_time (runTrace_reach h)
  inTree j p hp hj := by
    let _ := ω.params P; let _ := ω.bparams P
    exact properly_linked_pairwise (seedChain_valid hp hj).2.1
  decreasing j p hp hj := by
    let _ := ω.params P; let _ := ω.bparams P
    exact (seedChain_valid hp hj).2.2
  genesis_mem j p hp hj := by
    let _ := ω.params P; let _ := ω.bparams P
    exact (valid_chain_suffix_gb (seedChain_valid hp hj)).subset (List.mem_singleton_self _)
  genesis_slot := hGB
  commonPrefix := by
    intro p q j j' s hp hq hjj hj' hs
    let _ := ω.params P; let _ := ω.bparams P
    obtain ⟨l1, hl1⟩ := Option.isSome_iff_exists.1 (hp.2 j (hjj.trans hj'))
    obtain ⟨l2, hl2⟩ := Option.isSome_iff_exists.1 (hq.2 j' hj')
    simp only [seedTrace, seedChain, hl1, hl2]
    exact hCP j j' s hjj hj' hs p q l1 l2 hp.1 hq.1 hl1 hl2
  growth := hgrowth

/-- **Slot chain growth from chain quality.** On a seed with chain quality `CQGood` with
window `d` and quality `w ≥ 4`, if the genesis block has slot `0`, `d ≤ σ`, and the tip
condition with window `σ` holds, then chain growth in slot form with window `σ` holds up to
phase `K`: a window of `σ ≥ d` slots without a block of the chain would make two adjacent
blocks of the chain a fragment spanning more than `d + 1` slots with at most `2 < w - 1`
honest blocks. -/
theorem seed_slotChainGrowth (hGB : P.GB.sl = 0) {K d w σ : ℕ} {ω : Seed Tx Hash np n Hz Sch}
    (hCQ : CQGood P A K d w ω) (hw : 4 ≤ w) (hσ : d ≤ σ)
    (htip : (seedTrace P A K ω).SlotTip (seedNow P A ω) Block.sl σ K) :
    (seedTrace P A K ω).SlotChainGrowth (seedNow P A ω) Block.sl σ K := by
  intro p j a hp hj ha
  let _ := ω.params P; let _ := ω.bparams P
  obtain ⟨b, hb, hbt⟩ := htip p j hp hj
  have hval := seedChain_valid hp hj
  have hgen : P.GB ∈ seedChain P A ω j p :=
    (valid_chain_suffix_gb hval).subset (List.mem_singleton_self _)
  by_contra hno
  have hno' : ∀ z ∈ seedChain P A ω j p, a < z.sl → a + σ < z.sl := fun z hz h1 => by
    by_contra h2
    exact hno ⟨z, hz, h1, by omega⟩
  obtain ⟨s₁, s₃, x, y, hL, hx, hy⟩ := exists_adjacent_cross Block.sl a hval.2.2
    ⟨b, hb, by omega⟩ ⟨P.GB, hgen, by omega⟩
  have hx' := hno' x (by rw [← hL]; simp) hx
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (hp.2 j hj)
  have hfrag : PoSNSB.fragment ([x] ++ [] ++ [y])
      (l.tT.bestChain ((sTrace P ω A false j).t_now - 1) l.tree) :=
    ⟨s₁, s₃, by simpa [seedChain, hl] using hL⟩
  have hq := hCQ j hj p l hl hp.1 x y [] hfrag (by omega)
  have h2 : (honest_blocks ([x] ++ [] ++ [y])).length ≤ 2 :=
    (List.length_filter_le _ _).trans (by simp)
  omega

/-- **The tip condition from `TipGood`.** On a seed where the chain of every honest party
contains an honest block of slot above `t_now - (d + 2)` up to phase `K`, the tip condition
with window `σ ≥ d + 2` holds up to phase `K`. -/
theorem seed_slotTip {K d σ : ℕ} {ω : Seed Tx Hash np n Hz Sch} (hTip : TipGood P A K d ω)
    (hσ : d + 2 ≤ σ) : (seedTrace P A K ω).SlotTip (seedNow P A ω) Block.sl σ K := by
  intro p j hp hj
  let _ := ω.params P; let _ := ω.bparams P
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (hp.2 j hj)
  obtain ⟨b, hb, -, hbt⟩ := hTip j hj p l hl hp.1
  exact ⟨b, by simpa [seedTrace, seedChain, hl] using hb, by simp only [seedNow]; omega⟩

/-- An honest initial party is honest in `seedTrace P A K ω`: by `reachable_inv` it has a local
state at every phase. -/
theorem seedTrace_honest_of_init {K : ℕ} {ω : Seed Tx Hash np n Hz Sch} {p : Fin np}
    (hp : p ∈ P.IP) (hh : is_honest p = true) : (seedTrace P A K ω).honest p := by
  refine ⟨hh, fun j _ => ?_⟩
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  exact ((reachable_inv (reach_runTrace (Tx := Tx) (Hash := Hash) (Party := Fin np)
    (AdvState := A.AdvState) j)).state_init p).2 hp

/-- If the genesis block has slot `0`, the genesis checkpoint is the epoch-boundary checkpoint
of epoch `0` on the chain of every honest party at every phase up to `K`: the chain ends in
genesis and every other block of it has a larger slot. -/
theorem seed_genesis_checkpoint (hGB : P.GB.sl = 0) {K j : ℕ} {ω : Seed Tx Hash np n Hz Sch}
    {p : Fin np} (hp : (seedTrace P A K ω).honest p) (hj : j ≤ K) (E : ℕ) :
    IsCheckpointOf Block.sl E (seedChain P A ω j p) (genesisCheckpoint (seedTree P ω)) := by
  let _ := ω.params P; let _ := ω.bparams P
  have hval := seedChain_valid hp hj
  obtain ⟨s, hs⟩ := valid_chain_suffix_gb hval
  have hdec : List.Pairwise lt_slots (s ++ [P.GB]) := hs ▸ hval.2.2
  rw [List.pairwise_append] at hdec
  have hsn : s.find? (fun b => decide (b.sl ≤ 0 * E)) = none := by
    rw [List.find?_eq_none]
    intro x hx
    have := hdec.2.2 x hx P.GB (List.mem_singleton_self _)
    simp only [decide_eq_true_eq]
    change P.GB.sl < x.sl at this
    omega
  change (seedChain P A ω j p).find? (fun b => decide (b.sl ≤ 0 * E)) = some P.GB
  rw [← hs, List.find?_append, hsn, Option.none_or]
  simp
  exact ⟨hGB, rfl⟩

end Seed

/-! ### The probability bound -/

section Bound

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] [Fintype Tx] [Fintype Hash]
  [Nonempty Hash] {np : ℕ} [Corruption (Fin np)] {n Hz : ℕ}
  {Sch : SigScheme (Block Tx Hash (Fin np))}

/-- Δ-updatedness with lag `N` on an execution, from the phase of slot `τ` up to phase `hz`:
at every such phase `t`, every honest party has received votes finalizing an epoch-boundary
checkpoint `c` of its chain with `now t ≤ c.epoch * E + N`. -/
def DeltaUpdated {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B] (T : BlockTree B)
    (w : V → ℕ) (X : ChainTrace V B) (now : ℕ → ℕ) (slot : B → ℕ) (E hz τ N : ℕ)
    (seen : ℕ → V → Finset (Vote V B)) : Prop :=
  ∀ p t, X.honest p → t ≤ hz → τ ≤ now t →
    ∃ c : Checkpoint B, Finalized T w (seen t p) c ∧ IsCheckpointOf slot E (X.chain t p) c ∧
      now t ≤ c.epoch * E + N

variable (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz Sch) (Tree : TreeFamily P)

/-- **Δ-updatedness of FFG over PoS-NSB, with high probability.** Let the hypotheses of
`PoSNSB.pos_nsb_security` hold for the keyed hash family `H`, let the genesis block have slot
`0`, let the quality be `w ≥ 4` and the window `σ ≥ d + 2` (the tip condition then follows
from `TipGood` by `seed_slotTip` and chain growth in slot form from `CQGood` by
`seed_slotChainGrowth`), and let the vote layer of every
seed satisfy `VoteHyp` with the earliest start `τ₀ ω = (e₀ + 1) E + σ + d` (`hvote`, `hτ₀`).
Then the probability that Δ-updatedness with lag `3 E + σ + d + Δ` fails, from the phase of
slot `τ₀ ω + Δ` up to phase `K`, is at most
`slotBound (kindLaw μ) n d w ε + crAdv (collFinder P A H μ W K) + ∑ᵢ eufAdv (forger P A H μ W K i)`. -/
theorem finality_updated_prob (hP : ProtocolHyp P) (hTree : Tree.Longest) (hGB : P.GB.sl = 0)
    (H : HashFam (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (wst : Fin np → ℕ) (E σ Δ GST : ℕ)
    (HS : Seed Tx Hash np n Hz Sch → Finset (Fin np)) (v₀ : Seed Tx Hash np n Hz Sch → Fin np)
    (pre : Seed Tx Hash np n Hz Sch → Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
    (j₀ : Seed Tx Hash np n Hz Sch → Checkpoint (Block Tx Hash (Fin np)))
    (τ₀ : Seed Tx Hash np n Hz Sch → ℕ) (ρ : Seed Tx Hash np n Hz Sch → ℕ → ℕ)
    (cast : Seed Tx Hash np n Hz Sch → ℕ → Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
    (seen : Seed Tx Hash np n Hz Sch → ℕ → Fin np →
      Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
    (hw4 : 4 ≤ w) (hσd : d + 2 ≤ σ)
    (hvote : ∀ ω, VoteHyp (seedTree P ω) wst (seedTrace P A K ω) (seedNow P A ω) Block.sl E σ d
      Δ GST K (HS ω) (v₀ ω) (pre ω) (j₀ ω) (τ₀ ω) (ρ ω) (cast ω) (seen ω))
    (hτ₀ : ∀ ω, τ₀ ω = (livenessEpoch (pre ω) (j₀ ω) + 1) * E + σ + d) :
    (seedDist H μ P.h0 W n Sch).toOuterMeasure {ω | ¬DeltaUpdated (seedTree P ω) wst
        (seedTrace P A K ω) (seedNow P A ω) Block.sl E K (τ₀ ω + Δ) (3 * E + σ + d + Δ)
        (seen ω)} ≤
      slotBound (kindLaw μ) n d w ε + crAdv (collFinder P A H μ W K) +
        ∑ i : Fin np, eufAdv (forger P A H μ W K i) := by
  have hsub : {ω | ¬DeltaUpdated (seedTree P ω) wst (seedTrace P A K ω) (seedNow P A ω)
      Block.sl E K (τ₀ ω + Δ) (3 * E + σ + d + Δ) (seen ω)} ⊆
      {ω | ¬Good P A Tree (kindLaw μ) K d w ε ω} := by
    intro ω hω hG
    exact hω fun p t hp ht hτ =>
      finality_updated_start ⟨hvote ω, seed_slotChainHyp hGB hG.2.2.1
        (seed_slotChainGrowth hGB hG.2.1 hw4 (by omega) (seed_slotTip hG.2.2.2 hσd))⟩
        (hτ₀ ω) hp ht hτ
  exact (MeasureTheory.OuterMeasure.mono _ hsub).trans
    (pos_nsb_security P A Tree hP hTree H μ W K d w ε hwd hWn hn hHz hε hγ hw h3)

end Bound

/-! ### Phases and slots -/

section Phases

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

theorem phaseStep_progress_ne (N : GlobalState Tx Hash Party AdvState) :
    (phaseStep N).progress ≠ N.progress := by
  unfold phaseStep
  cases h : N.progress <;> simp

/-- Every phase advances the phase counter by one. -/
theorem phase_phaseStep (N : GlobalState Tx Hash Party AdvState) :
    phase (phaseStep N) = phase N + 1 := by
  rcases step_phase (step_phaseStep N) with h | ⟨-, -, -, -, h⟩
  · exact h
  · exact absurd h (phaseStep_progress_ne N)

theorem phase_runTrace (k : ℕ) :
    phase (runTrace (Tx := Tx) (Hash := Hash) (Party := Party) AdvState k) = k + 3 := by
  induction k with
  | zero => simp [runTrace, phase, N0]
  | succ k ih => rw [runTrace_succ, phase_phaseStep, ih]

/-- Phase `3 s` of an execution is the start of slot `s + 1`. -/
theorem runTrace_three_mul_t_now (s : ℕ) :
    (runTrace (Tx := Tx) (Hash := Hash) (Party := Party) AdvState (3 * s)).t_now = s + 1 :=
  (phase_ready (sl := s + 1) (by rw [phase_runTrace]; omega)).2

end Phases

section SeedPhases

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {Sch : SigScheme (Block Tx Hash (Fin np))}
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz Sch)

/-- Phase `3 s` of the real execution of a seed has slot `s + 1`; in particular every slot
`s + 1` is the slot of some phase, as required by `VoteHyp.round_slot`. -/
theorem seedNow_three_mul (ω : Seed Tx Hash np n Hz Sch) (s : ℕ) :
    seedNow P A ω (3 * s) = s + 1 := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  exact runTrace_three_mul_t_now (Tx := Tx) (Hash := Hash) (Party := Fin np)
    (AdvState := A.AdvState) s

end SeedPhases

/-! ### The finality layer started at genesis -/

section Genesis

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] [Fintype Tx] [Fintype Hash]
  [Nonempty Hash] {np : ℕ} [Corruption (Fin np)] {n Hz : ℕ}
  {Sch : SigScheme (Block Tx Hash (Fin np))}

/-- The honest initial parties of `P`: the validators of the vote layer started at genesis. -/
def honestInit (P : Protocol Tx Hash np n Hz) : Finset (Fin np) :=
  (P.IP.filter fun p => is_honest p).toFinset

/-- The phase of round `r` of the vote layer started at genesis: the phase of slot
`2 E + σ + d + r (2 E)`. -/
def genesisRound (E σ d r : ℕ) : ℕ := 3 * (2 * E + σ + d + r * (2 * E) - 1)

variable (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz Sch) (Tree : TreeFamily P)

/-- **Δ-updatedness of FFG over PoS-NSB from genesis, with high probability.** Let the
hypotheses of `PoSNSB.pos_nsb_security` hold for the keyed hash family `H`, let the genesis
block have slot `0`, `w ≥ 4` and `σ ≥ d + 2`. Let the finality layer start at genesis: no
votes before the start, the genesis checkpoint as the last justified checkpoint, the honest
initial parties `honestInit P` as the honest validators, and the rounds at the phases
`genesisRound E σ d r` of the slots `2 E + σ + d + r (2 E)`. Assume that the honest validators
hold two thirds of the stake (`quorum`), that some honest initial party `v₀` exists, that
honest validators cast the votes of the schedule (`round_cast`), that every vote cast is
received by every honest party within `Δ` slots after `GST` (`sync`), `GST ≤ 2 E + σ + d`,
`1 ≤ E` and `1 ≤ Δ`. Then the probability that Δ-updatedness with lag `3 E + σ + d + Δ`
fails, from the phase of slot `2 E + σ + d + Δ` up to phase `K`, is at most
`slotBound (kindLaw μ) n d w ε + crAdv (collFinder P A H μ W K) + ∑ᵢ eufAdv (forger P A H μ W K i)`. -/
theorem finality_updated_prob_genesis (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (hGB : P.GB.sl = 0)
    (H : HashFam (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (wst : Fin np → ℕ) (E σ Δ GST : ℕ) (v₀ : Fin np)
    (cast : Seed Tx Hash np n Hz Sch → ℕ → Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
    (seen : Seed Tx Hash np n Hz Sch → ℕ → Fin np →
      Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
    (hw4 : 4 ≤ w) (hσd : d + 2 ≤ σ) (hE : 1 ≤ E) (hΔ : 1 ≤ Δ) (hGST : GST ≤ 2 * E + σ + d)
    (hv₀ : v₀ ∈ P.IP ∧ is_honest v₀ = true)
    (quorum : 2 * totalStake wst ≤ 3 * stake wst (honestInit P))
    (round_cast : ∀ ω r, genesisRound E σ d r ≤ K →
      roundVotes (honestInit P)
          (roundExt (seedTree P ω) (seedTrace P A K ω) Block.sl E v₀ (genesisRound E σ d)) ∅
          (genesisCheckpoint (seedTree P ω)) r ⊆
        cast ω (genesisRound E σ d r))
    (sync : ∀ ω p j t x, (seedTrace P A K ω).honest p → j ≤ t → x ∈ cast ω j →
      max (seedNow P A ω j) GST + Δ ≤ seedNow P A ω t → x ∈ seen ω t p) :
    (seedDist H μ P.h0 W n Sch).toOuterMeasure {ω | ¬DeltaUpdated (seedTree P ω) wst
        (seedTrace P A K ω) (seedNow P A ω) Block.sl E K (2 * E + σ + d + Δ)
        (3 * E + σ + d + Δ) (seen ω)} ≤
      slotBound (kindLaw μ) n d w ε + crAdv (collFinder P A H μ W K) +
        ∑ i : Fin np, eufAdv (forger P A H μ W K i) := by
  have hlE : ∀ ω : Seed Tx Hash np n Hz Sch,
      livenessEpoch (∅ : Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
        (genesisCheckpoint (seedTree P ω)) = 1 := fun _ => by
    simp [livenessEpoch, genesisCheckpoint]
  have hmem : ∀ {v}, v ∈ honestInit P → v ∈ P.IP ∧ is_honest v = true := fun hv => by
    simpa [honestInit] using hv
  refine finality_updated_prob P A Tree hP hTree hGB H μ W K d w ε hwd hWn hn hHz hε hγ hw h3
    wst E σ Δ GST (fun _ => honestInit P) (fun _ => v₀) (fun _ => ∅)
    (fun ω => genesisCheckpoint (seedTree P ω)) (fun _ => 2 * E + σ + d)
    (fun _ => genesisRound E σ d) cast seen hw4 hσd (fun ω => ?_) (fun ω => ?_)
  · exact
      { epoch_pos := hE
        delay_pos := hΔ
        honest := fun v hv => seedTrace_honest_of_init (hmem hv).1 (hmem hv).2
        mem_v₀ := by simpa [honestInit] using hv₀
        quorum := quorum
        pre_justified := Justified.genesis
        pre_sources := fun _ hx => absurd hx (Finset.notMem_empty _)
        pre_unslashable := by
          refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
          rcases mem_slashable.1 (Finset.mem_inter.1 hv).1 with ⟨x, hx, -⟩ | ⟨x, hx, -⟩ <;>
            exact Finset.notMem_empty x hx
        pre_onChain := fun h0 v hv =>
          seed_genesis_checkpoint hGB (seedTrace_honest_of_init (hmem hv).1 (hmem hv).2) h0 E
        pre_cast := fun _ hx => absurd hx (Finset.notMem_empty _)
        start := (hlE ω).symm ▸ le_rfl
        gst := hGST
        round_slot := fun r => by
          rw [genesisRound, seedNow_three_mul]
          omega
        round_cast := round_cast ω
        sync := sync ω }
  · rw [hlE]

end Genesis

/-! ### The concrete instance `PoSNSB.Instance` -/

namespace Instance

open PoSNSB.Instance

attribute [local instance] PoSNSB.Instance.corruption

/-- The rounds of the schedule at the phases of slots `12 + 2 r`. -/
def ρI (r : ℕ) : ℕ := 3 * (11 + r * (2 * 1))

/-- **Non-vacuity of the hypotheses of `finality_updated_prob`.** For the instance `PoSNSB.Instance`
(`PoSNSB.Instance`: one honest party, all slots honest, horizon `K = 0`, `d = 4`, `w = 4`,
`ε = 0`), with `E = 1`, `σ = 6`, `Δ = 1`, `GST = 0`, unit stake, `HS = univ`, no votes, the
genesis checkpoint as `j₀`, `τ₀ = 12` and rounds at the phases `ρI r`, the hypotheses
`ProtocolHyp`, `Tree.Longest`, `P.GB.sl = 0`, `VoteHyp` and the start `τ₀` of
`finality_updated_prob` hold. The horizon `K = 0` of the instance precedes the first round, so
the conclusion carries no information there. -/
theorem prob_hyps :
    ProtocolHyp P ∧ Tree.Longest ∧ P.GB.sl = 0 ∧
      (∀ ω, VoteHyp (seedTree P ω) (fun _ => 1) (seedTrace P A 0 ω) (seedNow P A ω) Block.sl
        1 6 4 1 0 0 Finset.univ 0 ∅ (genesisCheckpoint (seedTree P ω)) 12 ρI (fun _ => ∅)
        (fun _ _ => ∅)) ∧
      (∀ ω : Seed Unit Unit 1 4 1 Sch,
        12 = (livenessEpoch (∅ : Finset (Vote (Fin 1) (Block Unit Unit (Fin 1))))
          (genesisCheckpoint (seedTree P ω)) + 1) * 1 + 6 + 4) := by
  obtain ⟨hP, hT, -⟩ := instance_hyps
  have hlE : ∀ ω : Seed Unit Unit 1 4 1 Sch,
      livenessEpoch (∅ : Finset (Vote (Fin 1) (Block Unit Unit (Fin 1))))
        (genesisCheckpoint (seedTree P ω)) = 1 := fun _ => by
    simp [livenessEpoch, genesisCheckpoint]
  refine ⟨hP, hT, rfl, fun ω => ?_, fun ω => by rw [hlE]⟩
  · have hρ : ∀ r, 0 < ρI r := fun r => by simp only [ρI]; omega
    exact
      { epoch_pos := le_rfl
        delay_pos := le_rfl
        honest := fun v _ => by
          refine ⟨rfl, fun j hj => ?_⟩
          obtain rfl : j = 0 := by omega
          obtain rfl : v = 0 := Subsingleton.elim _ _
          simp only [sTrace, runTrace, Function.iterate_zero, id, N0]
          exact if_pos (List.mem_singleton_self _) ▸ rfl
        mem_v₀ := Finset.mem_univ _
        quorum := by
          show 2 * stake (fun _ : Fin 1 => 1) Finset.univ ≤ 3 * stake (fun _ : Fin 1 => 1) _
          omega
        pre_justified := Justified.genesis
        pre_sources := fun _ hx => absurd hx (Finset.notMem_empty _)
        pre_unslashable := by
          refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
          rcases mem_slashable.1 (Finset.mem_inter.1 hv).1 with ⟨x, hx, -⟩ | ⟨x, hx, -⟩ <;>
            exact Finset.notMem_empty x hx
        pre_onChain := fun h => absurd h (by have := hρ 0; omega)
        pre_cast := fun _ hx => absurd hx (Finset.notMem_empty _)
        start := by rw [hlE]
        gst := Nat.zero_le _
        round_slot := fun r => by
          rw [ρI, seedNow_three_mul]
          omega
        round_cast := fun r h => absurd h (by have := hρ r; omega)
        sync := fun _ _ _ x _ _ hx _ => absurd hx (Finset.notMem_empty _) }

end Instance

end CatCryptCore.Consensus.Finality

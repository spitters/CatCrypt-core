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
execution of PoS-NSB (`CatCryptCore.Consensus.PoSNSB.Prob`, rows D1 and D2) and bounds the
probability that Δ-updatedness fails by the failure bound of D2 (`PoSNSB.pos_nsb_security`):

  `slotBound ν n d w ε + q (q - 1) / 2 / |Hash| + ∑ᵢ eufAdv (forger P A ν W K i)`,

the Chernoff-Hoeffding bound on the slot conditions, the birthday bound of the random oracle,
and the EUF-CMA advantages of the explicit forgers `forger P A ν W K i` built from the
adversary `A`. The only numeric terms are the two information-theoretic ones; the signature
scheme enters through `eufAdv` of explicit adversaries.

## The execution seen by the finality layer

For a seed `ω`, phase `j` of the real execution is `sTrace P ω A false j`:

* `seedNow P A ω j` is its slot `t_now`;
* `seedChain P A ω j p` is the chain that party `p` selects, `bestChain (t_now - 1)` of its
  block tree, and `[]` if `p` has no local state;
* `seedTrace P A K ω` regards a party as honest if it is honest for the corruption map and has
  a local state at every phase up to `K`;
* `seedTree P ω` is the ancestor relation of predecessor hashes under the random oracle of `ω`,
  with genesis `P.GB`.

## What is derived and what is assumed

From the event `PoSNSB.Good` of D2 (`seed_slotChainHyp`): the monotone clock, chains ordered by
`seedTree` with strictly decreasing slots and containing genesis (from `best_chain_valid`), and
common prefix by slots (`PoSNSB.CPGood`, which is exactly `ChainTrace.SlotCommonPrefix`).

Assumed explicitly in `finality_updated_prob`:

* `hGB : P.GB.sl = 0`: the genesis block has slot `0` (`ProtocolHyp` gives `≤ 1`);
* `hgrowth`: on every seed with `Good`, chain growth in slot form
  (`ChainTrace.SlotChainGrowth` with window `σ`) holds up to phase `K`. D2 proves chain growth
  for the length of the honest tree chain (`PoSNSB.CGGood`); that every window of `σ` slots
  contains a block of every honest chain is not among the properties of D2;
* `hvote`: on every seed, the vote layer (votes cast and received, the honest schedule, and
  the history before it) satisfies `VoteHyp`. PoS-NSB carries no FFG votes, so the vote layer
  is an additional component of the execution, given as functions of the seed.
* `hτ₀`: the honest schedule starts at the earliest slot `τ₀ = (e₀ + 1) E + σ + d`.

## Main results

* `properly_linked_pairwise`: a properly linked chain is ordered by the ancestor relation of
  predecessor hashes.
* `seed_slotChainHyp`: on the event `CPGood`, given slot chain growth and `P.GB.sl = 0`, the
  traces of PoS-NSB satisfy `SlotChainHyp` up to phase `K`.
* `finality_updated_prob`: Δ-updatedness with lag `3 E + σ + d + Δ` fails with probability at
  most the failure bound of D2.
* `Instance.prob_hyps`: the hypotheses of `finality_updated_prob` hold for the concrete
  instance of D2 (`PoSNSB.Instance`, horizon `K = 0`).
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
predecessor hashes under the random oracle of `ω`; genesis is `P.GB`. -/
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

/-- **The chain hypotheses from D2.** On a seed with common prefix `CPGood` with parameter `d`
up to phase `K`, if the genesis block has slot `0` and chain growth in slot form with window
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

/-- **Δ-updatedness of FFG over PoS-NSB, with high probability.** Let the hypotheses of D2
(`PoSNSB.pos_nsb_security`) hold, let the genesis block have slot `0`, let chain growth in slot
form with window `σ` hold on every seed with `Good` (`hgrowth`), and let the vote layer of every
seed satisfy `VoteHyp` with the earliest start `τ₀ ω = (e₀ + 1) E + σ + d` (`hvote`, `hτ₀`).
Then the probability that Δ-updatedness with lag `3 E + σ + d + Δ` fails, from the phase of
slot `τ₀ ω + Δ` up to phase `K`, is at most
`slotBound ν n d w ε + q (q - 1) / 2 / |Hash| + ∑ᵢ eufAdv (forger P A ν W K i)`. -/
theorem finality_updated_prob (hP : ProtocolHyp P) (hTree : Tree.Longest) (hGB : P.GB.sl = 0)
    (ν : PMF SlotKind) (W K d w : ℕ) (ε : ℝ)
    (hd : 1 ≤ d) (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA ν ≤ pH ν) (hw : (w : ℝ) ≤ d * (pH ν - pA ν))
    (h3 : (3 : ℝ) ≤ d * (pH ν - 2 * pA ν)) (q : ℕ)
    (next : (Fin n → SlotKind) → (Fin np → Sch.PK × Sch.SK) →
      Querier (BlockDom Tx Hash np Hz) Hash)
    (hRO : ∀ ω : Seed Tx Hash np n Hz Sch, ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      ∀ b ∈ block_hist_gb (sTrace P ω A false j), ∃ k < q,
        query (next ω.κ ω.ks) ω.f k = encB Hz b)
    (wst : Fin np → ℕ) (E σ Δ GST : ℕ)
    (H : Seed Tx Hash np n Hz Sch → Finset (Fin np)) (v₀ : Seed Tx Hash np n Hz Sch → Fin np)
    (pre : Seed Tx Hash np n Hz Sch → Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
    (j₀ : Seed Tx Hash np n Hz Sch → Checkpoint (Block Tx Hash (Fin np)))
    (τ₀ : Seed Tx Hash np n Hz Sch → ℕ) (ρ : Seed Tx Hash np n Hz Sch → ℕ → ℕ)
    (cast : Seed Tx Hash np n Hz Sch → ℕ → Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
    (seen : Seed Tx Hash np n Hz Sch → ℕ → Fin np →
      Finset (Vote (Fin np) (Block Tx Hash (Fin np))))
    (hgrowth : ∀ ω, Good P A Tree ν K d w ε ω →
      (seedTrace P A K ω).SlotChainGrowth (seedNow P A ω) Block.sl σ K)
    (hvote : ∀ ω, VoteHyp (seedTree P ω) wst (seedTrace P A K ω) (seedNow P A ω) Block.sl E σ d
      Δ GST K (H ω) (v₀ ω) (pre ω) (j₀ ω) (τ₀ ω) (ρ ω) (cast ω) (seen ω))
    (hτ₀ : ∀ ω, τ₀ ω = (livenessEpoch (pre ω) (j₀ ω) + 1) * E + σ + d) :
    (seedDist ν W n Hz Sch).toOuterMeasure {ω | ¬DeltaUpdated (seedTree P ω) wst
        (seedTrace P A K ω) (seedNow P A ω) Block.sl E K (τ₀ ω + Δ) (3 * E + σ + d + Δ)
        (seen ω)} ≤
      slotBound ν n d w ε + ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Hash +
        ∑ i : Fin np, eufAdv (forger P A ν W K i) := by
  have hsub : {ω | ¬DeltaUpdated (seedTree P ω) wst (seedTrace P A K ω) (seedNow P A ω)
      Block.sl E K (τ₀ ω + Δ) (3 * E + σ + d + Δ) (seen ω)} ⊆
      {ω | ¬Good P A Tree ν K d w ε ω} := by
    intro ω hω hG
    exact hω fun p t hp ht hτ =>
      finality_updated_start ⟨hvote ω, seed_slotChainHyp hGB hG.2.2 (hgrowth ω hG)⟩ (hτ₀ ω)
        hp ht hτ
  exact (MeasureTheory.OuterMeasure.mono _ hsub).trans
    (pos_nsb_security P A Tree hP hTree ν W K d w ε hd hwd hWn hn hHz hε hγ hw h3 q next hRO)

end Bound

end CatCryptCore.Consensus.Finality

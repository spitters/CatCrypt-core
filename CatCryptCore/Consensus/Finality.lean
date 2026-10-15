/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.FFGExamples

/-!
# Finality layers over a longest-chain protocol

This file states the interface of a finality layer running on top of a blockchain whose
chain-selection rule is abstract, as the parameter `bestChain` of the PoS-NSB model
(`CatCryptCore.Consensus.PoSNSB`): an execution is seen through the chain that each party
selects at each time (`ChainTrace`). Chains are lists of blocks, newest first, as in PoS-NSB;
the prefix order of chains is therefore `List.IsSuffix` (`<:+`). Ancestry of blocks is an
`FFG.BlockTree`.

## Properties of the underlying chain (hypotheses)

* `ChainTrace.CommonPrefix k`: the chain of an honest party with its newest `k` blocks
  removed is a prefix of the chain of every honest party at every later time
  (Garay, Kiayias and Leonardos, common prefix with parameter `k`).
* `ChainTrace.ChainGrowth s g`: after `s` time steps the chain of every honest party is at
  least `g` blocks longer than the chain of any honest party before (chain growth with rate
  `g / s`, two-party form as in PoS-NSB's `chain_growth_parties`).
* `ChainTrace.ChainQuality hb ℓ μ`: every `ℓ` consecutive blocks of an honest chain contain at
  least `μ` blocks satisfying `hb` (chain quality with ratio `μ / ℓ`).
* `ChainTrace.ChainsInTree T`: consecutive blocks of honest chains are related by the
  ancestor relation of `T`.
* `ChainTrace.TraceGuard`: the conjunction of the four, the guard under which the finality
  properties are required (our reading of the trace guard of Magri, Matt, Nielsen and
  Tschudi, *Enig*, §3: the finality properties are only demanded on traces of the underlying
  chain that satisfy the stated chain properties).

These are hypotheses of the theorems that use them, never axioms or instances.

## Properties of a finality layer (conclusions)

A finalization `fin : Finalization Party Blk` records `fin t p b i`: at time `t`, party `p`
regards block `b` as final at position `i` (a height, a finalization index or an epoch).
Following Dinsdale-Young, Magri, Matt, Nielsen and Tschudi (*Afgjort*, SCN 2020):

* `PositionRespecting T X fin`: finalized blocks of honest parties at positions `i ≤ j` are
  ancestors of one another, across parties and times (finality-respecting positions).
* `ChainForming T X fin`: the finalized blocks of an honest party at one time form a chain of
  `T`, ordered by position.
* `Agreement T X fin`: all finalized blocks of honest parties lie on one chain of `T`.
* `FinalityRespecting X fin`: a block finalized by an honest party stays on that party's
  selected chain at all later times.
* `FinalityLayer T X fin`: the conjunction of the four.

## Main results

* `PositionRespecting.chainForming`, `PositionRespecting.agreement`: finality-respecting
  positions give chain-forming and agreement.
* `kDeep_finalityLayer`: the rule "a block is final once it is `k` deep" is a finality layer
  on every trace with common prefix `k` whose chains lie in `T`.
* `kDeep_growth`, `kDeep_quality`: under chain growth and chain quality the `k`-deep
  finalized chain grows at rate `g / s` and has quality `μ / ℓ`.
* `kDeep_of_traceGuard`: the three statements together under `TraceGuard`.
* `ffg_positionRespecting`, `ffg_agreement`, `ffg_chainForming`: Casper FFG over a chain.
  Each party finalizes the checkpoints that are finalized by the votes it has seen; if the
  slashable validators of all votes cast hold less than a third of the stake, the finalized
  checkpoints of all parties respect epochs, form a chain and agree. The proof is FFG's
  accountable safety (`FFG.anc_of_kFinalized_of_justified`).
* `ffg_checkpointChain`: a list of finalized checkpoints sorted by epoch is a chain of `T`.
* `ffg_justified_isCheckpoint`, `ffg_finalized_isCheckpoint`: if honest validators vote only
  for epoch-boundary checkpoints of their selected chains and hold more than a third of the
  stake, every justified (in particular every finalized) checkpoint other than genesis is an
  epoch-boundary block of the selected chain of some honest validator.
* `Examples.ffg_nonvacuous`, `Examples.kDeep_nonvacuous`: concrete traces on which all
  hypotheses of the FFG and `k`-deep theorems hold and some block is finalized;
  `Examples.ffg_agreement_fails_doubleVotes`: with half of the stake slashable, FFG
  finalizes two conflicting checkpoints, so the stake bound cannot be dropped.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.Finality

open FFG

/-! ### Executions seen through the chain-selection rule -/

/-- An execution seen through the chain-selection rule: `chain t p` is the chain (newest block
first) that party `p` selects at time `t`, the output of `bestChain` in the PoS-NSB model;
`honest p` says that `p` follows the protocol. -/
structure ChainTrace (Party Blk : Type*) where
  /-- The honest parties. -/
  honest : Party → Prop
  /-- The chain selected by each party at each time, newest block first. -/
  chain : ℕ → Party → List Blk

namespace ChainTrace

variable {Party Blk : Type*} (X : ChainTrace Party Blk)

/-- Common prefix with parameter `k`: for honest `p`, `q` and times `t ≤ t'`, the chain of `p`
at `t` without its newest `k` blocks is a prefix of the chain of `q` at `t'`. -/
def CommonPrefix (k : ℕ) : Prop :=
  ∀ p q t t', X.honest p → X.honest q → t ≤ t' → (X.chain t p).drop k <:+ X.chain t' q

/-- Chain growth with window `s` and growth `g`: for honest `p`, `q` and times
`t + s ≤ t'`, the chain of `q` at `t'` is at least `g` blocks longer than the chain of `p` at
`t`. -/
def ChainGrowth (s g : ℕ) : Prop :=
  ∀ p q t t', X.honest p → X.honest q → t + s ≤ t' →
    (X.chain t p).length + g ≤ (X.chain t' q).length

/-- Chain quality with window `ℓ` and bound `μ` for the block predicate `hb` (for instance,
"baked by an honest party"): every `ℓ` consecutive blocks of the chain of an honest party
contain at least `μ` blocks satisfying `hb`. -/
def ChainQuality (hb : Blk → Bool) (ℓ μ : ℕ) : Prop :=
  ∀ p t i, X.honest p → i + ℓ ≤ (X.chain t p).length →
    μ ≤ (((X.chain t p).drop i).take ℓ).countP hb

/-- The chains of honest parties lie in the block tree `T`: of two blocks of such a chain, the
older one is an ancestor of the newer one. -/
def ChainsInTree (T : BlockTree Blk) : Prop :=
  ∀ p t, X.honest p → (X.chain t p).Pairwise fun b b' => T.anc b' b

/-- The trace guard: the chains of honest parties lie in `T` and satisfy common prefix `k`,
chain growth `(s, g)` and chain quality `(hb, ℓ, μ)`. The finality properties are required on
traces that satisfy this guard. -/
def TraceGuard (T : BlockTree Blk) (k s g : ℕ) (hb : Blk → Bool) (ℓ μ : ℕ) : Prop :=
  X.ChainsInTree T ∧ X.CommonPrefix k ∧ X.ChainGrowth s g ∧ X.ChainQuality hb ℓ μ

end ChainTrace

/-! ### Finality properties -/

/-- A finalization: `fin t p b i` says that at time `t` party `p` regards block `b` as final at
position `i`. -/
abbrev Finalization (Party Blk : Type*) := ℕ → Party → Blk → ℕ → Prop

variable {Party Blk : Type*}

/-- Finality-respecting positions: if honest `p` finalizes `b` at position `i` and honest `q`
finalizes `b'` at position `j ≥ i`, at any two times, then `b` is an ancestor of `b'`. -/
def PositionRespecting (T : BlockTree Blk) (X : ChainTrace Party Blk)
    (fin : Finalization Party Blk) : Prop :=
  ∀ p q t t' b b' i j, X.honest p → X.honest q → fin t p b i → fin t' q b' j → i ≤ j →
    T.anc b b'

/-- Chain-forming: the blocks an honest party has finalized at one time form a chain of `T`,
ordered by position. -/
def ChainForming (T : BlockTree Blk) (X : ChainTrace Party Blk)
    (fin : Finalization Party Blk) : Prop :=
  ∀ p t b b' i j, X.honest p → fin t p b i → fin t p b' j → i ≤ j → T.anc b b'

/-- Agreement: any two blocks finalized by honest parties, at any times, are related by the
ancestor relation, so that all of them lie on one chain of `T`. -/
def Agreement (T : BlockTree Blk) (X : ChainTrace Party Blk)
    (fin : Finalization Party Blk) : Prop :=
  ∀ p q t t' b b' i j, X.honest p → X.honest q → fin t p b i → fin t' q b' j →
    T.anc b b' ∨ T.anc b' b

/-- Finality-respecting chain selection: a block finalized by an honest party lies on the
chain that party selects at every later time. -/
def FinalityRespecting (X : ChainTrace Party Blk) (fin : Finalization Party Blk) : Prop :=
  ∀ p t t' b i, X.honest p → t ≤ t' → fin t p b i → b ∈ X.chain t' p

/-- A finality layer on the trace `X`: finality-respecting positions, chain-forming,
agreement and finality-respecting chain selection. -/
def FinalityLayer (T : BlockTree Blk) (X : ChainTrace Party Blk)
    (fin : Finalization Party Blk) : Prop :=
  PositionRespecting T X fin ∧ ChainForming T X fin ∧ Agreement T X fin ∧
    FinalityRespecting X fin

/-- Finality-respecting positions imply chain-forming. -/
theorem PositionRespecting.chainForming {T : BlockTree Blk} {X : ChainTrace Party Blk}
    {fin : Finalization Party Blk} (h : PositionRespecting T X fin) : ChainForming T X fin :=
  fun p t b b' i j hp hb hb' hij => h p p t t b b' i j hp hp hb hb' hij

/-- Finality-respecting positions imply agreement. -/
theorem PositionRespecting.agreement {T : BlockTree Blk} {X : ChainTrace Party Blk}
    {fin : Finalization Party Blk} (h : PositionRespecting T X fin) : Agreement T X fin := by
  intro p q t t' b b' i j hp hq hb hb'
  rcases le_total i j with hij | hij
  · exact Or.inl (h p q t t' b b' i j hp hq hb hb' hij)
  · exact Or.inr (h q p t' t b' b j i hq hp hb' hb hij)

/-! ### Finality by depth -/

/-- `k`-deep finality: party `p` regards `b` as final at time `t` at height `i` when `b` is a
block of its selected chain with at least `k` blocks above it and exactly `i` blocks below
it. -/
def kDeep (k : ℕ) (X : ChainTrace Party Blk) : Finalization Party Blk :=
  fun t p b i => ∃ C, b :: C <:+ (X.chain t p).drop k ∧ C.length = i

/-- Every position below the length of a list is the height of a block of it. -/
theorem exists_suffix_cons_of_lt {D : List Blk} {i : ℕ} (hi : i < D.length) :
    ∃ b C, b :: C <:+ D ∧ C.length = i := by
  obtain ⟨b, C, hbc⟩ : ∃ b C, D.drop (D.length - (i + 1)) = b :: C := by
    cases h : D.drop (D.length - (i + 1)) with
    | nil => simp at h; omega
    | cons b C => exact ⟨b, C, rfl⟩
  refine ⟨b, C, hbc ▸ List.drop_suffix _ _, ?_⟩
  have := congrArg List.length hbc
  simp only [List.length_drop, List.length_cons] at this
  omega

/-- Two suffixes of one chain in a tree, the first not longer than the second, headed by `b`
and `b'`: then `b` is an ancestor of `b'`. -/
theorem anc_of_suffix_cons {T : BlockTree Blk} {D C C' : List Blk} {b b' : Blk}
    (hD : D.Pairwise fun x y => T.anc y x) (h : b :: C <:+ D) (h' : b' :: C' <:+ D)
    (hl : C.length ≤ C'.length) : T.anc b b' := by
  have hs : b :: C <:+ b' :: C' :=
    List.suffix_of_suffix_length_le h h' (by simpa using hl)
  have hP : (b' :: C').Pairwise fun x y => T.anc y x := hD.sublist h'.sublist
  rcases List.mem_cons.1 (hs.subset List.mem_cons_self) with rfl | hm
  · exact T.anc_refl b
  · exact List.rel_of_pairwise_cons hP hm

variable {T : BlockTree Blk} {X : ChainTrace Party Blk}

/-- Under common prefix `k`, with honest chains in `T`, `k`-deep finality has
finality-respecting positions. -/
theorem kDeep_positionRespecting {k : ℕ} (hT : X.ChainsInTree T) (hcp : X.CommonPrefix k) :
    PositionRespecting T X (kDeep k X) := by
  rintro p q t t' b b' i j hp hq ⟨C, hC, rfl⟩ ⟨C', hC', rfl⟩ hij
  rcases le_total t t' with htt | htt
  · exact anc_of_suffix_cons (hT q t' hq)
      (hC.trans ((hcp p q t t' hp hq htt))) (hC'.trans (List.drop_suffix _ _)) hij
  · exact anc_of_suffix_cons (hT p t hp)
      (hC.trans (List.drop_suffix _ _)) (hC'.trans (hcp q p t' t hq hp htt)) hij

/-- Under common prefix `k`, a block that is `k` deep in the chain of an honest party stays in
its chain at every later time. -/
theorem kDeep_finalityRespecting {k : ℕ} (hcp : X.CommonPrefix k) :
    FinalityRespecting X (kDeep k X) := by
  rintro p t t' b i hp htt ⟨C, hC, -⟩
  exact ((hC.trans (hcp p p t t' hp hp htt)).subset List.mem_cons_self)

/-- `k`-deep finality is a finality layer on every trace with common prefix `k` whose honest
chains lie in `T`. -/
theorem kDeep_finalityLayer {k : ℕ} (hT : X.ChainsInTree T) (hcp : X.CommonPrefix k) :
    FinalityLayer T X (kDeep k X) :=
  let h := kDeep_positionRespecting hT hcp
  ⟨h, h.chainForming, h.agreement, kDeep_finalityRespecting hcp⟩

/-- Under chain growth `(s, g)`: if the chain of honest `p` at `t` has more than `k` blocks,
then at every time `t' ≥ t + s` every honest `q` has a `k`-deep final block at height `g`
above the top `k`-deep height of `p` at `t`. -/
theorem kDeep_growth {k s g : ℕ} (hcg : X.ChainGrowth s g) {p q : Party} {t t' : ℕ}
    (hp : X.honest p) (hq : X.honest q) (htt : t + s ≤ t') (hk : k < (X.chain t p).length) :
    ∃ b, kDeep k X t' q b ((X.chain t p).length - k - 1 + g) := by
  have := hcg p q t t' hp hq htt
  obtain ⟨b, C, hC, hl⟩ := exists_suffix_cons_of_lt
    (D := (X.chain t' q).drop k) (i := (X.chain t p).length - k - 1 + g)
    (by simp only [List.length_drop]; omega)
  exact ⟨b, C, hC, hl⟩

/-- Under chain quality `(hb, ℓ, μ)`: every `ℓ` consecutive `k`-deep blocks of the chain of an
honest party (blocks `k + i, …, k + i + ℓ - 1` counted from the newest) contain at least `μ` blocks satisfying `hb`. -/
theorem kDeep_quality {k : ℕ} {hb : Blk → Bool} {ℓ μ : ℕ} (hcq : X.ChainQuality hb ℓ μ)
    {p : Party} {t i : ℕ} (hp : X.honest p) (hi : k + i + ℓ ≤ (X.chain t p).length) :
    μ ≤ ((((X.chain t p).drop k).drop i).take ℓ).countP hb := by
  rw [List.drop_drop]
  exact hcq p t (k + i) hp hi

/-- On a trace that satisfies the trace guard, `k`-deep finality is a finality layer whose
finalized chain grows at rate `g / s` and has quality `μ / ℓ`. -/
theorem kDeep_of_traceGuard {k s g : ℕ} {hb : Blk → Bool} {ℓ μ : ℕ}
    (hG : X.TraceGuard T k s g hb ℓ μ) :
    FinalityLayer T X (kDeep k X) ∧
      (∀ p q t t', X.honest p → X.honest q → t + s ≤ t' → k < (X.chain t p).length →
        ∃ b, kDeep k X t' q b ((X.chain t p).length - k - 1 + g)) ∧
      (∀ p t i, X.honest p → k + i + ℓ ≤ (X.chain t p).length →
        μ ≤ ((((X.chain t p).drop k).drop i).take ℓ).countP hb) :=
  ⟨kDeep_finalityLayer hG.1 hG.2.1, fun _ _ _ _ hp hq htt hk => kDeep_growth hG.2.2.1 hp hq htt hk,
    fun _ _ _ hp hi => kDeep_quality hG.2.2.2 hp hi⟩

/-! ### Casper FFG over the chain -/

section FFGInstance

variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B]

/-- The epoch-boundary block of epoch `e` on the chain `C`, for epochs of `E` slots: the
newest block of `C` whose slot is at most `e * E`. -/
def epochBoundary (slot : B → ℕ) (E : ℕ) (C : List B) (e : ℕ) : Option B :=
  C.find? fun b => decide (slot b ≤ e * E)

/-- The checkpoint `c` is the epoch-boundary checkpoint of its epoch on the chain `C`. -/
def IsCheckpointOf (slot : B → ℕ) (E : ℕ) (C : List B) (c : Checkpoint B) : Prop :=
  epochBoundary slot E C c.epoch = some c.block

instance (slot : B → ℕ) (E : ℕ) (C : List B) (c : Checkpoint B) :
    Decidable (IsCheckpointOf slot E C c) := by
  unfold IsCheckpointOf; infer_instance

/-- Honest validators vote on their chain: for every vote of an honest validator there is a
time at which its source and its target are epoch-boundary checkpoints of the chain that
validator selects. -/
def HonestVotesOnChain (X : ChainTrace V B) (slot : B → ℕ) (E : ℕ)
    (votes : Finset (Vote V B)) : Prop :=
  ∀ x ∈ votes, X.honest x.validator → ∃ t,
    IsCheckpointOf slot E (X.chain t x.validator) x.source ∧
      IsCheckpointOf slot E (X.chain t x.validator) x.target

/-- FFG finality: validator `p` regards the block `b` as final at epoch `e` at time `t` when
the checkpoint `(b, e)` is finalized by the votes `seen t p` it has received. -/
def ffgFinalization (T : BlockTree B) (w : V → ℕ) (seen : ℕ → V → Finset (Vote V B)) :
    Finalization V B :=
  fun t p b e => Finalized T w (seen t p) ⟨b, e⟩

/-- Finalization is monotone in the vote set. -/
theorem Finalized.mono {T : BlockTree B} {w : V → ℕ} {votes votes' : Finset (Vote V B)}
    {c : Checkpoint B} (h : votes ⊆ votes') (hc : Finalized T w votes c) :
    Finalized T w votes' c :=
  ⟨hc.1.mono h, hc.2.imp fun _ hc' => ⟨hc'.1, hc'.2.mono h⟩⟩

variable {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
  {seen : ℕ → V → Finset (Vote V B)}

/-- FFG over the chain has finality-respecting positions. Let every party only see votes that
were cast (`seen t p ⊆ votes`), and let the validators that are slashable in `votes` hold less
than a third of the total stake. If party `p` finalizes the checkpoint `(b, i)` and party `q`
finalizes `(b', j)` with `i ≤ j`, at any times, then `b` is an ancestor of `b'`. -/
theorem ffg_positionRespecting (X : ChainTrace V B) (hseen : ∀ t p, seen t p ⊆ votes)
    (hS : 3 * stake w (slashable votes) < totalStake w) :
    PositionRespecting T X (ffgFinalization T w seen) := by
  intro p q t t' b b' i j _ _ hb hb' hij
  exact anc_of_kFinalized_of_justified (Finalized.mono (hseen t p) hb).kFinalized
    (Finalized.mono (hseen t' q) hb').1 hij hS

/-- Agreement of FFG over the chain: if the slashable validators of all cast votes hold less
than a third of the total stake, all checkpoints finalized by any parties at any times lie on
one chain of `T`. -/
theorem ffg_agreement (X : ChainTrace V B) (hseen : ∀ t p, seen t p ⊆ votes)
    (hS : 3 * stake w (slashable votes) < totalStake w) :
    Agreement T X (ffgFinalization T w seen) :=
  (ffg_positionRespecting X hseen hS).agreement

/-- FFG over the chain is chain-forming: if the slashable validators of all cast votes hold
less than a third of the total stake, the checkpoints finalized by one party at one time are
ordered by ancestry as by epoch. -/
theorem ffg_chainForming (X : ChainTrace V B) (hseen : ∀ t p, seen t p ⊆ votes)
    (hS : 3 * stake w (slashable votes) < totalStake w) :
    ChainForming T X (ffgFinalization T w seen) :=
  (ffg_positionRespecting X hseen hS).chainForming

/-- A finalized checkpoint chain is chain-forming: if the slashable validators hold less than
a third of the total stake, a list of checkpoints finalized by `votes` and sorted by epoch has
each block an ancestor of every later one. -/
theorem ffg_checkpointChain {cs : List (Checkpoint B)}
    (hS : 3 * stake w (slashable votes) < totalStake w)
    (hfin : ∀ c ∈ cs, Finalized T w votes c)
    (hsort : cs.Pairwise fun c c' => c.epoch ≤ c'.epoch) :
    cs.Pairwise fun c c' => T.anc c.block c'.block :=
  hsort.imp_of_mem fun hc hc' hle =>
    anc_of_kFinalized_of_justified (hfin _ hc).kFinalized (hfin _ hc').1 hle hS

/-- Two sets whose stakes sum to more than the total stake intersect. -/
theorem inter_nonempty_of_stake {S H : Finset V} (h : totalStake w < stake w S + stake w H) :
    (S ∩ H).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hu : stake w (S ∪ H) + stake w (S ∩ H) = stake w S + stake w H :=
    Finset.sum_union_inter
  rw [he] at hu
  have := stake_le_totalStake w (S ∪ H)
  simp [stake] at hu
  simp only [stake] at this h
  omega

/-- Justified checkpoints lie on honest chains. Let the validators of `H` be honest, hold
more than a third of the total stake, and vote only for epoch-boundary checkpoints of their
selected chains. Then every justified checkpoint other than genesis is the epoch-boundary
checkpoint of its epoch on the chain some honest validator selects at some time. -/
theorem ffg_justified_isCheckpoint {X : ChainTrace V B} {slot : B → ℕ} {E : ℕ} {H : Finset V}
    (hHon : ∀ v ∈ H, X.honest v) (hH : totalStake w < 3 * stake w H)
    (hvotes : HonestVotesOnChain X slot E votes) {c : Checkpoint B}
    (hc : Justified T w votes c) (hg : c ≠ genesisCheckpoint T) :
    ∃ v t, X.honest v ∧ IsCheckpointOf slot E (X.chain t v) c := by
  cases hc with
  | genesis => exact absurd rfl hg
  | @link s _ _ hl =>
    obtain ⟨v, hv⟩ := inter_nonempty_of_stake (w := w) (S := voters votes s c) (H := H)
      (by have := hl.2.2; omega)
    obtain ⟨hvs, hvH⟩ := Finset.mem_inter.1 hv
    obtain ⟨t, -, ht⟩ := hvotes _ (mem_voters.1 hvs) (hHon v hvH)
    exact ⟨v, t, hHon v hvH, ht⟩

/-- Finalized checkpoints lie on honest chains: under the hypotheses of
`ffg_justified_isCheckpoint`, every finalized checkpoint other than genesis is an
epoch-boundary checkpoint of the chain some honest validator selects at some time. -/
theorem ffg_finalized_isCheckpoint {X : ChainTrace V B} {slot : B → ℕ} {E : ℕ} {H : Finset V}
    (hHon : ∀ v ∈ H, X.honest v) (hH : totalStake w < 3 * stake w H)
    (hvotes : HonestVotesOnChain X slot E votes) {c : Checkpoint B}
    (hc : Finalized T w votes c) (hg : c ≠ genesisCheckpoint T) :
    ∃ v t, X.honest v ∧ IsCheckpointOf slot E (X.chain t v) c :=
  ffg_justified_isCheckpoint hHon hH hvotes hc.1 hg

end FFGInstance

/-! ### Concrete instances: the hypotheses are satisfiable -/

namespace Examples

open FFG.Examples

/-! #### FFG over a chain -/

/-- Four honest validators that select the chain `[1, 0]` (block `1` on genesis `0` of
`forkTree`) at all times. -/
def ffgTrace : ChainTrace (Fin 4) (Fin 3) where
  honest _ := True
  chain _ _ := [1, 0]

/-- The slot of a block of `forkTree`: its number. -/
def blockSlot : Fin 3 → ℕ := fun b => b.val

/-- Every party sees all votes of `honestVotes` at all times. -/
def ffgSeen : ℕ → Fin 4 → Finset (Vote (Fin 4) (Fin 3)) := fun _ _ => honestVotes

theorem ffgTrace_chainsInTree : ffgTrace.ChainsInTree forkTree := by
  intro _ _ _
  simp [ffgTrace, forkTree]

/-- The votes of `honestVotes` name epoch-boundary checkpoints of `[1, 0]`, with epochs of one
slot. -/
theorem honestVotes_onChain : HonestVotesOnChain ffgTrace blockSlot 1 honestVotes := by
  intro x hx _
  exact ⟨0, (show ∀ x ∈ honestVotes, IsCheckpointOf blockSlot 1 [1, 0] x.source ∧
    IsCheckpointOf blockSlot 1 [1, 0] x.target by decide) x hx⟩

/-- Every block finalized by `honestVotes` is block `0` or block `1`. -/
theorem honestVotes_justified_block {c : Checkpoint (Fin 3)}
    (hc : Justified forkTree unitStake honestVotes c) : c.block = 0 ∨ c.block = 1 := by
  cases hc with
  | genesis => exact Or.inl rfl
  | @link s _ _ hl =>
    obtain ⟨v, hv⟩ : (voters honestVotes s c).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have := hl.2.2
      rw [he, totalStake_unitStake] at this
      simp [stake] at this
    have hmem := mem_voters.1 hv
    have key : ∀ x ∈ honestVotes, x.target.block = 1 := by decide
    exact Or.inr (key _ hmem)

/-- FFG over the chain `[1, 0]`, with `honestVotes`, is a finality layer, and it finalizes the
checkpoint `(1, 1)`. All hypotheses of `ffg_positionRespecting` and
`ffg_finalized_isCheckpoint` hold: every party sees only cast votes, the slashable stake is
`0 < 4 / 3`, all four validators are honest with stake `4 > 4 / 3`, and honest votes name
epoch-boundary checkpoints of their chains. -/
theorem ffg_nonvacuous :
    ffgTrace.ChainsInTree forkTree ∧ HonestVotesOnChain ffgTrace blockSlot 1 honestVotes ∧
      (∀ t p, ffgSeen t p ⊆ honestVotes) ∧
      3 * stake unitStake (slashable honestVotes) < totalStake unitStake ∧
      totalStake unitStake < 3 * stake unitStake Finset.univ ∧
      ffgFinalization forkTree unitStake ffgSeen 0 0 1 1 ∧
      IsCheckpointOf blockSlot 1 (ffgTrace.chain 0 0) ⟨1, 1⟩ ∧
      FinalityLayer forkTree ffgTrace (ffgFinalization forkTree unitStake ffgSeen) := by
  have hseen : ∀ t p, ffgSeen t p ⊆ honestVotes := fun _ _ => subset_rfl
  have hS : 3 * stake unitStake (slashable honestVotes) < totalStake unitStake := by
    rw [honestVotes_slashable]; decide
  have hP := ffg_positionRespecting (T := forkTree) ffgTrace hseen hS
  refine ⟨ffgTrace_chainsInTree, honestVotes_onChain, hseen, hS, by decide,
    honestVotes_finalized, by decide, hP, hP.chainForming, hP.agreement, ?_⟩
  intro p t t' b i _ _ hb
  rcases honestVotes_justified_block hb.1 with h | h <;> simp_all [ffgTrace]

/-- Without the bound on the slashable stake agreement fails: with the votes `doubleVotes`,
whose slashable validators hold half of the stake, the conflicting checkpoints `(1, 1)` and
`(2, 1)` are both finalized. -/
theorem ffg_agreement_fails_doubleVotes :
    ¬ Agreement forkTree ffgTrace (ffgFinalization forkTree unitStake fun _ _ => doubleVotes) := by
  intro h
  rcases h 0 0 0 0 1 2 1 1 trivial trivial doubleVotes_finalized_conflicting.1
      doubleVotes_finalized_conflicting.2.1 with h' | h'
  · exact forkTree_conflicting.1 h'
  · exact forkTree_conflicting.2 h'

/-! #### Finality by depth on a growing chain -/

/-- The chain `[n, n - 1, …, 0]`. -/
def line : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (n + 1) :: line n

theorem length_line (n : ℕ) : (line n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [line, ih]

theorem mem_line {n b : ℕ} : b ∈ line n ↔ b ≤ n := by
  induction n with
  | zero => simp [line]
  | succ n ih => simp only [line, List.mem_cons, ih]; omega

theorem line_suffix {n m : ℕ} (h : n ≤ m) : line n <:+ line m := by
  induction m, h using Nat.le_induction with
  | base => exact List.suffix_refl _
  | succ m _ ih => exact ih.trans (List.suffix_cons _ _)

theorem drop_line {n i : ℕ} (h : i ≤ n) : (line n).drop i = line (n - i) := by
  induction i generalizing n with
  | zero => rfl
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [line, List.drop_succ_cons]
    rw [ih (by omega)]
    congr 1
    omega

/-- The block tree on `ℕ` ordered by `≤`: a single chain. -/
def lineTree : BlockTree ℕ where
  anc a b := a ≤ b
  genesis := 0
  anc_refl := Nat.le_refl
  anc_trans := Nat.le_trans

/-- One honest party whose chain at time `t` is `[t, …, 0]`. -/
def lineTrace : ChainTrace Unit ℕ where
  honest _ := True
  chain t _ := line t

/-- Blocks with an even number count as honest. -/
def evenBlock (b : ℕ) : Bool := b % 2 == 0

theorem lineTrace_chainsInTree : lineTrace.ChainsInTree lineTree := by
  intro _ t _
  induction t with
  | zero => simp [lineTrace, line]
  | succ n ih =>
    simp only [lineTrace, line, List.pairwise_cons] at ih ⊢
    exact ⟨fun b hb => by have := mem_line.1 hb; simp only [lineTree]; omega, ih⟩

theorem lineTrace_commonPrefix (k : ℕ) : lineTrace.CommonPrefix k :=
  fun _ _ _ _ _ _ h => (List.drop_suffix _ _).trans (line_suffix h)

theorem lineTrace_chainGrowth (s : ℕ) : lineTrace.ChainGrowth s s := by
  intro _ _ t t' _ _ h
  simp only [lineTrace, length_line]
  omega

/-- Every two consecutive blocks of `[t, …, 0]` contain an even one. -/
theorem lineTrace_chainQuality : lineTrace.ChainQuality evenBlock 2 1 := by
  intro _ t i _ h
  simp only [lineTrace, length_line] at h ⊢
  rw [drop_line (by omega)]
  obtain ⟨m, hm⟩ : ∃ m, t - i = m + 1 := ⟨t - i - 1, by omega⟩
  rw [hm]
  cases m with
  | zero => simp [line, evenBlock]
  | succ m =>
    simp only [line, List.take_succ_cons, List.take_zero, List.countP_cons, List.countP_nil,
      evenBlock]
    rcases Nat.mod_two_eq_zero_or_one (m + 1) with h2 | h2 <;> simp [h2, Nat.add_mod]

/-- `kDeep_of_traceGuard` applies to `lineTrace` with common prefix `2`, chain growth `(1, 1)`
and chain quality `(evenBlock, 2, 1)`, and at time `5` the block `3` is final at height `3`. -/
theorem kDeep_nonvacuous :
    lineTrace.TraceGuard lineTree 2 1 1 evenBlock 2 1 ∧ kDeep 2 lineTrace 5 () 3 3 ∧
      FinalityLayer lineTree lineTrace (kDeep 2 lineTrace) :=
  have hG : lineTrace.TraceGuard lineTree 2 1 1 evenBlock 2 1 :=
    ⟨lineTrace_chainsInTree, lineTrace_commonPrefix 2, lineTrace_chainGrowth 1,
      lineTrace_chainQuality⟩
  ⟨hG, ⟨[2, 1, 0], by decide, rfl⟩, (kDeep_of_traceGuard hG).1⟩

end Examples

end CatCryptCore.Consensus.Finality

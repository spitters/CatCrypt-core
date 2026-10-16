/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.FinalityExamples
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith

/-!
# Validity and chain-forming of Casper FFG over a chain

This file continues `CatCryptCore.Consensus.Finality` for Casper FFG run on top of a chain
whose selection rule is abstract (`ChainTrace`). Each party finalizes the checkpoints that are
finalized by the votes it has seen (`ffgFinalization`); honest validators vote only for
epoch-boundary checkpoints of the chain they select (`HonestVotesOnChain`).

Stake is natural-number valued and thresholds are stated without division. The honest
validators are a set `H` with `∀ v ∈ H, X.honest v`; the stake outside `H`,
`stake w (Finset.univ \ H)`, is the adversarial stake. Its share of the total stake `W` is
written `β`, so `stake w (Finset.univ \ H) ≤ β · W` in the rational statements.

## v-validity

A finalized checkpoint `c` comes with a supermajority link `c → c'`. Every honest voter of that
link voted with source `c`, so `c` is an epoch-boundary checkpoint of the chain it selected at
the time of its vote. The honest voters `S = voters votes c c' ∩ H` satisfy
`stake(voters) ≤ stake S + stake(univ \ H)`, which gives the exact bound

  `2 * W ≤ 3 * stake w S + 3 * stake w (Finset.univ \ H)`,

that is `stake S ≥ (2/3 - β) · W`. The bound needs no hypothesis on slashing and covers the
genesis checkpoint as well.

## Chain-forming

If the slashable validators of all cast votes hold less than a third of the stake (the bound of
`FFG.accountable_safety`), then the checkpoints finalized by honest parties, at any times, are
ordered by ancestry as by epoch, there is at most one per epoch, and every list of them sorted
by epoch is a chain of `T`. The bound follows from "adversarial or slashed stake below one
third" (`3 * stake w (slashable votes ∪ (Finset.univ \ H)) < W`), and in particular from
"honest validators are never slashable and the adversarial stake is below one third".

## Main results

* `finalized_validity`, `ffg_vValidity`: a finalized checkpoint is an epoch-boundary checkpoint
  of the selected chain of honest validators `S ⊆ H`, each at some time, with
  `2 * W ≤ 3 * stake w S + 3 * stake w (Finset.univ \ H)`.
* `ffg_vValidity_share`: the same bound as `(2/3 - β) · W ≤ stake w S`.
* `ffg_honestFinalized_chain`: under the slashing bound, the checkpoints finalized by honest
  parties respect epochs, are unique per epoch, and form a chain of `T` when sorted by epoch;
  FFG over the chain is position-respecting, chain-forming and in agreement.
* `ffg_honestFinalized_chain_of_adversarial`, `ffg_honestFinalized_chain_of_share`: the same
  under "honest validators are not slashable" and an adversarial stake (share `β`) below one
  third.
* `ffg_finalityValidity`: v-validity and chain-forming together.
* `Examples.ffgValidity_nonvacuous_allHonest`: all hypotheses hold on the instance
  `ffgTrace` with `H = univ` (`β = 0`).
* `Examples.ffgValidity_nonvacuous_adversary`: all hypotheses hold on a trace with one
  adversarial validator of four (`β = 1/4`) that double votes and is slashable; the checkpoint
  `(1, 1)` is finalized and lies on the chains of honest validators of stake at least `2`.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.Finality

open FFG

variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B]

/-! ### Checkpoints on chains -/

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
/-- The block of an epoch-boundary checkpoint of a chain is a block of that chain. -/
theorem IsCheckpointOf.mem {slot : B → ℕ} {E : ℕ} {C : List B} {c : Checkpoint B}
    (h : IsCheckpointOf slot E C c) : c.block ∈ C :=
  List.mem_of_find?_eq_some h

/-! ### Stake of honest voters -/

/-- The stake of `S` is at most the stake of `S ∩ H` plus the stake outside `H`. -/
theorem stake_le_inter_add_compl (w : V → ℕ) (S H : Finset V) :
    stake w S ≤ stake w (S ∩ H) + stake w (Finset.univ \ H) := by
  have hd : Disjoint (S ∩ H) (Finset.univ \ H) :=
    Finset.disjoint_left.2 fun _ ha hb => (Finset.mem_sdiff.1 hb).2 (Finset.mem_inter.1 ha).2
  have hsub : S ⊆ (S ∩ H) ∪ (Finset.univ \ H) := by
    intro v hv
    by_cases h : v ∈ H
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hv, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, h⟩)
  calc stake w S ≤ stake w ((S ∩ H) ∪ (Finset.univ \ H)) := stake_mono w hsub
    _ = stake w (S ∩ H) + stake w (Finset.univ \ H) := Finset.sum_union hd

variable {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
  {seen : ℕ → V → Finset (Vote V B)} {X : ChainTrace V B} {slot : B → ℕ} {E : ℕ}
  {H : Finset V}

/-- The honest voters of a supermajority link `s → c`, that is the voters in `H`, each select
at some time a chain of which `s` and `c` are epoch-boundary checkpoints, and they satisfy
`2 * W ≤ 3 * stake (voters ∩ H) + 3 * stake (univ \ H)`. -/
theorem link_validity (hHon : ∀ v ∈ H, X.honest v) (hvotes : HonestVotesOnChain X slot E votes)
    {s c : Checkpoint B} (hl : SupermajorityLink T w votes s c) :
    (∀ v ∈ voters votes s c ∩ H, ∃ t, IsCheckpointOf slot E (X.chain t v) s ∧
        IsCheckpointOf slot E (X.chain t v) c) ∧
      2 * totalStake w ≤
        3 * stake w (voters votes s c ∩ H) + 3 * stake w (Finset.univ \ H) := by
  refine ⟨fun v hv => ?_, ?_⟩
  · obtain ⟨hvs, hvH⟩ := Finset.mem_inter.1 hv
    exact hvotes _ (mem_voters.1 hvs) (hHon v hvH)
  · have := stake_le_inter_add_compl w (voters votes s c) H
    have := hl.2.2
    omega

/-! ### v-validity -/

/-- v-validity for a vote set. Let the validators of `H` be honest and let honest validators
vote only for epoch-boundary checkpoints of their selected chains. Every checkpoint `c`
finalized by `votes` is an epoch-boundary checkpoint of the chain selected at some time by
each validator of a set `S ⊆ H` with `2 * W ≤ 3 * stake w S + 3 * stake w (univ \ H)`. -/
theorem finalized_validity (hHon : ∀ v ∈ H, X.honest v)
    (hvotes : HonestVotesOnChain X slot E votes) {c : Checkpoint B}
    (hc : Finalized T w votes c) :
    ∃ S ⊆ H, (∀ v ∈ S, X.honest v ∧ ∃ t, IsCheckpointOf slot E (X.chain t v) c) ∧
      2 * totalStake w ≤ 3 * stake w S + 3 * stake w (Finset.univ \ H) := by
  obtain ⟨-, c', -, hl⟩ := hc
  obtain ⟨h₁, h₂⟩ := link_validity hHon hvotes hl
  refine ⟨voters votes c c' ∩ H, Finset.inter_subset_right, fun v hv => ?_, h₂⟩
  obtain ⟨t, ht, -⟩ := h₁ v hv
  exact ⟨hHon v (Finset.mem_inter.1 hv).2, t, ht⟩

/-- v-validity of FFG over the chain. Let the validators of `H` be honest, let honest
validators vote only for epoch-boundary checkpoints of their selected chains, and let every
honest party see only cast votes. If an honest party `p` finalizes the checkpoint `(b, e)` at
time `t`, then `(b, e)` is an epoch-boundary checkpoint of the chain selected at some time by
each validator of a set `S ⊆ H` of honest validators, `b` is on that chain, and
`2 * W ≤ 3 * stake w S + 3 * stake w (univ \ H)`. -/
theorem ffg_vValidity (hHon : ∀ v ∈ H, X.honest v) (hvotes : HonestVotesOnChain X slot E votes)
    (hseen : ∀ t p, X.honest p → seen t p ⊆ votes) {p : V} {t e : ℕ} {b : B}
    (hp : X.honest p) (hfin : ffgFinalization T w seen t p b e) :
    ∃ S ⊆ H, (∀ v ∈ S, X.honest v ∧ ∃ t', IsCheckpointOf slot E (X.chain t' v) ⟨b, e⟩ ∧
        b ∈ X.chain t' v) ∧
      2 * totalStake w ≤ 3 * stake w S + 3 * stake w (Finset.univ \ H) := by
  obtain ⟨S, hSH, hS, hb⟩ := finalized_validity hHon hvotes (Finalized.mono (hseen t p hp) hfin)
  refine ⟨S, hSH, fun v hv => ?_, hb⟩
  obtain ⟨hv, t', ht'⟩ := hS v hv
  exact ⟨hv, t', ht', ht'.mem⟩

/-- The natural-number bound of v-validity in terms of the adversarial share `β`: if
`2 * W ≤ 3 * s + 3 * a` and `a ≤ β · W`, then `(2/3 - β) · W ≤ s`. -/
theorem share_bound {W s a : ℕ} {β : ℚ} (h : 2 * W ≤ 3 * s + 3 * a) (hβ : (a : ℚ) ≤ β * W) :
    (2 / 3 - β) * W ≤ s := by
  have h' : ((2 * W : ℕ) : ℚ) ≤ ((3 * s + 3 * a : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- v-validity with the adversarial share `β`: under the hypotheses of `ffg_vValidity` and
`stake w (univ \ H) ≤ β · W`, a checkpoint `(b, e)` finalized by an honest party is an
epoch-boundary checkpoint of the selected chains of honest validators `S ⊆ H` holding at least
`(2/3 - β) · W`. -/
theorem ffg_vValidity_share (hHon : ∀ v ∈ H, X.honest v)
    (hvotes : HonestVotesOnChain X slot E votes) (hseen : ∀ t p, X.honest p → seen t p ⊆ votes)
    {β : ℚ} (hβ : (stake w (Finset.univ \ H) : ℚ) ≤ β * totalStake w) {p : V} {t e : ℕ} {b : B}
    (hp : X.honest p) (hfin : ffgFinalization T w seen t p b e) :
    ∃ S ⊆ H, (∀ v ∈ S, X.honest v ∧ ∃ t', IsCheckpointOf slot E (X.chain t' v) ⟨b, e⟩ ∧
        b ∈ X.chain t' v) ∧
      (2 / 3 - β) * totalStake w ≤ stake w S := by
  obtain ⟨S, hSH, hS, hb⟩ := ffg_vValidity hHon hvotes hseen hp hfin
  exact ⟨S, hSH, hS, share_bound hb hβ⟩

/-! ### Chain-forming -/

/-- The checkpoint `c` is finalized by an honest party: some honest `p` finalizes `c` with the
votes it has seen at some time `t`. -/
def HonestFinalized (T : BlockTree B) (w : V → ℕ) (X : ChainTrace V B)
    (seen : ℕ → V → Finset (Vote V B)) (c : Checkpoint B) : Prop :=
  ∃ p t, X.honest p ∧ Finalized T w (seen t p) c

/-- Honest validators are not slashable: no honest validator violates condition E1 or E2 in
`votes`. -/
def HonestUnslashable (X : ChainTrace V B) (votes : Finset (Vote V B)) : Prop :=
  ∀ v, X.honest v → v ∉ slashable votes

/-- If every honest party sees only cast votes, a checkpoint finalized by an honest party is
finalized by the cast votes. -/
theorem HonestFinalized.finalized (hseen : ∀ t p, X.honest p → seen t p ⊆ votes)
    {c : Checkpoint B} (hc : HonestFinalized T w X seen c) : Finalized T w votes c := by
  obtain ⟨p, t, hp, hc⟩ := hc
  exact Finalized.mono (hseen t p hp) hc

/-- Chain-forming of FFG over the chain. Let every honest party see only cast votes and let the
slashable validators of the cast votes hold less than a third of the total stake. Then:
checkpoints finalized by honest parties are ordered by ancestry as by epoch; two of them at the
same epoch are equal; every list of them sorted by epoch is a chain of `T`; and FFG over the
chain is position-respecting, chain-forming and in agreement. The proof is FFG's accountable
safety, `FFG.anc_of_kFinalized_of_justified` and `FFG.slashable_of_justified_same_epoch`. -/
theorem ffg_honestFinalized_chain (hseen : ∀ t p, X.honest p → seen t p ⊆ votes)
    (hS : 3 * stake w (slashable votes) < totalStake w) :
    (∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
        c.epoch ≤ c'.epoch → T.anc c.block c'.block) ∧
      (∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
        c.epoch = c'.epoch → c = c') ∧
      (∀ cs : List (Checkpoint B), (∀ c ∈ cs, HonestFinalized T w X seen c) →
        cs.Pairwise (fun c c' => c.epoch ≤ c'.epoch) →
        cs.Pairwise (fun c c' => T.anc c.block c'.block)) ∧
      PositionRespecting T X (ffgFinalization T w seen) ∧
      ChainForming T X (ffgFinalization T w seen) ∧
      Agreement T X (ffgFinalization T w seen) := by
  have hanc : ∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
      c.epoch ≤ c'.epoch → T.anc c.block c'.block := fun c c' hc hc' hle =>
    anc_of_kFinalized_of_justified (hc.finalized hseen).kFinalized (hc'.finalized hseen).1 hle hS
  have hP : PositionRespecting T X (ffgFinalization T w seen) :=
    fun p q t t' b b' i j hp hq hb hb' hij =>
      hanc ⟨b, i⟩ ⟨b', j⟩ ⟨p, t, hp, hb⟩ ⟨q, t', hq, hb'⟩ hij
  refine ⟨hanc, fun c c' hc hc' he => ?_,
    fun cs hcs hsort => hsort.imp_of_mem fun hc hc' hle => hanc _ _ (hcs _ hc) (hcs _ hc') hle,
    hP, hP.chainForming, hP.agreement⟩
  by_contra hne
  exact absurd (slashable_of_justified_same_epoch (hc.finalized hseen).1
    (hc'.finalized hseen).1 he hne) (by omega)

/-- If the adversarial or slashed validators, `slashable votes ∪ (univ \ H)`, hold less than a
third of the total stake, so do the slashable validators. -/
theorem slashable_lt_of_union (hS : 3 * stake w (slashable votes ∪ (Finset.univ \ H)) <
    totalStake w) : 3 * stake w (slashable votes) < totalStake w := by
  have := stake_mono w (Finset.subset_union_left (s₁ := slashable votes)
    (s₂ := Finset.univ \ H))
  omega

/-- If the validators of `H` are honest and honest validators are not slashable, the slashable
validators lie outside `H`. -/
theorem slashable_subset_compl (hHon : ∀ v ∈ H, X.honest v) (hU : HonestUnslashable X votes) :
    slashable votes ⊆ Finset.univ \ H := fun v hv =>
  Finset.mem_sdiff.2 ⟨Finset.mem_univ v, fun hvH => hU v (hHon v hvH) hv⟩

/-- Chain-forming under the adversarial bound: if the validators of `H` are honest, honest
validators are not slashable, every honest party sees only cast votes, and the stake outside
`H` is less than a third of the total stake, then the conclusions of
`ffg_honestFinalized_chain` hold. -/
theorem ffg_honestFinalized_chain_of_adversarial (hHon : ∀ v ∈ H, X.honest v)
    (hU : HonestUnslashable X votes) (hseen : ∀ t p, X.honest p → seen t p ⊆ votes)
    (hA : 3 * stake w (Finset.univ \ H) < totalStake w) :
    (∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
        c.epoch ≤ c'.epoch → T.anc c.block c'.block) ∧
      (∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
        c.epoch = c'.epoch → c = c') ∧
      (∀ cs : List (Checkpoint B), (∀ c ∈ cs, HonestFinalized T w X seen c) →
        cs.Pairwise (fun c c' => c.epoch ≤ c'.epoch) →
        cs.Pairwise (fun c c' => T.anc c.block c'.block)) ∧
      PositionRespecting T X (ffgFinalization T w seen) ∧
      ChainForming T X (ffgFinalization T w seen) ∧
      Agreement T X (ffgFinalization T w seen) := by
  refine ffg_honestFinalized_chain hseen ?_
  have := stake_mono w (slashable_subset_compl hHon hU)
  omega

/-- An adversarial share `β < 1/3` of a positive total stake gives the natural-number bound
`3 * stake w (univ \ H) < W`. -/
theorem adversarial_lt_of_share {β : ℚ} (hβ : (stake w (Finset.univ \ H) : ℚ) ≤ β * totalStake w)
    (hβ3 : β < 1 / 3) (hW : 0 < totalStake w) :
    3 * stake w (Finset.univ \ H) < totalStake w := by
  have hW' : (0 : ℚ) < totalStake w := by exact_mod_cast hW
  have : (3 * stake w (Finset.univ \ H) : ℚ) < totalStake w := by nlinarith
  exact_mod_cast this

/-- Chain-forming with the adversarial share: the conclusions of `ffg_honestFinalized_chain`
hold if the validators of `H` are honest, honest validators are not slashable, every honest
party sees only cast votes, the total stake is positive and the stake outside `H` is at most
`β · W` with `β < 1/3`. -/
theorem ffg_honestFinalized_chain_of_share (hHon : ∀ v ∈ H, X.honest v)
    (hU : HonestUnslashable X votes) (hseen : ∀ t p, X.honest p → seen t p ⊆ votes)
    {β : ℚ} (hβ : (stake w (Finset.univ \ H) : ℚ) ≤ β * totalStake w) (hβ3 : β < 1 / 3)
    (hW : 0 < totalStake w) :
    (∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
        c.epoch ≤ c'.epoch → T.anc c.block c'.block) ∧
      (∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
        c.epoch = c'.epoch → c = c') ∧
      (∀ cs : List (Checkpoint B), (∀ c ∈ cs, HonestFinalized T w X seen c) →
        cs.Pairwise (fun c c' => c.epoch ≤ c'.epoch) →
        cs.Pairwise (fun c c' => T.anc c.block c'.block)) ∧
      PositionRespecting T X (ffgFinalization T w seen) ∧
      ChainForming T X (ffgFinalization T w seen) ∧
      Agreement T X (ffgFinalization T w seen) :=
  ffg_honestFinalized_chain_of_adversarial hHon hU hseen (adversarial_lt_of_share hβ hβ3 hW)

/-! ### v-validity and chain-forming together -/

/-- FFG over the chain: v-validity and chain-forming. Let the validators of `H` be honest, let
honest validators vote only for epoch-boundary checkpoints of their selected chains and never
violate a slashing condition, let every honest party see only cast votes, and let the stake
outside `H` be less than a third of the total stake. Then every checkpoint finalized by an
honest party is an epoch-boundary checkpoint of the selected chains of honest validators
`S ⊆ H` with `2 * W ≤ 3 * stake w S + 3 * stake w (univ \ H)`, and the checkpoints finalized by
honest parties are ordered by ancestry as by epoch, are unique per epoch, and form a chain of
`T` when sorted by epoch. -/
theorem ffg_finalityValidity (hHon : ∀ v ∈ H, X.honest v)
    (hvotes : HonestVotesOnChain X slot E votes) (hU : HonestUnslashable X votes)
    (hseen : ∀ t p, X.honest p → seen t p ⊆ votes)
    (hA : 3 * stake w (Finset.univ \ H) < totalStake w) :
    (∀ c, HonestFinalized T w X seen c →
        ∃ S ⊆ H, (∀ v ∈ S, X.honest v ∧ ∃ t, IsCheckpointOf slot E (X.chain t v) c) ∧
          2 * totalStake w ≤ 3 * stake w S + 3 * stake w (Finset.univ \ H)) ∧
      (∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
        c.epoch ≤ c'.epoch → T.anc c.block c'.block) ∧
      (∀ c c', HonestFinalized T w X seen c → HonestFinalized T w X seen c' →
        c.epoch = c'.epoch → c = c') ∧
      (∀ cs : List (Checkpoint B), (∀ c ∈ cs, HonestFinalized T w X seen c) →
        cs.Pairwise (fun c c' => c.epoch ≤ c'.epoch) →
        cs.Pairwise (fun c c' => T.anc c.block c'.block)) := by
  obtain ⟨h₁, h₂, h₃, -⟩ := ffg_honestFinalized_chain_of_adversarial hHon hU hseen hA
  exact ⟨fun c hc => finalized_validity hHon hvotes (hc.finalized hseen), h₁, h₂, h₃⟩

/-! ### Concrete instances: the hypotheses are satisfiable -/

namespace Examples

open FFG.Examples

/-! #### All validators honest (`β = 0`) -/

/-- On the instance `ffgTrace` of `Finality.Examples` with `honestVotes` and `H = univ`, all
hypotheses of `ffg_finalityValidity` and `ffg_vValidity_share` (with `β = 0`) hold, and the checkpoint
`(1, 1)` is finalized by an honest party. -/
theorem ffgValidity_nonvacuous_allHonest :
    (∀ v ∈ (Finset.univ : Finset (Fin 4)), ffgTrace.honest v) ∧
      HonestVotesOnChain ffgTrace blockSlot 1 honestVotes ∧
      HonestUnslashable ffgTrace honestVotes ∧
      (∀ t p, ffgTrace.honest p → ffgSeen t p ⊆ honestVotes) ∧
      3 * stake unitStake (Finset.univ \ Finset.univ) < totalStake unitStake ∧
      (stake unitStake (Finset.univ \ Finset.univ) : ℚ) ≤ 0 * totalStake unitStake ∧
      HonestFinalized forkTree unitStake ffgTrace ffgSeen ⟨1, 1⟩ := by
  refine ⟨fun _ _ => trivial, honestVotes_onChain, ?_, fun _ _ _ => subset_rfl, by decide,
    by simp [stake], 0, 0, trivial, honestVotes_finalized⟩
  intro v _
  simp [honestVotes_slashable]

/-! #### One adversarial validator of four (`β = 1/4`) -/

/-- Validators `0, 1, 2` are honest and validator `3` is adversarial; every party selects the
chain `[1, 0]` at all times. -/
def advTrace : ChainTrace (Fin 4) (Fin 3) where
  honest v := v ≠ 3
  chain _ _ := [1, 0]

/-- The honest validators of `advTrace`. -/
def advHonest : Finset (Fin 4) := {0, 1, 2}

/-- The votes of `honestVotes` and a double vote of validator `3` for the off-chain checkpoint
`(2, 1)`. -/
def advVotes : Finset (Vote (Fin 4) (Fin 3)) := insert (vote 3 0 0 2 1) honestVotes

/-- Every party sees all votes of `advVotes` at all times. -/
def advSeen : ℕ → Fin 4 → Finset (Vote (Fin 4) (Fin 3)) := fun _ _ => advVotes

/-- The slashable set of `advVotes` is `{3}`: the adversary violates E1. -/
theorem advVotes_slashable : slashable advVotes = {3} := by decide

theorem advVotes_finalized : Finalized forkTree unitStake advVotes ⟨1, 1⟩ :=
  finalized_of_links (c' := ⟨1, 2⟩) (by decide) rfl (by decide)

/-- The votes of the honest validators of `advTrace` name epoch-boundary checkpoints of
`[1, 0]`, with epochs of one slot. -/
theorem advVotes_onChain : HonestVotesOnChain advTrace blockSlot 1 advVotes := by
  intro x hx hh
  exact ⟨0, (show ∀ x ∈ advVotes, x.validator ≠ 3 →
    IsCheckpointOf blockSlot 1 [1, 0] x.source ∧ IsCheckpointOf blockSlot 1 [1, 0] x.target by
      decide) x hx hh⟩

/-- On `advTrace` with `advVotes` and `H = {0, 1, 2}`, all hypotheses of `ffg_finalityValidity`
and of `ffg_honestFinalized_chain_of_share` with `β = 1/4` hold, while the adversary is
slashable; the checkpoint `(1, 1)` is finalized by an honest party, and the honest validators
on whose chains it lies hold stake at least `2 = ⌈(2/3 - 1/4) · 4⌉`. -/
theorem ffgValidity_nonvacuous_adversary :
    (∀ v ∈ advHonest, advTrace.honest v) ∧
      HonestVotesOnChain advTrace blockSlot 1 advVotes ∧
      HonestUnslashable advTrace advVotes ∧
      (∀ t p, advTrace.honest p → advSeen t p ⊆ advVotes) ∧
      3 * stake unitStake (Finset.univ \ advHonest) < totalStake unitStake ∧
      (stake unitStake (Finset.univ \ advHonest) : ℚ) ≤ 1 / 4 * totalStake unitStake ∧
      slashable advVotes = {3} ∧
      HonestFinalized forkTree unitStake advTrace advSeen ⟨1, 1⟩ ∧
      ∃ S ⊆ advHonest, (∀ v ∈ S, advTrace.honest v ∧
          ∃ t, IsCheckpointOf blockSlot 1 (advTrace.chain t v) ⟨1, 1⟩) ∧
        2 ≤ stake unitStake S := by
  have hHon : ∀ v ∈ advHonest, advTrace.honest v := by
    show ∀ v ∈ advHonest, v ≠ 3
    decide
  have hU : HonestUnslashable advTrace advVotes := by
    intro v hv
    rw [advVotes_slashable, Finset.mem_singleton]
    exact hv
  have hA : stake unitStake (Finset.univ \ advHonest) = 1 := by decide
  have hfin : HonestFinalized forkTree unitStake advTrace advSeen ⟨1, 1⟩ :=
    ⟨0, 0, (by decide : (0 : Fin 4) ≠ 3), advVotes_finalized⟩
  obtain ⟨S, hSH, hS, hb⟩ := finalized_validity hHon advVotes_onChain advVotes_finalized
  refine ⟨hHon, advVotes_onChain, hU, fun _ _ _ => subset_rfl, ?_, ?_, advVotes_slashable,
    hfin, S, hSH, hS, ?_⟩
  · rw [hA, totalStake_unitStake]; decide
  · rw [hA, totalStake_unitStake]; norm_num
  · rw [hA, totalStake_unitStake] at hb; omega

end Examples

end CatCryptCore.Consensus.Finality

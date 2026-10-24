/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.FinalityExamples
public import Mathlib.Tactic.Ring

/-!
# Casper FFG over a chain: the finalized checkpoint stays close to the tip

This file proves Δ-updatedness for Casper FFG run on top of a chain whose selection rule is
abstract (`ChainTrace` of `CatCryptCore.Consensus.Finality`): after the
global stabilization time `GST`, with honest validators holding at least two thirds of the
stake, every honest party has a finalized checkpoint that is an epoch-boundary checkpoint of
its selected chain and lies at most `3 E + σ + d + Δ` slots behind the current slot.

## Execution model

An execution is observed at phases `j : ℕ`; `now j` is the slot of phase `j` and
`X.chain j p` is the chain (newest block first) that party `p` selects at phase `j`. Blocks
carry a slot `slot b`; epochs have `E` slots. Votes are broadcast at phases (`cast j`) and
party `p` has received `seen j p` at phase `j`. All hypotheses are required only up to a
horizon phase `hz`, since the underlying chain properties are established for finitely many
phases (`CatCryptCore.Consensus.PoSNSB.Good`).

## Hypotheses on the chain (`SlotChainHyp`)

* `ChainTrace.SlotCommonPrefix now slot d hz`: for honest `p`, `q`, phases `j ≤ j' ≤ hz` and a
  slot `s` with `s + d ≤ now j`, the blocks of slot at most `s` of the chain of `p` at `j` form
  a suffix of the chain of `q` at `j'`. This is the form of common prefix proved in PoS-NSB
  (`PoSNSB.CPGood`, pruning by slot with `prune_time`).
* `ChainTrace.SlotChainGrowth now slot σ hz`: every window of `σ` consecutive slots that ends
  at or before the current slot contains a block of the chain of every honest party
  (chain growth in slot form: at least one block per `σ` slots; existential chain quality of
  Ouroboros Genesis without the honesty requirement).
* honest chains are ordered by the ancestor relation of the block tree `T`, have strictly
  decreasing slots, and contain the genesis block, of slot `0`; the clock `now` is monotone.

The length form of chain growth (`ChainTrace.ChainGrowth`) is not used: the
epoch-boundary checkpoint of epoch `e` is defined by slots, and it is fixed once some block
of the chain has a slot in `(e E, now - d]`, which is what `SlotChainGrowth` provides.

## The honest voting schedule (`VoteHyp`)

From a vote history `pre`, cast up to the first round, and a checkpoint `j₀` justified in it,
the honest validators `H` run rounds `r = 0, 1, …` at phases `ρ r` of slot
`τ₀ + r (2 E)`. In round `r` every validator of `H` casts the two votes of
`FFG.livenessVotes`: from the justified checkpoint `j_r` to the epoch-boundary checkpoint of
the new epoch `e_r = FFG.livenessEpoch`, and from that checkpoint to the epoch-boundary
checkpoint of epoch `e_r + 1`, both read off the selected chain at phase `ρ r`
(`schedule`, `roundVotes`). The next round starts from the new checkpoint. All votes have
epoch-boundary checkpoints of the voter's chain as source and target, so the honest votes
follow the voting rule `HonestVotesOnChain` (proved in `roundVotes_onChain`).

The extra hypothesis of `FFG.plausible_liveness` (every honest vote has its source at an epoch
not above that of the justified checkpoint) is not a consequence of the execution model for
the votes cast before the schedule starts: it is the hypothesis `pre_sources` of
`VoteHyp`, together with `pre_unslashable` (no honest validator is slashable in `pre`) and
`pre_justified`. For the votes of the schedule it is proved (`schedule_spec`). With
`pre = ∅` and `j₀` the genesis checkpoint the three hold trivially, as in the instance
`Examples.updated_nonvacuous`.

Synchrony after `GST`: a vote cast at phase `j` is received by every honest party at every
phase `t ≥ j` with `now t ≥ max (now j) GST + Δ`.

## Main results

* `boundary_settled`: under slot common prefix and slot chain growth, the epoch-boundary block
  of an epoch `e` with `e E + σ + d ≤ now j` is the same on the chain of every honest party at
  every phase from `j` to the horizon.
* `schedule_spec`: in every round the checkpoint `j_r` is justified by the honest votes, every
  honest vote has its source at an epoch at most that of `j_r`, no validator of `H` is
  slashable, and `e_r = e₀ + 2 r`.
* `roundVotes_onChain`: the votes of every round within the horizon follow the voting rule
  `HonestVotesOnChain`.
* `UpdatedHyp`: `VoteHyp` together with `SlotChainHyp`.
* `finality_updated`: Δ-updatedness. At every phase `t ≤ hz` with `now t ≥ τ₀ + Δ`, every
  honest party `p` has received votes finalizing a checkpoint `c` that is the epoch-boundary
  checkpoint of its epoch on the chain of `p` and satisfies
  `now t ≤ c.epoch * E + (τ₀ + 2 E + Δ - e₀ E)`.
* `finality_updated_start`: with the earliest start `τ₀ = (e₀ + 1) E + σ + d` the lag is at
  most `3 E + σ + d + Δ` slots; `finality_updated_tip` states the bound for every block of the
  chain, in particular its tip, when blocks have slots at most the current slot.
* `Examples.updated_nonvacuous`: all hypotheses hold on a chain with one block per slot, one
  validator, `E = 1`, `σ = 1`, `d = 0`, `Δ = 1`, `GST = 0`.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.Finality

open FFG

/-! ### Lists -/

section Lists

variable {B : Type*}

/-- Searching a filtered list for an element satisfying a stronger predicate gives the same
result as searching the list. -/
theorem find?_filter_of_imp {p q : B → Bool} (h : ∀ x, p x = true → q x = true) (L : List B) :
    (L.filter q).find? p = L.find? p := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    by_cases hp : p x = true
    · simp [h x hp, hp]
    · by_cases hq : q x = true <;> simp [hp, hq, ih]

/-- On a chain ordered by the ancestor relation, the newest block of slot at most `s₁` is an
ancestor of the newest block of slot at most `s₂ ≥ s₁`. -/
theorem anc_of_find?_le {T : BlockTree B} {slot : B → ℕ} {C : List B}
    (hT : C.Pairwise fun b b' => T.anc b' b) {s₁ s₂ : ℕ} {b₁ b₂ : B} (hs : s₁ ≤ s₂)
    (h₁ : C.find? (fun b => decide (slot b ≤ s₁)) = some b₁)
    (h₂ : C.find? (fun b => decide (slot b ≤ s₂)) = some b₂) : T.anc b₁ b₂ := by
  induction C with
  | nil => simp at h₁
  | cons x C ih =>
    rw [List.pairwise_cons] at hT
    by_cases hx₁ : slot x ≤ s₁
    · have hx₂ : slot x ≤ s₂ := hx₁.trans hs
      simp only [List.find?_cons, hx₁, hx₂, decide_true, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      exact T.anc_refl _
    · simp only [List.find?_cons, hx₁, decide_false] at h₁
      by_cases hx₂ : slot x ≤ s₂
      · simp only [List.find?_cons, hx₂, decide_true, Option.some.injEq] at h₂
        subst h₂
        exact hT.1 b₁ (List.mem_of_find?_eq_some h₁)
      · simp only [List.find?_cons, hx₂, decide_false] at h₂
        exact ih hT.2 h₁ h₂

end Lists

/-! ### Chains with slots -/

namespace ChainTrace

variable {Party Blk : Type*} (X : ChainTrace Party Blk)

/-- Common prefix by slots with parameter `d`, up to phase `hz`: for honest `p`, `q`, phases
`j ≤ j' ≤ hz` and a slot `s` with `s + d ≤ now j`, the blocks of slot at most `s` of the chain
of `p` at `j` form a suffix of the chain of `q` at `j'`. -/
def SlotCommonPrefix (now : ℕ → ℕ) (slot : Blk → ℕ) (d hz : ℕ) : Prop :=
  ∀ p q j j' s, X.honest p → X.honest q → j ≤ j' → j' ≤ hz → s + d ≤ now j →
    (X.chain j p).filter (fun b => decide (slot b ≤ s)) <:+ X.chain j' q

/-- Chain growth in slot form with window `σ`, up to phase `hz`: for honest `p` and phases
`j ≤ hz`, every window `(a, a + σ]` of slots with `a + σ ≤ now j` contains the slot of a block
of the chain of `p` at `j`. -/
def SlotChainGrowth (now : ℕ → ℕ) (slot : Blk → ℕ) (σ hz : ℕ) : Prop :=
  ∀ p j a, X.honest p → j ≤ hz → a + σ ≤ now j →
    ∃ b ∈ X.chain j p, a < slot b ∧ slot b ≤ a + σ

end ChainTrace

/-- The hypotheses on the honest chains up to phase `hz`: a monotone clock, chains ordered by
the ancestor relation of `T` with strictly decreasing slots and containing the genesis block
of slot `0`, common prefix by slots with parameter `d` and chain growth in slot form with
window `σ`. -/
structure SlotChainHyp {Party Blk : Type*} (T : BlockTree Blk) (X : ChainTrace Party Blk)
    (now : ℕ → ℕ) (slot : Blk → ℕ) (d σ hz : ℕ) : Prop where
  now_mono : Monotone now
  inTree : ∀ j p, X.honest p → j ≤ hz → (X.chain j p).Pairwise fun b b' => T.anc b' b
  decreasing : ∀ j p, X.honest p → j ≤ hz → (X.chain j p).Pairwise fun b b' => slot b' < slot b
  genesis_mem : ∀ j p, X.honest p → j ≤ hz → T.genesis ∈ X.chain j p
  genesis_slot : slot T.genesis = 0
  commonPrefix : X.SlotCommonPrefix now slot d hz
  growth : X.SlotChainGrowth now slot σ hz

section Settled

variable {Party Blk : Type*} {T : BlockTree Blk} {X : ChainTrace Party Blk} {now : ℕ → ℕ}
  {slot : Blk → ℕ} {d σ hz : ℕ}

/-- Settled boundaries. Let `s + σ + d ≤ now j`. Then the newest block of slot at most `s` is
the same on the chain of every honest party at every phase from `j` to `hz`. -/
theorem find?_settled (hX : SlotChainHyp T X now slot d σ hz) {p q : Party} {j j' s : ℕ}
    (hp : X.honest p) (hq : X.honest q) (hjj : j ≤ j') (hj' : j' ≤ hz) (hs : s + σ + d ≤ now j) :
    (X.chain j' q).find? (fun b => decide (slot b ≤ s)) =
      (X.chain j p).find? (fun b => decide (slot b ≤ s)) := by
  obtain ⟨b, hb, hsb, hbs⟩ := hX.growth p j s hp (hjj.trans hj') (by omega)
  have hF := hX.commonPrefix p q j j' (now j - d) hp hq hjj hj' (by omega)
  obtain ⟨Y, hY⟩ := hF
  have hbF : b ∈ (X.chain j p).filter (fun b => decide (slot b ≤ now j - d)) :=
    List.mem_filter.2 ⟨hb, by simp only [decide_eq_true_eq]; omega⟩
  have hdec := hX.decreasing j' q hq hj'
  rw [← hY, List.pairwise_append] at hdec
  have hYn : Y.find? (fun b => decide (slot b ≤ s)) = none := by
    rw [List.find?_eq_none]
    intro y hy
    have := hdec.2.2 y hy b hbF
    simp only [decide_eq_true_eq]
    omega
  rw [← hY, List.find?_append, hYn, Option.none_or]
  exact find?_filter_of_imp (fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega) _

end Settled

/-! ### Epoch-boundary blocks -/

section Boundary

variable {Party B : Type*}

/-- The epoch-boundary block of epoch `e` on the chain `C`, or `g` if there is none. -/
def boundaryBlock (slot : B → ℕ) (E : ℕ) (g : B) (C : List B) (e : ℕ) : B :=
  (epochBoundary slot E C e).getD g

/-- If the chain contains a block `g` of slot `0`, the epoch-boundary block of every epoch
exists. -/
theorem epochBoundary_eq_boundaryBlock {slot : B → ℕ} {E : ℕ} {C : List B} {g : B}
    (hg : g ∈ C) (hs : slot g = 0) (e : ℕ) :
    epochBoundary slot E C e = some (boundaryBlock slot E g C e) := by
  obtain ⟨b, hb⟩ : ∃ b, epochBoundary slot E C e = some b :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨g, hg, by simp [hs]⟩)
  simp [boundaryBlock, hb]

variable {T : BlockTree B} {X : ChainTrace Party B} {now : ℕ → ℕ} {slot : B → ℕ}
  {d σ hz E : ℕ}

/-- Settled epoch boundaries: if `e E + σ + d ≤ now j`, the epoch-boundary checkpoint of
epoch `e` is the same on the chain of every honest party at every phase from `j` to `hz`. -/
theorem boundary_settled (hX : SlotChainHyp T X now slot d σ hz) {p q : Party} {j j' e : ℕ}
    (hp : X.honest p) (hq : X.honest q) (hjj : j ≤ j') (hj' : j' ≤ hz)
    (he : e * E + σ + d ≤ now j) :
    epochBoundary slot E (X.chain j' q) e =
      some (boundaryBlock slot E T.genesis (X.chain j p) e) := by
  rw [← epochBoundary_eq_boundaryBlock (hX.genesis_mem j p hp (hjj.trans hj')) hX.genesis_slot]
  exact find?_settled hX hp hq hjj hj' he

/-- On the chain of an honest party, the epoch-boundary block of an epoch is an ancestor of
the epoch-boundary block of every later epoch. -/
theorem anc_boundaryBlock (hX : SlotChainHyp T X now slot d σ hz) {p : Party} {j e e' : ℕ}
    (hp : X.honest p) (hj : j ≤ hz) (hee : e ≤ e') :
    T.anc (boundaryBlock slot E T.genesis (X.chain j p) e)
      (boundaryBlock slot E T.genesis (X.chain j p) e') :=
  anc_of_find?_le (hX.inTree j p hp hj) (Nat.mul_le_mul_right E hee)
    (epochBoundary_eq_boundaryBlock (hX.genesis_mem j p hp hj) hX.genesis_slot e)
    (epochBoundary_eq_boundaryBlock (hX.genesis_mem j p hp hj) hX.genesis_slot e')

end Boundary

/-! ### The honest voting schedule -/

section Extend

variable {B : Type*}

open Classical in
/-- A descendant function built from a family of blocks `f e`: the block `f e` if `b` is an
ancestor of it, and `b` otherwise. -/
noncomputable def extendTo (T : BlockTree B) (f : ℕ → B) (b : B) (e : ℕ) : B :=
  if T.anc b (f e) then f e else b

theorem anc_extendTo (T : BlockTree B) (f : ℕ → B) (b : B) (e : ℕ) :
    T.anc b (extendTo T f b e) := by
  unfold extendTo
  split_ifs with h
  exacts [h, T.anc_refl b]

theorem extendTo_of_anc {T : BlockTree B} {f : ℕ → B} {b : B} {e : ℕ} (h : T.anc b (f e)) :
    extendTo T f b e = f e :=
  ite_eq_left h

end Extend

section Schedule

variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B]

/-- The honest liveness schedule for the descendant functions `D r`: after `r` rounds, the
vote set (the history `pre` and the votes of rounds `0, …, r - 1`) and the justified checkpoint
from which round `r` starts. Round `r` adds `livenessVotes H (D r)`. -/
noncomputable def schedule (H : Finset V) (D : ℕ → B → ℕ → B) (pre : Finset (Vote V B))
    (j₀ : Checkpoint B) : ℕ → Finset (Vote V B) × Checkpoint B
  | 0 => (pre, j₀)
  | r + 1 =>
    ((schedule H D pre j₀ r).1 ∪
        livenessVotes H (D r) (schedule H D pre j₀ r).1 (schedule H D pre j₀ r).2,
      livenessTarget (D r) (schedule H D pre j₀ r).1 (schedule H D pre j₀ r).2)

/-- The votes of `H` in round `r` of the schedule. -/
noncomputable def roundVotes (H : Finset V) (D : ℕ → B → ℕ → B) (pre : Finset (Vote V B))
    (j₀ : Checkpoint B) (r : ℕ) : Finset (Vote V B) :=
  livenessVotes H (D r) (schedule H D pre j₀ r).1 (schedule H D pre j₀ r).2

/-- The epoch of the checkpoint finalized in round `r`. -/
noncomputable def roundEpoch (H : Finset V) (D : ℕ → B → ℕ → B) (pre : Finset (Vote V B))
    (j₀ : Checkpoint B) (r : ℕ) : ℕ :=
  livenessEpoch (schedule H D pre j₀ r).1 (schedule H D pre j₀ r).2

omit [Fintype V] in
theorem schedule_succ (H : Finset V) (D : ℕ → B → ℕ → B) (pre : Finset (Vote V B))
    (j₀ : Checkpoint B) (r : ℕ) :
    schedule H D pre j₀ (r + 1) =
      ((schedule H D pre j₀ r).1 ∪ roundVotes H D pre j₀ r,
        livenessTarget (D r) (schedule H D pre j₀ r).1 (schedule H D pre j₀ r).2) :=
  rfl

omit [Fintype V] in
/-- Every vote of `livenessVotes H d votes j` has source `j` and target
`livenessTarget d votes j`, or source `livenessTarget d votes j` and target
`livenessNext d votes j`. -/
theorem mem_livenessVotes {H : Finset V} {d : B → ℕ → B} {votes : Finset (Vote V B)}
    {j : Checkpoint B} {x : Vote V B} (hx : x ∈ livenessVotes H d votes j) :
    x.validator ∈ H ∧
      ((x.source = j ∧ x.target = livenessTarget d votes j) ∨
        (x.source = livenessTarget d votes j ∧ x.target = livenessNext d votes j)) := by
  rcases Finset.mem_union.1 hx with hx | hx <;> obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
  · exact ⟨hv, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨hv, Or.inr ⟨rfl, rfl⟩⟩

variable {T : BlockTree B} {w : V → ℕ} {H : Finset V} {D : ℕ → B → ℕ → B}
  {pre : Finset (Vote V B)} {j₀ : Checkpoint B}

/-- The schedule is driven by plausible liveness. If `H` holds at least two thirds of the
stake and is nonempty, every `D r` is a descendant function, `j₀` is justified by `pre`, the
votes of `H` in `pre` have sources at epochs at most `j₀.epoch`, and no validator of `H` is
slashable in `pre`, then after every number `r` of rounds: the starting checkpoint is
justified, the votes of `H` have sources at epochs at most its epoch, no validator of `H` is
slashable, and the epoch of round `r` is `livenessEpoch pre j₀ + 2 r`. -/
theorem schedule_spec (hD : ∀ r b e, T.anc b (D r b e)) (hH : 2 * totalStake w ≤ 3 * stake w H)
    (hne : H.Nonempty) (hj₀ : Justified T w pre j₀)
    (hsrc : ∀ x ∈ pre, x.validator ∈ H → x.source.epoch ≤ j₀.epoch)
    (hhon : slashable pre ∩ H = ∅) (r : ℕ) :
    Justified T w (schedule H D pre j₀ r).1 (schedule H D pre j₀ r).2 ∧
      (∀ x ∈ (schedule H D pre j₀ r).1, x.validator ∈ H →
        x.source.epoch ≤ (schedule H D pre j₀ r).2.epoch) ∧
      slashable (schedule H D pre j₀ r).1 ∩ H = ∅ ∧
      roundEpoch H D pre j₀ r = livenessEpoch pre j₀ + 2 * r := by
  induction r with
  | zero => exact ⟨hj₀, hsrc, hhon, rfl⟩
  | succ r ih =>
    obtain ⟨hJ, hS, hU, hE⟩ := ih
    set votes := (schedule H D pre j₀ r).1 with hvotes
    set j := (schedule H D pre j₀ r).2 with hj
    obtain ⟨-, hje, hlt, hfin, hU'⟩ := plausible_liveness (D r) (hD r) hH hJ hS hU
    rw [schedule_succ]
    refine ⟨hfin.1, ?_, hU', ?_⟩
    · intro x hx hxH
      rcases Finset.mem_union.1 hx with hx | hx
      · exact (hS x hx hxH).trans hje.le
      · rcases (mem_livenessVotes hx).2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
        · exact hje.le
    · obtain ⟨v, hv⟩ := hne
      have hmem : (⟨v, livenessTarget (D r) votes j, livenessNext (D r) votes j⟩ : Vote V B) ∈
          votes ∪ roundVotes H D pre j₀ r :=
        Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv))
      have hsup : ((votes ∪ roundVotes H D pre j₀ r).sup fun x => x.target.epoch) =
          livenessEpoch votes j + 1 := by
        refine le_antisymm (Finset.sup_le fun x hx => ?_)
          (Finset.le_sup_of_le hmem (le_of_eq rfl))
        rcases Finset.mem_union.1 hx with hx | hx
        · exact (hlt x hx).le.trans (Nat.le_succ _)
        · rcases (mem_livenessVotes hx).2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
          · exact Nat.le_succ _
          · exact le_rfl
      have hE' : roundEpoch H D pre j₀ r = livenessEpoch votes j := rfl
      have key : roundEpoch H D pre j₀ (r + 1) = livenessEpoch votes j + 2 := by
        show max (livenessTarget (D r) votes j).epoch
          ((votes ∪ roundVotes H D pre j₀ r).sup fun x => x.target.epoch) + 1 = _
        rw [hsup]
        simp only [livenessTarget]
        omega
      omega

end Schedule

/-! ### Δ-updatedness -/

section Updated

variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B]

/-- The descendant functions of the honest schedule: in round `r`, the epoch-boundary blocks of
the chain that the validator `v₀` selects at phase `ρ r`. -/
noncomputable def roundExt (T : BlockTree B) (X : ChainTrace V B) (slot : B → ℕ) (E : ℕ)
    (v₀ : V) (ρ : ℕ → ℕ) (r : ℕ) : B → ℕ → B :=
  extendTo T (boundaryBlock slot E T.genesis (X.chain (ρ r) v₀))

/-- The hypotheses of Δ-updatedness on the votes.

* `epoch_pos`, `delay_pos`: `1 ≤ E` and `1 ≤ Δ`.
* `honest`, `mem_v₀`, `quorum`: the validators of `H` are honest, `v₀ ∈ H`, and `H` holds at
  least two thirds of the stake.
* `pre_justified`, `pre_sources`, `pre_unslashable`, `pre_onChain`, `pre_cast`: the history
  `pre` of votes cast up to phase `ρ 0` justifies `j₀`; the votes of `H` in `pre` have their
  sources at epochs at most `j₀.epoch` (the extra hypothesis of `FFG.plausible_liveness`); no
  validator of `H` is slashable in `pre`; `j₀` is the epoch-boundary checkpoint of its epoch on
  the chains of `H` at phase `ρ 0`.
* `start`, `gst`, `round_slot`: round `r` takes place at phase `ρ r`, of slot
  `τ₀ + r (2 E)`, with `τ₀` at least `GST` and at least `(e₀ + 1) E + σ + d`, where
  `e₀ = livenessEpoch pre j₀` is the epoch of the first new checkpoint.
* `round_cast`: in round `r` (within the horizon) the validators of `H` cast the votes
  `roundVotes`.
* `sync`: synchrony after `GST` with delay `Δ`.
-/
structure VoteHyp (T : BlockTree B) (w : V → ℕ) (X : ChainTrace V B) (now : ℕ → ℕ)
    (slot : B → ℕ) (E σ d Δ GST hz : ℕ) (H : Finset V) (v₀ : V) (pre : Finset (Vote V B))
    (j₀ : Checkpoint B) (τ₀ : ℕ) (ρ : ℕ → ℕ) (cast : ℕ → Finset (Vote V B))
    (seen : ℕ → V → Finset (Vote V B)) : Prop where
  epoch_pos : 1 ≤ E
  delay_pos : 1 ≤ Δ
  honest : ∀ v ∈ H, X.honest v
  mem_v₀ : v₀ ∈ H
  quorum : 2 * totalStake w ≤ 3 * stake w H
  pre_justified : Justified T w pre j₀
  pre_sources : ∀ x ∈ pre, x.validator ∈ H → x.source.epoch ≤ j₀.epoch
  pre_unslashable : slashable pre ∩ H = ∅
  pre_onChain : ρ 0 ≤ hz → ∀ v ∈ H, IsCheckpointOf slot E (X.chain (ρ 0) v) j₀
  pre_cast : ∀ x ∈ pre, ∃ j ≤ ρ 0, x ∈ cast j
  start : (livenessEpoch pre j₀ + 1) * E + σ + d ≤ τ₀
  gst : GST ≤ τ₀
  round_slot : ∀ r, now (ρ r) = τ₀ + r * (2 * E)
  round_cast : ∀ r, ρ r ≤ hz → roundVotes H (roundExt T X slot E v₀ ρ) pre j₀ r ⊆ cast (ρ r)
  sync : ∀ p j t x, X.honest p → j ≤ t → x ∈ cast j → max (now j) GST + Δ ≤ now t →
    x ∈ seen t p

/-- The hypotheses of Δ-updatedness: the hypotheses on the votes (`VoteHyp`) and on the honest
chains up to phase `hz` (`SlotChainHyp`, with common prefix parameter `d` and chain-growth
window `σ`). -/
structure UpdatedHyp (T : BlockTree B) (w : V → ℕ) (X : ChainTrace V B) (now : ℕ → ℕ)
    (slot : B → ℕ) (E σ d Δ GST hz : ℕ) (H : Finset V) (v₀ : V) (pre : Finset (Vote V B))
    (j₀ : Checkpoint B) (τ₀ : ℕ) (ρ : ℕ → ℕ) (cast : ℕ → Finset (Vote V B))
    (seen : ℕ → V → Finset (Vote V B)) : Prop
    extends VoteHyp T w X now slot E σ d Δ GST hz H v₀ pre j₀ τ₀ ρ cast seen where
  chain : SlotChainHyp T X now slot d σ hz

namespace UpdatedHyp

variable {T : BlockTree B} {w : V → ℕ} {X : ChainTrace V B} {now : ℕ → ℕ} {slot : B → ℕ}
  {E σ d Δ GST hz : ℕ} {H : Finset V} {v₀ : V} {pre : Finset (Vote V B)} {j₀ : Checkpoint B}
  {τ₀ : ℕ} {ρ : ℕ → ℕ} {cast : ℕ → Finset (Vote V B)} {seen : ℕ → V → Finset (Vote V B)}
  (h : UpdatedHyp T w X now slot E σ d Δ GST hz H v₀ pre j₀ τ₀ ρ cast seen)
include h

/-- The FFG invariants of the schedule (`schedule_spec`). -/
theorem spec (r : ℕ) :
    Justified T w (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).1
        (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).2 ∧
      (∀ x ∈ (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).1, x.validator ∈ H →
        x.source.epoch ≤ (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).2.epoch) ∧
      slashable (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).1 ∩ H = ∅ ∧
      roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r = livenessEpoch pre j₀ + 2 * r :=
  schedule_spec (fun _ b e => anc_extendTo T _ b e) h.quorum ⟨v₀, h.mem_v₀⟩ h.pre_justified
    h.pre_sources h.pre_unslashable r

/-- The phases of the rounds increase. -/
theorem rho_mono {r r' : ℕ} (hr : r ≤ r') : ρ r ≤ ρ r' := by
  rcases Nat.lt_or_eq_of_le hr with hr | rfl
  · by_contra hc
    have h1 := h.chain.now_mono (le_of_not_ge hc)
    rw [h.round_slot, h.round_slot] at h1
    have : r * (2 * E) < r' * (2 * E) :=
      Nat.mul_lt_mul_of_pos_right hr (by have := h.epoch_pos; omega)
    omega
  · exact le_rfl

/-- At the phase of round `r` the epoch-boundary checkpoints of epochs `e_r` and `e_r + 1`
are settled. -/
theorem epoch_slot (r : ℕ) :
    (roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r + 1) * E + σ + d ≤ now (ρ r) := by
  rw [(h.spec r).2.2.2, h.round_slot]
  have := h.start
  have e1 : (livenessEpoch pre j₀ + 2 * r + 1) * E =
      (livenessEpoch pre j₀ + 1) * E + r * (2 * E) := by ring
  omega

/-- Every epoch up to `e_r + 1` is settled at the phase of round `r`. -/
theorem settled_le (r : ℕ) {e : ℕ}
    (he : e ≤ roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r + 1) :
    e * E + σ + d ≤ now (ρ r) := by
  have := h.epoch_slot r
  have := Nat.mul_le_mul_right E he
  omega

/-- The block of the checkpoint `(schedule … r).2` and of the checkpoints of round `r`, read off
the chain of `v₀` at phase `ρ r`. -/
theorem round_blocks {r : ℕ} (hr : ρ r ≤ hz)
    (hon : IsCheckpointOf slot E (X.chain (ρ r) v₀) (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).2) :
    livenessTarget (roundExt T X slot E v₀ ρ r) (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).1
        (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).2 =
      ⟨boundaryBlock slot E T.genesis (X.chain (ρ r) v₀)
          (roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r),
        roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r⟩ ∧
    livenessNext (roundExt T X slot E v₀ ρ r) (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).1
        (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).2 =
      ⟨boundaryBlock slot E T.genesis (X.chain (ρ r) v₀)
          (roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r + 1),
        roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r + 1⟩ := by
  set S := schedule H (roundExt T X slot E v₀ ρ) pre j₀ r with hS
  have hv₀ := h.honest v₀ h.mem_v₀
  have hb : S.2.block = boundaryBlock slot E T.genesis (X.chain (ρ r) v₀) S.2.epoch := by
    have := epochBoundary_eq_boundaryBlock (h.chain.genesis_mem _ _ hv₀ hr) h.chain.genesis_slot
      (slot := slot) (E := E) S.2.epoch
    rw [IsCheckpointOf] at hon
    rw [hon] at this
    exact Option.some.inj this
  have hT : livenessTarget (roundExt T X slot E v₀ ρ r) S.1 S.2 =
      ⟨boundaryBlock slot E T.genesis (X.chain (ρ r) v₀) (livenessEpoch S.1 S.2),
        livenessEpoch S.1 S.2⟩ := by
    simp only [livenessTarget, roundExt]
    rw [extendTo_of_anc]
    rw [hb]
    exact anc_boundaryBlock h.chain hv₀ hr (epoch_lt_livenessEpoch S.1 S.2).le
  refine ⟨hT, ?_⟩
  have hN : livenessNext (roundExt T X slot E v₀ ρ r) S.1 S.2 =
      ⟨roundExt T X slot E v₀ ρ r (livenessTarget (roundExt T X slot E v₀ ρ r) S.1 S.2).block
        (livenessEpoch S.1 S.2 + 1), livenessEpoch S.1 S.2 + 1⟩ := rfl
  rw [hN, hT]
  simp only [roundExt]
  rw [extendTo_of_anc (anc_boundaryBlock h.chain hv₀ hr (Nat.le_succ _))]
  rfl

/-- The starting checkpoint of every round within the horizon is the epoch-boundary checkpoint
of its epoch on the chains of `H` at the phase of the round. -/
theorem onChain (r : ℕ) (hr : ρ r ≤ hz) :
    ∀ v ∈ H, IsCheckpointOf slot E (X.chain (ρ r) v)
      (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).2 := by
  induction r with
  | zero => exact h.pre_onChain hr
  | succ r ih =>
    have hr' : ρ r ≤ hz := (h.rho_mono (Nat.le_succ r)).trans hr
    intro v hv
    rw [schedule_succ, (h.round_blocks hr' (ih hr' v₀ h.mem_v₀)).1]
    exact boundary_settled h.chain (h.honest v₀ h.mem_v₀) (h.honest v hv)
      (h.rho_mono (Nat.le_succ r)) hr (h.settled_le r (Nat.le_succ _))

/-- The honest votes of every round within the horizon follow the voting rule
`HonestVotesOnChain`: each has source and target that are epoch-boundary checkpoints of the chain the voter selects at the
phase of the round. -/
theorem roundVotes_onChain (r : ℕ) (hr : ρ r ≤ hz) :
    HonestVotesOnChain X slot E (roundVotes H (roundExt T X slot E v₀ ρ) pre j₀ r) := by
  intro x hx _
  obtain ⟨hxH, hst⟩ := mem_livenessVotes hx
  have hv₀ := h.honest v₀ h.mem_v₀
  obtain ⟨hT, hN⟩ := h.round_blocks hr (h.onChain r hr v₀ h.mem_v₀)
  have he := h.epoch_slot r
  have hset : ∀ e, e ≤ roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r + 1 →
      epochBoundary slot E (X.chain (ρ r) x.validator) e =
        some (boundaryBlock slot E T.genesis (X.chain (ρ r) v₀) e) := fun e hle =>
    boundary_settled h.chain hv₀ (h.honest _ hxH) le_rfl hr (h.settled_le r hle)
  refine ⟨ρ r, ?_⟩
  rcases hst with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht, hT]
    exact ⟨h.onChain r hr _ hxH, hset _ (Nat.le_succ _)⟩
  · rw [hs, ht, hT, hN]
    exact ⟨hset _ (Nat.le_succ _), hset _ le_rfl⟩

omit [Fintype V] h in
/-- Every vote of the schedule after `r` rounds is a vote of `pre` or of an earlier round. -/
theorem mem_schedule {r : ℕ} {x : Vote V B}
    (hx : x ∈ (schedule H (roundExt T X slot E v₀ ρ) pre j₀ r).1) :
    x ∈ pre ∨ ∃ r' < r, x ∈ roundVotes H (roundExt T X slot E v₀ ρ) pre j₀ r' := by
  induction r with
  | zero => exact Or.inl hx
  | succ r ih =>
    rw [schedule_succ] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases ih hx with h' | ⟨r', hr', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨r', by omega, h'⟩
    · exact Or.inr ⟨r, by omega, hx⟩

/-- An honest party has received, at a phase `t ≤ hz` of slot at least
`τ₀ + r (2 E) + Δ` with `ρ r < t`, all votes of the schedule after `r + 1` rounds. -/
theorem schedule_subset_seen {p : V} {t r : ℕ} (hp : X.honest p) (ht : t ≤ hz)
    (hrt : ρ r < t) (hnow : τ₀ + r * (2 * E) + Δ ≤ now t) :
    (schedule H (roundExt T X slot E v₀ ρ) pre j₀ (r + 1)).1 ⊆ seen t p := by
  intro x hx
  have hgst := h.gst
  rcases mem_schedule hx with hx | ⟨r', hr', hx⟩
  · obtain ⟨j, hj, hxj⟩ := h.pre_cast x hx
    have h0 := h.rho_mono (Nat.zero_le r)
    have hnj := h.chain.now_mono hj
    rw [h.round_slot, Nat.zero_mul, Nat.add_zero] at hnj
    exact h.sync p j t x hp (by omega) hxj (by omega)
  · have hr'r := h.rho_mono (Nat.lt_succ_iff.1 hr')
    have hxc := h.round_cast r' (by omega) hx
    refine h.sync p _ t x hp (by omega) hxc ?_
    rw [h.round_slot]
    have : r' * (2 * E) ≤ r * (2 * E) := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 hr')
    omega

end UpdatedHyp

variable {T : BlockTree B} {w : V → ℕ} {X : ChainTrace V B} {now : ℕ → ℕ} {slot : B → ℕ}
  {E σ d Δ GST hz : ℕ} {H : Finset V} {v₀ : V} {pre : Finset (Vote V B)} {j₀ : Checkpoint B}
  {τ₀ : ℕ} {ρ : ℕ → ℕ} {cast : ℕ → Finset (Vote V B)} {seen : ℕ → V → Finset (Vote V B)}

/-- **Δ-updatedness of Casper FFG over a chain.** Under the hypotheses `UpdatedHyp` (honest
chains with common prefix by slots `d` and chain growth in slot form `σ` up to phase `hz`,
honest validators holding at least two thirds of the stake that follow the liveness schedule
from the slot `τ₀ ≥ GST`, synchrony with delay `Δ` after `GST`), at every phase `t ≤ hz` with
`now t ≥ τ₀ + Δ` every honest party `p` has received votes that finalize a checkpoint `c`
which is the epoch-boundary checkpoint of its epoch on the chain of `p`, and
`now t ≤ c.epoch * E + (τ₀ + 2 E + Δ - e₀ E)` with `e₀ = livenessEpoch pre j₀`. -/
theorem finality_updated (h : UpdatedHyp T w X now slot E σ d Δ GST hz H v₀ pre j₀ τ₀ ρ cast seen)
    {p : V} {t : ℕ} (hp : X.honest p) (ht : t ≤ hz) (hτ : τ₀ + Δ ≤ now t) :
    ∃ c : Checkpoint B, Finalized T w (seen t p) c ∧ IsCheckpointOf slot E (X.chain t p) c ∧
      now t ≤ c.epoch * E + (τ₀ + 2 * E + Δ - livenessEpoch pre j₀ * E) := by
  have hE := h.epoch_pos
  have hΔ := h.delay_pos
  set r := (now t - τ₀ - Δ) / (2 * E) with hr
  have hdm := Nat.div_add_mod (now t - τ₀ - Δ) (2 * E)
  have hmod := Nat.mod_lt (now t - τ₀ - Δ) (show 0 < 2 * E by omega)
  rw [← hr] at hdm
  have hcomm : 2 * E * r = r * (2 * E) := Nat.mul_comm _ _
  have hρt : ρ r < t := by
    by_contra hc
    have h1 := h.chain.now_mono (le_of_not_gt hc)
    rw [h.round_slot] at h1
    omega
  have hρ : ρ r ≤ hz := by omega
  set S := schedule H (roundExt T X slot E v₀ ρ) pre j₀ r with hS
  obtain ⟨hJ, hsrc, hU, hep⟩ := h.spec r
  obtain ⟨-, -, -, hfin, -⟩ :=
    plausible_liveness (roundExt T X slot E v₀ ρ r) (anc_extendTo T _) h.quorum hJ hsrc hU
  have hsub := h.schedule_subset_seen hp ht hρt (by omega)
  rw [schedule_succ] at hsub
  obtain ⟨hT, -⟩ := h.round_blocks hρ (h.onChain r hρ v₀ h.mem_v₀)
  refine ⟨_, Finalized.mono hsub hfin, ?_, ?_⟩
  · rw [hT]
    exact boundary_settled h.chain (h.honest v₀ h.mem_v₀) hp hρt.le ht
      (h.settled_le r (Nat.le_succ _))
  · rw [hT]
    show now t ≤ roundEpoch H (roundExt T X slot E v₀ ρ) pre j₀ r * E + _
    rw [hep]
    have hst := h.start
    have e1 : (livenessEpoch pre j₀ + 2 * r) * E = livenessEpoch pre j₀ * E + r * (2 * E) := by
      ring
    have e2 : (livenessEpoch pre j₀ + 1) * E = livenessEpoch pre j₀ * E + E := by ring
    omega

/-- **Δ-updatedness with the earliest start.** With `τ₀ = (e₀ + 1) E + σ + d`, at every phase
`t ≤ hz` with `now t ≥ τ₀ + Δ`, every honest party has received votes finalizing an
epoch-boundary checkpoint `c` of its chain with `now t ≤ c.epoch * E + 3 E + σ + d + Δ`: the
last finalized checkpoint is at most `3 E + σ + d + Δ` slots behind the current slot, hence
behind the tip of the chain. -/
theorem finality_updated_start
    (h : UpdatedHyp T w X now slot E σ d Δ GST hz H v₀ pre j₀ τ₀ ρ cast seen)
    (hτ₀ : τ₀ = (livenessEpoch pre j₀ + 1) * E + σ + d)
    {p : V} {t : ℕ} (hp : X.honest p) (ht : t ≤ hz) (hτ : τ₀ + Δ ≤ now t) :
    ∃ c : Checkpoint B, Finalized T w (seen t p) c ∧ IsCheckpointOf slot E (X.chain t p) c ∧
      now t ≤ c.epoch * E + (3 * E + σ + d + Δ) := by
  obtain ⟨c, h1, h2, h3⟩ := finality_updated h hp ht hτ
  refine ⟨c, h1, h2, h3.trans_eq ?_⟩
  have e2 : (livenessEpoch pre j₀ + 1) * E = livenessEpoch pre j₀ * E + E := by ring
  rw [hτ₀]
  omega

/-- **Δ-updatedness relative to the tip.** If moreover the blocks of the chain of `p` at phase
`t` have slots at most `now t`, then the finalized checkpoint `c` of `finality_updated_start`
is a block of that chain and every block of the chain, in particular its tip, has slot at most
`c.epoch * E + 3 E + σ + d + Δ`. -/
theorem finality_updated_tip
    (h : UpdatedHyp T w X now slot E σ d Δ GST hz H v₀ pre j₀ τ₀ ρ cast seen)
    (hτ₀ : τ₀ = (livenessEpoch pre j₀ + 1) * E + σ + d)
    {p : V} {t : ℕ} (hp : X.honest p) (ht : t ≤ hz) (hτ : τ₀ + Δ ≤ now t)
    (hslots : ∀ b ∈ X.chain t p, slot b ≤ now t) :
    ∃ c : Checkpoint B, Finalized T w (seen t p) c ∧ IsCheckpointOf slot E (X.chain t p) c ∧
      c.block ∈ X.chain t p ∧ ∀ b ∈ X.chain t p, slot b ≤ c.epoch * E + (3 * E + σ + d + Δ) := by
  obtain ⟨c, h1, h2, h3⟩ := finality_updated_start h hτ₀ hp ht hτ
  exact ⟨c, h1, h2, List.mem_of_find?_eq_some h2, fun b hb => (hslots b hb).trans h3⟩

end Updated

/-! ### A concrete instance: the hypotheses are satisfiable -/

namespace Examples

/-- The chain `[n, n - 1, …, 0]` has strictly decreasing entries. -/
theorem line_pairwise_lt (n : ℕ) : (line n).Pairwise fun b b' => b' < b := by
  induction n with
  | zero => simp [line]
  | succ n ih =>
    simp only [line, List.pairwise_cons]
    exact ⟨fun b hb => by have := mem_line.1 hb; omega, ih⟩

/-- The blocks of `[n, …, 0]` of slot at most `s` are `[min n s, …, 0]`. -/
theorem filter_line (s n : ℕ) : (line n).filter (fun b => decide (b ≤ s)) = line (min n s) := by
  induction n with
  | zero => simp [line]
  | succ n ih =>
    by_cases hn : n + 1 ≤ s
    · rw [line, List.filter_cons_of_pos (by simpa using hn), ih,
        Nat.min_eq_left (by omega), Nat.min_eq_left hn, line]
    · rw [line, List.filter_cons_of_neg (by simpa using hn), ih,
        Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

/-- One validator whose chain at phase `j` is `[j, …, 0]`: one block per slot, block `b` of
slot `b`. -/
def lineX : ChainTrace (Fin 1) ℕ where
  honest _ := True
  chain j _ := line j

/-- Unit stake. -/
def oneStake : Fin 1 → ℕ := fun _ => 1

/-- The rounds take place at the slots `3 + 2 r`. -/
def ρI (r : ℕ) : ℕ := 3 + r * (2 * 1)

/-- The votes of round `r` of the schedule from the genesis checkpoint. -/
noncomputable def votesI (r : ℕ) : Finset (Vote (Fin 1) ℕ) :=
  roundVotes Finset.univ (roundExt lineTree lineX id 1 0 ρI) ∅ (genesisCheckpoint lineTree) r

/-- The votes cast at phase `j`: the votes of the round held at `j`. -/
noncomputable def castI (j : ℕ) : Finset (Vote (Fin 1) ℕ) :=
  (Finset.range (j + 1)).biUnion fun r => if ρI r = j then votesI r else ∅

/-- Every vote is received in the phase it is cast. -/
noncomputable def seenI (t : ℕ) (_ : Fin 1) : Finset (Vote (Fin 1) ℕ) :=
  (Finset.range (t + 1)).biUnion castI

theorem lineX_slotChainHyp (hz : ℕ) : SlotChainHyp lineTree lineX id id 0 1 hz where
  now_mono := monotone_id
  inTree j _ _ _ := lineTrace_chainsInTree () j trivial
  decreasing j _ _ _ := line_pairwise_lt j
  genesis_mem j _ _ _ := mem_line.2 (Nat.zero_le j)
  genesis_slot := rfl
  commonPrefix := by
    intro _ _ j j' s _ _ hjj _ hs
    simp only [lineX, id] at hs ⊢
    rw [filter_line, Nat.min_eq_right (by omega)]
    exact line_suffix (by omega)
  growth := by
    intro _ j a _ _ ha
    exact ⟨a + 1, mem_line.2 (by simp only [id] at ha; omega), by simp, by simp⟩

theorem livenessEpoch_empty :
    livenessEpoch (∅ : Finset (Vote (Fin 1) ℕ)) (genesisCheckpoint lineTree) = 1 := by
  simp [livenessEpoch, genesisCheckpoint, lineTree]

/-- **Non-vacuity.** All hypotheses of Δ-updatedness hold, for every horizon `hz`, for the
chain `[j, …, 0]` with one block per slot and one honest validator of unit stake: epochs of
`E = 1` slot, chain-growth window `σ = 1`, common prefix parameter `d = 0`, delay `Δ = 1`,
`GST = 0`, empty history `pre`, start from the genesis checkpoint at slot `τ₀ = 3`, rounds at
slots `3 + 2 r`. -/
theorem updated_nonvacuous (hz : ℕ) :
    UpdatedHyp lineTree oneStake lineX id id 1 1 0 1 0 hz Finset.univ 0 ∅
      (genesisCheckpoint lineTree) 3 ρI castI seenI where
  chain := lineX_slotChainHyp hz
  epoch_pos := le_rfl
  delay_pos := le_rfl
  honest _ _ := trivial
  mem_v₀ := Finset.mem_univ _
  quorum := by
    show 2 * stake oneStake Finset.univ ≤ 3 * stake oneStake Finset.univ
    omega
  pre_justified := Justified.genesis
  pre_sources _ hx := absurd hx (Finset.notMem_empty _)
  pre_unslashable := by
    refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
    rcases mem_slashable.1 (Finset.mem_inter.1 hv).1 with ⟨x, hx, -⟩ | ⟨x, hx, -⟩ <;>
      exact Finset.notMem_empty x hx
  pre_onChain _ _ _ := by simp only [lineX]; decide
  pre_cast _ hx := absurd hx (Finset.notMem_empty _)
  start := by rw [livenessEpoch_empty]
  gst := Nat.zero_le _
  round_slot _ := rfl
  round_cast r _ x hx := Finset.mem_biUnion.2
    ⟨r, Finset.mem_range.2 (by simp only [ρI]; omega), by rw [ite_eq_left rfl]; exact hx⟩
  sync _ j t x _ hjt hx _ := Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 (by omega), hx⟩

/-- On the instance, at every phase `t ≥ 4` the validator has received votes finalizing an
epoch-boundary checkpoint `c` of its chain `[t, …, 0]` with `t ≤ c.epoch + 5`. -/
theorem updated_instance {t : ℕ} (ht : 4 ≤ t) :
    ∃ c : Checkpoint ℕ, Finalized lineTree oneStake (seenI t 0) c ∧
      IsCheckpointOf id 1 (line t) c ∧ t ≤ c.epoch * 1 + (3 * 1 + 1 + 0 + 1) :=
  finality_updated_start (updated_nonvacuous t) (by rw [livenessEpoch_empty]) trivial le_rfl ht

end Examples

end CatCryptCore.Consensus.Finality

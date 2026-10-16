/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.FFGDynamic
public import CatCryptCore.Consensus.FFGExamples

/-!
# Casper FFG with a dynamic validator set: a concrete instance with non-zero churn

This file shows that the hypotheses of `FFGDynamic.accountable_safety_dynamic` are satisfiable
with non-zero churn.

## Main results

* `Example.dyn_finalized_conflicting`, `Example.dyn_slashable`: a schedule of seven unit-stake
  validators with churn `2`, in which conflicting checkpoints are finalized, exactly one
  validator is slashable, the fixed-set bound fails for the sets active at every epoch, and
  the dynamic bound forces the slashable stable stake to be at least `1`, which it is.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.FFGDynamic

open CatCryptCore.Consensus.FFG

/-! ### A concrete instance with non-zero churn -/

namespace Example

open CatCryptCore.Consensus.FFG.Examples

/-- Seven unit-stake validators; validators `0, …, 5` are active at epoch `0`, and validator
`0` leaves while validator `6` joins, so `1, …, 6` are active from epoch `1` on. -/
def dynSchedule : Schedule (Fin 7) := fun e v =>
  if e = 0 then (if v = 6 then 0 else 1) else (if v = 0 then 0 else 1)

instance (votes : Finset (Vote (Fin 7) (Fin 3))) (s t : Checkpoint (Fin 3)) :
    Decidable (DSupermajorityLink forkTree dynSchedule votes s t) := by
  unfold DSupermajorityLink SupermajorityLink; infer_instance

instance (a b : Fin 3) : Decidable (forkTree.anc a b) := by
  unfold forkTree; infer_instance

/-- The vote of validator `v` for the link `(b₁, e₁) → (b₂, e₂)`. -/
def dvote (v : Fin 7) (b₁ : Fin 3) (e₁ : ℕ) (b₂ : Fin 3) (e₂ : ℕ) : Vote (Fin 7) (Fin 3) :=
  ⟨v, ⟨b₁, e₁⟩, ⟨b₂, e₂⟩⟩

/-- Validators `0, 1, 2, 3` justify `(1, 1)` from genesis and `3, 4, 5, 6` finalize it with the
link `(1, 1) → (1, 2)`, weighed by the set of epoch `1`; validators `0, 1, 2, 3` justify
`(2, 2)` from genesis, weighed by the set of epoch `0`, and `3, 4, 5, 6` finalize it. -/
def dynVotes : Finset (Vote (Fin 7) (Fin 3)) :=
  {dvote 0 0 0 1 1, dvote 1 0 0 1 1, dvote 2 0 0 1 1, dvote 3 0 0 1 1,
   dvote 3 1 1 1 2, dvote 4 1 1 1 2, dvote 5 1 1 1 2, dvote 6 1 1 1 2,
   dvote 0 0 0 2 2, dvote 1 0 0 2 2, dvote 2 0 0 2 2, dvote 3 0 0 2 2,
   dvote 3 2 2 2 3, dvote 4 2 2 2 3, dvote 5 2 2 2 3, dvote 6 2 2 2 3}

/-- The checkpoints `(1, 1)` and `(2, 2)` are finalized for `dynSchedule` and lie on
conflicting blocks. -/
theorem dyn_finalized_conflicting :
    DFinalized forkTree dynSchedule dynVotes ⟨1, 1⟩ ∧
      DFinalized forkTree dynSchedule dynVotes ⟨2, 2⟩ ∧
      forkTree.Conflicting (⟨1, 1⟩ : Checkpoint (Fin 3)).block
        (⟨2, 2⟩ : Checkpoint (Fin 3)).block :=
  ⟨⟨DJustified.link DJustified.genesis (by decide), ⟨1, 2⟩, rfl, by decide⟩,
    ⟨DJustified.link DJustified.genesis (by decide), ⟨2, 3⟩, rfl, by decide⟩,
    forkTree_conflicting⟩

/-- Up to the horizon `2` the churn is `2` (validator `0` leaves, validator `6` joins), the
stable validators are `1, …, 5`, and the path churn is also `2`. -/
theorem dyn_churn :
    churn dynSchedule 2 = 2 ∧ pathChurn dynSchedule 2 = 2 ∧
      totalStake (stableWeight dynSchedule 2) = 5 := by
  decide

/-- Only validator `3` is slashable (a double vote at target epoch `2`). Its stake is `1` in
every active set, so the fixed-set bound `W ≤ 3 · stake(slashable)` fails for the sets of
epochs `0`, `1` and `2` (each of total stake `6`), while the dynamic bound
`W_stable ≤ 3 · stake_stable(slashable) + 2 · churn`, i.e. `5 ≤ 3 · 1 + 4`, holds; with stable
slashable stake `0` it would fail, so the dynamic bound forces the value `1` attained here. -/
theorem dyn_slashable :
    slashable dynVotes = {3} ∧
      (∀ e ≤ 2, ¬ 3 * stake (dynSchedule e) (slashable dynVotes) ≥
        totalStake (dynSchedule e)) ∧
      stake (stableWeight dynSchedule 2) (slashable dynVotes) = 1 ∧
      ¬ totalStake (stableWeight dynSchedule 2) ≤ 3 * 0 + 2 * churn dynSchedule 2 := by
  decide

/-- `accountable_safety_dynamic` applies to `dynVotes`: its hypotheses are satisfiable with
non-zero churn. -/
theorem accountable_safety_dynVotes :
    totalStake (stableWeight dynSchedule 2) ≤
      3 * stake (stableWeight dynSchedule 2) (slashable dynVotes) +
        2 * churn dynSchedule 2 :=
  accountable_safety_dynamic dyn_finalized_conflicting.1 dyn_finalized_conflicting.2.1
    dyn_finalized_conflicting.2.2

end Example

end CatCryptCore.Consensus.FFGDynamic

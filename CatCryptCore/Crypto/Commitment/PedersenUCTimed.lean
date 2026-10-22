/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Commitment.PedersenUC
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the Pedersen UC simulators

The computation trees and costed forms of the simulators `pedersen_sim` and
`pedersen_commit_sim` of `CatCryptCore.Crypto.Commitment.PedersenUC`, derived by
`derive_reduction`, and their time bounds: the time of the simulated adversary plus a
constant.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the scalar operations `scalarDiv`, `scalarSub` are primitives with cost companions; the
adversary call costs its cost companion.

## Main results

* `pedersen_sim.tree.timeBound_timed` — time at most `T + a + td + tsub + 3`
* `pedersen_commit_sim.tree.timeBound_timed` — time at most `T + a + 2`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Commitment.PedersenUC

open CatCrypt.Core CatCrypt.Examples

derive_reduction pedersen_sim

derive_reduction pedersen_commit_sim

/-- **Time of the opening simulator.** For an adversary `A` of time at most `T` and call cost at
most `a`, with scalar division and subtraction of costs at most `td` and `tsub`, the simulator
runs in time at most `T + a + td + tsub + 3`. -/
theorem pedersen_sim.tree.timeBound_timed (gp : GroupParam) (crs : PedersenCRS gp)
    (view : Type) (A : gp.Scalar × gp.Scalar → SPTree.Timed view)
    (ACost : gp.Scalar × gp.Scalar → ℕ) (x : gp.Scalar × gp.Scalar)
    (scalarDiv : gp.Scalar → gp.Scalar → gp.Scalar) (scalarDivCost : gp.Scalar → gp.Scalar → ℕ)
    (scalarSub : gp.Scalar → gp.Scalar → gp.Scalar) (scalarSubCost : gp.Scalar → gp.Scalar → ℕ)
    {T a td tsub : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hd : ∀ u v, scalarDivCost u v ≤ td) (hsub : ∀ u v, scalarSubCost u v ≤ tsub) :
    SPTree.Timed.stepTime (pedersen_sim.tree.timed gp crs view A ACost x scalarDiv scalarDivCost
      scalarSub scalarSubCost) ≤ T + a + td + tsub + 3 := by
  time_bound

/-- **Time of the commit-phase simulator.** For an adversary `A` of time at most `T` and call
cost at most `a`, the simulator runs in time at most `T + a + 2`. -/
theorem pedersen_commit_sim.tree.timeBound_timed (gp : GroupParam) (view : Type)
    (A : gp.Scalar → SPTree.Timed view) (ACost : gp.Scalar → ℕ) {T a : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (u : Unit) :
    SPTree.Timed.stepTime (pedersen_commit_sim.tree.timed gp view A ACost u) ≤ T + a + 2 := by
  time_bound

end CatCrypt.Crypto.Commitment.PedersenUC

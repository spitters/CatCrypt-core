/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.DualModeOT
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the dual-mode OT simulator

The computation tree and costed form of the simulator `dualOT_sim` of
`CatCryptCore.Crypto.OT.DualModeOT`, derived by `derive_reduction`, and its time bound: the
time of the simulated adversary plus a constant.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the adversary call costs its cost companion.

## Main results

* `dualOT_sim.tree.timeBound_timed` — time at most `T + a + 3`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.DualModeOT

open CatCrypt.Core CatCrypt.Examples

derive_reduction dualOT_sim

/-- **Time of the simulator.** For an adversary `A` of time at most `T` and call cost at most
`a`, the simulator runs in time at most `T + a + 3`. -/
theorem dualOT_sim.tree.timeBound_timed (gp : GroupParam) (crs : DualModeCRS gp) (V : Type)
    (A : gp.G × gp.G → SPTree.Timed V) (ACost : gp.G × gp.G → ℕ) (x : Bool × gp.G) {T a : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) :
    SPTree.Timed.stepTime (dualOT_sim.tree.timed gp crs V A ACost x) ≤ T + a + 3 := by
  time_bound

end CatCrypt.Crypto.OT.DualModeOT

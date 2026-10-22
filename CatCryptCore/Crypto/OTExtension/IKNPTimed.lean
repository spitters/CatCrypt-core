/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNP
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the IKNP sender simulator

The computation tree and costed form of the sender simulator `iknpSimS` of
`CatCryptCore.Crypto.OTExtension.IKNP`, derived by `derive_reduction`, and its time bound: the
time of the simulated base-OT receiver simulator plus a constant.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the base-OT receiver simulator `simRB` is a computation primitive with costed form `simRB` and
cost companion `simRBCost`.

## Main results

* `iknpSimS.tree.timeBound_timed` — time at most `t + c + 3` for a base-OT simulator of time
  `t` and call cost `c`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT

open CatCrypt.Core

derive_reduction iknpSimS

/-- **Time of the sender simulator.** With a base-OT receiver simulator of time at most `t` and
call cost at most `c`, the sender simulator runs in time at most `t + c + 3`. -/
theorem iknpSimS.tree.timeBound_timed {κ m : ℕ} {M VRB : Type}
    (simRB : (Fin κ → Bool) → (Fin κ → Fin m → Bool) → SPTree.Timed VRB)
    (simRBCost : (Fin κ → Bool) → (Fin κ → Fin m → Bool) → ℕ) {t c : ℕ}
    (hs : ∀ s T, (simRB s T).time ≤ t) (hc : ∀ s T, simRBCost s T ≤ c) :
    SPTree.Timed.stepTime (iknpSimS.tree.timed (M := M) simRB simRBCost) ≤ t + c + 3 := by
  time_bound

end CatCrypt.Crypto.OT

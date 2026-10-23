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
# Time of the IKNP receiver simulator

The computation tree and costed form of the receiver simulator `iknpSimR` of
`CatCryptCore.Crypto.OTExtension.IKNP`, derived by `derive_reduction`, and its time bound: the
time of the simulated base-OT sender simulator plus a constant.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the base-OT sender simulator `simSB` is a computation primitive with costed form `simSB` and
cost companion `simSBCost`. The received messages `fun j => if r j then … else …` are a
function in data, carried as a costed closure whose companion prices each entry.

## Main results

* `iknpSimR.tree.timeBound_timed` — time at most `t + c + 3` for a base-OT simulator of time
  `t` and call cost `c`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT

open CatCrypt.Core

derive_reduction iknpSimR

/-- **Time of the receiver simulator.** With a base-OT sender simulator of time at most `t`
and call cost at most `c`, the receiver simulator runs in time at most `t + c + 3`. -/
theorem iknpSimR.tree.timeBound_timed {κ m : ℕ} {M VSB : Type} [AddCommGroup M] [Fintype M]
    [Nonempty M]
    (simSB : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPTree.Timed VSB)
    (simSBCost : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → ℕ)
    (H : Fin m → (Fin κ → Bool) → M) (HCost : Fin m → (Fin κ → Bool) → ℕ)
    (r : Fin m → Bool) (rCost : Fin m → ℕ) (z : Fin m → M) (zCost : Fin m → ℕ) {t c : ℕ}
    (hs : ∀ x, (simSB x).time ≤ t) (hc : ∀ x, simSBCost x ≤ c) :
    SPTree.Timed.stepTime (iknpSimR.tree.timed simSB simSBCost H HCost r rCost z zCost) ≤
      t + c + 3 := by
  time_bound

end CatCrypt.Crypto.OT

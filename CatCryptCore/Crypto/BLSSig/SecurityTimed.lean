/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.BLSSig.Security
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the BLS co-CDH reduction

The computation tree and costed form of `blsReduction` of
`CatCryptCore.Crypto.BLSSig.Security`, derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step; the forger's
field `run` is a computation primitive with costed form `run` and cost companion `runCost`,
which take the signing oracle handed to the forger as an argument, so that the forger's time
includes its oracle calls.

## Main results

* `blsReduction.tree.timeBound_timed` — a forger of time `T` and call cost `a` (for every
  signing oracle) gives a reduction of time at most `T + a + 1`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Crypto.BLSSig

open CatCrypt.Core CatCrypt.Crypto

derive_reduction blsReduction

/-- **Time of the BLS reduction.** A forger whose run has time at most `T` and call cost at most
`a` for every public key, hash and signing oracle gives a reduction of time at most
`T + a + 1`. -/
theorem blsReduction.tree.timeBound_timed (P : PairingGroup) (F : BLSForger P) (gx : P.G₁)
    (hx : P.G₂) (u : P.G₁) (run : P.G₂ → P.G₁ → (ZMod P.p → SPComp P.G₁) → SPTree.Timed P.G₁)
    (runCost : P.G₂ → P.G₁ → (ZMod P.p → SPComp P.G₁) → ℕ) {T a : ℕ}
    (hr : ∀ x y o, (run x y o).time ≤ T) (hrc : ∀ x y o, runCost x y o ≤ a) :
    SPTree.Timed.stepTime (blsReduction.tree.timed P F gx hx u run runCost) ≤ T + a + 1 := by
  time_bound

end CatCryptCore.Crypto.BLSSig

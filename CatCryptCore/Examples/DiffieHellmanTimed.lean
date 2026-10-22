/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.DiffieHellman
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the Diffie–Hellman key-agreement reduction

The computation tree and costed form of `dhReduction` of
`CatCryptCore.Examples.DiffieHellman`, derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step; the
distinguisher call costs its cost companion.

## Main results

* `dhReduction.tree.timeBound_timed` — a distinguisher of time `T` and call cost `a` gives a
  reduction of time at most `T + a + 1`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.DiffieHellman

open CatCrypt.Core CatCrypt.Crypto

derive_reduction dhReduction

/-- **Time of the key-agreement reduction.** A distinguisher `D` of time at most `T` and call
cost at most `a` gives a reduction of time at most `T + a + 1`. -/
theorem dhReduction.tree.timeBound_timed {P : PairingGroup}
    (D : P.G₁ × P.G₁ → P.G₁ → SPTree.Timed Bool) (DCost : P.G₁ × P.G₁ → P.G₁ → ℕ)
    {T a : ℕ} (hD : ∀ x y, (D x y).time ≤ T) (hDc : ∀ x y, DCost x y ≤ a) (g_a g_b z : P.G₁) :
    SPTree.Timed.stepTime (dhReduction.tree.timed D DCost g_a g_b z) ≤ T + a + 1 := by
  time_bound

end CatCrypt.Examples.DiffieHellman

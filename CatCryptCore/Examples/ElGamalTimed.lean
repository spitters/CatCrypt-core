/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.ElGamal
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the ElGamal DDH reduction

The computation tree and costed form of `elgamalReduction` of `CatCryptCore.Examples.ElGamal`,
derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step; the group
multiplication of `PairingGroup` costs one unit; the distinguisher call costs its cost
companion.

## Main results

* `elgamalReduction.tree.timeBound_timed` — a distinguisher of time `T` and call cost `a`
  gives a reduction of time at most `T + a + 2`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.ElGamal

open CatCrypt.Core CatCrypt.Crypto

derive_reduction elgamalReduction

/-- **Time of the ElGamal reduction.** A distinguisher `A` of time at most `T` and call cost at
most `a` gives a reduction of time at most `T + a + 2`. -/
theorem elgamalReduction.tree.timeBound_timed {P : PairingGroup} (m : P.G₁)
    (A : P.G₁ × P.G₁ → SPTree.Timed Bool) (ACost : P.G₁ × P.G₁ → ℕ)
    {T a : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (g_a g_b z : P.G₁) :
    SPTree.Timed.stepTime (elgamalReduction.tree.timed m A ACost g_a g_b z) ≤ T + a + 2 := by
  time_bound

end CatCrypt.Examples.ElGamal

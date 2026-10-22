/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.ElGamalDDH
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the ElGamal DDH reduction over a cyclic group

The computation tree and costed form of `Reduction` of `CatCryptCore.Examples.ElGamalDDH`,
derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step; the group
multiplication `CyclicGroup.mul` is a primitive with cost companion `mulCost`; the
distinguisher call costs its cost companion.

## Main results

* `Reduction.tree.timeBound_timed` — a distinguisher of time `T` and call cost `a`, with a
  multiplication of cost at most `tm`, gives a reduction of time at most `T + a + tm + 2`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Examples.ElGamalDDH

open CatCrypt.Core CatCryptCore.Examples.CyclicGroupDDH

derive_reduction Reduction

/-- **Time of the ElGamal DDH reduction.** A distinguisher `A` of time at most `T` and call cost
at most `a`, with a multiplication of cost at most `tm`, gives a reduction of time at most
`T + a + tm + 2`. -/
theorem Reduction.tree.timeBound_timed (G : Type) [CyclicGroup G] (m : G)
    (A : G × ElGamalScheme.Ciphertext G → SPTree.Timed Bool)
    (ACost : G × ElGamalScheme.Ciphertext G → ℕ) (mul : G → G → G) (mulCost : G → G → ℕ)
    {T a tm : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hm : ∀ x y, mulCost x y ≤ tm) (c : DDHTriple G) :
    SPTree.Timed.stepTime (Reduction.tree.timed G m A ACost c mul mulCost) ≤ T + a + tm + 2 := by
  time_bound

end CatCryptCore.Examples.ElGamalDDH

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.ElGamalDDHKeyMsg
public import CatCryptCore.Examples.ElGamalDDHTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the key-dependent-message ElGamal DDH reduction

The computation tree and costed form of `ReductionKeyMsg` of
`CatCryptCore.Examples.ElGamalDDHKeyMsg`, derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step; the message map
`m` and the group multiplication `CyclicGroup.mul` are primitives with cost companions; the
distinguisher call costs its cost companion.

## Main results

* `ReductionKeyMsg.tree.timeBound_timed` — a distinguisher of time `T` and call cost `a`, with a
  message map of cost at most `tk` and a multiplication of cost at most `tm`, gives a reduction
  of time at most `T + a + tk + tm + 3`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Examples.ElGamalDDH

open CatCrypt.Core CatCryptCore.Examples.CyclicGroupDDH

derive_reduction ReductionKeyMsg

/-- **Time of the key-dependent-message ElGamal DDH reduction.** A distinguisher `A` of time at
most `T` and call cost at most `a`, with a message map of cost at most `tk` and a multiplication
of cost at most `tm`, gives a reduction of time at most `T + a + tk + tm + 3`. -/
theorem ReductionKeyMsg.tree.timeBound_timed (G : Type) [CyclicGroup G] (m : G → G)
    (mCost : G → ℕ) (A : G × ElGamalScheme.Ciphertext G → SPTree.Timed Bool)
    (ACost : G × ElGamalScheme.Ciphertext G → ℕ) (mul : G → G → G) (mulCost : G → G → ℕ)
    {T a tk tm : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hk : ∀ x, mCost x ≤ tk) (hm : ∀ x y, mulCost x y ≤ tm) (c : DDHTriple G) :
    SPTree.Timed.stepTime (ReductionKeyMsg.tree.timed G m mCost A ACost c mul mulCost) ≤
      T + a + tk + tm + 3 := by
  time_bound

end CatCryptCore.Examples.ElGamalDDH

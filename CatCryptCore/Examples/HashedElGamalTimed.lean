/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.HashedElGamal
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the hashed ElGamal DDH reduction

The computation tree and costed form of `heg_ddh_reduction` of
`CatCryptCore.Examples.HashedElGamal`, derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step and per Boolean
operation; the hash `H` is a primitive with cost companion `HCost`; the distinguisher call
costs its cost companion.

## Main results

* `heg_ddh_reduction.tree.timeBound_timed` — a distinguisher of time `T` and call cost `a`,
  with a hash of cost at most `th`, gives a reduction of time at most `T + a + th + 6`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Examples.HashedElGamal

open CatCrypt.Core CatCryptCore.Examples.CyclicGroupDDH

derive_reduction heg_ddh_reduction

/-- **Time of the hashed ElGamal reduction.** A distinguisher `A` of time at most `T` and call
cost at most `a`, with a hash of cost at most `th`, gives a reduction of time at most
`T + a + th + 6`. -/
theorem heg_ddh_reduction.tree.timeBound_timed {G : Type} (H : G → Bool) (HCost : G → ℕ)
    (m : Bool) (A : G × Bool → SPTree.Timed Bool) (ACost : G × Bool → ℕ)
    {T a th : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hH : ∀ x, HCost x ≤ th)
    (c : DDHTriple G) :
    SPTree.Timed.stepTime (heg_ddh_reduction.tree.timed H HCost m A ACost c) ≤
      T + a + th + 6 := by
  time_bound

end CatCryptCore.Examples.HashedElGamal

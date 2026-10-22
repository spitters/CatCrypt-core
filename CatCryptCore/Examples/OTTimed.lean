/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.OT
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the OT receiver reduction

The computation tree and costed form of `receiverReduction` of `CatCryptCore.Examples.OT`,
derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the exponentiation `CyclicGroup.pow` is a primitive with cost companion `powCost`; the
distinguisher call costs its cost companion.

## Main results

* `receiverReduction.tree.timeBound_timed` — a distinguisher of time `T` and call cost `a`,
  with an exponentiation of cost at most `tp`, gives a reduction of time at most
  `T + a + tp + 5`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.OT

open CatCrypt.Core CatCryptCore.Examples.CyclicGroupDDH

derive_reduction receiverReduction

/-- **Time of the receiver reduction.** A distinguisher `A` of time at most `T` and call cost at
most `a`, with an exponentiation of cost at most `tp`, gives a reduction of time at most
`T + a + tp + 5`. -/
theorem receiverReduction.tree.timeBound_timed {G : Type} [CyclicGroupRing G] (sigma : Bool)
    (A : G × G × G × G → SPTree.Timed Bool) (ACost : G × G × G × G → ℕ) (c : DDHTriple G)
    (pow : CyclicGroup.Exp G → G) (powCost : CyclicGroup.Exp G → ℕ) {T a tp : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hp : ∀ e, powCost e ≤ tp) :
    SPTree.Timed.stepTime (receiverReduction.tree.timed sigma A ACost c pow powCost) ≤
      T + a + tp + 5 := by
  time_bound

end CatCrypt.Examples.OT

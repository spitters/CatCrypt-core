/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.CyclicGroupDDH
public import CatCryptCore.Tactics.DeriveTimed

/-!
# Cost of the exponentiation of a group element

The registered cost of `CyclicGroup.elemPow`, the exponentiation `x ^ a` of an element `x` of
the abstract cyclic group of `CatCryptCore.Examples.CyclicGroupDDH`. Its definition goes
through the discrete logarithm, which `derive_timed` cannot price, so the cost is registered by
`timed_cost`.

## Cost model

`elemPow x a` is priced like the exponentiation `pow a` of the generator: its cost is the cost
companion of the field `pow` of the group at `a`. The cost takes, after the arguments of
`elemPow`, the cost companions of the fields `pow` and `expMul` that its definition applies; the
companion of `expMul` is not charged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Examples.CyclicGroupDDH

-- The exponentiation `x ^ a` costs what the exponentiation `pow a` of the generator costs.
timed_cost CatCryptCore.Examples.CyclicGroupDDH.CyclicGroup.elemPow :=
  fun (G : Type) [CG : CyclicGroup G] (_x : G) (a : CG.Exp) (powCost : CG.Exp → ℕ)
    (_expMulCost : CG.Exp → CG.Exp → ℕ) => powCost a

/-- The registered cost of `elemPow x a` is the cost of `pow a` (the unfolding lemma of the
registration, read by `derive_time_bound`). -/
theorem CyclicGroup.elemPow.timedCost_eq (G : Type) [CG : CyclicGroup G] (x : G) (a : CG.Exp)
    (powCost : CG.Exp → ℕ) (expMulCost : CG.Exp → CG.Exp → ℕ) :
    CyclicGroup.elemPow.timedCost G x a powCost expMulCost = powCost a := rfl

end CatCryptCore.Examples.CyclicGroupDDH

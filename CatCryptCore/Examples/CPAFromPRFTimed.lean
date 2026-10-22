/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.CPAFromPRF
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the CPA-from-PRF reduction

The computation tree and costed form of `PRFEncScheme.cpaReduction` of
`CatCryptCore.Examples.CPAFromPRF`, derived by `derive_reduction`, and its time bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step; the combining
operation `xorOut` is a primitive with cost companion `xorOutCost`; the adversary call costs
its cost companion.

## Main results

* `PRFEncScheme.cpaReduction.tree.timeBound_timed` — an adversary of time `T` and call cost
  `a`, with a combining operation of cost at most `tx`, gives a distinguisher of time at most
  `T + a + tx + 2`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.CPAFromPRF

open CatCrypt.Core

derive_reduction PRFEncScheme.cpaReduction

/-- **Time of the CPA reduction.** An adversary `A` of time at most `T` and call cost at most
`a`, with a combining operation of cost at most `tx`, gives a distinguisher of time at most
`T + a + tx + 2`. -/
theorem PRFEncScheme.cpaReduction.tree.timeBound_timed (P : PRFEncScheme) (r : P.F.Input)
    (m : P.F.Output) (A : P.F.Input × P.F.Output → SPTree.Timed Bool)
    (ACost : P.F.Input × P.F.Output → ℕ) (y : P.F.Output)
    (xorOut : P.F.Output → P.F.Output → P.F.Output) (xorOutCost : P.F.Output → P.F.Output → ℕ)
    {T a tx : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hx : ∀ u v, xorOutCost u v ≤ tx) :
    SPTree.Timed.stepTime (PRFEncScheme.cpaReduction.tree.timed P r m A ACost y xorOut
      xorOutCost) ≤ T + a + tx + 2 := by
  time_bound

end CatCrypt.Examples.CPAFromPRF

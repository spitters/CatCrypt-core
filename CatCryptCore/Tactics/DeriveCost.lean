/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed

/-!
# Derived costs of recursive data functions

`derive_cost f` takes a computable data function `f`, recursive or not, and defines its cost
`f.timedCost` by the cost rules of `CatCryptCore.Tactics.DeriveTimed`. The cost takes the
arguments of `f`, each function-typed argument followed by its cost companion, and returns
`ℕ`; this is the convention of a registered cost, so `derive_timed` and `derive_reduction`
price every call of `f` through `f.timedCost` from then on.

## The body

The body priced is the one Lean keeps for the equation lemmas of `f`: for a structural or
well-founded recursion, the definition before its compilation to a recursor, in which the
recursive calls are applications of the constant `f`. For a non-recursive `f` it is the
definition itself.

## Cost rules

The rules are those of `derive_timed` for data terms (call-by-value):

* a call costs one plus the callee's cost at its arguments plus the costs of its arguments;
  a recursive call of `f` is priced by `f.timedCost` itself, so the cost is defined by the
  recursion of `f`, settled by Lean as a structural or well-founded recursion;
* a call of a function-typed parameter is priced by its cost companion;
* `if` and `match` cost one, plus the condition or the discriminants, plus the branch taken;
* constructors, literals, projections, casts and variables are free;
* a `let` of first-order data is priced once, and an unfolded definition prices each of its
  arguments once.

The derivation is `deriveCostCore` of `CatCryptCore.Tactics.DeriveTimed`, which also derives
the cost of a recursive callee on demand during `derive_timed`.

A class method on a local instance has no definition to price. `derive_cost (unit := m₁ … mₙ) f`
charges each listed method `mᵢ` on a local instance one unit plus its arguments; the listing
is a trusted statement about those methods, in the way a registered primitive cost is.

## What is refused

`f` whose result is a tree of a registered kind (use `derive_timed`), a callee that is
recursive or opaque and has no cost, a class method on a local instance that is not listed in
`unit`, and every refusal of the data rules of `derive_timed`. A cost whose recursion Lean
cannot settle is refused with Lean's reason.

The derivation reads the body of the equation lemmas as Ironwood's `assert_efficient` does
(D.-E. Hopwood, `Zcash/Meta/Efficient.lean`, dual-licensed under the MIT and Apache-2.0
licences).

## Main definitions

* `derive_cost f`, `derive_cost (unit := m₁ … mₙ) f` — define the cost `f.timedCost`
-/

public section

meta section

namespace CatCrypt.Tactics.DeriveCost

open Lean Elab Meta Term Command
open CatCrypt.Tactics.DeriveTimed

/-- `derive_cost f` defines the cost `f.timedCost` of the data function `f` by the recursion
of `f`; `derive_cost (unit := m₁ … mₙ) f` charges the class methods `mᵢ` on local instances
one unit. -/
syntax (name := deriveCostCmd) "derive_cost " ("(" &"unit" " := " ident+ ") ")? ident : command

@[command_elab deriveCostCmd]
def elabDeriveCost : CommandElab := fun stx => do
  liftTermElabM do
    -- The optional group `(unit := m₁ … mₙ)` is a node of five children when present.
    let units ← if stx[1].getNumArgs == 5 then
        stx[1][3].getArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
      else pure #[]
    deriveCostCore units (← realizeGlobalConstNoOverloadWithInfo stx[2])

end CatCrypt.Tactics.DeriveCost

end

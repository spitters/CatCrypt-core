/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveCost
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests for the mutual-block rule of `derive_cost`

* `TE`: terms whose operations take a list of terms (a nested inductive type).
* `TE.vars` and `TE.varsList`: the variables of a term and of a list of terms, a mutual
  structural recursion over the nested type. `derive_cost TE.vars` defines both costs,
  `TE.vars.timedCost` and `TE.varsList.timedCost`, as one mutual structural recursion.
* `TE.size` and `TE.sizeList`: the size of a term and of a list of terms; the costs of the
  block are derived on demand when `derive_cost TE.sizeTwice` prices a call of `TE.size`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveCostMutualTest

/-- Terms whose operations take a list of terms. -/
inductive TE where
  | var : Nat → TE
  | op : List TE → TE

mutual
/-- The variables of a term. -/
def TE.vars : TE → List Nat
  | .var n => [n]
  | .op ts => TE.varsList ts
/-- The variables of a list of terms. -/
def TE.varsList : List TE → List Nat
  | [] => []
  | t :: ts => TE.vars t ++ TE.varsList ts
end

derive_cost TE.vars

mutual
/-- The size of a term. -/
def TE.size : TE → Nat
  | .var _ => 1
  | .op ts => TE.sizeList ts + 1
/-- The size of a list of terms. -/
def TE.sizeList : List TE → Nat
  | [] => 0
  | t :: ts => TE.size t + TE.sizeList ts
end

/-- Twice the size of a term. -/
def TE.sizeTwice (t : TE) : Nat := TE.size t + TE.size t

derive_cost TE.sizeTwice

end CatCrypt.Tactics.DeriveCostMutualTest

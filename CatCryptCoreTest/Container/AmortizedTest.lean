/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.Amortized

/-!
# Tests of amortized cost over a state object

A fresh state object, none taken from a handler: a stack of natural numbers, whose potential is
its length; a step pushes a value and demands one clock tick plus one tick for each entry it
scans, `1 + n` at a stack of length `n`. Three steps from the empty stack cost `1 + 2 + 3 = 6`,
the sum of the demands along the states (`Clocked.iter_potential_cost`), and at most
`3 * (1 + 3) = 12` by the amortized bound (`Clocked.iter_potential_cost_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Container.AmortizedTest

open CatCrypt.Container

/-- A push onto a stack whose demand is one tick plus one tick per entry. -/
def push : Clocked (List ℕ) (List ℕ) :=
  Clocked.potential List.length (fun n => 1 + n) (List.cons 0)

/-- Three pushes from the empty stack cost six ticks. -/
example : (push.iter 3).cost [] = 6 := rfl

/-- The demand of a data token at a stack of length two is three ticks. -/
example : (Clocked.toDN push).toFunB [1, 2] false = {false} + 3 • {true} :=
  Clocked.toDN_potential_false _ _ _ _

/-- The amortized bound: `q` pushes from a stack of length `n` cost at most `q * (1 + (n + q))`. -/
example (q : ℕ) (l : List ℕ) : (push.iter q).cost l ≤ q * (1 + (l.length + q * 1)) :=
  Clocked.iter_potential_cost_le List.length (fun _ _ h => Nat.add_le_add_left h 1) _
    (fun _ => le_rfl) q l

/-- At the object of potentials, two steps of demand `2 * n` and growth `3` from `1` cost
`2 * 1 + 2 * 4 = 10`. -/
example : ((Clocked.potStep (fun n => 2 * n) 3).iter 2).cost 1 = 10 := rfl

end CatCrypt.Container.AmortizedTest

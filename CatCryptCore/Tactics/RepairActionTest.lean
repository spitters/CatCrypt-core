/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.RepairAction

/-!
# Leaves for the grind repair code action

Seven tactic leaves on which the code action of `CatCryptCore.Tactics.RepairAction` is
requested at the leaf's line. Each declaration is wrapped in `#guard_msgs (drop all)`, so
that the failing tactics and the open goals elaborate without diagnostics.

| leaf | goal | arm expected to close |
|---|---|---|
| `skip` | `a < b + 1` from `a ≤ b` | `grind` |
| `exact rfl` | `(xs ++ []).length = xs.length` | `grind` |
| `simp only [triple]` | `triple n = 3 * n` | `grind [triple]` |
| `skip` | `a * b = a + b` (false) | none |
| `simp [sumTo]` | `2 * sumTo n = n * (n + 1)` (needs induction) | none |
| `exact hp` | `p ∧ q` | `grind` |
| `skip` inside `have` | `a + 1 < c` | `grind` |
-/

set_option autoImplicit false

namespace CatCryptCore.RepairActionTest

/-- Three times `n`, as an opaque definition. -/
def triple (n : Nat) : Nat := n + n + n

/-- The sum `0 + 1 + ⋯ + n`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

#guard_msgs (drop all) in
example (a b : Nat) (h : a ≤ b) : a < b + 1 := by
  skip

#guard_msgs (drop all) in
example (xs : List Nat) : (xs ++ []).length = xs.length := by
  exact rfl

#guard_msgs (drop all) in
example (n : Nat) : triple n = 3 * n := by
  simp only [triple]

#guard_msgs (drop all) in
example (a b : Nat) : a * b = a + b := by
  skip

#guard_msgs (drop all) in
example (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  simp [sumTo]

#guard_msgs (drop all) in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact hp

#guard_msgs (drop all) in
example (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := by
  have h : a + 1 < c := by
    skip
  omega

end CatCryptCore.RepairActionTest

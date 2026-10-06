/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.ENNReal.Basic

/-!
# The grade interface `GradeQuantale`

A graded program logic consumes four pieces of structure on its grades:
addition, its unit, the order, and arbitrary suprema. `GradeQuantale` bundles
that fragment: a complete lattice with an ordered commutative addition whose
unit is the least element. The instance at `ℝ≥0∞` is the Lawvere quantale
`([0, ∞], ≤, +, 0)` without its distributive law.

`sSup`-distributivity of addition (the full quantale law, Mathlib's
`AddQuantale`) is not a field: the laws stated over this interface use suprema
only through `iSup_le` and `le_iSup`, so `GradeQuantale` is weaker than
`AddQuantale`.

## Main definitions

* `GradeQuantale`: a complete lattice with an ordered commutative addition whose unit is
  the least element; instance at `ℝ≥0∞`.

## Main results

* `GradeQuantale.le_add_right`, `GradeQuantale.le_add_left`: a summand is below the sum.
* `GradeQuantale.bot_eq_zero`: the additive unit is the least element.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Bridge

open scoped ENNReal

/-! ## The grade interface -/

/-- The fragment of quantale structure the graded layer consumes:
a complete lattice with an ordered commutative addition whose unit is
the least element. `sSup`-distributivity of `+` is deliberately not
demanded — no law of the graded layer uses it. -/
class GradeQuantale (V : Type*) extends CompleteLattice V, AddCommMonoid V where
  /-- Addition is monotone in both arguments. -/
  protected add_le_add : ∀ {a b c d : V}, a ≤ b → c ≤ d → a + c ≤ b + d
  /-- The additive unit is the least grade. -/
  protected zero_le : ∀ a : V, 0 ≤ a

namespace GradeQuantale

variable {V : Type*} [GradeQuantale V]

theorem add_le_add' {a b c d : V} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a + c ≤ b + d :=
  GradeQuantale.add_le_add h₁ h₂

theorem zero_le' (a : V) : 0 ≤ a := GradeQuantale.zero_le a

theorem le_add_right (a b : V) : a ≤ a + b :=
  (add_zero a).symm.trans_le (add_le_add' le_rfl (zero_le' b))

theorem le_add_left (a b : V) : b ≤ a + b :=
  (zero_add b).symm.trans_le (add_le_add' (zero_le' a) le_rfl)

/-- The additive unit is the lattice bottom: `0 ≤ ⊥` from the interface,
`⊥ ≤ 0` from the lattice. -/
theorem bot_eq_zero : (⊥ : V) = 0 :=
  le_antisymm bot_le (zero_le' ⊥)

end GradeQuantale

/-- `ℝ≥0∞` carries the grade interface. -/
noncomputable instance : GradeQuantale ℝ≥0∞ where
  add_le_add h₁ h₂ := add_le_add h₁ h₂
  zero_le := fun _ => zero_le

end CatCrypt.Bridge

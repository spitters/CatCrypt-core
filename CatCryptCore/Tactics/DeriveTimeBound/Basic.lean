/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.MinMax

/-!
# Affine bound lemmas of `derive_time_bound`

The lemmas `DeriveTimeBound.affine_*` on bounds `e ≤ a + b * X` that the time theorems derived by
`derive_time_bound` (`CatCryptCore.Tactics.DeriveTimeBound`) are assembled from, and the bound of
a dependent `if` by the maximum of its branches. Users that state or prove with these import this
module publicly and the procedure privately.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBound

/-! ## Rule lemmas -/

/-- A `dite` over `ℕ` is at most the maximum of the bounds of its branches. -/
theorem dite_le_max_of {c : Prop} [Decidable c] {t : c → ℕ} {f : ¬c → ℕ} {a b : ℕ}
    (ht : ∀ h, t h ≤ a) (hf : ∀ h, f h ≤ b) : dite c t f ≤ max a b := by
  by_cases h : c
  · rw [dite_eq_left h]
    exact le_max_of_le_left (ht h)
  · rw [dite_eq_right h]
    exact le_max_of_le_right (hf h)

/-! The clauses of the affine bound `e ≤ a + b * X` of a step cost in one atom `X`
(`affineLe`, the simulation rule). -/

/-- The atom is its own affine bound. -/
theorem affine_self (X : ℕ) : X ≤ 0 + 1 * X := by omega

/-- A term bounded free of the atom has coefficient `0`. -/
theorem affine_const {e a : ℕ} (X : ℕ) (h : e ≤ a) : e ≤ a + 0 * X := by omega

/-- The affine bound of a sum is the sum of the affine bounds. -/
theorem affine_add {e₁ e₂ a₁ a₂ b₁ b₂ X : ℕ} (h₁ : e₁ ≤ a₁ + b₁ * X) (h₂ : e₂ ≤ a₂ + b₂ * X) :
    e₁ + e₂ ≤ (a₁ + a₂) + (b₁ + b₂) * X := by
  rw [Nat.add_mul]
  omega

/-- The affine bound of a product by a factor `k` free of the atom. -/
theorem affine_mul_left {e a b X : ℕ} (k : ℕ) (h : e ≤ a + b * X) :
    k * e ≤ k * a + (k * b) * X := by
  calc k * e ≤ k * (a + b * X) := Nat.mul_le_mul_left k h
    _ = k * a + (k * b) * X := by rw [Nat.mul_add, Nat.mul_assoc]

/-- The affine bound of a product by a factor `k` free of the atom, on the right. -/
theorem affine_mul_right {e a b X : ℕ} (k : ℕ) (h : e ≤ a + b * X) :
    e * k ≤ a * k + (b * k) * X := by
  calc e * k ≤ (a + b * X) * k := Nat.mul_le_mul_right k h
    _ = a * k + (b * k) * X := by rw [Nat.add_mul, Nat.mul_right_comm]

/-- The affine bound of a maximum: the maximum of the constants and a coefficient above both. -/
theorem affine_max {e₁ e₂ a₁ a₂ b₁ b₂ b X : ℕ} (h₁ : e₁ ≤ a₁ + b₁ * X) (h₂ : e₂ ≤ a₂ + b₂ * X)
    (hb₁ : b₁ ≤ b) (hb₂ : b₂ ≤ b) : max e₁ e₂ ≤ max a₁ a₂ + b * X := by
  have := Nat.mul_le_mul_right X hb₁
  have := Nat.mul_le_mul_right X hb₂
  omega

/-- An affine bound `e ≤ a + b * X` with `b ≤ 1` is a bound `X + a`: the growth of a state
component read through `X`. -/
theorem affine_le_self_add {e a b X : ℕ} (h : e ≤ a + b * X) (hb : b ≤ 1) : e ≤ X + a := by
  have := Nat.mul_le_mul_right X hb
  omega

end CatCrypt.Tactics.DeriveTimeBound

end

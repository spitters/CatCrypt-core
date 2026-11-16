/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.ForMathlib.Tactic.PositivityMatrix

/-!
# Tests for the matrix `positivity` extensions and the tactic `psd`

One goal per clause of the grammar of the Loewner cone: Gram matrices and congruences for
rectangular factors, sums, finite sums, nonnegative scalars, Kronecker products, compressions,
reindexing, diagonal and block diagonal matrices, rank-one matrices, `0`, `1`, the functions of
the continuous functional calculus, star projections and differences `b - a` with `a ≤ b`; the
three goal forms of `psd`; and the report of `psd?`.
-/

set_option autoImplicit false

open Matrix

section Positivity

open scoped MatrixOrder ComplexOrder Kronecker

variable {n m k : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype k] [DecidableEq k]

example (c : Matrix m n ℂ) : 0 ≤ cᴴ * c := by positivity
example (c : Matrix n m ℂ) : 0 ≤ c * cᴴ := by positivity
example (a : Matrix m m ℂ) (c : Matrix m n ℂ) (ha : a.PosSemidef) : 0 ≤ cᴴ * a * c := by
  positivity
example (a : Matrix m m ℂ) (c : Matrix n m ℂ) (ha : 0 ≤ a) : 0 ≤ c * a * cᴴ := by positivity
example (a : Matrix m m ℂ) (c : Matrix m n ℂ) (ha : a.PosSemidef) : 0 ≤ cᴴ * (a * c) := by
  positivity
example (a : Matrix n n ℂ) (c : Matrix n n ℂ) (ha : 0 ≤ a) : 0 ≤ star c * a * c := by
  positivity
example (a b : Matrix n n ℂ) (ha : a.PosSemidef) (hb : b.PosSemidef) : 0 ≤ a + b := by
  positivity
example (a : Matrix n n ℂ) (ha : a.PosSemidef) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ r • a := by
  positivity
example (ρ : k → Matrix n n ℂ) (hρ : ∀ i, (ρ i).PosSemidef) : 0 ≤ ∑ i, ρ i := by positivity
example (a : Matrix n n ℂ) (b : Matrix m m ℂ) (ha : a.PosSemidef) (hb : b.PosSemidef) :
    0 ≤ a ⊗ₖ b := by positivity
example (a : Matrix n n ℂ) (ha : a.PosSemidef) (e : m → n) : 0 ≤ a.submatrix e e := by
  positivity
example (a : Matrix n n ℂ) (ha : a.PosSemidef) (e : n ≃ m) : 0 ≤ reindex e e a := by
  positivity
example (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) : 0 ≤ diagonal (fun i => (d i : ℂ)) := by
  positivity
example (v : n → ℂ) : 0 ≤ vecMulVec v (star v) := by positivity
example (M : k → Matrix n n ℂ) (hM : ∀ i, (M i).PosSemidef) : 0 ≤ blockDiagonal M := by
  positivity
example (a : Matrix n n ℂ) : 0 ≤ CFC.sqrt a := by positivity
example (a : Matrix n n ℂ) : 0 ≤ cfc Real.sqrt a := by positivity
example (p : Matrix n n ℂ) (hp : IsStarProjection p) : 0 ≤ 1 - p := by positivity
example (a b : Matrix n n ℂ) (h : a ≤ b) : 0 ≤ b - a := by positivity
example (a b : Matrix n n ℂ) (c : Matrix n m ℂ) (h : a ≤ b) : 0 ≤ cᴴ * (b - a) * c := by
  positivity

/-- The congruence `(1 - F)ᴴ M (1 - F)` of `Quantum/PowersStormer.lean`. -/
example (F M : Matrix n n ℂ) (hM : M.PosSemidef) : 0 ≤ (1 - F)ᴴ * M * (1 - F) := by positivity

end Positivity

section Psd

open scoped Kronecker ComplexOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

example : (0 : Matrix n n ℂ).PosSemidef := by psd
example : (1 : Matrix n n ℂ).PosSemidef := by psd
example (a : Matrix m m ℂ) (c : Matrix m n ℂ) (ha : a.PosSemidef) :
    (cᴴ * a * c).PosSemidef := by psd
example (a b : Matrix n n ℂ) (ha : a.PosDef) (hb : b.PosSemidef) : (a + b).PosSemidef := by psd
example (c : Matrix m n ℝ) : (cᴴ * c).PosSemidef := by psd
example (p : Matrix n n ℂ) (c : Matrix n m ℂ) (hp : IsStarProjection p) :
    (cᴴ * (1 - p) * c).PosSemidef := by psd

/-- The sum of Kronecker products of `Quantum/BB84KeySecrecy.lean`. -/
example {Θ : Type} [Fintype Θ] (D : Θ → Matrix n n ℂ) (hD : ∀ θ, (D θ).PosSemidef)
    (v : Θ → m → ℂ) : (∑ θ, D θ ⊗ₖ vecMulVec (v θ) (star (v θ))).PosSemidef := by psd

example {R : Type} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] (a c : R) :
    a ≤ a + star c * c := by psd

section Loewner

open scoped MatrixOrder

example : (0 : Matrix n n ℂ) ≤ 1 := by psd
example (a : Matrix n n ℂ) (z : ℂ) (hz : 0 ≤ z) (ha : a.PosSemidef) : 0 ≤ z • a := by psd
example (a b c : Matrix n n ℂ) (ha : a.PosSemidef) : b ≤ b + cᴴ * a * c := by psd
example (e : n ≃ m) (a b : Matrix n n ℂ) (hab : a ≤ b) (d : m → ℝ) (hd : ∀ i, 0 ≤ d i) :
    0 ≤ reindex e e (b - a) + diagonal (fun i => (d i : ℂ)) := by psd

end Loewner

/--
error: psd? failed: no rule of the positive cone proves `0 ≤ _` for the subterm
  b
of
  kroneckerMap (fun x1 x2 ↦ x1 * x2) a (b + vecMulVec v (star v))
-/
#guard_msgs in
example (a : Matrix n n ℂ) (b : Matrix m m ℂ) (ha : a.PosSemidef) (v : m → ℂ) :
    (a ⊗ₖ (b + vecMulVec v (star v))).PosSemidef := by psd?

/-- info: psd? closes the goal; `psd` does the same -/
#guard_msgs in
example (a : Matrix n n ℂ) (b : Matrix m m ℂ) (ha : a.PosSemidef) (hb : b.PosSemidef)
    (v : m → ℂ) : (a ⊗ₖ (b + vecMulVec v (star v))).PosSemidef := by psd?

end Psd

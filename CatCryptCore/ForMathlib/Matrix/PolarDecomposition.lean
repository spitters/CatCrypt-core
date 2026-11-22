/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.Matrix.ProjectorRewinding
public import CatCryptCore.ForMathlib.Matrix.Schmidt
public import CatCryptCore.ForMathlib.Tactic.PositivityMatrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Polar decomposition of a rectangular complex matrix

From the Schmidt decomposition `C = ∑ₖ sₖ aₖ bₖᵀ`, the matrix `P = ∑ₖ sₖ conj bₖ bₖᵀ` is
positive semidefinite with `P² = Cᴴ C`, hence `P = √(Cᴴ C)` by uniqueness of the square
root, and `W = ∑ₖ aₖ bₖᵀ` satisfies `C = W P`. The matrix `W` is an isometry on the support
of `P`, and `W`, `Wᴴ` are contractions because `W Wᴴ W = W`.

## Main results

* `Matrix.exists_eq_mul_sqrt_conjTranspose_mul_self` — the polar decomposition
  `C = W √(Cᴴ C)` with `W` a partial isometry.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013,
  §7.3 (the polar form).
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Cancelling `Aᴴ` against `A` when `Aᴴ A = 1`. -/
theorem conjTranspose_mul_mul_cancel {m' ι p : Type*} [Fintype m'] [Fintype ι] [DecidableEq ι]
    (A : Matrix m' ι ℂ) (hA : Aᴴ * A = 1) (X : Matrix ι p ℂ) : Aᴴ * (A * X) = X := by
  rw [← Matrix.mul_assoc, hA, Matrix.one_mul]

open scoped Classical in
/-- A matrix with `W Wᴴ W = W` is a contraction. -/
theorem norm_mulVec_le_of_mul_conjTranspose_mul_eq (W : Matrix m n ℂ)
    (h : W * Wᴴ * W = W) (x : n → ℂ) :
    ‖WithLp.toLp 2 (W *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  have hQ : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W, h]
  have hpsd : (1 - Wᴴ * W).PosSemidef := by
    have : (1 - Wᴴ * W) = (1 - Wᴴ * W)ᴴ * (1 - Wᴴ * W) := by
      simp [Matrix.sub_mul, Matrix.mul_sub, hQ, conjTranspose_sub]
    rw [this]
    psd
  have hnn := hpsd.re_dotProduct_nonneg x
  have key : ‖(WithLp.toLp 2 (W *ᵥ x) : EuclideanSpace ℂ m)‖ ^ 2 ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 := by
    rw [norm_toLp_sq_eq_re_star_dotProduct, norm_toLp_sq_eq_re_star_dotProduct]
    simp only [sub_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_sub, RCLike.re_to_complex,
      Complex.sub_re, sub_nonneg, star_mulVec] at hnn ⊢
    rwa [dotProduct_mulVec] at hnn
  exact le_of_sq_le_sq key (norm_nonneg _)

open scoped Classical in
/-- The polar decomposition of `C = A D Bcᴴ` for `A`, `Bc` with orthonormal columns and `D` a
nonnegative real diagonal matrix. -/
theorem polar_of_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix m n ℂ)
    (A : Matrix m ι ℂ) (Bc : Matrix n ι ℂ) (s : ι → ℝ) (hs : ∀ k, 0 ≤ s k)
    (hA : Aᴴ * A = 1) (hB : Bcᴴ * Bc = 1) (hC : C = A * diagonal (fun k => (s k : ℂ)) * Bcᴴ) :
    C = (A * Bcᴴ) * CFC.sqrt (Cᴴ * C) ∧
      (A * Bcᴴ)ᴴ * (A * Bcᴴ) * CFC.sqrt (Cᴴ * C) = CFC.sqrt (Cᴴ * C) ∧
      (∀ x, ‖WithLp.toLp 2 ((A * Bcᴴ) *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) ∧
      (∀ y, ‖WithLp.toLp 2 ((A * Bcᴴ)ᴴ *ᵥ y)‖ ≤ ‖WithLp.toLp 2 y‖) := by
  set D : Matrix ι ι ℂ := diagonal (fun k => (s k : ℂ)) with hDdef
  have hDh : Dᴴ = D := by
    ext i j
    simp only [hDdef, conjTranspose_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hCC : Cᴴ * C = Bc * (D * D) * Bcᴴ := by
    rw [hC]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hDh, Matrix.mul_assoc,
      conjTranspose_mul_mul_cancel, hA]
  have hDpsd : D.PosSemidef := by
    rw [hDdef, posSemidef_diagonal_iff]
    intro i
    simp [hs i]
  have hPpsd : (Bc * D * Bcᴴ).PosSemidef := hDpsd.mul_mul_conjTranspose_same Bc
  have hP : CFC.sqrt (Cᴴ * C) = Bc * D * Bcᴴ := by
    have h1 : 0 ≤ Cᴴ * C := Matrix.nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self C)
    have h2 : 0 ≤ Bc * D * Bcᴴ := Matrix.nonneg_iff_posSemidef.mpr hPpsd
    rw [CFC.sqrt_eq_iff _ _ h1 h2, hCC]
    simp only [Matrix.mul_assoc, conjTranspose_mul_mul_cancel, hB]
  have hWWW : (A * Bcᴴ) * (A * Bcᴴ)ᴴ * (A * Bcᴴ) = A * Bcᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      conjTranspose_mul_mul_cancel, hA, hB]
  refine ⟨?_, ?_, norm_mulVec_le_of_mul_conjTranspose_mul_eq _ hWWW, fun y => ?_⟩
  · rw [hP, hC]
    simp only [Matrix.mul_assoc, conjTranspose_mul_mul_cancel, hB]
  · rw [hP]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      conjTranspose_mul_mul_cancel, hA, hB]
  · refine norm_mulVec_le_of_mul_conjTranspose_mul_eq _ ?_ y
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      conjTranspose_mul_mul_cancel, hA, hB]

open scoped Classical in
/-- **Polar decomposition** of a rectangular matrix: `C = W |C|` with `|C| = √(Cᴴ C)`, `W` an
isometry on the support of `|C|`, and `W`, `Wᴴ` contractions. -/
theorem exists_eq_mul_sqrt_conjTranspose_mul_self (C : Matrix m n ℂ) :
    ∃ W : Matrix m n ℂ, C = W * CFC.sqrt (Cᴴ * C) ∧
      Wᴴ * W * CFC.sqrt (Cᴴ * C) = CFC.sqrt (Cᴴ * C) ∧
      (∀ x, ‖WithLp.toLp 2 (W *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) ∧
      (∀ y, ‖WithLp.toLp 2 (Wᴴ *ᵥ y)‖ ≤ ‖WithLp.toLp 2 y‖) := by
  obtain ⟨r, s, a, b, hs, ha, hb, hM⟩ := exists_schmidt C
  refine ⟨_, polar_of_factor C (Matrix.of fun i k => a k i)
    (Matrix.of fun j k => star (b k j)) s (fun k => (hs k).le) ?_ ?_ ?_⟩
  · ext k l
    simpa [Matrix.mul_apply, dotProduct, conjTranspose_apply, Matrix.one_apply] using ha k l
  · ext k l
    have := hb l k
    simp only [dotProduct, Pi.star_apply] at this
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply, of_apply, star_star]
    simp_rw [mul_comm (b k _)]
    rw [this]
    grind
  · ext i j
    simp only [Matrix.mul_apply, diagonal_apply, conjTranspose_apply, hM i j, of_apply,
      star_star]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact Finset.sum_congr rfl fun k _ => by ring

end Matrix

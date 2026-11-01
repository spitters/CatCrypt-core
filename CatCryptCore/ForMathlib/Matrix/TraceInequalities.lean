/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Trace inequalities for complex matrices

Mathlib candidates for `Mathlib/Analysis/Matrix/Order.lean`.

## Main results

* `Matrix.PosSemidef.exists_mul_self_eq` — a positive semidefinite matrix is the square of a
  positive semidefinite matrix.
* `Matrix.PosSemidef.re_trace_mul_nonneg` — `0 ≤ Re tr(A B)` for positive semidefinite
  `A`, `B`.
* `Matrix.re_trace_conjTranspose_mul_sq_le` — the Cauchy–Schwarz inequality for the
  Hilbert–Schmidt inner product: `(Re tr(Xᴴ Y))² ≤ Re tr(Xᴴ X) · Re tr(Yᴴ Y)`.
* `Matrix.PosDef.exists_fourthRoot` — a positive definite matrix `σ` has a Hermitian fourth
  root `a` with Hermitian two-sided inverse `b`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A positive semidefinite complex matrix is the square of a positive semidefinite
matrix (its square root `CFC.sqrt B`). -/
theorem PosSemidef.exists_mul_self_eq {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    ∃ R : Matrix n n ℂ, R.PosSemidef ∧ R * R = B := by
  classical
  exact ⟨CFC.sqrt B, nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B),
    CFC.sqrt_mul_sqrt_self B hB.nonneg⟩

/-- The trace of a product of two positive semidefinite complex matrices has nonnegative
real part. -/
theorem PosSemidef.re_trace_mul_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  obtain ⟨R, hR, hRR⟩ := hB.exists_mul_self_eq
  have h := (hA.conjTranspose_mul_mul_same R).trace_nonneg
  rw [hR.isHermitian.eq] at h
  have htr : (R * A * R).trace = (A * B).trace := by
    rw [← hRR, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [htr] at h
  exact (Complex.nonneg_iff.mp h).1

/-- The real part of `tr(Xᴴ X)` is nonnegative. -/
theorem re_trace_conjTranspose_mul_self_nonneg (X : Matrix n n ℂ) :
    0 ≤ (Xᴴ * X).trace.re :=
  (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self X).trace_nonneg).1

/-- **Cauchy–Schwarz for the Hilbert–Schmidt inner product**:
`(Re tr(Xᴴ Y))² ≤ Re tr(Xᴴ X) · Re tr(Yᴴ Y)`. -/
theorem re_trace_conjTranspose_mul_sq_le (X Y : Matrix n n ℂ) :
    (Xᴴ * Y).trace.re ^ 2 ≤ (Xᴴ * X).trace.re * (Yᴴ * Y).trace.re := by
  have hYX : (Yᴴ * X).trace.re = (Xᴴ * Y).trace.re := by
    rw [← conjTranspose_conjTranspose X, ← conjTranspose_mul, trace_conjTranspose,
      conjTranspose_conjTranspose]
    simp
  have hquad : ∀ t : ℝ, 0 ≤ (Yᴴ * Y).trace.re * (t * t)
      + 2 * (Xᴴ * Y).trace.re * t + (Xᴴ * X).trace.re := by
    intro t
    have h := re_trace_conjTranspose_mul_self_nonneg (X + (t : ℂ) • Y)
    have hexp : (X + (t : ℂ) • Y)ᴴ * (X + (t : ℂ) • Y)
        = Xᴴ * X + (t : ℂ) • (Xᴴ * Y) + (t : ℂ) • (Yᴴ * X)
          + ((t : ℂ) * t) • (Yᴴ * Y) := by
      simp only [conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      abel
    rw [hexp] at h
    simp only [trace_add, trace_smul, Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul,
      hYX] at h
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul] at h
    linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

/-- A positive definite complex matrix `σ` has a Hermitian fourth root `a`
(`a * a * (a * a) = σ`) whose two-sided inverse `b` is Hermitian. -/
theorem PosDef.exists_fourthRoot [DecidableEq n] {σ : Matrix n n ℂ} (hσ : σ.PosDef) :
    ∃ a b : Matrix n n ℂ, aᴴ = a ∧ bᴴ = b ∧ a * b = 1 ∧ b * a = 1 ∧ a * a * (a * a) = σ := by
  obtain ⟨r, hr, hrr⟩ := hσ.posSemidef.exists_mul_self_eq
  obtain ⟨a, ha, haa⟩ := hr.exists_mul_self_eq
  have h4 : a * a * (a * a) = σ := by rw [haa, hrr]
  have hdet : IsUnit a.det := by
    have hσd : σ.det ≠ 0 := (hσ.det_pos).ne'
    rw [← h4, det_mul, det_mul] at hσd
    exact isUnit_iff_ne_zero.mpr fun h0 => hσd (by rw [h0]; ring)
  refine ⟨a, a⁻¹, ha.isHermitian.eq, ?_, mul_nonsing_inv a hdet, nonsing_inv_mul a hdet, h4⟩
  rw [conjTranspose_nonsing_inv, ha.isHermitian.eq]

end Matrix

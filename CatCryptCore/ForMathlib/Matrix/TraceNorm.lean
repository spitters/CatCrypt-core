/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.Matrix.PolarDecomposition
public import CatCryptCore.ForMathlib.Matrix.TraceDual

/-!
# The trace norm of a complex matrix

The trace norm `‖M‖₁ = Re tr √(Mᴴ M)` is the sum of the singular values of `M`. By trace
duality it is the maximum of `‖tr(K M)‖` over contractions `K`, attained at a unitary.

## Main definitions

* `Matrix.traceNorm` — the trace norm `Re tr √(Mᴴ M)`.

## Main results

* `Matrix.norm_trace_mul_le_traceNorm`, `Matrix.exists_unitary_trace_mul_eq_traceNorm` — trace
  duality: `‖tr(K M)‖ ≤ ‖M‖₁` for contractions `K`, with equality at a unitary.
* `Matrix.re_trace_le_traceNorm` — `Re tr M ≤ ‖M‖₁`.
* `Matrix.traceNorm_conjTranspose` — `‖Mᴴ‖₁ = ‖M‖₁`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018, §1.1.3.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The trace norm `‖M‖₁ = Re tr √(Mᴴ M)` of a complex matrix, the sum of its singular
values. -/
noncomputable def traceNorm (M : Matrix m n ℂ) : ℝ :=
  (CFC.sqrt (Mᴴ * M)).trace.re

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg (M : Matrix m n ℂ) : 0 ≤ M.traceNorm := by
  have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Mᴴ * M))).trace_nonneg
  exact (Complex.nonneg_iff.mp h).1

/-- The trace norm is the sum of the singular values of a Schmidt decomposition. -/
private theorem traceNorm_eq_sum_of_schmidt (M : Matrix n n ℂ) {r : ℕ} (s : Fin r → ℝ)
    (a b : Fin r → n → ℂ) (hs : ∀ k, 0 < s k)
    (ha : ∀ k l, star (a k) ⬝ᵥ a l = if k = l then 1 else 0)
    (hb : ∀ k l, star (b k) ⬝ᵥ b l = if k = l then 1 else 0)
    (hM : ∀ i j, M i j = ∑ k, (s k : ℂ) * a k i * b k j) :
    M.traceNorm = ∑ k, s k := by
  set A : Matrix n (Fin r) ℂ := Matrix.of fun i k => a k i with hAdef
  set Bc : Matrix n (Fin r) ℂ := Matrix.of fun j k => star (b k j) with hBdef
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal (fun k => (s k : ℂ)) with hDdef
  have hA : Aᴴ * A = 1 := by
    ext k l
    simpa [mul_apply, dotProduct, conjTranspose_apply, one_apply, hAdef] using ha k l
  have hB : Bcᴴ * Bc = 1 := by
    ext k l
    have := hb l k
    simp only [dotProduct, Pi.star_apply] at this
    simp only [mul_apply, conjTranspose_apply, one_apply, of_apply, star_star, hBdef]
    simp_rw [mul_comm (b k _)]
    rw [this]
    grind
  have hC : M = A * D * Bcᴴ := by
    ext i j
    simp only [mul_apply, diagonal_apply, conjTranspose_apply, hM i j, of_apply, star_star,
      hAdef, hBdef, hDdef]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hDh : Dᴴ = D := by
    ext i j
    simp only [hDdef, conjTranspose_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hCC : Mᴴ * M = Bc * (D * D) * Bcᴴ := by
    rw [hC]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hDh, Matrix.mul_assoc,
      conjTranspose_mul_mul_cancel, hA]
  have hDpsd : D.PosSemidef := by
    rw [hDdef, posSemidef_diagonal_iff]
    intro i
    simp [(hs i).le]
  have hP : CFC.sqrt (Mᴴ * M) = Bc * D * Bcᴴ := by
    have h1 : 0 ≤ Mᴴ * M := Matrix.nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self M)
    have h2 : 0 ≤ Bc * D * Bcᴴ :=
      Matrix.nonneg_iff_posSemidef.mpr (hDpsd.mul_mul_conjTranspose_same Bc)
    rw [CFC.sqrt_eq_iff _ _ h1 h2, hCC]
    simp only [Matrix.mul_assoc, conjTranspose_mul_mul_cancel, hB]
  have htr : (CFC.sqrt (Mᴴ * M)).trace = ((∑ k, s k : ℝ) : ℂ) := by
    rw [hP, trace_mul_comm, conjTranspose_mul_mul_cancel Bc hB, hDdef]
    simp
  rw [traceNorm, htr, Complex.ofReal_re]

/-- **Trace duality, upper bound.** For a contraction `K`, `‖tr(K M)‖ ≤ ‖M‖₁`. -/
theorem norm_trace_mul_le_traceNorm (M K : Matrix n n ℂ)
    (hK : ∀ x, ‖WithLp.toLp 2 (K *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) :
    ‖(K * M).trace‖ ≤ M.traceNorm := by
  obtain ⟨r, s, a, b, hs, ha, hb, hM⟩ := exists_schmidt M
  rw [traceNorm_eq_sum_of_schmidt M s a b hs ha hb hM]
  have htr : (K * M).trace = ∑ k, (s k : ℂ) * (b k ⬝ᵥ (K *ᵥ a k)) := by
    simp only [trace, diag_apply, mul_apply, hM, mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hn : ∀ v : n → ℂ, star v ⬝ᵥ v = 1 → ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ = 1 := by
    intro v hv
    have : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      have h2 := congrArg Complex.re hv
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simpa [dotProduct, Complex.mul_re, Complex.conj_re] using h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  have hcs : ∀ k, ‖b k ⬝ᵥ (K *ᵥ a k)‖ ≤ 1 := by
    intro k
    have hb1 : star (star (b k)) ⬝ᵥ star (b k) = 1 := by
      have h := congrArg star (hb k k)
      simp only [star_dotProduct, dotProduct_comm] at h ⊢
      simpa [apply_ite] using h
    have ha1 : star (a k) ⬝ᵥ a k = 1 := by simpa using ha k k
    have hinner : b k ⬝ᵥ (K *ᵥ a k) =
        inner ℂ (WithLp.toLp 2 (star (b k)) : EuclideanSpace ℂ n) (WithLp.toLp 2 (K *ᵥ a k)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      simp
    rw [hinner]
    calc _ ≤ ‖(WithLp.toLp 2 (star (b k)) : EuclideanSpace ℂ n)‖ *
          ‖(WithLp.toLp 2 (K *ᵥ a k) : EuclideanSpace ℂ n)‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact (hn _ hb1).le
          · exact (hK _).trans (hn _ ha1).le
      _ = 1 := one_mul 1
  rw [htr]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  have h1 := hcs k
  rw [Complex.norm_real, Real.norm_of_nonneg (hs k).le]
  nlinarith [hs k]

/-- **Trace duality, attainment.** Some unitary `U` has `tr(U M) = ‖M‖₁`. -/
theorem exists_unitary_trace_mul_eq_traceNorm (M : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ, (U * M).trace = (M.traceNorm : ℂ) := by
  obtain ⟨U, hU, him, hU'⟩ := exists_unitary_forall_norm_trace_mul_le M
  obtain ⟨W, hWM, hWW, -, hWc⟩ := exists_eq_mul_sqrt_conjTranspose_mul_self M
  have hUc : ∀ x, ‖WithLp.toLp 2 (U *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
    refine norm_mulVec_le_of_mul_conjTranspose_mul_eq U ?_
    rw [Matrix.mem_unitaryGroup_iff] at hU
    rw [← star_eq_conjTranspose, hU, Matrix.one_mul]
  have hP : (CFC.sqrt (Mᴴ * M)).trace = (M.traceNorm : ℂ) := by
    have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Mᴴ * M))).trace_nonneg
    rw [traceNorm]
    exact (Complex.ext (by simp) (by simpa using (Complex.nonneg_iff.mp h).2.symm))
  have hlow : M.traceNorm ≤ (U * M).trace.re := by
    have h := hU' Wᴴ hWc
    have e : Wᴴ * M = CFC.sqrt (Mᴴ * M) :=
      calc Wᴴ * M = Wᴴ * (W * CFC.sqrt (Mᴴ * M)) := congrArg (Wᴴ * ·) hWM
        _ = Wᴴ * W * CFC.sqrt (Mᴴ * M) := (Matrix.mul_assoc _ _ _).symm
        _ = _ := hWW
    rw [e, hP, Complex.norm_real, Real.norm_of_nonneg (traceNorm_nonneg M)] at h
    exact h
  have hup := norm_trace_mul_le_traceNorm M U hUc
  refine ⟨U, hU, Complex.ext ?_ ?_⟩
  · exact le_antisymm ((Complex.re_le_norm _).trans hup) hlow
  · simpa using him

/-- The real part of the trace is at most the trace norm. -/
theorem re_trace_le_traceNorm (M : Matrix n n ℂ) : M.trace.re ≤ M.traceNorm := by
  have h := norm_trace_mul_le_traceNorm M 1 (fun x => by simp)
  rw [Matrix.one_mul] at h
  exact (Complex.re_le_norm _).trans h

/-- A square matrix and its conjugate transpose have the same trace norm. -/
theorem traceNorm_conjTranspose (M : Matrix n n ℂ) : Mᴴ.traceNorm = M.traceNorm := by
  have key : ∀ N : Matrix n n ℂ, N.traceNorm ≤ Nᴴ.traceNorm := by
    intro N
    obtain ⟨U, hU, hUN⟩ := exists_unitary_trace_mul_eq_traceNorm N
    have hc : ∀ x, ‖WithLp.toLp 2 (Uᴴ *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
      refine norm_mulVec_le_of_mul_conjTranspose_mul_eq Uᴴ ?_
      rw [Matrix.mem_unitaryGroup_iff'] at hU
      rw [conjTranspose_conjTranspose, ← star_eq_conjTranspose, hU, Matrix.one_mul]
    have h := norm_trace_mul_le_traceNorm Nᴴ Uᴴ hc
    have e : (Uᴴ * Nᴴ).trace = star (U * N).trace := by
      rw [← conjTranspose_mul, trace_conjTranspose, trace_mul_comm]
    rw [e, hUN] at h
    simpa [Complex.norm_real, Real.norm_of_nonneg (traceNorm_nonneg N)] using h
  exact le_antisymm (by simpa using key Mᴴ) (key M)

end Matrix

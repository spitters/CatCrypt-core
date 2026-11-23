/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.Matrix.TraceNorm
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The trace norm against the operator norm, and perturbation of a conjugation

With the `ℓ²` operator norm on square complex matrices, trace duality reads
`‖tr(K M)‖ ≤ ‖K‖ ‖M‖₁`. For contractions `U`, `V` and a positive semidefinite `ρ`, the
conjugations `U ρ Uᴴ` and `V ρ Vᴴ` are within `2 ‖U - V‖ tr ρ` in trace norm.

## Main results

* `Matrix.norm_trace_mul_le_norm_mul_traceNorm`: `‖tr(K M)‖ ≤ ‖K‖ ‖M‖₁`.
* `Matrix.PosSemidef.traceNorm_eq`: the trace norm of a positive semidefinite matrix is its
  trace.
* `Matrix.traceNorm_mul_mul_conjTranspose_sub_le`: `‖U ρ Uᴴ - V ρ Vᴴ‖₁ ≤ 2 ‖U - V‖ tr ρ`.
* `Matrix.re_trace_mul_le_add_traceNorm_sub`: for `‖E‖ ≤ 1`,
  `Re tr(E A) ≤ Re tr(E B) + ‖A - B‖₁`.

## Search words

trace norm, operator norm, Hölder inequality, trace duality, unitary perturbation, conjugation,
diamond norm bound, contraction
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix of `ℓ²` operator norm at most `1` is a contraction of the Euclidean norm. -/
theorem norm_toLp_mulVec_le_of_norm_le_one {K : Matrix n n ℂ} (hK : ‖K‖ ≤ 1) (x : n → ℂ) :
    ‖WithLp.toLp 2 (K *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  have h := K.l2_opNorm_mulVec (WithLp.toLp 2 x)
  calc _ ≤ ‖K‖ * ‖WithLp.toLp 2 x‖ := by simpa using h
    _ ≤ 1 * ‖WithLp.toLp 2 x‖ := by gcongr
    _ = _ := one_mul _

/-- Trace duality with the operator norm: `‖tr(K M)‖ ≤ ‖K‖ ‖M‖₁`. -/
theorem norm_trace_mul_le_norm_mul_traceNorm (K M : Matrix n n ℂ) :
    ‖(K * M).trace‖ ≤ ‖K‖ * M.traceNorm := by
  rcases (norm_nonneg K).eq_or_lt with h0 | hpos
  · rw [norm_eq_zero.mp h0.symm]; simp
  · set K' : Matrix n n ℂ := ((‖K‖⁻¹ : ℝ) : ℂ) • K with hK'
    have hK1 : ‖K'‖ ≤ 1 := by
      rw [hK', norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
        inv_mul_cancel₀ hpos.ne']
    have h := norm_trace_mul_le_traceNorm M K' (norm_toLp_mulVec_le_of_norm_le_one hK1)
    have he : (K * M).trace = (‖K‖ : ℂ) * (K' * M).trace := by
      rw [hK', Matrix.smul_mul, trace_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
    rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    gcongr

/-- The trace norm of a positive semidefinite matrix is its trace. -/
theorem PosSemidef.traceNorm_eq {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    ρ.traceNorm = ρ.trace.re := by
  rw [traceNorm, hρ.isHermitian.eq, CFC.sqrt_mul_self ρ (nonneg_iff_posSemidef.mpr hρ)]

/-- **Perturbation of a conjugation.** For contractions `U`, `V` and a positive semidefinite
`ρ`, `‖U ρ Uᴴ - V ρ Vᴴ‖₁ ≤ 2 ‖U - V‖ tr ρ`. -/
theorem traceNorm_mul_mul_conjTranspose_sub_le {U V ρ : Matrix n n ℂ} (hU : ‖U‖ ≤ 1)
    (hV : ‖V‖ ≤ 1) (hρ : ρ.PosSemidef) :
    (U * ρ * Uᴴ - V * ρ * Vᴴ).traceNorm ≤ 2 * ‖U - V‖ * ρ.trace.re := by
  obtain ⟨W, hW, hWM⟩ := exists_unitary_trace_mul_eq_traceNorm (U * ρ * Uᴴ - V * ρ * Vᴴ)
  have hsplit : U * ρ * Uᴴ - V * ρ * Vᴴ = (U - V) * ρ * Uᴴ + V * ρ * (U - V)ᴴ := by
    simp only [sub_mul, mul_sub, conjTranspose_sub]
    abel
  have e1 : (W * ((U - V) * ρ * Uᴴ)).trace = (Uᴴ * W * (U - V) * ρ).trace := by
    simp only [← Matrix.mul_assoc]; rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
  have e2 : (W * (V * ρ * (U - V)ᴴ)).trace = ((U - V)ᴴ * W * V * ρ).trace := by
    simp only [← Matrix.mul_assoc]; rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
  have n1 : ‖Uᴴ * W * (U - V)‖ ≤ ‖U - V‖ := by
    rw [Matrix.mul_assoc]
    calc _ ≤ ‖Uᴴ‖ * ‖W * (U - V)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖U - V‖ := by
        rw [CStarRing.norm_mem_unitary_mul _ hW, l2_opNorm_conjTranspose]; gcongr
      _ = _ := one_mul _
  have n2 : ‖(U - V)ᴴ * W * V‖ ≤ ‖U - V‖ := by
    rw [Matrix.mul_assoc]
    calc _ ≤ ‖(U - V)ᴴ‖ * ‖W * V‖ := norm_mul_le _ _
      _ ≤ ‖U - V‖ * 1 := by
        rw [CStarRing.norm_mem_unitary_mul _ hW, l2_opNorm_conjTranspose]; gcongr
      _ = _ := mul_one _
  have hρn := hρ.traceNorm_eq
  have t1 := norm_trace_mul_le_norm_mul_traceNorm (Uᴴ * W * (U - V)) ρ
  have t2 := norm_trace_mul_le_norm_mul_traceNorm ((U - V)ᴴ * W * V) ρ
  have htr : 0 ≤ ρ.trace.re := by
    rw [← hρn]; exact traceNorm_nonneg ρ
  calc (U * ρ * Uᴴ - V * ρ * Vᴴ).traceNorm
      = ‖(W * (U * ρ * Uᴴ - V * ρ * Vᴴ)).trace‖ := by
        rw [hWM, Complex.norm_real, Real.norm_of_nonneg (traceNorm_nonneg _)]
    _ = ‖(Uᴴ * W * (U - V) * ρ).trace + ((U - V)ᴴ * W * V * ρ).trace‖ := by
        rw [hsplit, Matrix.mul_add, trace_add, e1, e2]
    _ ≤ ‖(Uᴴ * W * (U - V) * ρ).trace‖ + ‖((U - V)ᴴ * W * V * ρ).trace‖ := norm_add_le _ _
    _ ≤ ‖U - V‖ * ρ.trace.re + ‖U - V‖ * ρ.trace.re := by
        rw [hρn] at t1 t2
        gcongr
        · exact t1.trans (by gcongr)
        · exact t2.trans (by gcongr)
    _ = 2 * ‖U - V‖ * ρ.trace.re := by ring

/-- The expectation of a matrix of operator norm at most `1` moves by at most the trace norm of
the change of state: `Re tr(E A) ≤ Re tr(E B) + ‖A - B‖₁`. -/
theorem re_trace_mul_le_add_traceNorm_sub {E : Matrix n n ℂ} (hE : ‖E‖ ≤ 1)
    (A B : Matrix n n ℂ) :
    (E * A).trace.re ≤ (E * B).trace.re + (A - B).traceNorm := by
  have h := norm_trace_mul_le_norm_mul_traceNorm E (A - B)
  have hre := Complex.re_le_norm (E * (A - B)).trace
  have hsub : (E * (A - B)).trace.re = (E * A).trace.re - (E * B).trace.re := by
    rw [Matrix.mul_sub, trace_sub, Complex.sub_re]
  nlinarith [traceNorm_nonneg (A - B)]

end Matrix

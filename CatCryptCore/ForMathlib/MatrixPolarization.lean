/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Polarization of rank-one complex matrices and entrywise norm bounds

Mathlib candidate. `Matrix.vecMulVec_star_eq_polarization` belongs in
`Mathlib/Data/Matrix/Mul.lean`, beside `Matrix.vecMulVec`; the two norm bounds
belong in `Mathlib/Analysis/Matrix/Normed.lean`, beside
`Matrix.norm_entry_le_entrywise_sup_norm`. Mathlib's polarization identity
`inner_map_polarization` is stated for inner products, not for `vecMulVec`.

## Main results

* `Matrix.vecMulVec_star_eq_polarization` — `u v*` is a combination of four
  matrices of the form `w w*`;
* `Matrix.norm_linearMap_apply_le_sum_single` — a linear map on square matrices
  satisfies `‖L X‖ ≤ ‖X‖ · ∑_{i,j} ‖L E_{ij}‖` in the entrywise sup norm;
* `Matrix.norm_trace_le_mul_norm` — `‖tr X‖ ≤ d · ‖X‖` in the entrywise sup norm.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix Matrix.Norms.Elementwise

namespace Matrix

variable {d : ℕ}

/-- Polarization: `u v*` is a combination of the four PSD matrices
    `(u + c v)(u + c v)*`, `c ∈ {1, i, -1, -i}`. -/
theorem vecMulVec_star_eq_polarization (u v : Fin d → ℂ) :
    vecMulVec u (star v) = (1 / 4 : ℂ) •
      (vecMulVec (u + v) (star (u + v))
        + Complex.I • vecMulVec (u + Complex.I • v) (star (u + Complex.I • v))
        - vecMulVec (u + (-1 : ℂ) • v) (star (u + (-1 : ℂ) • v))
        - Complex.I • vecMulVec (u + (-Complex.I) • v) (star (u + (-Complex.I) • v))) := by
  ext a b
  simp only [vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, star_add, star_mul', Complex.star_def,
    Complex.conj_I, map_neg, map_one]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A linear map on matrices is bounded entrywise by its values on the matrix
    units: `‖L X‖ ≤ ‖X‖ · ∑_{i,j} ‖L E_{ij}‖`. -/
theorem norm_linearMap_apply_le_sum_single
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖L X‖ ≤ ‖X‖ * ∑ i, ∑ j, ‖L (single i j 1)‖ := by
  have hX : X = ∑ i, ∑ j, X i j • single i j (1 : ℂ) := by
    conv_lhs => rw [matrix_eq_sum_single X]
    simp [smul_single]
  rw [hX, map_sum]
  calc ‖∑ i, L (∑ j, X i j • single i j (1 : ℂ))‖
        ≤ ∑ i, ‖L (∑ j, X i j • single i j (1 : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖X‖ * ∑ j, ‖L (single i j 1)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [map_sum, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [map_smul, norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_entry_le_entrywise_sup_norm X) (norm_nonneg _)
    _ = ‖X‖ * ∑ i, ∑ j, ‖L (single i j 1)‖ := by rw [Finset.mul_sum]
    _ = _ := by rw [← hX]

/-- The trace is bounded by the dimension times the entrywise sup norm. -/
theorem norm_trace_le_mul_norm (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖X.trace‖ ≤ d * ‖X‖ := by
  unfold Matrix.trace Matrix.diag
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖X i i‖ ≤ ∑ _i : Fin d, ‖X‖ :=
        Finset.sum_le_sum fun i _ => norm_entry_le_entrywise_sup_norm X
    _ = d * ‖X‖ := by simp

end Matrix

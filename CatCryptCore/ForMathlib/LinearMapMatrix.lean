/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Complex.Basic

/-!
# Linear maps on square matrices are determined by the matrix units

Mathlib candidate. `Matrix.linearMap_apply_eq_sum_single` belongs in
`Mathlib/Data/Matrix/Basis.lean`, beside `Matrix.matrix_eq_sum_single`.

## Main results

* `Matrix.linearMap_apply_eq_sum_single` — each entry of `f Y`, for a linear
  map `f` on complex square matrices, is `∑ k l, Y k l * f (single k l 1) i j`.
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

/-- Every linear map on square matrices is determined entrywise by its values on the
    matrix units. -/
theorem linearMap_apply_eq_sum_single {n m : ℕ}
    (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin m) :
    f Y i j = ∑ k, ∑ l, Y k l * f (Matrix.single k l 1) i j := by
  have h : ∀ k l, Matrix.single k l (Y k l) = Y k l • Matrix.single k l (1 : ℂ) := by
    intro k l; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum, Matrix.sum_apply, h, map_smul, Matrix.smul_apply, smul_eq_mul]

end Matrix

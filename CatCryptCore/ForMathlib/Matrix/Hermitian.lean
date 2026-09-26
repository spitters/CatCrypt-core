/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Basic

/-!
# Hermitian matrices: the trace is real

Mathlib candidate for `Mathlib/LinearAlgebra/Matrix/Hermitian.lean`.
Mathlib has `Matrix.IsHermitian.trace_eq_sum_eigenvalues` (in
`Mathlib.Analysis.Matrix.Spectrum`), which implies this through the spectral
theorem; the statement here needs only the diagonal entries and no spectral
machinery.
-/

namespace Matrix.IsHermitian

open Complex

variable {n : Type*} [Fintype n] {M : Matrix n n ℂ}

/-- The trace of a Hermitian complex matrix has imaginary part zero. -/
theorem trace_im (hM : M.IsHermitian) : M.trace.im = 0 := by
  unfold Matrix.trace Matrix.diag
  rw [show (∑ i, M i i).im = ∑ i, (M i i).im from map_sum Complex.imAddGroupHom _ _]
  exact Finset.sum_eq_zero fun i _ =>
    Complex.conj_eq_iff_im.mp (congr_fun (congr_fun hM i) i)

/-- The trace of a Hermitian complex matrix is its real part, coerced. -/
theorem trace_eq_re (hM : M.IsHermitian) : M.trace = (M.trace.re : ℂ) := by
  apply Complex.ext <;> simp [hM.trace_im]

end Matrix.IsHermitian

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.ForMathlib.Tactic.Spectral

/-!
# Tests for the `spectral` tactic

Goal shapes of the quantum matrix code in which the spectral theorem is used by hand.
-/

set_option autoImplicit false

open Matrix

section Tests

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Trace of a product with a Hermitian matrix as a sum over eigenvalues
(`TraceNorm.lean`, `HelstromPriors.lean`). -/
example (X E : Matrix n n ℂ) (hX : X.IsHermitian) :
    (E * X).trace = ∑ i, (star (hX.eigenvectorUnitary : Matrix n n ℂ) * E *
      (hX.eigenvectorUnitary : Matrix n n ℂ)) i i * (↑(hX.eigenvalues i) : ℂ) := by
  spectral hX with U d hU hU' hXd
  rw [hXd]
  calc _ = (star U * E * U * diagonal (fun i => (d i : ℂ))).trace := by
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm U]
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm _ (star U * (E * U))]
        simp only [Matrix.mul_assoc]
        rfl
    _ = _ := by simp [Matrix.trace, Matrix.mul_diagonal]

/-- The eigendata packaged as an existential (`PowersStormer.lean`, `Schmidt.lean`). -/
example (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    ∃ U : Matrix n n ℂ, star U * U = 1 ∧ U * star U = 1 ∧
      ∃ d : n → ℝ, X = U * diagonal (fun i => (d i : ℂ)) * star U := by
  spectral hX with U d hU hU' hXd
  exact ⟨U, hU, hU', d, hXd⟩

/-- The trace of a Hermitian matrix is the sum of its eigenvalues (`O2HTheorem.lean`). -/
example (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    X.trace = ∑ i, (↑(hX.eigenvalues i) : ℂ) := by
  spectral hX with U d hU hU' hXd
  rw [hXd, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp [Matrix.trace]

/-- Rewriting with `hXd` after `spectral` meets no dependent motive. -/
example (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    (X * X).trace = ∑ i, (↑(hX.eigenvalues i) : ℂ) ^ 2 := by
  spectral hX with U d hU hU' hXd
  have key : ∀ A : Matrix n n ℂ, star U * (U * A) = A := by
    intro A
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [hXd]
  simp only [Matrix.mul_assoc, key]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  simp [Matrix.trace, Matrix.diagonal_mul_diagonal, sq]

end Tests

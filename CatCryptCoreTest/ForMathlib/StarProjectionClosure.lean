/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.ForMathlib.Matrix.StarProjectionClosure

/-!
# Tests for the star-projection closure rules

Goal shapes of the quantum matrix code, closed by `aesop (rule_sets := [CStarAlgebra])` and by
`cfc_tac`.
-/

open Matrix Kronecker

section Tests

variable {A B M : Type} [Fintype A] [Fintype B] [Fintype M] [DecidableEq A] [DecidableEq B]
  [DecidableEq M]

/-- The Kronecker product of star projections (`isStarProjection_kronecker`). -/
example {p : Matrix A A ℂ} {q : Matrix B B ℂ} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : IsStarProjection (p ⊗ₖ q) := by
  aesop (rule_sets := [CStarAlgebra])

/-- The operator `1 ⊗ Q` of a projector (`bobOp_isStarProjection`). -/
example (Q : Matrix (M × B) (M × B) ℂ) (h : IsStarProjection Q) :
    IsStarProjection ((1 : Matrix A A ℂ) ⊗ₖ Q) := by
  aesop (rule_sets := [CStarAlgebra])

/-- The same operator, closed by `cfc_tac`. -/
example (Q : Matrix (M × B) (M × B) ℂ) (h : IsStarProjection Q) :
    IsStarProjection ((1 : Matrix A A ℂ) ⊗ₖ Q) := by
  cfc_tac

/-- Self-adjointness of a Kronecker product, closed by `cfc_tac`. -/
example {a : Matrix A A ℂ} {b : Matrix B B ℂ} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (a ⊗ₖ b) := by
  cfc_tac

/-- Hermitian Kronecker product. -/
example {a : Matrix A A ℂ} {b : Matrix B B ℂ} (ha : a.IsHermitian) (hb : b.IsHermitian) :
    (a ⊗ₖ b).IsHermitian := by
  aesop (rule_sets := [CStarAlgebra])

/-- Unitary Kronecker product. -/
example {a : Matrix A A ℂ} {b : Matrix B B ℂ} (ha : a ∈ unitary (Matrix A A ℂ))
    (hb : b ∈ unitary (Matrix B B ℂ)) : a ⊗ₖ b ∈ unitary (Matrix (A × B) (A × B) ℂ) := by
  aesop (rule_sets := [CStarAlgebra])

/-- Unitary conjugate of a projection (`isStarProjection_conjProj`). -/
example (U : Matrix.unitaryGroup A ℂ) {P : Matrix A A ℂ} (hP : IsStarProjection P) :
    IsStarProjection ((U : Matrix A A ℂ) * P * star (U : Matrix A A ℂ)) := by
  aesop (rule_sets := [CStarAlgebra])

/-- Unitary conjugate of a projection with a unitary hypothesis, closed by `cfc_tac`. -/
example {U P : Matrix A A ℂ} (hU : U ∈ unitary (Matrix A A ℂ)) (hP : IsStarProjection P) :
    IsStarProjection (U * P * star U) := by
  cfc_tac

/-- The complement of a projection. -/
example {P : Matrix A A ℂ} (hP : IsStarProjection P) : IsStarProjection (1 - P) := by
  aesop (rule_sets := [CStarAlgebra])

/-- A Kronecker product of a complement. -/
example {P : Matrix A A ℂ} {Q : Matrix B B ℂ} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : IsStarProjection ((1 - P) ⊗ₖ Q) := by
  aesop (rule_sets := [CStarAlgebra])

/-- Reindexing by an equivalence. -/
example {P : Matrix A A ℂ} (hP : IsStarProjection P) (e : B ≃ A) :
    IsStarProjection (P.submatrix e e) := by
  aesop (rule_sets := [CStarAlgebra])

/-- `Matrix.reindex` of a Hermitian matrix. -/
example {P : Matrix A A ℂ} (hP : P.IsHermitian) (e : A ≃ B) :
    (Matrix.reindex e e P).IsHermitian := by
  aesop (rule_sets := [CStarAlgebra])

/-- Reindexing a unitary. -/
example {U : Matrix A A ℂ} (hU : U ∈ unitary (Matrix A A ℂ)) (e : B ≃ A) :
    U.submatrix e e ∈ unitary (Matrix B B ℂ) := by
  aesop (rule_sets := [CStarAlgebra])

/-- A block diagonal of projections. -/
example {P : M → Matrix A A ℂ} (hP : ∀ i, IsStarProjection (P i)) :
    IsStarProjection (Matrix.blockDiagonal P) := by
  aesop (rule_sets := [CStarAlgebra])

/-- A block diagonal of unitaries. -/
example {U : M → Matrix A A ℂ} (hU : ∀ i, U i ∈ unitary (Matrix A A ℂ)) :
    Matrix.blockDiagonal U ∈ unitary (Matrix (A × M) (A × M) ℂ) := by
  aesop (rule_sets := [CStarAlgebra])

end Tests

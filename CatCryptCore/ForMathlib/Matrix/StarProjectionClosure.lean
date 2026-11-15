/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# Closure rules for star projections, self-adjoint and unitary matrices

The predicates `IsStarProjection`, `IsSelfAdjoint` (`Matrix.IsHermitian`) and membership in
`unitary` define subsets of a star ring that are closed under the constructors that occur in
quantum-information matrix code: the Kronecker product `⊗ₖ`, conjugation `U * P * star U` by a
unitary, reindexing by an equivalence (`Matrix.submatrix e e`, `Matrix.reindex e e`), block
diagonals, and `1 - P`. Each lemma is registered in Mathlib's `aesop` rule set `CStarAlgebra`,
which `cfc_tac` and `aesop (rule_sets := [CStarAlgebra])` run.

## Main results

* `Matrix.IsHermitian.kronecker`, `Matrix.isSelfAdjoint_kronecker`,
  `IsStarProjection.kronecker`: closure under `⊗ₖ`; Mathlib's `Matrix.kronecker_mem_unitary`
  is registered for membership in `unitary`.
* `IsStarProjection.conj_unitary`, `IsSelfAdjoint.conj_unitary`, `mem_unitary_conj_unitary`:
  closure under conjugation by a unitary.
* `Matrix.IsHermitian.submatrix_equiv`, `Matrix.isSelfAdjoint_submatrix_equiv`,
  `IsStarProjection.submatrix_equiv`, `Matrix.mem_unitary_submatrix_equiv` and the `reindex`
  forms: closure under reindexing by an equivalence.
* `Matrix.isHermitian_blockDiagonal_of_forall`, `Matrix.isSelfAdjoint_blockDiagonal`,
  `IsStarProjection.blockDiagonal`, `Matrix.blockDiagonal_mem_unitary`: closure under block
  diagonals.
* Registration of Mathlib's `IsStarProjection.zero`, `.one`, `.one_sub`.
-/

@[expose] public section

open Matrix Kronecker

section Kronecker

variable {R : Type*} [CommRing R] [StarRing R] {m n : Type*}

/-- The Kronecker product of Hermitian matrices is Hermitian. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.IsHermitian.kronecker {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  unfold Matrix.IsHermitian at *
  rw [conjTranspose_kronecker, hA, hB]

/-- The Kronecker product of self-adjoint matrices is self-adjoint. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.isSelfAdjoint_kronecker {A : Matrix m m R}
    {B : Matrix n n R} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A ⊗ₖ B) := by
  rw [← Matrix.isHermitian_iff_isSelfAdjoint] at *
  exact hA.kronecker hB

/-- The Kronecker product of star projections is a star projection. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsStarProjection.kronecker [Fintype m] [Fintype n] {A : Matrix m m R}
    {B : Matrix n n R} (hA : IsStarProjection A) (hB : IsStarProjection B) :
    IsStarProjection (A ⊗ₖ B) := by
  refine ⟨?_, Matrix.isSelfAdjoint_kronecker hA.isSelfAdjoint hB.isSelfAdjoint⟩
  change A ⊗ₖ B * A ⊗ₖ B = A ⊗ₖ B
  rw [← mul_kronecker_mul, hA.isIdempotentElem.eq, hB.isIdempotentElem.eq]

attribute [aesop safe apply (rule_sets := [CStarAlgebra])] Matrix.kronecker_mem_unitary

end Kronecker

section Conjugation

variable {R : Type*} [Ring R] [StarRing R]

/-- Conjugation of a star projection by a unitary is a star projection. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsStarProjection.conj_unitary {U P : R} (hU : U ∈ unitary R) (hP : IsStarProjection P) :
    IsStarProjection (U * P * star U) := by
  refine ⟨?_, hP.isSelfAdjoint.conjugate U⟩
  change U * P * star U * (U * P * star U) = U * P * star U
  have h : star U * U = 1 := (Unitary.mem_iff.mp hU).1
  calc U * P * star U * (U * P * star U) = U * P * (star U * U) * P * star U := by
        simp only [mul_assoc]
    _ = U * (P * P) * star U := by rw [h, mul_one]; simp only [mul_assoc]
    _ = U * P * star U := by rw [hP.isIdempotentElem.eq]

/-- Conjugation of a self-adjoint element by a unitary is self-adjoint. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsSelfAdjoint.conj_unitary {U P : R} (_hU : U ∈ unitary R) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (U * P * star U) :=
  hP.conjugate U

/-- Conjugation of a unitary by a unitary is unitary. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem mem_unitary_conj_unitary {U V : R} (hU : U ∈ unitary R) (hV : V ∈ unitary R) :
    U * V * star U ∈ unitary R :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ hU hV) (Unitary.star_mem hU)

end Conjugation

section Reindex

variable {R : Type*} [Ring R] [StarRing R] {m n : Type*}

/-- Reindexing a Hermitian matrix along an equivalence keeps it Hermitian. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.IsHermitian.submatrix_equiv {A : Matrix m m R} (hA : A.IsHermitian) (e : n ≃ m) :
    (A.submatrix e e).IsHermitian :=
  hA.submatrix e

/-- Reindexing a self-adjoint matrix along an equivalence keeps it self-adjoint. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.isSelfAdjoint_submatrix_equiv {A : Matrix m m R}
    (hA : IsSelfAdjoint A) (e : n ≃ m) : IsSelfAdjoint (A.submatrix e e) := by
  rw [← Matrix.isHermitian_iff_isSelfAdjoint] at *
  exact hA.submatrix e

/-- Reindexing a star projection along an equivalence gives a star projection. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsStarProjection.submatrix_equiv [Fintype m] [Fintype n] {A : Matrix m m R}
    (hA : IsStarProjection A) (e : n ≃ m) : IsStarProjection (A.submatrix e e) := by
  refine ⟨?_, Matrix.isSelfAdjoint_submatrix_equiv hA.isSelfAdjoint e⟩
  change A.submatrix e e * A.submatrix e e = A.submatrix e e
  rw [submatrix_mul_equiv, show A * A = A from hA.isIdempotentElem.eq]

/-- Reindexing a unitary matrix along an equivalence gives a unitary matrix. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.mem_unitary_submatrix_equiv [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A : Matrix m m R} (hA : A ∈ unitary (Matrix m m R)) (e : n ≃ m) :
    A.submatrix e e ∈ unitary (Matrix n n R) :=
  Matrix.submatrix_equiv_mem_unitary.mpr hA

/-- `Matrix.reindex` along an equivalence keeps a matrix Hermitian. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.IsHermitian.reindex_equiv {A : Matrix m m R} (hA : A.IsHermitian) (e : m ≃ n) :
    (Matrix.reindex e e A).IsHermitian :=
  hA.submatrix e.symm

/-- `Matrix.reindex` along an equivalence keeps a star projection a star projection. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsStarProjection.reindex_equiv [Fintype m] [Fintype n] {A : Matrix m m R}
    (hA : IsStarProjection A) (e : m ≃ n) : IsStarProjection (Matrix.reindex e e A) :=
  hA.submatrix_equiv e.symm

/-- `Matrix.reindex` along an equivalence keeps a unitary matrix unitary. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.mem_unitary_reindex_equiv [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A : Matrix m m R} (hA : A ∈ unitary (Matrix m m R)) (e : m ≃ n) :
    Matrix.reindex e e A ∈ unitary (Matrix n n R) :=
  Matrix.mem_unitary_submatrix_equiv hA e.symm

end Reindex

section BlockDiagonal

variable {R : Type*} [Ring R] [StarRing R] {o m : Type*} [Fintype m] [Fintype o]
  [DecidableEq o]

omit [Fintype m] [Fintype o] in
/-- A block diagonal matrix of Hermitian blocks is Hermitian. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.isHermitian_blockDiagonal_of_forall {A : o → Matrix m m R}
    (hA : ∀ i, (A i).IsHermitian) : (Matrix.blockDiagonal A).IsHermitian :=
  Matrix.isHermitian_blockDiagonal_iff.mpr hA

omit [Fintype m] [Fintype o] in
/-- A block diagonal matrix of self-adjoint blocks is self-adjoint. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.isSelfAdjoint_blockDiagonal {A : o → Matrix m m R}
    (hA : ∀ i, IsSelfAdjoint (A i)) : IsSelfAdjoint (Matrix.blockDiagonal A) := by
  rw [← Matrix.isHermitian_iff_isSelfAdjoint] at *
  exact Matrix.isHermitian_blockDiagonal_of_forall hA

/-- A block diagonal matrix of star projections is a star projection. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsStarProjection.blockDiagonal {A : o → Matrix m m R}
    (hA : ∀ i, IsStarProjection (A i)) : IsStarProjection (Matrix.blockDiagonal A) := by
  refine ⟨?_, Matrix.isSelfAdjoint_blockDiagonal fun i => (hA i).isSelfAdjoint⟩
  change Matrix.blockDiagonal A * Matrix.blockDiagonal A = Matrix.blockDiagonal A
  rw [← blockDiagonal_mul]
  exact congrArg _ (funext fun i => (hA i).isIdempotentElem.eq)

variable [DecidableEq m]

/-- A block diagonal matrix of unitary blocks is unitary. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem Matrix.blockDiagonal_mem_unitary {A : o → Matrix m m R}
    (hA : ∀ i, A i ∈ unitary (Matrix m m R)) :
    Matrix.blockDiagonal A ∈ unitary (Matrix (m × o) (m × o) R) := by
  rw [Unitary.mem_iff]
  simp only [star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  refine ⟨?_, ?_⟩
  · rw [← blockDiagonal_one]
    exact congrArg _ (funext fun i => (Unitary.mem_iff.mp (hA i)).1)
  · rw [← blockDiagonal_one]
    exact congrArg _ (funext fun i => (Unitary.mem_iff.mp (hA i)).2)

end BlockDiagonal

section Registered

attribute [aesop safe apply (rule_sets := [CStarAlgebra])]
  IsStarProjection.zero IsStarProjection.one IsStarProjection.one_sub

end Registered

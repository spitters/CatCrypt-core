/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# Kronecker products reindexed to `Fin (d₁ * d₂)`

Mathlib's `A ⊗ₖ B` is indexed by `Fin d₁ × Fin d₂`. Transporting it along
`finProdFinEquiv : Fin d₁ × Fin d₂ ≃ Fin (d₁ * d₂)` with `Matrix.reindex` gives the
row-major Kronecker product on `Fin (d₁ * d₂)`. This file states the entry formula and
the multiplicative, adjoint, unit and trace rules of that reindexed product, each by one
rewrite with the corresponding Mathlib lemma about `⊗ₖ` and `Matrix.reindex`.

## Main results

* `Matrix.reindex_kronecker_apply`, `Matrix.reindex_kronecker_apply_symm`: entries
* `Matrix.reindex_kronecker_mul_reindex_kronecker`: mixed-product rule
* `Matrix.conjTranspose_reindex_kronecker`: conjugate transpose
* `Matrix.reindex_one_kronecker_one`: the identity
* `Matrix.trace_reindex_kronecker`: trace
-/

@[expose] public section

set_option autoImplicit false

open Matrix Kronecker

namespace Matrix

variable {d₁ d₂ : ℕ} {R : Type*}

/-- Entry of the reindexed Kronecker product at the image of a pair of index pairs. -/
theorem reindex_kronecker_apply [Mul R] (A : Matrix (Fin d₁) (Fin d₁) R)
    (B : Matrix (Fin d₂) (Fin d₂) R) (i₁ j₁ : Fin d₁) (i₂ j₂ : Fin d₂) :
    reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) (finProdFinEquiv (i₁, i₂))
      (finProdFinEquiv (j₁, j₂)) = A i₁ j₁ * B i₂ j₂ := by
  simp [reindex_apply]

/-- Entry of the reindexed Kronecker product, decomposing indices by `finProdFinEquiv.symm`. -/
theorem reindex_kronecker_apply_symm [Mul R] (A : Matrix (Fin d₁) (Fin d₁) R)
    (B : Matrix (Fin d₂) (Fin d₂) R) (i j : Fin (d₁ * d₂)) :
    reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) i j =
      A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        B (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  simp [reindex_apply]

/-- Mixed-product rule for the reindexed Kronecker product. -/
theorem reindex_kronecker_mul_reindex_kronecker [CommSemiring R]
    (A C : Matrix (Fin d₁) (Fin d₁) R) (B D : Matrix (Fin d₂) (Fin d₂) R) :
    reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) *
        reindex finProdFinEquiv finProdFinEquiv (C ⊗ₖ D) =
      reindex finProdFinEquiv finProdFinEquiv ((A * C) ⊗ₖ (B * D)) := by
  rw [mul_kronecker_mul]
  simp only [reindex_apply]
  exact submatrix_mul_equiv _ _ _ _ _

/-- The conjugate transpose of a reindexed Kronecker product is the reindexed Kronecker product
of the conjugate transposes. -/
theorem conjTranspose_reindex_kronecker [CommSemiring R] [StarRing R]
    (A : Matrix (Fin d₁) (Fin d₁) R) (B : Matrix (Fin d₂) (Fin d₂) R) :
    (reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B))ᴴ =
      reindex finProdFinEquiv finProdFinEquiv (Aᴴ ⊗ₖ Bᴴ) := by
  rw [conjTranspose_reindex, conjTranspose_kronecker]

/-- The reindexed Kronecker product of identities is the identity. -/
theorem reindex_one_kronecker_one [MulZeroOneClass R] :
    reindex finProdFinEquiv finProdFinEquiv
      ((1 : Matrix (Fin d₁) (Fin d₁) R) ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) R)) = 1 := by
  rw [one_kronecker_one]
  simp [reindex_apply]

/-- The trace of a reindexed Kronecker product is the product of the traces. -/
theorem trace_reindex_kronecker [CommSemiring R]
    (A : Matrix (Fin d₁) (Fin d₁) R) (B : Matrix (Fin d₂) (Fin d₂) R) :
    (reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)).trace = A.trace * B.trace := by
  rw [← trace_kronecker]
  unfold Matrix.trace
  rw [← finProdFinEquiv.sum_comp]
  simp [diag, reindex_apply]

end Matrix

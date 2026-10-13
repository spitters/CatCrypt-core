/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.TensorProduct
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

set_option autoImplicit false

/-!
# Kronecker products of PSD matrices

`kronecker_posSemidef`: the index-flattened Kronecker product
`TensorProduct.kronecker` of two PSD matrices is PSD.
-/

open scoped Matrix ComplexOrder
open Matrix Classical

noncomputable section

namespace CatCrypt.Quantum.QHL

/-- The index-flattened Kronecker product is Mathlib's `kroneckerMap (· * ·)`
transported along `finProdEquiv`. -/
private theorem kronecker_eq_submatrix {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    TensorProduct.kronecker A B =
      (Matrix.kroneckerMap (· * ·) A B).submatrix
        (TensorProduct.finProdEquiv d₁ d₂).symm
        (TensorProduct.finProdEquiv d₁ d₂).symm := by
  ext i j
  simp [TensorProduct.kronecker_apply, Matrix.kroneckerMap_apply, Matrix.submatrix_apply]

/-- Kronecker products of PSD matrices are PSD. -/
theorem kronecker_posSemidef {d₁ d₂ : ℕ} {A : Matrix (Fin d₁) (Fin d₁) ℂ}
    {B : Matrix (Fin d₂) (Fin d₂) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (TensorProduct.kronecker A B).PosSemidef := by
  rw [kronecker_eq_submatrix]
  exact (Matrix.PosSemidef.kronecker hA hB).submatrix _

end CatCrypt.Quantum.QHL

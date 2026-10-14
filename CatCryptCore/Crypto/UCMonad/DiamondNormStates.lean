/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.TensorProduct
public import CatCryptCore.Quantum.Instrument
public import Mathlib.Analysis.Matrix.Order

/-!
# Kronecker Product of Density Matrices

The flat Kronecker product `kronecker ρ.val σ.val` of two density matrices is
again a density matrix on the product dimension `d₁ * d₂`.

## Main results

* `kronecker_posSemidef` — the flat Kronecker product of two PSD matrices is PSD,
  obtained from mathlib's `Matrix.PosSemidef.kronecker` (over the product index)
  transported along the reindexing `finProdEquiv`.
* `kroneckerDensity` — packages `kronecker` of two `DensityMatrix` values into a
  `DensityMatrix (d₁ * d₂)`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open scoped Matrix ComplexOrder

namespace CatCrypt.Crypto.UCMonad.DiamondNormStates

variable {d₁ d₂ : ℕ}

/-- The flat Kronecker product `kronecker A B` is the reindexing of mathlib's
    `Matrix.kroneckerMap (·*·) A B` (indexed by `Fin d₁ × Fin d₂`) along the
    equivalence `finProdEquiv`. -/
theorem kronecker_eq_submatrix
    (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker A B =
      (Matrix.kroneckerMap (· * ·) A B).submatrix
        (finProdEquiv d₁ d₂).symm (finProdEquiv d₁ d₂).symm := by
  ext i j
  simp [kronecker_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

/-- The flat Kronecker product of two PSD matrices is PSD. -/
theorem kronecker_posSemidef
    {A : Matrix (Fin d₁) (Fin d₁) ℂ} {B : Matrix (Fin d₂) (Fin d₂) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (kronecker A B).PosSemidef := by
  rw [kronecker_eq_submatrix]
  exact (hA.kronecker hB).submatrix (finProdEquiv d₁ d₂).symm

/-- Kronecker product of two density matrices is a density matrix. -/
noncomputable def kroneckerDensity
    (ρ : DensityMatrix d₁) (σ : DensityMatrix d₂) : DensityMatrix (d₁ * d₂) where
  val := kronecker ρ.val σ.val
  psd := kronecker_posSemidef ρ.psd σ.psd
  tr_one := by rw [trace_kronecker, ρ.tr_one, σ.tr_one]; ring

@[simp]
theorem kroneckerDensity_val (ρ : DensityMatrix d₁) (σ : DensityMatrix d₂) :
    (kroneckerDensity ρ σ).val = kronecker ρ.val σ.val := rfl

end CatCrypt.Crypto.UCMonad.DiamondNormStates

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.TensorProduct
public import CatCryptCore.Quantum.Instrument
public import CatCryptCore.Quantum.KroneckerPSD
public import Mathlib.Analysis.Matrix.Order

/-!
# Kronecker Product of Density Matrices

The flat Kronecker product `kronecker ρ.val σ.val` of two density matrices is
again a density matrix on the product dimension `d₁ * d₂`.

## Main results

* `kroneckerDensity` — packages `kronecker` of two `DensityMatrix` values into a
  `DensityMatrix (d₁ * d₂)`; positivity is `QHL.kronecker_posSemidef`
  (`CatCryptCore/Quantum/KroneckerPSD.lean`).
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open scoped Matrix ComplexOrder

namespace CatCrypt.Crypto.UCMonad.DiamondNormStates

variable {d₁ d₂ : ℕ}

/-- Kronecker product of two density matrices is a density matrix. -/
noncomputable def kroneckerDensity
    (ρ : DensityMatrix d₁) (σ : DensityMatrix d₂) : DensityMatrix (d₁ * d₂) where
  val := kronecker ρ.val σ.val
  psd := QHL.kronecker_posSemidef ρ.psd σ.psd
  tr_one := by rw [trace_kronecker, ρ.tr_one, σ.tr_one]; ring

@[simp]
theorem kroneckerDensity_val (ρ : DensityMatrix d₁) (σ : DensityMatrix d₂) :
    (kroneckerDensity ρ σ).val = kronecker ρ.val σ.val := rfl

end CatCrypt.Crypto.UCMonad.DiamondNormStates

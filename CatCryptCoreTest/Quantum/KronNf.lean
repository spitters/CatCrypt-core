/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Quantum.KronNf

/-!
# Tests for `kron_nf`, `kron_index` and `kron_ext`

The goal shapes of the Kronecker normal form: products, adjoints, `star`, scalars, sums, finite
sums, traces, partial traces and the action on product vectors of the product
`TensorProduct.kronecker` on `Fin (d₁ * d₂)` (written `⊗ₖ`, with `Kronecker` not open) and of
Mathlib's `kroneckerMap (· * ·)` on product types; goals stated at `Fin 4` and `Fin (2 ^ 2)`;
entry goals and entry hypotheses at `finProdEquiv` points.
-/

set_option autoImplicit false

open Matrix CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct (kronVec finProdEquiv)
open CatCrypt.Quantum.PartialTrace (partialTrace₁ partialTrace₂)

section Fin

variable {d₁ d₂ : ℕ} (A C E : Matrix (Fin d₁) (Fin d₁) ℂ) (B D F : Matrix (Fin d₂) (Fin d₂) ℂ)

/-- The mixed-product rule, applied twice. -/
example : (A ⊗ₖ B) * (C ⊗ₖ D) * (E ⊗ₖ F) = (A * C * E) ⊗ₖ (B * D * F) := by
  kron_nf

/-- Adjoint of a Kronecker product. -/
example : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = (Aᴴ * A) ⊗ₖ (Bᴴ * B) := by
  kron_nf

/-- `star` of a Kronecker product. -/
example : star (A ⊗ₖ B) * (A ⊗ₖ B) = (Aᴴ * A) ⊗ₖ (Bᴴ * B) := by
  kron_nf

/-- Scalars move out of either factor. -/
example (c : ℂ) : (c • A) ⊗ₖ B = A ⊗ₖ (c • B) := by
  kron_nf

/-- Additivity in the first factor under a product. -/
example : ((A + C) ⊗ₖ B) * (E ⊗ₖ F) = (A * E) ⊗ₖ (B * F) + (C * E) ⊗ₖ (B * F) := by
  kron_nf

/-- Finite sums in the first factor. -/
example {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin d₁) (Fin d₁) ℂ) :
    (∑ i ∈ s, f i) ⊗ₖ B = ∑ i ∈ s, f i ⊗ₖ B := by
  kron_nf

/-- Trace of a product of Kronecker products. -/
example : ((A ⊗ₖ B) * (C ⊗ₖ D)).trace = (A * C).trace * (B * D).trace := by
  kron_nf

/-- Partial trace over the second register. -/
example : partialTrace₂ ((A ⊗ₖ B) * (C ⊗ₖ D)) = (B * D).trace • (A * C) := by
  kron_nf

/-- Partial trace over the first register. -/
example : partialTrace₁ (A ⊗ₖ B) = A.trace • B := by
  kron_nf

/-- Action on a Kronecker product of vectors. -/
example (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) :
    ((A ⊗ₖ B) * (C ⊗ₖ D)) *ᵥ kronVec u v = kronVec ((A * C) *ᵥ u) ((B * D) *ᵥ v) := by
  kron_nf

/-- The identity as a Kronecker product. -/
example : ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) * (A ⊗ₖ B) =
    A ⊗ₖ B := by
  kron_nf

/-- Entry goals: additivity in the second factor. -/
example : A ⊗ₖ (B + D) = A ⊗ₖ B + A ⊗ₖ D := by
  kron_ext i₁ i₂ j₁ j₂
  ring

/-- `kron_ext` with unnamed indices. -/
example : A ⊗ₖ B = A ⊗ₖ B := by
  kron_ext

end Fin

section Literal

variable (X Y : Matrix (Fin 2) (Fin 2) ℂ)

/-- A product with an identity stated at `Fin 4`. -/
example : ((X ⊗ₖ Y) * (1 : Matrix (Fin 4) (Fin 4) ℂ))ᴴ = Xᴴ ⊗ₖ Yᴴ := by
  kron_nf

/-- A product of involutions stated at `Fin (2 ^ 2)`. -/
example (hX : X * X = 1) (hY : Y * Y = 1) :
    ((X ⊗ₖ Y) * (X ⊗ₖ Y) : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ) = 1 := by
  kron_nf
  rw [hX, hY, TensorProduct.kronecker_one_one]

/-- `kron_ext` at a goal whose left side is indexed by `Fin 4`. -/
example (Z : Matrix (Fin 4) (Fin 4) ℂ)
    (h : ∀ i₁ i₂ j₁ j₂, Z (finProdEquiv 2 2 (i₁, i₂)) (finProdEquiv 2 2 (j₁, j₂)) =
      X i₁ j₁ * Y i₂ j₂) :
    Z = X ⊗ₖ Y := by
  kron_ext a b c e
  exact h a b c e

/-- `kron_ext at h` for an equation with the identity. -/
example (h : X ⊗ₖ Y = 1) : X 0 0 * Y 0 0 = 1 := by
  kron_ext at h
  simpa using h 0 0 0 0

/-- `kron_ext at h` for an equation whose left side is indexed by `Fin 4`. -/
example (Z : Matrix (Fin 4) (Fin 4) ℂ) (h : Z = X ⊗ₖ Y) :
    Z (finProdEquiv 2 2 (0, 1)) (finProdEquiv 2 2 (1, 0)) = X 0 1 * Y 1 0 := by
  kron_ext at h
  exact h 0 1 1 0

end Literal

section Prod

variable {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]

/-- Mathlib's type-indexed Kronecker product. -/
example (P Q : Matrix l l ℂ) (R S : Matrix m m ℂ) :
    kroneckerMap (· * ·) P R * kroneckerMap (· * ·) Q S * (1 : Matrix (l × m) (l × m) ℂ) =
      kroneckerMap (· * ·) (P * Q) (R * S) := by
  kron_nf

/-- The reindexed type-indexed Kronecker product. -/
example {k n : ℕ} (P Q : Matrix (Fin k) (Fin k) ℂ) (R S : Matrix (Fin n) (Fin n) ℂ) :
    reindex finProdFinEquiv finProdFinEquiv (kroneckerMap (· * ·) P R) *
        reindex finProdFinEquiv finProdFinEquiv (kroneckerMap (· * ·) Q S) =
      reindex finProdFinEquiv finProdFinEquiv (kroneckerMap (· * ·) (P * Q) (R * S)) := by
  kron_nf

end Prod

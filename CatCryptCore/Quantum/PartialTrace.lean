/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Partial Trace

Defines the partial trace operation on bipartite quantum systems, tracing
out one subsystem.

## Main Definitions

* `partialTrace₂` — trace out the second register: `(tr₂ ρ)_{i₁,j₁} = ∑_k ρ_{(i₁,k),(j₁,k)}`
* `partialTrace₁` — trace out the first register: `(tr₁ ρ)_{i₂,j₂} = ∑_k ρ_{(k,i₂),(k,j₂)}`

## Properties

* `trace_partialTrace₂` — `tr(tr₂ ρ) = tr(ρ)`
* `partialTrace₂_kronecker` — `tr₂(A ⊗ B) = tr(B) • A`
* Partial trace preserves PSD
* `partialTrace₂_kronecker_one_mul`, `partialTrace₂_one_kronecker_mul_comm`
  and their `partialTrace₁` duals — partial traces of products with local
  operators
* `sum_partialTrace₂_kronecker_conj`, `sum_partialTrace₁_kronecker_conj` — a
  complete Kraus family on the traced register leaves the partial trace
  unchanged

## References

* Watrous — The Theory of Quantum Information, §2.4
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix Classical

noncomputable section

namespace CatCrypt.Quantum.PartialTrace

open CatCrypt.Quantum.TensorProduct

variable {d₁ d₂ : ℕ}

/-- Partial trace over the second register.

    `(partialTrace₂ ρ)_{i₁,j₁} = ∑_{k : Fin d₂} ρ_{(i₁,k),(j₁,k)}`

    This is a linear map from `(d₁·d₂)×(d₁·d₂)` matrices to `d₁×d₁` matrices. -/
def partialTrace₂ :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ →ₗ[ℂ]
    Matrix (Fin d₁) (Fin d₁) ℂ where
  toFun ρ := Matrix.of fun i₁ j₁ =>
    ∑ k : Fin d₂, ρ (finProdEquiv d₁ d₂ (i₁, k)) (finProdEquiv d₁ d₂ (j₁, k))
  map_add' ρ₁ ρ₂ := by
    ext i₁ j₁
    simp [Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c ρ := by
    ext i₁ j₁
    simp [Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum]

/-- Partial trace over the first register.

    `(partialTrace₁ ρ)_{i₂,j₂} = ∑_{k : Fin d₁} ρ_{(k,i₂),(k,j₂)}` -/
def partialTrace₁ :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ →ₗ[ℂ]
    Matrix (Fin d₂) (Fin d₂) ℂ where
  toFun ρ := Matrix.of fun i₂ j₂ =>
    ∑ k : Fin d₁, ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂))
  map_add' ρ₁ ρ₂ := by
    ext i₂ j₂
    simp [Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c ρ := by
    ext i₂ j₂
    simp [Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum]

theorem partialTrace₂_apply (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₁ j₁ : Fin d₁) :
    partialTrace₂ ρ i₁ j₁ =
      ∑ k : Fin d₂, ρ (finProdEquiv d₁ d₂ (i₁, k)) (finProdEquiv d₁ d₂ (j₁, k)) := by
  simp [partialTrace₂, Matrix.of_apply]

theorem partialTrace₁_apply (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₂ j₂ : Fin d₂) :
    partialTrace₁ ρ i₂ j₂ =
      ∑ k : Fin d₁, ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂)) := by
  simp [partialTrace₁, Matrix.of_apply]

/-- Total trace = trace of partial trace (over second register). -/
theorem trace_partialTrace₂ (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    (partialTrace₂ ρ : Matrix (Fin d₁) (Fin d₁) ℂ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTrace₂_apply]
  rw [← Fintype.sum_prod_type (fun p : Fin d₁ × Fin d₂ =>
    ρ (finProdEquiv d₁ d₂ p) (finProdEquiv d₁ d₂ p))]
  exact Equiv.sum_comp (finProdEquiv d₁ d₂) (fun i => ρ i i)

/-- Total trace = trace of partial trace (over first register). -/
theorem trace_partialTrace₁ (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    (partialTrace₁ ρ : Matrix (Fin d₂) (Fin d₂) ℂ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTrace₁_apply]
  rw [← Fintype.sum_prod_type_right (fun p : Fin d₁ × Fin d₂ =>
    ρ (finProdEquiv d₁ d₂ p) (finProdEquiv d₁ d₂ p))]
  exact Equiv.sum_comp (finProdEquiv d₁ d₂) (fun i => ρ i i)

/-- Partial trace of Kronecker product: `tr₂(A ⊗ B) = tr(B) • A`. -/
theorem partialTrace₂_kronecker
    (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    partialTrace₂ (A ⊗ₖ B) = B.trace • A := by
  ext i₁ j₁
  simp only [partialTrace₂_apply, kronecker_apply, Equiv.symm_apply_apply,
    Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  simp_rw [← Finset.mul_sum]
  ring

/-- Partial trace of Kronecker product: `tr₁(A ⊗ B) = tr(A) • B`. -/
theorem partialTrace₁_kronecker
    (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    partialTrace₁ (A ⊗ₖ B) = A.trace • B := by
  ext i₂ j₂
  simp only [partialTrace₁_apply, kronecker_apply, Equiv.symm_apply_apply,
    Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  simp_rw [← Finset.sum_mul]

/-- Partial trace preserves positive semidefiniteness. -/
theorem partialTrace₂_psd
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (hρ : ρ.PosSemidef) :
    (partialTrace₂ ρ : Matrix (Fin d₁) (Fin d₁) ℂ).PosSemidef := by
  have heq : partialTrace₂ ρ = ∑ k : Fin d₂,
      ρ.submatrix (fun i₁ => finProdEquiv d₁ d₂ (i₁, k))
        (fun j₁ => finProdEquiv d₁ d₂ (j₁, k)) := by
    refine Matrix.ext fun i₁ j₁ => ?_
    rw [partialTrace₂_apply, Matrix.sum_apply, Finset.sum_congr rfl fun k _ => ?_]
    simp [Matrix.submatrix_apply]
  rw [heq]
  exact posSemidef_sum _ fun k _ => hρ.submatrix _

theorem partialTrace₁_psd
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (hρ : ρ.PosSemidef) :
    (partialTrace₁ ρ : Matrix (Fin d₂) (Fin d₂) ℂ).PosSemidef := by
  have heq : partialTrace₁ ρ = ∑ k : Fin d₁,
      ρ.submatrix (fun i₂ => finProdEquiv d₁ d₂ (k, i₂))
        (fun j₂ => finProdEquiv d₁ d₂ (k, j₂)) := by
    refine Matrix.ext fun i₂ j₂ => ?_
    rw [partialTrace₁_apply, Matrix.sum_apply, Finset.sum_congr rfl fun k _ => ?_]
    simp [Matrix.submatrix_apply]
  rw [heq]
  exact posSemidef_sum _ fun k _ => hρ.submatrix _

/-! ## Partial traces of products with local operators -/

/-- `tr₂((A ⊗ I) X) = A tr₂(X)`. -/
theorem partialTrace₂_kronecker_one_mul (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    partialTrace₂ ((A ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) * X) =
      A * partialTrace₂ X := by
  ext i j
  simp only [partialTrace₂_apply, Matrix.mul_apply, kronecker_apply]
  rw [Finset.sum_comm, ← (finProdEquiv d₁ d₂).sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, one_apply, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]

/-- `tr₂(X (B ⊗ I)) = tr₂(X) B`. -/
theorem partialTrace₂_mul_kronecker_one (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (B : Matrix (Fin d₁) (Fin d₁) ℂ) :
    partialTrace₂ (X * (B ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ))) =
      partialTrace₂ X * B := by
  ext i j
  simp only [partialTrace₂_apply, Matrix.mul_apply, kronecker_apply]
  rw [Finset.sum_comm, ← (finProdEquiv d₁ d₂).sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]

/-- The traced register is cyclic: `tr₂((I ⊗ C) X) = tr₂(X (I ⊗ C))`. -/
theorem partialTrace₂_one_kronecker_mul_comm (C : Matrix (Fin d₂) (Fin d₂) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    partialTrace₂ (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ C) * X) =
      partialTrace₂ (X * ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ C)) := by
  ext i j
  simp only [partialTrace₂_apply, Matrix.mul_apply, kronecker_apply]
  have e : ∀ f : Fin (d₁ * d₂) → ℂ, ∑ l, f l = ∑ p : Fin d₁ × Fin d₂,
      f (finProdEquiv d₁ d₂ p) := fun f => ((finProdEquiv d₁ d₂).sum_comp f).symm
  simp only [e, Fintype.sum_prod_type, Equiv.symm_apply_apply, one_apply, ite_mul,
    zero_mul, one_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm (C _ _) _

/-- `tr₁((I ⊗ B) X) = B tr₁(X)`. -/
theorem partialTrace₁_one_kronecker_mul (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    partialTrace₁ (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ B) * X) =
      B * partialTrace₁ X := by
  ext i j
  simp only [partialTrace₁_apply, Matrix.mul_apply, kronecker_apply]
  have e : ∀ f : Fin (d₁ * d₂) → ℂ, ∑ l, f l = ∑ p : Fin d₁ × Fin d₂,
      f (finProdEquiv d₁ d₂ p) := fun f => ((finProdEquiv d₁ d₂).sum_comp f).symm
  simp only [e, Fintype.sum_prod_type, Equiv.symm_apply_apply, one_apply, ite_mul,
    zero_mul, one_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- `tr₁(X (I ⊗ B)) = tr₁(X) B`. -/
theorem partialTrace₁_mul_one_kronecker (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    partialTrace₁ (X * ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ B)) =
      partialTrace₁ X * B := by
  ext i j
  simp only [partialTrace₁_apply, Matrix.mul_apply, kronecker_apply]
  have e : ∀ f : Fin (d₁ * d₂) → ℂ, ∑ l, f l = ∑ p : Fin d₁ × Fin d₂,
      f (finProdEquiv d₁ d₂ p) := fun f => ((finProdEquiv d₁ d₂).sum_comp f).symm
  simp only [e, Fintype.sum_prod_type, Equiv.symm_apply_apply, one_apply, ite_mul,
    zero_mul, one_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

/-- The traced register is cyclic: `tr₁((C ⊗ I) X) = tr₁(X (C ⊗ I))`. -/
theorem partialTrace₁_kronecker_one_mul_comm (C : Matrix (Fin d₁) (Fin d₁) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    partialTrace₁ ((C ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) * X) =
      partialTrace₁ (X * (C ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ))) := by
  ext i j
  simp only [partialTrace₁_apply, Matrix.mul_apply, kronecker_apply]
  have e : ∀ f : Fin (d₁ * d₂) → ℂ, ∑ l, f l = ∑ p : Fin d₁ × Fin d₂,
      f (finProdEquiv d₁ d₂ p) := fun f => ((finProdEquiv d₁ d₂).sum_comp f).symm
  simp only [e, Fintype.sum_prod_type, Equiv.symm_apply_apply, one_apply, ite_mul,
    zero_mul, mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm (C _ _) _

/-! ## Local Kraus operators on the traced register -/

/-- The local Kraus sum on the traced register is invisible to `tr₂`: for a
complete family `N`, `∑_b tr₂((A ⊗ N_b) X (B ⊗ N_b)ᴴ) = A tr₂(X) Bᴴ`. -/
theorem sum_partialTrace₂_kronecker_conj {ι : Type} [Fintype ι]
    (A B : Matrix (Fin d₁) (Fin d₁) ℂ) (N : ι → Matrix (Fin d₂) (Fin d₂) ℂ)
    (hN : ∑ b, (N b)ᴴ * N b = 1) (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑ b, partialTrace₂ ((A ⊗ₖ N b) * X * (B ⊗ₖ N b)ᴴ) =
      A * partialTrace₂ X * Bᴴ := by
  have term : ∀ b, partialTrace₂ ((A ⊗ₖ N b) * X * (B ⊗ₖ N b)ᴴ) =
      A * partialTrace₂ (X * ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ ((N b)ᴴ * N b))) *
        Bᴴ := by
    intro b
    have hl : A ⊗ₖ N b = (A ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) *
        ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ N b) := by
      rw [kronecker_mul_kronecker, mul_one, one_mul]
    have hr : (B ⊗ₖ N b)ᴴ = ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ (N b)ᴴ) *
        (Bᴴ ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) := by
      rw [conjTranspose_kronecker, kronecker_mul_kronecker, mul_one, one_mul]
    rw [hl, hr]
    rw [show (A ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) *
        ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ N b) * X *
        (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ (N b)ᴴ) *
          (Bᴴ ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ))) =
        (A ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) *
          (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ N b) *
            (X * ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ (N b)ᴴ))) *
          (Bᴴ ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) by simp only [Matrix.mul_assoc]]
    rw [partialTrace₂_mul_kronecker_one, partialTrace₂_kronecker_one_mul,
      partialTrace₂_one_kronecker_mul_comm, Matrix.mul_assoc X, kronecker_mul_kronecker,
      one_mul]
  simp only [term]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, ← Finset.mul_sum,
    kronecker_finset_sum_right, hN, kronecker_one_one, mul_one]

/-- The local Kraus sum on the traced register is invisible to `tr₁`: for a
complete family `M`, `∑_a tr₁((M_a ⊗ A) X (M_a ⊗ B)ᴴ) = A tr₁(X) Bᴴ`. -/
theorem sum_partialTrace₁_kronecker_conj {ι : Type} [Fintype ι]
    (M : ι → Matrix (Fin d₁) (Fin d₁) ℂ) (A B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (hM : ∑ a, (M a)ᴴ * M a = 1) (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑ a, partialTrace₁ ((M a ⊗ₖ A) * X * (M a ⊗ₖ B)ᴴ) =
      A * partialTrace₁ X * Bᴴ := by
  have term : ∀ a, partialTrace₁ ((M a ⊗ₖ A) * X * (M a ⊗ₖ B)ᴴ) =
      A * partialTrace₁ (X * (((M a)ᴴ * M a) ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ))) *
        Bᴴ := by
    intro a
    have hl : M a ⊗ₖ A = ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ A) *
        (M a ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) := by
      rw [kronecker_mul_kronecker, mul_one, one_mul]
    have hr : (M a ⊗ₖ B)ᴴ = ((M a)ᴴ ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) *
        ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ Bᴴ) := by
      rw [conjTranspose_kronecker, kronecker_mul_kronecker, mul_one, one_mul]
    rw [hl, hr]
    rw [show ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ A) *
        (M a ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) * X *
        (((M a)ᴴ ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) *
          ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ Bᴴ)) =
        ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ A) *
          ((M a ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) *
            (X * ((M a)ᴴ ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)))) *
          ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ Bᴴ) by simp only [Matrix.mul_assoc]]
    rw [partialTrace₁_mul_one_kronecker, partialTrace₁_one_kronecker_mul,
      partialTrace₁_kronecker_one_mul_comm, Matrix.mul_assoc X, kronecker_mul_kronecker,
      one_mul]
  simp only [term]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, ← Finset.mul_sum,
    kronecker_finset_sum_left, hM, kronecker_one_one, mul_one]

/-- An isometry on the traced register is invisible to `tr₂`:
`tr₂((A ⊗ V) X (B ⊗ V)ᴴ) = A tr₂(X) Bᴴ` when `Vᴴ V = I`. -/
theorem partialTrace₂_kronecker_conj_of_isometry (A B : Matrix (Fin d₁) (Fin d₁) ℂ)
    {V : Matrix (Fin d₂) (Fin d₂) ℂ} (hV : Vᴴ * V = 1)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    partialTrace₂ ((A ⊗ₖ V) * X * (B ⊗ₖ V)ᴴ) = A * partialTrace₂ X * Bᴴ := by
  simpa using sum_partialTrace₂_kronecker_conj (ι := Unit) A B (fun _ => V)
    (by simpa using hV) X

/-- An isometry on the traced register is invisible to `tr₁`:
`tr₁((U ⊗ A) X (U ⊗ B)ᴴ) = A tr₁(X) Bᴴ` when `Uᴴ U = I`. -/
theorem partialTrace₁_kronecker_conj_of_isometry {U : Matrix (Fin d₁) (Fin d₁) ℂ}
    (hU : Uᴴ * U = 1) (A B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    partialTrace₁ ((U ⊗ₖ A) * X * (U ⊗ₖ B)ᴴ) = A * partialTrace₁ X * Bᴴ := by
  simpa using sum_partialTrace₁_kronecker_conj (ι := Unit) (fun _ => U) A B
    (by simpa using hU) X

end CatCrypt.Quantum.PartialTrace

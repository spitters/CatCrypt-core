/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SemiClassicalOracle

/-!
# The algebra of permutation unitaries

`permUnitary σ` is the unitary `e_k ↦ e_{σ k}` of a permutation `σ` of the
index set. This module gives its matrix entry, its behaviour under
multiplication, conjugation and Kronecker product, and identifies the oracle
unitary of the total register as a permutation unitary.

## Main definitions

* `oracleIndex m n w` — the row-major index of `((x, y), z)` in
  `Fin (m * n * w)`
* `oraclePerm m n w H` — the permutation `((x, y), z) ↦ ((x, y + H x), z)` of
  `Fin (m * n * w)`

## Main results

* `permUnitary_apply`, `permUnitary_apply'` — the entry
  `(permUnitary σ) i j = [i = σ j] = [j = σ⁻¹ i]`
* `permUnitary_one`, `permUnitary_mul` — `permUnitary` is multiplicative in
  the order `permUnitary σ * permUnitary τ = permUnitary (σ * τ)`
* `permUnitary_conj` — conjugation by `permUnitary σ` reindexes by `σ.symm`
* `permUnitary_conj_diagonal` — conjugating a diagonal matrix precomposes its
  diagonal with `σ.symm`
* `permUnitary_kron` — the Kronecker product of two permutation unitaries is
  the permutation unitary of the product permutation transported along
  `finProdEquiv`
* `oracleU_eq_permUnitary` — the oracle unitary on the total register is
  `permUnitary (oraclePerm m n w H)`

## Scope

Every statement is about permutation matrices over `ℂ` at an arbitrary finite
index type, except the Kronecker product and the oracle identification, which
use the row-major index `finProdEquiv` of the `Fin`-indexed Kronecker product.
No matrix is reduced at a numeric dimension.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Entries, products and conjugation -/

section Algebra

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The entry of a permutation unitary: `1` on the row `σ j`, `0` elsewhere. -/
theorem permUnitary_apply (σ : Equiv.Perm n) (i j : n) :
    (permUnitary σ : Matrix n n ℂ) i j = if i = σ j then 1 else 0 := by
  rw [permUnitary_val]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  by_cases h : i = σ j
  · subst h; simp
  · have h' : σ.symm i ≠ j := fun hj => h (by rw [← hj]; simp)
    simp [h, h']

/-- The entry of a permutation unitary, with the condition on the column. -/
theorem permUnitary_apply' (σ : Equiv.Perm n) (i j : n) :
    (permUnitary σ : Matrix n n ℂ) i j = if j = σ.symm i then 1 else 0 := by
  rw [permUnitary_apply]
  by_cases h : j = σ.symm i
  · subst h; simp
  · have h' : i ≠ σ j := fun hj => h (by rw [hj]; simp)
    simp [h, h']

@[simp]
theorem permUnitary_one : permUnitary (1 : Equiv.Perm n) = 1 := by
  ext i j
  rw [permUnitary_val, inv_one, Matrix.permMatrix_one]
  rfl

/-- `permUnitary` is multiplicative: the product of the unitaries of `σ` and
    `τ` is the unitary of `σ * τ`. -/
theorem permUnitary_mul (σ τ : Equiv.Perm n) :
    permUnitary σ * permUnitary τ = permUnitary (σ * τ) := by
  ext i j
  simp only [Submonoid.coe_mul, Matrix.mul_apply, permUnitary_apply, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (τ j)]
  · by_cases h : i = σ (τ j) <;> simp [h]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (τ j)) h

/-- Conjugation by `permUnitary σ` is reindexing by `σ.symm`. -/
theorem permUnitary_conj (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    (permUnitary σ : Matrix n n ℂ) * M * (permUnitary σ : Matrix n n ℂ)ᴴ =
      M.submatrix σ.symm σ.symm := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permUnitary_apply,
    Matrix.submatrix_apply]
  rw [Finset.sum_eq_single (σ.symm j)]
  · rw [Finset.sum_eq_single (σ.symm i)]
    · simp
    · intro b _ hb
      have hib : ¬ i = σ b := fun h => hb (by rw [h]; simp)
      simp [hib]
    · intro h
      exact absurd (Finset.mem_univ (σ.symm i)) h
  · intro a _ ha
    have hja : ¬ j = σ a := fun h => ha (by rw [h]; simp)
    simp [hja]
  · intro h
    exact absurd (Finset.mem_univ (σ.symm j)) h

/-- Conjugating a diagonal matrix by `permUnitary σ` precomposes its diagonal
    with `σ.symm`. -/
theorem permUnitary_conj_diagonal (σ : Equiv.Perm n) (f : n → ℂ) :
    (permUnitary σ : Matrix n n ℂ) * Matrix.diagonal f *
        (permUnitary σ : Matrix n n ℂ)ᴴ =
      Matrix.diagonal (fun k => f (σ.symm k)) := by
  rw [permUnitary_conj, Matrix.submatrix_diagonal_equiv]
  rfl

/-- `permUnitary σ` is invertible with inverse the conjugate transpose. -/
theorem star_permUnitary_mul (σ : Equiv.Perm n) :
    (permUnitary σ : Matrix n n ℂ)ᴴ * (permUnitary σ : Matrix n n ℂ) = 1 := by
  have := (permUnitary σ).prop
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at this
  exact this

end Algebra

/-! ## The Kronecker product of permutation unitaries -/

section Kron

variable {d₁ d₂ : ℕ}

/-- The Kronecker product of two permutation unitaries is the permutation
    unitary of the product permutation, transported along the row-major index
    `finProdEquiv`. -/
theorem permUnitary_kron (σ : Equiv.Perm (Fin d₁)) (τ : Equiv.Perm (Fin d₂)) :
    (permUnitary σ : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ
        (permUnitary τ : Matrix (Fin d₂) (Fin d₂) ℂ) =
      (permUnitary ((finProdEquiv d₁ d₂).permCongr (σ.prodCongr τ)) :
        Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) := by
  ext i j
  rw [kronecker_apply, permUnitary_apply, permUnitary_apply, permUnitary_apply,
    Equiv.permCongr_apply]
  have hiff : i = finProdEquiv d₁ d₂ ((σ.prodCongr τ) ((finProdEquiv d₁ d₂).symm j)) ↔
      (((finProdEquiv d₁ d₂).symm i).1 = σ ((finProdEquiv d₁ d₂).symm j).1 ∧
        ((finProdEquiv d₁ d₂).symm i).2 = τ ((finProdEquiv d₁ d₂).symm j).2) := by
    rw [← Equiv.symm_apply_eq, Prod.ext_iff]
    simp [Equiv.prodCongr_apply]
  rw [if_congr hiff rfl rfl, ite_and]
  split_ifs <;> simp

end Kron

/-! ## The oracle unitary as a permutation unitary -/

section Oracle

variable (m n w : ℕ) [NeZero n]

/-- The row-major index of `((x, y), z)` in the total register
    `Fin (m * n * w)`. -/
def oracleIndex : (Fin m × Fin n) × Fin w ≃ Fin (m * n * w) :=
  ((finProdEquiv m n).prodCongr (Equiv.refl (Fin w))).trans (finProdEquiv (m * n) w)

/-- The permutation `((x, y), z) ↦ ((x, y + H x), z)` of the total register's
    index set: the standard oracle for `H` acting on the value factor. -/
def oraclePerm (H : Fin m → Fin n) : Equiv.Perm (Fin (m * n * w)) :=
  (oracleIndex m n w).permCongr ((stdOraclePerm H).prodCongr (Equiv.refl (Fin w)))

@[simp]
theorem oraclePerm_apply (H : Fin m → Fin n) (x : Fin m) (y : Fin n) (z : Fin w) :
    oraclePerm m n w H (oracleIndex m n w ((x, y), z)) =
      oracleIndex m n w ((x, y + H x), z) := by
  simp [oraclePerm, Equiv.permCongr_apply, Equiv.prodCongr_apply]

/-- The oracle unitary on the total register is the permutation unitary of
    `oraclePerm`. -/
theorem oracleU_eq_permUnitary (H : Fin m → Fin n) :
    (oracleU m n w H : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) =
      (permUnitary (oraclePerm m n w H) : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) := by
  have h1 : (1 : Matrix (Fin w) (Fin w) ℂ) =
      (permUnitary (1 : Equiv.Perm (Fin w)) : Matrix (Fin w) (Fin w) ℂ) := by simp
  rw [oracleU_val, stdOracleFixedG, h1, permUnitary_kron]
  congr 1

end Oracle

end CatCrypt.Quantum.QROM

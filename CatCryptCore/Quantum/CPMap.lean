/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.PosDef
public import CatCryptCore.Quantum.TraceNorm
public import CatCryptCore.Quantum.UnitaryChannel

/-!
# Completely Positive Maps and Duality

This file defines positive, completely positive, and trace-preserving linear
maps on complex matrices, along with the dual (adjoint) map construction.

## Main Definitions

* `IsPositiveMap` — preserves positive semidefiniteness
* `IsCPMap` — completely positive (positive under tensoring with identity)
* `IsTP` — trace-preserving
* `CPTPMap` — bundled CPTP channel
* `dualMap` — dual/adjoint w.r.t. Hilbert-Schmidt inner product

## Main Results

* `cptp_id` — identity is CPTP
* `cptp_comp` — composition of CPTP maps is CPTP
* `isCPMap_add`, `isCPMap_sum`, `isCPMap_comp` — complete positivity is closed
  under sums and composition
* `isCPMap_conj` — a linear map acting as `ρ ↦ K ρ Kᴴ` for some matrix `K` is
  completely positive; `isCPMap_conjugate` is its instance at
  `UnitaryChannel.conjugate K`
* `tp_iff_dual_unital` — TP ↔ dual map is unital
* `dual_positive_of_positive` — dual of positive map is positive
* `dual_cp_of_cp` — dual of CP map is CP (via block-level duality)
* `cpu_preserves_effect` — CPU maps preserve effects

## References

* Wilde, *Quantum Information Theory* (Cambridge, 2017)
* Watrous, *The Theory of Quantum Information* (Cambridge, 2018)
-/

@[expose] public section

open scoped Matrix ComplexOrder
open Matrix

noncomputable section

namespace CatCrypt.Quantum

/-! ## General Theory (arbitrary Fintype index)

All definitions and lemmas in this section work for matrices indexed by any
`Fintype` with `DecidableEq`. This generality is needed to apply
`dual_positive_of_positive` at `ι = Fin k × Fin n` in the proof of `dual_cp_of_cp`. -/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear map on matrices is positive if it preserves PSD. -/
def IsPositiveMap
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) : Prop :=
  ∀ A, A.PosSemidef → (Φ A).PosSemidef

/-- Trace preserving: `tr(Φ(A)) = tr(A)` for all `A`. -/
def IsTP
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) : Prop :=
  ∀ A, (Φ A).trace = A.trace

/-- Sub-trace-preserving on PSD inputs: `tr(Φ(A)).re ≤ tr(A).re` for PSD `A`. -/
def IsSTP
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) : Prop :=
  ∀ A, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re

/-! ## Dual Map -/

/-- Standard matrix unit: 1 at position (i, j), 0 elsewhere. -/
def matUnit (i j : ι) : Matrix ι ι ℂ :=
  fun k l => if k = i ∧ l = j then 1 else 0

omit [Fintype ι] in
@[simp]
theorem matUnit_apply (i j k l : ι) :
    matUnit i j k l = if k = i ∧ l = j then 1 else 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Push a `Finset.sum` through two levels of Pi (matrix entry access). -/
@[simp]
theorem Finset.sum_matrix_entry {κ : Type*} (s : Finset κ)
    (f : κ → Matrix ι ι ℂ) (i j : ι) :
    (∑ x ∈ s, f x) i j = ∑ x ∈ s, f x i j := by
  have h1 : (∑ x ∈ s, f x) i = ∑ x ∈ s, f x i := Finset.sum_apply i s f
  have h2 : (∑ x ∈ s, (fun x => f x i) x) j = ∑ x ∈ s, (fun x => f x i) x j :=
    Finset.sum_apply j s (fun x => f x i)
  exact (congr_fun h1 j).trans h2

/-- Expand `Φ B` entry-wise using linearity over matrix units. -/
theorem linearMap_expand
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (B : Matrix ι ι ℂ) (l k : ι) :
    (Φ B) l k = ∑ q : ι, ∑ p : ι, B q p * (Φ (matUnit q p)) l k := by
  have hB : B = ∑ q : ι, ∑ p : ι, B q p • matUnit q p := by
    ext a b
    simp only [Finset.sum_matrix_entry, Matrix.smul_apply, matUnit_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp_rw [show ∀ q p, (if a = q ∧ b = p then B q p else 0) =
      if a = q then (if b = p then B q p else 0) else 0 from by
      intros q p; split_ifs <;> simp_all]
    simp [Finset.mem_univ]
  conv_lhs => rw [hB]
  simp only [map_sum, LinearMapClass.map_smul, Finset.sum_matrix_entry,
    Matrix.smul_apply, smul_eq_mul]

/-- Dual of a linear map on matrices: defined by `tr(Φ†(A) * B) = tr(A * Φ(B))`.
    Constructed entry-wise: `(Φ†(A))_{i,j} = ∑_k ∑_l A_{k,l} * (Φ(matUnit j i))_{l,k}`. -/
def dualMap
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun A i j := ∑ k : ι, ∑ l : ι, A k l * (Φ (matUnit j i)) l k
  map_add' A₁ A₂ := by
    ext i j
    change _ = (_ : ℂ) + _
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext i j
    show _ = c * _
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Entry formula of the dual map:
    `(Φ†(A))_{i,j} = ∑_k ∑_l A_{k,l} * (Φ(matUnit j i))_{l,k}`. -/
theorem dualMap_apply
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (i j : ι) :
    dualMap Φ A i j = ∑ k : ι, ∑ l : ι, A k l * (Φ (matUnit j i)) l k := rfl

/-- Defining property of the dual map:
    `tr(Φ†(A) * B) = tr(A * Φ(B))` for all `A`, `B`. -/
theorem dual_spec
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (A B : Matrix ι ι ℂ) :
    (dualMap Φ A * B).trace = (A * Φ B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dualMap_apply]
  simp_rw [Finset.sum_mul, linearMap_expand Φ B, Finset.mul_sum]
  -- Both sides are 4-nested sums of the same term up to commutativity of (*)
  -- Normalize both summands to: A k l * (B j i * Φ(matUnit j i) l k)
  trans ∑ i, ∑ j, ∑ k, ∑ l, A k l * (B j i * (Φ (matUnit j i)) l k)
  · -- ring-normalize the LHS summand
    congr 1; funext i; congr 1; funext j; congr 1; funext k; congr 1; funext l; ring
  · -- Reorder sums: (i,j,k,l) → (k,l,j,i) via bubble-sort of Finset.sum_comm
    calc ∑ i, ∑ j, ∑ k, ∑ l, A k l * (B j i * (Φ (matUnit j i)) l k)
        = ∑ i, ∑ k, ∑ j, ∑ l, A k l * (B j i * (Φ (matUnit j i)) l k) := by
          congr 1; funext i; exact Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, A k l * (B j i * (Φ (matUnit j i)) l k) :=
          Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, A k l * (B j i * (Φ (matUnit j i)) l k) := by
          congr 1; funext k; congr 1; funext i; exact Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ i, ∑ j, A k l * (B j i * (Φ (matUnit j i)) l k) := by
          congr 1; funext k; exact Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ j, ∑ i, A k l * (B j i * (Φ (matUnit j i)) l k) := by
          congr 1; funext k; congr 1; funext l; exact Finset.sum_comm

/-- Trace of product with matrix unit extracts an entry. -/
theorem trace_mul_matUnit (M : Matrix ι ι ℂ) (i j : ι) :
    (M * matUnit j i).trace = M i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, matUnit_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro k _ hk; apply Finset.sum_eq_zero; intro l _; simp [hk]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Trace of a matrix unit is 1 if on diagonal, 0 otherwise. -/
theorem trace_matUnit (i j : ι) :
    (matUnit i j : Matrix ι ι ℂ).trace = if i = j then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, matUnit_apply]
  split_ifs with h
  · subst h; simp
  · apply Finset.sum_eq_zero
    intro k _
    simp [show ¬(k = i ∧ k = j) from fun ⟨hki, hkj⟩ => h (hki.symm ▸ hkj)]

/-- TP ↔ dual map is unital. -/
theorem tp_iff_dual_unital
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    IsTP Φ ↔ dualMap Φ 1 = 1 := by
  constructor
  · intro hTP
    ext i j
    have h1 := dual_spec Φ 1 (matUnit j i)
    rw [trace_mul_matUnit, one_mul] at h1
    rw [h1, hTP, trace_matUnit]
    simp [Matrix.one_apply, eq_comm]
  · intro hdual B
    have := dual_spec Φ 1 B
    rw [one_mul] at this
    rw [← this, hdual, one_mul]

/-! ## Helper lemmas for dual positivity -/

omit [DecidableEq ι] in
/-- `(Uᴴ * N * U) i i` equals the quadratic form `⟨col_i(U), N · col_i(U)⟩`. -/
private theorem conjTranspose_mul_mul_diag_eq_quadForm
    (U N : Matrix ι ι ℂ) (i : ι) :
    (Uᴴ * N * U) i i = star (fun k => U k i) ⬝ᵥ N.mulVec (fun k => U k i) := by
  simp only [mul_apply, conjTranspose_apply, mulVec, dotProduct, Pi.star_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext j; ring

/-- Multiplication of a nonneg real scalar and a nonneg complex number is nonneg. -/
private theorem Complex.ofReal_mul_nonneg {r : ℝ} {z : ℂ} (hr : 0 ≤ r) (hz : 0 ≤ z) :
    0 ≤ (r : ℂ) * z := by
  rw [Complex.nonneg_iff] at hz ⊢
  constructor
  · simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz.2.symm]
    exact mul_nonneg hr hz.1
  · simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hz.2.symm]

omit [Fintype ι] in
/-- `conjTranspose (matUnit i j) = matUnit j i`. -/
private theorem matUnit_conjTranspose (i j : ι) :
    (matUnit i j : Matrix ι ι ℂ)ᴴ = matUnit j i := by
  ext k l
  simp only [conjTranspose_apply, matUnit_apply, and_comm]
  split <;> simp

/-- Trace of product of two PSD matrices is nonneg.
    Proof via spectral decomposition of `A`:
    `tr(A * B) = ∑ᵢ λᵢ · ⟨vᵢ, B vᵢ⟩` where `λᵢ ≥ 0` and `⟨vᵢ, B vᵢ⟩ ≥ 0`. -/
theorem trace_psd_mul_psd_nonneg
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  set U : Matrix ι ι ℂ := ↑hA.isHermitian.eigenvectorUnitary
  set ev := hA.isHermitian.eigenvalues
  set D : Matrix ι ι ℂ := diagonal (Complex.ofReal ∘ ev)
  have hA_spec : A = U * D * star U := by
    have hs := hA.isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at hs; convert hs using 1
  rw [hA_spec]
  have htrace : (U * D * star U * B).trace = (D * (Uᴴ * B * U)).trace := by
    calc (U * D * star U * B).trace
        = (U * (D * (star U * B))).trace := by rw [mul_assoc, mul_assoc]
      _ = (D * (star U * B) * U).trace := by rw [trace_mul_comm]
      _ = (D * (star U * (B * U))).trace := by rw [mul_assoc, mul_assoc]
      _ = (D * (Uᴴ * (B * U))).trace := by rw [star_eq_conjTranspose]
      _ = (D * (Uᴴ * B * U)).trace := by rw [mul_assoc]
  rw [htrace]
  simp only [trace, diag, diagonal_mul, D, Function.comp]
  apply Finset.sum_nonneg
  intro i _
  apply Complex.ofReal_mul_nonneg
  · exact hA.eigenvalues_nonneg i
  · rw [conjTranspose_mul_mul_diag_eq_quadForm]
    exact hB.dotProduct_mulVec_nonneg _

omit [DecidableEq ι] in
/-- `star v ⬝ᵥ M *ᵥ v = trace(M * vecMulVec v (star v))`. -/
private theorem quadForm_eq_trace (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ M.mulVec x = (M * vecMulVec x (star x)).trace := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

omit [DecidableEq ι] in
/-- `vecMulVec x (star x)` is PSD (rank-1 outer product). -/
private theorem posSemidef_outer_product (x : ι → ℂ) :
    (vecMulVec x (star x)).PosSemidef := by
  have := posSemidef_vecMulVec_star_self (star x)
  simp at this; exact this

omit [DecidableEq ι] in
/-- The imaginary part of `star x ⬝ᵥ M *ᵥ x` for PSD `M` is zero. -/
private theorem im_quadForm_of_psd {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (x : ι → ℂ) :
    (star x ⬝ᵥ M.mulVec x).im = 0 :=
  hM.isHermitian.im_star_dotProduct_mulVec_self x

/-- Standard basis vector: `eᵢ(k) = if k = i then 1 else 0`. -/
private def basisVec (i : ι) : ι → ℂ := fun k => if k = i then 1 else 0

omit [DecidableEq ι] in
/-- The outer product `vecMulVec (star v) v` is PSD. -/
private theorem psd_outer (v : ι → ℂ) :
    (vecMulVec (star v) v).PosSemidef := posSemidef_vecMulVec_star_self v

omit [Fintype ι] in
/-- Decomposition of `matUnit i j` into 4 PSD outer products:
    `matUnit i j = (1/4)•P₁ - (1/4)•P₂ - (I/4)•P₃ + (I/4)•P₄`. -/
private theorem matUnit_decomp₁ (i j : ι) :
    matUnit i j = (1/4 : ℂ) • vecMulVec (star (basisVec i + basisVec j)) (basisVec i + basisVec j)
      - (1/4 : ℂ) • vecMulVec (star (basisVec i - basisVec j)) (basisVec i - basisVec j)
      - (Complex.I/4) • vecMulVec (star (basisVec i + Complex.I • basisVec j)) (basisVec i + Complex.I • basisVec j)
      + (Complex.I/4) • vecMulVec (star (basisVec i - Complex.I • basisVec j)) (basisVec i - Complex.I • basisVec j) := by
  ext k l
  simp only [matUnit_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply, Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    basisVec, star_add, star_sub, star_smul, Complex.star_def, Complex.conj_I]
  by_cases hki : k = i <;> by_cases hlj : l = j <;>
    by_cases hkj : k = j <;> by_cases hli : l = i <;>
    simp_all <;> norm_num [Complex.ext_iff, Complex.I_re, Complex.I_im]

omit [Fintype ι] in
/-- Conjugate decomposition: `matUnit j i` from the same 4 PSD matrices,
    with sign of `I/4` terms flipped. -/
private theorem matUnit_decomp₂ (i j : ι) :
    matUnit j i = (1/4 : ℂ) • vecMulVec (star (basisVec i + basisVec j)) (basisVec i + basisVec j)
      - (1/4 : ℂ) • vecMulVec (star (basisVec i - basisVec j)) (basisVec i - basisVec j)
      + (Complex.I/4) • vecMulVec (star (basisVec i + Complex.I • basisVec j)) (basisVec i + Complex.I • basisVec j)
      - (Complex.I/4) • vecMulVec (star (basisVec i - Complex.I • basisVec j)) (basisVec i - Complex.I • basisVec j) := by
  ext k l
  simp only [matUnit_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply, Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    basisVec, star_add, star_sub, star_smul, Complex.star_def, Complex.conj_I]
  by_cases hki : k = i <;> by_cases hlj : l = j <;>
    by_cases hkj : k = j <;> by_cases hli : l = i <;>
    simp_all <;> norm_num [Complex.ext_iff, Complex.I_re, Complex.I_im]

/-- Positive maps are star-preserving on matrix units: `(Φ(eᵢⱼ))ᴴ = Φ(eⱼᵢ)`. -/
private theorem positive_map_conjTranspose_matUnit
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hΦ : IsPositiveMap Φ) (i j : ι) :
    (Φ (matUnit i j))ᴴ = Φ (matUnit j i) := by
  let P₁ := vecMulVec (star (basisVec i + basisVec j)) (basisVec i + basisVec j)
  let P₂ := vecMulVec (star (basisVec i - basisVec j)) (basisVec i - basisVec j)
  let P₃ := vecMulVec (star (basisVec i + Complex.I • basisVec j)) (basisVec i + Complex.I • basisVec j)
  let P₄ := vecMulVec (star (basisVec i - Complex.I • basisVec j)) (basisVec i - Complex.I • basisVec j)
  have hP₁ : (Φ P₁).IsHermitian := (hΦ _ (psd_outer _)).isHermitian
  have hP₂ : (Φ P₂).IsHermitian := (hΦ _ (psd_outer _)).isHermitian
  have hP₃ : (Φ P₃).IsHermitian := (hΦ _ (psd_outer _)).isHermitian
  have hP₄ : (Φ P₄).IsHermitian := (hΦ _ (psd_outer _)).isHermitian
  rw [matUnit_decomp₁ i j, matUnit_decomp₂ i j]
  simp only [map_add, map_sub, LinearMapClass.map_smul]
  simp only [conjTranspose_sub, conjTranspose_add, conjTranspose_smul]
  rw [hP₁.eq, hP₂.eq, hP₃.eq, hP₄.eq]
  rw [show star ((1 : ℂ) / 4) = 1 / 4 from by simp,
      show star (Complex.I / 4) = -(Complex.I / 4) from by simp [Complex.conj_I, neg_div]]
  simp only [neg_smul, sub_neg_eq_add]
  abel

/-- Dual of a positive map is positive. -/
theorem dual_positive_of_positive
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hΦ : IsPositiveMap Φ) : IsPositiveMap (dualMap Φ) := by
  intro A hA
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply IsHermitian.ext; intro i j
    simp only [dualMap_apply]
    simp_rw [star_sum, star_mul']
    simp_rw [show ∀ k l, star (A k l) = A l k from fun k l => hA.isHermitian.apply l k]
    simp_rw [show ∀ l k, star ((Φ (matUnit i j)) l k) = Φ (matUnit j i) k l from
      fun l k => by
        have h := congr_fun₂ (positive_map_conjTranspose_matUnit Φ hΦ i j) k l
        simp only [conjTranspose_apply] at h; exact h]
    rw [Finset.sum_comm]
  · intro x
    rw [quadForm_eq_trace]
    rw [dual_spec]
    exact trace_psd_mul_psd_nonneg A _ hA (hΦ _ (posSemidef_outer_product x))

end General

/-! ## Completely Positive Maps and Block Structure -/

section FinN

variable {n : ℕ}

/-- Extract the `(a, b)`-th `n×n` block from a `(k×n)×(k×n)` block matrix. -/
def blockMatrix {k : ℕ} (M : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ)
    (a b : Fin k) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => M (a, i) (b, j)

/-- Apply `Φ` blockwise to a `(k×n)×(k×n)` matrix, implementing `id_k ⊗ Φ`:
    `((id_k ⊗ Φ)(M))_{(a,i),(b,j)} = (Φ(M_{a,b}))_{i,j}`. -/
def tensorIdMap
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ →ₗ[ℂ]
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ where
  toFun M p q := (Φ (blockMatrix M p.1 q.1)) p.2 q.2
  map_add' M₁ M₂ := by
    funext ⟨a, i⟩ ⟨b, j⟩
    show (Φ (blockMatrix (M₁ + M₂) a b)) i j =
      (Φ (blockMatrix M₁ a b)) i j + (Φ (blockMatrix M₂ a b)) i j
    have : blockMatrix (M₁ + M₂) a b = blockMatrix M₁ a b + blockMatrix M₂ a b := by
      ext; simp [blockMatrix, Matrix.add_apply]
    rw [this, map_add]; rfl
  map_smul' c M := by
    funext ⟨a, i⟩ ⟨b, j⟩
    show (Φ (blockMatrix (c • M) a b)) i j = c * (Φ (blockMatrix M a b)) i j
    have : blockMatrix (c • M) a b = c • blockMatrix M a b := by
      ext; simp [blockMatrix, Matrix.smul_apply]
    rw [this, LinearMapClass.map_smul]; rfl

/-- Entry formula of the blockwise map `id_k ⊗ Φ`. -/
theorem tensorIdMap_apply
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (M : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) (p q : Fin k × Fin n) :
    tensorIdMap Φ k M p q = (Φ (blockMatrix M p.1 q.1)) p.2 q.2 := rfl

/-- A linear map is completely positive if `id_k ⊗ Φ` is positive for all `k`.
    Formulation: for all `k`, the induced blockwise map on `(k×n)×(k×n)` matrices
    preserves positive semidefiniteness. -/
def IsCPMap
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (k : ℕ) (M : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ),
    M.PosSemidef → (tensorIdMap Φ k M).PosSemidef

/-- A completely positive map is positive: complete positivity at `k = 1`,
    with `A` embedded as the single block of a `(1×n)×(1×n)` matrix. -/
theorem IsCPMap.isPositiveMap
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hΦ : IsCPMap Φ) : IsPositiveMap Φ := by
  intro A hA
  have h := hΦ 1 (A.submatrix Prod.snd Prod.snd) (hA.submatrix _)
  have e : Φ A = (tensorIdMap Φ 1 (A.submatrix Prod.snd Prod.snd)).submatrix
      (fun i => ((0 : Fin 1), i)) (fun i => ((0 : Fin 1), i)) := rfl
  rw [e]
  exact h.submatrix _

/-- `id_k ⊗ (Ψ ∘ Φ) = (id_k ⊗ Ψ) ∘ (id_k ⊗ Φ)`: the block-wise tensor with the
identity commutes with composition. -/
theorem tensorIdMap_comp
    (Ψ Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (M : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) :
    tensorIdMap (Ψ.comp Φ) k M = tensorIdMap Ψ k (tensorIdMap Φ k M) := by
  ext p q
  rfl

/-- The identity map is completely positive. -/
theorem isCPMap_id :
    IsCPMap (LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin n) (Fin n) ℂ) := by
  intro k M hM
  have h : tensorIdMap
      (LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
      k M = M := by
    funext p q
    rfl
  rwa [h]

/-- The sum of two completely positive maps is completely positive. -/
theorem isCPMap_add
    {Φ Ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hΦ : IsCPMap Φ) (hΨ : IsCPMap Ψ) : IsCPMap (Φ + Ψ) :=
  fun k M hM => (hΦ k M hM).add (hΨ k M hM)

/-- A finite sum of completely positive maps is completely positive. -/
theorem isCPMap_sum {ι : Type*} (s : Finset ι)
    (Φ : ι → Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i ∈ s, IsCPMap (Φ i)) : IsCPMap (∑ i ∈ s, Φ i) := by
  refine Finset.sum_induction _ IsCPMap (fun _ _ => isCPMap_add) ?_ h
  intro k M _
  have h0 : tensorIdMap
      (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) k M = 0 := by
    funext p q
    rfl
  rw [h0]
  exact Matrix.PosSemidef.zero

/-- The composite of two completely positive maps is completely positive. -/
theorem isCPMap_comp
    {Ψ Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hΨ : IsCPMap Ψ) (hΦ : IsCPMap Φ) : IsCPMap (Ψ.comp Φ) := by
  intro k M hM
  rw [tensorIdMap_comp]
  exact hΨ k _ (hΦ k M hM)

/-- A linear map `Φ` with `Φ ρ = K ρ Kᴴ` for every `ρ` is completely positive:
its extension `id_k ⊗ Φ` is conjugation by `1ₖ ⊗ K`. -/
theorem isCPMap_conj (K : Matrix (Fin n) (Fin n) ℂ)
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ ρ, Φ ρ = K * ρ * Kᴴ) : IsCPMap Φ := by
  intro k M hM
  have key : tensorIdMap Φ k M =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin k) (Fin k) ℂ) K * M *
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin k) (Fin k) ℂ) K)ᴴ := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [tensorIdMap_apply, hΦ, blockMatrix, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.one_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp
  rw [key]
  exact hM.mul_mul_conjTranspose_same _

/-- Conjugation `ρ ↦ K ρ Kᴴ` by any matrix is completely positive. -/
theorem isCPMap_conjugate (K : Matrix (Fin n) (Fin n) ℂ) :
    IsCPMap (UnitaryChannel.conjugate K) :=
  isCPMap_conj K _ (UnitaryChannel.conjugate_apply K)

/-! ## CPTP Map (Bundled) -/

/-- A CPTP (completely positive, trace-preserving) map.
    This represents a quantum channel. -/
structure CPTPMap (n : ℕ) where
  toLinearMap : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ
  cp : IsCPMap toLinearMap
  tp : IsTP toLinearMap

/-- A CPTP map is positive. -/
theorem CPTPMap.positive (Φ : CPTPMap n) : IsPositiveMap Φ.toLinearMap :=
  Φ.cp.isPositiveMap

/-! ## Basic Constructions -/

/-- The identity channel is CPTP. -/
def cptp_id : CPTPMap n where
  toLinearMap := LinearMap.id
  cp := isCPMap_id
  tp := fun A => by simp

/-- Composition of CPTP maps is CPTP. -/
def cptp_comp (Φ Ψ : CPTPMap n) : CPTPMap n where
  toLinearMap := Ψ.toLinearMap.comp Φ.toLinearMap
  cp := fun k M hM => by
    rw [tensorIdMap_comp]
    exact Ψ.cp k _ (Φ.cp k M hM)
  tp := fun A => by
    simp only [LinearMap.comp_apply]
    rw [Ψ.tp, Φ.tp]

/-- CPTP maps preserve PSD (complete positivity at `k = 1`). -/
theorem cptp_preserves_psd (Φ : CPTPMap n) {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) : (Φ.toLinearMap ρ).PosSemidef :=
  Φ.positive ρ hρ

/-- CPTP maps preserve trace (from TP). -/
theorem cptp_preserves_trace (Φ : CPTPMap n) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (Φ.toLinearMap ρ).trace = ρ.trace :=
  Φ.tp ρ

/-! ## CP Duality -/

/-- Collapse a sum over a product type with a first-component filter:
    `∑ x : α × β, (if x.1 = a then f x else 0) = ∑ b : β, f (a, b)`. -/
private lemma sum_prod_fst_eq {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [AddCommMonoid M] (a : α) (f : α × β → M) :
    ∑ x : α × β, (if x.1 = a then f x else 0) = ∑ b : β, f (a, b) := by
  rw [Fintype.sum_prod_type]
  have hfact : ∀ a', (∑ b' : β, if a' = a then f (a', b') else 0) =
      if a' = a then ∑ b', f (a', b') else 0 := by
    intro a'; split_ifs <;> simp
  simp_rw [hfact, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Block decomposition of matrix units in the product type:
    `blockMatrix (matUnit x y) d c` is `matUnit x.2 y.2` when `d = x.1 ∧ c = y.1`,
    and zero otherwise. Uses product-type arguments for `simp_rw` matching. -/
private theorem blockMatrix_matUnit {k : ℕ} (x y : Fin k × Fin n) (c d : Fin k) :
    blockMatrix (matUnit x y) d c =
      if d = x.1 ∧ c = y.1 then (matUnit x.2 y.2 : Matrix (Fin n) (Fin n) ℂ) else 0 := by
  obtain ⟨xk, xn⟩ := x; obtain ⟨yk, yn⟩ := y
  by_cases hd : d = xk <;> by_cases hc : c = yk
  · subst hd; subst hc; ext p q; unfold blockMatrix matUnit; simp [Prod.mk.injEq]
  · subst hd; ext p q; unfold blockMatrix matUnit; simp [Prod.mk.injEq, hc]
  · subst hc; ext p q; unfold blockMatrix matUnit; simp [hd]
  · ext p q; unfold blockMatrix matUnit; simp [hd]

/-- The dual of `tensorIdMap Φ k` (at the `Fin k × Fin n` level) equals
    `tensorIdMap (dualMap Φ) k`. This is the key lemma for `dual_cp_of_cp`. -/
private theorem dualMap_tensorIdMap {k : ℕ}
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    dualMap (tensorIdMap Φ k) = tensorIdMap (dualMap Φ) k := by
  ext M ⟨a, i⟩ ⟨b, j⟩
  simp only [dualMap_apply, tensorIdMap_apply]
  simp_rw [blockMatrix_matUnit, apply_ite Φ, map_zero,
    Matrix.ite_apply, Matrix.zero_apply, mul_ite, mul_zero]
  -- Collapse: only x_1.1=b, x.1=a terms survive in the double sum
  simp_rw [ite_and, sum_prod_fst_eq b]
  rw [Finset.sum_comm]
  simp_rw [sum_prod_fst_eq a]
  rw [Finset.sum_comm]
  unfold blockMatrix
  rfl

/-- The dual of a CP map is CP. Proof: for each `k`, `tensorIdMap Φ k` is positive
    (by CP). By `dual_positive_of_positive`, its dual is positive. By
    `dualMap_tensorIdMap`, this dual equals `tensorIdMap (dualMap Φ) k`. -/
theorem dual_cp_of_cp
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hΦ : IsCPMap Φ) : IsCPMap (dualMap Φ) := by
  intro k M hM
  rw [show tensorIdMap (dualMap Φ) k = dualMap (tensorIdMap Φ k) from
    (dualMap_tensorIdMap Φ).symm]
  exact dual_positive_of_positive _ (fun A hA => hΦ k A hA) M hM

/-! ## Corollaries -/

/-- CPTP dual is CPU (completely positive + unital). -/
theorem cptp_dual_is_cpu (Φ : CPTPMap n) :
    IsPositiveMap (dualMap Φ.toLinearMap) ∧ dualMap Φ.toLinearMap 1 = 1 := by
  constructor
  · exact dual_positive_of_positive _ Φ.positive
  · exact (tp_iff_dual_unital _).mp Φ.tp

/-- CPU maps preserve effects: `0 ≤ E ≤ I → 0 ≤ Φ†(E) ≤ I`.
    Proof: CP ⟹ positive, so Φ†(E) ≥ 0.
           Φ†(I-E) = I - Φ†(E) ≥ 0, so Φ†(E) ≤ I. -/
theorem cpu_preserves_effect (Φ : CPTPMap n) (E : Matrix (Fin n) (Fin n) ℂ)
    (hE : CatCrypt.Quantum.IsEffect E) :
    CatCrypt.Quantum.IsEffect (dualMap Φ.toLinearMap E) := by
  obtain ⟨hE_psd, hE_comp⟩ := hE
  constructor
  · exact dual_positive_of_positive _ Φ.positive _ hE_psd
  · rw [show 1 - dualMap Φ.toLinearMap E = dualMap Φ.toLinearMap (1 - E) from
      by rw [map_sub, (tp_iff_dual_unital _).mp Φ.tp]]
    exact dual_positive_of_positive _ Φ.positive _ hE_comp

end FinN

end CatCrypt.Quantum

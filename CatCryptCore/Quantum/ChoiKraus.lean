/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import CatCryptCore.Quantum.CPMap

@[expose] public section

set_option autoImplicit false

/-!
# Choi matrix and Kraus representation of completely positive maps

For a linear map `Φ` on `n × n` complex matrices, the Choi matrix is the
`(n·n) × (n·n)` matrix whose `(a, b)` block is `Φ (matUnit a b)`. It is the image
of the unnormalised maximally entangled projector under `id_n ⊗ Φ`, so complete
positivity in the sense of `IsCPMap` makes it positive semidefinite. A factorisation
`choi Φ = Bᴴ * B` (through the matrix square root) yields `n·n` Kraus operators.

## Main definitions

* `choi` — the Choi matrix of `Φ`, indexed by `Fin n × Fin n`.
* `krausOfFactor` — the Kraus operators read off a factor `B` of the Choi matrix.

## Main results

* `choi_posSemidef` — `IsCPMap Φ → (choi Φ).PosSemidef`.
* `exists_kraus_of_choi_posSemidef`, `exists_kraus` — a map with PSD Choi matrix,
  in particular a CP map, is a Kraus sum over `Fin n × Fin n`.
* `exists_kraus_fin` — the same with index set `Fin (n * n)`.
* `kraus_sum_conjTranspose_mul_self_eq_one` — the Kraus operators of a
  trace-preserving map satisfy `∑ i, (K i)ᴴ * K i = 1`.
* `isCPMap_of_kraus` — a Kraus sum is completely positive.
* `isCPMap_iff_exists_kraus`, `isCPMap_iff_choi_posSemidef` — the two
  characterisations of complete positivity.

## References

* Choi, *Completely positive linear maps on complex matrices*, Linear Algebra
  Appl. 10 (1975)
* Watrous, *The Theory of Quantum Information* (Cambridge, 2018), §2.2
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

namespace CatCrypt.Quantum

variable {n : ℕ}

/-! ## The Choi matrix -/

/-- The Choi matrix of `Φ`: `choi Φ (a, i) (b, j) = Φ (matUnit a b) i j`. -/
def choi (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q => Φ (matUnit p.1 q.1) p.2 q.2

/-- Entry formula of the Choi matrix. -/
theorem choi_apply (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (a i b j : Fin n) : choi Φ (a, i) (b, j) = Φ (matUnit a b) i j := rfl

/-- The unnormalised maximally entangled vector `∑ a, e_a ⊗ e_a`. -/
def maxEntVec : Fin n × Fin n → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- The `(a, b)` block of `|Ω⟩⟨Ω|` is the matrix unit `matUnit a b`. -/
theorem blockMatrix_maxEnt (a b : Fin n) :
    blockMatrix (vecMulVec (maxEntVec (n := n)) (star maxEntVec)) a b = matUnit a b := by
  ext i j
  simp only [blockMatrix, vecMulVec_apply, Pi.star_apply, maxEntVec, matUnit_apply]
  by_cases hai : a = i <;> by_cases hbj : b = j <;> simp [hai, hbj, eq_comm]

/-- The Choi matrix is `(id_n ⊗ Φ) |Ω⟩⟨Ω|`. -/
theorem choi_eq_tensorIdMap
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    choi Φ = tensorIdMap Φ n (vecMulVec maxEntVec (star maxEntVec)) := by
  funext p q
  rw [tensorIdMap_apply, blockMatrix_maxEnt]
  rfl

/-- The Choi matrix of a completely positive map is positive semidefinite. -/
theorem choi_posSemidef {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hΦ : IsCPMap Φ) : (choi Φ).PosSemidef := by
  rw [choi_eq_tensorIdMap]
  exact hΦ n _ (posSemidef_vecMulVec_self_star _)

/-! ## Kraus operators from a factorisation of the Choi matrix -/

/-- The Kraus operators read off a factor `B` of the Choi matrix:
`krausOfFactor B r i a = star (B r (a, i))`. -/
def krausOfFactor {r : Type*} (B : Matrix r (Fin n × Fin n) ℂ) (x : r) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i a => star (B x (a, i))

/-- If `choi Φ = Bᴴ * B`, then `Φ` is the Kraus sum of `krausOfFactor B`. -/
theorem eq_kraus_of_choi_eq {r : Type*} [Fintype r]
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix r (Fin n × Fin n) ℂ) (hB : choi Φ = Bᴴ * B)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Φ ρ = ∑ x, krausOfFactor B x * ρ * (krausOfFactor B x)ᴴ := by
  ext i j
  rw [linearMap_expand Φ ρ i j, Finset.sum_matrix_entry]
  have hc : ∀ a b, Φ (matUnit a b) i j = ∑ x, star (B x (a, i)) * B x (b, j) := by
    intro a b
    rw [← choi_apply, hB, mul_apply]
    rfl
  simp_rw [hc, mul_apply, conjTranspose_apply, krausOfFactor, of_apply, star_star,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring

/-- A positive semidefinite complex matrix is `Bᴴ * B` for a square `B`. -/
theorem exists_eq_conjTranspose_mul_self_of_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  have h0 : 0 ≤ A := nonneg_iff_posSemidef.mpr hA
  refine ⟨CFC.sqrt A, ?_⟩
  have hs : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  rw [← star_eq_conjTranspose, hs, CFC.sqrt_mul_sqrt_self A h0]

/-- A map whose Choi matrix is positive semidefinite is a Kraus sum over
`Fin n × Fin n`. -/
theorem exists_kraus_of_choi_posSemidef
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hΦ : (choi Φ).PosSemidef) :
    ∃ K : Fin n × Fin n → Matrix (Fin n) (Fin n) ℂ,
      ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ := by
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul_self_of_posSemidef hΦ
  exact ⟨krausOfFactor B, eq_kraus_of_choi_eq Φ B hB⟩

/-- Kraus representation: a completely positive map is a Kraus sum over
`Fin n × Fin n`. -/
theorem exists_kraus {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hΦ : IsCPMap Φ) :
    ∃ K : Fin n × Fin n → Matrix (Fin n) (Fin n) ℂ,
      ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ :=
  exists_kraus_of_choi_posSemidef (choi_posSemidef hΦ)

/-- Kraus representation with `n * n` operators indexed by `Fin (n * n)`. -/
theorem exists_kraus_fin {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hΦ : IsCPMap Φ) :
    ∃ K : Fin (n * n) → Matrix (Fin n) (Fin n) ℂ,
      ∀ ρ, Φ ρ = ∑ i, K i * ρ * (K i)ᴴ := by
  obtain ⟨K, hK⟩ := exists_kraus hΦ
  refine ⟨fun i => K (finProdFinEquiv.symm i), fun ρ => ?_⟩
  rw [hK ρ]
  exact (finProdFinEquiv.symm.sum_comp (fun x => K x * ρ * (K x)ᴴ)).symm

/-! ## Trace preservation -/

/-- The Kraus operators of a trace-preserving map satisfy the completeness
relation `∑ x, (K x)ᴴ * K x = 1`. -/
theorem kraus_sum_conjTranspose_mul_self_eq_one {r : Type*} [Fintype r]
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    {K : r → Matrix (Fin n) (Fin n) ℂ} (hK : ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ)
    (hTP : IsTP Φ) : ∑ x, (K x)ᴴ * K x = 1 := by
  have htr : ∀ ρ, ((∑ x, (K x)ᴴ * K x) * ρ).trace = ρ.trace := by
    intro ρ
    rw [← hTP ρ, hK ρ, trace_sum, Finset.sum_mul, trace_sum]
    exact Finset.sum_congr rfl fun x _ => trace_mul_cycle (K x) ρ (K x)ᴴ |>.symm
  refine Matrix.ext fun i j => ?_
  rw [← trace_mul_matUnit (∑ x, (K x)ᴴ * K x) i j, htr,
    ← trace_mul_matUnit (1 : Matrix (Fin n) (Fin n) ℂ) i j, Matrix.one_mul]

/-! ## Kraus sums are completely positive -/

/-- A Kraus sum `ρ ↦ ∑ x, K x * ρ * (K x)ᴴ` is completely positive. -/
theorem isCPMap_of_kraus {r : Type*} [Fintype r]
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (K : r → Matrix (Fin n) (Fin n) ℂ) (hK : ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ) :
    IsCPMap Φ := by
  classical
  let C : r → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) := fun x =>
    (LinearMap.mulLeft ℂ (K x)).comp (LinearMap.mulRight ℂ (K x)ᴴ)
  have hC : ∀ x ρ, C x ρ = K x * ρ * (K x)ᴴ := fun x ρ => by
    simp [C, Matrix.mul_assoc]
  intro k M hM
  have hsum : tensorIdMap Φ k M = ∑ x, tensorIdMap (C x) k M := by
    funext p q
    rw [tensorIdMap_apply, hK, Finset.sum_matrix_entry, Finset.sum_matrix_entry]
    simp only [tensorIdMap_apply, hC]
  rw [hsum]
  exact posSemidef_sum _ fun x _ =>
    isCPMap_conj (K x) (C x) (hC x) k M hM

/-! ## Characterisations of complete positivity -/

/-- A linear map is completely positive iff it is a Kraus sum over `Fin n × Fin n`. -/
theorem isCPMap_iff_exists_kraus
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} :
    IsCPMap Φ ↔ ∃ K : Fin n × Fin n → Matrix (Fin n) (Fin n) ℂ,
      ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ :=
  ⟨exists_kraus, fun ⟨K, hK⟩ => isCPMap_of_kraus K hK⟩

/-- Choi's theorem: a linear map is completely positive iff its Choi matrix is
positive semidefinite. -/
theorem isCPMap_iff_choi_posSemidef
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} :
    IsCPMap Φ ↔ (choi Φ).PosSemidef :=
  ⟨choi_posSemidef, fun h =>
    let ⟨K, hK⟩ := exists_kraus_of_choi_posSemidef h
    isCPMap_of_kraus K hK⟩

end CatCrypt.Quantum

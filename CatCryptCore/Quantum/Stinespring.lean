/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.ChoiKraus
public import CatCryptCore.Quantum.PartialTrace
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option autoImplicit false

/-!
# Stinespring dilation and purification

A register `Fin D` is split into a system `Fin d` and an ancilla `Fin r` by an
equivalence `e : Fin (d * r) ≃ Fin D`, with `Fin (d * r)` indexed row-major by
`finProdEquiv` (system first). This is the convention of `kr e A B =
(A ⊗ₖ B).submatrix e.symm e.symm` in `CatCryptCore.Quantum.QROM.MultiRound`; the ancilla state
`Matrix.diagonal (Pi.single 0 1)` is `ancProj 0` there.

## Main definitions

* `trAnc e M` — the partial trace of `M : Matrix (Fin D) (Fin D) ℂ` over the ancilla.
* `dilation e K` — the matrix `V : Matrix (Fin D) (Fin d) ℂ` with `V (x, i) y = K i x y`.
* `ancEmbed e` — the isometry `ψ ↦ ψ ⊗ |0⟩`.

## Main results

* `dilation_conjTranspose_mul_self_eq_one` — Kraus operators with
  `∑ i, (K i)ᴴ * K i = 1` give an isometry `Vᴴ * V = 1`.
* `trAnc_dilation_conj` — `trAnc e (V * ρ * Vᴴ) = ∑ i, K i * ρ * (K i)ᴴ`.
* `exists_unitary_mul_ancEmbed` — an isometry `V` is `U * ancEmbed e` for a unitary `U`.
* `unitary_conj_kr_ancProj` — then `U (ρ ⊗ |0⟩⟨0|) Uᴴ = V ρ Vᴴ`.
* `stinespring` — a completely positive trace-preserving map `Φ` on `Fin d`
  is `ρ ↦ trAnc e (U (ρ ⊗ |0⟩⟨0|) Uᴴ)` for a unitary `U` on `Fin (d * (d * d))`.
* `exists_purification` — a density matrix is the ancilla partial trace of a
  pure state on `Fin (d * d)`.

## References

* Watrous, *The Theory of Quantum Information* (Cambridge, 2018), §2.2
-/

open scoped Matrix ComplexOrder InnerProductSpace
open Matrix CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.PartialTrace

noncomputable section

namespace CatCrypt.Quantum.Stinespring

variable {d r D : ℕ}

/-! ## Partial trace over the ancilla -/

/-- The partial trace over the ancilla `Fin r` of a register `Fin D ≃ Fin (d * r)`. -/
def trAnc (e : Fin (d * r) ≃ Fin D) (M : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  partialTrace₂ (M.submatrix e e)

theorem trAnc_apply (e : Fin (d * r) ≃ Fin D) (M : Matrix (Fin D) (Fin D) ℂ) (x x' : Fin d) :
    trAnc e M x x' =
      ∑ k : Fin r, M (e (finProdEquiv d r (x, k))) (e (finProdEquiv d r (x', k))) := by
  simp [trAnc, partialTrace₂_apply]

theorem trace_trAnc (e : Fin (d * r) ≃ Fin D) (M : Matrix (Fin D) (Fin D) ℂ) :
    (trAnc e M).trace = M.trace := by
  rw [trAnc, trace_partialTrace₂]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact e.sum_comp (fun a => M a a)

/-- A sum over the register is a double sum over system and ancilla. -/
theorem sum_register (e : Fin (d * r) ≃ Fin D) (f : Fin D → ℂ) :
    ∑ a, f a = ∑ x : Fin d, ∑ i : Fin r, f (e (finProdEquiv d r (x, i))) := by
  rw [← (((finProdEquiv d r).trans e).sum_comp f), Fintype.sum_prod_type]
  rfl

/-! ## The isometry of a Kraus family -/

/-- The Stinespring isometry of Kraus operators `K`: `dilation e K (e (x, i)) y = K i x y`. -/
def dilation (e : Fin (d * r) ≃ Fin D) (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin D) (Fin d) ℂ :=
  Matrix.of fun a y =>
    K ((finProdEquiv d r).symm (e.symm a)).2 ((finProdEquiv d r).symm (e.symm a)).1 y

theorem dilation_apply_pair (e : Fin (d * r) ≃ Fin D) (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin d) (i : Fin r) (y : Fin d) :
    dilation e K (e (finProdEquiv d r (x, i))) y = K i x y := by
  simp [dilation]

theorem dilation_conjTranspose_mul_self (e : Fin (d * r) ≃ Fin D)
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    (dilation e K)ᴴ * dilation e K = ∑ i, (K i)ᴴ * K i := by
  ext y y'
  rw [mul_apply, sum_register e, Matrix.sum_apply, Finset.sum_comm]
  simp [mul_apply, conjTranspose_apply, dilation_apply_pair]

/-- Kraus operators satisfying the completeness relation give an isometry. -/
theorem dilation_conjTranspose_mul_self_eq_one (e : Fin (d * r) ≃ Fin D)
    {K : Fin r → Matrix (Fin d) (Fin d) ℂ} (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (dilation e K)ᴴ * dilation e K = 1 := by
  rw [dilation_conjTranspose_mul_self, hK]

/-- The ancilla partial trace of `V ρ Vᴴ` is the Kraus sum. -/
theorem trAnc_dilation_conj (e : Fin (d * r) ≃ Fin D) (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    trAnc e (dilation e K * ρ * (dilation e K)ᴴ) = ∑ i, K i * ρ * (K i)ᴴ := by
  ext x x'
  rw [trAnc_apply, Matrix.sum_apply]
  simp [mul_apply, conjTranspose_apply, dilation_apply_pair]

/-! ## Extension of an isometry to a unitary -/

section Ancilla

variable [NeZero r]

/-- The isometry `ψ ↦ ψ ⊗ |0⟩` from the system into the register. -/
def ancEmbed (e : Fin (d * r) ≃ Fin D) : Matrix (Fin D) (Fin d) ℂ :=
  Matrix.of fun a y => if a = e (finProdEquiv d r (y, 0)) then 1 else 0

/-- `ancEmbed e * ρ * (ancEmbed e)ᴴ` is `ρ ⊗ |0⟩⟨0|` along `e`. -/
theorem ancEmbed_conj (e : Fin (d * r) ≃ Fin D) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    ancEmbed e * ρ * (ancEmbed e)ᴴ =
      (ρ ⊗ₖ Matrix.diagonal (Pi.single 0 1)).submatrix e.symm e.symm := by
  ext a b
  obtain ⟨⟨x, i⟩, rfl⟩ := ((finProdEquiv d r).trans e).surjective a
  obtain ⟨⟨x', i'⟩, rfl⟩ := ((finProdEquiv d r).trans e).surjective b
  simp [ancEmbed, mul_apply, conjTranspose_apply, kronecker_apply, Matrix.diagonal_apply,
    Pi.single_apply]
  rcases eq_or_ne i 0 with rfl | hi <;> rcases eq_or_ne i' 0 with rfl | hi' <;>
    simp [*, Ne.symm]

/-- An isometry `V` factors as `U * ancEmbed e` with `U` unitary. -/
theorem exists_unitary_mul_ancEmbed (e : Fin (d * r) ≃ Fin D) {V : Matrix (Fin D) (Fin d) ℂ}
    (hV : Vᴴ * V = 1) :
    ∃ U ∈ Matrix.unitaryGroup (Fin D) ℂ, U * ancEmbed e = V := by
  let j : Fin d → Fin D := fun y => e (finProdEquiv d r (y, 0))
  have hj : Function.Injective j := fun y y' h => by
    simpa [j] using h
  let col : Fin d → EuclideanSpace ℂ (Fin D) := fun y => WithLp.toLp 2 (fun a => V a y)
  have hcol : Orthonormal ℂ col := by
    rw [orthonormal_iff_ite]
    intro y y'
    have h := congrFun (congrFun hV y) y'
    rw [mul_apply, one_apply] at h
    rw [← h]
    simp only [col, PiLp.inner_apply, conjTranspose_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  let v : Fin D → EuclideanSpace ℂ (Fin D) := Function.extend j col 0
  have hv : Orthonormal ℂ ((Set.range j).domRestrict v) := by
    have : (Set.range j).domRestrict v = col ∘ (Equiv.ofInjective j hj).symm := by
      funext ⟨_, y, rfl⟩
      simp [v, hj.extend_apply]
    rw [this]
    exact hcol.comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨(EuclideanSpace.basisFun (Fin D) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin D) ℂ).toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  ext a y
  have hby : b (j y) = col y := by
    rw [hb _ ⟨y, rfl⟩]
    simp [v, hj.extend_apply]
  simp [ancEmbed, mul_apply, Module.Basis.toMatrix_apply]
  exact congrArg (fun w => w.ofLp a) hby

/-- For `U * ancEmbed e = V`, conjugating `ρ ⊗ |0⟩⟨0|` by `U` is conjugating `ρ` by `V`. -/
theorem unitary_conj_kr_ancProj (e : Fin (d * r) ≃ Fin D) {U : Matrix (Fin D) (Fin D) ℂ}
    {V : Matrix (Fin D) (Fin d) ℂ} (hU : U * ancEmbed e = V) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    U * (ρ ⊗ₖ Matrix.diagonal (Pi.single 0 1)).submatrix e.symm e.symm * Uᴴ =
      V * ρ * Vᴴ := by
  rw [← ancEmbed_conj, ← hU, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-! ## Stinespring dilation -/

/-- A Kraus family satisfying the completeness relation is the ancilla partial
trace of a unitary conjugation of `ρ ⊗ |0⟩⟨0|`. -/
theorem exists_unitary_of_kraus (e : Fin (d * r) ≃ Fin D)
    {K : Fin r → Matrix (Fin d) (Fin d) ℂ} (hK : ∑ i, (K i)ᴴ * K i = 1) :
    ∃ U ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
      ∑ i, K i * ρ * (K i)ᴴ =
        trAnc e (U * (ρ ⊗ₖ Matrix.diagonal (Pi.single 0 1)).submatrix e.symm e.symm * Uᴴ) := by
  obtain ⟨U, hU, hUV⟩ :=
    exists_unitary_mul_ancEmbed e (dilation_conjTranspose_mul_self_eq_one e hK)
  exact ⟨U, hU, fun ρ => by rw [unitary_conj_kr_ancProj e hUV, trAnc_dilation_conj]⟩

end Ancilla

/-- Stinespring dilation: a completely positive trace-preserving map on `Fin d`
is the ancilla partial trace of a unitary conjugation of `ρ ⊗ |0⟩⟨0|` on a
register `Fin D ≃ Fin (d * (d * d))`. -/
theorem stinespring [NeZero d] {Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hCP : IsCPMap Φ) (hTP : IsTP Φ) (e : Fin (d * (d * d)) ≃ Fin D) :
    ∃ U ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
      Φ ρ = trAnc e (U * (ρ ⊗ₖ Matrix.diagonal (Pi.single 0 1)).submatrix e.symm e.symm * Uᴴ) := by
  obtain ⟨K, hK⟩ := exists_kraus_fin hCP
  obtain ⟨U, hU, hUρ⟩ := exists_unitary_of_kraus e (kraus_sum_conjTranspose_mul_self_eq_one hK hTP)
  exact ⟨U, hU, fun ρ => by rw [hK ρ, hUρ ρ]⟩

/-! ## Purification -/

/-- A density matrix on `Fin d` is the ancilla partial trace of a pure state on
a register `Fin D ≃ Fin (d * d)`. -/
theorem exists_purification (e : Fin (d * d) ≃ Fin D) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ ψ : Fin D → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ ρ = trAnc e (vecMulVec ψ (star ψ)) := by
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul_self_of_posSemidef hρ
  let ψ : Fin D → ℂ := fun a =>
    star (B ((finProdEquiv d d).symm (e.symm a)).2 ((finProdEquiv d d).symm (e.symm a)).1)
  have hρψ : ρ = trAnc e (vecMulVec ψ (star ψ)) := by
    rw [hB]
    ext x x'
    rw [trAnc_apply]
    simp [ψ, mul_apply, conjTranspose_apply, vecMulVec_apply]
  refine ⟨ψ, ?_, hρψ⟩
  rw [← htr, hρψ, trace_trAnc, trace_vecMulVec, dotProduct_comm]

end CatCrypt.Quantum.Stinespring

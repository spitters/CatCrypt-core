/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.Stinespring
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Naimark dilation of a measurement

A measurement `M : X → Matrix E E ℂ` (positive semidefinite effects summing to `1`) is the
compression of a projective measurement on the larger register `E × X`: there are pairwise
orthogonal projections `Q x` with `∑ x, Q x = 1` and `Vᴴ (Q x) V = M x` for the isometry
`V = ancEmb x₀ : ψ ↦ ψ ⊗ |x₀⟩`.

## Main definitions

* `ancProj x` — the projector onto the outcome `x` of the ancilla `X` of `E × X`
* `ancEmb x₀` — the isometry `ψ ↦ ψ ⊗ |x₀⟩`
* `povmDilation M` — the isometry `ψ ↦ ∑ x, √(M x) ψ ⊗ |x⟩`

## Main results

* `povmDilation_isometry` — `povmDilation M` is an isometry when `∑ x, M x = 1`
* `exists_unitary_mul_ancEmb` — an isometry `V` is `U * ancEmb x₀` for a unitary `U`
* `exists_naimark` — a measurement is the compression of pairwise orthogonal projections
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace Kronecker

noncomputable section

namespace CatCrypt.Quantum.Naimark

open Matrix

section Naimark

variable {E X : Type} [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

/-- The projector onto the outcome `x` of the ancilla `X` of the register `E × X`. -/
def ancProj (x : X) : Matrix (E × X) (E × X) ℂ :=
  diagonal fun p => if p.2 = x then 1 else 0

/-- The embedding `e ↦ e ⊗ |x₀⟩` of `E` into `E × X`. -/
def ancEmb (x₀ : X) : Matrix (E × X) E ℂ :=
  Matrix.of fun p e => if p = (e, x₀) then 1 else 0

/-- The dilation of a measurement `M`: the matrix `V` with `V (f, z) e = (√M_z) f e`. -/
def povmDilation (M : X → Matrix E E ℂ) : Matrix (E × X) E ℂ :=
  Matrix.of fun p e => CFC.sqrt (M p.2) p.1 e

/-- The ancilla projector is a star projection. -/
theorem ancProj_isStarProjection (x : X) : IsStarProjection (ancProj (E := E) x) := by
  constructor <;> ext p q <;> simp [ancProj, diagonal_apply] <;> grind

/-- Ancilla projectors of distinct outcomes are orthogonal. -/
theorem ancProj_mul_ancProj {x x' : X} (h : x ≠ x') :
    ancProj (E := E) x * ancProj x' = 0 := by
  ext p q
  simp [ancProj, diagonal_apply]
  grind

omit [Fintype E] in
/-- The ancilla projectors sum to the identity. -/
theorem sum_ancProj : ∑ x : X, ancProj (E := E) x = 1 := by
  ext p q
  simp [ancProj, diagonal_apply, Matrix.sum_apply, Matrix.one_apply]

/-- `Vᴴ (1 ⊗ |x⟩⟨x|) V = M_x` for the dilation `V` of a measurement `M`. -/
theorem povmDilation_compress {M : X → Matrix E E ℂ} (hM : ∀ x, (M x).PosSemidef) (x : X) :
    (povmDilation M)ᴴ * ancProj x * povmDilation M = M x := by
  have h0 : (0 : Matrix E E ℂ) ≤ M x := (hM x).nonneg
  have hH : (CFC.sqrt (M x))ᴴ = CFC.sqrt (M x) := (CFC.sqrt_nonneg (M x)).isSelfAdjoint
  conv_rhs => rw [← CFC.sqrt_mul_sqrt_self (M x) h0]
  nth_rw 1 [← hH]
  ext e e'
  simp [Matrix.mul_apply, povmDilation, ancProj, Fintype.sum_prod_type, diagonal_apply]

omit [DecidableEq X] in
/-- The dilation of a measurement is an isometry. -/
theorem povmDilation_isometry {M : X → Matrix E E ℂ} (hM : ∀ x, (M x).PosSemidef)
    (hsum : ∑ x, M x = 1) : (povmDilation M)ᴴ * povmDilation M = 1 := by
  classical
  calc (povmDilation M)ᴴ * povmDilation M
      = (povmDilation M)ᴴ * (∑ x : X, ancProj x) * povmDilation M := by
        rw [sum_ancProj, Matrix.mul_one]
    _ = 1 := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        simp only [povmDilation_compress hM, hsum]

/-- An isometry `V : E → E × X` is `U * ancEmb x₀` for a unitary `U`. -/
theorem exists_unitary_mul_ancEmb (x₀ : X) {V : Matrix (E × X) E ℂ} (hV : Vᴴ * V = 1) :
    ∃ U ∈ Matrix.unitaryGroup (E × X) ℂ, U * ancEmb x₀ = V := by
  let j : E → E × X := fun y => (y, x₀)
  have hj : Function.Injective j := fun y y' h => by simpa [j] using h
  let col : E → EuclideanSpace ℂ (E × X) := fun y => WithLp.toLp 2 (fun a => V a y)
  have hcol : Orthonormal ℂ col := by
    rw [orthonormal_iff_ite]
    intro y y'
    have h := congrFun (congrFun hV y) y'
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    simp only [col, PiLp.inner_apply, conjTranspose_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  let v : E × X → EuclideanSpace ℂ (E × X) := Function.extend j col 0
  have hv : Orthonormal ℂ ((Set.range j).domRestrict v) := by
    have : (Set.range j).domRestrict v = col ∘ (Equiv.ofInjective j hj).symm := by
      funext ⟨_, y, rfl⟩
      simp [v, hj.extend_apply]
    rw [this]
    exact hcol.comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨(EuclideanSpace.basisFun (E × X) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (E × X) ℂ).toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  ext a y
  have hby : b (j y) = col y := by
    rw [hb _ ⟨y, rfl⟩]
    simp [v, hj.extend_apply]
  simpa [ancEmb, Matrix.mul_apply, Module.Basis.toMatrix_apply] using
    congrArg (fun w => w.ofLp a) hby

/-- **Naimark dilation.** A measurement `M` on `E` with outcomes in `X` is the compression to
`E ⊗ |x₀⟩` of a family of pairwise orthogonal star projections on `E × X`. -/
theorem exists_naimark (x₀ : X) {M : X → Matrix E E ℂ} (hM : ∀ x, (M x).PosSemidef)
    (hsum : ∑ x, M x = 1) :
    ∃ Q : X → Matrix (E × X) (E × X) ℂ, (∀ x, IsStarProjection (Q x)) ∧
      (∀ x x', x ≠ x' → Q x * Q x' = 0) ∧ ∀ x, (ancEmb x₀)ᴴ * Q x * ancEmb x₀ = M x := by
  obtain ⟨U, hU, hUV⟩ := exists_unitary_mul_ancEmb x₀ (povmDilation_isometry hM hsum)
  have h1 : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  refine ⟨fun x => Uᴴ * ancProj x * U, fun x => ⟨?_, ?_⟩, fun x x' hx => ?_, fun x => ?_⟩
  · obtain ⟨hid, -⟩ := ancProj_isStarProjection (E := E) x
    change Uᴴ * ancProj x * U * (Uᴴ * ancProj x * U) = Uᴴ * ancProj x * U
    calc Uᴴ * ancProj x * U * (Uᴴ * ancProj x * U)
        = Uᴴ * (ancProj x * (U * Uᴴ) * ancProj x) * U := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * ancProj x * U := by rw [h1, Matrix.mul_one, hid.eq]
  · obtain ⟨-, hsa⟩ := ancProj_isStarProjection (E := E) x
    change star (Uᴴ * ancProj x * U) = Uᴴ * ancProj x * U
    rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      ← star_eq_conjTranspose (ancProj x), hsa.star_eq, Matrix.mul_assoc]
  · calc Uᴴ * ancProj x * U * (Uᴴ * ancProj x' * U)
        = Uᴴ * (ancProj x * (U * Uᴴ) * ancProj x') * U := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1, Matrix.mul_one, ancProj_mul_ancProj hx, Matrix.mul_zero,
          Matrix.zero_mul]
  · rw [← povmDilation_compress hM x, ← hUV, conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end Naimark

end CatCrypt.Quantum.Naimark

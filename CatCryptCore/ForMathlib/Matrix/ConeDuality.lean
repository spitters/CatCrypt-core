/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Basic

/-!
# The trace pairing and the positive semidefinite cone of complex matrices

Facts for conic duality over the real vector space of complex matrices: every real-linear
functional is a trace pairing `A ↦ Re tr(G A)`, with `G` Hermitian on Hermitian arguments;
a Hermitian matrix whose quadratic form has nonnegative real part is positive semidefinite;
the positive semidefinite cone is closed.

## Main results

* `Matrix.exists_re_trace_conjTranspose_mul_eq`: every `ℝ`-linear functional on
  `Matrix n n ℂ` is `A ↦ Re tr(Gᴴ A)` for some `G`
* `Matrix.exists_isHermitian_re_trace_mul_eq`: on Hermitian arguments the representing
  matrix can be taken Hermitian
* `Matrix.posSemidef_of_re_dotProduct_mulVec_nonneg`: positivity from the real part of the
  quadratic form
* `Matrix.isClosed_setOf_posSemidef`: the positive semidefinite matrices form a closed set
* `Matrix.trace_mul_vecMulVec_star`: `tr(A v v†) = v† A v`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- `tr(A · v v†) = v† A v`. -/
theorem trace_mul_vecMulVec_star (A : Matrix n n ℂ) (v : n → ℂ) :
    (A * vecMulVec v (star v)).trace = star v ⬝ᵥ (A *ᵥ v) := by
  rw [trace_mul_comm, vecMulVec_mul, trace_vecMulVec, dotProduct_comm, dotProduct_mulVec]

/-- A Hermitian matrix whose quadratic form has nonnegative real part at every vector is
positive semidefinite. -/
theorem posSemidef_of_re_dotProduct_mulVec_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re) : A.PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hA, fun v => ?_⟩
  have him : (star v ⬝ᵥ (A *ᵥ v)).im = 0 :=
    Complex.conj_eq_iff_im.mp (hA.star_dotProduct_mulVec_comm v v)
  exact Complex.nonneg_iff.mpr ⟨h v, him.symm⟩

/-- The positive semidefinite complex matrices form a closed set. -/
theorem isClosed_setOf_posSemidef {m : Type*} [Finite m] :
    IsClosed {A : Matrix m m ℂ | A.PosSemidef} := by
  have := Fintype.ofFinite m
  have h : {A : Matrix m m ℂ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : m → ℂ, {A | 0 ≤ star x ⬝ᵥ A *ᵥ x} := by
    ext A
    simp [posSemidef_iff_dotProduct_mulVec, IsHermitian]
  rw [h]
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)))

/-- The real trace pairing `(G, A) ↦ Re tr(Gᴴ A)` as a real-linear map into the dual. -/
private noncomputable def reTracePairing : Matrix n n ℂ →ₗ[ℝ] Module.Dual ℝ (Matrix n n ℂ) :=
  LinearMap.mk₂ ℝ (fun G A => (Gᴴ * A).trace.re)
    (fun G₁ G₂ A => by simp [Matrix.add_mul, trace_add])
    (fun c G A => by simp [conjTranspose_smul, trace_smul])
    (fun G A₁ A₂ => by simp [Matrix.mul_add, trace_add])
    (fun c G A => by simp [trace_smul])

/-- Every real-linear functional on `Matrix n n ℂ` is a trace pairing `A ↦ Re tr(Gᴴ A)`. -/
theorem exists_re_trace_conjTranspose_mul_eq (g : Matrix n n ℂ →ₗ[ℝ] ℝ) :
    ∃ G : Matrix n n ℂ, ∀ A, g A = (Gᴴ * A).trace.re := by
  have hinj : Function.Injective (reTracePairing (n := n)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro G hG
    have hre : (Gᴴ * G).trace.re = 0 := LinearMap.congr_fun hG G
    have hnn := Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self G).trace_nonneg
    exact trace_conjTranspose_mul_self_eq_zero_iff.mp (Complex.ext hre (by simpa using hnn.2.symm))
  have hsurj : Function.Surjective (reTracePairing (n := n)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).mp hinj
  obtain ⟨G, hG⟩ := hsurj g
  exact ⟨G, fun A => by rw [← hG]; rfl⟩

/-- Every real-linear functional on `Matrix n n ℂ` agrees on Hermitian matrices with a trace
pairing `A ↦ Re tr(G A)` against a Hermitian `G`. -/
theorem exists_isHermitian_re_trace_mul_eq (g : Matrix n n ℂ →ₗ[ℝ] ℝ) :
    ∃ G : Matrix n n ℂ, G.IsHermitian ∧ ∀ A, A.IsHermitian → g A = (G * A).trace.re := by
  obtain ⟨G, hG⟩ := exists_re_trace_conjTranspose_mul_eq g
  refine ⟨(2⁻¹ : ℝ) • (G + Gᴴ), ?_, fun A hA => ?_⟩
  · simp [IsHermitian, conjTranspose_smul, add_comm]
  · have hconj : (G * A).trace.re = (Gᴴ * A).trace.re := by
      rw [← Complex.conj_re, ← Complex.star_def, ← trace_conjTranspose, conjTranspose_mul,
        hA.eq, trace_mul_comm]
    rw [hG A, Matrix.smul_mul, Matrix.add_mul, trace_smul, trace_add, Complex.real_smul,
      Complex.re_ofReal_mul, Complex.add_re, hconj]
    ring

end Matrix

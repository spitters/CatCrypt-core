/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Simultaneous orthogonal diagonalisation of real symmetric matrices

Mathlib candidates for `Mathlib/Analysis/Matrix/Spectrum.lean` (the matrix statements) and
`Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean` (polar coordinates).

Mathlib has the joint eigenspace decomposition of commuting symmetric operators
(`LinearMap.IsSymmetric.directSum_isInternal_of_commute`); the statements here are its
matrix form.

## Main results

* `Matrix.exists_orthogonal_mul_diagonal_of_commute` — two commuting real symmetric matrices
  are diagonalised by one orthogonal matrix.
* `Matrix.exists_orthogonal_diagonal_of_symm_unitary` — a complex symmetric unitary matrix is
  diagonalised by a real orthogonal matrix.
* `Real.exists_polar` — every point of the plane is `r (cos θ, sin θ)` with
  `r = √(x ^ 2 + y ^ 2)`.
-/

set_option autoImplicit false

@[expose] public section

namespace Matrix

variable {m : ℕ}

/-- The eigenvector equation of a real matrix, coordinate by coordinate. -/
theorem sum_mul_eq_of_toEuclideanLin_eq_smul {Z : Matrix (Fin m) (Fin m) ℝ}
    {v : EuclideanSpace ℝ (Fin m)} {μ : ℝ} (h : toEuclideanLin Z v = μ • v) (i : Fin m) :
    ∑ k, Z i k * v k = μ * v i := by
  have h' := congrArg (fun w => w i) h
  simpa [Matrix.mulVec, dotProduct] using h'

/-- Two commuting real symmetric matrices are diagonalised by one orthogonal matrix. -/
theorem exists_orthogonal_mul_diagonal_of_commute {X Y : Matrix (Fin m) (Fin m) ℝ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hXY : Commute X Y) :
    ∃ O ∈ Matrix.unitaryGroup (Fin m) ℝ, ∃ x y : Fin m → ℝ,
      X * O = O * diagonal x ∧ Y * O = O * diagonal y := by
  have hA := Matrix.isSymmetric_toEuclideanLin_iff.mpr hX
  have hB := Matrix.isSymmetric_toEuclideanLin_iff.mpr hY
  have hAB : Commute (toEuclideanLin X) (toEuclideanLin Y) := by
    rw [Commute, SemiconjBy, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, hXY.eq]
  classical
  have hV₀ := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  let := hV₀.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hV := DirectSum.isInternal_ne_bot_iff.mpr hV₀
  have hV' := (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB).comp
    (Subtype.val_injective (p := fun i : ℝ × ℝ => Module.End.eigenspace (toEuclideanLin X) i.2 ⊓
      Module.End.eigenspace (toEuclideanLin Y) i.1 ≠ ⊥))
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  set b := hV.subordinateOrthonormalBasis hn hV' with hb
  set idx := fun a => (hV.subordinateOrthonormalBasisIndex hn a hV').val with hidx
  have hmem := fun a => hV.subordinateOrthonormalBasis_subordinate hn a hV'
  refine ⟨(EuclideanSpace.basisFun (Fin m) ℝ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin m) ℝ).toMatrix_orthonormalBasis_mem_unitary b,
    fun a => (idx a).2, fun a => (idx a).1, ?_, ?_⟩
  · ext i a
    rw [Matrix.mul_diagonal, Matrix.mul_apply, mul_comm]
    exact sum_mul_eq_of_toEuclideanLin_eq_smul (Module.End.mem_eigenspace_iff.mp (hmem a).1) i
  · ext i a
    rw [Matrix.mul_diagonal, Matrix.mul_apply, mul_comm]
    exact sum_mul_eq_of_toEuclideanLin_eq_smul (Module.End.mem_eigenspace_iff.mp (hmem a).2) i

open Complex in
/-- A complex symmetric unitary matrix is `O * D * Oᵀ` with `O` real orthogonal and `D`
diagonal. -/
theorem exists_orthogonal_diagonal_of_symm_unitary {S : Matrix (Fin m) (Fin m) ℂ}
    (hS : Sᵀ = S) (hU : S ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    ∃ O : Matrix (Fin m) (Fin m) ℝ, Oᵀ * O = 1 ∧ ∃ d : Fin m → ℂ,
      S * O.map ofReal = O.map ofReal * diagonal d := by
  have hsym : ∀ a b, S a b = S b a := fun a b => congrFun (congrFun hS b) a
  have hX : (S.map re).IsHermitian := by
    ext i j
    simp [hsym i j]
  have hY : (S.map im).IsHermitian := by
    ext i j
    simp [hsym i j]
  have hXY : Commute (S.map re) (S.map im) := by
    rw [Commute, SemiconjBy]
    ext i j
    have h' := congrArg im (congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) i) j)
    simp only [Matrix.mul_apply, Matrix.star_apply, Complex.im_sum, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Matrix.one_apply] at h'
    simp only [Matrix.mul_apply, Matrix.map_apply]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simp only [show ∀ x, S x i = S i x from fun x => hsym x i, ← sub_eq_add_neg, neg_mul] at h'
    rw [h']
    split_ifs <;> simp
  obtain ⟨O, hO, x, y, hx, hy⟩ := exists_orthogonal_mul_diagonal_of_commute hX hY hXY
  refine ⟨O, Matrix.mem_unitaryGroup_iff'.mp hO, fun k => ⟨x k, y k⟩, ?_⟩
  ext i a
  have hx' := congrFun (congrFun hx i) a
  have hy' := congrFun (congrFun hy i) a
  rw [Matrix.mul_diagonal] at hx' hy' ⊢
  simp only [Matrix.mul_apply, Matrix.map_apply] at hx' hy' ⊢
  apply Complex.ext <;> simp [Complex.re_sum, Complex.im_sum, ← hx', ← hy']

end Matrix

namespace Real

/-- Polar coordinates of a point of the plane: `(x, y) = r (cos θ, sin θ)` with
`r = √(x ^ 2 + y ^ 2)`. -/
theorem exists_polar (x y : ℝ) :
    ∃ θ : ℝ, x = √(x ^ 2 + y ^ 2) * Real.cos θ ∧ y = √(x ^ 2 + y ^ 2) * Real.sin θ := by
  set z : ℂ := ⟨x, y⟩
  have hn : ‖z‖ = √(x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]
    ring_nf
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [← hn, Complex.norm_mul_cos_arg]
  · rw [← hn, Complex.norm_mul_sin_arg]

end Real

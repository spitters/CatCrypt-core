/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace Norm for Hermitian Matrices

This file defines the trace norm of a Hermitian matrix using eigenvalues
(via Mathlib's spectral theorem) and proves basic properties including
the Helstrom dual characterization.

## Main Definitions

* `traceNormH` — trace norm of a Hermitian matrix: `∑ i, |λᵢ|`
* `IsEffect` — a matrix `E` with `0 ≤ E ≤ I` (quantum effect / POVM element)

## Main Results

* `traceNormH_nonneg` — trace norm is non-negative
* `traceNormH_zero` — trace norm of zero is zero
* `helstrom_traceless` — Helstrom dual characterization for traceless matrices
* `effect_trace_le` — upper bound: `Re(tr(EX)) ≤ ½ ‖X‖₁` for effects and traceless X
* `exists_effect_achieves` — achievability: spectral projection attains the bound
* `traceNormH_triangle_traceless` — triangle inequality (via Helstrom)
* `exists_selfAdjoint_involution_trace_eq_traceNormH` — `‖X‖₁ = Re tr(SX)` for a
  self-adjoint involution `S`

## References

* Helstrom, "Quantum Detection and Estimation Theory" (1976)
* Wilde, *Quantum Information Theory* (Cambridge, 2017), Chapter 9
-/

@[expose] public section

open scoped Matrix ComplexOrder
open Matrix Polynomial Unitary

noncomputable section

namespace CatCrypt.Quantum

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ## Eigenvalues of Negated Matrices

Helper lemmas relating the eigenvalues of `-A` to those of `A` via the spectral theorem
and characteristic polynomial roots.
-/

/-- Spectral decomposition of `-A` using `A`'s eigenvector basis with negated eigenvalues. -/
private lemma neg_spectral (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    -A = (conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary)
    (diagonal (RCLike.ofReal ∘ (-hA.eigenvalues))) := by
  suffices h : diagonal (RCLike.ofReal ∘ (-hA.eigenvalues)) =
    -(diagonal (RCLike.ofReal ∘ hA.eigenvalues)) by
    rw [h, map_neg, ← hA.spectral_theorem]
  ext i j
  simp only [diagonal, of_apply, Function.comp, Pi.neg_apply, Matrix.neg_apply, map_neg]
  split <;> simp

/-- Characteristic polynomial of `-A` expressed via eigenvalues of `A`. -/
private lemma neg_charpoly_eq (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (-A).charpoly = ∏ i, (X - C ((-hA.eigenvalues i : ℝ) : ℂ)) := by
  conv_lhs => rw [neg_spectral A hA, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

/-- Roots of `(-A).charpoly` are negations of roots of `A.charpoly`. -/
private lemma neg_roots_charpoly (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (-A).charpoly.roots =
    Multiset.map (RCLike.ofReal ∘ fun i => -hA.eigenvalues i) Finset.univ.val := by
  rw [neg_charpoly_eq A hA, roots_prod]
  · simp [Function.comp, map_neg]
  · rw [Finset.prod_ne_zero_iff]; intro i _; exact X_sub_C_ne_zero _

/-- The multiset of eigenvalues of `-A` equals the multiset of negated eigenvalues of `A`.
    This is the key step: the eigenvector bases for `hNA` and `hA` may differ, but the
    *multisets* of eigenvalues are related by negation. -/
private lemma neg_eigenvalues_multiset (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hNA : (-A).IsHermitian) :
    Multiset.map hNA.eigenvalues Finset.univ.val =
    Multiset.map (fun i => -hA.eigenvalues i) Finset.univ.val := by
  apply Multiset.map_injective (f := (RCLike.ofReal (K := ℂ)))
  · exact RCLike.ofReal_injective
  · simp only [Multiset.map_map]
    rw [← hNA.roots_charpoly_eq_eigenvalues, neg_roots_charpoly A hA]

/-! ## Trace Norm Definition -/

/-- Trace norm of a Hermitian matrix: sum of absolute eigenvalues.
    For Hermitian `A`, `‖A‖₁ = ∑ i, |λᵢ|` where `λᵢ` are the eigenvalues. -/
def traceNormH (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- An effect (POVM element): Hermitian operator between 0 and I in Loewner order. -/
def IsEffect (E : Matrix n n ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

/-! ## Basic Properties -/

/-- Trace norm is non-negative (sum of non-negative terms). -/
theorem traceNormH_nonneg (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    0 ≤ traceNormH A hA := by
  apply Finset.sum_nonneg
  intro i _
  exact abs_nonneg _

/-- Trace norm of zero is zero. -/
theorem traceNormH_zero (h0 : (0 : Matrix n n ℂ).IsHermitian) :
    traceNormH 0 h0 = 0 := by
  simp only [traceNormH]
  apply Finset.sum_eq_zero
  intro i _
  rw [IsHermitian.eigenvalues_eq]
  simp

/-- Trace norm of negation equals trace norm: `‖-A‖₁ = ‖A‖₁`.
    The eigenvector bases for `-A` and `A` differ, so we cannot match eigenvalues
    term-by-term. Instead, we show the *multisets* of eigenvalues are related by
    negation (via characteristic polynomial roots), then `|(-λ)| = |λ|` gives
    equality of the multiset sums of absolute values. -/
theorem traceNormH_neg (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hNA : (-A).IsHermitian) :
    traceNormH (-A) hNA = traceNormH A hA := by
  simp only [traceNormH]
  simp_rw [← Finset.sum_map_val]
  have key : Multiset.map (fun i => |hNA.eigenvalues i|) Finset.univ.val =
             Multiset.map (fun i => |hA.eigenvalues i|) Finset.univ.val := by
    have h1 := congr_arg (Multiset.map (|·|)) (neg_eigenvalues_multiset A hA hNA)
    simp only [Multiset.map_map, Function.comp] at h1
    rw [h1]; simp_rw [abs_neg]
  simp only [key]

/-! ## Effects -/

omit [Fintype n] in
/-- The identity matrix is an effect. -/
theorem isEffect_one : IsEffect (1 : Matrix n n ℂ) := by
  constructor
  · exact PosSemidef.one
  · simp; exact PosSemidef.zero

omit [Fintype n] in
/-- The zero matrix is an effect. -/
theorem isEffect_zero : IsEffect (0 : Matrix n n ℂ) := by
  constructor
  · exact PosSemidef.zero
  · simp; exact PosSemidef.one

/-! ## Trace of PSD matrices -/

omit [DecidableEq n] in
/-- The trace of a PSD matrix has zero imaginary part. -/
theorem trace_im_zero_of_psd {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A.trace.im = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact (Complex.nonneg_iff.mp (hA.diag_nonneg)).2.symm

/-! ## Helstrom Helper Lemmas -/

/-- Eigenvalues of a traceless Hermitian matrix sum to zero. -/
private lemma eigenvalues_sum_zero (X : Matrix n n ℂ) (hX : X.IsHermitian)
    (htr : X.trace = 0) :
    ∑ i, hX.eigenvalues i = 0 := by
  have h := hX.trace_eq_sum_eigenvalues; rw [htr] at h
  have h2 : ((∑ i, hX.eigenvalues i : ℝ) : ℂ) = 0 := by push_cast; exact h.symm
  exact_mod_cast h2

/-- For a function summing to zero, the sum of positive parts equals half the sum of
    absolute values: `∑ max(fᵢ, 0) = ½ ∑ |fᵢ|`. -/
private lemma sum_pos_eq_half_abs_sum {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hsum : ∑ i, f i = 0) :
    ∑ i, (if 0 ≤ f i then f i else 0) = (1/2 : ℝ) * ∑ i, |f i| := by
  have h1 : ∑ i, |f i| = ∑ i, (if 0 ≤ f i then f i else 0) +
                           ∑ i, (if 0 ≤ f i then 0 else -(f i)) := by
    rw [← Finset.sum_add_distrib]; congr 1; funext i
    by_cases h : 0 ≤ f i
    · simp [h, abs_of_nonneg h]
    · push Not at h; simp [show ¬(0 ≤ f i) from not_le.mpr h, abs_of_neg h]
  have h2 : ∑ i, f i = ∑ i, (if 0 ≤ f i then f i else 0) -
                         ∑ i, (if 0 ≤ f i then 0 else -(f i)) := by
    rw [← Finset.sum_sub_distrib]; congr 1; funext i
    by_cases h : 0 ≤ f i
    · simp [h]
    · push Not at h; simp [show ¬(0 ≤ f i) from not_le.mpr h]
  rw [hsum] at h2; linarith

/-- Unitary conjugation preserves effects: if `E` is an effect and `U` is unitary,
    then `U* E U` is an effect. -/
private lemma isEffect_conj (E : Matrix n n ℂ) (hE : IsEffect E)
    (U : ↥(unitaryGroup n ℂ)) :
    IsEffect (star (U : Matrix n n ℂ) * E * (U : Matrix n n ℂ)) := by
  constructor
  · rw [star_eq_conjTranspose]; exact hE.1.conjTranspose_mul_mul_same _
  · have : 1 - star (U : Matrix n n ℂ) * E * (U : Matrix n n ℂ) =
           star (U : Matrix n n ℂ) * (1 - E) * (U : Matrix n n ℂ) := by
      rw [mul_sub, sub_mul, mul_one, UnitaryGroup.star_mul_self]
    rw [this, star_eq_conjTranspose]; exact hE.2.conjTranspose_mul_mul_same _

omit [Fintype n] in
/-- Diagonal entries of an effect have real parts in [0, 1]. -/
private lemma effect_diag_re_bounds (F : Matrix n n ℂ) (hF : IsEffect F) (i : n) :
    0 ≤ (F i i).re ∧ (F i i).re ≤ 1 := by
  refine ⟨(Complex.nonneg_iff.mp (hF.1.diag_nonneg)).1, ?_⟩
  have h : 0 ≤ ((1 - F) i i).re := (Complex.nonneg_iff.mp (hF.2.diag_nonneg)).1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at h
  linarith

/-- Express `tr(EX)` in the eigenvector basis of `X`: the trace reduces to a sum
    over diagonal entries of the conjugated effect times eigenvalues. -/
private lemma trace_EX_eq_sum (E X : Matrix n n ℂ) (hX : X.IsHermitian) :
    (E * X).trace = ∑ i, (star (hX.eigenvectorUnitary : Matrix n n ℂ) * E *
      (hX.eigenvectorUnitary : Matrix n n ℂ)) i i *
      (↑(hX.eigenvalues i) : ℂ) := by
  set U := (hX.eigenvectorUnitary : Matrix n n ℂ)
  set D := diagonal (RCLike.ofReal ∘ hX.eigenvalues : n → ℂ)
  have hX_spec : X = U * D * star U := by
    rw [hX.spectral_theorem, conjStarAlgAut_apply]
  calc (E * X).trace
      = (E * (U * D * star U)).trace := by rw [hX_spec]
    _ = ((E * U) * D * star U).trace := by
        congr 1; rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (star U * (E * U) * D).trace := by rw [trace_mul_cycle]
    _ = (star U * E * U * D).trace := by
        congr 1; rw [← Matrix.mul_assoc (star U)]
    _ = ∑ i, (star U * E * U) i i * (↑(hX.eigenvalues i) : ℂ) := by
        simp only [Matrix.trace, Matrix.diag]
        congr 1; funext i; rw [mul_diagonal]; simp [Function.comp]

/-- Unitary conjugation cancels: `U* (U D U*) U = D`. -/
private lemma unitary_conj_cancel (U : ↥(unitaryGroup n ℂ)) (D : Matrix n n ℂ) :
    star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * D * star (U : Matrix n n ℂ)) *
      (U : Matrix n n ℂ) = D := by
  have hU'U := UnitaryGroup.star_mul_self U
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      show star (↑U) * (↑U * (D * (star ↑U * ↑U))) =
        (star (↑U) * ↑U) * (D * (star (↑U) * ↑U)) from by
        rw [← Matrix.mul_assoc]]
  rw [hU'U, Matrix.mul_one, Matrix.one_mul]

/-! ## Spectral Projection -/

/-- The spectral projection onto the positive eigenspace of a Hermitian matrix:
    `E₊ = U diag(1_{λᵢ≥0}) U*` where `U` diagonalizes `X`. -/
private def spectralProjection (X : Matrix n n ℂ) (hX : X.IsHermitian) : Matrix n n ℂ :=
  let U := (hX.eigenvectorUnitary : Matrix n n ℂ)
  U * diagonal (fun i => if 0 ≤ hX.eigenvalues i then 1 else 0) * star U

/-- The spectral projection is an effect (both it and its complement are PSD). -/
private lemma spectralProjection_isEffect (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    IsEffect (spectralProjection X hX) := by
  unfold spectralProjection
  set U := hX.eigenvectorUnitary
  set d := fun i => if 0 ≤ hX.eigenvalues i then (1 : ℂ) else 0
  have hUU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff.mp U.2
  have conj_psd : ∀ A : Matrix n n ℂ, A.PosSemidef →
      ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)).PosSemidef := by
    intro A hA
    rw [show (U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ) =
      (star (U : Matrix n n ℂ))ᴴ * A * star (U : Matrix n n ℂ) from by
      simp [star_eq_conjTranspose, conjTranspose_conjTranspose]]
    exact hA.conjTranspose_mul_mul_same _
  constructor
  · exact conj_psd _ (by rw [posSemidef_diagonal_iff]; intro i; simp [d]; split_ifs <;> simp)
  · rw [show 1 - (U : Matrix n n ℂ) * diagonal d * star (U : Matrix n n ℂ) =
      (U : Matrix n n ℂ) * (1 - diagonal d) * star (U : Matrix n n ℂ) from by
      rw [mul_sub, sub_mul, mul_one, hUU]]
    have : 1 - diagonal d = diagonal (fun i => 1 - d i) := by
      ext i j; simp [diagonal, one_apply]; split_ifs <;> simp_all
    rw [this]
    exact conj_psd _ (by rw [posSemidef_diagonal_iff]; intro i; simp [d]; split_ifs <;> simp)

/-! ## Helstrom Dual Characterization -/

/-- **Upper bound**: for any effect `E` and traceless Hermitian `X`,
    `Re(tr(EX)) ≤ ½ ‖X‖₁`.

    Proof: conjugate `E` by the diagonalizing unitary of `X` to get `F = U*EU`,
    which is also an effect. Then `tr(EX) = ∑ Fᵢᵢ λᵢ` and since `0 ≤ Fᵢᵢ.re ≤ 1`,
    each term is bounded by `max(λᵢ, 0)`. The sum of positive eigenvalues equals
    `½ ‖X‖₁` by tracelessness. -/
theorem effect_trace_le (X : Matrix n n ℂ) (hX : X.IsHermitian) (htr : X.trace = 0)
    (E : Matrix n n ℂ) (hE : IsEffect E) :
    (E * X).trace.re ≤ (1/2 : ℝ) * traceNormH X hX := by
  rw [trace_EX_eq_sum E X hX]
  set F := star (hX.eigenvectorUnitary : Matrix n n ℂ) * E *
    (hX.eigenvectorUnitary : Matrix n n ℂ)
  have hF : IsEffect F := isEffect_conj E hE hX.eigenvectorUnitary
  rw [Complex.re_sum]; simp_rw [Complex.re_mul_ofReal]
  calc ∑ i, (F i i).re * hX.eigenvalues i
      ≤ ∑ i, (if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0) := by
        apply Finset.sum_le_sum; intro i _
        have ⟨hF0, hF1⟩ := effect_diag_re_bounds F hF i
        by_cases h : 0 ≤ hX.eigenvalues i
        · simp [h]; exact mul_le_of_le_one_left h hF1
        · push Not at h; simp [show ¬(0 ≤ hX.eigenvalues i) from not_le.mpr h]
          exact mul_nonpos_of_nonneg_of_nonpos hF0 (le_of_lt h)
    _ = (1/2 : ℝ) * traceNormH X hX := by
        simp only [traceNormH]
        exact sum_pos_eq_half_abs_sum _ (eigenvalues_sum_zero X hX htr)

/-- **Achievability**: the spectral projection onto the positive eigenspace achieves
    the bound `Re(tr(E₊ X)) = ½ ‖X‖₁`. -/
theorem exists_effect_achieves (X : Matrix n n ℂ) (hX : X.IsHermitian)
    (htr : X.trace = 0) :
    ∃ E : Matrix n n ℂ, IsEffect E ∧
      (E * X).trace.re = (1/2 : ℝ) * traceNormH X hX := by
  refine ⟨spectralProjection X hX, spectralProjection_isEffect X hX, ?_⟩
  rw [trace_EX_eq_sum _ _ hX]
  have hF : star (hX.eigenvectorUnitary : Matrix n n ℂ) * spectralProjection X hX *
      (hX.eigenvectorUnitary : Matrix n n ℂ) =
    diagonal (fun i => if 0 ≤ hX.eigenvalues i then (1 : ℂ) else 0) := by
    unfold spectralProjection
    exact unitary_conj_cancel hX.eigenvectorUnitary _
  rw [hF, Complex.re_sum]
  simp_rw [diagonal_apply_eq, Complex.re_mul_ofReal]
  simp_rw [show ∀ i, (if 0 ≤ hX.eigenvalues i then (1 : ℂ) else 0).re * hX.eigenvalues i =
    if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0 from by
    intro i; split_ifs <;> simp]
  simp only [traceNormH]
  exact sum_pos_eq_half_abs_sum _ (eigenvalues_sum_zero X hX htr)

/-- **Helstrom's theorem** for traceless Hermitian matrices:
    `½ ‖X‖₁ = sup {Re(tr(EX)) | 0 ≤ E ≤ I}`

    This variational characterization of trace distance is the foundation
    for the post-processing lemma at the density matrix level.

    Proved as `le_antisymm` using `effect_trace_le` (upper bound)
    and `exists_effect_achieves` (achievability via spectral projection). -/
theorem helstrom_traceless (X : Matrix n n ℂ) (hX : X.IsHermitian)
    (htr : X.trace = 0) :
    (1/2 : ℝ) * traceNormH X hX =
    sSup {r : ℝ | ∃ E : Matrix n n ℂ, IsEffect E ∧ r = (E * X).trace.re} := by
  apply le_antisymm
  · obtain ⟨Ep, hEp, hachieve⟩ := exists_effect_achieves X hX htr
    rw [← hachieve]
    apply le_csSup
    · exact ⟨(1/2 : ℝ) * traceNormH X hX,
        fun r ⟨E, hE, hr⟩ => hr ▸ effect_trace_le X hX htr E hE⟩
    · exact ⟨Ep, hEp, rfl⟩
  · apply csSup_le
    · exact ⟨_, ⟨0, isEffect_zero, rfl⟩⟩
    · rintro _ ⟨E, hE, rfl⟩
      exact effect_trace_le X hX htr E hE

/-- Triangle inequality for trace norm of traceless Hermitian matrices.

    Derived from Helstrom: for traceless A, B:
    `½‖A+B‖₁ = Re(tr(E₊(A+B))) = Re(tr(E₊A)) + Re(tr(E₊B)) ≤ ½‖A‖₁ + ½‖B‖₁`
    where `E₊` is the spectral projection achieving `½‖A+B‖₁`. -/
theorem traceNormH_triangle_traceless (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A + B).IsHermitian)
    (htrA : A.trace = 0) (htrB : B.trace = 0) :
    traceNormH (A + B) hAB ≤ traceNormH A hA + traceNormH B hB := by
  obtain ⟨E, hE, hachieve⟩ := exists_effect_achieves (A + B) hAB (by simp [htrA, htrB])
  have hlin : (E * (A + B)).trace.re = (E * A).trace.re + (E * B).trace.re := by
    simp [mul_add, Complex.add_re]
  have hbound : (E * A).trace.re + (E * B).trace.re ≤
      (1/2 : ℝ) * traceNormH A hA + (1/2 : ℝ) * traceNormH B hB :=
    add_le_add (effect_trace_le A hA htrA E hE) (effect_trace_le B hB htrB E hE)
  have h2 : (1/2 : ℝ) * traceNormH (A + B) hAB ≤
      (1/2 : ℝ) * (traceNormH A hA + traceNormH B hB) := by
    rw [hachieve] at hlin; linarith
  linarith

/-! ## Sign Matrix of a Hermitian Matrix -/

/-- The trace norm of a Hermitian matrix `X` is attained by a self-adjoint
    involution: there is `S` with `S† = S`, `S² = 1` and
    `Re tr(SX) = ‖X‖₁`. The witness is `S = U diag(sgn λᵢ) U†` for the
    eigenvector unitary `U` of `X`, with `sgn λ = 1` for `λ ≥ 0` and `-1`
    otherwise. -/
theorem exists_selfAdjoint_involution_trace_eq_traceNormH
    (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    ∃ S : Matrix n n ℂ, Sᴴ = S ∧ S * S = 1 ∧
      (S * X).trace.re = traceNormH X hX := by
  set U : Matrix n n ℂ := (hX.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hX.eigenvectorUnitary
  let σ : n → ℂ := fun i => if 0 ≤ hX.eigenvalues i then 1 else -1
  have hσ : diagonal σ * diagonal σ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; simp only [σ]; split_ifs <;> simp
  have hσs : star σ = σ := by
    funext i; simp only [σ, Pi.star_apply]; split_ifs <;> simp
  refine ⟨U * diagonal σ * star U, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul, ← Matrix.star_eq_conjTranspose (star U),
      star_star, diagonal_conjTranspose, hσs, mul_assoc]
    rfl
  · calc U * diagonal σ * star U * (U * diagonal σ * star U)
        = U * (diagonal σ * (star U * U) * diagonal σ) * star U := by
          simp only [mul_assoc]
      _ = 1 := by rw [hUU, mul_one, hσ, mul_one, hUU']
  · conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    have hmid : U * diagonal σ * star U *
        (U * diagonal (RCLike.ofReal ∘ hX.eigenvalues) * star U) =
        U * (diagonal σ * diagonal (RCLike.ofReal ∘ hX.eigenvalues)) * star U := by
      calc _ = U * diagonal σ * (star U * U) *
            diagonal (RCLike.ofReal ∘ hX.eigenvalues) * star U := by
              simp only [mul_assoc]
        _ = _ := by rw [hUU, mul_one, mul_assoc U]
    rw [hmid, trace_mul_cycle, hUU, one_mul, diagonal_mul_diagonal, trace_diagonal,
      Complex.re_sum]
    unfold traceNormH
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [σ, Function.comp]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (not_le.mp h)]

/-! ## Trace Distance for Density Matrices -/

/-- Trace distance between density matrices:
    `traceDist ρ σ = ½ ‖ρ - σ‖₁`

    This is a proper metric on the space of density matrices.
    The factor ½ normalizes it to the range [0, 1]. -/
def traceDist {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (_hρ : ρ.PosSemidef) (_hσ : σ.PosSemidef)
    (h_herm : (ρ - σ).IsHermitian) : ℝ :=
  (1/2 : ℝ) * traceNormH (ρ - σ) h_herm

end CatCrypt.Quantum

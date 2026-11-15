/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.TraceNorm

@[expose] public section

set_option autoImplicit false

/-!
# The Helstrom bound for two states with arbitrary priors

For density matrices `ρ`, `σ` given with prior probabilities `p` and `1 - p`, the best
probability of guessing which one was prepared, over all two-outcome measurements
`{E, 1 - E}`, is `1/2 + 1/2 ‖p ρ - (1 - p) σ‖₁`. The bound comes from the variational
formula for the trace norm of a Hermitian matrix of arbitrary trace:
`max {Re tr(E X) | 0 ≤ E ≤ 1} = (Re tr X + ‖X‖₁) / 2`, attained by the projection onto
the non-negative eigenspace of `X`.

## Main definitions

* `succProb p ρ σ E` — the success probability `p tr(E ρ) + (1 - p) tr((1 - E) σ)`.

## Main results

* `effect_trace_le_half_trace_add` — `Re tr(E X) ≤ (Re tr X + ‖X‖₁) / 2` for an effect `E`
  and a Hermitian `X`.
* `exists_effect_trace_eq_half_trace_add` — the bound is attained by an effect.
* `isGreatest_effect_trace` — `(Re tr X + ‖X‖₁) / 2` is the maximum of `Re tr(E X)` over
  effects.
* `helstrom` — for density matrices `ρ`, `σ` and `p ∈ [0, 1]`, the maximum of
  `succProb p ρ σ E` over effects is `1/2 + 1/2 ‖p ρ - (1 - p) σ‖₁`.

## References

* Helstrom, *Quantum Detection and Estimation Theory* (1976)
* Watrous, *The Theory of Quantum Information* (Cambridge, 2018), Theorem 3.4
-/

open scoped Matrix ComplexOrder
open Matrix

noncomputable section

namespace CatCrypt.Quantum.HelstromPriors

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Unitary conjugation preserves effects. -/
theorem isEffect_star_mul_mul {E : Matrix n n ℂ} (hE : IsEffect E)
    (U : ↥(unitaryGroup n ℂ)) :
    IsEffect (star (U : Matrix n n ℂ) * E * (U : Matrix n n ℂ)) := by
  constructor
  · rw [star_eq_conjTranspose]; exact hE.1.conjTranspose_mul_mul_same _
  · have : 1 - star (U : Matrix n n ℂ) * E * (U : Matrix n n ℂ) =
        star (U : Matrix n n ℂ) * (1 - E) * (U : Matrix n n ℂ) := by
      rw [mul_sub, sub_mul, mul_one, UnitaryGroup.star_mul_self]
    rw [this, star_eq_conjTranspose]; exact hE.2.conjTranspose_mul_mul_same _

omit [Fintype n] in
/-- The diagonal entries of an effect have real parts in `[0, 1]`. -/
theorem isEffect_diag_re_mem_Icc {F : Matrix n n ℂ} (hF : IsEffect F) (i : n) :
    0 ≤ (F i i).re ∧ (F i i).re ≤ 1 := by
  refine ⟨(Complex.nonneg_iff.mp hF.1.diag_nonneg).1, ?_⟩
  have h : 0 ≤ ((1 - F) i i).re := (Complex.nonneg_iff.mp hF.2.diag_nonneg).1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at h
  linarith

/-- `tr(E X)` in the eigenbasis of a Hermitian `X`. -/
theorem trace_mul_eq_sum_eigenvalues (E X : Matrix n n ℂ) (hX : X.IsHermitian) :
    (E * X).trace = ∑ i, (star (hX.eigenvectorUnitary : Matrix n n ℂ) * E *
      (hX.eigenvectorUnitary : Matrix n n ℂ)) i i * (↑(hX.eigenvalues i) : ℂ) := by
  set U := (hX.eigenvectorUnitary : Matrix n n ℂ)
  set D := diagonal (RCLike.ofReal ∘ hX.eigenvalues : n → ℂ) with hD
  have hX_spec : X = U * D * star U := by
    have h := hX.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  calc (E * X).trace
      = ((E * U) * D * star U).trace := by
        rw [hX_spec]; simp only [Matrix.mul_assoc]
    _ = (star U * (E * U) * D).trace := by
        rw [trace_mul_cycle]
    _ = ∑ i, (star U * E * U) i i * (↑(hX.eigenvalues i) : ℂ) := by
        rw [← Matrix.mul_assoc (star U)]
        simp only [D, Matrix.trace, Matrix.diag, mul_diagonal, Function.comp_apply]
        rfl

/-- The real part of the trace of a Hermitian matrix is the sum of its eigenvalues. -/
theorem trace_re_eq_sum_eigenvalues (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    X.trace.re = ∑ i, hX.eigenvalues i := by
  rw [hX.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp

/-- `max(f, 0)` summed is `(∑ f + ∑ |f|) / 2`. -/
theorem sum_posPart_eq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∑ i, (if 0 ≤ f i then f i else 0) = (∑ i, f i + ∑ i, |f i|) / 2 := by
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [abs_of_nonneg h]; ring
  · rw [abs_of_neg (not_le.mp h)]; ring

/-- **Upper bound**: for an effect `E` and a Hermitian `X`,
`Re tr(E X) ≤ (Re tr X + ‖X‖₁) / 2`. -/
theorem effect_trace_le_half_trace_add (X : Matrix n n ℂ) (hX : X.IsHermitian)
    (E : Matrix n n ℂ) (hE : IsEffect E) :
    (E * X).trace.re ≤ (X.trace.re + traceNormH X hX) / 2 := by
  rw [trace_mul_eq_sum_eigenvalues E X hX]
  set F := star (hX.eigenvectorUnitary : Matrix n n ℂ) * E *
    (hX.eigenvectorUnitary : Matrix n n ℂ)
  have hF : IsEffect F := isEffect_star_mul_mul hE hX.eigenvectorUnitary
  rw [Complex.re_sum]
  simp_rw [Complex.re_mul_ofReal]
  calc ∑ i, (F i i).re * hX.eigenvalues i
      ≤ ∑ i, (if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        obtain ⟨hF0, hF1⟩ := isEffect_diag_re_mem_Icc hF i
        split_ifs with h
        · exact mul_le_of_le_one_left h hF1
        · exact mul_nonpos_of_nonneg_of_nonpos hF0 (le_of_lt (not_le.mp h))
    _ = (X.trace.re + traceNormH X hX) / 2 := by
        rw [sum_posPart_eq, trace_re_eq_sum_eigenvalues X hX, traceNormH]

/-- The projection onto the non-negative eigenspace of a Hermitian matrix. -/
def posProj (X : Matrix n n ℂ) (hX : X.IsHermitian) : Matrix n n ℂ :=
  (hX.eigenvectorUnitary : Matrix n n ℂ) *
    diagonal (fun i => if 0 ≤ hX.eigenvalues i then (1 : ℂ) else 0) *
    star (hX.eigenvectorUnitary : Matrix n n ℂ)

/-- The projection onto the non-negative eigenspace is an effect. -/
theorem isEffect_posProj (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    IsEffect (posProj X hX) := by
  set U := hX.eigenvectorUnitary
  have hUU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff.mp U.2
  have conj_psd : ∀ A : Matrix n n ℂ, A.PosSemidef →
      ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)).PosSemidef := by
    intro A hA
    have := hA.conjTranspose_mul_mul_same (star (U : Matrix n n ℂ))
    rwa [← star_eq_conjTranspose, star_star] at this
  constructor
  · exact conj_psd _ (by
      rw [posSemidef_diagonal_iff]; intro i; split_ifs <;> simp)
  · have h1 : 1 - posProj X hX = (U : Matrix n n ℂ) *
        diagonal (fun i => 1 - if 0 ≤ hX.eigenvalues i then (1 : ℂ) else 0) *
        star (U : Matrix n n ℂ) := by
      rw [posProj, ← diagonal_one, ← diagonal_sub, diagonal_one, mul_sub, sub_mul, mul_one,
        hUU]
    rw [h1]
    exact conj_psd _ (by
      rw [posSemidef_diagonal_iff]; intro i; split_ifs <;> simp)

/-- **Achievability**: the projection onto the non-negative eigenspace attains
`Re tr(E X) = (Re tr X + ‖X‖₁) / 2`. -/
theorem exists_effect_trace_eq_half_trace_add (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    ∃ E : Matrix n n ℂ, IsEffect E ∧
      (E * X).trace.re = (X.trace.re + traceNormH X hX) / 2 := by
  refine ⟨posProj X hX, isEffect_posProj X hX, ?_⟩
  rw [trace_mul_eq_sum_eigenvalues _ _ hX]
  have hF : star (hX.eigenvectorUnitary : Matrix n n ℂ) * posProj X hX *
      (hX.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => if 0 ≤ hX.eigenvalues i then (1 : ℂ) else 0) := by
    have hU := UnitaryGroup.star_mul_self hX.eigenvectorUnitary
    simp only [posProj, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [hF, Complex.re_sum, trace_re_eq_sum_eigenvalues X hX, traceNormH, ← sum_posPart_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagonal_apply_eq, Complex.re_mul_ofReal]
  split_ifs <;> simp

/-- **Variational formula**: `(Re tr X + ‖X‖₁) / 2` is the maximum of `Re tr(E X)` over
effects `0 ≤ E ≤ 1`. -/
theorem isGreatest_effect_trace (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    IsGreatest {r : ℝ | ∃ E : Matrix n n ℂ, IsEffect E ∧ r = (E * X).trace.re}
      ((X.trace.re + traceNormH X hX) / 2) := by
  obtain ⟨E, hE, hEq⟩ := exists_effect_trace_eq_half_trace_add X hX
  exact ⟨⟨E, hE, hEq.symm⟩, fun _ ⟨F, hF, hr⟩ =>
    hr ▸ effect_trace_le_half_trace_add X hX F hF⟩

/-- The success probability of guessing between `ρ` (prior `p`) and `σ` (prior `1 - p`)
with the measurement `{E, 1 - E}`, answering `ρ` on outcome `E`. -/
def succProb (p : ℝ) (ρ σ E : Matrix n n ℂ) : ℝ :=
  p * (E * ρ).trace.re + (1 - p) * ((1 - E) * σ).trace.re

omit [Fintype n] [DecidableEq n] in
/-- The weighted difference `p ρ - (1 - p) σ` of two Hermitian matrices is Hermitian. -/
theorem isHermitian_weightedDiff (p : ℝ) {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) : ((p : ℂ) • ρ - ((1 - p : ℝ) : ℂ) • σ).IsHermitian := by
  refine IsHermitian.sub ?_ ?_
  · rw [IsHermitian, conjTranspose_smul, hρ.eq, Complex.star_def, Complex.conj_ofReal]
  · rw [IsHermitian, conjTranspose_smul, hσ.eq, Complex.star_def, Complex.conj_ofReal]

/-- The success probability is `(1 - p) tr σ + Re tr(E (p ρ - (1 - p) σ))`. -/
theorem succProb_eq (p : ℝ) (ρ σ E : Matrix n n ℂ) :
    succProb p ρ σ E =
      (1 - p) * σ.trace.re + (E * ((p : ℂ) • ρ - ((1 - p : ℝ) : ℂ) • σ)).trace.re := by
  simp only [succProb, Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mul, Matrix.one_mul,
    trace_sub, trace_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul]
  ring

/-- **Helstrom's theorem with arbitrary priors.** For density matrices `ρ`, `σ` and a
prior `p ∈ [0, 1]`, the maximum over effects `0 ≤ E ≤ 1` of the success probability
`p tr(E ρ) + (1 - p) tr((1 - E) σ)` is `1/2 + 1/2 ‖p ρ - (1 - p) σ‖₁`. -/
theorem helstrom (p : ℝ) {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    IsGreatest {r : ℝ | ∃ E : Matrix n n ℂ, IsEffect E ∧ r = succProb p ρ σ E}
      (1 / 2 + 1 / 2 * traceNormH ((p : ℂ) • ρ - ((1 - p : ℝ) : ℂ) • σ)
        (isHermitian_weightedDiff p hρ.isHermitian hσ.isHermitian)) := by
  set X := (p : ℂ) • ρ - ((1 - p : ℝ) : ℂ) • σ
  have hX := isHermitian_weightedDiff p hρ.isHermitian hσ.isHermitian
  have htrX : X.trace.re = 2 * p - 1 := by
    simp only [X, trace_sub, trace_smul, hρ1, hσ1, smul_eq_mul, mul_one, Complex.sub_re,
      Complex.ofReal_re]
    ring
  have key : ∀ E, succProb p ρ σ E = (1 - p) + (E * X).trace.re := by
    intro E
    rw [succProb_eq, hσ1, Complex.one_re, mul_one]
  obtain ⟨hmem, hub⟩ := isGreatest_effect_trace X hX
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hE, hEq⟩ := hmem
    refine ⟨E, hE, ?_⟩
    rw [key, ← hEq, htrX]
    ring
  · rintro _ ⟨E, hE, rfl⟩
    have := hub ⟨E, hE, rfl⟩
    rw [key]
    rw [htrX] at this
    linarith

end CatCrypt.Quantum.HelstromPriors

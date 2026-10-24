/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Products of probability mass functions and the bridge to `Measure.pi`

This file defines the joint distribution of `n` independent draws as a probability mass
function on `Fin n → α`, obtained by binding the draws one after the other, and relates it
to the measure-theoretic product.

## Main definitions

* `PMF.piFin p`: the distribution of `(X₀, …, X_{n-1})` where `Xᵢ ∼ p i` are drawn
  independently, defined by successive `PMF.bind`.

## Main results

* `PMF.piFin_apply`: the mass of a tuple is the product of the masses of its coordinates.
* `PMF.toMeasure_piFin`: for a finite type with the discrete σ-algebra, the measure of
  `PMF.piFin p` is `Measure.pi (fun i ↦ (p i).toMeasure)`.
* `PMF.iIndepFun_piFin`: the coordinate random variables are mutually independent
  (`ProbabilityTheory.iIndepFun`) under `(PMF.piFin p).toMeasure`.
* `PMF.integral_comp_eval_piFin`: the expectation of a function of one coordinate.
* `PMF.one_sub_add_mul_exp_le`: Hoeffding's lemma for a Bernoulli variable,
  `1 - q + q eˡ ≤ exp (l q + l² / 8)`, obtained from Mathlib's Hoeffding lemma
  `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace PMF

variable {α : Type*}

/-- The joint distribution of `n` independent draws `Xᵢ ∼ p i`, built by binding the draws
in order: draw `X₀ ∼ p 0`, then the remaining `n - 1` draws, and return `Fin.cons X₀ rest`. -/
noncomputable def piFin : {n : ℕ} → (Fin n → PMF α) → PMF (Fin n → α)
  | 0, _ => PMF.pure Fin.elim0
  | _ + 1, p => (p 0).bind fun a => (piFin (Fin.tail p)).bind fun v => PMF.pure (Fin.cons a v)

/-- The mass of a tuple under `piFin p` is the product of the masses of its coordinates. -/
theorem piFin_apply : ∀ {n : ℕ} (p : Fin n → PMF α) (v : Fin n → α),
    piFin p v = ∏ i, p i (v i)
  | 0, p, v => by
    simp [piFin, PMF.pure_apply, Subsingleton.elim v Fin.elim0]
  | n + 1, p, v => by
    classical
    rw [piFin, PMF.bind_apply, Fin.prod_univ_succ, tsum_eq_single (v 0)]
    · rw [PMF.bind_apply, tsum_eq_single (Fin.tail v), piFin_apply, PMF.pure_apply,
        ite_eq_left (Fin.cons_self_tail v).symm, mul_one]
      · rfl
      · intro w hw
        rw [PMF.pure_apply, ite_eq_right, mul_zero]
        intro h
        exact hw ((congrArg Fin.tail h).trans (Fin.tail_cons _ _)).symm
    · intro a ha
      rw [PMF.bind_apply, ENNReal.tsum_eq_zero.2, mul_zero]
      intro w
      rw [PMF.pure_apply, ite_eq_right, mul_zero]
      intro h
      exact ha ((congrFun h 0).trans (Fin.cons_zero _ _)).symm

section Measure

variable [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- **Bridge to `Measure.pi`.** The measure of the product mass function is the product
measure of the coordinate measures. -/
theorem toMeasure_piFin {n : ℕ} (p : Fin n → PMF α) :
    (piFin p).toMeasure = Measure.pi (fun i => (p i).toMeasure) := by
  classical
  symm
  refine Measure.pi_eq fun s _ => ?_
  rw [toMeasure_apply_fintype]
  rw [Finset.prod_congr rfl fun i _ => toMeasure_apply_fintype (p i) (s i), Fintype.prod_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : v ∈ Set.pi Set.univ s
  · rw [Set.indicator_of_mem hv, piFin_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Set.indicator_of_mem (hv i (Set.mem_univ i))]
  · rw [Set.indicator_of_notMem hv]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hv
    obtain ⟨i, hi⟩ := hv
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

/-- The coordinates of `piFin p` are mutually independent: for any real functions `f i`, the
random variables `v ↦ f i (v i)` are `iIndepFun` under `(piFin p).toMeasure`. -/
theorem iIndepFun_piFin {n : ℕ} (p : Fin n → PMF α) (f : Fin n → α → ℝ) :
    iIndepFun (fun i (v : Fin n → α) => f i (v i)) (piFin p).toMeasure := by
  rw [toMeasure_piFin]
  exact iIndepFun_pi (fun i => (measurable_of_countable (f i)).aemeasurable)

/-- The expectation of a function of the `i`-th coordinate under `piFin p` is its
expectation under `p i`, written as a finite sum. -/
theorem integral_comp_eval_piFin {n : ℕ} (p : Fin n → PMF α) (g : α → ℝ) (i : Fin n) :
    ∫ v, g (v i) ∂(piFin p).toMeasure = ∑ a, (p i a).toReal * g a := by
  rw [toMeasure_piFin, ← integral_map (measurable_pi_apply i).aemeasurable
    (measurable_of_countable g).aestronglyMeasurable,
    (measurePreserving_eval (fun i => (p i).toMeasure) i).map_eq, integral_eq_sum]
  rfl

end Measure

/-- The Bernoulli distribution on `Bool` with success probability `q ∈ [0, 1]`, with the
parameter given as a real number. (`PMF.bernoulli` is deprecated in Mathlib.) -/
noncomputable def coin (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then q else 1 - q)) (by
    rw [Fintype.sum_bool, ite_eq_left rfl, ite_eq_right Bool.false_ne_true,
      ← ENNReal.ofReal_add hq0 (sub_nonneg.2 hq1)]
    simp)

@[simp] theorem coin_apply (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) :
    coin q hq0 hq1 b = ENNReal.ofReal (if b then q else 1 - q) := rfl

theorem coin_apply_toReal (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) :
    (coin q hq0 hq1 b).toReal = if b then q else 1 - q := by
  cases b <;> simp [hq0, hq1]

/-- **Hoeffding's lemma for a Bernoulli variable**: for `0 ≤ q ≤ 1` and every real `l`,
`1 - q + q eˡ ≤ exp (l q + l² / 8)`. Proved by applying Mathlib's Hoeffding lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` to the indicator of `true` under
`(PMF.coin q _ _).toMeasure`. -/
theorem one_sub_add_mul_exp_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (l : ℝ) :
    1 - q + q * Real.exp l ≤ Real.exp (l * q + l ^ 2 / 8) := by
  set μ := (coin q hq0 hq1).toMeasure
  set X : Bool → ℝ := fun b => if b then 1 else 0
  have hX : μ[X] = q := by
    simp [μ, X, integral_eq_sum, hq0]
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X) (a := 0) (b := 1)
    (measurable_of_countable X).aemeasurable
    (ae_of_all _ fun b => by cases b <;> simp [X])).mgf_le l
  rw [hX] at h
  have hmgf : mgf (fun b => X b - q) μ l
      = (1 - q) * Real.exp (-(l * q)) + q * Real.exp (l * (1 - q)) := by
    simp [mgf, μ, X, integral_eq_sum, hq0, hq1]
    ring_nf
  rw [hmgf] at h
  have hc : (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by
    norm_num
  rw [hc] at h
  have e1 : Real.exp (l * q + l ^ 2 / 8) = Real.exp (l * q) * Real.exp (1 / 4 * l ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : 1 - q + q * Real.exp l = Real.exp (l * q) *
      ((1 - q) * Real.exp (-(l * q)) + q * Real.exp (l * (1 - q))) := by
    rw [mul_add, ← mul_assoc, mul_comm (Real.exp _) (1 - q), mul_assoc, ← Real.exp_add,
      mul_left_comm, ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero]
    ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end PMF

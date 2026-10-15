/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PMFPi
public import CatCryptCore.Prob.SDistr

/-!
# Concentration bounds: Chernoff-Hoeffding

This file proves the Chernoff-Hoeffding bound for sums of independent random variables with
values in `[0, 1]`, for distributions given as Mathlib `PMF`s and as CatCrypt sub-distributions
`SDistr α = PMF (Option α)`.

Independence is not an abstract hypothesis: the `n` draws are combined into the joint
distribution `PMF.piFin p : PMF (Fin n → α)` obtained by binding them one after the other
(`CatCryptCore/ForMathlib/PMFPi.lean`), respectively `SDistr.drawN d` built with the `SDistr`
monad.

## Method

The bounds are obtained from Mathlib's measure-theoretic Hoeffding inequality
`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` and Hoeffding's lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, through the bridge
`PMF.toMeasure_piFin : (PMF.piFin p).toMeasure = Measure.pi (fun i ↦ (p i).toMeasure)`
and the independence statement `PMF.iIndepFun_piFin` derived from it.

## Main results

* `hoeffding_piFin_upper`, `hoeffding_piFin_lower`: for `fᵢ : α → [0, 1]` and `S = ∑ᵢ fᵢ(Xᵢ)`,
  `Pr[S - E S ≥ n t] ≤ exp (-2 n t²)` and `Pr[E S - S ≥ n t] ≤ exp (-2 n t²)`.
* `chernoff_coin_upper`, `chernoff_coin_lower`: the same for `n` independent Bernoulli(`q`)
  trials, with `S` the number of successes and `E S = n q`.
* `SDistr.hoeffding_drawN_upper`, `SDistr.hoeffding_drawN_lower`: the same for `n`
  independent lossless sub-distributions.

## References

* W. Hoeffding, *Probability inequalities for sums of bounded random variables*,
  J. Amer. Statist. Assoc. 58 (1963), Theorem 1.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CatCrypt.Prob

variable {α : Type*} [Fintype α]

/-- The expectation `∑ₐ p(a) f(a)` of a real function under a distribution on a finite type. -/
noncomputable def expect (p : PMF α) (f : α → ℝ) : ℝ := ∑ a, (p a).toReal * f a

/-- The Hoeffding constant `((1 - 0) / 2)² = 1 / 4` of a variable with values in an interval
of length one. -/
private theorem nnnorm_one_div_two_sq :
    ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
  ext; simp; norm_num

private theorem nnnorm_neg_div_two_sq :
    ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
  ext; simp; norm_num

/-- Core tail bound: if the coordinate variables `v ↦ X i (v i)` are `1/4`-sub-Gaussian under
`(PMF.piFin p).toMeasure`, then `Pr[∑ᵢ X i (vᵢ) ≥ n t] ≤ exp (-2 n t²)`. Obtained from
`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` and `PMF.iIndepFun_piFin`. -/
private theorem tail_of_subgaussian [MeasurableSpace α] [DiscreteMeasurableSpace α] {n : ℕ}
    (p : Fin n → PMF α) (X : Fin n → α → ℝ)
    (hX : ∀ i, HasSubgaussianMGF (fun v : Fin n → α => X i (v i)) (1 / 4)
      (PMF.piFin p).toMeasure)
    {t : ℝ} (ht : 0 ≤ t) :
    (PMF.piFin p).toOuterMeasure {v | (n : ℝ) * t ≤ ∑ i, X i (v i)}
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (PMF.iIndepFun_piFin p X) (s := Finset.univ)
    (fun i _ => hX i) (ε := n * t) (by positivity)
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure, ← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- **Chernoff-Hoeffding bound, upper tail.** Let `X₀, …, X_{n-1}` be drawn independently,
`Xᵢ ∼ p i`, jointly distributed as `PMF.piFin p`, and let `fᵢ : α → [0, 1]`. For `t ≥ 0`,
`Pr[∑ᵢ fᵢ(Xᵢ) - ∑ᵢ E[fᵢ(Xᵢ)] ≥ n t] ≤ exp (-2 n t²)`.

Proved from Mathlib's Hoeffding inequality `measure_sum_ge_le_of_iIndepFun` and Hoeffding's lemma
`hasSubgaussianMGF_of_mem_Icc`, through the bridge `PMF.toMeasure_piFin`. -/
theorem hoeffding_piFin_upper {n : ℕ} (p : Fin n → PMF α) (f : Fin n → α → ℝ)
    (hf : ∀ i a, f i a ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    (PMF.piFin p).toOuterMeasure
        {v | (n : ℝ) * t ≤ ∑ i, f i (v i) - ∑ i, expect (p i) (f i)}
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  let : MeasurableSpace α := ⊤
  have : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  have h := tail_of_subgaussian p (fun i a => f i a - expect (p i) (f i)) (fun i => by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := (PMF.piFin p).toMeasure)
      (X := fun v : Fin n → α => f i (v i)) (a := 0) (b := 1)
      (measurable_of_countable _).aemeasurable (ae_of_all _ fun v => hf i (v i))
    rwa [PMF.integral_comp_eval_piFin, nnnorm_one_div_two_sq] at h) ht
  simpa only [Finset.sum_sub_distrib] using h

/-- **Chernoff-Hoeffding bound, lower tail.** Under the hypotheses of `hoeffding_piFin_upper`,
`Pr[∑ᵢ E[fᵢ(Xᵢ)] - ∑ᵢ fᵢ(Xᵢ) ≥ n t] ≤ exp (-2 n t²)`.

Proved from Mathlib's Hoeffding inequality `measure_sum_ge_le_of_iIndepFun` and Hoeffding's lemma
`hasSubgaussianMGF_of_mem_Icc` applied to `-fᵢ`, through the bridge `PMF.toMeasure_piFin`. -/
theorem hoeffding_piFin_lower {n : ℕ} (p : Fin n → PMF α) (f : Fin n → α → ℝ)
    (hf : ∀ i a, f i a ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    (PMF.piFin p).toOuterMeasure
        {v | (n : ℝ) * t ≤ ∑ i, expect (p i) (f i) - ∑ i, f i (v i)}
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  let : MeasurableSpace α := ⊤
  have : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  have h := tail_of_subgaussian p (fun i a => expect (p i) (f i) - f i a) (fun i => by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := (PMF.piFin p).toMeasure)
      (X := fun v : Fin n → α => -f i (v i)) (a := -1) (b := 0)
      (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun v => ⟨by linarith [(hf i (v i)).2], by linarith [(hf i (v i)).1]⟩)
    rw [PMF.integral_comp_eval_piFin p (fun a => -f i a), nnnorm_neg_div_two_sq] at h
    refine h.congr (ae_of_all _ fun v => ?_)
    simp only [expect, mul_neg, Finset.sum_neg_distrib]
    ring) ht
  simpa only [Finset.sum_sub_distrib] using h

/-- The Hoeffding bounds with a common mean: if `E[fᵢ(Xᵢ)] = m` for every `i`, then
`Pr[∑ᵢ fᵢ(Xᵢ) - n m ≥ n t] ≤ exp (-2 n t²)` and `Pr[n m - ∑ᵢ fᵢ(Xᵢ) ≥ n t] ≤ exp (-2 n t²)`. -/
theorem hoeffding_piFin_of_expect_eq {n : ℕ} (p : Fin n → PMF α) (f : Fin n → α → ℝ)
    (hf : ∀ i a, f i a ∈ Set.Icc (0 : ℝ) 1) {m : ℝ} (hm : ∀ i, expect (p i) (f i) = m)
    {t : ℝ} (ht : 0 ≤ t) :
    (PMF.piFin p).toOuterMeasure {v | (n : ℝ) * t ≤ ∑ i, f i (v i) - n * m}
        ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) ∧
      (PMF.piFin p).toOuterMeasure {v | (n : ℝ) * t ≤ n * m - ∑ i, f i (v i)}
        ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  have hsum : ∑ i, expect (p i) (f i) = n * m := by simp [hm]
  exact ⟨hsum ▸ hoeffding_piFin_upper p f hf ht, hsum ▸ hoeffding_piFin_lower p f hf ht⟩

/-! ### Bernoulli trials -/

/-- The number of successes of a tuple of Bernoulli outcomes. -/
def numTrue {n : ℕ} (v : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => v i = true).card

private theorem sum_ite_eq_numTrue {n : ℕ} (v : Fin n → Bool) :
    ∑ i, (if v i = true then (1 : ℝ) else 0) = numTrue v := by
  simp [numTrue, Finset.sum_boole]

private theorem expect_coin (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    expect (PMF.coin q hq0 hq1) (fun b => if b = true then (1 : ℝ) else 0) = q := by
  simp [expect, hq0]

/-- **Chernoff-Hoeffding bound for Bernoulli trials, upper tail.** For `n` independent
Bernoulli(`q`) trials with `0 ≤ q ≤ 1`, distributed as `PMF.piFin (fun _ ↦ PMF.coin q _ _)`,
and `t ≥ 0`: `Pr[#successes - n q ≥ n t] ≤ exp (-2 n t²)`.

Specialisation of `hoeffding_piFin_upper` (Mathlib's Hoeffding inequality through the bridge). -/
theorem chernoff_coin_upper {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (PMF.piFin fun _ : Fin n => PMF.coin q hq0 hq1).toOuterMeasure
        {v | (n : ℝ) * t ≤ numTrue v - n * q}
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  have h := (hoeffding_piFin_of_expect_eq (fun _ : Fin n => PMF.coin q hq0 hq1)
    (fun _ b => if b = true then (1 : ℝ) else 0) (fun _ b => by cases b <;> simp)
    (fun _ => expect_coin q hq0 hq1) ht).1
  simpa only [sum_ite_eq_numTrue] using h

/-- **Chernoff-Hoeffding bound for Bernoulli trials, lower tail.** Under the hypotheses of
`chernoff_coin_upper`: `Pr[n q - #successes ≥ n t] ≤ exp (-2 n t²)`.

Specialisation of `hoeffding_piFin_lower` (Mathlib's Hoeffding inequality through the bridge). -/
theorem chernoff_coin_lower {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (PMF.piFin fun _ : Fin n => PMF.coin q hq0 hq1).toOuterMeasure
        {v | (n : ℝ) * t ≤ n * q - numTrue v}
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  have h := (hoeffding_piFin_of_expect_eq (fun _ : Fin n => PMF.coin q hq0 hq1)
    (fun _ b => if b = true then (1 : ℝ) else 0) (fun _ b => by cases b <;> simp)
    (fun _ => expect_coin q hq0 hq1) ht).2
  simpa only [sum_ite_eq_numTrue] using h

/-- **Instance: three fair coins.** For `n = 3`, `q = 1/2` and `t = 1/4` the hypotheses of
`chernoff_coin_upper` hold, and the theorem gives
`Pr[#heads - 3/2 ≥ 3/4] ≤ exp (-3/8)`. The bound is below one, and the event is nonempty
(three heads lie in it), so the statement is not vacuous. -/
theorem three_fair_coins :
    (PMF.piFin fun _ : Fin 3 => PMF.coin (1 / 2) (by norm_num) (by norm_num)).toOuterMeasure
        {v | (3 : ℝ) * (1 / 4) ≤ numTrue v - 3 * (1 / 2)}
      ≤ ENNReal.ofReal (Real.exp (-3 / 8)) ∧
    Real.exp (-3 / 8) < 1 ∧
    (fun _ => true) ∈ {v : Fin 3 → Bool | (3 : ℝ) * (1 / 4) ≤ numTrue v - 3 * (1 / 2)} := by
  refine ⟨?_, by rw [Real.exp_lt_one_iff]; norm_num, ?_⟩
  · have h := chernoff_coin_upper (n := 3) (1 / 2) (by norm_num) (by norm_num)
      (t := 1 / 4) (by norm_num)
    norm_num at h ⊢
    exact h
  · simp [numTrue]
    norm_num

/-! ### Sub-distributions -/

namespace SDistr

/-- The joint sub-distribution of `n` independent draws `Xᵢ ∼ d i`, built in the `SDistr` monad:
draw `X₀`, then the remaining draws, and return `Fin.cons X₀ rest`. It fails as soon as one
draw fails. -/
noncomputable def drawN {β : Type*} : {n : ℕ} → (Fin n → SDistr β) → SDistr (Fin n → β)
  | 0, _ => SDistr.pure Fin.elim0
  | _ + 1, d => SDistr.bind (d 0) fun a =>
      SDistr.bind (drawN (Fin.tail d)) fun v => SDistr.pure (Fin.cons a v)

/-- A lossless sub-distribution (`d none = 0`) on a finite type, viewed as a `PMF`. -/
noncomputable def toPMF (d : SDistr α) (hd : d none = 0) : PMF α :=
  PMF.ofFintype (fun a => d (some a)) (by
    have h := d.tsum_coe
    rw [tsum_fintype, Fintype.sum_option, hd, zero_add] at h
    exact h)

theorem map_some_toPMF (d : SDistr α) (hd : d none = 0) : (toPMF d hd).map some = d := by
  ext o
  cases o with
  | none =>
    rw [hd, PMF.map_apply]
    simp
  | some a =>
    rw [PMF.map_apply, tsum_eq_single a]
    · simp [toPMF]
    · intro b hb
      simp [Ne.symm hb]

/-- If every draw is the image under `some` of a `PMF`, then `drawN` is the image under `some`
of the product `PMF.piFin`. -/
theorem drawN_eq_map_piFin {β : Type*} : ∀ {n : ℕ} (d : Fin n → SDistr β) (q : Fin n → PMF β),
    (∀ i, d i = (q i).map some) → drawN d = (PMF.piFin q).map some
  | 0, _, _, _ => by
    simp [drawN, PMF.piFin, SDistr.pure, PMF.pure_map]
  | n + 1, d, q, h => by
    rw [drawN, PMF.piFin, drawN_eq_map_piFin (Fin.tail d) (Fin.tail q) (fun i => h i.succ), h 0]
    simp only [SDistr.bind, PMF.bind_map, PMF.map_bind, SDistr.pure, PMF.pure_map]
    rfl

/-- **Chernoff-Hoeffding bound for sub-distributions, upper tail.** Let `d i : SDistr α` be
lossless (`d i none = 0`) and `fᵢ : α → [0, 1]`. Under the joint sub-distribution
`drawN d` of independent draws, for `t ≥ 0`,
`Pr[some v with ∑ᵢ fᵢ(vᵢ) - ∑ᵢ E[fᵢ(Xᵢ)] ≥ n t] ≤ exp (-2 n t²)`, where
`E[fᵢ(Xᵢ)] = ∑ₐ dᵢ(some a) fᵢ(a)`.

Reduced to `hoeffding_piFin_upper` (Mathlib's Hoeffding inequality through the bridge) by
`drawN_eq_map_piFin`. -/
theorem hoeffding_drawN_upper {n : ℕ} (d : Fin n → SDistr α) (hd : ∀ i, d i none = 0)
    (f : Fin n → α → ℝ) (hf : ∀ i a, f i a ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    (drawN d).toOuterMeasure (some '' {v | (n : ℝ) * t ≤
        ∑ i, f i (v i) - ∑ i, ∑ a, (d i (some a)).toReal * f i a})
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  rw [drawN_eq_map_piFin d (fun i => toPMF (d i) (hd i)) (fun i => (map_some_toPMF _ _).symm),
    PMF.toOuterMeasure_map_apply, Set.preimage_image_eq _ (Option.some_injective _)]
  exact hoeffding_piFin_upper _ f hf ht

/-- **Chernoff-Hoeffding bound for sub-distributions, lower tail.** Under the hypotheses of
`hoeffding_drawN_upper`, `Pr[some v with ∑ᵢ E[fᵢ(Xᵢ)] - ∑ᵢ fᵢ(vᵢ) ≥ n t] ≤ exp (-2 n t²)`.

Reduced to `hoeffding_piFin_lower` (Mathlib's Hoeffding inequality through the bridge) by
`drawN_eq_map_piFin`. -/
theorem hoeffding_drawN_lower {n : ℕ} (d : Fin n → SDistr α) (hd : ∀ i, d i none = 0)
    (f : Fin n → α → ℝ) (hf : ∀ i a, f i a ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    (drawN d).toOuterMeasure (some '' {v | (n : ℝ) * t ≤
        ∑ i, ∑ a, (d i (some a)).toReal * f i a - ∑ i, f i (v i)})
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  rw [drawN_eq_map_piFin d (fun i => toPMF (d i) (hd i)) (fun i => (map_some_toPMF _ _).symm),
    PMF.toOuterMeasure_map_apply, Set.preimage_image_eq _ (Option.some_injective _)]
  exact hoeffding_piFin_lower _ f hf ht

end SDistr

end CatCrypt.Prob

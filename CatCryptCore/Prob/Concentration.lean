/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PMFPi
public import CatCryptCore.Prob.SDistr
public import CatCryptCore.ForMathlib.EmbeddingFinSucc
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Concentration bounds: Chernoff-Hoeffding and sampling without replacement

This file proves the Chernoff-Hoeffding bound for sums of independent random variables with
values in `[0, 1]`, and the corresponding upper tail for sampling without replacement
(hypergeometric tail), for distributions given as Mathlib `PMF`s and as CatCrypt
sub-distributions `SDistr α = PMF (Option α)`.

Independence is not an abstract hypothesis: the `n` draws are combined into the joint
distribution `PMF.piFin p : PMF (Fin n → α)` obtained by binding them one after the other
(`CatCryptCore/ForMathlib/PMFPi.lean`), respectively `SDistr.drawN d` built with the `SDistr`
monad.

## Method

The bounds for independent draws are obtained from Mathlib's measure-theoretic Hoeffding inequality
`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` and Hoeffding's lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, through the bridge
`PMF.toMeasure_piFin : (PMF.piFin p).toMeasure = Measure.pi (fun i ↦ (p i).toMeasure)`
and the independence statement `PMF.iIndepFun_piFin` derived from it.

The bound for sampling without replacement is proved directly by the moment-generating-function
method on the uniform `PMF` over injective sequences `Fin k ↪ β`: the moment-generating function
of the marked count is bounded by that of `k` draws with replacement (Hoeffding 1963, §6, for
the exponential function), by induction along the sequential description of the draw
(`Fintype.sum_embedding_fin_succ`) and Chebyshev's sum inequality; Hoeffding's lemma for a
Bernoulli variable (`PMF.one_sub_add_mul_exp_le`, from Mathlib) concludes.

## Main results

* `hoeffding_piFin_upper`, `hoeffding_piFin_lower`: for `fᵢ : α → [0, 1]` and `S = ∑ᵢ fᵢ(Xᵢ)`,
  `Pr[S - E S ≥ n t] ≤ exp (-2 n t²)` and `Pr[E S - S ≥ n t] ≤ exp (-2 n t²)`.
* `chernoff_coin_upper`, `chernoff_coin_lower`: the same for `n` independent Bernoulli(`q`)
  trials, with `S` the number of successes and `E S = n q`.
* `SDistr.hoeffding_drawN_upper`, `SDistr.hoeffding_drawN_lower`: the same for `n`
  independent lossless sub-distributions.
* `hypergeometric_upper`: for `k` items drawn uniformly without replacement from `N` items of
  which `K` are marked, `Pr[#marked - k K / N ≥ k t] ≤ exp (-2 k t²)`;
  `committee_upper` states it for the drawn set, `SDistr.hypergeometric_upper` for `SDistr`.
* `three_fair_coins`, `committee_four_of_ten`: concrete instances of the hypotheses.

## References

* W. Hoeffding, *Probability inequalities for sums of bounded random variables*,
  J. Amer. Statist. Assoc. 58 (1963), Theorem 1 and Section 6.
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

/-! ### Sampling without replacement -/

section Hypergeometric

variable {β : Type*} [DecidableEq β] (M : Finset β)

/-- The number of positions `i` at which the sequence `v` takes a value in the marked set `M`. -/
def numMarked {k : ℕ} (v : Fin k → β) : ℕ := (Finset.univ.filter fun i => v i ∈ M).card

/-- The indicator of the marked set, as a real function. -/
private noncomputable def ind (x : β) : ℝ := if x ∈ M then 1 else 0

private theorem numMarked_eq_sum {k : ℕ} (v : Fin k → β) :
    (numMarked M v : ℝ) = ∑ i, ind M (v i) := by
  simp [numMarked, ind, Finset.sum_boole]

private theorem numMarked_cons {k : ℕ} (x : β) (v : Fin k → β) :
    (numMarked M (Fin.cons x v : Fin (k + 1) → β) : ℝ) = ind M x + numMarked M v := by
  rw [numMarked_eq_sum, numMarked_eq_sum, Fin.sum_univ_succ]
  simp

variable [Fintype β]

private theorem sum_ind : ∑ x, ind M x = M.card := by
  simp [ind]

/-- A sum over the complement of the range of an injective sequence. -/
private theorem sum_compl_map {k : ℕ} (e : Fin k ↪ β) (g : β → ℝ) :
    ∑ x ∈ (Finset.univ.map e)ᶜ, g x = ∑ x, g x - ∑ i, g (e i) := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_map Finset.univ e g, Finset.sum_compl_add_sum]

/-- The number of injective sequences of length `k`, as a real number. -/
private noncomputable def numEmb (β : Type*) [Fintype β] [DecidableEq β] (k : ℕ) : ℝ :=
  Fintype.card (Fin k ↪ β)

private theorem numEmb_succ (k : ℕ) :
    numEmb β (k + 1) = numEmb β k * (Fintype.card β - k) := by
  calc numEmb β (k + 1) = ∑ _e : Fin (k + 1) ↪ β, (1 : ℝ) := by simp [numEmb]
    _ = ∑ e : Fin k ↪ β, ∑ x ∈ (Finset.univ.map e)ᶜ, (1 : ℝ) :=
      Fintype.sum_embedding_fin_succ (fun _ => (1 : ℝ))
    _ = ∑ _e : Fin k ↪ β, ((Fintype.card β : ℝ) - k) :=
      Finset.sum_congr rfl fun e _ => by rw [sum_compl_map]; simp
    _ = _ := by simp [numEmb, mul_sub]

/-- One step of sequential sampling without replacement for the marked count: the new item
is marked for `K - c` of the `N - k` remaining choices. -/
private theorem sum_numMarked_succ (k : ℕ) :
    ∑ e : Fin (k + 1) ↪ β, (numMarked M e : ℝ) =
      ∑ e : Fin k ↪ β, ((M.card : ℝ) + ((Fintype.card β : ℝ) - k - 1) * numMarked M e) := by
  rw [Fintype.sum_embedding_fin_succ (fun v => (numMarked M v : ℝ))]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp_rw [numMarked_cons]
  rw [Finset.sum_add_distrib, sum_compl_map, sum_compl_map e (fun _ => (numMarked M e : ℝ)),
    sum_ind, ← numMarked_eq_sum]
  simp
  ring

/-- **Mean of the marked count.** Over all injective sequences of length `k`,
`(∑ₑ #marked(e)) · N = #sequences · k · K`, i.e. the expected marked count is `k K / N`. -/
private theorem sum_numMarked_mul (k : ℕ) :
    (∑ e : Fin k ↪ β, (numMarked M e : ℝ)) * Fintype.card β = numEmb β k * k * M.card := by
  induction k with
  | zero => simp [numMarked]
  | succ k ih =>
    rw [sum_numMarked_succ, Finset.sum_add_distrib, ← Finset.mul_sum, numEmb_succ]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold numEmb at *
    push_cast
    linear_combination ((Fintype.card β : ℝ) - k - 1) * ih

/-- One step of sequential sampling without replacement for the moment-generating function
of the marked count. -/
private theorem sum_exp_numMarked_succ (k : ℕ) (l : ℝ) :
    ∑ e : Fin (k + 1) ↪ β, Real.exp (l * numMarked M e) =
      ∑ e : Fin k ↪ β, Real.exp (l * numMarked M e) *
        (((Fintype.card β : ℝ) - k) + (Real.exp l - 1) * (M.card - numMarked M e)) := by
  rw [Fintype.sum_embedding_fin_succ (fun v => Real.exp (l * numMarked M v))]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hx : ∀ x, Real.exp (l * (ind M x + numMarked M e)) =
      Real.exp (l * numMarked M e) * (1 + (Real.exp l - 1) * ind M x) := by
    intro x
    unfold ind
    split_ifs <;> simp [mul_add, Real.exp_add]
    ring
  simp_rw [numMarked_cons, hx]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_compl_map,
    sum_compl_map, sum_ind, ← numMarked_eq_sum]
  simp

/-- **Moment-generating function of sampling without replacement.** For `l ≥ 0` and a
nonempty population of `N` items with `K` marked,
`∑ₑ exp (l · #marked(e)) ≤ #sequences · (1 + (eˡ - 1) K / N)ᵏ`, the sum ranging over the
injective sequences `e` of length `k`. The right-hand side is `#sequences` times the
moment-generating function of `k` draws with replacement.

Proved by induction on `k` along the sequential description of drawing without replacement:
the factor contributed by the next draw is a decreasing function of the current marked count,
the weight `exp (l · #marked)` is increasing in it, and Chebyshev's sum inequality
(`Antivary.card_mul_sum_le_sum_mul_sum`) bounds the average of their product by the product of
their averages; the average of the factor is computed from `sum_numMarked_mul`. -/
private theorem sum_exp_numMarked_le {l : ℝ} (hl : 0 ≤ l) (hN : 0 < Fintype.card β) (k : ℕ) :
    ∑ e : Fin k ↪ β, Real.exp (l * numMarked M e) ≤
      numEmb β k * (1 + (Real.exp l - 1) * (M.card / Fintype.card β)) ^ k := by
  set N : ℝ := (Fintype.card β : ℝ) with hNdef
  set K : ℝ := (M.card : ℝ)
  set ρ : ℝ := 1 + (Real.exp l - 1) * (K / N)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hexp : 0 ≤ Real.exp l - 1 := by linarith [Real.add_one_le_exp l]
  have hρ : 1 ≤ ρ := by
    have : 0 ≤ (Real.exp l - 1) * (K / N) := mul_nonneg hexp (by positivity)
    linarith
  induction k with
  | zero => simp [numMarked, numEmb]
  | succ k ih =>
    rw [sum_exp_numMarked_succ, numEmb_succ, pow_succ]
    set C := numEmb β k
    set A := ∑ e : Fin k ↪ β, Real.exp (l * numMarked M e)
    set w : (Fin k ↪ β) → ℝ := fun e => Real.exp (l * numMarked M e)
    set g : (Fin k ↪ β) → ℝ := fun e => (N - k) + (Real.exp l - 1) * (K - numMarked M e)
    rcases (Nat.cast_nonneg (Fintype.card (Fin k ↪ β)) : (0 : ℝ) ≤ _).eq_or_lt with hC | hC
    · -- no injective sequence of length `k`: both sides vanish
      have hE : IsEmpty (Fin k ↪ β) := Fintype.card_eq_zero_iff.1 (by exact_mod_cast hC.symm)
      simp [C, numEmb]
    · obtain ⟨e₀⟩ : Nonempty (Fin k ↪ β) := Fintype.card_pos_iff.1 (by exact_mod_cast hC)
      have hk : (k : ℝ) ≤ N := by
        have := Fintype.card_le_of_embedding e₀
        simp only [Fintype.card_fin] at this
        exact Nat.cast_le.2 this
      have hanti : Antivary w g := by
        intro i j hij
        simp only [w, g] at hij ⊢
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hl)
        by_contra hc
        have hc := not_le.1 hc
        nlinarith
      have hcheb := Antivary.card_mul_sum_le_sum_mul_sum hanti
      have hsumg : (∑ e, g e) = C * (N - k) * ρ := by
        have hD := sum_numMarked_mul M k
        simp only [g, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change _ + _ * (_ - ∑ e : Fin k ↪ β, (numMarked M e : ℝ)) = _
        have hD' : ∑ e : Fin k ↪ β, (numMarked M e : ℝ) = C * k * K / N := by
          rw [eq_div_iff hN'.ne']; exact hD
        rw [hD']
        simp only [ρ, C, numEmb]
        field_simp
      have hCpos : (0 : ℝ) < C := hC
      have hstep : ∑ e, w e * g e ≤ A * ((N - k) * ρ) := by
        rw [hsumg] at hcheb
        have : C * ∑ e, w e * g e ≤ C * (A * ((N - k) * ρ)) := by
          simp only [numEmb, C] at hcheb ⊢
          nlinarith [hcheb]
        exact le_of_mul_le_mul_left this hCpos
      calc ∑ e, w e * g e ≤ A * ((N - k) * ρ) := hstep
        _ ≤ C * ρ ^ k * ((N - k) * ρ) :=
          mul_le_mul_of_nonneg_right ih (mul_nonneg (by linarith) (by linarith))
        _ = C * (N - k) * (ρ ^ k * ρ) := by ring

/-- **Tail bound for sampling without replacement (hypergeometric tail).** Draw `k` items
uniformly without replacement from a finite population `β` of `N` items of which the
`K = #M` items of `M` are marked; the draw is a uniformly distributed injective sequence
`e : Fin k ↪ β`, which requires `k ≤ N` (stated as the hypothesis `Nonempty (Fin k ↪ β)`).
For every `t ≥ 0`,
`Pr[#marked(e) - k K / N ≥ k t] ≤ exp (-2 k t²)`.

Proved directly by the moment-generating-function method on the uniform `PMF`: Markov's
inequality for `exp (4 t · #marked)`, the comparison `sum_exp_numMarked_le` of the
moment-generating function with that of `k` draws with replacement (Hoeffding 1963, §6, for the
exponential function), and Hoeffding's lemma for a Bernoulli variable
`PMF.one_sub_add_mul_exp_le`, which is obtained from Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`. -/
theorem hypergeometric_upper {k : ℕ} [Nonempty (Fin k ↪ β)] {t : ℝ} (ht : 0 ≤ t) :
    (PMF.uniformFintype (Fin k ↪ β)).toOuterMeasure
        {e | (k : ℝ) * t ≤ numMarked M e - k * M.card / Fintype.card β}
      ≤ ENNReal.ofReal (Real.exp (-2 * k * t ^ 2)) := by
  obtain ⟨e₀⟩ := ‹Nonempty (Fin k ↪ β)›
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [show (-2 * ((0 : ℕ) : ℝ) * t ^ 2) = 0 by simp, Real.exp_zero, ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans (by simp)
  have hN : 0 < Fintype.card β :=
    lt_of_lt_of_le (by simpa using hk) (Fintype.card_le_of_embedding e₀)
  set N : ℝ := (Fintype.card β : ℝ) with hNdef
  set K : ℝ := (M.card : ℝ) with hKdef
  set C : ℝ := numEmb β k with hCdef
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hC : 0 < C := Nat.cast_pos.2 Fintype.card_pos
  set l : ℝ := 4 * t with hldef
  have hl : 0 ≤ l := by positivity
  set a : ℝ := k * K / N + k * t with hadef
  set ρ : ℝ := 1 + (Real.exp l - 1) * (K / N) with hρdef
  rw [PMF.toOuterMeasure_apply_fintype]
  have hpt : ∀ e : Fin k ↪ β,
      Set.indicator {e : Fin k ↪ β | (k : ℝ) * t ≤ numMarked M e - k * K / N}
        (PMF.uniformFintype (Fin k ↪ β)) e
        ≤ ENNReal.ofReal (C⁻¹ * Real.exp (l * (numMarked M e - a))) := by
    intro e
    by_cases he : e ∈ {e : Fin k ↪ β | (k : ℝ) * t ≤ numMarked M e - k * K / N}
    · rw [Set.indicator_of_mem he, PMF.uniformFintype_apply]
      have h1 : 1 ≤ Real.exp (l * (numMarked M e - a)) := by
        refine Real.one_le_exp (mul_nonneg hl ?_)
        simp only [Set.mem_ofPred_eq] at he
        linarith
      calc ((Fintype.card (Fin k ↪ β) : ℝ≥0∞))⁻¹ = ENNReal.ofReal C⁻¹ := by
            rw [ENNReal.ofReal_inv_of_pos hC]; simp [C, numEmb]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right (inv_nonneg.2 hC.le) h1)
    · rw [Set.indicator_of_notMem he]
      exact zero_le
  refine (Finset.sum_le_sum fun e _ => hpt e).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hA := sum_exp_numMarked_le M hl hN k
  have hp1 : K / N ≤ 1 := div_le_one_of_le₀ (Nat.cast_le.2 (Finset.card_le_univ M)) hN'.le
  have hρ0 : 0 ≤ ρ := by
    have : 0 ≤ (Real.exp l - 1) * (K / N) :=
      mul_nonneg (by linarith [Real.add_one_le_exp l]) (by positivity)
    linarith
  have hρ : ρ ≤ Real.exp (l * (K / N) + l ^ 2 / 8) := by
    have := PMF.one_sub_add_mul_exp_le (q := K / N) (by positivity) hp1 l
    linarith
  calc ∑ e : Fin k ↪ β, C⁻¹ * Real.exp (l * (numMarked M e - a))
      = C⁻¹ * Real.exp (-(l * a)) * ∑ e : Fin k ↪ β, Real.exp (l * numMarked M e) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [show l * ((numMarked M e : ℝ) - a) = -(l * a) + l * numMarked M e by ring,
          Real.exp_add]
        ring
    _ ≤ C⁻¹ * Real.exp (-(l * a)) * (C * ρ ^ k) := by gcongr
    _ = Real.exp (-(l * a)) * ρ ^ k := by field_simp
    _ ≤ Real.exp (-(l * a)) * Real.exp (l * (K / N) + l ^ 2 / 8) ^ k := by gcongr
    _ = Real.exp (-2 * k * t ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        simp only [hadef, hldef]
        field_simp
        ring

/-- **Committee selection.** The committee is the set `univ.map e` of the members drawn by a
uniformly distributed injective sequence `e : Fin k ↪ β` (equivalently, `k` members drawn
uniformly without replacement). For `t ≥ 0`, the number of marked members of the committee
satisfies `Pr[#(T ∩ M) - k K / N ≥ k t] ≤ exp (-2 k t²)`.

Direct consequence of `hypergeometric_upper` (MGF method on `PMF`). -/
theorem committee_upper {k : ℕ} [Nonempty (Fin k ↪ β)] {t : ℝ} (ht : 0 ≤ t) :
    ((PMF.uniformFintype (Fin k ↪ β)).map fun e => Finset.univ.map e).toOuterMeasure
        {T | (k : ℝ) * t ≤ (T ∩ M).card - k * M.card / Fintype.card β}
      ≤ ENNReal.ofReal (Real.exp (-2 * k * t ^ 2)) := by
  have key : ∀ e : Fin k ↪ β, (Finset.univ.map e ∩ M).card = numMarked M e := fun e => by
    rw [← Finset.filter_mem_eq_inter, Finset.filter_map, Finset.card_map]
    rfl
  rw [PMF.toOuterMeasure_map_apply]
  convert hypergeometric_upper M ht using 3
  ext e
  simp [key]

/-- **Sampling without replacement as a sub-distribution.** Under the `SDistr` uniform
distribution on injective sequences `e : Fin k ↪ β`, for `t ≥ 0`,
`Pr[some e with #marked(e) - k K / N ≥ k t] ≤ exp (-2 k t²)`.

Reduced to `hypergeometric_upper` (MGF method on `PMF`) since `SDistr.uniform` is the image of
`PMF.uniformFintype` under `some`. -/
theorem SDistr.hypergeometric_upper {k : ℕ} [Nonempty (Fin k ↪ β)] {t : ℝ} (ht : 0 ≤ t) :
    (SDistr.uniform (Fin k ↪ β)).toOuterMeasure
        (some '' {e | (k : ℝ) * t ≤ numMarked M e - k * M.card / Fintype.card β})
      ≤ ENNReal.ofReal (Real.exp (-2 * k * t ^ 2)) := by
  rw [SDistr.uniform, PMF.toOuterMeasure_map_apply,
    Set.preimage_image_eq _ (Option.some_injective _)]
  exact CatCrypt.Prob.hypergeometric_upper M ht

end Hypergeometric

/-- **Instance: a committee of 4 out of 10 with 5 marked members.** For `N = 10`, `K = 5`,
`k = 4` and `t = 1/4` the hypotheses of `hypergeometric_upper` hold (`4 ≤ 10` gives an
injective sequence), and the theorem gives `Pr[#marked - 2 ≥ 1] ≤ exp (-1/2)`. The bound is
below one and the event is nonempty (the sequence `0, 1, 2, 3` draws four marked items), so the
statement is not vacuous. -/
theorem committee_four_of_ten :
    haveI : Nonempty (Fin 4 ↪ Fin 10) := ⟨Fin.castLEEmb (by norm_num : 4 ≤ 10)⟩
    (PMF.uniformFintype (Fin 4 ↪ Fin 10)).toOuterMeasure
        {e | (4 : ℝ) * (1 / 4) ≤
          numMarked (Finset.univ.filter fun i : Fin 10 => i.val < 5) e - 4 * 5 / 10}
      ≤ ENNReal.ofReal (Real.exp (-1 / 2)) ∧
    Real.exp (-1 / 2) < 1 ∧
    (4 : ℝ) * (1 / 4) ≤
      numMarked (Finset.univ.filter fun i : Fin 10 => i.val < 5) (Fin.castLEEmb (by norm_num : 4 ≤ 10))
        - 4 * 5 / 10 := by
  have hM : (Finset.univ.filter fun i : Fin 10 => i.val < 5).card = 5 := by decide
  have hc : numMarked (Finset.univ.filter fun i : Fin 10 => i.val < 5)
      (Fin.castLEEmb (by norm_num : 4 ≤ 10)) = 4 := by decide
  refine ⟨?_, by rw [Real.exp_lt_one_iff]; norm_num, ?_⟩
  · have : Nonempty (Fin 4 ↪ Fin 10) := ⟨Fin.castLEEmb (by norm_num : 4 ≤ 10)⟩
    have h := hypergeometric_upper (Finset.univ.filter fun i : Fin 10 => i.val < 5)
      (k := 4) (t := 1 / 4) (by norm_num)
    rw [hM] at h
    norm_num at h ⊢
    exact h
  · rw [hc]
    norm_num

end CatCrypt.Prob

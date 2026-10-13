/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SparseSearch

/-!
# Search in a uniformly random function

The bound of Ambainis–Hamburg–Unruh (CRYPTO 2019, §4.1) at the uniform weight
on `Fin m → Fin n`: when the bad values at every point carry at most a `λ`
fraction of `Fin n`, a `q`-query adversary outputs a bad point with probability
at most `4 (q + 1)² λ` on average over the oracle.

The reference oracle of `SparseSearch.sparse_search` is global, which at the
uniform weight forces every oracle to agree with it at every good point. Here
the reference is the table obtained from the oracle by replacing its value at
each bad point by an independent value drawn uniformly from the good values at
that point. Under the uniform weight the resampled table has the product of
the good-value weights whether or not a given point was bad, so the guessing
probabilities average against one weight on the reference tables.

## Main definitions

* `goodVals bad x`, `badVals bad x` — the values `y` with `bad x y = false`
  and with `bad x y`
* `goodMass bad x y` — the uniform weight on `goodVals bad x`
* `tableMass bad K` — the product weight `∏ x, goodMass bad x (K x)` on tables
* `pairMass bad a` — the weight on pairs of tables `a : Fin m → Fin n × Fin n`
  whose first component is uniform and whose second is `tableMass`
* `resampleTable bad a` — the first component of `a` with its value at each
  bad point replaced by the second component

## Main results

* `sum_pi_fiber` — a sum of a product weight against a coordinatewise map is
  the sum against the product of the fibre weights
* `sum_pairMass_fst` — the first marginal of `pairMass` is the uniform weight
* `sum_pairMass_resample` — the pairs whose first component is bad at `x`
  carry `(badVals bad x).card / n` of the weight, and on them the resampled
  table carries `tableMass`
* `generic_search_uniform` — `∑ H, (n ^ m)⁻¹ · prBad bad A H ≤ 4 (q + 1)² λ`
* `generic_search_uniform_card` — the same with the weight written as the
  inverse cardinality of the table type

## The hypotheses

In `generic_search_uniform` the adversary's initial state is pure (`hpure`), as
in `SparseSearch`. The predicate `bad` reads the oracle value at the output only
and has a good value at every point (`hgood : ∀ x, ∃ y, bad x y = false`), which
makes the resampling weight a probability weight. The per-point hypothesis `hlam`
is `(badVals bad x).card / n ≤ lam` at every `x`, and the constant is
`4 (q + 1) (q + 1)`.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §4.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Product weights and coordinatewise maps -/

/-- A sum of a product weight against a coordinatewise map, grouped by the
    image: the weight of a table `K` is the product of the weights of the
    fibres of `ρ i` at `K i`. -/
theorem sum_pi_fiber {ι α κ : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ] (ω : ι → α → ℝ≥0∞) (ρ : ι → α → κ) (f : (ι → κ) → ℝ≥0∞) :
    ∑ a : ι → α, (∏ i, ω i (a i)) * f (fun i => ρ i (a i)) =
      ∑ K : ι → κ, (∏ i, ∑ b ∈ Finset.univ.filter fun b => ρ i b = K i, ω i b) * f K := by
  rw [← Finset.sum_fiberwise Finset.univ (fun a : ι → α => fun i => ρ i (a i))
    (fun a => (∏ i, ω i (a i)) * f (fun i => ρ i (a i)))]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hfil : (Finset.univ.filter fun a : ι → α => (fun i => ρ i (a i)) = K) =
      Fintype.piFinset fun i => Finset.univ.filter fun b => ρ i b = K i := by
    ext a
    simp [Fintype.mem_piFinset, funext_iff]
  rw [hfil, Finset.prod_univ_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : (fun i => ρ i (a i)) = K := by
    have := (Fintype.mem_piFinset).mp ha
    funext i
    simpa using (Finset.mem_filter.mp (this i)).2
  rw [this]

/-! ## The resampling weight -/

section Resample

variable {m n : ℕ} [NeZero n]

/-- The values that are good at `x`. -/
def goodVals (bad : Fin m → Fin n → Bool) (x : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun y => bad x y = false

/-- The values that are bad at `x`. -/
def badVals (bad : Fin m → Fin n → Bool) (x : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun y => bad x y

/-- The uniform weight on the good values at `x`. -/
def goodMass (bad : Fin m → Fin n → Bool) (x : Fin m) (y : Fin n) : ℝ≥0∞ :=
  if bad x y then 0 else ((goodVals bad x).card : ℝ≥0∞)⁻¹

/-- The product of the good-value weights over the points. -/
def tableMass (bad : Fin m → Fin n → Bool) (K : Fin m → Fin n) : ℝ≥0∞ :=
  ∏ x, goodMass bad x (K x)

/-- The weight on pairs of tables whose first component is uniform and whose
    second component carries `tableMass`. -/
def pairMass (bad : Fin m → Fin n → Bool) (a : Fin m → Fin n × Fin n) : ℝ≥0∞ :=
  ∏ x, (n : ℝ≥0∞)⁻¹ * goodMass bad x (a x).2

/-- The first component of `a` with its value at each bad point replaced by
    the second component. -/
def resampleTable (bad : Fin m → Fin n → Bool) (a : Fin m → Fin n × Fin n) : Fin m → Fin n :=
  fun x => if bad x (a x).1 then (a x).2 else (a x).1

variable {bad : Fin m → Fin n → Bool}

omit [NeZero n] in
/-- The bad and the good values at `x` exhaust `Fin n`. -/
theorem card_badVals_add_card_goodVals (x : Fin m) :
    (badVals bad x).card + (goodVals bad x).card = n := by
  have h : goodVals bad x = Finset.univ.filter fun y => ¬ (bad x y = true) := by
    unfold goodVals
    simp
  rw [badVals, h, Finset.card_filter_add_card_filter_not]
  simp

omit [NeZero n] in
theorem card_goodVals_ne_zero (hgood : ∀ x, ∃ y, bad x y = false) (x : Fin m) :
    ((goodVals bad x).card : ℝ≥0∞) ≠ 0 := by
  obtain ⟨y, hy⟩ := hgood x
  have : y ∈ goodVals bad x := by simp [goodVals, hy]
  simpa using Finset.card_ne_zero_of_mem this

omit [NeZero n] in
/-- The good-value weights at `x` sum to one. -/
theorem sum_goodMass (hgood : ∀ x, ∃ y, bad x y = false) (x : Fin m) :
    ∑ y, goodMass bad x y = 1 := by
  have h : ∀ y, goodMass bad x y =
      if y ∈ goodVals bad x then ((goodVals bad x).card : ℝ≥0∞)⁻¹ else 0 := by
    intro y
    unfold goodMass goodVals
    cases hb : bad x y <;> simp [hb]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (card_goodVals_ne_zero hgood x) (ENNReal.natCast_ne_top _)

omit [NeZero n] in
/-- The weights on the tables sum to one. -/
theorem sum_tableMass (hgood : ∀ x, ∃ y, bad x y = false) :
    ∑ K : Fin m → Fin n, tableMass bad K = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset (Fin n)))
    (fun x y => goodMass bad x y)
  rw [Fintype.piFinset_univ] at h
  simp only [tableMass]
  rw [← h]
  simp [sum_goodMass hgood]

/-! ## The fibres of the resampling map -/

omit [NeZero n] in
/-- The weight of the fibre of the resampling map at `k`, with a factor `c`
    depending on the value before resampling. -/
theorem sum_fiber_resample (hgood : ∀ x, ∃ y, bad x y = false) (x : Fin m) (k : Fin n)
    (c : Fin n → ℝ≥0∞) :
    ∑ p ∈ Finset.univ.filter fun p : Fin n × Fin n => (if bad x p.1 then p.2 else p.1) = k,
      (n : ℝ≥0∞)⁻¹ * goodMass bad x p.2 * c p.1 =
      (∑ y ∈ badVals bad x, c y) * ((n : ℝ≥0∞)⁻¹ * goodMass bad x k) +
        (if bad x k then 0 else (n : ℝ≥0∞)⁻¹ * c k) := by
  have hz : ∀ y : Fin n, ∑ z : Fin n,
      (if (if bad x y then z else y) = k then (n : ℝ≥0∞)⁻¹ * goodMass bad x z * c y else 0) =
      if bad x y then (n : ℝ≥0∞)⁻¹ * goodMass bad x k * c y
        else if y = k then (n : ℝ≥0∞)⁻¹ * c y else 0 := by
    intro y
    by_cases hb : bad x y
    · simp only [hb, if_true]
      rw [Finset.sum_ite_eq' Finset.univ k fun z => (n : ℝ≥0∞)⁻¹ * goodMass bad x z * c y]
      simp
    · simp only [hb]
      by_cases hyk : y = k
      · simp only [hyk, Bool.false_eq_true, if_false, if_true]
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_goodMass hgood, mul_one]
      · simp [hyk]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [hz]
  rw [Finset.sum_ite, Finset.sum_ite_eq' (Finset.univ.filter fun y => ¬ bad x y) k
    fun y => (n : ℝ≥0∞)⁻¹ * c y]
  congr 1
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => by ring
  · by_cases hk : bad x k <;> simp [hk]

/-- The fibre weight of the resampling map is the good-value weight. -/
theorem sum_fiber_resample_one (hgood : ∀ x, ∃ y, bad x y = false) (x : Fin m) (k : Fin n) :
    ∑ p ∈ Finset.univ.filter fun p : Fin n × Fin n => (if bad x p.1 then p.2 else p.1) = k,
      (n : ℝ≥0∞)⁻¹ * goodMass bad x p.2 * 1 = goodMass bad x k := by
  rw [sum_fiber_resample hgood x k (fun _ => 1)]
  by_cases hk : bad x k
  · simp [goodMass, hk]
  · have hc : ((goodVals bad x).card : ℝ≥0∞) ≠ 0 := card_goodVals_ne_zero hgood x
    have hn : (n : ℝ≥0∞) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).2 (NeZero.ne n)
    have hsplit : ((badVals bad x).card : ℝ≥0∞) + ((goodVals bad x).card : ℝ≥0∞) = (n : ℝ≥0∞) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ≥0∞)) (card_badVals_add_card_goodVals x)
    have hg : ((goodVals bad x).card : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
        ((goodVals bad x).card : ℝ≥0∞)⁻¹) = (n : ℝ≥0∞)⁻¹ := by
      rw [← mul_assoc, mul_comm ((goodVals bad x).card : ℝ≥0∞) ((n : ℝ≥0∞)⁻¹), mul_assoc,
        ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), mul_one]
    simp only [goodMass, hk, Finset.sum_const, nsmul_eq_mul, mul_one]
    calc ((badVals bad x).card : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ * ((goodVals bad x).card : ℝ≥0∞)⁻¹) +
          (n : ℝ≥0∞)⁻¹
        = ((badVals bad x).card : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ * ((goodVals bad x).card : ℝ≥0∞)⁻¹) +
            ((goodVals bad x).card : ℝ≥0∞) *
              ((n : ℝ≥0∞)⁻¹ * ((goodVals bad x).card : ℝ≥0∞)⁻¹) := by rw [hg]
      _ = (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ * ((goodVals bad x).card : ℝ≥0∞)⁻¹) := by
            rw [← add_mul, hsplit]
      _ = ((goodVals bad x).card : ℝ≥0∞)⁻¹ := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hn (ENNReal.natCast_ne_top _), one_mul]

omit [NeZero n] in
/-- The fibre weight of the resampling map on the pairs that are bad before
    resampling. -/
theorem sum_fiber_resample_bad (hgood : ∀ x, ∃ y, bad x y = false) (x : Fin m) (k : Fin n) :
    ∑ p ∈ Finset.univ.filter fun p : Fin n × Fin n => (if bad x p.1 then p.2 else p.1) = k,
      (n : ℝ≥0∞)⁻¹ * goodMass bad x p.2 * (if bad x p.1 then 1 else 0) =
      ((badVals bad x).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * goodMass bad x k := by
  rw [sum_fiber_resample hgood x k (fun y => if bad x y then 1 else 0)]
  have hb : ∑ y ∈ badVals bad x, (if bad x y then (1 : ℝ≥0∞) else 0) =
      ((badVals bad x).card : ℝ≥0∞) := by
    have h1 : ∀ y ∈ badVals bad x, (if bad x y then (1 : ℝ≥0∞) else 0) = 1 := by
      intro y hy
      have hby : bad x y = true := by simpa [badVals] using hy
      simp [hby]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hb]
  by_cases hk : bad x k
  · simp [goodMass, hk]
  · simp [hk, mul_assoc]

/-! ## The two marginals of the pair weight -/

omit [NeZero n] in
/-- The fibre weight of the first projection. -/
theorem sum_fiber_fst (hgood : ∀ x, ∃ y, bad x y = false) (x : Fin m) (k : Fin n) :
    ∑ p ∈ Finset.univ.filter fun p : Fin n × Fin n => p.1 = k,
      (n : ℝ≥0∞)⁻¹ * goodMass bad x p.2 = (n : ℝ≥0∞)⁻¹ := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hy : ∀ y : Fin n,
      (∑ z : Fin n, if y = k then (n : ℝ≥0∞)⁻¹ * goodMass bad x z else 0) =
        if y = k then (n : ℝ≥0∞)⁻¹ else 0 := by
    intro y
    by_cases hyk : y = k
    · simp only [hyk, if_true]
      rw [← Finset.mul_sum, sum_goodMass hgood, mul_one]
    · simp [hyk]
  simp only [hy]
  rw [Finset.sum_ite_eq' Finset.univ k fun _ => (n : ℝ≥0∞)⁻¹]
  simp

omit [NeZero n] in
/-- The first marginal of the pair weight is the uniform weight on the
    tables. -/
theorem sum_pairMass_fst (hgood : ∀ x, ∃ y, bad x y = false)
    (f : (Fin m → Fin n) → ℝ≥0∞) :
    ∑ a : Fin m → Fin n × Fin n, pairMass bad a * f (fun x => (a x).1) =
      ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * f H := by
  have hL : (∑ a : Fin m → Fin n × Fin n, pairMass bad a * f (fun x => (a x).1)) =
      ∑ a : Fin m → Fin n × Fin n,
        (∏ x, (n : ℝ≥0∞)⁻¹ * goodMass bad x (a x).2) * f (fun x => (a x).1) := rfl
  rw [hL, sum_pi_fiber (fun x (p : Fin n × Fin n) => (n : ℝ≥0∞)⁻¹ * goodMass bad x p.2)
    (fun _ (p : Fin n × Fin n) => p.1) f]
  refine Finset.sum_congr rfl fun H _ => ?_
  congr 1
  rw [Finset.prod_congr rfl fun x _ => sum_fiber_fst hgood x (H x), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← ENNReal.inv_pow]

/-- The pairs whose first component is bad at `x₀` carry
    `(badVals bad x₀).card / n` of the weight, and on them the resampled table
    carries `tableMass`. -/
theorem sum_pairMass_resample (hgood : ∀ x, ∃ y, bad x y = false) (x₀ : Fin m)
    (f : (Fin m → Fin n) → ℝ≥0∞) :
    ∑ a : Fin m → Fin n × Fin n,
        pairMass bad a * (if bad x₀ (a x₀).1 then 1 else 0) * f (resampleTable bad a) =
      ((badVals bad x₀).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
        ∑ K : Fin m → Fin n, tableMass bad K * f K := by
  have hprod : ∀ a : Fin m → Fin n × Fin n,
      (∏ x, (n : ℝ≥0∞)⁻¹ * goodMass bad x (a x).2 *
          (if x = x₀ then (if bad x (a x).1 then 1 else 0) else 1)) =
        pairMass bad a * (if bad x₀ (a x₀).1 then 1 else 0) := by
    intro a
    rw [Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ x₀ fun x => (if bad x (a x).1 then 1 else 0)]
    simp [pairMass]
  have hL : (∑ a : Fin m → Fin n × Fin n,
        pairMass bad a * (if bad x₀ (a x₀).1 then 1 else 0) * f (resampleTable bad a)) =
      ∑ a : Fin m → Fin n × Fin n,
        (∏ x, (n : ℝ≥0∞)⁻¹ * goodMass bad x (a x).2 *
          (if x = x₀ then (if bad x (a x).1 then 1 else 0) else 1)) *
          f (fun x => if bad x (a x).1 then (a x).2 else (a x).1) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hprod a]
    rfl
  rw [hL, sum_pi_fiber (fun x (p : Fin n × Fin n) => (n : ℝ≥0∞)⁻¹ * goodMass bad x p.2 *
      (if x = x₀ then (if bad x p.1 then 1 else 0) else 1))
    (fun x (p : Fin n × Fin n) => if bad x p.1 then p.2 else p.1) f, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← mul_assoc]
  congr 1
  have hfib : ∀ x : Fin m,
      (∑ p ∈ Finset.univ.filter fun p : Fin n × Fin n => (if bad x p.1 then p.2 else p.1) = K x,
        (n : ℝ≥0∞)⁻¹ * goodMass bad x p.2 *
          (if x = x₀ then (if bad x p.1 then 1 else 0) else 1)) =
        (if x = x₀ then ((badVals bad x₀).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ else 1) *
          goodMass bad x (K x) := by
    intro x
    by_cases hx : x = x₀
    · subst hx
      simp only [if_true]
      rw [sum_fiber_resample_bad hgood x (K x), mul_assoc]
    · simp only [if_neg hx, one_mul]
      exact sum_fiber_resample_one hgood x (K x)
  rw [Finset.prod_congr rfl fun x _ => hfib x, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ x₀ fun _ => ((badVals bad x₀).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹]
  simp [tableMass]

end Resample

/-! ## The bound at the uniform weight -/

section Uniform

variable {m n w q : ℕ} [NeZero n]

/-- Search in a uniformly random function (Ambainis–Hamburg–Unruh, CRYPTO
    2019, §4.1): when the values that are bad at `x` are at most a `lam`
    fraction of `Fin n` at every `x`, the probability that a `q`-query
    adversary outputs a bad point is at most `4 (q + 1)² lam` on average over
    the uniform oracle. -/
theorem generic_search_uniform (bad : Fin m → Fin n → Bool) (A : QAdv m n (m * w) q)
    (lam : ℝ≥0∞) (hgood : ∀ x, ∃ y, bad x y = false)
    (hlam : ∀ x, ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    {ψ : Fin (m * n * (m * w)) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prBad bad A H ≤
      4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam := by
  have hcomm : ∀ F : (Fin m → Fin n × Fin n) → Fin (q + 1) → Fin m → ℝ≥0∞,
      ∑ a, ∑ j, ∑ x, F a j x = ∑ j, ∑ x, ∑ a, F a j x := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have key : ∀ a : Fin m → Fin n × Fin n,
      prBad bad A (fun x => (a x).1) ≤ 4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x,
        (if bad x (a x).1 then 1 else 0) *
          guessProb (extend A ∅) (resampleTable bad a) {x} j := by
    intro a
    refine (prBad_le_four_sum_guess bad A (fun x => (a x).1) (resampleTable bad a)
      (fun x hx => by simp [resampleTable, hx]) hpure).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [guessProb_extend A _ ∅, guessProb_eq_sum _ (resampleTable bad a) _ j hpure]
    simp only [badSet, Finset.sum_filter, boole_mul]
  calc ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prBad bad A H
      = ∑ a : Fin m → Fin n × Fin n, pairMass bad a * prBad bad A (fun x => (a x).1) :=
        (sum_pairMass_fst hgood fun H => prBad bad A H).symm
    _ ≤ ∑ a : Fin m → Fin n × Fin n, pairMass bad a * (4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x,
          (if bad x (a x).1 then 1 else 0) *
            guessProb (extend A ∅) (resampleTable bad a) {x} j) := by
        exact Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (key a)
    _ = 4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x, ∑ a : Fin m → Fin n × Fin n,
          pairMass bad a * (if bad x (a x).1 then 1 else 0) *
            guessProb (extend A ∅) (resampleTable bad a) {x} j := by
        rw [← hcomm fun a j x => pairMass bad a * (if bad x (a x).1 then 1 else 0) *
          guessProb (extend A ∅) (resampleTable bad a) {x} j, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_left_comm]
        congr 1
        simp only [Finset.mul_sum, ← mul_assoc]
    _ = 4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x,
          ((badVals bad x).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
            ∑ K, tableMass bad K * guessProb (extend A ∅) K {x} j := by
        refine congrArg _ (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_)
        exact sum_pairMass_resample hgood x fun K => guessProb (extend A ∅) K {x} j
    _ ≤ 4 * ((q : ℝ≥0∞) + 1) * ∑ j : Fin (q + 1), lam * 1 := by
        gcongr with j _
        calc ∑ x, ((badVals bad x).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
              ∑ K, tableMass bad K * guessProb (extend A ∅) K {x} j
            ≤ ∑ x, lam * ∑ K, tableMass bad K * guessProb (extend A ∅) K {x} j := by
              gcongr with x _
              rw [← div_eq_mul_inv]
              exact hlam x
          _ = lam * ∑ K, tableMass bad K * ∑ x, guessProb (extend A ∅) K {x} j := by
              rw [← Finset.mul_sum, Finset.sum_comm]
              refine congrArg _ (Finset.sum_congr rfl fun K _ => ?_)
              rw [Finset.mul_sum]
          _ ≤ lam * ∑ K : Fin m → Fin n, tableMass bad K * 1 := by
              gcongr with K _
              exact sum_guessProb_singleton_le_one (extend A ∅) K j hpure
          _ = lam * 1 := by simp only [mul_one, sum_tableMass hgood]
    _ = 4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam := by
        simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- `generic_search_uniform` with the uniform weight written as the inverse
    cardinality of the type of tables. -/
theorem generic_search_uniform_card (bad : Fin m → Fin n → Bool) (A : QAdv m n (m * w) q)
    (lam : ℝ≥0∞) (hgood : ∀ x, ∃ y, bad x y = false)
    (hlam : ∀ x, ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    {ψ : Fin (m * n * (m * w)) → ℂ} (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    ∑ H : Fin m → Fin n,
        (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ * prBad bad A H ≤
      4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam := by
  have hc : (Fintype.card (Fin m → Fin n) : ℝ≥0∞) = (n : ℝ≥0∞) ^ m := by
    simp
  rw [hc]
  exact generic_search_uniform bad A lam hgood hlam hpure

end Uniform

end CatCrypt.Quantum.QROM

end

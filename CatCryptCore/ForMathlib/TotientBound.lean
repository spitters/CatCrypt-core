/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Lower bounds on Euler's totient and on coprime pair counts

Three elementary lower bounds used by Shor's algorithm.

## Main results

* `totient_div_ge` — `1 / (log₂ n + 1) ≤ φ(n) / n`.
* `prod_one_sub_inv_sq_ge` — `1 / 2 ≤ ∏_{p ∣ r} (1 - 1 / p²)`.
* `card_gcd3_eq_one_ge` — at least `r² / 2` pairs `(a, b) ∈ [0, r)²` have `gcd (a, b, r) = 1`.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace TotientBound

/-- A product of `1 - 1/p` over `k` integers `p ≥ 2` is at least `1 / (k + 1)`. -/
theorem one_div_card_succ_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (1 : ℝ) / (S.card + 1) ≤ ∏ p ∈ S, (1 - ((p : ℝ))⁻¹) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl _ (ha a h)
    have hsub : S ⊆ Finset.Ico 2 a := fun x hx =>
      Finset.mem_Ico.2 ⟨hS x (Finset.mem_insert_of_mem hx), ha x hx⟩
    have hcard : S.card + 2 ≤ a := by
      have := Finset.card_le_card hsub
      simp only [Nat.card_Ico] at this
      have h2 : 2 ≤ a := hS a (Finset.mem_insert_self a S)
      omega
    have ih' := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS]
    have ha2 : (S.card : ℝ) + 2 ≤ a := by exact_mod_cast hcard
    have hk : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have hapos : (0 : ℝ) < a := by linarith
    have hinv : (a : ℝ)⁻¹ ≤ 1 / ((S.card : ℝ) + 2) := by
      rw [one_div]; exact inv_anti₀ (by linarith) ha2
    have h1 : 1 / ((S.card : ℝ) + 1 + 1) ≤ (1 - (a : ℝ)⁻¹) * (1 / ((S.card : ℝ) + 1)) := by
      have h3 : (1 - (a : ℝ)⁻¹) ≥ 1 - 1 / ((S.card : ℝ) + 2) := by linarith
      calc 1 / ((S.card : ℝ) + 1 + 1)
          = (1 - 1 / ((S.card : ℝ) + 2)) * (1 / ((S.card : ℝ) + 1)) := by
            field_simp; ring
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right h3
            positivity
    have hnn : 0 ≤ 1 - (a : ℝ)⁻¹ := by
      have : (a : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hapos]; linarith
      linarith
    push_cast
    exact h1.trans (mul_le_mul_of_nonneg_left ih' hnn)

/-- Telescoping lower bound: for `S ⊆ [2, M]`, `∏ (1 - 1/p²) ≥ (M + 1) / (2 M)`. -/
theorem prod_one_sub_inv_sq_Icc (M : ℕ) (hM : 1 ≤ M) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 2 M) :
    ((M : ℝ) + 1) / (2 * M) ≤ ∏ p ∈ S, (1 - ((p : ℝ) ^ 2)⁻¹) := by
  induction M, hM using Nat.le_induction generalizing S with
  | base =>
    have : S = ∅ := by simpa using hS
    subst this; norm_num
  | succ M hM ih =>
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hstep : ((M : ℝ) + 1 + 1) / (2 * ((M : ℝ) + 1)) ≤ ((M : ℝ) + 1) / (2 * M) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    by_cases h : (M + 1) ∈ S
    · have hsub : S.erase (M + 1) ⊆ Finset.Icc 2 M := by
        intro x hx
        have hx1 := Finset.mem_erase.1 hx
        have hx2 := Finset.mem_Icc.1 (hS hx1.2)
        exact Finset.mem_Icc.2 ⟨hx2.1, by omega⟩
      have ih' := ih _ hsub
      have hnn : 0 ≤ ∏ p ∈ S.erase (M + 1), (1 - ((p : ℝ) ^ 2)⁻¹) := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hp2 : (2 : ℝ) ≤ p := by
          exact_mod_cast (Finset.mem_Icc.1 (hS (Finset.mem_of_mem_erase hp))).1
        have : ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (by positivity)]; nlinarith
        linarith
      rw [← Finset.mul_prod_erase S _ h]
      have hc : ((M : ℝ) + 1 + 1) / (2 * ((M : ℝ) + 1)) ≤
          (1 - (((M + 1 : ℕ) : ℝ) ^ 2)⁻¹) * (((M : ℝ) + 1) / (2 * M)) := by
        push_cast
        rw [div_le_iff₀ (by positivity)]
        field_simp
        nlinarith
      have hf : 0 ≤ 1 - (((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
        have : (((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (by positivity)]; push_cast; nlinarith
        linarith
      have := hc.trans (mul_le_mul_of_nonneg_left ih' hf)
      push_cast at this ⊢
      exact this
    · have hsub : S ⊆ Finset.Icc 2 M := by
        intro x hx
        have hx2 := Finset.mem_Icc.1 (hS hx)
        have : x ≠ M + 1 := fun e => h (e ▸ hx)
        exact Finset.mem_Icc.2 ⟨hx2.1, by omega⟩
      push_cast
      exact hstep.trans (ih _ hsub)

/-- The sum of `1/p²` over a finite set of odd integers `≥ 3` is at most `1/4`. -/
theorem sum_inv_sq_odd_le (T : Finset ℕ) (hT : ∀ p ∈ T, Odd p ∧ 3 ≤ p) :
    ∑ p ∈ T, ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
  have aux : ∀ N : ℕ, ∑ j ∈ Finset.range N, (((2 * j + 3 : ℕ) : ℝ) ^ 2)⁻¹
      ≤ 1 / 4 - 1 / (4 * ((N : ℝ) + 1)) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have : (((2 * N + 3 : ℕ) : ℝ) ^ 2)⁻¹
          ≤ 1 / (4 * ((N : ℝ) + 1)) - 1 / (4 * ((N : ℝ) + 1 + 1)) := by
        push_cast
        rw [inv_eq_one_div, div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at ih this ⊢
      linarith
  obtain ⟨N, hN⟩ : ∃ N, ∀ p ∈ T, p ≤ N := ⟨T.sup id, fun p hp => Finset.le_sup (f := id) hp⟩
  have hsub : T ⊆ (Finset.range N).image (fun j : ℕ => (2 * j + 3 : ℕ)) := by
    intro p hp
    obtain ⟨⟨k, hk⟩, h3⟩ := hT p hp
    have := hN p hp
    refine Finset.mem_image.2 ⟨k - 1, Finset.mem_range.2 (by omega), by omega⟩
  calc ∑ p ∈ T, ((p : ℝ) ^ 2)⁻¹
      ≤ ∑ p ∈ (Finset.range N).image (fun j : ℕ => (2 * j + 3 : ℕ)), ((p : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ j ∈ Finset.range N, (((2 * j + 3 : ℕ) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_image (fun a _ b _ h => by omega)
    _ ≤ 1 / 4 := by
        have := aux N
        have : 0 ≤ 1 / (4 * ((N : ℝ) + 1)) := by positivity
        linarith

/-- The sum of `1/p²` over a finite set of primes is at most `1/2`. -/
theorem sum_inv_sq_primes_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p = 2)]
  have h1 : ∑ p ∈ S.filter (fun p => p = 2), ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    calc _ ≤ ∑ p ∈ ({2} : Finset ℕ), ((p : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => by simpa using (Finset.mem_filter.1 hx).2) (fun _ _ _ => by positivity)
      _ = 1 / 4 := by norm_num
  have h2 : ∑ p ∈ S.filter (fun p => ¬ p = 2), ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    refine sum_inv_sq_odd_le _ fun p hp => ?_
    obtain ⟨hpS, hp2⟩ := Finset.mem_filter.1 hp
    have hpp := hS p hpS
    exact ⟨hpp.odd_of_ne_two hp2, by have := hpp.two_le; omega⟩
  linarith

end TotientBound

open TotientBound

/-- `φ(n) / n ≥ 1 / (⌊log₂ n⌋ + 1)`. -/
theorem totient_div_ge {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / (Nat.log 2 n + 1) ≤ (n.totient : ℝ) / n := by
  have hk : n.primeFactors.card ≤ Nat.log 2 n := by
    have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
      calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := (Finset.prod_const 2).symm
        _ ≤ ∏ p ∈ n.primeFactors, p :=
          Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    exact Nat.le_log_of_pow_le (by norm_num)
      (h1.trans (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)))
  have hprod := one_div_card_succ_le_prod n.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have htot : (n.totient : ℝ) / n = ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    rw [h]
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [htot]
  refine le_trans ?_ hprod
  gcongr

/-- `∏_{p ∣ r} (1 - 1/p²) ≥ 1/2`. -/
theorem prod_one_sub_inv_sq_ge (r : ℕ) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ r.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) := by
  have := prod_one_sub_inv_sq_Icc (r + 1) (by omega) r.primeFactors (fun p hp =>
    Finset.mem_Icc.2 ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      (Nat.le_of_mem_primeFactors hp).trans (Nat.le_succ r)⟩)
  refine le_trans ?_ this
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  push_cast
  nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

namespace TotientBound

/-- At most `r / p` elements of `Fin r` are divisible by a divisor `p` of `r`. -/
theorem card_dvd_fin_le {r p : ℕ} (hpr : p ∣ r) :
    ((Finset.univ : Finset (Fin r)).filter (fun a => p ∣ a.val)).card ≤ r / p := by
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin r)).filter
    (fun a => p ∣ a.val)) (t := Finset.range (r / p)) (fun a => a.val / p) ?_ ?_
  · simpa using h
  · intro a ha
    exact Finset.mem_range.2 (Nat.div_lt_div_of_lt_of_dvd hpr a.isLt)
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    exact Fin.ext ((Nat.div_left_inj ha' hb').1 hab)

end TotientBound

/-- At least half of the pairs `(a, b) ∈ [0, r)²` satisfy `gcd (a, b, r) = 1`. -/
theorem card_gcd3_eq_one_ge {r : ℕ} (hr : 0 < r) :
    r ^ 2 ≤ 2 * ((Finset.univ : Finset (Fin r × Fin r)).filter
      (fun s => Nat.gcd (Nat.gcd s.1 s.2) r = 1)).card := by
  set G := (Finset.univ : Finset (Fin r × Fin r)).filter
    (fun s => Nat.gcd (Nat.gcd s.1 s.2) r = 1) with hG
  set B := (Finset.univ : Finset (Fin r × Fin r)).filter
    (fun s => ¬ Nat.gcd (Nat.gcd s.1 s.2) r = 1) with hB
  set A : ℕ → Finset (Fin r) := fun p =>
    (Finset.univ : Finset (Fin r)).filter (fun a => p ∣ a.val) with hA
  have hsum : G.card + B.card = r ^ 2 := by
    rw [hG, hB, Finset.card_filter_add_card_filter_not]; simp [sq]
  have hBsub : B ⊆ r.primeFactors.biUnion (fun p => A p ×ˢ A p) := by
    intro s hs
    have hne := (Finset.mem_filter.1 hs).2
    obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpr : p ∣ r := hpd.trans (Nat.gcd_dvd_right _ _)
    have hpg := hpd.trans (Nat.gcd_dvd_left _ _)
    refine Finset.mem_biUnion.2 ⟨p, Nat.mem_primeFactors.2 ⟨hpp, hpr, hr.ne'⟩, ?_⟩
    simp only [hA, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hpg.trans (Nat.gcd_dvd_left _ _), hpg.trans (Nat.gcd_dvd_right _ _)⟩
  have hBnat : B.card ≤ ∑ p ∈ r.primeFactors, (r / p) ^ 2 := by
    calc B.card ≤ (r.primeFactors.biUnion (fun p => A p ×ˢ A p)).card :=
          Finset.card_le_card hBsub
      _ ≤ ∑ p ∈ r.primeFactors, (A p ×ˢ A p).card := Finset.card_biUnion_le
      _ ≤ _ := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpr := Nat.dvd_of_mem_primeFactors hp
        rw [Finset.card_product, ← sq]
        exact Nat.pow_le_pow_left (card_dvd_fin_le hpr) 2
  have hBreal : (B.card : ℝ) ≤ (r : ℝ) ^ 2 * ∑ p ∈ r.primeFactors, ((p : ℝ) ^ 2)⁻¹ := by
    have h1 : (B.card : ℝ) ≤ ∑ p ∈ r.primeFactors, (((r / p : ℕ) : ℝ)) ^ 2 := by
      exact_mod_cast hBnat
    refine h1.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) hp0]
    field_simp
  have hS := sum_inv_sq_primes_le r.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hsumR : (G.card : ℝ) + B.card = (r : ℝ) ^ 2 := by exact_mod_cast hsum
  have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  have : (r : ℝ) ^ 2 ≤ 2 * G.card := by nlinarith
  exact_mod_cast this

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.GenericSearchUniform

/-!
# Search in a uniformly random function away from one point

A uniform table on `Fin m → Fin n` is its value at a point `t` together with a
uniform table on the other points. When an adversary is chosen as a function of
the value `H t`, and a point counts as bad only away from `t`, the search bound
of `generic_search_uniform` holds with the same constant: conditioned on
`H t = u`, the resampling argument leaves the entry at `t` untouched and the
adversary fixed.

## Main definitions

* `offPoint bad t` — the predicate `bad` with the point `t` declared good

## Main results

* `sum_split_point` — a sum over the tables is a sum over the value at `t` and
  over the tables on the other points, with the uniform weight factoring as
  `n⁻¹ · (n ^ (m - 1))⁻¹`
* `sum_tableMass_eval` — the `tableMass` weight of the tables with `K t = u` is
  `goodMass bad t u`
* `generic_search_at_point` — at a fixed value `u`, the tables with `H t = u`
  carry at most `4 (q + 1)² λ / n` of bad-output weight
* `generic_search_off_point` — `∑ H, (n ^ m)⁻¹ · prBad (offPoint bad t) (A (H t)) H ≤
  4 (q + 1)² λ` for an adversary family `A : Fin n → QAdv _ _ _ q`

## The hypotheses

In `generic_search_off_point` the initial states are pure, as in
`GenericSearchUniform`, and the per-point hypotheses `hgood` and `hlam` hold at
the points `x ≠ t`. The adversary depends on the table only through its oracle
and through the value `H t`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Splitting a table at a point -/

section Split

variable {m n : ℕ}

/-- A sum over the tables is a sum over the value at `t` and over the tables on
    the other points. -/
theorem sum_split_point (t : Fin m) (f : (Fin m → Fin n) → ℝ≥0∞) :
    ∑ H : Fin m → Fin n, f H =
      ∑ u : Fin n, ∑ H' : {x // x ≠ t} → Fin n,
        f ((Equiv.piSplitAt t fun _ => Fin n).symm (u, H')) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.piSplitAt t fun _ => Fin n) _ _ fun H =>
    (congrArg f ((Equiv.piSplitAt t fun _ => Fin n).symm_apply_apply H)).symm

/-- The uniform weight on the tables factors as the uniform weight on the value
    at `t` times the uniform weight on the tables on the other points. -/
theorem sum_split_point_uniform (t : Fin m) (f : (Fin m → Fin n) → ℝ≥0∞) :
    ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * f H =
      ∑ u : Fin n, (n : ℝ≥0∞)⁻¹ * ∑ H' : {x // x ≠ t} → Fin n,
        ((n : ℝ≥0∞) ^ (m - 1))⁻¹ * f ((Equiv.piSplitAt t fun _ => Fin n).symm (u, H')) := by
  have hm : m = (m - 1) + 1 := by have := t.isLt; omega
  have hw : ((n : ℝ≥0∞) ^ m)⁻¹ = (n : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) ^ (m - 1))⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (ENNReal.natCast_ne_top n)),
      ← pow_succ']
    conv_lhs => rw [hm]
  rw [sum_split_point t]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun H' _ => ?_
  rw [hw, mul_assoc]

end Split

/-! ## The predicate away from a point -/

section OffPoint

variable {m n : ℕ}

/-- The predicate `bad` with every value at `t` declared good. -/
def offPoint (bad : Fin m → Fin n → Bool) (t : Fin m) : Fin m → Fin n → Bool :=
  fun x y => bad x y && decide (x ≠ t)

variable {bad : Fin m → Fin n → Bool}

@[simp] theorem offPoint_self (t : Fin m) (y : Fin n) : offPoint bad t t y = false := by
  simp [offPoint]

theorem offPoint_of_ne {t x : Fin m} (hx : x ≠ t) (y : Fin n) : offPoint bad t x y = bad x y := by
  simp [offPoint, hx]

theorem offPoint_good [NeZero n] (t : Fin m) (hgood : ∀ x, x ≠ t → ∃ y, bad x y = false) :
    ∀ x, ∃ y, offPoint bad t x y = false := by
  intro x
  by_cases hx : x = t
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨y, hy⟩ := hgood x hx
    exact ⟨y, by rw [offPoint_of_ne hx, hy]⟩

theorem card_badVals_offPoint_le (t : Fin m) (lam : ℝ≥0∞)
    (hlam : ∀ x, x ≠ t → ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam) :
    ∀ x, ((badVals (offPoint bad t) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam := by
  intro x
  by_cases hx : x = t
  · subst hx
    have : badVals (offPoint bad x) x = ∅ := by simp [badVals]
    simp [this]
  · have : badVals (offPoint bad t) x = badVals bad x := by
      simp [badVals, offPoint_of_ne hx]
    rw [this]
    exact hlam x hx

/-- The tables whose entry at `t` is `u` carry `goodMass bad t u` of the
    `tableMass` weight. -/
theorem sum_tableMass_eval (hgood : ∀ x, ∃ y, bad x y = false) (t : Fin m) (u : Fin n) :
    ∑ K : Fin m → Fin n, tableMass bad K * (if K t = u then 1 else 0) = goodMass bad t u := by
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset (Fin n)))
    (fun x y => goodMass bad x y * (if x = t then (if y = u then 1 else 0) else 1))
  rw [Fintype.piFinset_univ] at h
  have hL : ∀ K : Fin m → Fin n, tableMass bad K * (if K t = u then 1 else 0) =
      ∏ x, goodMass bad x (K x) * (if x = t then (if K x = u then 1 else 0) else 1) := by
    intro K
    rw [Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ t fun x => (if K x = u then (1 : ℝ≥0∞) else 0)]
    simp [tableMass]
  simp only [hL]
  rw [← h]
  have hx : ∀ x : Fin m, ∑ y, goodMass bad x y * (if x = t then (if y = u then 1 else 0) else 1) =
      if x = t then goodMass bad t u else 1 := by
    intro x
    by_cases hxt : x = t
    · subst hxt
      simp
    · simp [hxt, sum_goodMass hgood x]
  simp only [hx]
  rw [Finset.prod_ite_eq' Finset.univ t fun _ => goodMass bad t u]
  simp

end OffPoint

/-! ## The search bound away from a point -/

section Search

variable {m n w q : ℕ} [NeZero n]

/-- At a fixed value `u` of the entry at `t`, the tables with `H t = u` carry at
    most `4 (q + 1)² lam / n` of the probability that the adversary outputs a
    point that is bad away from `t`. -/
theorem generic_search_at_point (bad : Fin m → Fin n → Bool) (t : Fin m) (u : Fin n)
    (B : QAdv m n (m * w) q) (lam : ℝ≥0∞) (hgood : ∀ x, x ≠ t → ∃ y, bad x y = false)
    (hlam : ∀ x, x ≠ t → ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    {ψ : Fin (m * n * (m * w)) → ℂ} (hpure : B.init.val = vecMulVec ψ (star ψ)) :
    ∑ H : Fin m → Fin n,
        ((n : ℝ≥0∞) ^ m)⁻¹ * ((if H t = u then 1 else 0) * prBad (offPoint bad t) B H) ≤
      4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam * (n : ℝ≥0∞)⁻¹ := by
  set bad' := offPoint bad t with hbad'
  have hgood' : ∀ x, ∃ y, bad' x y = false := offPoint_good t hgood
  have hlam' := card_badVals_offPoint_le t lam hlam
  have hres : ∀ a : Fin m → Fin n × Fin n, resampleTable bad' a t = (a t).1 := by
    intro a
    simp [resampleTable, hbad']
  have hcomm : ∀ F : (Fin m → Fin n × Fin n) → Fin (q + 1) → Fin m → ℝ≥0∞,
      ∑ a, ∑ j, ∑ x, F a j x = ∑ j, ∑ x, ∑ a, F a j x := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have key : ∀ a : Fin m → Fin n × Fin n,
      (if (a t).1 = u then 1 else 0) * prBad bad' B (fun x => (a x).1) ≤
        4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x, (if bad' x (a x).1 then 1 else 0) *
          ((if resampleTable bad' a t = u then 1 else 0) *
            guessProb (extend B ∅) (resampleTable bad' a) {x} j) := by
    intro a
    have h0 : prBad bad' B (fun x => (a x).1) ≤ 4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x,
        (if bad' x (a x).1 then 1 else 0) *
          guessProb (extend B ∅) (resampleTable bad' a) {x} j := by
      refine (prBad_le_four_sum_guess bad' B (fun x => (a x).1) (resampleTable bad' a)
        (fun x hx => by simp [resampleTable, hx]) hpure).trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [guessProb_extend B _ ∅, guessProb_eq_sum _ (resampleTable bad' a) _ j hpure]
      simp only [badSet, Finset.sum_filter, boole_mul]
    rw [hres a]
    by_cases hu : (a t).1 = u
    · simpa [hu] using h0
    · simp [hu]
  calc ∑ H : Fin m → Fin n,
        ((n : ℝ≥0∞) ^ m)⁻¹ * ((if H t = u then 1 else 0) * prBad bad' B H)
      = ∑ a : Fin m → Fin n × Fin n, pairMass bad' a *
          ((if (a t).1 = u then 1 else 0) * prBad bad' B (fun x => (a x).1)) :=
        (sum_pairMass_fst hgood' fun H => (if H t = u then 1 else 0) * prBad bad' B H).symm
    _ ≤ ∑ a : Fin m → Fin n × Fin n, pairMass bad' a * (4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x,
          (if bad' x (a x).1 then 1 else 0) *
            ((if resampleTable bad' a t = u then 1 else 0) *
              guessProb (extend B ∅) (resampleTable bad' a) {x} j)) :=
        Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (key a)
    _ = 4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x, ∑ a : Fin m → Fin n × Fin n,
          pairMass bad' a * (if bad' x (a x).1 then 1 else 0) *
            ((if resampleTable bad' a t = u then 1 else 0) *
              guessProb (extend B ∅) (resampleTable bad' a) {x} j) := by
        rw [← hcomm fun a j x => pairMass bad' a * (if bad' x (a x).1 then 1 else 0) *
          ((if resampleTable bad' a t = u then 1 else 0) *
            guessProb (extend B ∅) (resampleTable bad' a) {x} j), Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_left_comm]
        congr 1
        simp only [Finset.mul_sum, ← mul_assoc]
    _ = 4 * ((q : ℝ≥0∞) + 1) * ∑ j, ∑ x,
          ((badVals bad' x).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
            ∑ K, tableMass bad' K *
              ((if K t = u then 1 else 0) * guessProb (extend B ∅) K {x} j) := by
        refine congrArg _ (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_)
        exact sum_pairMass_resample hgood' x fun K =>
          (if K t = u then 1 else 0) * guessProb (extend B ∅) K {x} j
    _ ≤ 4 * ((q : ℝ≥0∞) + 1) * ∑ j : Fin (q + 1), lam * (n : ℝ≥0∞)⁻¹ := by
        gcongr with j _
        calc ∑ x, ((badVals bad' x).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
              ∑ K, tableMass bad' K *
                ((if K t = u then 1 else 0) * guessProb (extend B ∅) K {x} j)
            ≤ ∑ x, lam * ∑ K, tableMass bad' K *
                ((if K t = u then 1 else 0) * guessProb (extend B ∅) K {x} j) := by
              gcongr with x _
              rw [← div_eq_mul_inv]
              exact hlam' x
          _ = lam * ∑ K, tableMass bad' K * ((if K t = u then 1 else 0) *
                ∑ x, guessProb (extend B ∅) K {x} j) := by
              rw [← Finset.mul_sum, Finset.sum_comm]
              refine congrArg _ (Finset.sum_congr rfl fun K _ => ?_)
              rw [Finset.mul_sum, Finset.mul_sum]
          _ ≤ lam * ∑ K : Fin m → Fin n, tableMass bad' K * (if K t = u then 1 else 0) := by
              gcongr with K _
              calc (if K t = u then (1 : ℝ≥0∞) else 0) *
                    ∑ x, guessProb (extend B ∅) K {x} j
                  ≤ (if K t = u then 1 else 0) * 1 :=
                    mul_le_mul' le_rfl (sum_guessProb_singleton_le_one (extend B ∅) K j hpure)
                _ = _ := mul_one _
          _ = lam * (n : ℝ≥0∞)⁻¹ := by
              rw [sum_tableMass_eval hgood' t u]
              simp [goodMass, goodVals, hbad']
    _ = 4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam * (n : ℝ≥0∞)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- Search away from a point (Ambainis–Hamburg–Unruh, CRYPTO 2019, §4.1, with
    the adversary chosen from the value of the table at `t`): when the values
    that are bad at `x ≠ t` are at most a `lam` fraction of `Fin n`, the
    probability that the adversary `A (H t)` outputs a point `x ≠ t` with
    `bad x (H x)` is at most `4 (q + 1)² lam` on average over the uniform
    table `H`. -/
theorem generic_search_off_point (bad : Fin m → Fin n → Bool) (t : Fin m)
    (A : Fin n → QAdv m n (m * w) q) (lam : ℝ≥0∞)
    (hgood : ∀ x, x ≠ t → ∃ y, bad x y = false)
    (hlam : ∀ x, x ≠ t → ((badVals bad x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam)
    {ψ : Fin n → Fin (m * n * (m * w)) → ℂ}
    (hpure : ∀ u, (A u).init.val = vecMulVec (ψ u) (star (ψ u))) :
    ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prBad (offPoint bad t) (A (H t)) H ≤
      4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam := by
  have hsplit : ∀ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * prBad (offPoint bad t) (A (H t)) H =
      ∑ u, ((n : ℝ≥0∞) ^ m)⁻¹ *
        ((if H t = u then 1 else 0) * prBad (offPoint bad t) (A u) H) := by
    intro H
    rw [← Finset.mul_sum]
    congr 1
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  have hn : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)
  simp only [hsplit]
  rw [Finset.sum_comm]
  calc ∑ u : Fin n, ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ *
        ((if H t = u then 1 else 0) * prBad (offPoint bad t) (A u) H)
      ≤ ∑ _u : Fin n, 4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam * (n : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun u _ =>
          generic_search_at_point bad t u (A u) lam hgood hlam (hpure u)
    _ = 4 * ((q : ℝ≥0∞) + 1) * ((q : ℝ≥0∞) + 1) * lam := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_comm, mul_assoc, mul_comm (n : ℝ≥0∞)⁻¹, hn, mul_one]

end Search

end CatCrypt.Quantum.QROM

end

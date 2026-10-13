/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.O2HTheorem
public import Mathlib.Analysis.MeanInequalities

/-!
# The O2H bound with classical side information

A `QGame` is a finite classical input distribution together with, at each
input, a `q`-query adversary of `Quantum/QROM/SemiClassicalOracle.lean` and
the two oracle functions it may be run against, agreeing outside a punctured
set. The one-way-to-hiding bound of `Quantum/QROM/O2HTheorem.lean` holds at
each input; averaging it over the input distribution and moving the average
inside the square root by concavity gives the bound for the averaged
probabilities (Ambainis–Hamburg–Unruh, CRYPTO 2019, §3).

## Main definitions

* `QGame m n w q ι` — the input distribution `sample`, the adversary `adv`, the
  two oracles `oracle`, `oracle'`, the punctured set `S`, and the proofs that
  the oracles agree outside `S` and that every initial state is pure
* `prWin`, `prWin'` — the averaged acceptance probabilities with `oracle` and
  `oracle'`
* `prFindAvg` — the averaged `Find` probability

## Main results

* `absDiff_sum_le`, `absDiff_mul_left_le` — `absDiff` of finite sums and of
  scalar multiples in `ℝ≥0∞`
* `sum_mul_rpow_half_le` — `∑ᵢ pᵢ xᵢ^(1/2) ≤ (∑ᵢ pᵢ xᵢ)^(1/2)` when `∑ᵢ pᵢ = 1`
* `o2h_avg` — `|prWin G − prWin' G| ≤ 4 √(q · prFindAvg G)`
* `o2h_avg_sq` — the squared form `|prWin G − prWin' G|² ≤ (4q)² · prFindAvg G`

## The model

In a `QGame` the side information is a finite classical input `i : ι` with
`Fintype ι`, sampled with weights `sample i` that sum to one as a `Finset.sum`;
the adversary, the two oracles and the punctured set are functions of `i`; each
adversary starts from a pure state (the field `pure`). The averaged
probabilities `prWin`, `prWin'` and `prFindAvg` are the `Finset.sum` over `ι`
weighted by `sample`.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §3
* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.1
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open CatCrypt.Quantum

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## `absDiff` over sums and scalar multiples -/

section AbsDiff

variable {ι : Type} [Fintype ι]

/-- `absDiff` of two finite sums is at most the sum of the termwise `absDiff`s. -/
theorem absDiff_sum_le (a b : ι → ℝ≥0∞) :
    absDiff (∑ i, a i) (∑ i, b i) ≤ ∑ i, absDiff (a i) (b i) := by
  have h : ∀ i, a i ≤ b i + absDiff (a i) (b i) ∧ b i ≤ a i + absDiff (a i) (b i) :=
    fun i => absDiff_le_iff.mp le_rfl
  rw [absDiff_le_iff, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact ⟨Finset.sum_le_sum fun i _ => (h i).1, Finset.sum_le_sum fun i _ => (h i).2⟩

/-- `absDiff` of two scalar multiples is at most the scalar times the `absDiff`. -/
theorem absDiff_mul_left_le (c a b : ℝ≥0∞) :
    absDiff (c * a) (c * b) ≤ c * absDiff a b := by
  obtain ⟨h₁, h₂⟩ : a ≤ b + absDiff a b ∧ b ≤ a + absDiff a b := absDiff_le_iff.mp le_rfl
  rw [absDiff_le_iff, ← mul_add, ← mul_add]
  exact ⟨by gcongr, by gcongr⟩

end AbsDiff

/-! ## Concavity of the square root over a probability vector -/

section Concavity

variable {ι : Type} [Fintype ι]

/-- `x ^ (1/2)` squared is `x` in `ℝ≥0∞`. -/
theorem rpow_half_rpow_two (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]; norm_num

/-- `x ^ (1/2) · x ^ (1/2) = x` in `ℝ≥0∞`. -/
theorem rpow_half_mul_self (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← sq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- Jensen's inequality for the square root over a probability vector:
    `∑ᵢ pᵢ xᵢ^(1/2) ≤ (∑ᵢ pᵢ xᵢ)^(1/2)` when `∑ᵢ pᵢ = 1`, by Cauchy–Schwarz with
    `pᵢ^(1/2)` and `(pᵢ xᵢ)^(1/2)`. -/
theorem sum_mul_rpow_half_le (p x : ι → ℝ≥0∞) (hp : ∑ i, p i = 1) :
    ∑ i, p i * x i ^ (1 / 2 : ℝ) ≤ (∑ i, p i * x i) ^ (1 / 2 : ℝ) := by
  have hcs := ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun i => p i ^ (1 / 2 : ℝ))
    (fun i => (p i * x i) ^ (1 / 2 : ℝ)) Real.HolderConjugate.two_two
  simp only [rpow_half_rpow_two, hp, ENNReal.one_rpow, one_mul] at hcs
  refine le_of_eq_of_le ?_ hcs
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← mul_assoc,
    rpow_half_mul_self]

end Concavity

/-! ## The game -/

/-- A `q`-query oracle game with finite classical side information: an input
    `i : ι` is sampled with weight `sample i`; the adversary `adv i` is run against
    the oracle `oracle i` or its reprogrammed version `oracle' i`, which agree
    outside the punctured set `S i`; every adversary starts from a pure state. -/
structure QGame (m n w q : ℕ) (ι : Type) [Fintype ι] where
  /-- The weight of each input. -/
  sample : ι → ℝ≥0∞
  /-- The weights sum to one. -/
  sample_sum : ∑ i, sample i = 1
  /-- The adversary at each input. -/
  adv : ι → QAdv m n w q
  /-- The oracle at each input. -/
  oracle : ι → (Fin m → Fin n)
  /-- The reprogrammed oracle at each input. -/
  oracle' : ι → (Fin m → Fin n)
  /-- The punctured set at each input. -/
  S : ι → Finset (Fin m)
  /-- The two oracles agree outside the punctured set. -/
  agree : ∀ i x, x ∉ S i → oracle i x = oracle' i x
  /-- Every adversary starts from a pure state. -/
  pure : ∀ i, ∃ ψ : Fin (m * n * w) → ℂ, (adv i).init.val = Matrix.vecMulVec ψ (star ψ)

section Game

variable {m n w q : ℕ} {ι : Type} [Fintype ι] [NeZero n]

/-- The averaged probability that the adversary outputs `1` against `oracle`. -/
def prWin (G : QGame m n w q ι) : ℝ≥0∞ :=
  ∑ i, G.sample i * prOut (G.adv i) (G.oracle i)

/-- The averaged probability that the adversary outputs `1` against `oracle'`. -/
def prWin' (G : QGame m n w q ι) : ℝ≥0∞ :=
  ∑ i, G.sample i * prOut (G.adv i) (G.oracle' i)

/-- The averaged probability of `Find` against `oracle` on the punctured set. -/
def prFindAvg (G : QGame m n w q ι) : ℝ≥0∞ :=
  ∑ i, G.sample i * prFind (G.adv i) (G.oracle i) (G.S i)

/-- The one-way-to-hiding bound averaged over the classical side information
    (Ambainis–Hamburg–Unruh, CRYPTO 2019, §3):
    `|prWin G − prWin' G| ≤ 4 √(q · prFindAvg G)`. -/
theorem o2h_avg (G : QGame m n w q ι) :
    absDiff (prWin G) (prWin' G) ≤ 4 * ((q : ℝ≥0∞) * prFindAvg G) ^ (1 / 2 : ℝ) := by
  calc absDiff (prWin G) (prWin' G)
      ≤ ∑ i, absDiff (G.sample i * prOut (G.adv i) (G.oracle i))
          (G.sample i * prOut (G.adv i) (G.oracle' i)) := absDiff_sum_le _ _
    _ ≤ ∑ i, G.sample i * (4 * ((q : ℝ≥0∞) * prFind (G.adv i) (G.oracle i) (G.S i)) ^
          (1 / 2 : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => (absDiff_mul_left_le _ _ _).trans ?_
        obtain ⟨ψ, hψ⟩ := G.pure i
        have := o2h (G.adv i) (G.oracle i) (G.oracle' i) (G.S i) (G.agree i) hψ
        gcongr
    _ = 4 * ∑ i, G.sample i * ((q : ℝ≥0∞) * prFind (G.adv i) (G.oracle i) (G.S i)) ^
          (1 / 2 : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 4 * (∑ i, G.sample i * ((q : ℝ≥0∞) * prFind (G.adv i) (G.oracle i) (G.S i))) ^
          (1 / 2 : ℝ) := by
        have := sum_mul_rpow_half_le G.sample
          (fun i => (q : ℝ≥0∞) * prFind (G.adv i) (G.oracle i) (G.S i)) G.sample_sum
        gcongr
    _ = 4 * ((q : ℝ≥0∞) * prFindAvg G) ^ (1 / 2 : ℝ) := by
        unfold prFindAvg
        rw [Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The squared form of `o2h_avg`: `|prWin G − prWin' G|² ≤ (4q)² · prFindAvg G`. -/
theorem o2h_avg_sq (G : QGame m n w q ι) :
    absDiff (prWin G) (prWin' G) ^ 2 ≤ (4 * (q : ℝ≥0∞)) ^ 2 * prFindAvg G := by
  have h := o2h_avg G
  have hsq : (((q : ℝ≥0∞) * prFindAvg G) ^ (1 / 2 : ℝ)) ^ 2 = (q : ℝ≥0∞) * prFindAvg G := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc absDiff (prWin G) (prWin' G) ^ 2
      ≤ (4 * ((q : ℝ≥0∞) * prFindAvg G) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' h 2
    _ = 4 ^ 2 * ((q : ℝ≥0∞) * prFindAvg G) := by rw [mul_pow, hsq]
    _ ≤ (4 * (q : ℝ≥0∞)) ^ 2 * prFindAvg G := by
        rcases Nat.eq_zero_or_pos q with hq | hq
        · subst hq; simp
        · rw [mul_pow, mul_assoc]
          gcongr
          calc (q : ℝ≥0∞) = (q : ℝ≥0∞) * 1 := (mul_one _).symm
            _ ≤ (q : ℝ≥0∞) * q := by gcongr; exact_mod_cast hq
            _ = (q : ℝ≥0∞) ^ 2 := (sq _).symm

end Game

end CatCrypt.Quantum.QROM

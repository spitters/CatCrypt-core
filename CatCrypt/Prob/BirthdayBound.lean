/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.HybridArgument
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Inv
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Birthday Bound

This file provides the **birthday bound**: the probability that q uniform
samples from a set of size N contain a collision is at most `q(q-1)/(2N)`.

## Structure

**Layer 1 — Pure arithmetic**: Gauss sum formula in ENNReal.

**Layer 2 — Abstract composition**: If the per-step collision probability
at step i is at most i/N, the total collision probability is ≤ q(q-1)/(2N).

**Layer 3 — Connection to security games**: The birthday bound implies that
advantage between random function and random permutation games is small.

## Key Theorems

* `gauss_sum_ennreal` — `∑_{i<q} i/N = q(q-1)/2 / N` in ENNReal
* `birthday_bound_sum` — If step_pr(i) ≤ i/N, then ∑ step_pr(i) ≤ q(q-1)/(2N)
* `birthday_advantage` — Compose per-step advantage bounds into birthday bound

## References

* [Bellare & Rogaway, Introduction to Modern Cryptography]
* [Shoup, Sequences of Games]
-/

namespace CatCrypt.Prob.BirthdayBound

open Finset
open scoped ENNReal

/-! ## Layer 1: Pure Arithmetic -/

/-- Gauss sum formula in ℕ: `∑_{i<q} i = q*(q-1)/2` -/
theorem gauss_sum_nat (q : ℕ) : ∑ i ∈ range q, i = q * (q - 1) / 2 :=
  Finset.sum_range_id q

/-- Gauss sum formula with factor of 2: `2 * ∑_{i<q} i = q*(q-1)` -/
theorem gauss_sum_mul_two (q : ℕ) : (∑ i ∈ range q, i) * 2 = q * (q - 1) :=
  Finset.sum_range_id_mul_two q

/-- Key arithmetic identity in ENNReal:
    `∑_{i<q} (i : ℝ≥0∞) / N = q*(q-1)/2 / N`

    This is the birthday bound formula expressed as a sum of per-step
    collision probabilities. -/
theorem gauss_sum_ennreal (q : ℕ) (N : ℝ≥0∞) :
    ∑ i ∈ range q, (↑i : ℝ≥0∞) / N = ↑(q * (q - 1) / 2) / N := by
  -- Factor out 1/N from the sum: ∑ (i/N) = (∑ i) / N
  conv_lhs => arg 2; ext i; rw [show (↑i : ℝ≥0∞) / N = ↑i * N⁻¹ from div_eq_mul_inv _ _]
  rw [← Finset.sum_mul, div_eq_mul_inv]
  congr 1
  -- Need: ∑ i ∈ range q, (↑i : ℝ≥0∞) = ↑(q * (q - 1) / 2)
  rw [← Nat.cast_sum]
  congr 1
  exact gauss_sum_nat q

/-! ## Layer 2: Abstract Composition

    Given per-step collision probabilities bounded by i/N,
    bound the total collision probability by q(q-1)/(2N).
-/

/-- **Birthday bound from per-step bounds**:
    If the probability of a collision at step i (given no collision at steps < i)
    is at most i/N, then the total collision probability is at most q(q-1)/(2N).

    The per-step bound `i/N` is the probability that a fresh uniform sample
    from a set of size N collides with any of the i previously seen values.

    The composition uses the union bound (sum of per-step probabilities). -/
theorem birthday_bound_sum (q : ℕ) (N : ℝ≥0∞) (step_pr : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < q → step_pr i ≤ (↑i : ℝ≥0∞) / N) :
    ∑ i ∈ range q, step_pr i ≤ ↑(q * (q - 1) / 2) / N := by
  calc ∑ i ∈ range q, step_pr i
      ≤ ∑ i ∈ range q, (↑i : ℝ≥0∞) / N := by
        apply Finset.sum_le_sum
        intro i hi
        exact hstep i (Finset.mem_range.mp hi)
    _ = ↑(q * (q - 1) / 2) / N := gauss_sum_ennreal q N

/-- **Birthday bound (natural number denominator)**:
    Specialization with N as a natural number. -/
theorem birthday_bound_sum_nat (q N : ℕ) (step_pr : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < q → step_pr i ≤ (↑i : ℝ≥0∞) / ↑N) :
    ∑ i ∈ range q, step_pr i ≤ ↑(q * (q - 1) / 2) / ↑N :=
  birthday_bound_sum q ↑N step_pr hstep

/-! ## Layer 3: Integration with Security Games

    These lemmas connect the birthday bound to the advantage framework,
    allowing it to be used directly in game-hopping security proofs.
-/

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

variable {α : Type}

/-- **Birthday bound for advantage**: Given a sequence of hybrid games
    where step i→(i+1) has advantage ≤ i/N, the total advantage is
    at most q(q-1)/(2N).

    This combines the birthday bound arithmetic with the hybrid argument. -/
theorem birthday_advantage (G : ℕ → SPComp α) (A : α → SPComp Bool) (q N : ℕ)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ (↑i : ℝ≥0∞) / ↑N) :
    AdvantageA (G 0) (G q) A ≤ ↑(q * (q - 1) / 2) / ↑N := by
  calc AdvantageA (G 0) (G q) A
      ≤ ∑ i ∈ range q, AdvantageA (G i) (G (i + 1)) A :=
        CatCrypt.Crypto.HybridArgument.advantage_hybrid_dep G A q
    _ ≤ ↑(q * (q - 1) / 2) / ↑N :=
        birthday_bound_sum_nat q N _ hstep

/-- **Birthday bound for advantage with boundary conditions**:
    When real = G 0 and ideal = G q. -/
theorem birthday_advantage_bound (real ideal : SPComp α) (G : ℕ → SPComp α)
    (A : α → SPComp Bool) (q N : ℕ)
    (hleft : real = G 0) (hright : ideal = G q)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ (↑i : ℝ≥0∞) / ↑N) :
    AdvantageA real ideal A ≤ ↑(q * (q - 1) / 2) / ↑N := by
  rw [hleft, hright]
  exact birthday_advantage G A q N hstep

/-! ## Birthday Bound: Small Cases

    For small concrete cases, the birthday bound gives explicit values.
-/

/-- Birthday bound for q=2, N: Pr[collision] ≤ 1/N -/
theorem birthday_q2 (N : ℕ) (step_pr : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < 2 → step_pr i ≤ (↑i : ℝ≥0∞) / ↑N) :
    ∑ i ∈ range 2, step_pr i ≤ 1 / ↑N := by
  have h := birthday_bound_sum_nat 2 N step_pr hstep
  simp only [show 2 * (2 - 1) / 2 = 1 from rfl, Nat.cast_one] at h
  exact h

/-- Birthday bound for q=0: trivially 0 -/
theorem birthday_q0 (N : ℕ) (step_pr : ℕ → ℝ≥0∞) :
    ∑ i ∈ range 0, step_pr i ≤ 0 / (↑N : ℝ≥0∞) := by
  simp

/-- Birthday bound for q=1: 0 (no collision possible with one sample) -/
theorem birthday_q1 (N : ℕ) (step_pr : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < 1 → step_pr i ≤ (↑i : ℝ≥0∞) / ↑N) :
    ∑ i ∈ range 1, step_pr i = 0 := by
  simp only [Finset.sum_range_one]
  have h0 := hstep 0 (by omega)
  simp only [Nat.cast_zero] at h0
  exact le_antisymm (h0.trans (by simp)) (zero_le _)

end CatCrypt.Prob.BirthdayBound

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Uniform averages in `ℝ≥0∞`

Mathlib candidate. The uniform average of `f : ι → ℝ≥0∞` over a nonempty finite type is
`(Fintype.card ι)⁻¹ * ∑ i, f i`.

## Main results

* `ENNReal.inv_card_mul_sum_pow_three_le` — Jensen's inequality for the cube of a uniform
  average; it belongs in `Mathlib/Analysis/MeanInequalitiesPow.lean`, beside
  `ENNReal.rpow_arith_mean_le_arith_mean_rpow`;
* `ENNReal.inv_card_mul_sum_add_const` — the uniform average of `f i + b` is the average
  of `f` plus `b`; it belongs in `Mathlib/Data/ENNReal/BigOperators.lean`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace ENNReal

/-- Jensen's inequality for the cube of a uniform average. -/
theorem inv_card_mul_sum_pow_three_le {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ≥0∞) :
    ((Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, f i) ^ 3 ≤ (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, f i ^ 3 := by
  have hc0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : ∑ _i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ENNReal.mul_inv_cancel hc0 (ENNReal.natCast_ne_top _)]
  have h := ENNReal.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ => (Fintype.card ι : ℝ≥0∞)⁻¹) f hw (p := 3) (by norm_num)
  simp only [← Finset.mul_sum] at h
  exact_mod_cast h

/-- A uniform average of `f i + b` is the average of `f` plus `b`. -/
theorem inv_card_mul_sum_add_const {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ≥0∞)
    (b : ℝ≥0∞) :
    (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, (f i + b) = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, f i + b := by
  have hc0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel hc0 (ENNReal.natCast_ne_top _), one_mul]

end ENNReal

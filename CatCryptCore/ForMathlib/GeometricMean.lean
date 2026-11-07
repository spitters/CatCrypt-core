/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The mean of the number of trials until a success

A sequence of independent trials, each succeeding with probability `p` (`0 < p ≤ 1`), first succeeds
at trial `n + 1` with probability `(1 - p) ^ n * p`: these masses sum to one
(`tsum_geometric_mul_self`), and the expected number of trials is `p⁻¹`
(`tsum_succ_mul_geometric_mul`), the mean of the geometric distribution plus one.

## Main results

* `tsum_geometric_mul_self`, `tsum_succ_mul_geometric_mul`
-/

@[expose] public section

set_option autoImplicit false

/-- The masses `(1 - p) ^ n * p` of the first success at trial `n + 1` sum to one. -/
theorem tsum_geometric_mul_self {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, (1 - p) ^ n * p = 1 := by
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hr, sub_sub_cancel, inv_mul_cancel₀ hp0.ne']

/-- The expected number of trials until the first success is `p⁻¹`. -/
theorem tsum_succ_mul_geometric_mul {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((1 - p) ^ n * p) = p⁻¹ := by
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have h1 : Summable fun n : ℕ => (n : ℝ) * (1 - p) ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 : Summable fun n : ℕ => (1 - p) ^ n := summable_geometric_of_norm_lt_one hr
  calc ∑' n : ℕ, ((n : ℝ) + 1) * ((1 - p) ^ n * p)
      = (∑' n : ℕ, ((n : ℝ) * (1 - p) ^ n + (1 - p) ^ n)) * p := by
        rw [← tsum_mul_right]
        congr 1
        funext n
        ring
    _ = ((1 - p) / (1 - (1 - p)) ^ 2 + (1 - (1 - p))⁻¹) * p := by
        rw [h1.tsum_add h2, tsum_coe_mul_geometric_of_norm_lt_one hr,
          tsum_geometric_of_norm_lt_one hr]
    _ = p⁻¹ := by
        rw [sub_sub_cancel]
        field_simp
        ring

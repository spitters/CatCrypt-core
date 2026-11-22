/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ConcreteReductions
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Negligibility of exponentially small bounds

This file proves that the bound `2⁻ⁿ`, the bound `k n / 2 ⁿ` and the birthday bound
`q n ^ 2 / 2 ⁿ` are negligible in the sense of `IsNegligible`, where `k n ≤ n ^ d` and
`q n ≤ n ^ d` at every `n`, including `n = 0` and `n = 1`. This hypothesis, with constant
factor 1 and no threshold on `n`, is the one of `isNegligible_poly_mul`.

## Main results

* `isNegligible_two_pow_inv` — `n ↦ (2 ^ n)⁻¹` is negligible
* `isNegligible_natCast_div_two_pow` — `n ↦ k n / 2 ^ n` is negligible if `k n ≤ n ^ d` at
  every `n`
* `isNegligible_sq_div_two_pow` — `n ↦ q n ^ 2 / 2 ^ n` is negligible if `q n ≤ n ^ d` at
  every `n`
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace CatCrypt.Crypto

/-- The function `n ↦ (2 ^ n)⁻¹` is negligible: `n ^ c ≤ 2 ^ n` for all large `n`. -/
theorem isNegligible_two_pow_inv : IsNegligible (fun n => ((2 : ℝ≥0∞) ^ n)⁻¹) := by
  rw [isNegligible_iff_mul_pow_le]
  intro c
  have ht := tendsto_pow_const_div_const_pow_of_one_lt c (r := (2 : ℝ)) one_lt_two
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually (ge_mem_nhds zero_lt_one))
  refine ⟨N, fun n hn => ?_⟩
  have hnat : n ^ c ≤ 2 ^ n := by
    exact_mod_cast (div_le_one (by positivity)).1 (hN n hn)
  rw [ENNReal.inv_mul_le_iff (by simp) (by simp), mul_one]
  exact_mod_cast hnat

/-- If `k n ≤ n ^ d` at every `n`, the function `n ↦ k n / 2 ^ n` is negligible. -/
theorem isNegligible_natCast_div_two_pow (k : ℕ → ℕ) (d : ℕ) (hk : ∀ n, k n ≤ n ^ d) :
    IsNegligible (fun n => (k n : ℝ≥0∞) / 2 ^ n) := by
  have h := isNegligible_poly_mul d (fun n => (k n : ℝ≥0∞))
    (fun n => by exact_mod_cast hk n) isNegligible_two_pow_inv
  simpa only [div_eq_mul_inv] using h

/-- Birthday bound: if `q n ≤ n ^ d` at every `n`, the function `n ↦ q n ^ 2 / 2 ^ n` is
negligible. -/
theorem isNegligible_sq_div_two_pow (q : ℕ → ℕ) (d : ℕ) (hq : ∀ n, q n ≤ n ^ d) :
    IsNegligible (fun n => (q n : ℝ≥0∞) ^ 2 / 2 ^ n) := by
  have h := isNegligible_natCast_div_two_pow (fun n => q n ^ 2) (2 * d)
    (fun n => by rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (hq n) 2)
  simpa only [Nat.cast_pow] using h

end CatCrypt.Crypto

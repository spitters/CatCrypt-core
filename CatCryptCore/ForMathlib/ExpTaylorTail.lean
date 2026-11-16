/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Taylor remainder of the exponential in a Banach algebra

For `x` in a complete normed algebra over `ℂ` and `K : ℕ`,
`‖exp x - ∑_{k ≤ K} x^k / k!‖ ≤ ‖x‖^(K+1) / (K+1)! * e^‖x‖`.

## Main results

* `NormedSpace.norm_exp_sub_sum_le` — the remainder bound.
-/

@[expose] public section

set_option autoImplicit false

open NormedSpace

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- The remainder of the exponential series after the terms `k ≤ K` is at most
`‖x‖^(K+1) / (K+1)! * e^‖x‖`. -/
theorem norm_exp_sub_sum_le (x : 𝔸) (K : ℕ) :
    ‖exp x - ∑ k ∈ Finset.range (K + 1), (k.factorial : ℂ)⁻¹ • x ^ k‖ ≤
      ‖x‖ ^ (K + 1) / (K + 1).factorial * Real.exp ‖x‖ := by
  have hs : Summable fun n : ℕ => ((n.factorial : ℂ)⁻¹) • x ^ n :=
    expSeries_summable' (𝕂 := ℂ) x
  have hn : Summable fun n : ℕ => ‖((n.factorial : ℂ)⁻¹) • x ^ n‖ :=
    norm_expSeries_summable' (𝕂 := ℂ) x
  have hre : Summable fun j : ℕ => ‖x‖ ^ j / (j.factorial : ℝ) := by
    have := expSeries_summable' (𝕂 := ℝ) ‖x‖
    simpa [div_eq_inv_mul] using this
  have hsum : ∑' j : ℕ, ‖x‖ ^ j / (j.factorial : ℝ) = Real.exp ‖x‖ := by
    rw [Real.exp_eq_exp_ℝ, exp_eq_tsum_div (𝔸 := ℝ)]
  have htail : exp x - ∑ k ∈ Finset.range (K + 1), (k.factorial : ℂ)⁻¹ • x ^ k =
      ∑' j : ℕ, ((j + (K + 1)).factorial : ℂ)⁻¹ • x ^ (j + (K + 1)) := by
    rw [exp_eq_tsum ℂ]
    beta_reduce
    rw [← hs.sum_add_tsum_nat_add (K + 1)]
    abel
  rw [htail]
  have hn' : Summable fun j : ℕ => ‖((j + (K + 1)).factorial : ℂ)⁻¹ • x ^ (j + (K + 1))‖ :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖((n.factorial : ℂ)⁻¹) • x ^ n‖) (K + 1)).mpr hn
  refine (norm_tsum_le_tsum_norm hn').trans ?_
  rw [← hsum, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) hn' (hre.mul_left _)
  have hd : (K + 1).factorial * j.factorial ≤ (j + (K + 1)).factorial := by
    rw [mul_comm]
    exact Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  have hpow : ‖x ^ (j + (K + 1))‖ ≤ ‖x‖ ^ (j + (K + 1)) := norm_pow_le' x (by omega)
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc ((j + (K + 1)).factorial : ℝ)⁻¹ * ‖x ^ (j + (K + 1))‖
      ≤ ((j + (K + 1)).factorial : ℝ)⁻¹ * ‖x‖ ^ (j + (K + 1)) := by gcongr
    _ ≤ (((K + 1).factorial * j.factorial : ℕ) : ℝ)⁻¹ * ‖x‖ ^ (j + (K + 1)) := by
        gcongr
    _ = _ := by
        push_cast
        rw [pow_add]
        field_simp

end NormedSpace

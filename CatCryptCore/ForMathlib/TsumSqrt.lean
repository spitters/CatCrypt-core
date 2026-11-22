/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Jensen's inequality for the square root over a countable distribution

For nonnegative summable weights `q` of total weight `1` and nonnegative values `a` with
`q z * a z` summable, `∑' z, q z * √(a z) ≤ √(∑' z, q z * a z)`.

## Main results

* `summable_of_tsum_ne_zero`: a real function with nonzero sum is summable.
* `two_mul_mul_sqrt_le`: `2 t √a ≤ a + t²` for `a ≥ 0`.
* `tsum_mul_sqrt_le`: Jensen's inequality for the square root.

## Search words

Jensen inequality, square root, tsum, countable probability distribution, concavity
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

variable {ζ : Type}

/-- A real function with nonzero sum is summable. -/
theorem summable_of_tsum_ne_zero {f : ζ → ℝ} (h : ∑' z, f z ≠ 0) : Summable f := by
  exact of_not_not fun hs => h (tsum_eq_zero_of_not_summable hs)

/-- `2 t √a ≤ a + t²` for `a ≥ 0`. -/
theorem two_mul_mul_sqrt_le (a t : ℝ) (ha : 0 ≤ a) : 2 * t * Real.sqrt a ≤ a + t ^ 2 := by
  nlinarith [sq_nonneg (Real.sqrt a - t), Real.sq_sqrt ha]

/-- **Jensen's inequality for the square root** over a countable probability distribution:
`Σ q(z) √(a z) ≤ √(Σ q(z) a z)`. -/
theorem tsum_mul_sqrt_le {q a : ζ → ℝ} (hq : ∀ z, 0 ≤ q z) (hqs : Summable q)
    (hq1 : ∑' z, q z = 1) (ha : ∀ z, 0 ≤ a z) (hqa : Summable fun z => q z * a z) :
    ∑' z, q z * Real.sqrt (a z) ≤ Real.sqrt (∑' z, q z * a z) := by
  obtain ⟨S, hS⟩ : ∃ S, ∑' z, q z * a z = S := ⟨_, rfl⟩
  rw [hS]
  have hnn : ∀ z, 0 ≤ q z * a z := fun z => mul_nonneg (hq z) (ha z)
  have hS0 : 0 ≤ S := hS ▸ tsum_nonneg hnn
  rcases hS0.eq_or_lt with h0 | hpos
  · have hz : ∀ z, q z * a z = 0 := fun z =>
      congrFun ((hasSum_zero_iff_of_nonneg hnn).mp (by simpa [hS, ← h0] using hqa.hasSum)) z
    have hz' : ∀ z, q z * Real.sqrt (a z) = 0 := fun z => by
      rcases mul_eq_zero.mp (hz z) with h | h <;> simp [h]
    simp [hz', ← h0]
  · have ht : 0 < Real.sqrt S := Real.sqrt_pos.mpr hpos
    have hts : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0
    have hle : ∀ z, q z * Real.sqrt (a z) ≤ (q z * a z + q z * S) / (2 * Real.sqrt S) := by
      intro z
      rw [le_div_iff₀ (by positivity)]
      have h := two_mul_mul_sqrt_le (a z) (Real.sqrt S) (ha z)
      rw [hts] at h
      nlinarith [mul_nonneg (hq z) (sub_nonneg.mpr h)]
    have hsum : Summable fun z => (q z * a z + q z * S) / (2 * Real.sqrt S) :=
      (hqa.add (hqs.mul_right S)).div_const _
    calc ∑' z, q z * Real.sqrt (a z)
        ≤ ∑' z, (q z * a z + q z * S) / (2 * Real.sqrt S) :=
          Summable.tsum_le_tsum hle
            (hsum.of_nonneg_of_le (fun z => mul_nonneg (hq z) (Real.sqrt_nonneg _)) hle) hsum
      _ = (S + S) / (2 * Real.sqrt S) := by
          rw [tsum_div_const, hqa.tsum_add (hqs.mul_right S), tsum_mul_right, hq1, one_mul, hS]
      _ = Real.sqrt S := by
          rw [div_eq_iff (by positivity)]
          nlinarith

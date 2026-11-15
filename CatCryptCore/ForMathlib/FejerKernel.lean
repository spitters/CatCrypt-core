/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Fejér kernel of phase estimation

`fejer t δ = ‖2^{-t} ∑_{j < 2^t} e^{2π i j δ}‖²` is the probability that phase estimation
with `t` counting qubits reads the outcome `y` when the eigenphase is `φ` and
`δ = φ - y / 2^t`. It is the squared modulus of a normalized geometric sum, so it has the
closed form `sin²(π 2^t δ) / (4^t sin²(π δ))` away from the integers, value `1` at the
integers, and period `1` in `δ`. By Jordan's inequality `2x/π ≤ sin x` on `[0, π/2]` and
`|sin x| ≤ |x|`, the value is at least `4/π²` whenever `|δ| ≤ 2^{-(t+1)}`, the offset of the
outcome nearest to `2^t φ`.

## Main results

* `fejer_eq_sin_sq_div` — the closed form `sin²(π 2^t δ) / ((2^t)² sin²(π δ))` for
  `sin (π δ) ≠ 0`.
* `fejer_zero_right` — `fejer t 0 = 1`.
* `fejer_add_int`, `fejer_neg` — period `1` and symmetry.
* `fejer_nonneg`, `fejer_le_one` — `0 ≤ fejer t δ ≤ 1`.
* `four_div_pi_sq_le_fejer` — `4 / π² ≤ fejer t δ` for `|δ| ≤ 1 / 2^(t+1)`.
-/

@[expose] public section

set_option autoImplicit false

open Complex Finset

namespace PhaseEstimation

/-- The Fejér kernel `‖2^{-t} ∑_{j < 2^t} e^{2π i j δ}‖²`. -/
noncomputable def fejer (t : ℕ) (δ : ℝ) : ℝ :=
  ‖(2 ^ t : ℂ)⁻¹ * ∑ j ∈ range (2 ^ t), Complex.exp (2 * Real.pi * Complex.I * j * δ)‖ ^ 2

theorem fejer_nonneg (t : ℕ) (δ : ℝ) : 0 ≤ fejer t δ := by
  unfold fejer; positivity

/-- The summand `e^{2π i j δ}` is the `j`-th power of `e^{i (2π δ)}`. -/
theorem exp_term_eq_pow (j : ℕ) (δ : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * j * δ) =
      Complex.exp (Complex.I * ((2 * Real.pi * δ : ℝ) : ℂ)) ^ j := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Each summand has norm `1`. -/
theorem norm_exp_term (j : ℕ) (δ : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * j * δ)‖ = 1 := by
  rw [exp_term_eq_pow, norm_pow, Complex.norm_exp_I_mul_ofReal, one_pow]

theorem fejer_zero_right (t : ℕ) : fejer t 0 = 1 := by
  unfold fejer
  simp

theorem fejer_add_int (t : ℕ) (δ : ℝ) (k : ℤ) : fejer t (δ + k) = fejer t δ := by
  have hterm : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * j * ((δ + k : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * j * δ) := by
    intro j
    have h1 : Complex.exp (((j * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I _
    have h2 : 2 * Real.pi * Complex.I * j * ((δ + k : ℝ) : ℂ) =
        2 * Real.pi * Complex.I * j * δ + ((j * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [h2, Complex.exp_add, h1, mul_one]
  unfold fejer
  simp only [hterm]

theorem fejer_neg (t : ℕ) (δ : ℝ) : fejer t (-δ) = fejer t δ := by
  have hterm : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * j * ((-δ : ℝ) : ℂ)) =
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * j * δ)) := by
    intro j
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_natCast, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  unfold fejer
  simp only [hterm]
  rw [← map_sum, ← Complex.norm_conj]
  simp

theorem fejer_le_one (t : ℕ) (δ : ℝ) : fejer t δ ≤ 1 := by
  unfold fejer
  have h1 : ‖∑ j ∈ range (2 ^ t), Complex.exp (2 * Real.pi * Complex.I * j * δ)‖ ≤ 2 ^ t := by
    calc _ ≤ ∑ j ∈ range (2 ^ t), ‖Complex.exp (2 * Real.pi * Complex.I * j * δ)‖ :=
          norm_sum_le _ _
      _ = 2 ^ t := by simp [norm_exp_term]
  have h2 : ‖(2 ^ t : ℂ)⁻¹ * ∑ j ∈ range (2 ^ t), Complex.exp (2 * Real.pi * Complex.I * j * δ)‖
      ≤ 1 := by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
    have : (0 : ℝ) < 2 ^ t := by positivity
    rw [inv_mul_le_iff₀ this]
    simpa using h1
  exact pow_le_one₀ (norm_nonneg _) h2

theorem fejer_eq_sin_sq_div (t : ℕ) {δ : ℝ} (h : Real.sin (Real.pi * δ) ≠ 0) :
    fejer t δ
      = Real.sin (Real.pi * 2 ^ t * δ) ^ 2 / ((2 ^ t) ^ 2 * Real.sin (Real.pi * δ) ^ 2) := by
  set z : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * δ : ℝ) : ℂ)) with hz
  have hsum : ∑ j ∈ range (2 ^ t), Complex.exp (2 * Real.pi * Complex.I * j * δ) =
      ∑ j ∈ range (2 ^ t), z ^ j :=
    sum_congr rfl (fun j _ => exp_term_eq_pow j δ)
  have hn1 : ‖z - 1‖ = 2 * |Real.sin (Real.pi * δ)| := by
    rw [hz, Complex.norm_exp_I_mul_ofReal_sub_one]
    have : 2 * Real.pi * δ / 2 = Real.pi * δ := by ring
    rw [this, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    norm_num
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, sub_self, norm_zero] at hn1
    have : |Real.sin (Real.pi * δ)| = 0 := by linarith
    exact h (abs_eq_zero.1 this)
  have hzN : z ^ 2 ^ t = Complex.exp (Complex.I * ((2 * Real.pi * (2 ^ t * δ) : ℝ) : ℂ)) := by
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnN : ‖z ^ 2 ^ t - 1‖ = 2 * |Real.sin (Real.pi * 2 ^ t * δ)| := by
    rw [hzN, Complex.norm_exp_I_mul_ofReal_sub_one]
    have : 2 * Real.pi * (2 ^ t * δ) / 2 = Real.pi * 2 ^ t * δ := by ring
    rw [this, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    norm_num
  have hs : |Real.sin (Real.pi * δ)| ≠ 0 := abs_ne_zero.2 h
  have hnS : ‖∑ j ∈ range (2 ^ t), z ^ j‖ =
      |Real.sin (Real.pi * 2 ^ t * δ)| / |Real.sin (Real.pi * δ)| := by
    rw [geom_sum_eq hz1, norm_div, hn1, hnN]
    field_simp
  unfold fejer
  rw [hsum, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat, hnS]
  rw [mul_pow, div_pow, sq_abs, sq_abs]
  field_simp

/-- The bound `4 / π² ≤ fejer t δ` for a positive offset `δ ≤ 1 / 2^(t+1)`. -/
theorem four_div_pi_sq_le_fejer_of_pos (t : ℕ) {δ : ℝ} (h0 : 0 < δ)
    (hδ : δ ≤ 1 / 2 ^ (t + 1)) : 4 / Real.pi ^ 2 ≤ fejer t δ := by
  have hN : (0 : ℝ) < 2 ^ t := by positivity
  have hN1 : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  have hNδ : 2 ^ t * δ ≤ 1 / 2 := by
    have h : δ * 2 ^ (t + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 hδ
    rw [pow_succ] at h
    nlinarith
  have hpi := Real.pi_pos
  have hδ1 : δ ≤ 1 / 2 := by nlinarith
  have hsinpos : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  rw [fejer_eq_sin_sq_div t hsinpos.ne']
  have h1 : 2 * (2 ^ t * δ) ≤ Real.sin (Real.pi * 2 ^ t * δ) := by
    have h := Real.mul_le_sin (x := Real.pi * 2 ^ t * δ) (by positivity) (by nlinarith)
    calc 2 * (2 ^ t * δ) = 2 / Real.pi * (Real.pi * 2 ^ t * δ) := by field_simp
      _ ≤ _ := h
  have h2 : Real.sin (Real.pi * δ) ≤ Real.pi * δ := Real.sin_le (by positivity)
  calc 4 / Real.pi ^ 2 = (2 * (2 ^ t * δ)) ^ 2 / ((2 ^ t) ^ 2 * (Real.pi * δ) ^ 2) := by
        field_simp
        norm_num
    _ ≤ _ := by
        apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 2)
          (by positivity)
        gcongr

theorem four_div_pi_sq_le_fejer (t : ℕ) {δ : ℝ} (hδ : |δ| ≤ 1 / 2 ^ (t + 1)) :
    4 / Real.pi ^ 2 ≤ fejer t δ := by
  rcases lt_trichotomy δ 0 with hneg | hzero | hpos
  · rw [← fejer_neg]
    exact four_div_pi_sq_le_fejer_of_pos t (neg_pos.2 hneg) (by rwa [abs_of_neg hneg] at hδ)
  · subst hzero
    rw [fejer_zero_right, div_le_one (by positivity)]
    nlinarith [Real.two_le_pi]
  · exact four_div_pi_sq_le_fejer_of_pos t hpos (by rwa [abs_of_pos hpos] at hδ)

end PhaseEstimation

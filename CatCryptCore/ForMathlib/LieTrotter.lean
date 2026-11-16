/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.TrotterBound

/-!
# The Lie product formula

For skew-adjoint `x`, `y` in a C⋆-algebra (`x = -i t H₁`, `y = -i t H₂` for Hermitian
Hamiltonians), `(exp (x / r) exp (y / r))ʳ → exp (x + y)` as `r → ∞`, with the rate
`‖exp (x + y) - (exp (x / r) exp (y / r))ʳ‖ ≤ (‖x‖ + ‖y‖)² / r` of
`CStarAlgebra.norm_exp_sub_trotter_le`.

For arbitrary `x`, `y` in a complete normed algebra over `ℝ` with `‖1‖ = 1` the same holds with
the rate `2 ‖x‖ ‖y‖ e^{5(‖x‖ + ‖y‖)} / r`: the exponentials are bounded by `e^‖x‖`, the mean
value inequality for `u ↦ exp (-u (x + y)) exp (u x) exp (u y)` gives
`‖exp (x + y) - exp x exp y‖ ≤ 2 ‖x‖ ‖y‖ e^{4(‖x‖ + ‖y‖)}`, and
`‖Uʳ - Vʳ‖ ≤ r Mʳ ‖U - V‖` for `‖U‖, ‖V‖ ≤ M`.

## Main results

* `CStarAlgebra.norm_exp_add_sub_trotter_pow_le` — the rate `(‖x‖ + ‖y‖)² / r`.
* `CStarAlgebra.tendsto_trotter_pow` — **the Lie product formula** for skew-adjoint elements.
* `CStarAlgebra.tendsto_trotter_pow_list` — the same for a finite list of skew-adjoint
  elements.
* `LieTrotter.norm_exp_le_exp_norm` — `‖exp x‖ ≤ e^‖x‖` in a complete normed algebra.
* `LieTrotter.norm_exp_add_sub_exp_mul_exp_le` —
  `‖exp (x + y) - exp x exp y‖ ≤ 2 ‖x‖ ‖y‖ e^{4(‖x‖ + ‖y‖)}`.
* `LieTrotter.norm_exp_add_sub_trotter_pow_le` — the rate `2 ‖x‖ ‖y‖ e^{5(‖x‖ + ‖y‖)} / r`.
* `LieTrotter.tendsto_trotter_pow` — **the Lie product formula** for arbitrary elements of a
  complete normed algebra over `ℝ` (matrices included).
-/

@[expose] public section

set_option autoImplicit false

open NormedSpace Filter Topology

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [NormedAlgebra ℚ A] [Nontrivial A]

/-- **Lie product formula, list form.** For skew-adjoint `x₁, …, x_L`,
`(∏ exp (xₖ / r))ʳ → exp (∑ xₖ)`. -/
theorem tendsto_trotter_pow_list (l : List A) (hl : ∀ x ∈ l, x ∈ skewAdjoint A) :
    Tendsto (fun r : ℕ => ((l.map fun x => exp ((r : ℝ)⁻¹ • x)).prod) ^ r) atTop
      (𝓝 (exp l.sum)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat ((l.map norm).sum ^ 2))
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [norm_sub_rev]
  exact norm_exp_sub_trotter_le l hl r hr

/-- The rate of the Lie product formula for two skew-adjoint elements. -/
theorem norm_exp_add_sub_trotter_pow_le {x y : A} (hx : x ∈ skewAdjoint A)
    (hy : y ∈ skewAdjoint A) (r : ℕ) (hr : 0 < r) :
    ‖exp (x + y) - (exp ((r : ℝ)⁻¹ • x) * exp ((r : ℝ)⁻¹ • y)) ^ r‖ ≤
      (‖x‖ + ‖y‖) ^ 2 / r := by
  have h := norm_exp_sub_trotter_le [x, y] (by simp [hx, hy]) r hr
  simpa using h

/-- **Lie product formula** for skew-adjoint elements of a C⋆-algebra:
`(exp (x / r) exp (y / r))ʳ → exp (x + y)`. -/
theorem tendsto_trotter_pow {x y : A} (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A) :
    Tendsto (fun r : ℕ => (exp ((r : ℝ)⁻¹ • x) * exp ((r : ℝ)⁻¹ • y)) ^ r) atTop
      (𝓝 (exp (x + y))) := by
  have h := tendsto_trotter_pow_list [x, y] (by simp [hx, hy])
  simpa using h

end CStarAlgebra

/-! ## Arbitrary elements of a complete normed algebra -/

namespace LieTrotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸]
  [CompleteSpace 𝔸]

omit [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] in
/-- `‖exp x‖ ≤ e^‖x‖`. -/
theorem norm_exp_le_exp_norm (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  rw [exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ (𝔸 := ℝ)]
  refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂 := ℝ) x)).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (norm_expSeries_summable' (𝕂 := ℝ) x)
    (expSeries_summable' (𝕂 := ℝ) ‖x‖)
  rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

omit [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] in
theorem norm_exp_smul_le {z : 𝔸} {u c : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hz : ‖z‖ ≤ c) :
    ‖exp (u • z)‖ ≤ Real.exp c := by
  refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) hu.2).trans hz

omit [NormedAlgebra ℚ 𝔸] in
/-- `‖exp x - 1‖ ≤ ‖x‖ e^‖x‖`. -/
theorem norm_exp_sub_one_le (x : 𝔸) : ‖exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => exp (u • x))
      (exp (u • x) * x) (Set.Icc 0 1) u := fun u _ =>
    (hasDerivAt_exp_smul_const x u).hasDerivWithinAt
  have hb : ∀ u ∈ Set.Ico (0 : ℝ) 1, ‖exp (u • x) * x‖ ≤ ‖x‖ * Real.exp ‖x‖ := fun u hu => by
    calc ‖exp (u • x) * x‖ ≤ ‖exp (u • x)‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖x‖ * ‖x‖ := by
          gcongr; exact norm_exp_smul_le (Set.Ico_subset_Icc_self hu) le_rfl
      _ = _ := mul_comm _ _
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb 1 (by simp)
  simpa using this

/-- `‖exp (x + y) - exp x exp y‖ ≤ 2 ‖x‖ ‖y‖ e^{4(‖x‖ + ‖y‖)}`. -/
theorem norm_exp_add_sub_exp_mul_exp_le (x y : 𝔸) :
    ‖exp (x + y) - exp x * exp y‖ ≤ 2 * ‖x‖ * ‖y‖ * Real.exp (‖x‖ + ‖y‖) ^ 4 := by
  set E := Real.exp (‖x‖ + ‖y‖) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  let G : ℝ → 𝔸 := fun u => exp (u • -(x + y)) * (exp (u • x) * exp (u • y))
  let G' : ℝ → 𝔸 := fun u =>
    exp (u • -(x + y)) * ((exp (u • x) * y - y * exp (u • x)) * exp (u • y))
  have hG : ∀ u, HasDerivAt G (G' u) u := by
    intro u
    have h1 := hasDerivAt_exp_smul_const (-(x + y)) u
    have h2 := hasDerivAt_exp_smul_const' x u
    have h3 := hasDerivAt_exp_smul_const' y u
    convert h1.mul (h2.mul h3) using 1
    simp only [G', Pi.mul_apply]
    noncomm_ring
  have hb : ∀ u ∈ Set.Ico (0 : ℝ) 1, ‖G' u‖ ≤ 2 * ‖x‖ * ‖y‖ * E ^ 3 := by
    intro u hu
    have hu' := Set.Ico_subset_Icc_self hu
    have hs : ‖-(x + y)‖ ≤ ‖x‖ + ‖y‖ := by rw [norm_neg]; exact norm_add_le _ _
    have h1 : ‖exp (u • -(x + y))‖ ≤ E := norm_exp_smul_le hu' hs
    have h3 : ‖exp (u • y)‖ ≤ E := norm_exp_smul_le hu' (le_add_of_nonneg_left (norm_nonneg x))
    have hux : ‖u • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hu.2.le
    have hE' : ‖exp (u • x) - 1‖ ≤ ‖x‖ * E :=
      (norm_exp_sub_one_le _).trans (mul_le_mul hux
        (Real.exp_le_exp.mpr (hux.trans (le_add_of_nonneg_right (norm_nonneg y))))
        (Real.exp_pos _).le (norm_nonneg _))
    have hcomm : exp (u • x) * y - y * exp (u • x) =
        (exp (u • x) - 1) * y - y * (exp (u • x) - 1) := by noncomm_ring
    have h2 : ‖exp (u • x) * y - y * exp (u • x)‖ ≤ 2 * ‖x‖ * ‖y‖ * E := by
      rw [hcomm]
      calc _ ≤ ‖exp (u • x) - 1‖ * ‖y‖ + ‖y‖ * ‖exp (u • x) - 1‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ ‖x‖ * E * ‖y‖ + ‖y‖ * (‖x‖ * E) := by gcongr
        _ = _ := by ring
    calc ‖G' u‖ ≤ ‖exp (u • -(x + y))‖ *
          (‖exp (u • x) * y - y * exp (u • x)‖ * ‖exp (u • y)‖) :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ E * ((2 * ‖x‖ * ‖y‖ * E) * E) := by gcongr
      _ = _ := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u _ => (hG u).hasDerivWithinAt) hb 1 (by simp)
  have hG0 : G 0 = 1 := by simp [G]
  have hG1 : G 1 = exp (-(x + y)) * (exp x * exp y) := by simp only [G, one_smul]
  rw [hG0, hG1, sub_zero, mul_one] at hmv
  have hinv : exp (x + y) * exp (-(x + y)) = 1 := by
    rw [← exp_add_of_commute (Commute.refl (x + y)).neg_right, add_neg_cancel, exp_zero]
  calc ‖exp (x + y) - exp x * exp y‖ =
        ‖exp (x + y) * (1 - exp (-(x + y)) * (exp x * exp y))‖ := by
        rw [mul_sub, mul_one, ← mul_assoc, hinv, one_mul]
    _ ≤ ‖exp (x + y)‖ * ‖1 - exp (-(x + y)) * (exp x * exp y)‖ := norm_mul_le _ _
    _ ≤ E * (2 * ‖x‖ * ‖y‖ * E ^ 3) := by
        rw [norm_sub_rev]
        exact mul_le_mul ((norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (norm_add_le _ _)))
          hmv (norm_nonneg _) hE0
    _ = _ := by ring

omit [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] in
/-- `‖Uʳ - Vʳ‖ ≤ r Mʳ ‖U - V‖` for `‖U‖, ‖V‖ ≤ M` and `1 ≤ M`. -/
theorem norm_pow_sub_pow_le {U V : 𝔸} {M : ℝ} (hM : 1 ≤ M) (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M)
    (r : ℕ) : ‖U ^ r - V ^ r‖ ≤ r * M ^ r * ‖U - V‖ := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hVr : ∀ r : ℕ, ‖V ^ r‖ ≤ M ^ r := fun r =>
    (norm_pow_le V r).trans (pow_le_pow_left₀ (norm_nonneg _) hV r)
  induction r with
  | zero => simp
  | succ r ih =>
    have hsplit : U ^ (r + 1) - V ^ (r + 1) = (U ^ r - V ^ r) * U + V ^ r * (U - V) := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [hsplit]
    have hMr : M ^ r ≤ M ^ (r + 1) := pow_le_pow_right₀ hM (Nat.le_succ r)
    calc _ ≤ ‖U ^ r - V ^ r‖ * ‖U‖ + ‖V ^ r‖ * ‖U - V‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (r * M ^ r * ‖U - V‖) * M + M ^ r * ‖U - V‖ := by gcongr; exact hVr r
      _ ≤ (r * M ^ r * ‖U - V‖) * M + M ^ (r + 1) * ‖U - V‖ := by gcongr
      _ = ((r + 1 : ℕ) : ℝ) * M ^ (r + 1) * ‖U - V‖ := by push_cast; ring

/-- The rate of the Lie product formula in a complete normed algebra:
`‖exp (x + y) - (exp (x / r) exp (y / r))ʳ‖ ≤ 2 ‖x‖ ‖y‖ e^{5(‖x‖ + ‖y‖)} / r`. -/
theorem norm_exp_add_sub_trotter_pow_le (x y : 𝔸) (r : ℕ) (hr : 0 < r) :
    ‖exp (x + y) - (exp ((r : ℝ)⁻¹ • x) * exp ((r : ℝ)⁻¹ • y)) ^ r‖ ≤
      2 * ‖x‖ * ‖y‖ * Real.exp (‖x‖ + ‖y‖) ^ 5 / r := by
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
  set a := (r : ℝ)⁻¹ • x with ha
  set b := (r : ℝ)⁻¹ • y with hb
  have hna : ‖a‖ = ‖x‖ / r := by
    rw [ha, norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  have hnb : ‖b‖ = ‖y‖ / r := by
    rw [hb, norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  set M := Real.exp (‖a‖ + ‖b‖) with hM
  have hM1 : 1 ≤ M := Real.one_le_exp (by positivity)
  have hxy : x + y = r • (a + b) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_add, ha, hb, smul_smul, smul_smul,
      mul_inv_cancel₀ hr'.ne', one_smul, one_smul]
  rw [hxy, exp_nsmul]
  have hP : ‖exp a * exp b‖ ≤ M := (norm_mul_le _ _).trans (by
    rw [hM, Real.exp_add]
    exact mul_le_mul (norm_exp_le_exp_norm a) (norm_exp_le_exp_norm b) (norm_nonneg _)
      (Real.exp_pos _).le)
  have hQ : ‖exp (a + b)‖ ≤ M :=
    (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (norm_add_le _ _))
  have hMr : M ^ r = Real.exp (‖x‖ + ‖y‖) := by
    rw [hM, ← Real.exp_nat_mul, hna, hnb]
    congr 1
    field_simp
  have hab : ‖a‖ + ‖b‖ ≤ ‖x‖ + ‖y‖ := by
    rw [hna, hnb, ← add_div]
    exact div_le_self (by positivity) hr1
  have hM4 : M ^ 4 ≤ Real.exp (‖x‖ + ‖y‖) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr hab) 4
  calc ‖exp (a + b) ^ r - (exp a * exp b) ^ r‖
      ≤ r * M ^ r * ‖exp (a + b) - exp a * exp b‖ := norm_pow_sub_pow_le hM1 hQ hP r
    _ ≤ r * M ^ r * (2 * ‖a‖ * ‖b‖ * M ^ 4) := by
        gcongr; exact norm_exp_add_sub_exp_mul_exp_le a b
    _ ≤ r * Real.exp (‖x‖ + ‖y‖) * (2 * (‖x‖ / r) * (‖y‖ / r) * Real.exp (‖x‖ + ‖y‖) ^ 4) := by
        rw [hMr, hna, hnb]; gcongr
    _ = _ := by field_simp

/-- **Lie product formula** in a complete normed algebra over `ℝ`:
`(exp (x / r) exp (y / r))ʳ → exp (x + y)` for all `x`, `y`. -/
theorem tendsto_trotter_pow (x y : 𝔸) :
    Tendsto (fun r : ℕ => (exp ((r : ℝ)⁻¹ • x) * exp ((r : ℝ)⁻¹ • y)) ^ r) atTop
      (𝓝 (exp (x + y))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖x‖ * ‖y‖ * Real.exp (‖x‖ + ‖y‖) ^ 5))
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [norm_sub_rev]
  exact norm_exp_add_sub_trotter_pow_le x y r hr

end LieTrotter

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

set_option autoImplicit false

/-!
# The first-order Trotter error in a C⋆-algebra

For skew-adjoint elements `x`, `y` of a C⋆-algebra (`x = -i A` for a Hermitian `A`), the
exponentials are unitary and

* `‖exp x - 1‖ ≤ ‖x‖`,
* `‖exp (x + y) - exp x exp y‖ ≤ 2 ‖x‖ ‖y‖`,
* for a list of skew-adjoint elements, `‖exp (∑ xₖ) - ∏ exp xₖ‖ ≤ (∑ ‖xₖ‖)²`,
* `‖Uʳ - Vʳ‖ ≤ r ‖U - V‖` for `‖U‖, ‖V‖ ≤ 1`.

With `xₖ = -i (t / r) Hₖ` these give the first-order Trotter bound
`‖exp (-i t ∑ Hₖ) - (∏ exp (-i (t / r) Hₖ))ʳ‖ ≤ t² (∑ ‖Hₖ‖)² / r`. The second bound comes
from the mean value inequality for `G u = exp (-u (x + y)) exp (u x) exp (u y)`, whose
derivative is `exp (-u (x + y)) [exp (u x), y] exp (u y)`.

## Main results

* `norm_exp_sub_one_le` — `‖exp x - 1‖ ≤ ‖x‖` for skew-adjoint `x`.
* `norm_exp_add_sub_exp_mul_exp_le` — `‖exp (x + y) - exp x exp y‖ ≤ 2 ‖x‖ ‖y‖`.
* `norm_exp_list_sum_sub_prod_le` — `‖exp (∑ xₖ) - ∏ exp xₖ‖ ≤ (∑ ‖xₖ‖)²`.
* `norm_pow_sub_pow_le` — `‖Uʳ - Vʳ‖ ≤ r ‖U - V‖` for contractions.
* `norm_exp_sub_trotter_le` — the first-order Trotter bound.
* `exp_smul_of_mul_self_eq_neg_one` — `exp (θ J) = cos θ + sin θ J` when `J² = -1`.

## References

* Childs, Su, Tran, Wiebe, Zhu, *Theory of Trotter error with commutator scaling*,
  Phys. Rev. X 11 (2021)
-/

open NormedSpace

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [NormedAlgebra ℚ A] [Nontrivial A]

theorem norm_exp_le_one {x : A} (hx : x ∈ skewAdjoint A) : ‖exp x‖ ≤ 1 :=
  (CStarRing.norm_of_mem_unitary (exp_mem_unitary_of_mem_skewAdjoint hx)).le

omit [NormedAlgebra ℚ A] [Nontrivial A] in
theorem real_smul_mem_skewAdjoint {x : A} (hx : x ∈ skewAdjoint A) (u : ℝ) :
    u • x ∈ skewAdjoint A :=
  skewAdjoint.smul_mem u hx

/-- `‖exp x - 1‖ ≤ ‖x‖` for skew-adjoint `x`. -/
theorem norm_exp_sub_one_le {x : A} (hx : x ∈ skewAdjoint A) : ‖exp x - 1‖ ≤ ‖x‖ := by
  have hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => exp (u • x))
      (exp (u • x) * x) (Set.Icc 0 1) u := fun u _ =>
    (hasDerivAt_exp_smul_const x u).hasDerivWithinAt
  have hb : ∀ u ∈ Set.Ico (0 : ℝ) 1, ‖exp (u • x) * x‖ ≤ ‖x‖ := fun u _ => by
    calc ‖exp (u • x) * x‖ ≤ ‖exp (u • x)‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ 1 * ‖x‖ := by
          gcongr; exact norm_exp_le_one (real_smul_mem_skewAdjoint hx u)
      _ = ‖x‖ := one_mul _
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb 1 (by simp)
  simpa using this

/-- `‖exp (x + y) - exp x exp y‖ ≤ 2 ‖x‖ ‖y‖` for skew-adjoint `x`, `y`. -/
theorem norm_exp_add_sub_exp_mul_exp_le {x y : A} (hx : x ∈ skewAdjoint A)
    (hy : y ∈ skewAdjoint A) : ‖exp (x + y) - exp x * exp y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  have hzs : x + y ∈ skewAdjoint A := add_mem hx hy
  let G : ℝ → A := fun u => exp (u • -(x + y)) * (exp (u • x) * exp (u • y))
  let G' : ℝ → A := fun u =>
    exp (u • -(x + y)) * ((exp (u • x) * y - y * exp (u • x)) * exp (u • y))
  have hG : ∀ u, HasDerivAt G (G' u) u := by
    intro u
    have h1 := hasDerivAt_exp_smul_const (-(x + y)) u
    have h2 := hasDerivAt_exp_smul_const' x u
    have h3 := hasDerivAt_exp_smul_const' y u
    convert h1.mul (h2.mul h3) using 1
    simp only [G', Pi.mul_apply]
    noncomm_ring
  have hb : ∀ u ∈ Set.Ico (0 : ℝ) 1, ‖G' u‖ ≤ 2 * ‖x‖ * ‖y‖ := by
    intro u hu
    have hux : ‖u • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hu.2.le
    have hE := norm_exp_sub_one_le (real_smul_mem_skewAdjoint hx u)
    have hcomm : exp (u • x) * y - y * exp (u • x) =
        (exp (u • x) - 1) * y - y * (exp (u • x) - 1) := by noncomm_ring
    calc ‖G' u‖ ≤ ‖exp (u • -(x + y))‖ * (‖exp (u • x) * y - y * exp (u • x)‖ * ‖exp (u • y)‖) := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ 1 * (‖exp (u • x) * y - y * exp (u • x)‖ * 1) := by
          gcongr
          · exact norm_exp_le_one (real_smul_mem_skewAdjoint (neg_mem hzs) u)
          · exact norm_exp_le_one (real_smul_mem_skewAdjoint hy u)
      _ ≤ ‖exp (u • x) - 1‖ * ‖y‖ + ‖y‖ * ‖exp (u • x) - 1‖ := by
          rw [one_mul, mul_one, hcomm]
          exact (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 2 * ‖x‖ * ‖y‖ := by
          nlinarith [norm_nonneg y, hE.trans hux]
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
    _ ≤ 1 * ‖exp (-(x + y)) * (exp x * exp y) - 1‖ := by
        rw [norm_sub_rev]
        gcongr
        exact norm_exp_le_one hzs
    _ ≤ 2 * ‖x‖ * ‖y‖ := by rw [one_mul]; exact hmv

omit [NormedAlgebra ℚ A] [Nontrivial A] in
theorem norm_list_sum_le (l : List A) : ‖l.sum‖ ≤ (l.map norm).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- `‖exp (∑ xₖ) - ∏ exp xₖ‖ ≤ (∑ ‖xₖ‖)²` for a list of skew-adjoint elements. -/
theorem norm_exp_list_sum_sub_prod_le (l : List A) (hl : ∀ x ∈ l, x ∈ skewAdjoint A) :
    ‖exp l.sum - (l.map exp).prod‖ ≤ (l.map norm).sum ^ 2 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx : x ∈ skewAdjoint A := hl x (by simp)
    have hl' : ∀ y ∈ l, y ∈ skewAdjoint A := fun y hy => hl y (by simp [hy])
    have hS : l.sum ∈ skewAdjoint A := AddSubgroup.list_sum_mem _ hl'
    have hSn : ‖l.sum‖ ≤ (l.map norm).sum := norm_list_sum_le l
    have hIH := ih hl'
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    have hsplit : exp (x + l.sum) - exp x * (l.map exp).prod =
        (exp (x + l.sum) - exp x * exp l.sum) + exp x * (exp l.sum - (l.map exp).prod) := by
      noncomm_ring
    rw [hsplit]
    calc ‖(exp (x + l.sum) - exp x * exp l.sum) + exp x * (exp l.sum - (l.map exp).prod)‖
        ≤ 2 * ‖x‖ * ‖l.sum‖ + 1 * (l.map norm).sum ^ 2 := by
          refine (norm_add_le _ _).trans (add_le_add
            (norm_exp_add_sub_exp_mul_exp_le hx hS) ?_)
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_exp_le_one hx
      _ ≤ (‖x‖ + (l.map norm).sum) ^ 2 := by
          nlinarith [norm_nonneg x, norm_nonneg l.sum]

omit [NormedAlgebra ℚ A] in
/-- `‖Uʳ - Vʳ‖ ≤ r ‖U - V‖` for `‖U‖, ‖V‖ ≤ 1`. -/
theorem norm_pow_sub_pow_le {U V : A} (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (r : ℕ) :
    ‖U ^ r - V ^ r‖ ≤ r * ‖U - V‖ := by
  have hVr : ∀ r : ℕ, ‖V ^ r‖ ≤ 1 := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (V ^ r), norm_nonneg V])
  induction r with
  | zero => simp
  | succ r ih =>
    have hsplit : U ^ (r + 1) - V ^ (r + 1) = (U ^ r - V ^ r) * U + V ^ r * (U - V) := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [hsplit]
    calc ‖(U ^ r - V ^ r) * U + V ^ r * (U - V)‖
        ≤ ‖U ^ r - V ^ r‖ * ‖U‖ + ‖V ^ r‖ * ‖U - V‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ r * ‖U - V‖ * 1 + 1 * ‖U - V‖ := by
          gcongr
          · exact hVr r
      _ = ((r + 1 : ℕ) : ℝ) * ‖U - V‖ := by push_cast; ring

/-- **First-order Trotter bound.** For skew-adjoint `x₁, …, x_L` and `r > 0`,
`‖exp (∑ xₖ) - (∏ exp (xₖ / r))ʳ‖ ≤ (∑ ‖xₖ‖)² / r`. -/
theorem norm_exp_sub_trotter_le (l : List A) (hl : ∀ x ∈ l, x ∈ skewAdjoint A) (r : ℕ)
    (hr : 0 < r) :
    ‖exp l.sum - ((l.map fun x => exp ((r : ℝ)⁻¹ • x)).prod) ^ r‖ ≤
      (l.map norm).sum ^ 2 / r := by
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  set l' := l.map fun x => (r : ℝ)⁻¹ • x with hl'def
  have hl' : ∀ x ∈ l', x ∈ skewAdjoint A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact real_smul_mem_skewAdjoint (hl y hy) _
  have hsum' : l'.sum = (r : ℝ)⁻¹ • l.sum := by
    rw [hl'def, List.smul_sum]
  have hsum : l.sum = r • l'.sum := by
    rw [hsum', ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hr'.ne', one_smul]
  have hprod : (l.map fun x => exp ((r : ℝ)⁻¹ • x)) = l'.map exp := by
    rw [hl'def, List.map_map]; rfl
  have hnorm : (l'.map norm).sum = (r : ℝ)⁻¹ * (l.map norm).sum := by
    rw [hl'def, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp [norm_smul]
  have hP : ∀ k : List A, (∀ x ∈ k, x ∈ skewAdjoint A) → ‖(k.map exp).prod‖ ≤ 1 := by
    intro k hk
    induction k with
    | nil => simp
    | cons x k ih =>
      rw [List.map_cons, List.prod_cons]
      refine (norm_mul_le _ _).trans ?_
      have h1 := norm_exp_le_one (hk x (by simp))
      have h2 := ih fun y hy => hk y (by simp [hy])
      nlinarith [norm_nonneg (exp x), norm_nonneg (k.map exp).prod]
  rw [hsum, exp_nsmul, hprod]
  calc ‖exp l'.sum ^ r - (l'.map exp).prod ^ r‖
      ≤ r * ‖exp l'.sum - (l'.map exp).prod‖ :=
        norm_pow_sub_pow_le (norm_exp_le_one (AddSubgroup.list_sum_mem _ hl')) (hP l' hl') r
    _ ≤ r * (l'.map norm).sum ^ 2 := by
        gcongr; exact norm_exp_list_sum_sub_prod_le l' hl'
    _ = (l.map norm).sum ^ 2 / r := by
        rw [hnorm]; field_simp

omit [Nontrivial A] in
/-- **Exponential of a square root of `-1`**: if `J² = -1`, then
`exp (θ J) = cos θ + sin θ J`. -/
theorem exp_smul_of_mul_self_eq_neg_one {J : A} (hJ : J * J = -1) (θ : ℝ) :
    exp (θ • J) = Real.cos θ • (1 : A) + Real.sin θ • J := by
  let g : ℝ → A := fun θ => Real.cos θ • (1 : A) + Real.sin θ • J
  let h : ℝ → A := fun θ => exp (θ • -J) * g θ
  have hg : ∀ θ, HasDerivAt g (-Real.sin θ • (1 : A) + Real.cos θ • J) θ := fun θ =>
    ((Real.hasDerivAt_cos θ).smul_const (1 : A)).add ((Real.hasDerivAt_sin θ).smul_const J)
  have hh : ∀ θ, HasDerivAt h 0 θ := by
    intro θ
    have h1 := hasDerivAt_exp_smul_const (-J) θ
    convert h1.mul (hg θ) using 1
    simp only [g]
    rw [mul_assoc, ← mul_add]
    have : -J * (Real.cos θ • (1 : A) + Real.sin θ • J) +
        (-Real.sin θ • (1 : A) + Real.cos θ • J) = 0 := by
      rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, neg_mul, hJ]
      simp only [neg_neg, neg_smul, smul_neg]
      abel
    rw [this, mul_zero]
  have hconst : h θ = h 0 := is_const_of_deriv_eq_zero
    (fun θ => (hh θ).differentiableAt) (fun θ => (hh θ).deriv) θ 0
  have h0 : h 0 = 1 := by simp [h, g]
  have hinv : exp (θ • J) * exp (θ • -J) = 1 := by
    rw [smul_neg, ← exp_add_of_commute (Commute.refl _).neg_right, add_neg_cancel, exp_zero]
  calc exp (θ • J) = exp (θ • J) * h θ := by rw [hconst, h0, mul_one]
    _ = g θ := by simp only [h]; rw [← mul_assoc, hinv, one_mul]

end CStarAlgebra

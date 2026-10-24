/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PMFUniformDefs

/-!
# `PMF.bind` on the support and images of the uniform distribution

Mathlib candidates about `PMF.bind`, `PMF.map` and `PMF.support`.

## Main results

* `PMF.bind_congr_support` — two continuations that agree on the support of `p`
  give the same bind; it belongs in
  `Mathlib/Probability/ProbabilityMassFunction/Monad.lean`.
* `PMF.map_uniformFintype_apply` — the image of the uniform distribution under
  `c` puts weight `|c⁻¹(a)| / |R|` on `a`; it belongs in
  `Mathlib/Probability/Distributions/Uniform.lean`.
* `PMF.toOuterMeasure_bind_le_add` — an event after `p.bind f` has probability at most
  `p(B) + a` when every outcome outside `B` gives it probability at most `a`; it belongs
  in `Mathlib/Probability/ProbabilityMassFunction/Monad.lean`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace PMF

/-- Two continuations that agree on the support of `p` give the same bind. -/
theorem bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff p a).mpr ha, zero_mul, zero_mul]

/-- The image of the uniform distribution under `c` puts weight
`|c⁻¹(a)| / |R|` on `a`. -/
theorem map_uniformFintype_apply {R A : Type*} [Fintype R] [Nonempty R] [DecidableEq A]
    (c : R → A) (a : A) :
    ((PMF.uniformFintype R).map c) a =
      ((Finset.univ.filter fun r => c r = a).card : ℝ≥0∞) / Fintype.card R := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]
  congr 3
  ext r
  simp [eq_comm]

/-- An event after a bind has probability at most the probability of `B` plus `a`,
when every outcome outside `B` gives it probability at most `a`. -/
theorem toOuterMeasure_bind_le_add {β γ : Type} (p : PMF β) (f : β → PMF γ) (B : Set β)
    (S : Set γ) (a : ℝ≥0∞) (h : ∀ y ∉ B, (f y).toOuterMeasure S ≤ a) :
    (p.bind f).toOuterMeasure S ≤ p.toOuterMeasure B + a := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  calc ∑' y, p y * (f y).toOuterMeasure S ≤ ∑' y, (B.indicator p y + p y * a) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hy : y ∈ B
        · rw [Set.indicator_of_mem hy]
          refine (mul_le_of_le_one_right' ?_).trans le_self_add
          exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
            ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
        · rw [Set.indicator_of_notMem hy, zero_add]
          gcongr
          exact h y hy
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end PMF

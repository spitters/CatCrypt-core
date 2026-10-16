/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Probability.Distributions.Uniform

/-!
# `PMF.bind` on the support and images of the uniform distribution

Mathlib candidates about `PMF.bind`, `PMF.map` and `PMF.support`.

## Main results

* `PMF.bind_congr_support` — two continuations that agree on the support of `p`
  give the same bind; it belongs in
  `Mathlib/Probability/ProbabilityMassFunction/Monad.lean`.
* `PMF.map_uniformOfFintype_apply` — the image of the uniform distribution under
  `c` puts weight `|c⁻¹(a)| / |R|` on `a`; it belongs in
  `Mathlib/Probability/Distributions/Uniform.lean`.
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
theorem map_uniformOfFintype_apply {R A : Type*} [Fintype R] [Nonempty R] [DecidableEq A]
    (c : R → A) (a : A) :
    ((PMF.uniformOfFintype R).map c) a =
      ((Finset.univ.filter fun r => c r = a).card : ℝ≥0∞) / Fintype.card R := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]
  congr 3
  ext r
  simp [eq_comm]

end PMF

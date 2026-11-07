/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The probability of an event under a probability mass function

Mathlib candidates about `PMF.toOuterMeasure`.

## Main results

* `PMF.toOuterMeasure_eq_tsum_ite` — the probability of the event `{x | P x}` is the sum of the
  weights times the indicator `if P x then 1 else 0`; its neighbour `PMF.toOuterMeasure_apply`
  states the sum with `Set.indicator`. It belongs in
  `Mathlib/Probability/ProbabilityMassFunction/Basic.lean`.
* `PMF.toOuterMeasure_eq_of_map_eq` — if `p.map f = q`, the probability of `f ⁻¹' A` under `p` is
  the probability of `A` under `q`; it is `PMF.toOuterMeasure_map_apply` at an image given by an
  equation. It belongs in `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace PMF

/-- The probability of an event under a distribution, as a sum of indicator weights. -/
theorem toOuterMeasure_eq_tsum_ite {σ : Type*} (p : PMF σ) (P : σ → Prop) [DecidablePred P] :
    p.toOuterMeasure {x | P x} = ∑' x, p x * (if P x then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases h : P x <;> simp [Set.indicator, h]

/-- The probability of an event under the image of a distribution. -/
theorem toOuterMeasure_eq_of_map_eq {β γ : Type*} {p : PMF β} {q : PMF γ} {f : β → γ}
    (h : p.map f = q) (A : Set γ) : p.toOuterMeasure (f ⁻¹' A) = q.toOuterMeasure A := by
  rw [← h, PMF.toOuterMeasure_map_apply]

end PMF

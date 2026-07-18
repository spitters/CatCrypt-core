/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Prob.SDistr
import CatCryptCore.Prob.Support
import CatCryptCore.Unary.Judgment

/-!
# Event Probability for Unary Computations

This file defines the probability of events for single computations,
bridging pHL judgments to actual probability bounds.

## Main definitions

* `prEvent d E` - Probability that event `E` holds under sub-distribution `d`
* `prEventComp c h₀ E` - Probability that event `E` holds for computation `c`
  starting from heap `h₀`

## Main results

* `prEvent_le_mass` - Event probability is at most the total mass
* `prEvent_complement` - Complementary event probabilities sum to 1 (when mass = 1)
* `prEvent_union_le` - Union bound: Pr[E₁ ∨ E₂] ≤ Pr[E₁] + Pr[E₂]
* `prEvent_mono` - Monotonicity of event probability
* `prEvent_of_pHoare` - If all outcomes satisfy E, then Pr[E] = mass
* `prEvent_zero_of_pHoare_neg` - If no outcome satisfies E, then Pr[E] = 0

## References

* EasyCrypt pHL (unary probabilistic Hoare logic)
* CatCrypt.Unary.Judgment (pHL judgment definition)
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob Classical
open scoped ENNReal

variable {α : Type*}

/-- Probability of an event E under a sub-distribution over (value, heap) pairs.
    This sums the probability of all outcomes satisfying the predicate. -/
noncomputable def prEvent (d : SDistr (α × Heap)) (E : α → Heap → Prop) : ℝ≥0∞ :=
  ∑' (p : α × Heap), if E p.1 p.2 then d (some p) else 0

/-- Probability of an event for a computation from a given initial heap -/
noncomputable def prEventComp (c : SPComp α) (h₀ : Heap) (E : α → Heap → Prop) : ℝ≥0∞ :=
  prEvent (c h₀) E

/-- Event probability is at most the total mass.
    This holds because prEvent sums over a subset of outcomes (those satisfying E),
    while mass sums over all outcomes. -/
theorem prEvent_le_mass (d : SDistr (α × Heap)) (E : α → Heap → Prop) :
    prEvent d E ≤ SDistr.mass d := by
  unfold prEvent
  rw [← tsum_some_eq_mass]
  exact tsum_ite_le (fun p => E p.1 p.2) (fun p => d (some p))

/-- Complementary events: if mass = 1, Pr[E] + Pr[not E] = 1.
    Every outcome satisfies exactly one of E or not E, so their probabilities
    partition the total mass. -/
theorem prEvent_complement (d : SDistr (α × Heap)) (E : α → Heap → Prop)
    (hmass : SDistr.mass d = 1) :
    prEvent d E + prEvent d (fun a h => ¬ E a h) = 1 := by
  have key : prEvent d E + prEvent d (fun a h => ¬ E a h) = SDistr.mass d := by
    show prEvent d E + prEvent d (fun a h => ¬ E a h) = SDistr.mass d
    unfold prEvent
    rw [← tsum_some_eq_mass, ← ENNReal.tsum_add]
    congr 1; funext p
    by_cases hE : E p.1 p.2
    · rw [if_pos hE, if_neg (not_not.mpr hE), add_zero]
    · rw [if_neg hE, if_pos hE, zero_add]
  rw [key, hmass]

/-- Union bound: Pr[E₁ ∨ E₂] ≤ Pr[E₁] + Pr[E₂].
    Standard inclusion-exclusion upper bound. -/
theorem prEvent_union_le (d : SDistr (α × Heap))
    (E₁ E₂ : α → Heap → Prop) :
    prEvent d (fun a h => E₁ a h ∨ E₂ a h) ≤ prEvent d E₁ + prEvent d E₂ := by
  unfold prEvent
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro p
  by_cases h₁ : E₁ p.1 p.2 <;> by_cases h₂ : E₂ p.1 p.2 <;> simp [h₁, h₂]

/-- Monotonicity: if E₁ → E₂, then Pr[E₁] ≤ Pr[E₂] -/
theorem prEvent_mono (d : SDistr (α × Heap))
    (E₁ E₂ : α → Heap → Prop) (h : ∀ a h, E₁ a h → E₂ a h) :
    prEvent d E₁ ≤ prEvent d E₂ := by
  unfold prEvent
  apply ENNReal.tsum_le_tsum
  intro p
  by_cases hE : E₁ p.1 p.2
  · rw [if_pos hE, if_pos (h p.1 p.2 hE)]
  · rw [if_neg hE]; exact zero_le

/-- True event has probability equal to mass.
    Since every outcome satisfies True, the sum is over all outcomes. -/
theorem prEvent_true (d : SDistr (α × Heap)) :
    prEvent d (fun _ _ => True) = SDistr.mass d := by
  unfold prEvent
  rw [show (fun _ _ => True : α → Heap → Prop) = fun _ _ => True from rfl, ← tsum_some_eq_mass]
  congr 1; funext p
  exact if_pos trivial

/-- False event has probability 0 -/
theorem prEvent_false (d : SDistr (α × Heap)) :
    prEvent d (fun _ _ => False) = 0 := by
  unfold prEvent
  apply ENNReal.tsum_eq_zero.mpr
  intro p
  simp

/-- If pHoare says all outcomes satisfy E (and computation is lossless), Pr[E] = mass.
    When every nonzero-probability outcome satisfies E, the filtered sum equals
    the unfiltered sum. -/
theorem prEvent_of_pHoare {P : UPre} {c : SPComp α} {E : α → Heap → Prop}
    (hph : ∀ h₀, P h₀ → ∀ a h', (c h₀) (some (a, h')) ≠ 0 → E a h')
    (h₀ : Heap) (hP : P h₀) :
    prEvent (c h₀) E = SDistr.mass (c h₀) := by
  unfold prEvent
  rw [← tsum_some_eq_mass]
  congr 1; funext p
  by_cases hE : E p.1 p.2
  · rw [if_pos hE]
  · -- If ¬E, then d(some p) must be 0 (by contrapositive of hph)
    rw [if_neg hE]
    by_contra hne
    exact hE (hph h₀ hP p.1 p.2 (Ne.symm hne))

/-- If pHoare says no outcomes satisfy E, Pr[E] = 0.
    Every term in the sum is 0: either E doesn't hold (if-branch gives 0)
    or the probability is 0 (by the pHoare hypothesis). -/
theorem prEvent_zero_of_pHoare_neg {P : UPre} {c : SPComp α} {E : α → Heap → Prop}
    (hph : ∀ h₀, P h₀ → ∀ a h', (c h₀) (some (a, h')) ≠ 0 → ¬ E a h')
    (h₀ : Heap) (hP : P h₀) :
    prEvent (c h₀) E = 0 := by
  unfold prEvent
  apply ENNReal.tsum_eq_zero.mpr
  intro p
  by_cases hE : E p.1 p.2
  · -- E holds, so the probability must be 0 (by hph, if prob ≠ 0 then ¬E)
    rw [if_pos hE]
    by_contra hne
    exact hph h₀ hP p.1 p.2 hne hE
  · rw [if_neg hE]

end CatCrypt.Unary

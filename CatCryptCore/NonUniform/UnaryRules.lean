/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.Sample
import CatCryptCore.Unary.Event
import CatCryptCore.Crypto.ForkingLemma

/-!
# Unary rules for sampling from an arbitrary distribution

Event and success probabilities of a program that starts with `sampleFrom d`
average the continuation's probabilities against the weights `d (some a)`.

## Main results

* `sampleFrom_bind_apply_some` — the pointwise mass of `sampleFrom d >>= k`
* `prEvent_pure_indicator` — event probability of a point mass
* `prEvent_sampleFrom_bind` — `Pr[E] = ∑' a, d a * Pr[E after k a]`
* `prTrue_bind_sampleFrom` — the same for the `prTrue` of a Boolean game
* `prTrue_bind_sample_of_sampleFrom` — `Crypto.prTrue_bind_sample` re-derived as
  the uniform instance, with the statement of the existing lemma verbatim
* `mass_bind_sampleFrom` — mass averages the same way
-/

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Unary CatCrypt.Crypto CatCrypt.Crypto.ForkingLemma
open scoped ENNReal
open Classical

variable {α β : Type*}

/-! ## Pointwise mass -/

/-- The probability that `sampleFrom d >>= k` produces the outcome `p` is the
    `d`-average of the continuation's probabilities of producing `p`. -/
theorem sampleFrom_bind_apply_some (d : SDistr α) (k : α → SPComp β) (h₀ : Heap)
    (p : β × Heap) :
    (SPComp.bind (sampleFrom d) k) h₀ (some p) = ∑' a, d (some a) * (k a h₀) (some p) := by
  simp only [sampleFrom_bind_apply, SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add,
    SDistr.fail_apply_some, mul_zero, zero_add]

/-- The failure probability of `sampleFrom d >>= k` is the failure probability of
    `d` plus the `d`-average of the continuations' failure probabilities. -/
theorem sampleFrom_bind_apply_none (d : SDistr α) (k : α → SPComp β) (h₀ : Heap) :
    (SPComp.bind (sampleFrom d) k) h₀ none = d none + ∑' a, d (some a) * (k a h₀) none := by
  simp only [sampleFrom_bind_apply, SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add,
    SDistr.fail_apply_none, mul_one]

/-! ## Event probability -/

/-- Event probability of a point mass is the indicator of the event. Generalizes
    `Unary.prEvent_pure`, whose event depends on the heap only. -/
theorem prEvent_pure_indicator (a : α) (h₀ : Heap) (E : α → Heap → Prop) :
    prEvent (SDistr.pure (a, h₀) : SDistr (α × Heap)) E = if E a h₀ then 1 else 0 := by
  unfold prEvent
  have hsingle : ∀ p : α × Heap, p ≠ (a, h₀) →
      (if E p.1 p.2 then (SDistr.pure (a, h₀) : SDistr (α × Heap)) (some p) else 0) = 0 :=
    fun p hp => by
      rw [SDistr.pure_apply_some, if_neg (Ne.symm hp), ite_self]
  rw [tsum_eq_single (a, h₀) hsingle]
  by_cases hE : E a h₀ <;> simp [hE, SDistr.pure_apply_some]

/-- `prEvent_pure_indicator` in the `SPComp` form used by the averaging rule. -/
theorem prEvent_pure_comp (a : α) (h₀ : Heap) (E : α → Heap → Prop) :
    prEvent ((SPComp.pure a : SPComp α) h₀) E = if E a h₀ then 1 else 0 :=
  prEvent_pure_indicator a h₀ E

/-- Average-over-the-distribution characterisation of the event probability of a
    program that starts with a general sample. -/
theorem prEvent_sampleFrom_bind (d : SDistr α) (k : α → SPComp β) (h₀ : Heap)
    (E : β → Heap → Prop) :
    prEvent ((SPComp.bind (sampleFrom d) k) h₀) E
      = ∑' a, d (some a) * prEvent ((k a) h₀) E := by
  unfold prEvent
  calc ∑' p : β × Heap, (if E p.1 p.2 then (SPComp.bind (sampleFrom d) k) h₀ (some p) else 0)
      = ∑' p : β × Heap, ∑' a, d (some a) * (if E p.1 p.2 then (k a h₀) (some p) else 0) := by
        refine tsum_congr fun p => ?_
        by_cases hE : E p.1 p.2
        · simpa only [if_pos hE] using sampleFrom_bind_apply_some d k h₀ p
        · simp only [if_neg hE, mul_zero, tsum_zero]
    _ = ∑' a, ∑' p : β × Heap, d (some a) * (if E p.1 p.2 then (k a h₀) (some p) else 0) :=
        ENNReal.tsum_comm
    _ = ∑' a, d (some a) * ∑' p : β × Heap, (if E p.1 p.2 then (k a h₀) (some p) else 0) :=
        tsum_congr fun a => ENNReal.tsum_mul_left

/-- Event probability of a bare general sample: the heap is unchanged, so the
    event is decided by the sampled value alone. -/
theorem prEvent_sampleFrom (d : SDistr α) (h₀ : Heap) (E : α → Heap → Prop) :
    prEvent (sampleFrom d h₀) E = ∑' a, (if E a h₀ then d (some a) else 0) := by
  have hb : sampleFrom d h₀ = (SPComp.bind (sampleFrom d) SPComp.pure) h₀ :=
    congrFun (SPComp.bind_pure (sampleFrom d)).symm h₀
  rw [hb, prEvent_sampleFrom_bind]
  refine tsum_congr fun a => ?_
  rw [prEvent_pure_comp]
  by_cases hE : E a h₀ <;> simp [hE]

/-! ## Success probability of a Boolean game -/

/-- Average-over-the-distribution characterisation of the success probability of
    a Boolean game that starts with a general sample. -/
theorem prTrue_bind_sampleFrom (d : SDistr α) (k : α → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (sampleFrom d) k) h₀ = ∑' a, d (some a) * prTrue (k a) h₀ := by
  unfold prTrue
  calc ∑' h, (SPComp.bind (sampleFrom d) k) h₀ (some (true, h))
      = ∑' h, ∑' a, d (some a) * (k a h₀) (some (true, h)) :=
        tsum_congr fun h => sampleFrom_bind_apply_some d k h₀ (true, h)
    _ = ∑' a, ∑' h, d (some a) * (k a h₀) (some (true, h)) := ENNReal.tsum_comm
    _ = ∑' a, d (some a) * ∑' h, (k a h₀) (some (true, h)) :=
        tsum_congr fun a => ENNReal.tsum_mul_left

/-- Success probability of a bare general Boolean sample. -/
theorem prTrue_sampleFrom (d : SDistr Bool) (h₀ : Heap) :
    prTrue (sampleFrom d) h₀ = d (some true) := by
  have hb : (sampleFrom d : SPComp Bool) = SPComp.bind (sampleFrom d) SPComp.pure :=
    (SPComp.bind_pure _).symm
  rw [hb, prTrue_bind_sampleFrom, tsum_eq_single true]
  · simp [prTrue_pure_bool]
  · intro b hb'
    cases b <;> simp_all [prTrue_pure_bool]

/-! ## Mass -/

/-- If every continuation is lossless, the mass of `sampleFrom d >>= k` is the
    mass of `d`. -/
theorem mass_bind_sampleFrom (d : SDistr α) (k : α → SPComp β) (h₀ : Heap)
    (hk : ∀ a, SDistr.mass (k a h₀) = 1) :
    SDistr.mass ((SPComp.bind (sampleFrom d) k) h₀) = SDistr.mass d := by
  have hzero : ∀ a, (k a h₀) none = 0 := fun a =>
    Classical.byContradiction fun hne =>
      absurd (hk a) (ne_of_lt (ENNReal.sub_lt_self (by norm_num) (by norm_num) hne))
  simp only [SDistr.mass, sampleFrom_bind_apply_none, hzero, mul_zero, tsum_zero, add_zero]

/-! ## The uniform instance -/

/-- `Crypto.prTrue_bind_sample` derived from `prTrue_bind_sampleFrom`. -/
theorem prTrue_bind_sample_of_sampleFrom {α : Type*} [Fintype α] [Nonempty α]
    (F : α → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample α) F) h₀ =
    ∑ x : α, (↑(Fintype.card α) : ℝ≥0∞)⁻¹ * prTrue (F x) h₀ := by
  rw [← sampleFrom_uniform α, prTrue_bind_sampleFrom, tsum_fintype]
  exact Finset.sum_congr rfl fun a _ => by rw [SDistr.uniform_apply_some]

/-- The derived lemma and the library's `Crypto.prTrue_bind_sample` are the same
    proposition. -/
example : @Crypto.prTrue_bind_sample = @prTrue_bind_sample_of_sampleFrom := rfl

end CatCrypt.NonUniform

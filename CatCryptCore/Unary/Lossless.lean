/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Unary.Judgment

/-!
# Losslessness for Stateful Probabilistic Computations

This file defines the `isLossless` predicate for `SPComp` computations and proves
that basic operations (pure, get, set, sample) are lossless, while `fail` is not.

A computation is lossless if it has total mass 1 from any initial heap, meaning
it never fails (never produces the `none` outcome in the underlying sub-distribution).

## Main definitions

* `isLossless` - Unconditional losslessness: mass 1 from every heap
* `isLosslessIf` - Conditional losslessness: mass 1 from heaps satisfying a precondition

## Main results

* `lossless_pure` - `pure a` is lossless
* `lossless_get` - `get l` is lossless
* `lossless_set` - `set l v` is lossless
* `lossless_sample` - `sample α` is lossless (for finite nonempty types)
* `not_lossless_fail` - `fail` is not lossless
* `lossless_bind` - bind preserves losslessness

## References

* EasyCrypt: `islossless` predicate on distributions
* SSProve (Rocq): lossless reasoning in pHL
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {α β : Type*}

/-! ## Losslessness predicates -/

/-- A computation is lossless if it has total mass 1 from any initial heap.
    This means the computation never fails. -/
def isLossless (c : SPComp α) : Prop :=
  ∀ h : Heap, SDistr.mass (c h) = 1

/-- Lossless with precondition: only requires mass 1 from heaps satisfying P. -/
def isLosslessIf (P : UPre) (c : SPComp α) : Prop :=
  ∀ h, P h → SDistr.mass (c h) = 1

/-! ## Relationship between isLossless and isLosslessIf -/

/-- Unconditional losslessness implies conditional losslessness for any P. -/
theorem isLossless_implies_if (P : UPre) {c : SPComp α} (h : isLossless c) :
    isLosslessIf P c := fun h₀ _ => h h₀

/-- Conditional losslessness with truePre is equivalent to unconditional. -/
theorem isLosslessIf_truePre {c : SPComp α} :
    isLosslessIf truePre c ↔ isLossless c :=
  ⟨fun h h₀ => h h₀ trivial, fun h h₀ _ => h h₀⟩

/-! ## Losslessness of basic operations -/

/-- `pure a` is lossless: returning a value never fails. -/
theorem lossless_pure (a : α) : isLossless (SPComp.pure a) := by
  intro h
  simp only [SPComp.pure]
  exact SDistr.mass_pure (a, h)

/-- `get l` is lossless: reading from a location never fails. -/
theorem lossless_get (l : Location) : isLossless (SPComp.get l) := by
  intro h
  simp only [SPComp.get]
  exact SDistr.mass_pure (h.get l, h)

/-- `set l v` is lossless: writing to a location never fails. -/
theorem lossless_set (l : Location) (v : l.ty) : isLossless (SPComp.set l v) := by
  intro h
  simp only [SPComp.set]
  exact SDistr.mass_pure ((), h.set l v)

/-- `fail` is not lossless: it always fails (mass 0). -/
theorem not_lossless_fail : ¬ isLossless (SPComp.fail : SPComp α) := by
  intro h
  have := h Heap.empty
  simp only [SPComp.fail] at this
  rw [SDistr.mass_fail] at this
  exact absurd this (by norm_num)

/-- The mass of `fail` is 0, as an explicit lemma for use in proofs. -/
theorem mass_fail_eq_zero (h : Heap) : SDistr.mass ((SPComp.fail : SPComp α) h) = 0 := by
  simp only [SPComp.fail]
  exact SDistr.mass_fail

/-! ## Helper lemmas for mass reasoning -/

/-- If mass = 1, then the distribution assigns probability 0 to none.
    This is the key connection between mass and the none outcome. -/
private theorem mass_one_implies_none_zero {d : SDistr α} (h : SDistr.mass d = 1) :
    d none = 0 := by
  unfold SDistr.mass at h
  -- h : 1 - d none = 1
  -- In ENNReal: 1 - x = 1 implies x = 0 (when x ≤ 1)
  by_contra hne
  have h1 : (1 : ENNReal) - d none < 1 := by
    apply ENNReal.sub_lt_self
    · norm_num
    · norm_num
    · exact hne
  exact absurd h (ne_of_lt h1)

/-- Sum over Option α can be split into the none term plus sum over some terms.
    This mirrors the private `tsum_option_eq_add` in Coupling.lean. -/
private theorem tsum_option_eq_add {γ : Type*} (f : Option γ → ENNReal) :
    ∑' x : Option γ, f x = f none + ∑' a : γ, f (some a) := by
  -- Use the equivalence Option γ ≃ γ ⊕ PUnit
  let e := Equiv.optionEquivSumPUnit γ
  have heq := e.symm.tsum_eq (f := f)
  rw [← heq]
  -- Split γ ⊕ PUnit using Summable.tsum_sum
  have h := Summable.tsum_sum (f := fun y => f (e.symm y))
             (ENNReal.summable) (ENNReal.summable)
  rw [h]
  have h_punit : ∑' u : PUnit, f (e.symm (Sum.inr u)) = f none := by
    rw [tsum_eq_single ()]
    · simp only [Equiv.optionEquivSumPUnit_symm_inr, e]
    · intro u hu; exact absurd (PUnit.eq_punit u) hu
  have h_gamma : ∑' a : γ, f (e.symm (Sum.inl a)) = ∑' a : γ, f (some a) := by
    apply tsum_congr
    intro a
    simp only [Equiv.optionEquivSumPUnit_symm_inl, e]
  rw [h_punit, h_gamma, add_comm]

/-- If mass of `d` is 1, the sum over `some` values equals 1. -/
private theorem tsum_some_of_mass_one {d : SDistr α} (h : SDistr.mass d = 1) :
    ∑' a : α, d (some a) = 1 := by
  have hd_none := mass_one_implies_none_zero h
  have htotal := PMF.tsum_coe d
  rw [tsum_option_eq_add] at htotal
  rw [hd_none, zero_add] at htotal
  exact htotal

/-! ## Losslessness of sample -/

/-- `sample α` is lossless: sampling from a finite nonempty type never fails. -/
theorem lossless_sample [Fintype α] [Nonempty α] : isLossless (SPComp.sample α) := by
  intro h
  -- SPComp.sample α h = (SDistr.uniform α).bind (fun a => SDistr.pure (a, h))
  -- We need mass of this to be 1, i.e., it assigns probability 0 to none.
  simp only [SPComp.sample]
  unfold SDistr.mass SDistr.bind
  simp only [PMF.bind_apply]
  -- Goal: 1 - ∑' oa, (uniform α) oa * (match oa ...) none = 1
  -- Show the sum is 0, so 1 - 0 = 1
  convert_to 1 - (0 : ℝ≥0∞) = 1
  · congr 1
    apply ENNReal.tsum_eq_zero.mpr
    intro oa
    cases oa with
    | none =>
      rw [SDistr.uniform_apply_none]
      simp
    | some a =>
      simp only [SDistr.pure_apply_none, mul_zero]
  · simp

/-! ## Losslessness of bind -/

/-- Bind preserves losslessness: if `c` is lossless and `f a` is lossless for all `a`,
    then `c.bind f` is lossless.

    **Proof idea**: We need to show `(c h).bind (fun (a, h') => f a h') none = 0`.
    Since `c` is lossless, `(c h) none = 0`, so the none-to-none path contributes 0.
    For each `(a, h')` in the support of `c h`, `f a h'` is lossless, so
    `(f a h') none = 0`, meaning the some-to-none path also contributes 0. -/
theorem lossless_bind {c : SPComp α} {f : α → SPComp β}
    (hc : isLossless c) (hf : ∀ a, isLossless (f a)) :
    isLossless (SPComp.bind c f) := by
  intro h
  simp only [SPComp.bind]
  unfold SDistr.mass SDistr.bind
  simp only [PMF.bind_apply]
  -- Goal: 1 - ∑' oa, (c h) oa * (match oa with ...) none = 1
  -- Show the sum is 0, so 1 - 0 = 1
  convert_to 1 - (0 : ℝ≥0∞) = 1
  · congr 1
    apply ENNReal.tsum_eq_zero.mpr
    intro oa
    cases oa with
    | none =>
      -- (c h) none = 0 because c is lossless
      have hc_none := mass_one_implies_none_zero (hc h)
      rw [hc_none]
      simp
    | some p =>
      obtain ⟨a, h'⟩ := p
      -- (f a h') none = 0 because f a is lossless
      have hf_none : (f a h') none = 0 := mass_one_implies_none_zero (hf a h')
      rw [hf_none]
      simp
  · simp

/-- Variant of lossless_bind with conditional losslessness for the continuation.
    The continuation only needs to be lossless for outcomes actually produced by `c`. -/
theorem lossless_bind_of_support {c : SPComp α} {f : α → SPComp β}
    (hc : isLossless c)
    (hf : ∀ h a h', (c h) (some (a, h')) ≠ 0 → isLossless (f a)) :
    isLossless (SPComp.bind c f) := by
  intro h
  simp only [SPComp.bind]
  unfold SDistr.mass SDistr.bind
  simp only [PMF.bind_apply]
  convert_to 1 - (0 : ℝ≥0∞) = 1
  · congr 1
    apply ENNReal.tsum_eq_zero.mpr
    intro oa
    cases oa with
    | none =>
      have hc_none := mass_one_implies_none_zero (hc h)
      rw [hc_none]; simp
    | some p =>
      obtain ⟨a, h'⟩ := p
      -- If (c h)(some (a, h')) = 0, the product is 0
      by_cases hca : (c h) (some (a, h')) = 0
      · rw [hca]; simp
      · -- (c h)(some (a, h')) ≠ 0, so f a is lossless by hypothesis
        have hf_ll := hf h a h' hca
        have hf_none : (f a h') none = 0 := mass_one_implies_none_zero (hf_ll h')
        rw [hf_none]; simp
  · simp

/-! ## Derived losslessness lemmas -/

/-- Assert is lossless when the condition holds. -/
theorem lossless_assert_of (P : Prop) [Decidable P] (hp : P) :
    isLossless (SPComp.assert P) := by
  intro h
  simp only [SPComp.assert, hp, ite_true]
  exact lossless_pure () h

/-- Assert is not lossless when the condition fails. -/
theorem not_lossless_assert_of_not (P : Prop) [Decidable P] (hp : ¬ P) :
    ¬ isLossless (SPComp.assert P) := by
  intro hll
  have := hll Heap.empty
  simp only [SPComp.assert, hp, ite_false, SPComp.fail] at this
  rw [SDistr.mass_fail] at this
  exact absurd this (by norm_num)

/-- Sequential composition preserves losslessness. -/
theorem lossless_seq {c₁ : SPComp α} {c₂ : SPComp β}
    (h₁ : isLossless c₁) (h₂ : isLossless c₂) :
    isLossless (SPComp.seq c₁ c₂) := by
  unfold SPComp.seq
  exact lossless_bind h₁ (fun _ => h₂)

end CatCrypt.Unary

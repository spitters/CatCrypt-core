/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Prob.SDistr

/-!
# Support Analysis for Sub-Distributions

This file provides key lemmas for extracting support information from
sub-distribution operations, particularly `SDistr.bind`.

## Main results

* `SDistr.bind_support_witness` - If `(d.bind f)(some b) ≠ 0`, then there
  exists an intermediate value `a` with `d(some a) ≠ 0` and `(f a)(some b) ≠ 0`.
* `tsum_option_split` - Split a sum over `Option α` into the `none` term
  plus the sum over `some` terms.
* `tsum_some_eq_mass` - The sum over `some` outcomes equals the mass.

## Motivation

These lemmas are the foundation for the unary probabilistic Hoare logic (pHL)
proof rules, particularly `pHoare_bind` and `pHoare_sample`. They extract
existential witnesses from nonzero probability observations.

## References

* EasyCrypt: support analysis in pRHL `rnd` tactic
* CertiCrypt (Barthe et al.): coupling and support reasoning in Coq
-/

namespace CatCrypt.Prob

open scoped ENNReal

variable {α β γ : Type*}

/-! ## Splitting sums over Option -/

/-- Sum over `Option α` splits into the `none` term plus sum over `some` terms.
    This is a fundamental decomposition for reasoning about sub-distributions. -/
theorem tsum_option_split (f : Option α → ℝ≥0∞) :
    ∑' x : Option α, f x = f none + ∑' a : α, f (some a) := by
  let e := Equiv.optionEquivSumPUnit α
  have heq := e.symm.tsum_eq (f := f)
  rw [← heq]
  have h := Summable.tsum_sum (f := fun y => f (e.symm y))
           (ENNReal.summable) (ENNReal.summable)
  rw [h]
  have h_punit : ∑' u : PUnit, f (e.symm (Sum.inr u)) = f none := by
    rw [tsum_eq_single ()]
    · simp only [Equiv.optionEquivSumPUnit_symm_inr, e]
    · intro u hu; exact absurd (PUnit.eq_punit u) hu
  have h_gamma : ∑' a : α, f (e.symm (Sum.inl a)) = ∑' a : α, f (some a) := by
    apply tsum_congr
    intro a
    simp only [Equiv.optionEquivSumPUnit_symm_inl, e]
  rw [h_punit, h_gamma, add_comm]

/-- The sum over `some` outcomes equals the mass of the distribution. -/
theorem tsum_some_eq_mass (d : SDistr α) :
    ∑' a : α, d (some a) = SDistr.mass d := by
  have htotal := PMF.tsum_coe d
  rw [tsum_option_split] at htotal
  unfold SDistr.mass
  -- htotal : d none + ∑' a, d (some a) = 1
  -- goal : ∑' a, d (some a) = 1 - d none
  have hfin : d none ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc d none ≤ d none + ∑' a, d (some a) := le_add_right le_rfl
    _ = 1 := htotal
  rw [add_comm] at htotal
  exact ENNReal.eq_sub_of_add_eq hfin htotal

/-- If mass = 1, the sum over `some` outcomes equals 1. -/
theorem tsum_some_of_mass_one (d : SDistr α) (h : SDistr.mass d = 1) :
    ∑' a : α, d (some a) = 1 := by
  rw [tsum_some_eq_mass]; exact h

/-- If mass = 1, then d(none) = 0 (no failure). -/
theorem mass_one_implies_none_zero (d : SDistr α) (h : SDistr.mass d = 1) :
    d none = 0 := by
  unfold SDistr.mass at h
  by_contra hne
  have h1 : (1 : ENNReal) - d none < 1 := by
    apply ENNReal.sub_lt_self
    · norm_num
    · norm_num
    · exact hne
  exact absurd h (ne_of_lt h1)

/-! ## Bind support witness -/

/-- **Key lemma**: If `(d.bind f)(some b) ≠ 0`, then there exists an intermediate
    value `a` such that `d(some a) ≠ 0` and `(f a)(some b) ≠ 0`.

    This extracts a witness from the nonzero probability of a bind result.
    The proof uses the contrapositive of `ENNReal.tsum_eq_zero`:
    if the sum `∑ oa, d(oa) * (cont oa)(some b)` is nonzero,
    at least one term must be nonzero.

    **Proof sketch**:
    1. `SDistr.bind` is `PMF.bind` with failure propagation
    2. `PMF.bind_apply` gives `(d.bind f)(some b) = ∑' oa, d(oa) * (cont oa)(some b)`
    3. If this sum ≠ 0, by contrapositive of `tsum_eq_zero`, ∃ oa with term ≠ 0
    4. That term is `d(oa) * (cont oa)(some b) ≠ 0`, so both factors ≠ 0
    5. `oa` cannot be `none` (since cont of none is `fail`, giving 0)
    6. So `oa = some a` for some `a`, giving our witness -/
theorem SDistr.bind_support_witness {d : SDistr α} {f : α → SDistr β} {b : β}
    (h : (d.bind f) (some b) ≠ 0) :
    ∃ a, d (some a) ≠ 0 ∧ (f a) (some b) ≠ 0 := by
  unfold SDistr.bind at h
  rw [PMF.bind_apply] at h
  -- h : ∑' oa, d oa * (match oa with | some a => f a | none => SDistr.fail) (some b) ≠ 0
  -- By contrapositive of tsum_eq_zero, there exists oa with the term ≠ 0
  rw [ne_eq, ENNReal.tsum_eq_zero] at h
  push Not at h
  obtain ⟨oa, hoa⟩ := h
  -- hoa : d oa * (match oa with ...) (some b) ≠ 0
  cases oa with
  | none =>
    -- d none * fail(some b) = d none * 0 = 0, contradiction
    simp only [SDistr.fail_apply_some, mul_zero, ne_eq, not_true_eq_false] at hoa
  | some a =>
    -- d (some a) * (f a)(some b) ≠ 0
    -- In ENNReal, a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0
    simp only [] at hoa
    exact ⟨a, (mul_ne_zero_iff.mp hoa).1, (mul_ne_zero_iff.mp hoa).2⟩

/-- Variant: if the bind result with a continuation on pairs has nonzero probability,
    extract the intermediate pair. -/
theorem SDistr.bind_support_witness_pair {d : SDistr (α × β)} {f : α × β → SDistr γ} {c : γ}
    (h : (d.bind f) (some c) ≠ 0) :
    ∃ a b, d (some (a, b)) ≠ 0 ∧ (f (a, b)) (some c) ≠ 0 := by
  obtain ⟨⟨a, b⟩, hd, hf⟩ := SDistr.bind_support_witness h
  exact ⟨a, b, hd, hf⟩

/-! ## Pointwise reasoning helpers -/

/-- In ENNReal, if the sum of f is ≤ sum of g pointwise, then tsum f ≤ tsum g. -/
theorem ENNReal_tsum_le_of_pointwise {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) :
    ∑' a, f a ≤ ∑' a, g a :=
  ENNReal.tsum_le_tsum h

/-- Conditional sum is bounded by unconditional sum. -/
theorem tsum_ite_le (P : α → Prop) [DecidablePred P] (f : α → ℝ≥0∞) :
    ∑' a, (if P a then f a else 0) ≤ ∑' a, f a := by
  apply ENNReal.tsum_le_tsum
  intro a
  split_ifs <;> simp

/-- Conditional sums partition the unconditional sum when terms are nonneg. -/
theorem tsum_ite_add_compl (P : α → Prop) [DecidablePred P] (f : α → ℝ≥0∞) :
    (∑' a, if P a then f a else 0) + (∑' a, if ¬P a then f a else 0) = ∑' a, f a := by
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro a
  by_cases hp : P a
  · simp [hp]
  · simp [hp]

/-! ## Product type tsum splitting -/

/-- Split a tsum over `α × β` into nested tsums. -/
theorem tsum_prod_eq {f : α × β → ℝ≥0∞} :
    ∑' p : α × β, f p = ∑' a, ∑' b, f (a, b) :=
  ENNReal.tsum_prod'

/-- Split a tsum over `Bool × β` into true and false parts. -/
theorem tsum_bool_prod_eq {f : Bool × β → ℝ≥0∞} :
    ∑' p : Bool × β, f p = (∑' b, f (true, b)) + (∑' b, f (false, b)) := by
  rw [tsum_prod_eq, tsum_bool]
  exact add_comm _ _

end CatCrypt.Prob

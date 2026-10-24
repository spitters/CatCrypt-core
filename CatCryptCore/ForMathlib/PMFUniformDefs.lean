/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform probability mass functions on finsets, fintypes and multisets

The probability mass functions `PMF.uniformFinset`, `PMF.uniformFintype` and
`PMF.ofMultiset''''`, with their evaluation, support and measure lemmas. Mathlib #42909
moved the constructions `uniformFinset`, `uniformFintype` and `ofMultiset` to
`MeasureTheory.Measure`; this file defines their `PMF` forms under these names.

## Main definitions

* `PMF.uniformFinset s hs` — the uniform distribution on a nonempty finset `s`
* `PMF.uniformFintype α` — the uniform distribution on a nonempty fintype `α`
* `PMF.ofMultiset'''' s hs` — the distribution sending `a` to the fraction of the elements
  of the nonzero multiset `s` equal to `a`
-/

@[expose] public section

set_option autoImplicit false

namespace PMF

variable {α : Type*}

open scoped ENNReal
open Finset

section UniformFinset

/-- The uniform distribution on the nonempty finset `s`: each element of `s` has
probability `1 / #s`. -/
noncomputable def uniformFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) s ?_ ?_
  · rw [Finset.sum_ite_of_true (fun _ h => h), Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simpa using hs.ne_empty) (ENNReal.natCast_ne_top _)
  · grind only

variable {s : Finset α} (hs : s.Nonempty) {a : α}

open scoped Classical in
/-- Unfolding lemma of `uniformFinset`: the probability of `a` is `1 / #s` on `s` and `0`
off `s`. -/
@[simp]
theorem uniformFinset_apply (a : α) :
    uniformFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  rfl

theorem uniformFinset_apply_of_mem (ha : a ∈ s) :
    uniformFinset s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  simp only [uniformFinset_apply, ↓reduceIte, ha]

theorem uniformFinset_apply_of_notMem (ha : a ∉ s) : uniformFinset s hs a = 0 := by
  simp only [uniformFinset_apply, ↓reduceIte, ha]

@[simp]
theorem support_uniformFinset : (uniformFinset s hs).support = s := by
  ext a; simp [mem_support_iff]

theorem mem_support_uniformFinset_iff (a : α) :
    a ∈ (uniformFinset s hs).support ↔ a ∈ s := by
  simp only [support_uniformFinset, SetLike.mem_coe]

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_uniformFinset_apply :
    (uniformFinset s hs).toOuterMeasure t = #{x ∈ s | x ∈ t} / #s := by
  rw [toOuterMeasure_apply, tsum_eq_sum (s := s) (fun x hx => by simp [Set.indicator, hx]),
    Finset.sum_congr rfl (g := fun x => if x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0)
      (fun x hx => by simp [Set.indicator, hx]),
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

open scoped Classical in
@[simp]
theorem toMeasure_uniformFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformFinset s hs).toMeasure t = #{x ∈ s | x ∈ t} / #s := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ ht, toOuterMeasure_uniformFinset_apply]

end Measure

end UniformFinset

section UniformFintype

/-- The uniform distribution on the nonempty fintype `α`. -/
noncomputable def uniformFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniformFintype_apply (a : α) :
    uniformFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [uniformFintype, uniformFinset_apply_of_mem _ (Finset.mem_univ a), Finset.card_univ]

@[simp]
theorem support_uniformFintype (α : Type*) [Fintype α] [Nonempty α] :
    (uniformFintype α).support = ⊤ := by
  ext x; simp [mem_support_iff]

theorem mem_support_uniformFintype (a : α) : a ∈ (uniformFintype α).support := by
  simp only [support_uniformFintype, Set.top_eq_univ, Set.mem_univ]

section Measure

variable (s : Set α)

theorem toOuterMeasure_uniformFintype_apply [Fintype s] :
    (uniformFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [uniformFintype, toOuterMeasure_uniformFinset_apply, Finset.card_univ, Fintype.card_subtype]

theorem toMeasure_uniformFintype_apply [MeasurableSpace α] (hs : MeasurableSet s)
    [Fintype s] :
    (uniformFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ hs, toOuterMeasure_uniformFintype_apply]

end Measure

end UniformFintype

section OfMultiset

open scoped Classical in
/-- The distribution on the nonzero multiset `s` sending `a` to the fraction of the
elements of `s` equal to `a`. -/
noncomputable def ofMultiset' (s : Multiset α) (hs : s ≠ 0) : PMF α :=
  ⟨fun a => s.count a / (Multiset.card s), by
    rw [ENNReal.summable.hasSum_iff]
    simp_rw [div_eq_mul_inv, ENNReal.tsum_mul_right]
    rw [tsum_eq_sum (s := s.toFinset) (fun a ha => by simpa using ha), ← Nat.cast_sum,
      Multiset.toFinset_sum_count_eq]
    exact ENNReal.mul_inv_cancel (by simpa using hs) (ENNReal.natCast_ne_top _)⟩

variable {s : Multiset α} (hs : s ≠ 0)

open scoped Classical in
/-- Unfolding lemma of `ofMultiset'`: the probability of `a` is its multiplicity in `s`
divided by the cardinality of `s`. -/
@[simp]
theorem ofMultiset'_apply (a : α) : ofMultiset' s hs a = s.count a / (Multiset.card s) := by
  rfl

open scoped Classical in
@[simp]
theorem support_ofMultiset' : (ofMultiset' s hs).support = s.toFinset := by
  ext a; simp [mem_support_iff]

open scoped Classical in
theorem mem_support_ofMultiset'_iff (a : α) :
    a ∈ (ofMultiset' s hs).support ↔ a ∈ s.toFinset := by
  simp only [support_ofMultiset', SetLike.mem_coe, Multiset.mem_toFinset]

theorem ofMultiset'_apply_of_notMem {a : α} (ha : a ∉ s) : ofMultiset' s hs a = 0 := by
  classical
  simp only [ofMultiset'_apply, Multiset.count_eq_zero_of_notMem ha, CharP.cast_eq_zero,
    ENNReal.zero_div]

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_ofMultiset'_apply :
    (ofMultiset' s hs).toOuterMeasure t =
      (∑' x, (s.filter (· ∈ t)).count x : ℝ≥0∞) / (Multiset.card s) := by
  rw [toOuterMeasure_apply, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ t <;> simp [Set.indicator, hx, div_eq_mul_inv]

open scoped Classical in
@[simp]
theorem toMeasure_ofMultiset'_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofMultiset' s hs).toMeasure t =
      (∑' x, (s.filter (· ∈ t)).count x : ℝ≥0∞) / (Multiset.card s) := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ ht, toOuterMeasure_ofMultiset'_apply]

end Measure

end OfMultiset

end PMF

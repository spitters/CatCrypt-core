/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Exchange of weighted sums and subtraction of sums

Two facts about unconditional sums in complete-lattice monoids and in `ℝ≥0∞`.

## Main results

* `tsum_tsub_tsum_le`: the difference of two sums is at most the sum of the pointwise
  truncated differences, `(∑' i, f i) - (∑' i, g i) ≤ ∑' i, (f i - g i)`.
* `ENNReal.tsum_mul_tsum_mul_comm`: two nested weighted sums in the other order,
  `∑' a, p a * ∑' b, q b * F a b = ∑' b, q b * ∑' a, p a * F a b`.

## Search words

tsum, Fubini, Tonelli, swap of sums, weighted sum, expectation over two independent draws,
truncated subtraction, tsub, ENNReal, complete-lattice monoid
-/

public section

open scoped ENNReal

/-- The difference of two sums is at most the sum of the pointwise truncated differences. -/
theorem tsum_tsub_tsum_le {ι α : Type*} [AddCommMonoid α] [CompleteLattice α]
    [CanonicallyOrderedAdd α] [TopologicalSpace α] [SupConvergenceClass α]
    [IsOrderedAddMonoid α] [OrderClosedTopology α] [T2Space α] [ContinuousAdd α]
    [Sub α] [OrderedSub α] (f g : ι → α) :
    (∑' i, f i) - (∑' i, g i) ≤ ∑' i, (f i - g i) := by
  rw [tsub_le_iff_right, ← tsum_add]
  exact tsum_le_tsum fun i => le_tsub_add

/-- Two nested weighted sums in the other order: the sum over `a` with weight `p a` of the sum
over `b` with weight `q b` equals the sum over `b` with weight `q b` of the sum over `a` with
weight `p a`. -/
theorem ENNReal.tsum_mul_tsum_mul_comm {α β : Type*} (p : α → ℝ≥0∞) (q : β → ℝ≥0∞)
    (F : α → β → ℝ≥0∞) :
    ∑' a, p a * ∑' b, q b * F a b = ∑' b, q b * ∑' a, p a * F a b := by
  simp only [← ENNReal.tsum_mul_left]
  rw [tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => mul_left_comm _ _ _

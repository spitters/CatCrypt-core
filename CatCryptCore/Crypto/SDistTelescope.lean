/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SDist

/-!
# Telescoping bound of the unsigned difference

The unsigned difference `absDiff` of the extreme terms of a sequence in `ℝ≥0∞` is at most the sum
of the unsigned differences of consecutive terms; the hybrid arguments over a range of indices
use it.
-/

@[expose] public section

namespace CatCrypt.Crypto

open scoped ENNReal

/-- The telescoping bound of a sequence of values by its steps. -/
theorem absDiff_le_sum_range (f : ℕ → ℝ≥0∞) (n : ℕ) :
    absDiff (f 0) (f n) ≤ ∑ i ∈ Finset.range n, absDiff (f i) (f (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (absDiff_triangle _ (f n) _).trans (add_le_add ih le_rfl)

end CatCrypt.Crypto

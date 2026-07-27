/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.WhileApprox

/-!
# Order theory of the bounded loop approximants

The mass `whileApprox guard body n h` assigns to a value is non-decreasing in the
budget `n`, the mass it assigns to failure is non-increasing, and the value mass
is bounded by `1` at every budget. Together these make the pointwise supremum
over `n` a well-defined sub-probability assignment, which is what a limit
construction for `while guard do body` consumes.

## Main results

* `SDistr.bind_apply_mono` — `bind` is monotone in its continuation, pointwise at
  a fixed outcome
* `whileApprox_apply_le_succ`, `whileApprox_apply_mono`,
  `monotone_whileApprox_apply` — the value mass is non-decreasing in the budget
* `whileApprox_apply_none_succ_le`, `whileApprox_apply_none_antitone` — the
  failure mass is non-increasing in the budget
* `whileApprox_apply_le_one`, `tsum_whileApprox_apply_le_one` — the value mass is
  bounded by `1` at every budget
* `iSup_whileApprox_apply_le_one`, `tsum_iSup_whileApprox_apply_le_one` — the same
  bounds for the pointwise supremum over budgets
-/

set_option autoImplicit false

open scoped ENNReal

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob

/-! ## Unfolding at a fixed outcome -/

/-- The guarded step of an approximant as an `SDistr` bind: the body is run once
and the remaining budget is spent from the resulting heap. -/
theorem whileApprox_succ_bind_of_guard {guard : Heap → Bool} {body : SPComp Unit}
    {h : Heap} (hg : guard h = true) (n : ℕ) :
    whileApprox guard body (n + 1) h
      = (body h).bind fun q => whileApprox guard body n q.2 := by
  rw [whileApprox_succ_of_guard hg]
  rfl

@[simp] theorem whileApprox_zero_apply_some (guard : Heap → Bool) (body : SPComp Unit)
    (h : Heap) (p : Unit × Heap) :
    whileApprox guard body 0 h (some p) = 0 :=
  SDistr.fail_apply_some p

@[simp] theorem whileApprox_zero_apply_none (guard : Heap → Bool) (body : SPComp Unit)
    (h : Heap) :
    whileApprox guard body 0 h none = 1 :=
  SDistr.fail_apply_none

/-! ## The value mass is non-decreasing in the budget -/

/-- Raising the budget by one does not decrease the mass at a value: a run that has
not yet left the loop contributes no mass at the smaller budget. -/
theorem whileApprox_apply_le_succ (guard : Heap → Bool) (body : SPComp Unit) :
    ∀ (n : ℕ) (h : Heap) (p : Unit × Heap),
      whileApprox guard body n h (some p) ≤ whileApprox guard body (n + 1) h (some p)
  | 0, h, p => by
      rw [whileApprox_zero_apply_some]
      exact zero_le
  | n + 1, h, p => by
      cases hg : guard h with
      | false =>
          rw [whileApprox_succ_of_not_guard hg, whileApprox_succ_of_not_guard hg]
      | true =>
          rw [whileApprox_succ_bind_of_guard hg, whileApprox_succ_bind_of_guard hg]
          exact SDistr.bind_apply_mono _ _ fun q =>
            whileApprox_apply_le_succ guard body n q.2 p

/-- The mass at a value is non-decreasing in the budget. -/
theorem whileApprox_apply_mono (guard : Heap → Bool) (body : SPComp Unit) (h : Heap) :
    ∀ n m : ℕ, n ≤ m → ∀ p : Unit × Heap,
      whileApprox guard body n h (some p) ≤ whileApprox guard body m h (some p) := by
  intro n m hnm p
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (whileApprox_apply_le_succ guard body m h p)

/-- The mass at a value, as a function of the budget, is monotone. -/
theorem monotone_whileApprox_apply (guard : Heap → Bool) (body : SPComp Unit)
    (h : Heap) (p : Unit × Heap) :
    Monotone fun n => whileApprox guard body n h (some p) :=
  fun _ _ hnm => whileApprox_apply_mono guard body h _ _ hnm p

/-! ## The failure mass is non-increasing in the budget -/

/-- Raising the budget by one does not increase the mass at failure. -/
theorem whileApprox_apply_none_succ_le (guard : Heap → Bool) (body : SPComp Unit) :
    ∀ (n : ℕ) (h : Heap),
      whileApprox guard body (n + 1) h none ≤ whileApprox guard body n h none
  | 0, h => by
      rw [whileApprox_zero_apply_none]
      exact PMF.coe_le_one _ _
  | n + 1, h => by
      cases hg : guard h with
      | false =>
          rw [whileApprox_succ_of_not_guard hg, whileApprox_succ_of_not_guard hg]
      | true =>
          rw [whileApprox_succ_bind_of_guard hg, whileApprox_succ_bind_of_guard hg]
          exact SDistr.bind_apply_mono _ _ fun q =>
            whileApprox_apply_none_succ_le guard body n q.2

/-- The mass at failure is non-increasing in the budget. -/
theorem whileApprox_apply_none_antitone (guard : Heap → Bool) (body : SPComp Unit)
    (h : Heap) :
    ∀ n m : ℕ, n ≤ m →
      whileApprox guard body m h none ≤ whileApprox guard body n h none := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact (whileApprox_apply_none_succ_le guard body m h).trans ih

/-- The mass at failure, as a function of the budget, is antitone. -/
theorem antitone_whileApprox_apply_none (guard : Heap → Bool) (body : SPComp Unit)
    (h : Heap) :
    Antitone fun n => whileApprox guard body n h none :=
  fun _ _ hnm => whileApprox_apply_none_antitone guard body h _ _ hnm

/-! ## The value mass is bounded -/

/-- The mass at a single value is at most `1`. -/
theorem whileApprox_apply_le_one (guard : Heap → Bool) (body : SPComp Unit) (n : ℕ)
    (h : Heap) (p : Unit × Heap) :
    whileApprox guard body n h (some p) ≤ 1 :=
  PMF.coe_le_one _ _

/-- The mass at a single value is finite. -/
theorem whileApprox_apply_ne_top (guard : Heap → Bool) (body : SPComp Unit) (n : ℕ)
    (h : Heap) (p : Unit × Heap) :
    whileApprox guard body n h (some p) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (whileApprox_apply_le_one guard body n h p)

/-- The total mass on values is at most `1` at every budget. -/
theorem tsum_whileApprox_apply_le_one (guard : Heap → Bool) (body : SPComp Unit)
    (n : ℕ) (h : Heap) :
    ∑' p : Unit × Heap, whileApprox guard body n h (some p) ≤ 1 := by
  have htot := PMF.tsum_coe (whileApprox guard body n h)
  rw [SDistr.tsum_option_eq_add] at htot
  exact htot ▸ le_add_self

/-! ## The bounds for the supremum over budgets -/

/-- The supremum over budgets of the mass at a value is at most `1`. -/
theorem iSup_whileApprox_apply_le_one (guard : Heap → Bool) (body : SPComp Unit)
    (h : Heap) (p : Unit × Heap) :
    ⨆ n, whileApprox guard body n h (some p) ≤ 1 :=
  iSup_le fun n => whileApprox_apply_le_one guard body n h p

/-- The total mass on values of the pointwise supremum over budgets is at most `1`,
so the supremum is a sub-probability assignment. -/
theorem tsum_iSup_whileApprox_apply_le_one (guard : Heap → Bool) (body : SPComp Unit)
    (h : Heap) :
    ∑' p : Unit × Heap, ⨆ n, whileApprox guard body n h (some p) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [ENNReal.finsetSum_iSup_of_monotone fun p => monotone_whileApprox_apply guard body h p]
  refine iSup_le fun n => ?_
  exact le_trans (ENNReal.sum_le_tsum s) (tsum_whileApprox_apply_le_one guard body n h)

end CatCrypt.NonUniform

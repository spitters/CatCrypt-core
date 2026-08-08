/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.While

/-!
# The unbounded loop over a threaded state

`whileLoopS guard body s` runs `body` while `guard` holds, threading a value of
`σ` through the iterations alongside the heap. `While.lean`'s `whileLoop` is this
at `σ = Unit`, and `whileLoopS_unit` says so.

The state is what a caller carries that the heap does not. A translation whose
local variables live outside the heap — a valuation the lowering threads rather
than a set of heap cells — has a loop guard reading that valuation and a body
rewriting it, so neither is a function of the heap alone and neither fits
`whileLoop`. `σ` is that valuation.

The development follows `WhileApprox`, `WhileApproxMono` and `While` line for
line: the approximants fail at budget zero, which makes the mass at a value
non-decreasing in the budget, and the loop is the pointwise limit.
-/

set_option autoImplicit false

open scoped ENNReal

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob

variable {σ : Type*}

/-! ## Approximants -/

/-- The `n`-step approximant of `while guard do body` at the state `s`: run `body`
while `guard` holds of the state and the heap, for at most `n` iterations, and
fail if the budget runs out. -/
noncomputable def whileApproxS (guard : σ → Heap → Bool) (body : σ → SPComp σ) :
    ℕ → σ → SPComp σ
  | 0, _ => SPComp.fail
  | n + 1, s => fun h =>
      if guard s h then
        SPComp.bind (body s) (fun s' => whileApproxS guard body n s') h
      else
        SPComp.pure s h

@[simp] theorem whileApproxS_zero (guard : σ → Heap → Bool) (body : σ → SPComp σ)
    (s : σ) : whileApproxS guard body 0 s = SPComp.fail := rfl

theorem whileApproxS_succ (guard : σ → Heap → Bool) (body : σ → SPComp σ) (n : ℕ)
    (s : σ) (h : Heap) :
    whileApproxS guard body (n + 1) s h =
      if guard s h then
        SPComp.bind (body s) (fun s' => whileApproxS guard body n s') h
      else SPComp.pure s h := rfl

theorem whileApproxS_succ_of_guard {guard : σ → Heap → Bool} {body : σ → SPComp σ}
    {s : σ} {h : Heap} (hg : guard s h = true) (n : ℕ) :
    whileApproxS guard body (n + 1) s h =
      SPComp.bind (body s) (fun s' => whileApproxS guard body n s') h := by
  rw [whileApproxS_succ, if_pos hg]

theorem whileApproxS_succ_of_not_guard {guard : σ → Heap → Bool}
    {body : σ → SPComp σ} {s : σ} {h : Heap} (hg : guard s h = false) (n : ℕ) :
    whileApproxS guard body (n + 1) s h = SPComp.pure s h := by
  rw [whileApproxS_succ, if_neg (by simp [hg])]

/-- The guarded step as an `SDistr` bind: the body runs once and the remaining
budget is spent from the resulting state and heap. -/
theorem whileApproxS_succ_bind_of_guard {guard : σ → Heap → Bool}
    {body : σ → SPComp σ} {s : σ} {h : Heap} (hg : guard s h = true) (n : ℕ) :
    whileApproxS guard body (n + 1) s h
      = (body s h).bind fun q => whileApproxS guard body n q.1 q.2 := by
  rw [whileApproxS_succ_of_guard hg]
  rfl

@[simp] theorem whileApproxS_zero_apply_some (guard : σ → Heap → Bool)
    (body : σ → SPComp σ) (s : σ) (h : Heap) (p : σ × Heap) :
    whileApproxS guard body 0 s h (some p) = 0 :=
  SDistr.fail_apply_some p

@[simp] theorem whileApproxS_zero_apply_none (guard : σ → Heap → Bool)
    (body : σ → SPComp σ) (s : σ) (h : Heap) :
    whileApproxS guard body 0 s h none = 1 :=
  SDistr.fail_apply_none

/-! ## The value mass is non-decreasing in the budget -/

/-- Raising the budget by one does not decrease the mass at a value: a run that
has not yet left the loop contributes no mass at the smaller budget. -/
theorem whileApproxS_apply_le_succ (guard : σ → Heap → Bool) (body : σ → SPComp σ) :
    ∀ (n : ℕ) (s : σ) (h : Heap) (p : σ × Heap),
      whileApproxS guard body n s h (some p)
        ≤ whileApproxS guard body (n + 1) s h (some p)
  | 0, _, _, p => by
      rw [whileApproxS_zero_apply_some]
      exact zero_le
  | n + 1, s, h, p => by
      cases hg : guard s h with
      | false =>
          rw [whileApproxS_succ_of_not_guard hg, whileApproxS_succ_of_not_guard hg]
      | true =>
          rw [whileApproxS_succ_bind_of_guard hg, whileApproxS_succ_bind_of_guard hg]
          exact SDistr.bind_apply_mono _ _ fun q =>
            whileApproxS_apply_le_succ guard body n q.1 q.2 p

/-- The mass at a value is non-decreasing in the budget. -/
theorem whileApproxS_apply_mono (guard : σ → Heap → Bool) (body : σ → SPComp σ)
    (s : σ) (h : Heap) :
    ∀ n m : ℕ, n ≤ m → ∀ p : σ × Heap,
      whileApproxS guard body n s h (some p)
        ≤ whileApproxS guard body m s h (some p) := by
  intro n m hnm p
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (whileApproxS_apply_le_succ guard body m s h p)

/-! ## The loop -/

/-- `while guard do body`, threading a state of `σ`, as the limit of its bounded
approximants. -/
noncomputable def whileLoopS (guard : σ → Heap → Bool) (body : σ → SPComp σ) :
    σ → SPComp σ :=
  fun s h => mlim (fun n => whileApproxS guard body n s h)
    (whileApproxS_apply_mono guard body s h)

@[simp] theorem whileLoopS_apply_some (guard : σ → Heap → Bool)
    (body : σ → SPComp σ) (s : σ) (h : Heap) (p : σ × Heap) :
    whileLoopS guard body s h (some p)
      = ⨆ n, whileApproxS guard body n s h (some p) := rfl

/-- An outcome of the loop is an outcome of some approximant: a supremum over the
budgets is nonzero only if one of them is. -/
theorem exists_whileApproxS_ne_zero {guard : σ → Heap → Bool} {body : σ → SPComp σ}
    {s : σ} {h : Heap} {p : σ × Heap} (hp : whileLoopS guard body s h (some p) ≠ 0) :
    ∃ n, whileApproxS guard body n s h (some p) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hp (by simpa [whileLoopS_apply_some] using iSup_eq_bot.mpr hcon)

/-! ## Agreement with the stateless loop

At `σ = Unit` the threaded state carries nothing, and the two developments are the
same computation. -/

theorem whileApproxS_unit (guard : Heap → Bool) (body : SPComp Unit) :
    ∀ (n : ℕ) (h : Heap),
      whileApproxS (fun _ => guard) (fun _ => body) n () h = whileApprox guard body n h
  | 0, _ => rfl
  | n + 1, h => by
      cases hg : guard h with
      | false =>
          rw [whileApproxS_succ_of_not_guard (by simpa using hg),
            whileApprox_succ_of_not_guard hg]
      | true =>
          rw [whileApproxS_succ_bind_of_guard (by simpa using hg),
            whileApprox_succ_bind_of_guard hg]
          exact congrArg _ (funext fun q => whileApproxS_unit guard body n q.2)

theorem whileLoopS_unit (guard : Heap → Bool) (body : SPComp Unit) (h : Heap) :
    whileLoopS (fun _ => guard) (fun _ => body) () h = whileLoop guard body h := by
  unfold whileLoopS whileLoop
  congr 1
  exact funext fun n => whileApproxS_unit guard body n h

end CatCrypt.NonUniform

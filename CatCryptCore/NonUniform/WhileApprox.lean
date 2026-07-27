/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Unary.Lossless

/-!
# Bounded approximants of an unbounded loop

`whileApprox guard body n` runs `body` at most `n` times, continuing while
`guard` holds of the current heap, and fails when the budget is exhausted. It is
the finite unrolling whose limit denotes `while guard do body`: the mass
`whileApprox guard body n` assigns to a heap is the probability of reaching that
heap and leaving the loop within `n` iterations.

Failure at zero is what makes the sequence increasing in `n`: a run that has not
yet left the loop contributes no mass, so extending the budget can only add mass
at a value, never move it.

The loop itself is the limit of this sequence, which is developed separately;
this file fixes the approximants and their defining equations.
-/

set_option autoImplicit false

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob

/-- The `n`-step approximant of `while guard do body`: run `body` while `guard`
holds, for at most `n` iterations, and fail if the budget runs out. -/
noncomputable def whileApprox (guard : Heap → Bool) (body : SPComp Unit) :
    ℕ → SPComp Unit
  | 0 => SPComp.fail
  | n + 1 => fun h =>
      if guard h then
        SPComp.bind body (fun _ => whileApprox guard body n) h
      else
        SPComp.pure () h

@[simp] theorem whileApprox_zero (guard : Heap → Bool) (body : SPComp Unit) :
    whileApprox guard body 0 = SPComp.fail := rfl

theorem whileApprox_succ (guard : Heap → Bool) (body : SPComp Unit) (n : ℕ)
    (h : Heap) :
    whileApprox guard body (n + 1) h =
      if guard h then SPComp.bind body (fun _ => whileApprox guard body n) h
      else SPComp.pure () h := rfl

theorem whileApprox_succ_of_guard {guard : Heap → Bool} {body : SPComp Unit}
    {h : Heap} (hg : guard h = true) (n : ℕ) :
    whileApprox guard body (n + 1) h =
      SPComp.bind body (fun _ => whileApprox guard body n) h := by
  rw [whileApprox_succ, if_pos hg]

theorem whileApprox_succ_of_not_guard {guard : Heap → Bool} {body : SPComp Unit}
    {h : Heap} (hg : guard h = false) (n : ℕ) :
    whileApprox guard body (n + 1) h = SPComp.pure () h := by
  rw [whileApprox_succ, if_neg (by simp [hg])]

end CatCrypt.NonUniform

/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Relational.Rules
import CatCrypt.Invariant

/-!
# Invariant Restoration Tactics

This file provides tactics for restoring invariants after put (write) operations.

## Background

After a `put` operation in a relational proof, the precondition may become "broken" -
the rules `rHoare_put_l` and `rHoare_put_r` produce goals where the precondition
is wrapped in `set_lhs` or `set_rhs`.

In the Lean formulation:
- `set_lhs l v pre h₀ h₁` means `pre (h₀.set l v) h₁`
- `set_rhs l v pre h₀ h₁` means `pre h₀ (h₁.set l v)`

These tactics help "unwrap" the set operations when we can show that the
invariant is preserved by the write.

## Main tactics

* `ssprove_restore_pre` - Restore precondition after put operations
* `ssprove_restore_mem` - Restore precondition including remembered values

## References

* CatCrypt: theories/Crypt/package/pkg_user_util.v
* CatCrypt: theories/Crypt/package/pkg_invariants.v
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob CatCrypt.Invariant

/-! ## Consequence-based Restoration

An alternative approach is to use the consequence rule directly.
When `set_lhs l v pre h₀ h₁` holds (i.e., `pre (h₀.set l v) h₁`),
we can establish `pre' h₀ h₁` for some weaker precondition pre'
if we can show that pre' is implied by pre on the modified heap.
-/

/-- Weaken a set_lhs precondition using consequence.
    If we have `set_lhs l v pre` and can derive `pre'` from `pre (_.set l v) _`,
    then we can use `pre'` instead. -/
theorem set_lhs_conseq {pre pre' : RPre} {l : Location} {v : l.ty}
    (h : ∀ h₀ h₁, pre (h₀.set l v) h₁ → pre' h₀ h₁) :
    ∀ h₀ h₁, set_lhs l v pre h₀ h₁ → pre' h₀ h₁ := by
  intro h₀ h₁ hset
  simp only [set_lhs] at hset
  exact h h₀ h₁ hset

/-- Weaken a set_rhs precondition using consequence. -/
theorem set_rhs_conseq {pre pre' : RPre} {l : Location} {v : l.ty}
    (h : ∀ h₀ h₁, pre h₀ (h₁.set l v) → pre' h₀ h₁) :
    ∀ h₀ h₁, set_rhs l v pre h₀ h₁ → pre' h₀ h₁ := by
  intro h₀ h₁ hset
  simp only [set_rhs] at hset
  exact h h₀ h₁ hset

/-- Restore with consequence: the most general form.
    Apply the consequence rule to weaken from set_lhs pre to pre'. -/
theorem rHoare_restore_lhs_conseq {α β : Type*} {l : Location} {v : l.ty}
    {pre pre' : RPre} {post : RPost α β} {c₁ : SPComp α} {c₂ : SPComp β}
    (hweaken : ∀ h₀ h₁, pre (h₀.set l v) h₁ → pre' h₀ h₁)
    (hrh : rHoare pre' c₁ c₂ post) :
    rHoare (set_lhs l v pre) c₁ c₂ post :=
  rHoare_conseq (set_lhs_conseq hweaken) (fun _ _ _ _ h => h) hrh

/-- Restore with consequence for right side. -/
theorem rHoare_restore_rhs_conseq {α β : Type*} {l : Location} {v : l.ty}
    {pre pre' : RPre} {post : RPost α β} {c₁ : SPComp α} {c₂ : SPComp β}
    (hweaken : ∀ h₀ h₁, pre h₀ (h₁.set l v) → pre' h₀ h₁)
    (hrh : rHoare pre' c₁ c₂ post) :
    rHoare (set_rhs l v pre) c₁ c₂ post :=
  rHoare_conseq (set_rhs_conseq hweaken) (fun _ _ _ _ h => h) hrh

end CatCrypt.Relational

/-! ## Tactics -/

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational CatCrypt.Invariant

/-- `ssprove_restore_pre` restores the precondition after put operations.

After a `put` operation, the precondition is wrapped in `set_lhs` or `set_rhs`.
This tactic applies the appropriate consequence-based restoration rule.

Example:
```lean
-- Goal: rHoare (set_lhs l v pre) c₁ c₂ post
-- After ssprove_restore_pre:
-- Goal 1: ∀ h₀ h₁, pre (h₀.set l v) h₁ → pre' h₀ h₁
-- Goal 2: rHoare pre' c₁ c₂ post
```
-/
macro "ssprove_restore_pre" : tactic => `(tactic| (
  first
  | apply rHoare_restore_lhs_conseq <;> [intro h₀ h₁ _; skip]
  | apply rHoare_restore_rhs_conseq <;> [intro h₀ h₁ _; skip]
  | fail "ssprove_restore_pre: could not identify set_lhs/set_rhs wrapper"
))

/-- `ssprove_restore_mem` restores the precondition including remembered values.

This is an alias for `ssprove_restore_pre` in the current implementation.
-/
macro "ssprove_restore_mem" : tactic => `(tactic| ssprove_restore_pre)

/-- `ssprove_restore_inv` is an automation tactic that tries various restoration
strategies and attempts to discharge preservation side conditions automatically. -/
macro "ssprove_restore_inv" : tactic => `(tactic| (
  first
  | ssprove_restore_pre <;> [try assumption; skip]
  | fail "ssprove_restore_inv: could not restore invariant automatically"
))

end CatCrypt.Tactics

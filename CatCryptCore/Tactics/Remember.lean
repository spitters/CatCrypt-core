/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCryptCore.Relational.Rules
import CatCryptCore.Invariant.Coupling

/-!
# Memory/Remember Tactics

This file provides tactics and rules for remembering values read from memory locations
during relational proofs. This is useful when the same location is read multiple times
and you want to avoid re-reading it.

## Main definitions

### Rules
* `r_get_remember_lhs` - One-sided get on LHS that adds rem_lhs to precondition
* `r_get_remember_rhs` - One-sided get on RHS that adds rem_rhs to precondition
* `r_get_remind_lhs` - One-sided get on LHS that uses existing rem_lhs from precondition
* `r_get_remind_rhs` - One-sided get on RHS that uses existing rem_rhs from precondition
* `r_forget_lhs` - Weaken precondition by dropping rem_lhs
* `r_forget_rhs` - Weaken precondition by dropping rem_rhs

### Tactics
* `ssprove_forget` - Discard most recent remembered value from precondition
* `ssprove_forget_all` - Discard all remembered values from precondition
* `ssprove_remember_lhs` - Apply r_get_remember_lhs rule
* `ssprove_remember_rhs` - Apply r_get_remember_rhs rule
* `ssprove_remind_lhs` - Apply r_get_remind_lhs rule
* `ssprove_remind_rhs` - Apply r_get_remind_rhs rule

## Usage

When reading from a location, you can "remember" the value for later use.
This adds a `rem_lhs l v` or `rem_rhs l v` conjunct to the precondition.
Later, `remind` rules let you use the remembered value instead of reading again.

```lean
-- When we have a goal with `x <- get l` on the left
-- Apply r_get_remember_lhs to add rem_lhs l x to precondition
ssprove_remember_lhs

-- Later, when we read from the same location again
-- Apply r_get_remind_lhs to use the remembered value
ssprove_remind_lhs
```

## References

* SSProve: theories/Crypt/package/pkg_rhl.v (r_get_remember_lhs, etc.)
* SSProve: theories/Crypt/package/pkg_user_util.v (ssprove_forget)
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob CatCrypt.Invariant

variable {α β γ δ : Type*}

/-! ## Remember Rules -/

/-- One-sided get on the left that remembers the value.

After reading a value `v` from location `l` on the left side,
the precondition is extended with `rem_lhs l v`, remembering that
the left heap has value `v` at location `l`.

This is useful when the same location is read multiple times
and you want to use `r_get_remind_lhs` for subsequent reads.
-/
theorem r_get_remember_lhs {α β : Type} {Φ : RPre} {Ψ : RPost α β}
    (l : Location) {c₂ : SPComp β} {f : l.ty → SPComp α}
    (h : ∀ v, rHoare (Φ ⋊ rem_lhs l v) (f v) c₂ Ψ) :
    rHoare Φ (SPComp.get l >>= f) c₂ Ψ := by
  intro h₁ h₂ hΦ
  have hv := h (h₁.get l) h₁ h₂ ⟨hΦ, rfl⟩
  have heq : (SPComp.get l >>= f) h₁ = f (h₁.get l) h₁ := by
    simp only [bind, SPComp.bind, SPComp.get, SDistr.pure_bind]
  rw [heq]
  exact hv

/-- One-sided get on the right that remembers the value.

After reading a value `v` from location `l` on the right side,
the precondition is extended with `rem_rhs l v`, remembering that
the right heap has value `v` at location `l`.
-/
theorem r_get_remember_rhs {α β : Type} {Φ : RPre} {Ψ : RPost α β}
    (l : Location) {c₁ : SPComp α} {f : l.ty → SPComp β}
    (h : ∀ v, rHoare (Φ ⋊ rem_rhs l v) c₁ (f v) Ψ) :
    rHoare Φ c₁ (SPComp.get l >>= f) Ψ := by
  intro h₁ h₂ hΦ
  have hv := h (h₂.get l) h₁ h₂ ⟨hΦ, rfl⟩
  have heq : (SPComp.get l >>= f) h₂ = f (h₂.get l) h₂ := by
    simp only [bind, SPComp.bind, SPComp.get, SDistr.pure_bind]
  rw [heq]
  exact hv

/-! ## Remind Rules -/

/-- One-sided get on the left that uses a remembered value.

If the precondition contains `rem_lhs l v`, then reading from location `l`
on the left side can be replaced by using the known value `v` directly.

The `[ProvenBy (rem_lhs l v) Φ]` constraint ensures that the precondition
contains the remembered value. This is automatically inferred using the
`ProvenBy` instances.
-/
theorem r_get_remind_lhs {α β : Type} {l : Location} {v : l.ty}
    {Φ : RPre} {Ψ : RPost α β} {f : l.ty → SPComp α} {c₂ : SPComp β}
    [hr : ProvenBy (rem_lhs l v) Φ]
    (h : rHoare Φ (f v) c₂ Ψ) :
    rHoare Φ (SPComp.get l >>= f) c₂ Ψ := by
  intro h₁ h₂ hΦ
  -- Get the remembered value from precondition
  have hrem := hr.holds h₁ h₂ hΦ
  simp only [rem_lhs] at hrem
  -- Show get l h₁ = v
  have heq_val : h₁.get l = v := hrem
  -- Simplify the computation
  have heq : (SPComp.get l >>= f) h₁ = f (h₁.get l) h₁ := by
    simp only [bind, SPComp.bind, SPComp.get, SDistr.pure_bind]
  rw [heq, heq_val]
  exact h h₁ h₂ hΦ

/-- One-sided get on the right that uses a remembered value.

If the precondition contains `rem_rhs l v`, then reading from location `l`
on the right side can be replaced by using the known value `v` directly.
-/
theorem r_get_remind_rhs {α β : Type} {l : Location} {v : l.ty}
    {Φ : RPre} {Ψ : RPost α β} {c₁ : SPComp α} {f : l.ty → SPComp β}
    [hr : ProvenBy (rem_rhs l v) Φ]
    (h : rHoare Φ c₁ (f v) Ψ) :
    rHoare Φ c₁ (SPComp.get l >>= f) Ψ := by
  intro h₁ h₂ hΦ
  -- Get the remembered value from precondition
  have hrem := hr.holds h₁ h₂ hΦ
  simp only [rem_rhs] at hrem
  -- Show get l h₂ = v
  have heq_val : h₂.get l = v := hrem
  -- Simplify the computation
  have heq : (SPComp.get l >>= f) h₂ = f (h₂.get l) h₂ := by
    simp only [bind, SPComp.bind, SPComp.get, SDistr.pure_bind]
  rw [heq, heq_val]
  exact h h₁ h₂ hΦ

/-! ## Forget Rules -/

/-- Weaken precondition by dropping rem_lhs.

This rule drops a remembered value once it is irrelevant to the goal.
It projects out the rem_lhs conjunct from the precondition.
-/
theorem r_forget_lhs {α β : Type*} {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β} {l : Location} {v : l.ty}
    (h : rHoare Φ c₁ c₂ Ψ) :
    rHoare (Φ ⋊ rem_lhs l v) c₁ c₂ Ψ := by
  intro h₁ h₂ ⟨hΦ, _⟩
  exact h h₁ h₂ hΦ

/-- Weaken precondition by dropping rem_rhs.

This rule drops a remembered value once it is irrelevant to the goal.
-/
theorem r_forget_rhs {α β : Type*} {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β} {l : Location} {v : l.ty}
    (h : rHoare Φ c₁ c₂ Ψ) :
    rHoare (Φ ⋊ rem_rhs l v) c₁ c₂ Ψ := by
  intro h₁ h₂ ⟨hΦ, _⟩
  exact h h₁ h₂ hΦ

/-! ## Synchronized Remember Rules -/

/-- Synchronized get that remembers on the left.

When both sides read from synchronized locations (same value on both sides),
and we want to remember the value on the left side.
-/
theorem r_get_vs_get_remember_lhs {α β : Type} {Φ : RPre} {Ψ : RPost α β}
    (l : Location) {f₁ : l.ty → SPComp α} {f₂ : l.ty → SPComp β}
    [ht : ProvenBy (syncsAt l) Φ]
    (h : ∀ v, rHoare (Φ ⋊ rem_lhs l v) (f₁ v) (f₂ v) Ψ) :
    rHoare Φ (SPComp.get l >>= f₁) (SPComp.get l >>= f₂) Ψ := by
  intro h₁ h₂ hΦ
  -- Get synchronization from precondition
  have hsync := ht.holds h₁ h₂ hΦ
  simp only [syncsAt] at hsync
  -- The values are equal
  have heq : h₁.get l = h₂.get l := hsync
  -- Simplify the computations
  have heq₁ : (SPComp.get l >>= f₁) h₁ = f₁ (h₁.get l) h₁ := by
    simp only [bind, SPComp.bind, SPComp.get]; rw [SDistr.pure_bind]
  have heq₂ : (SPComp.get l >>= f₂) h₂ = f₂ (h₂.get l) h₂ := by
    simp only [bind, SPComp.bind, SPComp.get]; rw [SDistr.pure_bind]
  rw [heq₁, heq₂, ← heq]
  exact h (h₁.get l) h₁ h₂ ⟨hΦ, rfl⟩

/-- Synchronized get that remembers on the right.

When both sides read from synchronized locations,
and we want to remember the value on the right side.
-/
theorem r_get_vs_get_remember_rhs {α β : Type} {Φ : RPre} {Ψ : RPost α β}
    (l : Location) {f₁ : l.ty → SPComp α} {f₂ : l.ty → SPComp β}
    [ht : ProvenBy (syncsAt l) Φ]
    (h : ∀ v, rHoare (Φ ⋊ rem_rhs l v) (f₁ v) (f₂ v) Ψ) :
    rHoare Φ (SPComp.get l >>= f₁) (SPComp.get l >>= f₂) Ψ := by
  intro h₁ h₂ hΦ
  -- Get synchronization from precondition
  have hsync := ht.holds h₁ h₂ hΦ
  simp only [syncsAt] at hsync
  -- The values are equal
  have heq : h₁.get l = h₂.get l := hsync
  -- Simplify the computations
  have heq₁ : (SPComp.get l >>= f₁) h₁ = f₁ (h₁.get l) h₁ := by
    simp only [bind, SPComp.bind, SPComp.get]; rw [SDistr.pure_bind]
  have heq₂ : (SPComp.get l >>= f₂) h₂ = f₂ (h₂.get l) h₂ := by
    simp only [bind, SPComp.bind, SPComp.get]; rw [SDistr.pure_bind]
  rw [heq₁, heq₂, heq]
  exact h (h₂.get l) h₁ h₂ ⟨hΦ, rfl⟩

/-! ## Remembers Syncs -/

/-- If we remember a value on one side and locations are synced,
we can derive the remembered value on the other side. -/
theorem Remembers_syncs {s : Side} {l : Location} {v : l.ty} {Φ : RPre}
    [ProvenBy (rem_inv s l v) Φ] [ProvenBy (syncsAt l) Φ] :
    ∀ h₁ h₂, Φ h₁ h₂ → rem_inv s.other l v h₁ h₂ := by
  intro h₁ h₂ hΦ
  have hrem : rem_inv s l v h₁ h₂ :=
    @ProvenBy.holds (rem_inv s l v) Φ inferInstance h₁ h₂ hΦ
  have hsync : syncsAt l h₁ h₂ :=
    @ProvenBy.holds (syncsAt l) Φ inferInstance h₁ h₂ hΦ
  exact rem_sync hrem hsync

end CatCrypt.Relational

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational
open CatCrypt.Invariant
open CatCrypt.Core

/-! ## Forget Tactics -/

/-- `ssprove_forget` discards the most recent remembered value from the precondition.

This tactic looks for a precondition of the form `(Φ ⋊ rem_lhs l v)` or `(Φ ⋊ rem_rhs l v)`
and applies the corresponding forget rule to drop the remembered value.

Example:
```lean
-- Goal: rHoare (Φ ⋊ rem_lhs l v) c₁ c₂ Ψ
ssprove_forget
-- New goal: rHoare Φ c₁ c₂ Ψ
```
-/
macro "ssprove_forget" : tactic => `(tactic| (
  first
  | apply r_forget_rhs
  | apply r_forget_lhs
  | fail "ssprove_forget: no rem_lhs or rem_rhs found in precondition"
))

/-- `ssprove_forget_all` discards all remembered values from the precondition.

This repeatedly applies `ssprove_forget` until no more remembered values remain.

Example:
```lean
-- Goal: rHoare (Φ ⋊ rem_lhs l₁ v₁ ⋊ rem_rhs l₂ v₂ ⋊ rem_lhs l₃ v₃) c₁ c₂ Ψ
ssprove_forget_all
-- New goal: rHoare Φ c₁ c₂ Ψ
```
-/
macro "ssprove_forget_all" : tactic => `(tactic| (
  repeat ssprove_forget
))

/-! ## Remember Tactics -/

/-- `ssprove_remember_lhs` applies the r_get_remember_lhs rule.

This is used when you have a `get l` on the left side and want to
remember the value for later use. The precondition is extended with
`rem_lhs l v`.

Example:
```lean
-- Goal: rHoare Φ (SPComp.get l >>= f) c₂ Ψ
ssprove_remember_lhs
-- New goal: ∀ v, rHoare (Φ ⋊ rem_lhs l v) (f v) c₂ Ψ
```
-/
macro "ssprove_remember_lhs" : tactic => `(tactic| (
  first
  | apply r_get_remember_lhs
  | fail "ssprove_remember_lhs: goal is not a get-bind on LHS"
))

/-- `ssprove_remember_rhs` applies the r_get_remember_rhs rule.

This is used when you have a `get l` on the right side and want to
remember the value for later use.

Example:
```lean
-- Goal: rHoare Φ c₁ (SPComp.get l >>= f) Ψ
ssprove_remember_rhs
-- New goal: ∀ v, rHoare (Φ ⋊ rem_rhs l v) c₁ (f v) Ψ
```
-/
macro "ssprove_remember_rhs" : tactic => `(tactic| (
  first
  | apply r_get_remember_rhs
  | fail "ssprove_remember_rhs: goal is not a get-bind on RHS"
))

/-! ## Remind Tactics -/

/-- `ssprove_remind_lhs` applies the r_get_remind_lhs rule.

This is used when you have a `get l` on the left side and the precondition
already contains `rem_lhs l v`. The get is replaced by using the known value.

Example:
```lean
-- Goal: rHoare (Φ ⋊ rem_lhs l v) (SPComp.get l >>= f) c₂ Ψ
ssprove_remind_lhs
-- New goal: rHoare (Φ ⋊ rem_lhs l v) (f v) c₂ Ψ
```
-/
macro "ssprove_remind_lhs" : tactic => `(tactic| (
  first
  | apply r_get_remind_lhs
  | fail "ssprove_remind_lhs: goal is not a get-bind on LHS or rem_lhs not in precondition"
))

/-- `ssprove_remind_rhs` applies the r_get_remind_rhs rule.

This is used when you have a `get l` on the right side and the precondition
already contains `rem_rhs l v`.

Example:
```lean
-- Goal: rHoare (Φ ⋊ rem_rhs l v) c₁ (SPComp.get l >>= f) Ψ
ssprove_remind_rhs
-- New goal: rHoare (Φ ⋊ rem_rhs l v) c₁ (f v) Ψ
```
-/
macro "ssprove_remind_rhs" : tactic => `(tactic| (
  first
  | apply r_get_remind_rhs
  | fail "ssprove_remind_rhs: goal is not a get-bind on RHS or rem_rhs not in precondition"
))

/-! ## Combined Remember/Remind Tactics -/

/-- `ssprove_get_lhs` handles a get on the left side by either remembering or reminding.

If the precondition already contains `rem_lhs l v`, it uses the remembered value.
Otherwise, it remembers the new value.
-/
macro "ssprove_get_lhs" : tactic => `(tactic| (
  first
  | ssprove_remind_lhs
  | ssprove_remember_lhs
  | fail "ssprove_get_lhs: goal is not a get-bind on LHS"
))

/-- `ssprove_get_rhs` handles a get on the right side by either remembering or reminding.

If the precondition already contains `rem_rhs l v`, it uses the remembered value.
Otherwise, it remembers the new value.
-/
macro "ssprove_get_rhs" : tactic => `(tactic| (
  first
  | ssprove_remind_rhs
  | ssprove_remember_rhs
  | fail "ssprove_get_rhs: goal is not a get-bind on RHS"
))

end CatCrypt.Tactics

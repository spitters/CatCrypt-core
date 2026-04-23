/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Relational.Rules
import CatCrypt.Tactics.Basic

/-!
# Weakest Precondition Tactics

This file provides tactics for weakest precondition reasoning in pRHL,
analogous to EasyCrypt's `wp` tactic.

## Main tactics

* `ssprove_wp` - process deterministic suffix backwards, computing the WP
* `ssprove_wp_step` - process one WP step from the tail

## What EasyCrypt does

EasyCrypt's `wp` processes the deterministic suffix of programs backwards,
computing the weakest precondition. For each assignment `x <- e`, it
substitutes `e` for `x` in the postcondition. It stops at random sampling,
procedure calls, or loops.

## How it maps to SPComp

In our monadic setting, the "deterministic suffix" consists of `pure`, `get`,
`set` operations chained by `>>=`. The wp computation:

| SPComp tail | WP transformation |
|-------------|-------------------|
| `pure v`    | Substitute `v` for result in postcondition |
| `set l v >>= fun _ => k` | Push heap update into postcondition |
| `get l >>= fun x => k`   | Push heap lookup into postcondition |
| `sample`, `fail`          | **Stop** — non-deterministic |

## References

* EasyCrypt: ecWp tactic
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β γ δ : Type}

/-! ## WP Rules: Absorbing Tail Operations into Postcondition

These rules process the deterministic suffix of both programs simultaneously,
absorbing `pure`, `get`, and `set` operations into the postcondition.
-/

/-- WP for `pure f(x)` at the end of both programs.

Both programs end with `c >>= fun x => pure (f x)`. We absorb the
pure map into the postcondition: instead of proving `Ψ (f a) h₁ (f b) h₂`,
we prove a judgment about `c₁` and `c₂` with a modified postcondition
that pre-applies `f₁` and `f₂`.
-/
theorem rHoare_wp_ret {Φ : RPre} {Ψ : RPost γ δ}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {f₁ : α → γ} {f₂ : β → δ}
    (h : rHoare Φ c₁ c₂ (fun a₁ h₁ a₂ h₂ => Ψ (f₁ a₁) h₁ (f₂ a₂) h₂)) :
    rHoare Φ (c₁.bind (fun x => pure (f₁ x))) (c₂.bind (fun x => pure (f₂ x))) Ψ := by
  intro h₁ h₂ hΦ
  have hh := h h₁ h₂ hΦ
  simp only [SPComp.bind_def]
  apply liftR_bind hh
  intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ hΨ
  apply liftR_pure
  exact hΨ

/-- WP for `set l (g x)` at the end of both programs.

Both programs end with `c >>= fun x => set l₁ (g₁ x)` and
`c >>= fun x => set l₂ (g₂ x)`. We absorb the set into the
postcondition by requiring `Ψ` to hold after the heap updates.
-/
theorem rHoare_wp_set {Φ : RPre} {Ψ : RPost Unit Unit}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {l₁ l₂ : Location} {g₁ : α → l₁.ty} {g₂ : β → l₂.ty}
    (h : rHoare Φ c₁ c₂
      (fun a₁ h₁ a₂ h₂ => Ψ () (h₁.set l₁ (g₁ a₁)) () (h₂.set l₂ (g₂ a₂)))) :
    rHoare Φ (c₁.bind (fun x => SPComp.set l₁ (g₁ x)))
             (c₂.bind (fun x => SPComp.set l₂ (g₂ x))) Ψ := by
  intro h₁ h₂ hΦ
  have hh := h h₁ h₂ hΦ
  simp only [SPComp.bind_def, SPComp.set_def]
  apply liftR_bind hh
  intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ hΨ
  apply liftR_pure
  exact hΨ

/-- WP for `get l` followed by pure (absorbs get into postcondition).

Both programs do `c >>= fun x => get l >>= fun v => pure (f x v)` at the tail.
We absorb this by substituting `h.get l` for `v` in the postcondition.
Note: γ, δ constrained to Type since l.ty : Type.
-/
theorem rHoare_wp_get_ret {Φ : RPre} {Ψ : RPost γ δ}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {l₁ l₂ : Location}
    {f₁ : α → l₁.ty → γ} {f₂ : β → l₂.ty → δ}
    (h : rHoare Φ c₁ c₂
      (fun a₁ h₁ a₂ h₂ => Ψ (f₁ a₁ (h₁.get l₁)) h₁ (f₂ a₂ (h₂.get l₂)) h₂)) :
    rHoare Φ
      (c₁.bind (fun x => SPComp.get l₁ >>= fun v => pure (f₁ x v)))
      (c₂.bind (fun x => SPComp.get l₂ >>= fun v => pure (f₂ x v))) Ψ := by
  intro h₁ h₂ hΦ
  have hh := h h₁ h₂ hΦ
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.get_def, SDistr.pure_bind]
  apply liftR_bind hh
  intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ hΨ
  apply liftR_pure
  exact hΨ

/-! ## One-Sided WP Rules

These rules process the deterministic suffix on only one side.
-/

/-- WP for `pure f(x)` on the left side only. -/
theorem rHoare_wp_ret_lhs {Φ : RPre} {Ψ : RPost γ β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {f₁ : α → γ}
    (h : rHoare Φ c₁ c₂ (fun a₁ h₁ a₂ h₂ => Ψ (f₁ a₁) h₁ a₂ h₂)) :
    rHoare Φ (c₁.bind (fun x => pure (f₁ x))) c₂ Ψ := by
  intro h₁ h₂ hΦ
  have hh := h h₁ h₂ hΦ
  simp only [SPComp.bind_def]
  rw [← SDistr.bind_pure (c₂ h₂)]
  apply liftR_bind hh
  intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ hΨ
  apply liftR_pure
  exact hΨ

/-- WP for `pure f(x)` on the right side only. -/
theorem rHoare_wp_ret_rhs {Φ : RPre} {Ψ : RPost α δ}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {f₂ : β → δ}
    (h : rHoare Φ c₁ c₂ (fun a₁ h₁ a₂ h₂ => Ψ a₁ h₁ (f₂ a₂) h₂)) :
    rHoare Φ c₁ (c₂.bind (fun x => pure (f₂ x))) Ψ := by
  intro h₁ h₂ hΦ
  have hh := h h₁ h₂ hΦ
  simp only [SPComp.bind_def]
  rw [← SDistr.bind_pure (c₁ h₁)]
  apply liftR_bind hh
  intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ hΨ
  apply liftR_pure
  exact hΨ

/-- WP for `set l (g x)` on the left side only. -/
theorem rHoare_wp_set_lhs {Φ : RPre} {Ψ : RPost Unit β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {l : Location} {g : α → l.ty}
    (h : rHoare Φ c₁ c₂
      (fun a₁ h₁ a₂ h₂ => Ψ () (h₁.set l (g a₁)) a₂ h₂)) :
    rHoare Φ (c₁.bind (fun x => SPComp.set l (g x))) c₂ Ψ := by
  intro h₁ h₂ hΦ
  have hh := h h₁ h₂ hΦ
  simp only [SPComp.bind_def, SPComp.set_def]
  rw [← SDistr.bind_pure (c₂ h₂)]
  apply liftR_bind hh
  intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ hΨ
  apply liftR_pure
  exact hΨ

/-- WP for `set l (g x)` on the right side only. -/
theorem rHoare_wp_set_rhs {Φ : RPre} {Ψ : RPost α Unit}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {l : Location} {g : β → l.ty}
    (h : rHoare Φ c₁ c₂
      (fun a₁ h₁ a₂ h₂ => Ψ a₁ h₁ () (h₂.set l (g a₂)))) :
    rHoare Φ c₁ (c₂.bind (fun x => SPComp.set l (g x))) Ψ := by
  intro h₁ h₂ hΦ
  have hh := h h₁ h₂ hΦ
  simp only [SPComp.bind_def, SPComp.set_def]
  rw [← SDistr.bind_pure (c₁ h₁)]
  apply liftR_bind hh
  intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ hΨ
  apply liftR_pure
  exact hΨ

end CatCrypt.Relational

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational CatCrypt.Core

/-! ## WP Tactics -/

/-- `ssprove_wp` processes the deterministic suffix of both programs
backwards, computing the weakest precondition.

It repeatedly peels off deterministic tail operations (`pure`, `set`, `get`)
from both sides, absorbing them into the postcondition.

The tactic stops at `sample`, `fail`, or any non-deterministic operation.

Example:
```
-- Before ssprove_wp:
-- rHoare Φ (do let k ← sample Bool; pure (xor k x))
--           (do let k ← sample Bool; pure k)
--           (fun a h₁ b h₂ => a = b)
-- After ssprove_wp:
-- rHoare Φ (sample Bool) (sample Bool)
--           (fun k₁ h₁ k₂ h₂ => xor k₁ x = k₂)
```
-/
macro "ssprove_wp" : tactic => `(tactic| (
  try ssprove_code_simpl
  repeat (first
    | apply rHoare_wp_ret
    | apply rHoare_wp_set
    | apply rHoare_wp_get_ret
    | apply rHoare_wp_ret_lhs
    | apply rHoare_wp_ret_rhs
    | apply rHoare_wp_set_lhs
    | apply rHoare_wp_set_rhs
  )
))

/-- `ssprove_wp_step` processes exactly one wp step from the tail. -/
macro "ssprove_wp_step" : tactic => `(tactic| (
  first
  | apply rHoare_wp_ret
  | apply rHoare_wp_set
  | apply rHoare_wp_get_ret
  | apply rHoare_wp_ret_lhs
  | apply rHoare_wp_ret_rhs
  | apply rHoare_wp_set_lhs
  | apply rHoare_wp_set_rhs
  | fail "ssprove_wp_step: no deterministic tail found"
))

end CatCrypt.Tactics

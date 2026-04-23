/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Relational.Rules

/-!
# Conditional Resolution Tactics

This file provides tactics for resolving conditional branches in relational
proofs, inspired by EasyCrypt's `rcondt` and `rcondf` tactics.

## Main tactics

* `ssprove_rcondt` - resolve a conditional when condition is always true
* `ssprove_rcondf` - resolve a conditional when condition is always false
* `ssprove_ite` - try to resolve conditionals automatically

## Main lemmas

* `rHoare_ite_true` - if condition is true under precondition, reduce to then-branch
* `rHoare_ite_false` - if condition is false under precondition, reduce to else-branch
* `rHoare_ite_left_true/false` - asymmetric: condition on left side only
* `rHoare_ite_right_true/false` - asymmetric: condition on right side only

## Design rationale

Crypto games are full of `if b then ... else ...` branches. In many proofs,
the precondition (invariant) determines which branch is taken. EasyCrypt's
`rcondt`/`rcondf` tactics automate this pattern. Without these tactics,
users must manually `simp [h]` or `split_ifs`, which is verbose and fragile.

## References

* EasyCrypt: `rcondt`, `rcondf` tactics
* CatCrypt: manual branch resolution via `simp`
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β γ δ : Type*}

/-! ## Symmetric if-then-else rules (same condition both sides) -/

/-- If condition is true under the precondition, reduce both sides to then-branch. -/
theorem rHoare_ite_true {Φ : RPre} {Ψ : RPost α β}
    {c : Bool} {t₁ e₁ : SPComp α} {t₂ e₂ : SPComp β}
    (hc : ∀ h₁ h₂, Φ h₁ h₂ → c = true)
    (ht : rHoare Φ t₁ t₂ Ψ) :
    rHoare Φ (if c then t₁ else e₁) (if c then t₂ else e₂) Ψ := by
  intro h₁ h₂ hΦ
  simp only [hc h₁ h₂ hΦ, ↓reduceIte]
  exact ht h₁ h₂ hΦ

/-- If condition is false under the precondition, reduce both sides to else-branch. -/
theorem rHoare_ite_false {Φ : RPre} {Ψ : RPost α β}
    {c : Bool} {t₁ e₁ : SPComp α} {t₂ e₂ : SPComp β}
    (hc : ∀ h₁ h₂, Φ h₁ h₂ → c = false)
    (he : rHoare Φ e₁ e₂ Ψ) :
    rHoare Φ (if c then t₁ else e₁) (if c then t₂ else e₂) Ψ := by
  intro h₁ h₂ hΦ
  simp only [hc h₁ h₂ hΦ, ↓reduceIte, Bool.false_eq_true]
  exact he h₁ h₂ hΦ

/-! ## Asymmetric rules (condition on one side only) -/

/-- Left side has condition true, right side is unconditional. -/
theorem rHoare_ite_left_true {Φ : RPre} {Ψ : RPost α β}
    {c : Bool} {t₁ e₁ : SPComp α} {c₂ : SPComp β}
    (hc : ∀ h₁ h₂, Φ h₁ h₂ → c = true)
    (ht : rHoare Φ t₁ c₂ Ψ) :
    rHoare Φ (if c then t₁ else e₁) c₂ Ψ := by
  intro h₁ h₂ hΦ
  simp only [hc h₁ h₂ hΦ, ↓reduceIte]
  exact ht h₁ h₂ hΦ

/-- Left side has condition false, right side is unconditional. -/
theorem rHoare_ite_left_false {Φ : RPre} {Ψ : RPost α β}
    {c : Bool} {t₁ e₁ : SPComp α} {c₂ : SPComp β}
    (hc : ∀ h₁ h₂, Φ h₁ h₂ → c = false)
    (he : rHoare Φ e₁ c₂ Ψ) :
    rHoare Φ (if c then t₁ else e₁) c₂ Ψ := by
  intro h₁ h₂ hΦ
  simp only [hc h₁ h₂ hΦ, ↓reduceIte, Bool.false_eq_true]
  exact he h₁ h₂ hΦ

/-- Right side has condition true, left side is unconditional. -/
theorem rHoare_ite_right_true {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c : Bool} {t₂ e₂ : SPComp β}
    (hc : ∀ h₁ h₂, Φ h₁ h₂ → c = true)
    (ht : rHoare Φ c₁ t₂ Ψ) :
    rHoare Φ c₁ (if c then t₂ else e₂) Ψ := by
  intro h₁ h₂ hΦ
  simp only [hc h₁ h₂ hΦ, ↓reduceIte]
  exact ht h₁ h₂ hΦ

/-- Right side has condition false, left side is unconditional. -/
theorem rHoare_ite_right_false {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c : Bool} {t₂ e₂ : SPComp β}
    (hc : ∀ h₁ h₂, Φ h₁ h₂ → c = false)
    (he : rHoare Φ c₁ e₂ Ψ) :
    rHoare Φ c₁ (if c then t₂ else e₂) Ψ := by
  intro h₁ h₂ hΦ
  simp only [hc h₁ h₂ hΦ, ↓reduceIte, Bool.false_eq_true]
  exact he h₁ h₂ hΦ

/-! ## Decidable condition versions

These handle `if (decide P) then ...` patterns, which are common when
conditions are decidable propositions rather than booleans. -/

/-- If a decidable proposition holds under precondition, take then-branch. -/
theorem rHoare_dite_true {Φ : RPre} {Ψ : RPost α β}
    {P : Prop} [inst : Decidable P] {t₁ : P → SPComp α} {e₁ : ¬P → SPComp α}
    {t₂ : P → SPComp β} {e₂ : ¬P → SPComp β}
    (hp : ∀ h₁ h₂, Φ h₁ h₂ → P)
    (ht : ∀ h, rHoare Φ (t₁ h) (t₂ h) Ψ) :
    rHoare Φ (dite P t₁ e₁) (dite P t₂ e₂) Ψ := by
  intro h₁ h₂ hΦ
  have hP := hp h₁ h₂ hΦ
  cases inst with
  | isTrue h => exact ht h h₁ h₂ hΦ
  | isFalse h => exact absurd hP h

/-- If a decidable proposition fails under precondition, take else-branch. -/
theorem rHoare_dite_false {Φ : RPre} {Ψ : RPost α β}
    {P : Prop} [inst : Decidable P] {t₁ : P → SPComp α} {e₁ : ¬P → SPComp α}
    {t₂ : P → SPComp β} {e₂ : ¬P → SPComp β}
    (hp : ∀ h₁ h₂, Φ h₁ h₂ → ¬P)
    (he : ∀ h, rHoare Φ (e₁ h) (e₂ h) Ψ) :
    rHoare Φ (dite P t₁ e₁) (dite P t₂ e₂) Ψ := by
  intro h₁ h₂ hΦ
  have hP := hp h₁ h₂ hΦ
  cases inst with
  | isTrue h => exact absurd h hP
  | isFalse h => exact he h h₁ h₂ hΦ

/-! ## Code-level if-then-else equality lemmas

These lemmas state that if a condition is known, if-then-else simplifies.
Useful for rewriting inside SPComp terms. -/

/-- If condition is true, `if c then t else e = t` at SPComp level. -/
theorem SPComp.ite_true_eq {c : Bool} {t e : SPComp α} (hc : c = true) :
    (if c then t else e) = t := by simp [hc]

/-- If condition is false, `if c then t else e = e` at SPComp level. -/
theorem SPComp.ite_false_eq {c : Bool} {t e : SPComp α} (hc : c = false) :
    (if c then t else e) = e := by simp [hc]

end CatCrypt.Relational

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational
open CatCrypt.Core

/-! ## Conditional Resolution Tactics -/

/-- `ssprove_rcondt` resolves a conditional branch by proving the condition is true.

When the goal has `if c then t else e` on one or both sides of an rHoare judgment,
and the precondition implies `c = true`, this tactic simplifies to the then-branch.

Generates a subgoal for proving `c = true` under the precondition.

Example:
```lean
theorem example (hb : ∀ h₁ h₂, Φ h₁ h₂ → b = true) :
    rHoare Φ (if b then t₁ else e₁) (if b then t₂ else e₂) Ψ := by
  ssprove_rcondt
  · exact hb  -- prove condition is true
  · ...       -- prove rHoare Φ t₁ t₂ Ψ
```
-/
macro "ssprove_rcondt" : tactic => `(tactic| (
  first
  | apply rHoare_ite_true
  | apply rHoare_ite_left_true
  | apply rHoare_ite_right_true
  | fail "ssprove_rcondt: no if-then-else found in goal"
))

/-- `ssprove_rcondf` resolves a conditional branch by proving the condition is false.

When the goal has `if c then t else e` on one or both sides of an rHoare judgment,
and the precondition implies `c = false`, this tactic simplifies to the else-branch.

Generates a subgoal for proving `c = false` under the precondition.

Example:
```lean
theorem example (hb : ∀ h₁ h₂, Φ h₁ h₂ → b = false) :
    rHoare Φ (if b then t₁ else e₁) (if b then t₂ else e₂) Ψ := by
  ssprove_rcondf
  · exact hb  -- prove condition is false
  · ...       -- prove rHoare Φ e₁ e₂ Ψ
```
-/
macro "ssprove_rcondf" : tactic => `(tactic| (
  first
  | apply rHoare_ite_false
  | apply rHoare_ite_left_false
  | apply rHoare_ite_right_false
  | fail "ssprove_rcondf: no if-then-else found in goal"
))

/-- `ssprove_ite` tries to resolve if-then-else branches automatically.

This tactic first tries `split_ifs` and then attempts to close goals with
`simp_all`, `assumption`, or `decide`.

Example:
```lean
theorem example : rHoare Φ (if true then t₁ else e₁) c₂ Ψ := by
  ssprove_ite
```
-/
macro "ssprove_ite" : tactic => `(tactic| (
  first
  | simp only [ite_true, ite_false]
  | split_ifs <;> first | assumption | simp_all | decide
  | fail "ssprove_ite: could not resolve if-then-else"
))

end CatCrypt.Tactics

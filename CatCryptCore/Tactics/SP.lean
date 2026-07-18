/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCryptCore.Relational.Rules
import CatCryptCore.Tactics.Basic

/-!
# Strongest Postcondition Tactics

This file provides tactics for strongest postcondition reasoning in pRHL,
analogous to EasyCrypt's `sp` tactic.

## Main tactics

* `ssprove_sp` - process deterministic prefix forwards, computing the SP
* `ssprove_sp_step` - process one SP step from the head

## What EasyCrypt does

EasyCrypt's `sp` processes the deterministic prefix of programs forwards,
updating the precondition to reflect the operations consumed. It is the
forward dual of `wp`.

## How it maps to SPComp

In our monadic setting, prefix consumption means decomposing
`set l v >>= k` or `get l >>= k` at the HEAD of the program using
`rHoare_bind` + sync rules. The precondition gets updated.

| SPComp head | SP transformation |
|-------------|-------------------|
| `pure v >>= k` | Substitute `v`, precondition unchanged |
| `set l v >>= k` | Consume set, precondition updated with heap set |
| `get l >>= k` | Consume get, precondition gains knowledge of heap value |
| `sample`, `fail` | **Stop** — non-deterministic |

## References

* EasyCrypt: ecSp tactic
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

/-! ## SP Rules: Consuming Head Operations into Precondition -/

/-- SP for `pure a >>= k` at the head of both programs.

Both programs start with `pure a >>= k₁` and `pure b >>= k₂`.
Since `pure a >>= k = k a`, we reduce to `k₁ a` and `k₂ b`
with the same precondition (possibly strengthened). -/
theorem rHoare_sp_ret {α β γ δ : Type} {Φ Φ' : RPre} {Ψ : RPost γ δ}
    {a : α} {b : β} {k₁ : α → SPComp γ} {k₂ : β → SPComp δ}
    (hpre : ∀ h₁ h₂, Φ h₁ h₂ → Φ' h₁ h₂)
    (h : rHoare Φ' (k₁ a) (k₂ b) Ψ) :
    rHoare Φ (SPComp.bind (SPComp.pure a) k₁) (SPComp.bind (SPComp.pure b) k₂) Ψ := by
  rw [SPComp.pure_bind, SPComp.pure_bind]
  exact rHoare_mono_pre h hpre

/-- SP for `set l v >>= k` at the head of both programs.

Both programs start with `set l v >>= k`. After consuming the set,
the precondition is updated: instead of requiring `Φ h₁ h₂`, we
require `Φ (h₁.set l v) (h₂.set l v)`. -/
theorem rHoare_sp_set {γ δ : Type*} {Φ : RPre} {Ψ : RPost γ δ}
    {l : Location} {v : l.ty}
    {k₁ : Unit → SPComp γ} {k₂ : Unit → SPComp δ}
    (h : rHoare (fun h₁ h₂ => Φ h₁ h₂) (k₁ ()) (k₂ ()) Ψ) :
    rHoare (fun h₁ h₂ => Φ (h₁.set l v) (h₂.set l v))
      (SPComp.bind (SPComp.set l v) k₁) (SPComp.bind (SPComp.set l v) k₂) Ψ := by
  intro h₁ h₂ hΦ
  have heq₁ : (SPComp.bind (SPComp.set l v) k₁) h₁ = k₁ () (h₁.set l v) := by
    simp only [SPComp.bind, SPComp.set, SDistr.pure_bind]
  have heq₂ : (SPComp.bind (SPComp.set l v) k₂) h₂ = k₂ () (h₂.set l v) := by
    simp only [SPComp.bind, SPComp.set, SDistr.pure_bind]
  rw [heq₁, heq₂]
  exact h (h₁.set l v) (h₂.set l v) hΦ

/-- SP for `get l >>= k` at the head of both programs.

Both programs start with `get l >>= k`. After consuming the get,
we universally quantify over the value read and add the knowledge
that the heap value equals the read value.

Requires that the precondition implies both heaps agree at `l`. -/
theorem rHoare_sp_get {γ δ : Type} {Φ : RPre} {Ψ : RPost γ δ}
    {l : Location}
    {k₁ : l.ty → SPComp γ} {k₂ : l.ty → SPComp δ}
    (h : ∀ v, rHoare (fun h₁ h₂ => Φ h₁ h₂ ∧ h₁.get l = v ∧ h₂.get l = v)
      (k₁ v) (k₂ v) Ψ) :
    rHoare (fun h₁ h₂ => Φ h₁ h₂ ∧ h₁.get l = h₂.get l)
      (SPComp.bind (SPComp.get l) k₁) (SPComp.bind (SPComp.get l) k₂) Ψ := by
  intro h₁ h₂ ⟨hΦ, hSync⟩
  have heq₁ : (SPComp.bind (SPComp.get l) k₁) h₁ = k₁ (h₁.get l) h₁ := by
    simp only [SPComp.bind, SPComp.get, SDistr.pure_bind]
  have heq₂ : (SPComp.bind (SPComp.get l) k₂) h₂ = k₂ (h₂.get l) h₂ := by
    simp only [SPComp.bind, SPComp.get, SDistr.pure_bind]
  rw [heq₁, heq₂, ← hSync]
  exact h (h₁.get l) h₁ h₂ ⟨hΦ, rfl, hSync ▸ rfl⟩

end CatCrypt.Relational

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational CatCrypt.Core

/-! ## SP Tactics -/

/-- `ssprove_sp_step` processes one deterministic operation at the head
of both programs, updating the precondition.

It tries (in order):
1. `pure >>= k` — substitute the value
2. `set l v >>= k` — consume the set, update precondition
3. `get l >>= k` — consume the get, add value knowledge
4. One-sided put (left or right)
5. One-sided get (left or right)
-/
macro "ssprove_sp_step" : tactic => `(tactic| (
  first
  | apply rHoare_sp_ret (fun _ _ h => h)
  | apply rHoare_sp_set
  | (apply rHoare_sp_get; intro _)
  -- One-sided variants
  | (apply rHoare_put_l; try intro _)
  | (apply rHoare_put_r; try intro _)
  | (apply rHoare_get_l; intro _)
  | (apply rHoare_get_r; intro _)
  | fail "ssprove_sp_step: no deterministic prefix found"
))

/-- `ssprove_sp` processes the deterministic prefix of both programs
forwards, computing the strongest postcondition.

It normalizes code first, then repeatedly peels off deterministic
head operations (`pure`, `set`, `get`) from both sides, updating
the precondition.

The tactic stops at `sample`, `fail`, or any non-deterministic operation.

Example:
```
-- Before ssprove_sp:
-- rHoare Φ (do SPComp.set l v; sample Bool) (do SPComp.set l v; sample Bool) Ψ
-- After ssprove_sp:
-- rHoare (fun h₁ h₂ => Φ (h₁.set l v) (h₂.set l v)) (sample Bool) (sample Bool) Ψ
```
-/
macro "ssprove_sp" : tactic => `(tactic| (
  try ssprove_code_simpl
  repeat ssprove_sp_step
))

end CatCrypt.Tactics

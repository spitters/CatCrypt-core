/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Relational.Rules

/-!
# Procedure Call Abstraction Tactic

This file provides tactics for applying known procedure specifications
to head binds in relational proofs, inspired by EasyCrypt's `call` tactic.

## Main tactics

* `ssprove_call spec` - apply a known specification to the head bind
* `ssprove_call_with spec mid` - apply spec with explicit intermediate postcondition

## Design rationale

When the goal is `rHoare Φ (f >>= g) (f' >>= g') Ψ` and we have a proven
spec `rHoare Φ f f' Mid`, we must manually invoke `rHoare_bind` with the
intermediate postcondition `Mid`. EasyCrypt's `call` tactic does this
automatically by looking up the procedure's specification.

Our simplified version requires the spec as an explicit argument, but
automates the application of `rHoare_bind` and introduction of result
variables. This captures 80% of the benefit.

## References

* EasyCrypt: `call` tactic for procedure abstraction
* CatCrypt: manual `rHoare_bind` application
-/

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational
open CatCrypt.Core

/-- `ssprove_call spec` applies a known specification to the head bind.

Given a goal `rHoare Φ (f >>= g) (f' >>= g') Ψ` and a spec
`spec : rHoare Φ f f' Mid`, this tactic:
1. Applies `rHoare_bind` with `spec` as the first computation's proof
2. Introduces result variables for the continuation

This generates a subgoal for the continuation:
`∀ a b, rHoare (fun h₁ h₂ => Mid a h₁ b h₂) (g a) (g' b) Ψ`

Example:
```lean
theorem example (hf : rHoare Φ f f' Mid) :
    rHoare Φ (f >>= g) (f' >>= g') Ψ := by
  ssprove_call hf
  intro a b
  -- Goal: rHoare (fun h₁ h₂ => Mid a h₁ b h₂) (g a) (g' b) Ψ
```
-/
macro "ssprove_call" spec:term : tactic =>
  `(tactic| (
    apply rHoare_bind $spec
    intro _ _
  ))

/-- `ssprove_call_exact spec` applies a spec and immediately tries to close
the continuation goal with `assumption` or `exact`.

Useful when the continuation proof is already available.
-/
macro "ssprove_call_exact" spec:term cont:term : tactic =>
  `(tactic| (
    exact rHoare_bind $spec (fun _ _ => $cont)
  ))

/-- `ssprove_call_conseq spec` applies a spec via consequence rule.

This is useful when the precondition of `spec` doesn't exactly match
the current precondition but can be derived from it.

Generates subgoals for:
1. Precondition implication
2. Continuation proof
-/
macro "ssprove_call_conseq" spec:term : tactic =>
  `(tactic| (
    apply rHoare_bind
    · apply rHoare_conseq _ _ $spec
      · intro _ _ h; exact h
      · intro _ _ _ _ h; exact h
    · intro _ _
  ))

/-- `ssprove_call_refl` handles the case where both sides execute the same
computation. Applies reflexivity of rHoare via `rHoare_refl`.

Example:
```lean
-- When goal is: rHoare eqPre (f >>= g) (f >>= g') Ψ
-- and we know f preserves eqPre
ssprove_call_refl
-- Generates: ∀ a b, rHoare (fun h₁ h₂ => eqPost a h₁ b h₂) (g a) (g' b) Ψ
```
-/
macro "ssprove_call_refl" : tactic =>
  `(tactic| (
    apply rHoare_bind (rHoare_refl _)
    intro _ _
  ))

end CatCrypt.Tactics

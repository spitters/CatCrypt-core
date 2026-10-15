/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import CatCryptCore.Relational.Rules

/-!
# Procedure Call Abstraction Tactic

This file provides tactics for applying known procedure specifications
to head binds in relational proofs, inspired by EasyCrypt's `call` tactic.

## Main tactics

* `ssprove_call spec` - apply a known specification to the head bind

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

@[expose] public section

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

end CatCrypt.Tactics

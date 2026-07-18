/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCryptCore.Tactics.Basic

/-!
# Procedure Unfolding Tactics

This file provides tactics for unfolding game and oracle definitions,
analogous to EasyCrypt's `proc` tactic.

## Main tactics

* `ssprove_proc` - unfold named definitions and normalize SPComp
* `ssprove_proc!` - aggressive version that also unfolds let bindings

## What EasyCrypt does

In EasyCrypt, `proc` replaces procedure identifiers with their bodies,
turning a goal about named procedures into a goal about code.

## How it maps to CatCrypt

Since our games are plain Lean functions (not a separate language),
`proc` amounts to: unfold the game/oracle definitions + normalize.

## References

* EasyCrypt: ecProc tactic
* SSProve: theories/Crypt/package/pkg_rhl.v
-/

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational CatCrypt.Core

/-- `ssprove_proc [d₁, d₂, ...]` unfolds the given definitions in the goal
and normalizes the resulting SPComp expressions.

This is the CatCrypt analogue of EasyCrypt's `proc` tactic.

Example:
```
noncomputable def myGame : SPComp Bool := do
  let k ← SPComp.sample Bool
  SPComp.pure k

theorem game_equiv : rHoare eqPre myGame myGame eqPost := by
  ssprove_proc [myGame]
  -- Goal now shows the unfolded code
  ...
```
-/
macro "ssprove_proc" "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [$[$defs],*]
  try ssprove_code_simpl
))

/-- `ssprove_proc!` aggressively unfolds all local definitions and normalizes.

This variant uses `simp` with Function.comp and monad laws to expand
all definitions in the goal, then normalizes the monad structure.

Use this when you don't want to specify which definitions to unfold.

Example:
```
theorem game_equiv : rHoare eqPre complexGame complexGame eqPost := by
  ssprove_proc!
  -- All definitions unfolded and code normalized
  ...
```
-/
macro "ssprove_proc!" : tactic => `(tactic| (
  simp only [Function.comp, SPComp.monad_bind_eq]
  try ssprove_code_simpl
))

/-- `ssprove_proc_lhs [d₁, d₂, ...]` unfolds definitions only on the left side
of a relational judgment.

Example:
```
theorem game_equiv : rHoare Φ myGame otherGame Ψ := by
  ssprove_proc_lhs [myGame]
  -- Only left side is unfolded
```
-/
macro "ssprove_proc_lhs" "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  conv => arg 2; simp only [$[$defs],*]
  try ssprove_code_simpl
))

/-- `ssprove_proc_rhs [d₁, d₂, ...]` unfolds definitions only on the right side
of a relational judgment.

Example:
```
theorem game_equiv : rHoare Φ myGame otherGame Ψ := by
  ssprove_proc_rhs [otherGame]
  -- Only right side is unfolded
```
-/
macro "ssprove_proc_rhs" "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  conv => arg 3; simp only [$[$defs],*]
  try ssprove_code_simpl
))

end CatCrypt.Tactics

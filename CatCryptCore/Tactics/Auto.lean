/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import CatCryptCore.Tactics.WP
public import CatCryptCore.Tactics.Sync
public import CatCryptCore.Tactics.ProofFrog
public import CatCryptCore.Tactics.Conditional

/-!
# EasyCrypt-Style Auto Tactic

This file provides an `auto`-style meta-tactic that chains together
wp, sync, conditional resolution, and goal closure, analogous to
EasyCrypt's `auto` tactic.

## Main tactics

* `ssprove_auto_step` - one round; fails unless it changes a goal
* `ssprove_auto_repeat` - at most 64 rounds of `ssprove_auto_step`
* `ssprove_auto_ec` - EasyCrypt-style auto: wp + rnd + skip, repeated
* `ssprove_auto_ec!` - `rHoare_refl` first, then `ssprove_auto_ec`

## What EasyCrypt does

EasyCrypt's `auto` is a meta-tactic that chains:
1. `wp` to consume deterministic suffixes
2. `rnd` for random sampling
3. `skip` for empty programs
4. Repeats until no progress

## How it maps to CatCrypt

We chain our existing tactics in the same order:
1. `ssprove_wp` for deterministic tails
2. `ssprove_sync` for synchronized operations (EasyCrypt's `rnd`)
3. `rHoare_ret_same` / `rHoare_refl` for empty programs (EasyCrypt's `skip`)
4. `ssprove_rcondt` / `ssprove_rcondf` for conditionals

## References

* EasyCrypt: ecAuto tactic
-/

@[expose] public section

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational CatCrypt.Core

/-- `ssprove_auto_step` performs one round of EasyCrypt-style automation: the
first of the following alternatives that succeeds and makes progress.
1. WP step (consume deterministic tail)
2. Sync rule (coupling for matching operations)
3. Conditional resolution
4. One-sided sampling
5. Dead code elimination
6. Goal closure (assumption)

An alternative makes progress when the resulting goal list differs from the
previous one in its goal types or hypothesis counts. An alternative that fails
or makes no progress is undone and the next one is tried; the step fails when
none makes progress.
-/
elab "ssprove_auto_step" : tactic => do
  let shape : TacticM (List (Expr × Nat)) := do
    (← getGoals).mapM fun g => do
      pure ((← instantiateMVars (← g.getType)), (← g.getDecl).lctx.numIndices)
  let alts : Array (TSyntax `tactic) := #[
    ← `(tactic| ssprove_wp_step),
    ← `(tactic| ssprove_sync),
    ← `(tactic| ssprove_rcondt),
    ← `(tactic| ssprove_rcondf),
    ← `(tactic| (apply rHoare_sample_l; intro _)),
    ← `(tactic| (apply rHoare_sample_r; intro _)),
    ← `(tactic| ssprove_dead_code),
    ← `(tactic| assumption)]
  let before ← shape
  for alt in alts do
    let s ← saveState
    let progressed ← try
        evalTactic alt
        pure (before != (← shape))
      catch _ =>
        pure false
    if progressed then return
    s.restore
  throwError "ssprove_auto_step: no alternative made progress"

/-- `ssprove_auto_repeat` applies `ssprove_auto_step` to the main goal until the
step fails, no goal is left, or 64 rounds have run. A failing round leaves the
proof state unchanged. The tactic always succeeds. -/
elab "ssprove_auto_repeat" : tactic => do
  for _ in [0:64] do
    if (← getGoals).isEmpty then break
    let s ← saveState
    let ok ← try
        evalTactic (← `(tactic| ssprove_auto_step))
        pure true
      catch _ =>
        s.restore
        pure false
    unless ok do break

/-- `ssprove_auto_ec` is the EasyCrypt-style auto tactic.

It normalizes code, then applies `ssprove_auto_step` through
`ssprove_auto_repeat` until a step makes no progress (at most
64 rounds). Finally, it runs a closing tactic (`rfl`, `assumption`, a
postcondition projection, `simp_all`) on every remaining goal, and fails when
that tactic fails on one of them.

This tactic handles common patterns:
- Programs with deterministic tails followed by sampling
- Identical programs (reflexivity)
- Programs differing only in dead code
- Programs with matching conditionals

Example:
```
-- Prove two games equivalent when they sample and return the same thing
theorem game_equiv : rHoare eqPre
    (do let k ← SPComp.sample Bool; pure (xor k x))
    (do let k ← SPComp.sample Bool; pure (xor k x))
    eqPost := by
  ssprove_auto_ec
```
-/
macro "ssprove_auto_ec" : tactic => `(tactic| (
  -- First normalize code
  try ssprove_code_simpl
  -- Then apply auto steps while they make progress, under a round bound
  ssprove_auto_repeat
  -- Try to close remaining goals with lightweight tactics only
  all_goals first
    | rfl
    | apply rHoare_refl
    | assumption
    | (intro _ _ _ _ h; exact h)
    | (intro _ _ _ _ ⟨h, _⟩; exact h)
    | (simp_all; try apply rHoare_refl)
  -- Fail when a goal stays open
  done
))

/-- `ssprove_auto_ec!` first attempts to prove the goal by `rHoare_refl`
(identical programs), then falls back to `ssprove_auto_ec`. It closes the goal
or fails.
-/
macro "ssprove_auto_ec!" : tactic => `(tactic| (
  first
  -- Try reflexivity first (identical programs)
  | apply rHoare_refl
  -- Fallback to step-by-step
  | ssprove_auto_ec
))

end CatCrypt.Tactics

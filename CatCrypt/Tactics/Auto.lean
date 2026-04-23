/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Tactics.WP
import CatCrypt.Tactics.Sync
import CatCrypt.Tactics.ProofFrog
import CatCrypt.Tactics.Conditional

/-!
# EasyCrypt-Style Auto Tactic

This file provides an `auto`-style meta-tactic that chains together
wp, sync, conditional resolution, and goal closure, analogous to
EasyCrypt's `auto` tactic.

## Main tactics

* `ssprove_auto_ec` - EasyCrypt-style auto: wp + rnd + skip, repeat
* `ssprove_auto_ec!` - Aggressive version including sim-like behavior

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

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational CatCrypt.Core

/-- `ssprove_auto_step` performs one round of EasyCrypt-style automation.

It tries (in order):
1. WP step (consume deterministic tail)
2. Sync rule (coupling for matching operations)
3. Bind decomposition
4. Conditional resolution
5. Dead code elimination
6. Goal closure (rfl, assumption, trivial)
-/
macro "ssprove_auto_step" : tactic => `(tactic| (
  first
  -- 1. Try wp to consume deterministic tail
  | ssprove_wp_step
  -- 2. Try coupling for matching operations (EasyCrypt's rnd/skip)
  | ssprove_sync
  -- 3. Try conditional resolution
  | ssprove_rcondt
  | ssprove_rcondf
  -- 4. Try one-sided sampling
  | (apply rHoare_sample_l; intro _)
  | (apply rHoare_sample_r; intro _)
  -- 5. Try dead code elimination
  | ssprove_dead_code
  -- 6. Try closing the goal
  | assumption
))

/-- `ssprove_auto_ec` is the EasyCrypt-style auto tactic.

It normalizes code, then repeatedly applies auto steps until no more
progress can be made. Finally, it tries to close all remaining goals.

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
  -- Then repeatedly apply auto steps
  repeat ssprove_auto_step
  -- Try to close remaining goals with lightweight tactics only
  all_goals first
    | rfl
    | assumption
    | (intro _ _ _ _ h; exact h)
    | (intro _ _ _ _ ⟨h, _⟩; exact h)
    | simp_all
))

/-- `ssprove_auto_ec!` is a more aggressive version that also tries
reflexivity and full simplification upfront.

It first attempts to prove the goal by reflexivity (identical programs),
then falls back to step-by-step automation.
-/
macro "ssprove_auto_ec!" : tactic => `(tactic| (
  first
  -- Try reflexivity first (identical programs)
  | apply rHoare_refl
  -- Fallback to step-by-step
  | ssprove_auto_ec
))

end CatCrypt.Tactics

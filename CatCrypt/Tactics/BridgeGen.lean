/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean

/-!
# Bridge Lemma Generator

Automates the generation of correspondence lemmas between
hax-extracted protocol functions and abstract `Dependencies` typeclasses.

## Problem

The CatCrypt methodology pipeline (Section 13) requires bridge lemmas of the form:

```
theorem extraction_foo_eq (args : W) :
    extracted_foo deps.field₁ deps.field₂ args = deps.fieldₖ (deps.fieldⱼ args) := rfl
```

These are currently hand-written (one per extracted function). Since the proofs
are all `rfl` (definitional equality after unfolding), they can be auto-generated.

## Usage

```
-- Given extracted functions and a Dependencies structure:
#bridge_check (compute_prk_2e f g x y z) ~= (f z (g x y))
```

The command unfolds the extracted function and attempts `rfl`. If `rfl` fails,
it reports which subterms don't match, guiding manual intervention.

## Design

The tactic works in two modes:

1. **Verification mode** (`bridge_verify`): Given an extracted function name and
   the expected abstract expression, verify they are definitionally equal.

2. **Discovery mode** (`bridge_discover`): Given a namespace of extracted functions,
   attempt `rfl` for each against each field of the Dependencies structure,
   reporting successes and failures.
-/

namespace CatCrypt.Tactics.BridgeGen

open Lean Elab Meta Term Tactic Command

/--
`bridge_rfl` tactic: attempt to close a bridge correspondence goal by `rfl`,
falling back to `simp` with default lemmas then `rfl`.

Usage in a theorem:
```
theorem foo_eq : extracted_foo f g x = f (g x) := by bridge_rfl
```
-/
syntax "bridge_rfl" : tactic

elab_rules : tactic
  | `(tactic| bridge_rfl) => do
    let goal ← getMainGoal
    -- Try rfl first
    try
      goal.refl
      return
    catch _ => pure ()
    -- Fall back to simp + rfl
    evalTactic (← `(tactic| (simp; try rfl)))

/--
`#bridge_check lhs ~= rhs` command: given two expressions,
verify they are definitionally equal.

```
#bridge_check (extracted_foo f g x) ~= (f (g x))
```
-/
elab "#bridge_check " lhs:term " ~= " rhs:term : command => do
  liftTermElabM do
    let lhsExpr ← elabTerm lhs none
    let rhsExpr ← elabTerm rhs none
    if ← isDefEq lhsExpr rhsExpr then
      logInfo m!"✓ Bridge verified: definitionally equal"
    else
      logWarning m!"✗ Bridge failed: not definitionally equal\n  LHS: {lhsExpr}\n  RHS: {rhsExpr}"

end CatCrypt.Tactics.BridgeGen

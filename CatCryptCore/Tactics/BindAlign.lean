/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean

/-!
# `bind_align` — peel matching `SPComp.bind` layers from a goal equality

A recurring pattern in distributional-equivalence proofs is

```
  SPComp.bind X (fun a => SPComp.bind Y (fun b => ... pure(...))) =
  SPComp.bind X (fun a => SPComp.bind Y (fun b => ... pure(...)))
```

where the outer binds match exactly and only the innermost pure body
differs (or differs only at one binder level).  The mechanical proof
is `congr 1; funext a; congr 1; funext b; …` until the residual
obligation appears.

`bind_align` does this peeling automatically.  At each step it tries:

1. `rfl` — if both sides are already syntactically equal, done.
2. `congr 1` followed by `funext _` on the resulting function-equality
   subgoal — peels one bind layer.

The tactic stops as soon as a layer doesn't match (so it cannot use
`congr 1`); the residual subgoals are left for manual proof.

The peel is generic — it works for any `f x = g x` where `f`, `g` are
function applications with matching head, not just `SPComp.bind`.  In
practice the only callers are bind chains.
-/

namespace CatCrypt.Tactic

open Lean Elab Tactic

/-- Peel a single bind layer.

    Uses `congrArg` (not `congr 1`) so the head function must match
    syntactically — this means `SPComp.bind X` aligns with `SPComp.bind X`
    but NOT with `SPComp.bind Y` for a different `Y`.  When the heads
    differ the tactic fails (cleanly), so callers can wrap it in
    `repeat` without runaway behaviour. -/
syntax "bind_step" : tactic
macro_rules
  | `(tactic| bind_step) => `(tactic|
      first
      | rfl
      | (refine congrArg _ ?_; try funext _))

/-- Peel matching bind layers from both sides of a goal equality.
    Stops at the first mismatch; remaining subgoals are left for the
    caller to discharge.

    Typical usage:
    ```
    -- goal: bind X (fun a => bind Y (fun b => f a b)) =
    --       bind X (fun a => bind Y (fun b => g a b))
    bind_align
    -- residual goal: f a b = g a b
    ```
-/
syntax "bind_align" : tactic
macro_rules
  | `(tactic| bind_align) => `(tactic|
      repeat bind_step)

end CatCrypt.Tactic

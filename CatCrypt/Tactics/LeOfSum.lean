/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean

/-!
# `le_of_sum` Tactic

A recursive tactic for proving `x ≤ a + b + c + ...` goals that arise from
showing a single summand is bounded by a left-associated sum. Replaces
8-line `calc` chains of `le_add_self`/`le_self_add` with a single call.
-/

open Lean Elab Tactic in
private partial def leOfSumImpl : TacticM Unit := do
  -- Build unhygienic tactic syntax
  let leSelfAdd := mkIdent `le_self_add
  let leAddSelf := mkIdent `le_add_self
  let leTrans := mkIdent `le_trans
  -- Try closing with le_self_add (x ≤ x + b)
  try evalTactic (← `(tactic| exact $leSelfAdd)); return
  catch _ => pure ()
  -- Try closing with le_add_self (x ≤ a + x)
  try evalTactic (← `(tactic| exact $leAddSelf)); return
  catch _ => pure ()
  -- Peel off rightmost summand via le_trans _ le_self_add
  evalTactic (← `(tactic| apply $leTrans _ $leSelfAdd))
  leOfSumImpl

open Lean Elab Tactic in
/-- Prove `x ≤ a + b + c + ...` by recursively applying `le_self_add`
and `le_add_self`. Handles left-associated sums of any depth. -/
elab "le_of_sum" : tactic => leOfSumImpl

/-! ## `congr_funext` Tactic

Closes goals of the form `C a₁ ... (fun x => f x) = C a₁ ... (fun x => g x)`
arising in structural induction on free-monad-like types (SPTree, RawCode, etc.).

The typical pattern is:
```
simp only [defs, ih]; congr 1; funext _; exact ih _
```
This tactic replaces the `congr 1; funext _; exact ih _` part.
-/

/-- Close `congr 1; funext _; exact ih _`-shaped goals from inductive bind cases.
    Also handles `congr 1; exact ih` when no funext is needed (e.g., `set` cases). -/
syntax "congr_funext" : tactic
macro_rules
  | `(tactic| congr_funext) =>
    `(tactic| (congr 1; try (funext _; apply_assumption)))

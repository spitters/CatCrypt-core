/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.KatGuard

/-!
# A named known-answer theorem under the `#kat` budgets

`#kat_kernel t` proves `t` by `decide +kernel` under the `kat.ms` and `kat.heartbeats`
budgets, as an anonymous `example`. A closed check that a later theorem consumes — the
coverage of an emitted instruction list by an encoder fragment, the injectivity of a
register naming on a gathered block — needs a name. `kat_kernel_theorem` is that form:

```
/-- Every instruction of the body is in the tied fragment. -/
kat_kernel_theorem body_tied : body.all tiedInstr = true
```

elaborates `theorem body_tied : body.all tiedInstr = true := by decide +kernel` under the
same budgets, so the build fails at this line when the check exceeds them. Lower a budget
per check with `set_option kat.heartbeats N in`.

The wall-clock budget is measured synchronously. With `Elab.async` on, a theorem's body
and its kernel check run in a task after the command returns, so a wall-clock budget
around the command measures nothing; and the first synchronous command after a run of
asynchronous ones waits for their pending kernel checks, so a budget around it would
measure the neighbours. `runBudgetedSync` therefore disables `Elab.async` for the
check, and elaborates a trivial synchronous barrier outside the timer first, so the
timer sees the check alone.

## Main results

* `runBudgetedSync`: `KatGuard.runBudgeted` with the check elaborated synchronously
  behind a barrier.
* `kat_kernel_theorem`: the command.
-/

public section

meta section

open Lean Elab Command

namespace CatCrypt.Tactic.KatGuard

/-- Elaborate `cmd` synchronously under the `kat.heartbeats` budget and fail when its
own wall time exceeds `kat.ms`: a trivial synchronous command elaborated first absorbs
the wait for pending asynchronous kernel checks, so the timed region holds `cmd` alone. -/
def runBudgetedSync (cmd : Syntax) : CommandElabM Unit := do
  let opts ← getOptions
  let ms := kat.ms.get opts
  let hb := kat.heartbeats.get opts
  withScope (fun s => { s with opts := Elab.async.set s.opts false }) do
    elabCommand (← `(example : True := trivial))
  let t0 ← IO.monoMsNow
  withScope (fun s =>
      { s with opts := Elab.async.set (maxHeartbeats.set s.opts hb) false }) do
    elabCommand cmd
  let dt := (← IO.monoMsNow) - t0
  if dt > ms then
    throwError "known-answer check took {dt} ms, over its budget of {ms} ms"

/-- `kat_kernel_theorem name : t`: the theorem `name : t`, proved by `decide +kernel`
synchronously under the `kat.ms` and `kat.heartbeats` budgets. Declaration modifiers (a
docstring, `private`, attributes) apply to the theorem. -/
syntax (name := katKernelTheorem)
  declModifiers "kat_kernel_theorem " ident " : " term : command

@[command_elab katKernelTheorem]
def elabKatKernelTheorem : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers kat_kernel_theorem $id:ident : $t:term) =>
      runBudgetedSync (← `($mods:declModifiers theorem $id:ident : $t := by decide +kernel))
  | _ => throwUnsupportedSyntax

end CatCrypt.Tactic.KatGuard

end

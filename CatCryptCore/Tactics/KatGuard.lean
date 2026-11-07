/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# `#kat` — known-answer checks under a time and heartbeat budget

A known-answer check compares a computed value with an expected one on concrete data. It
belongs in a source file only if it is cheap, so every such check carries its budget and
is reported at its own line when the budget is exceeded.

* `#kat t` evaluates the Boolean or decidable term `t` with the compiled evaluator, as
  `#guard` does, and fails when `t` is false or when elaborating it exceeds the heartbeat
  budget; a check that takes longer than the millisecond budget is reported as below.
* `#kat_kernel t` states `t` and closes it by `decide +kernel` under the same heartbeat
  budget, which bounds the kernel's reduction as well as elaboration, and applies the same
  millisecond budget.

The budgets are the options `kat.ms` (default 200) and `kat.heartbeats` (default 20000,
in thousands of heartbeats), set per check with `set_option … in`, for instance
`set_option kat.ms 50 in #kat f 3 == 9`. The millisecond budget is multiplied by the
positive integer in the environment variable `CATCRYPT_KAT_MS_SCALE` (default 1; a value
that is not a positive integer is ignored), so that a slower machine scales every wall-clock
budget at once; the heartbeat budget is machine-independent and is not scaled.

The millisecond budget is measured, not enforced during evaluation: compiled code does
not poll for cancellation, so an evaluation that exceeds it runs to completion and is
reported afterwards. An overrun is an error when the environment variable
`CATCRYPT_KAT_STRICT` is `1`, as the development scripts and CI set it, and a warning
otherwise, so that a build on a slower or busier machine than the one the budgets were set
on still succeeds. A false check and a heartbeat overrun are errors in both cases. The
heartbeat budget is enforced during elaboration and kernel checking.

## Main definitions

* `#kat`, `#kat_kernel`: the two commands.
* `kat.ms`, `kat.heartbeats`: their budgets.
-/

public section

meta section

register_option kat.ms : Nat := {
  defValue := 200
  descr := "wall-clock budget of a `#kat` / `#kat_kernel` check, in milliseconds"
}

register_option kat.heartbeats : Nat := {
  defValue := 20000
  descr := "heartbeat budget of a `#kat` / `#kat_kernel` check, in thousands"
}

open Lean Elab Command

namespace CatCrypt.Tactic.KatGuard

/-- `#kat t`: evaluate the Boolean or decidable term `t` under the `kat.ms` and
`kat.heartbeats` budgets. -/
syntax (name := kat) "#kat " term : command

/-- `#kat_kernel t`: prove `t` by `decide +kernel` under the `kat.ms` and
`kat.heartbeats` budgets. -/
syntax (name := katKernel) "#kat_kernel " term : command

/-- The scale of the wall-clock budget: the positive integer in `CATCRYPT_KAT_MS_SCALE`,
and 1 when the variable is unset or not a positive integer. -/
def msScale : IO Nat := do
  match (← IO.getEnv "CATCRYPT_KAT_MS_SCALE").bind String.toNat? with
  | some k => return if k = 0 then 1 else k
  | none => return 1

/-- The wall-clock budget of a check: `kat.ms` times `msScale`. -/
def msBudget (opts : Options) : IO Nat := do
  return kat.ms.get opts * (← msScale)

/-- Whether a wall-clock overrun is an error: `CATCRYPT_KAT_STRICT` is `1`. -/
def strict : IO Bool := do
  return (← IO.getEnv "CATCRYPT_KAT_STRICT") == some "1"

/-- Run a command with `maxHeartbeats` set to the `kat.heartbeats` budget, and report when
it takes longer than the scaled `kat.ms` budget: an error under `strict`, a warning
otherwise. -/
def runBudgeted (cmd : Syntax) : CommandElabM Unit := do
  let opts ← getOptions
  let ms ← msBudget opts
  let hb := kat.heartbeats.get opts
  let t0 ← IO.monoMsNow
  withScope (fun s => { s with opts := maxHeartbeats.set s.opts hb }) do
    elabCommand cmd
  let dt := (← IO.monoMsNow) - t0
  if dt > ms then
    let msg := m!"known-answer check took {dt} ms, over its budget of {ms} ms"
    if ← strict then throwError msg else logWarning msg

@[command_elab kat]
def elabKat : CommandElab := fun stx => do
  match stx with
  | `(#kat $t:term) => runBudgeted (← `(#guard $t))
  | _ => throwUnsupportedSyntax

@[command_elab katKernel]
def elabKatKernel : CommandElab := fun stx => do
  match stx with
  | `(#kat_kernel $t:term) => runBudgeted (← `(example : $t := by decide +kernel))
  | _ => throwUnsupportedSyntax

end CatCrypt.Tactic.KatGuard

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Tactics.KatGuard

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

elaborates `theorem body_tied : body.all tiedInstr = true := by decide +kernel` through
`KatGuard.runBudgeted`, so the same budgets apply and the build fails at this line when
the check exceeds them. Lower a budget per check with `set_option kat.heartbeats N in`.

## Main results

* `kat_kernel_theorem`: the command.
-/

open Lean Elab Command

namespace CatCrypt.Tactic.KatGuard

/-- `kat_kernel_theorem name : t`: the theorem `name : t`, proved by `decide +kernel`
under the `kat.ms` and `kat.heartbeats` budgets. Declaration modifiers (a docstring,
`private`, attributes) apply to the theorem. -/
syntax (name := katKernelTheorem)
  declModifiers "kat_kernel_theorem " ident " : " term : command

@[command_elab katKernelTheorem]
def elabKatKernelTheorem : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers kat_kernel_theorem $id:ident : $t:term) =>
      runBudgeted (← `($mods:declModifiers theorem $id:ident : $t := by decide +kernel))
  | _ => throwUnsupportedSyntax

end CatCrypt.Tactic.KatGuard

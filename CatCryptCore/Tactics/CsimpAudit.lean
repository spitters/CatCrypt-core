/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public meta import Lean.Compiler.CSimpAttr
public meta import Lean.Util.CollectAxioms

/-!
# `#csimp_audit`: the axioms of `@[csimp]` theorems

A `@[csimp]` theorem `@f = @g` makes the code generator compile every later occurrence of `f`
as `g`. Lean does not check the axioms of such a theorem: one proved by `sorry` is registered,
and its replacement runs. The axioms of a computable caller of `f` do not include those of the
csimp theorem, since the replacement happens in the code generator, so `#print axioms` of the
caller does not show an unproved replacement.

`#csimp_audit` reads the csimp theorems from the state of Lean's csimp extension
(`Lean.Compiler.CSimp.ext`) and collects the axioms of each:

* `#csimp_audit` audits every csimp theorem of the environment;
* `#csimp_audit n₁ n₂ …` audits the csimp theorems whose name is `nᵢ` or lies in the namespace
  `nᵢ`.

An axiom outside `propext`, `Classical.choice`, `Quot.sound` is reported: `sorryAx` as an
error, any other axiom as a warning. A final information message gives the number of theorems
audited and the number reported.
-/

public section

namespace CatCrypt.Tactics.CsimpAudit

open Lean Elab Command

/-- The axioms a csimp theorem may depend on without a report. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The csimp theorems of `env` with the constants they replace, sorted by theorem name:
`(thm, from, to)` for each registered `@[csimp] theorem thm : @from = @to`. -/
meta def csimpEntries (env : Environment) : Array (Name × Name × Name) :=
  let s := Compiler.CSimp.ext.getState env
  let fromMap : Std.HashMap Name (Name × Name) :=
    s.map.fold (fun acc _ e => acc.insert e.thmName (e.fromDeclName, e.toDeclName)) {}
  let thms : Array Name := s.thmNames.fold (fun acc n => acc.push n) #[]
  let rows := thms.map fun n => (n, (fromMap.get? n).getD (.anonymous, .anonymous))
  rows.qsort (fun a b => Name.lt a.1 b.1)

/-- Whether `thm` is selected by the name list `sel`: the list is empty, or `thm` is one of its
names or lies in the namespace of one of them. -/
meta def selected (sel : Array Name) (thm : Name) : Bool :=
  sel.isEmpty || sel.any (fun p => p == thm || p.isPrefixOf thm)

/-- The axioms of `thm` outside `standardAxioms`. -/
meta def nonstandardAxioms (thm : Name) : CommandElabM (Array Name) := do
  let axs ← liftCoreM (collectAxioms thm)
  return axs.filter (fun a => !standardAxioms.contains a)

/-- Audits the csimp theorems selected by `sel` and reports each one with an axiom outside
`standardAxioms` (an error for `sorryAx`, a warning otherwise); returns the number audited and
the number reported. -/
meta def runCsimpAudit (sel : Array Name) : CommandElabM (Nat × Nat) := do
  let rows := (csimpEntries (← getEnv)).filter (fun r => selected sel r.1)
  let mut flagged := 0
  for (thm, src, tgt) in rows do
    let bad ← nonstandardAxioms thm
    if bad.isEmpty then continue
    flagged := flagged + 1
    let names (l : List Name) : String := "[" ++ ", ".intercalate (l.map toString) ++ "]"
    let head := m!"csimp theorem `{thm}` (`{src}` compiled as `{tgt}`) depends on {names bad.toList}"
    if bad.contains ``sorryAx then
      logError m!"{head}; its replacement runs in compiled code without a proof"
    else
      logWarning m!"{head}, outside {names standardAxioms}"
  return (rows.size, flagged)

/-- `#csimp_audit` reports every `@[csimp]` theorem of the environment whose axioms are not
among `propext`, `Classical.choice`, `Quot.sound`: an error for `sorryAx`, a warning for any
other axiom. `#csimp_audit n₁ n₂ …` restricts the audit to the theorems named `nᵢ` or in the
namespace `nᵢ`; a name that selects no csimp theorem is an error. -/
syntax (name := csimpAuditCmd) "#csimp_audit" (ppSpace ident)* : command

@[command_elab csimpAuditCmd, inherit_doc csimpAuditCmd]
meta def elabCsimpAudit : CommandElab
  | `(#csimp_audit $ids*) => do
    let sel := ids.map (·.getId)
    let env ← getEnv
    for id in ids do
      if !(csimpEntries env).any (fun r => selected #[id.getId] r.1) then
        throwErrorAt id m!"no csimp theorem is named `{id.getId}` or lies in that namespace"
    let (n, k) ← runCsimpAudit sel
    logInfo m!"csimp audit: {n} theorems, {k} reported"
  | _ => throwUnsupportedSyntax

end CatCrypt.Tactics.CsimpAudit

end

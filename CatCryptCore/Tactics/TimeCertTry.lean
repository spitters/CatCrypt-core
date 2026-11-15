/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# `time_cert_try` — a time certificate or a recorded exception

`time_cert_try c` elaborates the command `c`, typically one of `derive_timed X`,
`derive_reduction X`, `derive_time_bound X`, `derive_hybrid_time X` or a `theorem` stating a
time bound.

* When `c` logs no error, `time_cert_try c` has the effect of `c`: its declarations and its
  messages.
* When `c` logs an error or throws, the environment and the message log are restored to their
  state before `c`, so that no declaration of `c` is added, and one warning is logged whose
  text is `time-cert exception:` followed by three tab-separated fields: the declaration
  name `c` mentions, the keyword of `c`, and the first line of the first error of `c`.

The warning has a fixed form so that a build log can be scanned for it; the script
`scripts/time-cert-exceptions.sh` of the development repository collects these warnings into
a table of time certificates to revisit. `c` is elaborated with `Elab.async` off, so that its
errors are logged before `time_cert_try` inspects the message log.

The declaration name is, in order: the first identifier that is an argument of `c` itself
(`derive_timed (suffix := s) X` names `X`), the identifier of the first `declId` of `c` (the
name of a `theorem`), and `?` when `c` has neither (an `example`).

## Main definitions

* `time_cert_try`: the command.
* `CatCrypt.Tactics.TimeCertTry.exceptionTag`: the tag that starts the warning.
-/

public section

set_option autoImplicit false

meta section

open Lean Elab Command

namespace CatCrypt.Tactics.TimeCertTry

/-- `time_cert_try c`: elaborate the command `c`; when it fails, discard its effects and log
a `time-cert exception:` warning naming the declaration, the command and the first error. -/
syntax (name := timeCertTry) "time_cert_try " command : command

/-- The tag that starts the warning of a failed command. -/
def exceptionTag : String := "time-cert exception:"

/-- The first identifier in pre-order of a syntax tree. -/
partial def firstIdent? : Syntax → Option Name
  | .ident _ _ n _ => some n
  | .node _ _ args => args.findSome? firstIdent?
  | _ => none

/-- The identifier of the first `declId` node in pre-order of a syntax tree. -/
partial def firstDeclId? : Syntax → Option Name
  | stx@(.node _ k args) =>
    if k == ``Lean.Parser.Command.declId then firstIdent? stx
    else args.findSome? firstDeclId?
  | _ => none

/-- The first atom in pre-order of a syntax tree that is not the start of a doc comment or
an attribute list, trimmed. -/
partial def firstKeyword? : Syntax → Option String
  | .atom _ v => some v.trimAscii.toString
  | .node _ k args =>
    if k == ``Lean.Parser.Command.declModifiers then none
    else args.findSome? firstKeyword?
  | _ => none

/-- The declaration name a command mentions: a direct identifier argument, else the name of
its first `declId`, else `?`. -/
def declNameOf (cmd : Syntax) : String :=
  let direct := cmd.getArgs.findSome? fun a => if a.isIdent then some a.getId else none
  match direct <|> firstDeclId? cmd with
  | some n => n.toString
  | none => "?"

/-- The keyword of a command: its first atom outside declaration modifiers, or `?`. -/
def keywordOf (cmd : Syntax) : String :=
  (firstKeyword? cmd).getD "?"

/-- The first line of a string. -/
def firstLine (s : String) : String :=
  ((s.splitOn "\n").headD "").trimAscii.toString

/-- The text of the warning of a failed command: the tag, then the declaration name, the
keyword and the first line of the first error, separated by tabs. -/
def exceptionText (cmd : Syntax) (err : String) : String :=
  s!"{exceptionTag} {declNameOf cmd}\t{keywordOf cmd}\t{firstLine err}"

@[command_elab timeCertTry, inherit_doc timeCertTry]
def elabTimeCertTry : CommandElab := fun stx => do
  let cmd := stx[1]
  let env0 ← getEnv
  let msgs0 := (← get).messages
  modify fun s => { s with messages := {} }
  let thrown : Option String ← try
      withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
        elabCommand cmd
      pure none
    catch ex => pure (some (← ex.toMessageData.toString))
  let msgs := (← get).messages
  let firstErr? ← match msgs.toList.find? (·.severity == .error) with
    | some m => some <$> m.data.toString
    | none => pure none
  match firstErr? <|> thrown with
  | none =>
    modify fun s => { s with messages := msgs0 ++ msgs }
  | some err =>
    setEnv env0
    modify fun s => { s with messages := msgs0 }
    logWarning (exceptionText cmd err)

end CatCrypt.Tactics.TimeCertTry

end

end

/-! ## Checks -/

#guard_msgs in
time_cert_try theorem timeCertTry_ok : 1 + 1 = 2 := rfl

/-- info: timeCertTry_ok : 1 + 1 = 2 -/
#guard_msgs in
#check timeCertTry_ok

/-- warning: time-cert exception: timeCertTry_bad	theorem	Type mismatch -/
#guard_msgs in
time_cert_try theorem timeCertTry_bad : 1 + 1 = 3 := rfl

/-- error: Unknown identifier `timeCertTry_bad` -/
#guard_msgs in
#check timeCertTry_bad

/--
warning: time-cert exception: timeCertTry_none	#print	Unknown constant `timeCertTry_none`
-/
#guard_msgs in
time_cert_try #print timeCertTry_none

/-- warning: time-cert exception: ?	example	omega could not prove the goal: -/
#guard_msgs in
time_cert_try example : 1 + 1 = 3 := by omega

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Lean
public meta import CatCryptCore.Tactics.RepairAction
public import CatCryptCore.Tactics.AutoDispatch
public meta import CatCryptCore.Tactics.AutoDispatch

/-!
# Leaves for the grind repair code action

Seven tactic leaves on which the code action of `CatCryptCore.Tactics.RepairAction` is
requested at the leaf's line. Each declaration is wrapped in `#guard_msgs (drop all)`, so
that the failing tactics and the open goals elaborate without diagnostics.

| leaf | goal | arm expected to close |
|---|---|---|
| `skip` | `a < b + 1` from `a ≤ b` | `grind` |
| `exact rfl` | `(xs ++ []).length = xs.length` | `grind` |
| `simp only [triple]` | `triple n = 3 * n` | `grind [triple]` |
| `skip` | `a * b = a + b` (false) | none |
| `simp [sumTo]` | `2 * sumTo n = n * (n + 1)` (needs induction) | `try?` |
| `exact hp` | `p ∧ q` | `grind` |
| `skip` inside `have` | `a + 1 < c` | `grind` |

The probes of this file, each over fresh definitions:
* `repair_dispatch_probe` runs `RepairAction.repairGoal` (every arm, in order) on the goal,
  requires the closing arm's text to start with the given prefix and closes the goal with
  that text; or requires that no arm closes, within the given time. With a leaf, given in
  parentheses, the arm `grind [args]` takes its arguments from that leaf.
* `repair_suggestion_probe` runs one suggestion arm (`RepairAction.runSuggestionArm`) with a
  given tactic text, and can require its failure to be final or not.
* `repair_final_probe` runs `RepairAction.repairGoal` and requires the finality of each arm
  (`A final`, `A open`), and optionally a reason and the title.
* `repair_range_probe` elaborates a declaration and checks the edit range
  (`RepairAction.editSpan`) at one of its leaves.
* `repair_action_probe` elaborates a declaration, lists the code actions of the provider
  (`RepairAction.actionsAt`) at the first occurrence of a text in it, and checks the title of
  one action and its text edit, or that it has the field `edit` and no text edit.
* `repair_resolve_probe` lists the code actions at a range, or at a cursor, resolves them as
  lean-lsp-mcp and VS Code do (only an action without the field `edit`) by the steps of Lean's
  `handleCodeActionResolve`, and counts the arms run (`RepairAction.armRuns`).

The file sets `repairAction.suggestionIndex` to false, so that the suggestion arms use the
theorems of this file and no index of the imported theorems is built, except in its last
test, the only one that builds the index (about 10 s of wall time and 81 s of CPU time).

The probes and their outcomes:
* dispatch: `IsPure flipNeg` by `(unfold flipNeg; simp only [...]; aesop ...)`; `IsPure` of
  a `do` block by `(simp only [...]; aesop ...)`; `rHoare eqPre (bind (pure a) negStep)
  (negStep a) eqPost` by `aesop ...`; a sum of two `AdvantageA` hops `≤ ε₁ + ε₂` by
  `sum_atoms_le`; `gameL = gameR` (samples swapped) by `(unfold gameL; …; bind_swap_nf)`.
* dispatch: `dbl (a + b + c) = dbl a + dbl b + dbl c` (needs `dbl_add`) by
  `grind only [dbl_add, …]`, the arm `grind? +suggestions`; `2 * sumTo n = n * (n + 1)` by
  `fun_induction sumTo <;> grind`, the arm `try?`.
* dispatch with a leaf: `p` from `h : ∀ n, n * n = 49 → p` at the leaf
  `grind [h seven rfl, seven]` by `grind [h seven rfl]`, and at the leaf
  `simp [h seven rfl, ← seven_def, seven, *, -Nat.add_zero]` by
  `grind [h seven rfl, seven_def]` (`seven` is reducible); `triple n = 3 * n` at the leaf
  `simp only [triple, seven]` by `grind [triple]`, with the title `[head Eq]`.
* suggestion: `grind? +suggestions` on `2 * sumTo n = n * (n + 1)` suggests a `grind` script
  that ends in an open case, which does not close.
* range: `funext n; simp [shift]` at `funext n`: the line; `intro s` then `simp_all [shift]`
  on the next line: both lines; after `constructor`, `funext n` and `simp [shift]` then
  `exact hp`: the first two, and `simp [shift]` alone at `simp [shift]`;
  `(intro s); simp [shift]` at `intro s`: the line; `skip` inside `have … := by`: `skip`;
  `intro s` inside `·`: the bullet's body.
* range, none: `skip` then `all_goals assumption`; `skip`, `swap`, `exact hq`, `exact hp`;
  `intro s`, a failing `simp only []`, then `rfl`.
* final, on `quad n = 4 * n` (`quad` not unfolded by `grind`): every arm at a wall-clock cap
  of 0 ms, none final and no element `final` in the title `[head Eq]`; `grind` at a heartbeat
  cap of 1 (thousand), not final; `grind` failing within its caps, final, and
  `grind? +suggestions` failing with the theorems of the file, not final (`index not
  built`), with the title `[head Eq, final: grind]`.
* final, the dispatcher: on `2 * sumTo n = n * (n + 1)` (shape `other`, which has an arm
  `grind +suggestions`) not final, since the dispatcher consulted the library suggestions;
  on `Holds n` (the shape `repair holds` of this file, whose one arm is `omega`, and no
  premise) final, with the title `[head …Holds, shape repair holds, final: grind;
  catcrypt_auto?]`; on the same goal with `catcrypt_auto.totalMillis` 1, not final, since a
  budget ran out.
* resolution, on `quad n = 4 * n` at the failing leaf `skip`: four arms in all, both when
  listed with a range (the failing action carries the empty edit and is not resolved) and at
  a cursor (no arm when listed, four when resolved); no unsolved-goals action at `skip`.
* unsolved goals: `refine ⟨?_, trivial⟩` leaving `a < a + 1`, closed by `grind` on a new line;
  `constructor` leaving `a < a + 1` and `triple n = 3 * n`, closed by `grind` and
  `grind [triple]` in two bullets (title `[unsolved 2, head LT.lt]`); `intro n` leaving
  `quad n = 4 * n`, closed by no arm (title `[unsolved 1, head Eq, final: grind]`, no text
  edit); a request at the `by` token of a block ending in `intro h`; `refine ⟨?_, ?_⟩` in a
  nested bullet, two bullets at the column of that bullet's block.
* caps: `False` from `∀ n, 2 * sumTo n = n * n`: no arm, within 7000 ms in all, with the
  title `[head False, shape other, final: grind]`.
* index, last in the file: `grind? +suggestions` on `Holds n` waits for the build of the
  index, runs with it, suggests a script containing `sorry`, and fails without reaching a
  cap: final.
-/

set_option autoImplicit false

set_option repairAction.suggestionIndex false

namespace CatCryptCore.RepairActionTest

/-- Three times `n`, as an opaque definition. -/
def triple (n : Nat) : Nat := n + n + n

/-- The sum `0 + 1 + ⋯ + n`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

#guard_msgs (drop all) in
example (a b : Nat) (h : a ≤ b) : a < b + 1 := by
  skip

#guard_msgs (drop all) in
example (xs : List Nat) : (xs ++ []).length = xs.length := by
  exact rfl

#guard_msgs (drop all) in
example (n : Nat) : triple n = 3 * n := by
  simp only [triple]

#guard_msgs (drop all) in
example (a b : Nat) : a * b = a + b := by
  skip

#guard_msgs (drop all) in
example (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  simp [sumTo]

#guard_msgs (drop all) in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact hp

#guard_msgs (drop all) in
example (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := by
  have h : a + 1 < c := by
    skip
  omega

/-! ## The probes -/

public meta section

open Lean Elab Meta Command CatCryptCore.RepairAction

/-- One entry per arm: its text, time and outcome. -/
def report (rs : Array ArmResult) : String :=
  "; ".intercalate (rs.map fun r =>
    s!"{r.text}: {r.ms} ms, {if r.closed then "closed" else r.msg}").toList

/-- `repairGoal` on the main goal with the leaves `leaves`, the arms reported as information
with their total time. When `title?` is given, the title of the code action for these arms
at line 1 (`mkAction`) must start with it. -/
def probeArms (stx : Syntax) (leaves : Array Syntax) (title? : Option String) :
    Tactic.TacticM (Array ArmResult × Nat) := do
  let g ← Tactic.getMainGoal
  let some r := stx.getRange? | throwError "repair_dispatch_probe: no source range"
  let rs ← g.withContext (repairGoal g leaves r (← Term.getDeclName?))
  let total := rs.foldl (· + ·.ms) 0
  logInfo m!"repair arms ({total} ms): {report rs}"
  if let some t := title? then
    let rep : LeafReport := { head := ← goalHead g, span := .ok { range := r, tactics := #[] },
                              arms := rs }
    let a := mkAction { uri := "file:///probe.lean", version? := none } (← getFileMap) 1 rep
    unless a.title.startsWith t do
      throwError "repair_dispatch_probe: the title is {a.title}, expected {t}"
  return (rs, total)

/-- `repair_dispatch_probe closes "p"` requires that `repairGoal` closes the main goal by an
arm whose text starts with `p`, then closes the goal with that text. It reports the arms
with their times. `repair_dispatch_probe closes "p" (tac)` does the same with `tac` as the
leaf, from which the arm `grind [args]` takes its arguments; `tac` is not run. With
`titled "t"`, the title of the code action must start with `t`. -/
syntax (name := probeCloses)
  "repair_dispatch_probe" " closes " str (" (" tactic ")")? (" titled " str)? : tactic

/-- `repair_dispatch_probe fails_within n` requires that no arm of `repairGoal` closes the
main goal and that the arms take under `n` milliseconds in all; the goal is unchanged. It
reports the arms with their times. With `titled "t"`, the title of the code action must
start with `t`. -/
syntax (name := probeFails) "repair_dispatch_probe" " fails_within " num (" titled " str)? :
  tactic

/-- Runs the closing text `text` of an arm on the main goal. -/
def runClosing (text : String) : Tactic.TacticM Unit := do
  let .ok tac := Parser.runParserCategory (← getEnv) `tactic text
    | throwError "repair probe: the closing text does not parse: {text}"
  Tactic.evalTactic tac

@[tactic probeCloses, inherit_doc probeCloses]
def evalProbeCloses : Tactic.Tactic := fun stx => do
  let p := stx[2].isStrLit?.getD ""
  let leaves := if stx[3].getNumArgs == 0 then #[] else #[stx[3][1]]
  let (rs, _) ← probeArms stx leaves (stx[4][1].isStrLit?)
  let some c := rs.find? (·.closed)
    | throwError "repair_dispatch_probe: no arm closes the goal: {report rs}"
  unless c.text.startsWith p do
    throwError "repair_dispatch_probe: the closing arm is {c.text}, expected {p}"
  runClosing c.text

@[tactic probeFails, inherit_doc probeFails]
def evalProbeFails : Tactic.Tactic := fun stx => do
  let n := stx[2].isNatLit?.getD 0
  let (rs, total) ← probeArms stx #[] (stx[3][1].isStrLit?)
  if let some c := rs.find? (·.closed) then
    throwError "repair_dispatch_probe: the arm {c.text} closes the goal"
  unless total < n do
    throwError "repair_dispatch_probe: the arms take {total} ms, not under {n} ms"

/-- The finality of each arm, `A final` or `A open` (`A closed` for a closing arm), joined by
`; `, and the reasons. -/
def finalities (rs : Array ArmResult) : String × String :=
  ("; ".intercalate (rs.map fun r =>
      s!"{r.arm} {if r.closed then "closed" else if r.final then "final" else "open"}").toList,
    "; ".intercalate (rs.map fun r => s!"{r.arm}: {r.finality}").toList)

/-- `repair_final_probe "A final; B open; …"` runs `repairGoal` on the main goal and requires
that the finality of its arms (`finalities`) is the given text; the goal is unchanged. It
reports the arms, then their finality with the reasons. With `because "m"` the reasons must
contain `m`; with `titled "t"` the title of the code action must start with `t`. -/
syntax (name := finalProbe)
  "repair_final_probe " str (" because " str)? (" titled " str)? : tactic

@[tactic finalProbe, inherit_doc finalProbe]
def evalFinalProbe : Tactic.Tactic := fun stx => do
  let expected := stx[1].isStrLit?.getD ""
  let (rs, _) ← probeArms stx #[] (stx[3][1].isStrLit?)
  let (got, why) := finalities rs
  logInfo m!"finality: {why}"
  unless got == expected do
    throwError "repair_final_probe: the finality is {got}, expected {expected}"
  if let some m := stx[2][1].isStrLit? then
    unless (why.splitOn m).length > 1 do
      throwError "repair_final_probe: the reasons are {why}, expected {m} among them"

/-- `repair_suggestion_probe "t" fails "m"` runs the suggestion arm `t` (`runSuggestionArm`,
under the cap `repairAction.tryMillis`) on the main goal and requires that it does not close
the goal, with a failure reason containing `m`; the goal is unchanged. It reports the arm,
its finality and the time it waited for the library-suggestion index. With `final` or
`open` after it, the failure must be final, or not final. -/
syntax (name := suggestionProbe)
  "repair_suggestion_probe " str " fails " str (ppSpace (&"final" <|> &"open"))? :
    tactic

@[tactic suggestionProbe, inherit_doc suggestionProbe]
def evalSuggestionProbe : Tactic.Tactic := fun stx => do
  let text := stx[1].isStrLit?.getD ""
  let m := stx[3].isStrLit?.getD ""
  let g ← Tactic.getMainGoal
  let some r := stx.getRange? | throwError "repair_suggestion_probe: no source range"
  let opts ← getOptions
  let res ← g.withContext <| runSuggestionArm g text r
    (opts.get `repairAction.maxHeartbeats (100000 : Nat))
    (opts.get `repairAction.tryMillis (2000 : Nat)) (← Term.getDeclName?)
  logInfo m!"repair arm: {report #[res]}; {res.finality}; waited {res.waitMs} ms"
  if res.closed then throwError "repair_suggestion_probe: the arm closes the goal"
  unless (res.msg.splitOn m).length > 1 do
    throwError "repair_suggestion_probe: the failure reason is {res.msg}, expected {m}"
  if stx[4].getNumArgs > 0 then
    let wantFinal := (stx[4].find? (·.isAtom)).any (·.getAtomVal == "final")
    unless res.final == wantFinal do
      throwError "repair_suggestion_probe: the failure is {if res.final then "" else "not "}\
        final ({res.finality})"

/-- `repair_range_probe "t" ↦ "s" in cmd` elaborates `cmd`, takes the leaf of the code action
whose source text is the first occurrence of `t` in `cmd`, and requires that its edit range
(`editSpan`) holds the text `s`, runs of white space compared as single spaces. With
`↦ none` it requires that there is no edit range, and reports why. -/
syntax (name := rangeProbe)
  "repair_range_probe " str " ↦ " (str <|> &"none") " in " command : command

@[command_elab rangeProbe, inherit_doc rangeProbe]
def elabRangeProbe : CommandElab := fun stx => do
  let leafText := stx[1].isStrLit?.getD ""
  let expected := stx[3].isStrLit?
  let cmd := stx[5]
  elabCommand cmd
  let trees := (← getInfoTrees)
  let src := (← getFileMap).source
  let some r := cmd.getRange? | throwError "repair_range_probe: no source range"
  let body := String.Pos.Raw.extract src r.start r.stop
  let parts := body.splitOn leafText
  unless parts.length > 1 do throwError "repair_range_probe: {leafText} is not in the command"
  let lo : String.Pos.Raw := ⟨r.start.byteIdx + (parts.headD "").utf8ByteSize⟩
  let hi : String.Pos.Raw := ⟨lo.byteIdx + leafText.utf8ByteSize⟩
  let leaves := trees.foldl (fun acc t => acc ++ minimalLeaves (collectLeaves t lo hi)) #[]
  let some l := leaves.find? fun l => l.range.start == lo && l.range.stop == hi
    | throwError "repair_range_probe: no leaf {leafText}"
  let some g := l.info.goalsBefore.head? | throwError "repair_range_probe: the leaf has no goal"
  let ss := trees.foldl (fun acc t => acc ++ steps t) #[]
  match editSpan ss l.range g, expected with
  | .ok sp, some e =>
    let got := String.Pos.Raw.extract src sp.range.start sp.range.stop
    unless squash got == squash e do
      throwError "repair_range_probe: the edit range holds {got}, expected {e}"
  | .ok sp, none =>
    throwError "repair_range_probe: the edit range holds \
      {String.Pos.Raw.extract src sp.range.start sp.range.stop}, expected none"
  | .error why, some e => throwError "repair_range_probe: no edit range ({why}), expected {e}"
  | .error why, none => logInfo m!"no edit range: {why}"

/-- `repair_layout_probe c "t" ↦ "s"` requires that `layoutAt` lays out the tactic text `t`
for the column `c` as `s`. -/
syntax (name := layoutProbe) "repair_layout_probe " num ppSpace str " ↦ " str : command

@[command_elab layoutProbe, inherit_doc layoutProbe]
def elabLayoutProbe : CommandElab := fun stx => do
  let col := stx[1].isNatLit?.getD 0
  let text := stx[2].isStrLit?.getD ""
  let expected := stx[4].isStrLit?.getD ""
  let got ← liftTermElabM (layoutAt text col)
  unless got == expected do
    throwError "repair_layout_probe: the layout is{indentD got}\nexpected{indentD expected}"

/-- The document of the actions of the probes. -/
def probeDoc : Lsp.VersionedTextDocumentIdentifier :=
  { uri := "file:///probe.lean", version? := none }

/-- Elaborates `cmd`, dropping its messages, and returns its info tree, the line of its start
and the source range of the first occurrence of `sel` in it. -/
def elabForActions (cmd : Syntax) (sel : String) :
    CommandElabM (InfoTree × Nat × Syntax.Range) := do
  let msgs := (← get).messages
  let n := (← getInfoTrees).size
  elabCommand cmd
  modify fun s => { s with messages := msgs }
  let some t := (← getInfoTrees).toArray[n]? | throwError "repair probe: no info tree"
  let text ← getFileMap
  let some r := cmd.getRange? | throwError "repair probe: no source range"
  let body := String.Pos.Raw.extract text.source r.start r.stop
  let parts := body.splitOn sel
  unless parts.length > 1 do throwError "repair probe: {sel} is not in the command"
  let lo : String.Pos.Raw := ⟨r.start.byteIdx + (parts.headD "").utf8ByteSize⟩
  return (t, (text.toPosition r.start).line, ⟨lo, ⟨lo.byteIdx + sel.utf8ByteSize⟩⟩)

/-- The line `N` of a title `Repair line N…` and the rest of the title. -/
def titleLine (title : String) : Option (Nat × String) := do
  unless title.startsWith "Repair line " do none
  let rest := (title.drop 12).toString
  let digits := (rest.takeWhile Char.isDigit).toString
  return (← digits.toNat?, (rest.drop digits.length).toString)

/-- `title` with the line `N` of `Repair line N` written `+k`, where `k = N - base`. -/
def relativeTitle (title : String) (base : Nat) : String :=
  match titleLine title with
  | some (n, rest) => s!"Repair line +{n - base}{rest}"
  | none => title

/-- The text edits of the action `a`, read from its JSON as lean-lsp-mcp reads them (the edits
of each element of `documentChanges`); `none` when the JSON has no field `edit`. -/
def jsonEdits (a : Lsp.CodeAction) : Option (Array Lsp.TextEdit) := do
  let e ← ((toJson a).getObjVal? "edit").toOption
  let dcs := ((e.getObjVal? "documentChanges").toOption.bind (·.getArr?.toOption)).getD #[]
  return dcs.flatMap fun dc =>
    (((dc.getObjVal? "edits").toOption.bind (·.getArr?.toOption)).getD #[]).filterMap
      fun te => (fromJson? te).toOption

/-- `repair_action_probe "s" titled "t" ↦ "e" in cmd` elaborates `cmd`, dropping its messages,
lists the code actions of the provider (`actionsAt`, the arms run at once) for the range of
the first occurrence of `s` in `cmd`, and requires an action whose title, with its line
written `+k` for the `k`-th line after the first line of `cmd`, starts with `t`. With `↦ "e"`
that action has one text edit, which starts on the line of its title and has the text `e`;
with `↦ none` its JSON has the field `edit` and it has no text edit. -/
syntax (name := actionProbe)
  "repair_action_probe " str " titled " str " ↦ " (str <|> &"none") " in " command : command

@[command_elab actionProbe, inherit_doc actionProbe]
def elabActionProbe : CommandElab := fun stx => do
  let sel := stx[1].isStrLit?.getD ""
  let expected := stx[3].isStrLit?.getD ""
  let edit? := stx[5].isStrLit?
  let (t, base, r) ← elabForActions stx[7] sel
  let text ← getFileMap
  let actions ← actionsAt probeDoc text t r.start r.stop true
  let titles := actions.map (relativeTitle ·.eager.title base)
  let some (a, title) := (actions.zip titles).find? (·.2.startsWith expected)
    | throwError "repair_action_probe: no title starts with {expected}; the titles are\
        {indentD (MessageData.joinSep (titles.map toMessageData).toList "\n")}"
  let a := a.eager
  logInfo m!"{title}"
  match jsonEdits a, edit? with
  | none, _ => throwError "repair_action_probe: the action has no field edit"
  | some es, none =>
    unless es.isEmpty do throwError "repair_action_probe: the action has {es.size} text edits"
  | some es, some e =>
    let #[te] := es | throwError "repair_action_probe: the action has {es.size} text edits"
    unless (titleLine a.title).any (·.1 == te.range.start.line + 1) do
      throwError "repair_action_probe: the edit starts on line {te.range.start.line + 1}, \
        not on the line of the title"
    unless te.newText == e do
      throwError "repair_action_probe: the edit text is{indentD te.newText}\nexpected{indentD e}"

/-- `repair_resolve_probe "s" runs n in cmd` elaborates `cmd` as `repair_action_probe` does,
lists the code actions of the provider for the range of the first occurrence of `s` (the
empty range at its start with `cursor`), then resolves each action as lean-lsp-mcp and VS Code
do, only when its JSON has no field `edit`, and as `handleCodeActionResolve` does: the
provider runs again on the same range and the lazy part of the action at the same index, if
any, gives the result. Requires that listing and resolution run `n` arms in all (`armRuns`),
and reports the arms run by each and the titles of the resolved actions. -/
syntax (name := resolveProbe)
  "repair_resolve_probe " str (ppSpace &"cursor")? " runs " num " in " command : command

@[command_elab resolveProbe, inherit_doc resolveProbe]
def elabResolveProbe : CommandElab := fun stx => do
  let sel := stx[1].isStrLit?.getD ""
  let cursor := stx[2].getNumArgs > 0
  let n := stx[4].isNatLit?.getD 0
  let (t, base, r) ← elabForActions stx[6] sel
  let text ← getFileMap
  let list := actionsAt probeDoc text t r.start (if cursor then r.start else r.stop) (!cursor)
  let runs0 ← armRuns.get
  let listed ← list
  let runs1 ← armRuns.get
  let mut resolved : Array Lsp.CodeAction := #[]
  for h : i in [0:listed.size] do
    let a := listed[i].eager
    if (jsonEdits a).isSome then
      resolved := resolved.push a
      continue
    match (← list)[i]?.bind (·.lazy?) with
    | some lazy => resolved := resolved.push (← lazy)
    | none => resolved := resolved.push a
  let runs2 ← armRuns.get
  let titles := resolved.map (relativeTitle ·.title base)
  logInfo m!"listing: {runs1 - runs0} arms; resolution: {runs2 - runs1} arms; titles:\
    {indentD (MessageData.joinSep (titles.map toMessageData).toList "\n")}"
  unless runs2 - runs0 == n do
    throwError "repair_resolve_probe: {runs2 - runs0} arms ran, expected {n}"

end

/-! ## The layout of the edit text -/

-- The text that `catcrypt_auto?` suggests at the column of a line's first tactic, placed after
-- `intro s; `: on one line.
repair_layout_probe 11 "(unfold
    shift;
  simp_all)" ↦ "(unfold shift; simp_all)"

-- A bullet script does not go on one line: it is pretty-printed for the column.
repair_layout_probe 11 "·
    fun_induction sumTo
    · grind
    · grind only" ↦ "· fun_induction sumTo
             · grind
             · grind only"

/-! ## The suggestion arms -/

/-- Twice `n`, as a definition that `grind` does not unfold. -/
def dbl (n : Nat) : Nat := 2 * n

/-- `dbl` is additive. -/
theorem dbl_add (a b : Nat) : dbl (a + b) = dbl a + dbl b := by
  simp only [dbl]
  omega

-- `grind` fails without a fact about `dbl`; `grind? +suggestions` finds one among the
-- declarations of the file, `dbl_add` or the equation lemma `dbl.eq_1` (after the tests
-- moved to the CatCryptCoreTest root, core ca93ef6, the selector returned the latter). The
-- cap of 0 ms stops the arm `catcrypt_auto?` at once.
set_option repairAction.suggestionIndex false in
set_option repairAction.dispatchMillis 0 in
#guard_msgs (drop info) in
example (a b c : Nat) : dbl (a + b + c) = dbl a + dbl b + dbl c := by
  repair_dispatch_probe closes "grind only [dbl"

-- Induction on the recursion of `sumTo`: the arm `try?`.
set_option repairAction.dispatchMillis 0 in
#guard_msgs (drop info) in
example (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  repair_dispatch_probe closes "fun_induction sumTo <;> grind"

-- `grind? +suggestions` closes the goal by `grind`, but suggests a `grind` script ending in
-- an open case, which does not close.
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  repair_suggestion_probe "grind? +suggestions" fails "sorry"
  fun_induction sumTo <;> grind

/-! ## The arguments of `grind [args]` -/

/-- Seven, as a reducible definition, which `grind` refuses as a parameter. -/
@[reducible] def seven : Nat := 7

/-- `seven` is `7`. -/
theorem seven_def : seven = 7 := rfl

-- The term argument is kept as written and the reducible definition is dropped.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
#guard_msgs (drop info) in
example (p : Prop) (h : ∀ n : Nat, n * n = 49 → p) : p := by
  repair_dispatch_probe closes "grind [h seven rfl]" (grind [h seven rfl, seven])

-- From a `simp` leaf: the terms without `←`; `*` and erasures are not passed.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
#guard_msgs (drop info) in
example (p : Prop) (h : ∀ n : Nat, n * n = 49 → p) : p := by
  repair_dispatch_probe closes "grind [h seven rfl, seven_def]"
    (simp [h seven rfl, ← seven_def, seven, *, -Nat.add_zero])

-- A definition that is not reducible is kept.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
#guard_msgs (drop info) in
example (n : Nat) : triple n = 3 * n := by
  repair_dispatch_probe closes "grind [triple]" (simp only [triple, seven])
    titled "Repair line 1 [head Eq]: grind [triple] (kernel-checked"

/-! ## The edit range -/

/-- The identity plus zero, which `simp` proves equal to the identity once unfolded. -/
def shift (n : Nat) : Nat := n + 0

-- `tac; tac'` on one line: `simp` acts on the goal that `funext` leaves.
repair_range_probe "funext n" ↦ "funext n; simp [shift]" in
example : (fun n => shift n) = id := by
  funext n; simp [shift]

-- A sequence over two lines.
repair_range_probe "intro s" ↦ "intro s
  simp_all [shift]" in
example : ∀ s : Nat, shift s = s := by
  intro s
  simp_all [shift]

-- After `constructor`: `exact hp` acts on the other goal.
set_option linter.style.multiGoal false in
repair_range_probe "funext n" ↦ "funext n
  simp [shift]" in
example (p : Prop) (hp : p) : (fun n => shift n) = id ∧ p := by
  constructor
  funext n
  simp [shift]
  exact hp

-- The last tactic on its goal.
set_option linter.style.multiGoal false in
repair_range_probe "simp [shift]" ↦ "simp [shift]" in
example (p : Prop) (hp : p) : (fun n => shift n) = id ∧ p := by
  constructor
  funext n
  simp [shift]
  exact hp

-- `all_goals` acts on the goal of the leaf and on the other goal.
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
repair_range_probe "skip" ↦ none in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  skip
  all_goals assumption

-- `swap` and `exact hq` come between `skip` and `exact hp`, which acts on its goal.
set_option linter.style.multiGoal false in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
repair_range_probe "skip" ↦ none in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  skip
  swap
  exact hq
  exact hp

-- `simp only []` fails, so `rfl` does not run.
#guard_msgs (drop info) in
repair_range_probe "intro s" ↦ none in
#guard_msgs (drop all) in
example : ∀ s : Nat, shift s = s := by
  intro s
  simp only []
  rfl

-- The goal of `intro s` leaves the parentheses: the range starts at them.
repair_range_probe "intro s" ↦ "(intro s); simp [shift]" in
example : ∀ s : Nat, shift s = s := by
  (intro s); simp [shift]

-- Inside `have … := by`: the goal of the leaf ends with that block.
repair_range_probe "skip" ↦ "skip" in
#guard_msgs (drop all) in
example (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := by
  have h : a + 1 < c := by
    skip
  omega

-- Inside a bullet.
repair_range_probe "intro s" ↦ "intro s
    simp [shift]" in
example (p : Prop) (hp : p) : (∀ s : Nat, shift s = s) ∧ p := by
  constructor
  · intro s
    simp [shift]
  · exact hp

section Dispatch

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto
open scoped ENNReal

/-- A fair coin, negated. -/
noncomputable def flipNeg : SPComp Bool := do
  let a ← SPComp.sample Bool
  pure (!a)

/-- Negation as a program. -/
noncomputable def negStep (b : Bool) : SPComp Bool := SPComp.pure (!b)

/-- Two coins sampled in one order. -/
noncomputable def gameL : SPComp Bool := do
  let a ← SPComp.sample Bool
  let b ← SPComp.sample Bool
  pure (a && !b)

/-- The coins of `gameL` sampled in the other order. -/
noncomputable def gameR : SPComp Bool := do
  let b ← SPComp.sample Bool
  let a ← SPComp.sample Bool
  pure (a && !b)

#guard_msgs (drop info) in
example : SPComp.IsPure flipNeg := by
  repair_dispatch_probe closes "(unfold"

#guard_msgs (drop info) in
example : SPComp.IsPure (do
    let a ← SPComp.sample Bool
    let b ← SPComp.sample Bool
    pure (a && b) : SPComp Bool) := by
  repair_dispatch_probe closes "(simp only"

#guard_msgs (drop info) in
example (a : Bool) :
    rHoare eqPre (SPComp.bind (SPComp.pure a) negStep) (negStep a) eqPost := by
  repair_dispatch_probe closes "aesop"

#guard_msgs (drop info) in
example (A : Bool → SPComp Bool) (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : AdvantageA gameL flipNeg A ≤ ε₁) (h₂ : AdvantageA flipNeg gameR A ≤ ε₂) :
    AdvantageA gameL flipNeg A + AdvantageA flipNeg gameR A ≤ ε₁ + ε₂ := by
  repair_dispatch_probe closes "sum_atoms_le"

set_option repairAction.dispatchMillis 3000 in
#guard_msgs (drop info) in
example : gameL = gameR := by
  repair_dispatch_probe closes "(unfold"

end Dispatch

/-! ## Final failures -/

/-- Four times `n`, as a definition that `grind` does not unfold. -/
def quad (n : Nat) : Nat := n + n + n + n

/-- A predicate that holds of every number, by a constructor that neither `grind` nor the
premise stage of the dispatcher applies. -/
public inductive Holds : Nat → Prop
  | intro (n : Nat) : Holds n

catcrypt_auto_shape "repair holds" priority 200 := app CatCryptCore.RepairActionTest.Holds
catcrypt_auto_arm "repair holds" order 10 := "omega"

-- Every arm stops at its wall-clock cap of 0 ms: no failure is final, and the title has no
-- element `final`.
set_option repairAction.grindMillis 0 in
set_option repairAction.dispatchMillis 0 in
set_option repairAction.grindSuggestionsMillis 0 in
set_option repairAction.tryMillis 0 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : quad n = 4 * n := by
  repair_final_probe "grind open; catcrypt_auto? open; grind? +suggestions open; try? open"
    because "grind: not final: stopped at the wall-clock cap"
    titled "Repair line 1 [head Eq]: no closing arm; grind "
  grind [quad]

-- Under a heartbeat cap of one thousand, `grind` stops at the heartbeat cap well within its
-- wall-clock cap: not final.
set_option repairAction.maxHeartbeats 1 in
set_option repairAction.grindMillis 5000 in
set_option repairAction.dispatchMillis 0 in
set_option repairAction.grindSuggestionsMillis 0 in
set_option repairAction.tryMillis 0 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : quad n = 4 * n := by
  repair_final_probe "grind open; catcrypt_auto? open; grind? +suggestions open; try? open"
    because "grind: not final: stopped at the heartbeat cap"
  grind [quad]

-- `grind` fails without reaching a cap: final. `grind? +suggestions` fails too, but with the
-- theorems of the file in place of the index: not final, and its message says so.
set_option repairAction.dispatchMillis 0 in
set_option repairAction.tryMillis 0 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : quad n = 4 * n := by
  repair_final_probe "grind final; catcrypt_auto? open; grind? +suggestions open; try? open"
    because "grind? +suggestions: not final: the index was not built"
    titled "Repair line 1 [head Eq, final: grind]: no closing arm; grind "
  grind [quad]

-- The shape `other` has the dispatcher arm `grind +suggestions`, which consults the library
-- suggestions that the arm `catcrypt_auto?` switches off: not final, though no budget ran
-- out under the cap of 10 s.
set_option repairAction.grindMillis 0 in
set_option repairAction.dispatchMillis 10000 in
set_option repairAction.grindSuggestionsMillis 0 in
set_option repairAction.tryMillis 0 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  repair_final_probe "grind open; catcrypt_auto? open; grind? +suggestions open; try? open"
    because "catcrypt_auto?: not final: the dispatcher consulted the library suggestions"
  fun_induction sumTo <;> grind

-- The shape `repair holds` has the one arm `omega`, the premise stage finds no premise, and
-- no budget runs out: the failure of `catcrypt_auto?` is final.
set_option repairAction.dispatchMillis 10000 in
set_option repairAction.grindSuggestionsMillis 0 in
set_option repairAction.tryMillis 0 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : Holds n := by
  repair_final_probe "grind final; catcrypt_auto? final; grind? +suggestions open; try? open"
    titled "Repair line 1 [head CatCryptCore.RepairActionTest.Holds, shape repair holds, \
      final: grind; catcrypt_auto?]: no closing arm; grind "
  exact Holds.intro n

-- The same dispatch with a total budget of 1 ms: the budget runs out, not final.
set_option catcrypt_auto.totalMillis 1 in
set_option repairAction.grindMillis 0 in
set_option repairAction.dispatchMillis 10000 in
set_option repairAction.grindSuggestionsMillis 0 in
set_option repairAction.tryMillis 0 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : Holds n := by
  repair_final_probe "grind open; catcrypt_auto? open; grind? +suggestions open; try? open"
    because "catcrypt_auto?: not final: a budget of the dispatcher ran out"
  exact Holds.intro n

/-! ## One run of the arms per action

The failing leaf `skip`, on `quad n = 4 * n`: four arms, `grind` failing and the others at a
cap of 0 ms. Its block has no unsolved-goals action, since `skip` leaves its one goal as it
was and the request selects it as a leaf. -/

-- Listed with a nonempty range: the arms run once, and the failing action, which carries the
-- empty edit, is not resolved.
set_option repairAction.dispatchMillis 0 in
set_option repairAction.grindSuggestionsMillis 0 in
set_option repairAction.tryMillis 0 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
repair_resolve_probe "skip" runs 4 in
example (n : Nat) : quad n = 4 * n := by
  skip

-- Listed at a cursor: no arm runs, then the resolve runs the provider again and the lazy part
-- of the action, which runs the arms once.
set_option repairAction.dispatchMillis 0 in
set_option repairAction.grindSuggestionsMillis 0 in
set_option repairAction.tryMillis 0 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
repair_resolve_probe "skip" cursor runs 4 in
example (n : Nat) : quad n = 4 * n := by
  skip

/-! ## Unsolved goals at the end of a block -/

-- One goal left, closed by `grind`: a new line at the block's column.
#guard_msgs (drop info) in
repair_action_probe "refine ⟨?_, trivial⟩"
  titled "Repair line +1 [unsolved 1, head LT.lt]: grind (kernel-checked"
  ↦ "refine ⟨?_, trivial⟩\n  grind" in
example (a : Nat) : a < a + 1 ∧ True := by
  refine ⟨?_, trivial⟩

-- Two goals left, closed by `grind` and by `grind [triple]`: one bullet per goal.
set_option repairAction.extraNames "triple" in
#guard_msgs (drop info) in
repair_action_probe "constructor"
  titled "Repair line +1 [unsolved 2, head LT.lt]: grind; grind [triple] (kernel-checked"
  ↦ "constructor\n  · grind\n  · grind [triple]" in
example (a n : Nat) : a < a + 1 ∧ triple n = 3 * n := by
  constructor

-- One goal that no arm closes: `grind` fails within its caps, the other arms stop at a cap of
-- 0 ms; no text edit.
set_option repairAction.dispatchMillis 0 in
set_option repairAction.grindSuggestionsMillis 0 in
set_option repairAction.tryMillis 0 in
#guard_msgs (drop info) in
repair_action_probe "intro n"
  titled "Repair line +1 [unsolved 1, head Eq, final: grind]: no closing arm; grind "
  ↦ none in
example : ∀ n : Nat, quad n = 4 * n := by
  intro n

-- A request at the `by` token selects the block; the line is that of its last tactic.
#guard_msgs (drop info) in
repair_action_probe "by"
  titled "Repair line +2 [unsolved 1, head LT.lt]: grind (kernel-checked"
  ↦ "intro h\n  grind" in
example (a b : Nat) :
    a ≤ b → a < b + 1 := by
  intro h

-- A nested bullet: the bullets go at the column of its block.
#guard_msgs (drop info) in
repair_action_probe "refine ⟨?_, ?_⟩"
  titled "Repair line +3 [unsolved 2, head LT.lt]: grind; grind (kernel-checked"
  ↦ "refine ⟨?_, ?_⟩\n    · grind\n    · grind" in
example (p : Prop) (hp : p) (a : Nat) : p ∧ (a < a + 1 ∧ True) := by
  constructor
  · exact hp
  · refine ⟨?_, ?_⟩

/-! ## The caps

Near the end of the file: a run of `try?` that reaches its cap goes on in the background for
a while and slows the arms that run after it. -/

-- No arm closes; every arm stops within its cap.
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (h : ∀ n, 2 * sumTo n = n * n) : False := by
  repair_dispatch_probe fails_within 7000
    titled "Repair line 1 [head False, shape other, final: grind]: no closing arm; grind "
  have h1 := h 1
  simp [sumTo] at h1

/-! ## The library-suggestion index

Last in the file, and the only test that builds the index of the imported theorems (about
10 s of wall time and 81 s of CPU time): once built, the index serves the suggestion arms
of the rest of the process. -/

-- The arm waits for the build that it starts, then runs with the registered selector and
-- its index and fails without reaching a cap: final.
set_option repairAction.suggestionIndex true in
set_option repairAction.indexWaitMillis 300000 in
set_option repairAction.tryMillis 20000 in
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : Holds n := by
  repair_suggestion_probe "grind? +suggestions" fails "grind" final
  exact Holds.intro n

end CatCryptCore.RepairActionTest

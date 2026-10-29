/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Lean
public meta import CatCryptCore.Tactics.RepairAction

/-!
# The edit range at a failing leaf

Probes of the edit range of the grind repair code action of
`CatCryptCore.Tactics.RepairAction` at a leaf that fails, so that the later tactics of its
sequence did not run and have no tactic nodes; the range is then read from the syntax of the
sequence (`RepairAction.failedSpan`).

* `repair_range_probe` elaborates a declaration and checks the edit range
  (`RepairAction.editSpan`) at one of its leaves, or that there is none and why.
* `repair_edit_probe` elaborates a declaration, lists the code actions of the provider
  (`RepairAction.actionsAt`, the arms run at once) at the first occurrence of a text in it,
  and reports the title of the first action with a text edit, the range of the edit (lines
  relative to the first line of the declaration, columns from 0), the text it replaces and
  its new text.

The cases, each over the fresh definition `twice`:
* a failing `simp only` followed by `exact h` on the same goal: the range runs to `exact h`;
* the same on one line, `simp only [...]; exact h`;
* inside a `·` block, over two lines: the range ends with the block;
* a failing leaf with one other goal, followed by one `·` block, or by one `case` block for
  that goal: the range is the leaf;
* a failing leaf with one other goal, followed by `exact hp`, or by two `·` blocks: no range.
-/

set_option autoImplicit false

set_option repairAction.suggestionIndex false
set_option repairAction.dispatchMillis 0
set_option repairAction.grindSuggestionsMillis 0
set_option repairAction.tryMillis 0

namespace CatCryptCore.RepairActionSpanTest

/-- Twice `n`, as an opaque definition. -/
def twice (n : Nat) : Nat := n + n

/-! ## The probes -/

public meta section

open Lean Elab Meta Command CatCryptCore.RepairAction

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

/-- `title` with the line `N` of `Repair line N` written `+k`, where `k = N - base`, and
without the timing in parentheses at its end. -/
def relativeTitle (title : String) (base : Nat) : String :=
  let title := (title.splitOn " (kernel-checked").headD title
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

/-- `repair_edit_probe "s" in cmd` elaborates `cmd`, dropping its messages, lists the code
actions of the provider (`actionsAt`, the arms run at once) for the range of the first
occurrence of `s` in `cmd`, and reports the first action with one text edit: its title (line
written `+k` for the `k`-th line after the first line of `cmd`), the range of the edit (lines
`+k`, columns from 0), the source text in that range and the new text. -/
syntax (name := editProbe) "repair_edit_probe " str " in " command : command

@[command_elab editProbe, inherit_doc editProbe]
def elabEditProbe : CommandElab := fun stx => do
  let sel := stx[1].isStrLit?.getD ""
  let (t, base, r) ← elabForActions stx[3] sel
  let text ← getFileMap
  let actions ← actionsAt probeDoc text t r.start r.stop true
  let edits := actions.filterMap fun a =>
    match jsonEdits a.eager with
    | some #[te] => some (a.eager.title, te)
    | _ => none
  let some (title, te) := edits[0]?
    | throwError "repair_edit_probe: no action with one text edit; the titles are\
        {indentD (MessageData.joinSep (actions.map (toMessageData ·.eager.title)).toList "\n")}"
  let old := String.Pos.Raw.extract text.source (text.lspPosToUtf8Pos te.range.start)
    (text.lspPosToUtf8Pos te.range.end)
  let pos (p : Lsp.Position) := s!"+{p.line + 1 - base}:{p.character}"
  logInfo m!"{relativeTitle title base}\nrange {pos te.range.start}-{pos te.range.end}\
    \nreplaces{indentD old}\nby{indentD te.newText}"

end

/-! ## Ranges -/

-- A failing `simp only` followed by `exact h` on the same goal: the range runs to `exact h`.
#guard_msgs (drop info) in
repair_range_probe "simp only [Nat.mul_one]" ↦ "simp only [Nat.mul_one]
  exact h" in
#guard_msgs (drop all) in
example (n : Nat) (h : twice n = 2 * n) : twice n = 2 * n := by
  simp only [Nat.mul_one]
  exact h

-- `tac; tac'` on one line.
repair_range_probe "simp only [Nat.mul_one]" ↦ "simp only [Nat.mul_one]; exact h" in
#guard_msgs (drop all) in
example (n : Nat) (h : twice n = 2 * n) : twice n = 2 * n := by
  simp only [Nat.mul_one]; exact h

-- Inside a `·` block: the range ends with the block; the other block ran.
repair_range_probe "simp only [Nat.mul_one]" ↦ "simp only [Nat.mul_one]
    exact h" in
#guard_msgs (drop all) in
example (n : Nat) (p : Prop) (hp : p) (h : twice n = 2 * n) : twice n = 2 * n ∧ p := by
  constructor
  · simp only [Nat.mul_one]
    exact h
  · exact hp

-- One other goal and one `·` block for it: the range is the leaf.
repair_range_probe "simp only [Nat.mul_one]" ↦ "simp only [Nat.mul_one]" in
#guard_msgs (drop all) in
example (n : Nat) (p : Prop) (hp : p) (h : twice n = 2 * n) : twice n = 2 * n ∧ p := by
  refine ⟨?_, ?_⟩
  simp only [Nat.mul_one]
  · exact hp

-- One other goal and one `case` block for it: the range is the leaf.
repair_range_probe "simp only [Nat.mul_one]" ↦ "simp only [Nat.mul_one]" in
#guard_msgs (drop all) in
example (n : Nat) (p : Prop) (hp : p) (h : twice n = 2 * n) : twice n = 2 * n ∧ p := by
  refine ⟨?_, ?right⟩
  simp only [Nat.mul_one]
  case right => exact hp

-- One other goal, then `exact hp`: written for the goal of the leaf or for the other goal.
/--
info: no edit range: the leaf failed with 1 other goals open, and the tactics after it are
not one block `·`, `case` or `next` per other goal
-/
#guard_msgs (whitespace := lax) in
repair_range_probe "simp only [Nat.mul_one]" ↦ none in
#guard_msgs (drop all) in
example (n : Nat) (p : Prop) (hp : p) (h : twice n = 2 * n) : twice n = 2 * n ∧ p := by
  refine ⟨?_, ?_⟩
  simp only [Nat.mul_one]
  exact hp

-- One other goal and two `·` blocks: the leaf was to leave a goal of its own.
#guard_msgs (drop info) in
repair_range_probe "simp only [Nat.mul_one]" ↦ none in
#guard_msgs (drop all) in
example (n : Nat) (p : Prop) (hp : p) (h : twice n = 2 * n) : twice n = 2 * n ∧ p := by
  refine ⟨?_, ?_⟩
  simp only [Nat.mul_one]
  · exact h
  · exact hp

-- A tactic between the leaf and a later tactic failed: no range.
#guard_msgs (drop info) in
repair_range_probe "intro m" ↦ none in
#guard_msgs (drop all) in
example : ∀ m : Nat, twice m = 2 * m := by
  intro m
  simp only [Nat.mul_one]
  omega

/-! ## Offered edits -/

-- The edit replaces `simp only [...]` and `exact h` by `grind`.
/--
info: Repair line +1 [head Eq]: grind
range +1:2-+2:9
replaces
  simp only [Nat.mul_one]
    exact h
by
  grind
-/
#guard_msgs in
set_option linter.unusedVariables false in
repair_edit_probe "simp only [Nat.mul_one]" in
example (n : Nat) (h : twice n = 2 * n) : twice n = 2 * n := by
  simp only [Nat.mul_one]
  exact h

-- The edit replaces `simp only [...]; exact h` on one line by `grind`.
/--
info: Repair line +1 [head Eq]: grind
range +1:2-+1:34
replaces
  simp only [Nat.mul_one]; exact h
by
  grind
-/
#guard_msgs in
set_option linter.unusedVariables false in
repair_edit_probe "simp only [Nat.mul_one]" in
example (n : Nat) (h : twice n = 2 * n) : twice n = 2 * n := by
  simp only [Nat.mul_one]; exact h

-- The edit replaces the leaf alone; the `·` block takes the other goal.
/--
info: Repair line +2 [head Eq]: grind
range +2:2-+2:25
replaces
  simp only [Nat.mul_one]
by
  grind
-/
#guard_msgs in
set_option linter.unusedVariables false in
repair_edit_probe "simp only [Nat.mul_one]" in
example (n : Nat) (p : Prop) (hp : p) (h : twice n = 2 * n) : twice n = 2 * n ∧ p := by
  refine ⟨?_, ?_⟩
  simp only [Nat.mul_one]
  · exact hp

end CatCryptCore.RepairActionSpanTest

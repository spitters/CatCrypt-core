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
  given tactic text.
* `repair_range_probe` elaborates a declaration and checks the edit range
  (`RepairAction.editSpan`) at one of its leaves.

The file sets `repairAction.suggestionIndex` to false, so that the suggestion arms use the
theorems of this file and no index of the imported theorems is built.

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
* caps, last in the file: `False` from `∀ n, 2 * sumTo n = n * n`: no arm, within 7000 ms in
  all, with the title `[head False, shape other]`.
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

/-- `repair_suggestion_probe "t" fails "m"` runs the suggestion arm `t` (`runSuggestionArm`,
under the cap `repairAction.tryMillis`) on the main goal and requires that it does not close
the goal, with a failure reason containing `m`; the goal is unchanged. It reports the arm. -/
syntax (name := suggestionProbe) "repair_suggestion_probe " str " fails " str : tactic

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
  logInfo m!"repair arm: {report #[res]}"
  if res.closed then throwError "repair_suggestion_probe: the arm closes the goal"
  unless (res.msg.splitOn m).length > 1 do
    throwError "repair_suggestion_probe: the failure reason is {res.msg}, expected {m}"

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

-- `grind` fails without `dbl_add`; `grind? +suggestions` finds it among the theorems of the
-- file. The cap of 0 ms stops the arm `catcrypt_auto?` at once.
set_option repairAction.dispatchMillis 0 in
#guard_msgs (drop info) in
example (a b c : Nat) : dbl (a + b + c) = dbl a + dbl b + dbl c := by
  repair_dispatch_probe closes "grind only [dbl_add"

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

/-! ## The caps

Last in the file: a run of `try?` that reaches its cap goes on in the background for a while
and slows the arms that run after it. -/

-- No arm closes; every arm stops within its cap.
set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (h : ∀ n, 2 * sumTo n = n * n) : False := by
  repair_dispatch_probe fails_within 7000
    titled "Repair line 1 [head False, shape other]: no closing arm; grind "
  have h1 := h 1
  simp [sumTo] at h1

end CatCryptCore.RepairActionTest

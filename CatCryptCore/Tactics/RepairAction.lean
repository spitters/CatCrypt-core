/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Lean

/-!
# Grind repair code action

A code action provider that, at a tactic leaf selected by the request range, runs a sequence
of arms on the goal recorded in the info tree of the elaborated file and stops at the first
closing arm. The goal is taken from `TacticInfo.goalsBefore` and its metavariable context
`mctxBefore`, so no part of the file is elaborated again. A proof that an arm produces is
closed over its local context and checked by the kernel before the arm counts as closing.
The auxiliary declarations an arm adds (`_proof_1`, …) are named under the prefix
`<declaration>._repairAction`, which no declaration of the file has: under the empty prefix of
a fresh elaboration state their names would be those of the file's own auxiliary
declarations.

## The arms, in order

Each arm, kernel check included, runs under the heartbeat cap `repairAction.maxHeartbeats`
(default 100000, in the unit of `maxHeartbeats`) and under a wall-clock cap, since a run of
`grind` or of the library-suggestion selector can exceed any heartbeat cap. The arm runs in
a task of its own on a copy of the state (`capped`); at its cap the action sets the arm's
cancellation token and goes on without waiting for the task, since `try?` can run on for
seconds after the token is set. Such a task ends in the background, and while it runs it
takes cores from the arms after it.

1. `grind`, cap `repairAction.grindMillis` (default 600 ms).
2. `grind [args]`, when there are arguments, cap `repairAction.grindMillis`.
3. `catcrypt_auto?`, when that tactic parses in the environment of the leaf
   (`dispatchAvailable`; the module names no constant of the dispatcher), cap
   `repairAction.dispatchMillis` (default 1000 ms). It runs under the dispatcher's own
   budgets (`catcrypt_auto.maxHeartbeats` per arm of the dispatcher), with
   `catcrypt_auto.totalMillis` and `catcrypt_auto.maxMillis` cut to the cap. Unless
   `repairAction.dispatchSuggestions` is set, its library-suggestion selector is
   `offSelector`, which fails, so that the arms `grind +suggestions` of the dispatcher fail
   at once, and records the call (see "Final failures"). Its
   text is the suggestion it adds to the info tree (its last `TryThisInfo` node), and
   `catcrypt_auto` when there is none.
4. `grind? +suggestions`, cap `repairAction.grindSuggestionsMillis` (default 1000 ms).
5. `try?`, cap `repairAction.tryMillis` (default 2000 ms).

The arms 4 and 5 are suggestion arms: the arm runs, its text is the first suggestion of the
last "Try this" message it adds to the info tree, and the arm closes only when that text
contains no placeholder token for a missing proof (`hasSorryToken`; a `grind` script ending
in an open case has one) and, run alone on the goal under the same token, closes it with a
proof that the kernel accepts. The library-suggestion selector of these arms indexes the
imported theorems on first use in a process (10 s of wall time and 81 s of CPU time on 24
threads over Mathlib; the second use takes milliseconds), and an index build that is
interrupted is not kept. The first suggestion arm of a process therefore starts the build in
a background task, under no cap and no token. While that task runs, a suggestion arm waits
for it before its caps start, until `repairAction.indexWaitMillis` milliseconds (default
40000) after the start of the build; the bound counts from the start of the build, so that
the arms and leaves after a wait that ended without the index do not wait again. An arm
whose wait ends without the index runs with the selector `LibrarySuggestions.currentFile`
(the theorems of the current file) in place of the registered one, and its failure reason
says `index not built`. When `repairAction.suggestionIndex` is false no build starts, no arm
waits, and the arms run with `currentFile`. While the build runs it takes the cores of the
machine, and the arms are slower.

## Final failures

When no arm closes, the outer tool that calls the action runs `grind? +suggestions`,
`catcrypt_auto?` and `try?` again in a scratch copy of the file, each as
`set_option maxHeartbeats 100000 in <arm>`, with no wall-clock cap and the options of the
file: the registered selector with its index, the dispatcher's own budgets and its library
suggestions. A failed arm is final when it follows from how the arm ran that the same arm
fails in that run, on the same environment and goal (`ArmResult.final`, with the reason in
`ArmResult.finality`):
* no arm that reached its heartbeat cap or its wall-clock cap is final (`capped` records the
  cap reached: an interrupt or a run past the deadline, the heartbeat exception, or at least
  `repairAction.maxHeartbeats` thousand heartbeats spent by the arm's thread, since a tactic
  can catch the exception and fail for another reason);
* `grind` and `grind [args]` are final otherwise: the tactic, goal and options are those of
  the scratch run, and a run that stayed under the cap stays under any larger limit;
* a suggestion arm is final otherwise when it ran with the registered selector and its
  index built, whatever its failure (no suggestion, a suggestion containing `sorry`, one
  that leaves goals or that the kernel rejects); with `currentFile` it is not final;
* `catcrypt_auto?` is final when it is not in the environment, and otherwise when the run
  differs from the scratch run in nothing that can change its outcome. The run differs in
  two ways. Its wall-clock budgets `catcrypt_auto.maxMillis` and `catcrypt_auto.totalMillis`
  are cut to the arm's cap (its heartbeat budgets are its own in both runs); the dispatcher
  reports each budget that ran out in its error ("exceeded the time budget of N ms", "the
  total time budget of N ms is spent", `reportsBudgetOut`; a step between arms that
  exceeds the time left also spends the total budget, which the error then reports). And
  unless `repairAction.dispatchSuggestions` is set its selector is `offSelector`, which
  records that the run consulted it (the dispatcher's `warmSuggestions` before an arm
  `grind +suggestions`, or the arm itself) and fails. The failure is final when the run
  reached no cap, no budget ran out and no library suggestion was consulted. A run under
  the scratch run's budgets (5 s per arm, 30 s in all by default) does not fit the arm's cap
  of 1 s, so the arm is not run again.

## Arguments of `grind [args]`

`args` are taken from the tactics of the edit range (below) and from
`repairAction.extraNames` (names separated by spaces or commas):
* each `grind` parameter and each `simp` argument of these tactics, as written: the term of a
  `simp` argument without its `←`, `↓` or `↑`, a `grind` parameter with its modifier; `simp`
  erasures, `*` and `grind` erasures and anchors are not passed;
* the other identifiers of these tactics that resolve to a global constant and are not local
  hypotheses.
An argument is passed only when `grind` accepts it, by the rules of `grind`'s parameter
elaboration: an identifier naming a theorem, an axiom, a constructor, an inductive type or a
definition that is not reducible (a definition with no modifier or `=`), or an identifier with
a local hypothesis as its root (dot notation); a local hypothesis itself (which `grind`
refuses as redundant), a reducible definition (which `grind` refuses since it unfolds it) and
any other constant are dropped. A term argument is passed when each identifier in it is a
local hypothesis, has one as its root, or resolves to a global constant.

## The edit range

On a closing arm the action replaces the edit range of the leaf by the arm's text. The range
is decided from the tactic nodes of the info tree (`editSpan`). The anchor is the element of
the innermost tactic sequence that contains the leaf (the leaf itself, or the combinator
around it); its main goal before must be the leaf's goal `g`. From the anchor on, the
elements of the sequence are followed with the set `D` of the goals that descend from `g`:
an element acts on `D` when the goals it removes are in `D` (then `D` loses them and gains
the goals it adds) or when it changes no goal and its main goal is in `D` (`skip`, or a
tactic that failed). The range runs from the anchor to the last element acting on `D`, and
stops once `D` is empty. When `D` is still nonempty at the end of the sequence and its goals
outlive the tactic enclosing the sequence (a goal after that tactic is in `D`), the anchor
moves to that tactic, provided the leaf's anchor is the first element of its sequence. The
action offers no closure, and says why in its title, when an element acts on `D` and on
other goals, when an element that changes other goals comes between two elements acting on
`D`, when an element after the anchor did not run while `D` is nonempty (a tactic before it
failed), or when the leaf runs on several goals.

The text of a closing arm is laid out for the column at which the edit range starts
(`layoutAt`): a suggestion is laid out for the column of the syntax that made it, and a text
over several lines placed after other tactics on a line need not parse there. The text is put
on one line when that parses to the same tactic, else pretty-printed for the column when that
parses there to the same tactic.

## Leaves, titles, options

* A leaf is a node of the info tree for a tactic as written in the source: its syntax kind
  is a kind of the tactic category other than a tactic sequence, and its source information
  is original. Its source range meets the request range (overlaps it when the request range
  is nonempty, contains it when it is empty), and it contains no other such node. A line
  inside a tactic written over several lines thus selects that tactic, and a step that a
  macro adds (the closing `rfl` of `rw`, placed at its `]`) is not a leaf.
  At most three leaves are treated per request.
* The title of the action names, in brackets, the head symbol of the goal (`goalHead`),
  when the arm `catcrypt_auto?` ran and failed, the goal shape its error names, and, when no
  arm closed and some failure is final, the element `final: A; B; …` naming the arms whose
  failure is final, by the names `grind`, `grind args`, `catcrypt_auto?`,
  `grind? +suggestions` and `try?` (`grind args` is the arm `grind [args]`: the tag holds no
  `]`, so that the outer tool's pattern `Repair line (\d+)( \[[^\]]*\])?: (.*)` reads it).
  A closing title then gives the arm's text and time, a failing one each arm with its time
  and outcome, so that logs can group the leaves by goal. Examples:
  `Repair line 12 [head Eq]: grind [triple] (kernel-checked, 19 ms)`,
  `Repair line 12 [head Eq, shape other, final: grind; catcrypt_auto?]: no closing arm;
  grind 4 ms (…); …`, and with no final failure
  `Repair line 12 [head Eq]: no closing arm; grind 0 ms (exceeded the cap of 0 ms); …`.
* The options are read from the options in force at the leaf (`set_option` above the
  declaration), by name.
* For a request with a nonempty range the arms run when the actions are listed; for an empty
  range (an editor cursor) they run when the action is resolved.

The provider is in scope wherever `CatCryptCore.Tactics.AutoBase` is imported.
-/

set_option autoImplicit false

public meta section

namespace CatCryptCore.RepairAction

open Lean Elab Server Lsp RequestM Snapshots Meta

register_option repairAction.maxHeartbeats : Nat := {
  defValue := 100000
  descr := "heartbeat cap (in thousands, as `maxHeartbeats`) for each arm of the grind \
    repair code action and for its kernel check; an arm that reaches it, or its \
    wall-clock cap, has no final failure"
}

register_option repairAction.extraNames : String := {
  defValue := ""
  descr := "names, separated by spaces or commas, added to the `grind [args]` arm of the \
    grind repair code action"
}

register_option repairAction.dispatchMillis : Nat := {
  defValue := 1000
  descr := "wall-clock cap, in milliseconds, of the `catcrypt_auto?` arm of the repair \
    code action"
}

register_option repairAction.grindMillis : Nat := {
  defValue := 600
  descr := "wall-clock cap, in milliseconds, of each arm `grind` and `grind [args]` of the \
    repair code action, kernel check included"
}

register_option repairAction.grindSuggestionsMillis : Nat := {
  defValue := 1000
  descr := "wall-clock cap, in milliseconds, of the `grind? +suggestions` arm of the repair \
    code action, the run of its suggestion and the kernel check included"
}

register_option repairAction.tryMillis : Nat := {
  defValue := 2000
  descr := "wall-clock cap, in milliseconds, of the `try?` arm of the repair code action, \
    the run of its suggestion and the kernel check included"
}

register_option repairAction.dispatchSuggestions : Bool := {
  defValue := false
  descr := "keep the library-suggestion selector in the `catcrypt_auto?` arm of the \
    repair code action; when false a failure of that arm in which the dispatcher \
    consulted library suggestions is not final"
}

register_option repairAction.suggestionIndex : Bool := {
  defValue := true
  descr := "build the library-suggestion index of the imported theorems in a background \
    task for the suggestion arms of the repair code action, and let these arms wait for it \
    (`repairAction.indexWaitMillis`); when false they use the theorems of the current file \
    only, with no wait, and their failures are not final"
}

/-- The default of `repairAction.indexWaitMillis`. The first run of the registered selector
in a process, which builds its index, was measured at 10.1 s of wall time and 81 s of CPU
time on 24 threads in a worker importing `AutoDispatch`; the same CPU time takes longer on
fewer cores (32.5 s on 4 cores). The outer tool waits up to 60 s for the action. The action
treats up to three leaves; by the default caps each runs its arms in at most 5.2 s, and the
build starts at the first suggestion arm, so a request takes at most `W + 15.6` s with a
bound of `W`. A bound of 40 s covers both measurements and keeps a request under 60 s. -/
def indexWaitDefault : Nat := 40000

register_option repairAction.indexWaitMillis : Nat := {
  defValue := indexWaitDefault
  descr := "wall-clock bound, in milliseconds counted from the start of the build, for \
    which the suggestion arms of the repair code action wait for the library-suggestion \
    index; when the wait ends without it they run with the theorems of the current file. \
    The default (40000) covers the measured build (10.1 s on 24 threads, 32.5 s on 4) and \
    keeps the wait and the arms of three leaves (5.2 s each) under the caller's bound of \
    60 s"
}

/-- Syntax kinds of tactic sequences; nodes of these kinds are never leaves. -/
def sequenceKinds : List SyntaxNodeKind :=
  [``Parser.Tactic.tacticSeq, ``Parser.Tactic.tacticSeq1Indented,
    ``Parser.Tactic.tacticSeqBracketed, nullKind]

/-- A tactic node of the info tree with its context and original source range. -/
structure Leaf where
  /-- Context of the node. -/
  ctx : ContextInfo
  /-- The tactic node. -/
  info : TacticInfo
  /-- Original source range of the node's syntax. -/
  range : Syntax.Range

/-- `k` is a syntax kind of the tactic category of `env`. -/
def isTacticKind (env : Environment) (k : SyntaxNodeKind) : Bool :=
  match Parser.getParserCategory? env `tactic with
  | some cat => cat.kinds.contains k
  | none => false

/-- Nodes of tactics as written in the source, with a goal, whose original range meets
`[lo, hi]`: overlaps it when `lo < hi`, contains `lo` when `lo = hi`. -/
def collectLeaves (t : InfoTree) (lo hi : String.Pos.Raw) : Array Leaf :=
  t.foldInfo (init := #[]) fun ctx info acc => Id.run do
    let .ofTacticInfo ti := info | acc
    let k := ti.stx.getKind
    if sequenceKinds.contains k || !isTacticKind ctx.env k then return acc
    unless ti.stx.getHeadInfo matches .original .. do return acc
    if ti.goalsBefore.isEmpty then return acc
    let some r := ti.stx.getRange? (canonicalOnly := true) | acc
    let meets := if lo == hi then r.start ≤ lo && lo ≤ r.stop else r.start < hi && lo < r.stop
    unless meets do return acc
    acc.push { ctx, info := ti, range := r }

/-- `r` and `s` are the same range. -/
def Syntax.Range.same (r s : Syntax.Range) : Bool :=
  r.start == s.start && r.stop == s.stop

/-- `r` lies inside `s`. -/
def Syntax.Range.inside (r s : Syntax.Range) : Bool :=
  s.start ≤ r.start && r.stop ≤ s.stop

/-- `r` lies inside `s` and differs from it. -/
def Syntax.Range.strictlyInside (r s : Syntax.Range) : Bool :=
  Syntax.Range.inside r s && !Syntax.Range.same r s

/-- The leaves containing no other leaf, the first of each source range only. -/
def minimalLeaves (ls : Array Leaf) : Array Leaf := Id.run do
  let mut out : Array Leaf := #[]
  for l in ls do
    if ls.any (fun m => Syntax.Range.strictlyInside m.range l.range) then continue
    if out.any (fun m => Syntax.Range.same m.range l.range) then continue
    out := out.push l
  return out

/-! ## The edit range -/

/-- A tactic node of the info tree: its syntax, original source range and goals. -/
structure Step where
  /-- Syntax of the node. -/
  stx : Syntax
  /-- Original source range of the syntax. -/
  range : Syntax.Range
  /-- Goals before the tactic. -/
  before : List MVarId
  /-- Goals after the tactic. -/
  after : List MVarId

/-- The tactic nodes of `t` with an original source range, in preorder. -/
def steps (t : InfoTree) : Array Step :=
  t.foldInfo (init := #[]) fun _ info acc => Id.run do
    let .ofTacticInfo ti := info | acc
    let some range := ti.stx.getRange? (canonicalOnly := true) | acc
    acc.push { stx := ti.stx, range, before := ti.goalsBefore, after := ti.goalsAfter }

/-- The elements of a tactic sequence node, with their source ranges. -/
def sequenceElements (stx : Syntax) : Option (Array (Syntax × Syntax.Range)) :=
  let elems (args : Array Syntax) :=
    args.filterMap fun e => (e.getRange? (canonicalOnly := true)).map (e, ·)
  if stx.isOfKind ``Parser.Tactic.tacticSeq1Indented then some (elems stx[0].getSepArgs)
  else if stx.isOfKind ``Parser.Tactic.tacticSeqBracketed then some (elems stx[1].getSepArgs)
  else none

/-- A tactic sequence: its source range and its elements. -/
structure Sequence where
  /-- Source range of the sequence. -/
  range : Syntax.Range
  /-- Elements of the sequence with their source ranges. -/
  elems : Array (Syntax × Syntax.Range)

/-- The tactic sequences in the syntax `stx`, added to `acc` when no sequence of the same
source range is there. They are read from the syntax, since the info tree has no node for
the sequence of a nested `by` block. -/
partial def sequencesIn (stx : Syntax) (acc : Array Sequence) : Array Sequence :=
  let acc := match sequenceElements stx, stx.getRange? (canonicalOnly := true) with
    | some elems, some range =>
      if acc.any (Syntax.Range.same ·.range range) then acc else acc.push { range, elems }
    | _, _ => acc
  match stx with
  | .node _ _ args => args.foldl (fun a s => sequencesIn s a) acc
  | _ => acc

/-- The range of the edit at a leaf and the tactics it replaces. -/
structure EditSpan where
  /-- Source range replaced by the edit. -/
  range : Syntax.Range
  /-- The tactics in the range, in order. -/
  tactics : Array Syntax

/-- The node of the sequence element `e`: the node of its kind and range. `none` when the
element did not run; an error when it ran on several goal lists. -/
def elementNode (ss : Array Step) (e : Syntax × Syntax.Range) : Except String (Option Step) := do
  let ns := ss.filter fun s => s.stx.getKind == e.1.getKind && Syntax.Range.same s.range e.2
  let some n := ns[0]? | return none
  unless ns.all (·.before == n.before) do
    throw "the tactic of the leaf runs on several goals"
  return some n

/-- The element of the innermost sequence of `seqs` that contains `cur`: the index of the
sequence and of the element. -/
def innermost (seqs : Array Sequence) (cur : Syntax.Range) : Option (Nat × Nat) := Id.run do
  let mut best : Option (Nat × Nat × Nat) := none
  for h : i in [0:seqs.size] do
    let es := seqs[i].elems
    for h : j in [0:es.size] do
      let r := es[j].2
      unless Syntax.Range.inside cur r do continue
      let size := r.stop.byteIdx - r.start.byteIdx
      if best.all (size < ·.2.2) then best := some (i, j, size)
  return best.map fun (i, j, _) => (i, j)

/-- The element of a sequence other than `seqs[si]` whose range contains the range of
`seqs[si]` strictly, the smallest such. -/
def enclosing (seqs : Array Sequence) (si : Nat) : Option (Syntax × Syntax.Range) := Id.run do
  let some s := seqs[si]? | return none
  let mut best : Option (Syntax × Syntax.Range) := none
  for h : i in [0:seqs.size] do
    if i == si then continue
    for e in seqs[i].elems do
      unless Syntax.Range.strictlyInside s.range e.2 do continue
      let size (r : Syntax.Range) := r.stop.byteIdx - r.start.byteIdx
      if best.all fun b => size e.2 < size b.2 then
        best := some e
  return best

/-- The edit range for a closure of the goal `g` of the tactic at `cur`, by the rule of the
module docstring, over the tactic nodes `ss` of the info tree, within the outermost of them
that contains `cur`. `fuel` bounds the number of times the anchor moves outwards. -/
partial def editSpan (ss : Array Step) (cur : Syntax.Range) (g : MVarId) (fuel : Nat := 16) :
    Except String EditSpan := do
  let top? := (ss.filter (Syntax.Range.inside cur ·.range)).foldl (init := none)
    fun (b : Option Step) s =>
      if b.all (Syntax.Range.strictlyInside ·.range s.range) then some s else b
  let some top := top? | throw "the leaf is in no tactic block"
  let ss := ss.filter (Syntax.Range.inside ·.range top.range)
  let seqs := sequencesIn top.stx #[]
  let some (si, ei) := innermost seqs cur | throw "the leaf is in no tactic sequence"
  let some s := seqs[si]? | throw "the leaf is in no tactic sequence"
  let es := s.elems
  let some e := es[ei]? | throw "the leaf is in no tactic sequence"
  let some n ← elementNode ss e | throw "the leaf did not run"
  unless n.before.head? == some g do
    throw "the leaf runs inside a tactic on another goal"
  let mut d : List MVarId := [g]
  let mut last := ei
  let mut gap := false
  for h : j in [ei:es.size] do
    if d.isEmpty then break
    let some n ← elementNode ss es[j]
      | throw "a tactic after the leaf did not run (a tactic before it failed)"
    let removed := n.before.filter (!n.after.contains ·)
    let added := n.after.filter (!n.before.contains ·)
    let acts := removed.any d.contains ||
      (removed.isEmpty && n.before == n.after && n.before.head?.any d.contains)
    if acts then
      unless removed.all d.contains do
        throw "a tactic after the leaf acts on its goal and on other goals"
      if gap then
        throw "a tactic on other goals comes between the tactics on the goal of the leaf"
      d := d.filter (!removed.contains ·) ++ added
      last := j
    else if n.before != n.after then
      gap := true
  if !d.isEmpty then
    if let some e' := enclosing seqs si then
      if let some n' ← elementNode ss e' then
        if n'.after.any d.contains then
          unless ei == 0 && fuel > 0 do
            throw "the goal of the leaf outlives the tactic around the leaf"
          return ← editSpan ss e'.2 g (fuel - 1)
  let stop := (es[last]?.map (·.2.stop)).getD e.2.stop
  return { range := ⟨e.2.start, stop⟩,
           tactics := (es.extract ei (last + 1)).map (·.1) }

/-! ## Arguments of `grind [args]` -/

/-- Identifiers occurring in `stx`, without repetition, in order of occurrence. -/
partial def identsOf (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  match stx with
  | .ident _ _ n _ => if acc.contains n then acc else acc.push n
  | .node _ _ args => args.foldl (fun a s => identsOf s a) acc
  | _ => acc

/-- `stx` is a `grind` parameter or a `simp` argument. -/
def isArgNode (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Tactic.grindParam || stx.isOfKind ``Parser.Tactic.simpLemma ||
    stx.isOfKind ``Parser.Tactic.simpErase || stx.isOfKind ``Parser.Tactic.simpStar

/-- The outermost `grind` parameters and `simp` arguments of `stx`, and the identifiers of
`stx` outside them. -/
partial def argsAndIdents (stx : Syntax) (acc : Array Syntax × Array Name := (#[], #[])) :
    Array Syntax × Array Name :=
  if isArgNode stx then (acc.1.push stx, acc.2) else
  match stx with
  | .ident _ _ n _ => if acc.2.contains n then acc else (acc.1, acc.2.push n)
  | .node _ _ args => args.foldl (fun a s => argsAndIdents s a) acc
  | _ => acc

/-- `n` is a local hypothesis of the context or has one as its root (dot notation). -/
def isLocalRooted (lctx : LocalContext) (n : Name) : Bool :=
  (lctx.findFromUserName? n).isSome ||
    (lctx.findFromUserName? (n.components.headD .anonymous)).isSome

/-- `grind` accepts the constant `c` as a parameter: a theorem, an axiom, a constructor, an
inductive type, or a definition that is not reducible when `eqOk` (no modifier, or `=`). -/
def acceptsConst (c : Name) (eqOk : Bool) : MetaM Bool := do
  match (← getEnv).find? c with
  | some (.thmInfo _) | some (.axiomInfo _) | some (.ctorInfo _) | some (.inductInfo _) =>
    return true
  | some (.defnInfo _) => return eqOk && !(← isReducible c)
  | _ => return false

/-- `grind` accepts the term `t` as a parameter in the local context, by the rules of the
module docstring; `eqOk` when its modifier is absent or `=`. -/
def acceptsParam (t : Syntax) (eqOk : Bool) : MetaM Bool := do
  let lctx ← getLCtx
  match t with
  | .ident _ _ n _ =>
    if (lctx.findFromUserName? n).isSome then return false
    if isLocalRooted lctx n then return true
    let rs ← resolveGlobalName n
    match rs.filter (·.2.isEmpty) with
    | [(c, _)] => acceptsConst c eqOk
    | [] => return rs.any (!·.2.isEmpty)
    | _ => return false
  | _ =>
    (identsOf t).allM fun n => do
      if isLocalRooted lctx n then return true
      return !(← resolveGlobalName n).isEmpty

/-- `s` with its runs of white space made single spaces, and none at its ends. -/
def squash (s : String) : String :=
  " ".intercalate ((s.splitToList Char.isWhitespace).filter (!·.isEmpty))

/-- Source text of `stx`, read from its source information (the file map of a context of the
info tree need not be that of the document), its runs of white space made single spaces. -/
def sourceText (stx : Syntax) : String :=
  squash (stx.reprint.getD stx.prettyPrint.pretty)

/-- The `grind` parameter for the argument node `a` (see `isArgNode`), or `none` when it is not
passed. -/
def paramOf (a : Syntax) : MetaM (Option String) := do
  if a.isOfKind ``Parser.Tactic.simpLemma then
    let t := a[2]
    unless ← acceptsParam t true do return none
    return some (sourceText t)
  unless a.isOfKind ``Parser.Tactic.grindParam do return none
  let p := a[0]
  let (mod, t) :=
    if p.isOfKind ``Parser.Tactic.grindLemma then (p[0], p[1])
    else if p.isOfKind ``Parser.Tactic.grindLemmaMin then (p[1], p[2])
    else (.missing, .missing)
  if t.isMissing then return none
  let eqOk := mod.getNumArgs == 0 || mod[0][0].isOfKind ``Parser.Attr.grindEq
  unless ← acceptsParam t eqOk do return none
  return some (sourceText a)

/-- Names of `repairAction.extraNames`. -/
def extraNames (opts : Options) : Array Name :=
  ((opts.get `repairAction.extraNames "").replace "," " ").splitOn " "
    |>.filter (!·.isEmpty) |>.map String.toName |>.toArray

/-- The arguments of the arm `grind [args]` from the tactics `stxs` and the names `extra`,
without repetition, in the local context of `g`. -/
def grindArgs (g : MVarId) (stxs : Array Syntax) (extra : Array Name) : MetaM (Array String) :=
  g.withContext do
    let lctx ← getLCtx
    let mut out : Array String := #[]
    let mut names : Array Name := #[]
    for stx in stxs do
      let (args, idents) := argsAndIdents stx
      for a in args do
        if let some p ← paramOf a then
          unless p.isEmpty || out.contains p do out := out.push p
      names := names ++ idents
    for n in names ++ extra do
      if isLocalRooted lctx n then continue
      unless ← acceptsParam (mkIdent n) true do continue
      let p := toString n
      unless out.contains p do out := out.push p
    return out

/-! ## Running an arm -/

/-- Outcome of one arm. -/
structure ArmResult where
  /-- Tactic text of the arm. -/
  text : String
  /-- The arm closed the goal and the kernel accepted the proof. -/
  closed : Bool
  /-- Wall time of the arm and its kernel check, in milliseconds. -/
  ms : Nat
  /-- Failure reason, empty on success. -/
  msg : String
  /-- The goal shape that the arm reported, empty when it reported none. -/
  shape : String := ""
  /-- Name of the arm in the title element `final:`: `grind`, `grind args`,
  `catcrypt_auto?`, `grind? +suggestions` or `try?`. -/
  arm : String := text
  /-- The failure is final: the arm run as in the outer tool's scratch run (module
  docstring, "Final failures") fails as well. `false` on success. -/
  final : Bool := false
  /-- Why the failure is final or not; empty on success. -/
  finality : String := ""
  /-- Milliseconds waited for the library-suggestion index before the arm ran. -/
  waitMs : Nat := 0

/-- Kernel check of `value : type of g`, closed over the local context of `g`. The check
stops when `cancelTk?` is set. -/
def kernelCheck (g : MVarId) (value : Expr) (hb : Nat) (declName? : Option Name)
    (cancelTk? : Option IO.CancelToken := none) : MetaM (Option String) := g.withContext do
  let fvars := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.toExpr
  let type ← instantiateMVars (← mkForallFVars fvars (← instantiateMVars (← g.getType)))
  let val ← instantiateMVars (← mkLambdaFVars fvars value)
  if type.hasMVar || val.hasMVar then return some "metavariables remain in the proof"
  if val.hasSorry then return some "the proof uses sorry"
  let lps := (collectLevelParams (collectLevelParams {} type) val).params
  let name := (declName?.getD .anonymous) ++ `_repairAction_check
  let decl := Declaration.thmDecl { name, levelParams := lps.toList, type, value := val }
  let maxRec := (← readThe Core.Context).maxRecDepth
  match (← getEnv).addDeclCore (hb * 1000).toUSize maxRec.toUSize decl cancelTk? with
  | .ok _ => return none
  | .error e => return some s!"kernel: {← (e.toMessageData (← getOptions)).toString}"

/-- First line of `s`, at most `n` characters. -/
def shorten (s : String) (n : Nat := 80) : String :=
  let l := (s.splitOn "\n").headD ""
  if l.length ≤ n then l else (l.take n).toString ++ "…"

/-- `x`, with every exception of `x`, including an interrupt, passed to `h`. -/
def catchAllCore {α : Type} (x : CoreM α) (h : Exception → CoreM α) : CoreM α :=
  fun ctx s => (x ctx s).tryCatch (fun e => h e ctx s)

/-- `catchAllCore` lifted to `MetaM`. -/
def catchAll {α : Type} (x : MetaM α) (h : Exception → MetaM α) : MetaM α :=
  controlAt CoreM fun run => catchAllCore (run x) (fun e => run (h e))

/-- The prefix of the names of the auxiliary declarations that an arm adds. -/
def auxPrefix (declName? : Option Name) : Name :=
  (declName?.getD .anonymous) ++ `_repairAction

/-- Waits until `t` has finished or the time `deadline` (of `IO.monoMsNow`) has come, polling
every 2 ms; `true` when `t` has finished. -/
partial def waitUntil {α : Type} (t : Task α) (deadline : Nat) : IO Bool := do
  if ← IO.hasFinished t then return true
  if (← IO.monoMsNow) ≥ deadline then return false
  IO.sleep 2
  waitUntil t deadline

/-- The outcome of a run under `capped`. -/
structure Capped (α : Type) where
  /-- The value, or the failure reason. -/
  res : Except String α
  /-- Time waited for the run, in milliseconds. -/
  ms : Nat
  /-- The cap that the run reached (`heartbeat cap`, `wall-clock cap`), `none` when it
  reached neither. -/
  cap? : Option String := none

/-- `x` in a task of its own, on a copy of the state, under the heartbeat cap `hb` and a
cancellation token, with the auxiliary declarations named under `auxPrefix declName?`. The
caller waits for the task until `ms` milliseconds have passed; then it sets the token and
returns without waiting further, since a tactic (`try?`, the library-suggestion selector)
can run on for a while after the token is set. The state of the caller is not changed. An
exception of `x` becomes its failure reason. Returns the outcome, the time waited and the
cap reached: the wall-clock cap when the task had not finished at the deadline or was
interrupted, the heartbeat cap when the task threw the heartbeat exception or used at least
`hb` thousand heartbeats (a tactic such as `grind` can catch the exception and fail for
another reason). Heartbeats are counted per thread, and the task has a thread of its own. -/
def capped {α : Type} (hb ms : Nat) (declName? : Option Name)
    (x : IO.CancelToken → MetaM (Except String α)) : MetaM (Capped α) := do
  let t0 ← IO.monoMsNow
  let tk ← IO.CancelToken.new
  let mctx ← readThe Meta.Context
  let mst ← getThe Meta.State
  let wall := s!"exceeded the cap of {ms} ms"
  let body : CoreM (Capped α) := do
    let h0 ← IO.getNumHeartbeats
    let spent : CoreM Bool := return hb != 0 && (← IO.getNumHeartbeats) - h0 ≥ hb * 1000
    catchAllCore
      (do
        let r ← withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) <|
          withCurrHeartbeats <| withDeclNameForAuxNaming (auxPrefix declName?) <|
            (x tk).run' mctx mst
        return { res := r, ms := 0, cap? := if ← spent then some "heartbeat cap" else none })
      (fun e => do
        if e.isInterrupt then return { res := .error wall, ms := 0, cap? := some "wall-clock cap" }
        let cap? := if e.isMaxHeartbeat || (← spent) then some "heartbeat cap" else none
        return { res := .error (shorten (← e.toMessageData.toString)), ms := 0, cap? })
  let act ← Core.wrapAsync (fun (_ : Unit) => body) (some tk)
  let task ← EIO.asTask (act ()) (prio := .dedicated)
  let r ← if ← waitUntil task (t0 + ms) then
      match task.get with
      | .ok r => pure r
      | .error e => pure { res := .error (shorten (← e.toMessageData.toString)), ms := 0 }
    else
      tk.set
      pure { res := .error wall, ms := 0, cap? := some "wall-clock cap" }
  return { r with ms := (← IO.monoMsNow) - t0 }

/-- Finality of a failure that reached the cap `cap?`: not final at a cap, since the scratch
run has no wall-clock cap and its own heartbeat limit; otherwise final when `final`, with the
reason `why`. -/
def finalityAt (cap? : Option String) (final : Bool) (why : String) : Bool × String :=
  match cap? with
  | some c => (false, s!"not final: stopped at the {c}")
  | none => (final, why)

/-- Runs the tactic `stx` on `g` and checks the proof in the kernel, the check under the
cancellation token `tk`. -/
def closeWith (g : MVarId) (stx : Syntax) (hb : Nat) (declName? : Option Name)
    (tk : IO.CancelToken) : MetaM (Except String Unit) := do
  let gs ← (Tactic.run g (Tactic.evalTactic stx)).run'
    { declName? := declName?, errToSorry := false }
  unless gs.isEmpty do return .error s!"{gs.length} goals remain"
  match ← kernelCheck g (← instantiateMVars (mkMVar g)) hb declName? (some tk) with
  | some m => return .error m
  | none => return .ok ()

/-- Runs the tactic `text` (the arm named `arm`) on `g`, then checks the proof in the kernel,
under `capped` with the heartbeat cap `hb` and the wall-clock cap `ms`. The wall-clock cap
bounds a run of `grind` that does not reach the heartbeat check. A failure is final when it
reached neither cap: the tactic and the goal are those of the scratch run, and the heartbeat
cap that it did not reach bounds the run as `maxHeartbeats` does there. The state of the
caller is not changed. -/
def runArm (g : MVarId) (text arm : String) (hb ms : Nat) (declName? : Option Name) :
    MetaM ArmResult := do
  let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
    | .ok stx => pure stx
    | .error e => return { text, arm, closed := false, ms := 0, msg := s!"parse: {e}",
                           final := true, finality := "final: the arm does not parse" }
  let c ← capped hb ms declName? (closeWith g stx hb declName?)
  match c.res with
  | .ok () => return { text, arm, closed := true, ms := c.ms, msg := "" }
  | .error m =>
    let (final, finality) := finalityAt c.cap? true "final: no cap reached"
    return { text, arm, closed := false, ms := c.ms, msg := m, final, finality }

/-- `stx` with every node and token given the synthetic source range `r`. -/
partial def atRange (r : Syntax.Range) : Syntax → Syntax
  | .node _ k args => .node (.synthetic r.start r.stop) k (args.map (atRange r))
  | .atom _ v => .atom (.synthetic r.start r.stop) v
  | .ident _ raw n pre => .ident (.synthetic r.start r.stop) raw n pre
  | .missing => .missing

/-- The `TryThisInfo` nodes of `t`, in order, with the source range of their syntax. -/
partial def suggestionsOf (t : InfoTree) (acc : Array (Option Syntax.Range × String) := #[]) :
    Array (Option Syntax.Range × String) :=
  match t with
  | .context _ t => suggestionsOf t acc
  | .node i cs =>
    let acc := match i with
      | .ofCustomInfo ci =>
        match ci.value.get? Tactic.TryThis.TryThisInfo with
        | some tti => acc.push (ci.stx.getRange?, tti.edit.newText)
        | none => acc
      | _ => acc
    cs.foldl (fun a c => suggestionsOf c a) acc
  | .hole _ => acc

/-- The replacement text of the last `TryThisInfo` node of `trees`. -/
def lastSuggestion (trees : PersistentArray InfoTree) : Option String :=
  (trees.foldl (fun a t => suggestionsOf t a) #[]).back?.map (·.2)

/-- The first suggestion of the last "Try this" message in `trees`: the first `TryThisInfo`
node among the last ones sharing the source range of the last one. -/
def firstOfLastSuggestions (trees : PersistentArray InfoTree) : Option String := Id.run do
  let ss := trees.foldl (fun a t => suggestionsOf t a) #[]
  let some (r, _) := ss.back? | return none
  let sameRange (r' : Option Syntax.Range) : Bool := match r, r' with
    | some a, some b => Syntax.Range.same a b
    | none, none => true
    | _, _ => false
  let mut i := ss.size - 1
  while i > 0 && sameRange ss[i - 1]!.1 do i := i - 1
  return ss[i]?.map (·.2)

/-- `stx` contains the placeholder token for a missing proof, as a tactic or a term. -/
partial def hasSorryToken : Syntax → Bool
  | .atom _ v => v == "sorry"
  | .node _ _ args => args.any hasSorryToken
  | _ => false

/-! ## The arm `catcrypt_auto?` -/

/-- The tactic text of the dispatcher arm. -/
def dispatchText : String := "catcrypt_auto?"

/-- The tactic `catcrypt_auto?` parses in `env`. -/
def dispatchAvailable (env : Environment) : Bool :=
  (Parser.runParserCategory env `tactic dispatchText).toOption.isSome

/-- The options `opts` with the total and per-arm wall-clock budgets of `catcrypt_auto` cut
to `ms` milliseconds (a budget of `0`, none, becomes `ms`). -/
def capOptions (opts : Options) (ms : Nat) : Options :=
  let cut (n : Name) (o : Options) : Options :=
    let v := o.get n ms
    o.set n (if v == 0 then ms else min v ms)
  cut `catcrypt_auto.maxMillis (cut `catcrypt_auto.totalMillis opts)

/-- The goal shape named by an error of `catcrypt_auto` (`goal shape S; …`), or empty. -/
def shapeOfError (msg : String) : String :=
  match msg.splitOn "goal shape " with
  | _ :: rest :: _ => ((rest.splitOn ";").headD "").trimAscii.toString
  | _ => ""

/-- The error `m` of `catcrypt_auto` reports that a wall-clock budget of the dispatcher ran
out: an arm or step "exceeded the time budget", or "the total time budget of N ms is
spent". These are the only budgets that `capOptions` cuts; the heartbeat budgets of the
dispatcher are its own in the scratch run as well. -/
def reportsBudgetOut (m : String) : Bool :=
  (m.splitOn "exceeded the time budget").length > 1 ||
    ((m.splitOn "total time budget of").length > 1 && (m.splitOn "ms is spent").length > 1)

/-- The key, in the options of a run of the arm `catcrypt_auto?`, of the number of that run
(`dispatchRunCounter`), which `offSelector` reads. -/
def dispatchRunKey : Name := `repairAction.dispatchRun

/-- The number of the last run of the arm `catcrypt_auto?` in this process. -/
initialize dispatchRunCounter : IO.Ref Nat ← IO.mkRef 0

/-- The numbers of the runs of the arm `catcrypt_auto?` in which the dispatcher called the
library-suggestion selector. -/
initialize consultedRuns : IO.Ref (Array Nat) ← IO.mkRef #[]

/-- The library-suggestion selector of the arm `catcrypt_auto?` when
`repairAction.dispatchSuggestions` is false: records that the run (`dispatchRunKey`)
consulted library suggestions and fails, so that an arm `grind +suggestions` of the
dispatcher fails at once. -/
def offSelector : LibrarySuggestions.Selector := fun _ _ => do
  let n := (← getOptions).get dispatchRunKey (0 : Nat)
  consultedRuns.modify (·.push n)
  throwError "library suggestions are off in the repair action"

/-- Runs `catcrypt_auto?` on `g` under the dispatcher's budgets cut to `ms` milliseconds,
then checks the proof in the kernel, under `capped` with the heartbeat cap `hb` and the
wall-clock cap `ms`. The syntax of the run carries the source range `r`. Unless
`repairAction.dispatchSuggestions` is set, the library-suggestion selector of the run is
`offSelector`. On a failure the goal shape that the dispatcher's error names is kept, and
the failure is final when the run reached neither cap, the dispatcher's error reports no
budget that ran out (`reportsBudgetOut`), and the dispatcher did not consult the selector
`offSelector` (each of these differs from the scratch run, where the dispatcher runs under
its own budgets with the registered selector). The state of the caller is not changed. -/
def runDispatch (g : MVarId) (r : Syntax.Range) (hb ms : Nat) (declName? : Option Name) :
    MetaM ArmResult := do
  let some stx := (Parser.runParserCategory (← getEnv) `tactic dispatchText).toOption
    | return { text := "catcrypt_auto", arm := dispatchText, closed := false, ms := 0,
               msg := "catcrypt_auto? is not in the environment", final := true,
               finality := "final: catcrypt_auto? is not in the environment" }
  let stx := atRange r stx
  let shape ← IO.mkRef ""
  let budgetOut ← IO.mkRef false
  let run ← dispatchRunCounter.modifyGet fun n => (n + 1, n + 1)
  let off := !(← getOptions).get `repairAction.dispatchSuggestions false
  let opts := (capOptions (← getOptions) ms).set dispatchRunKey run
  let c ← capped hb ms declName? fun tk =>
    withTheReader Core.Context (fun c => { c with options := opts }) do
      modifyThe Core.State fun s => { s with infoState := { enabled := true } }
      if off then
        modifyEnv fun env => LibrarySuggestions.librarySuggestionsExt.modifyState env
          fun _ => some ``offSelector
      let r ← catchAll (closeWith g stx hb declName? tk) fun e => do
        if e.isInterrupt then throw e
        let m ← e.toMessageData.toString
        shape.set (shapeOfError m)
        budgetOut.set (reportsBudgetOut m)
        return .error (shorten m)
      let trees := (← getThe Core.State).infoState.trees
      return r.map fun () => lastSuggestion trees
  let shape ← shape.get
  let consulted := (← consultedRuns.get).contains run
  consultedRuns.modify (·.filter (· != run))
  match c.res with
  | .ok s => return { text := s.getD "catcrypt_auto", arm := dispatchText, closed := true,
                      ms := c.ms, msg := "" }
  | .error m =>
    let why := (if ← budgetOut.get then #["a budget of the dispatcher ran out"] else #[]) ++
      (if consulted then #["the dispatcher consulted the library suggestions, which are off"]
       else #[])
    let (final, finality) := finalityAt c.cap? why.isEmpty <|
      if why.isEmpty then "final: no cap reached, no budget ran out, no library suggestion \
        consulted"
      else s!"not final: {", ".intercalate why.toList}"
    return { text := "catcrypt_auto", arm := dispatchText, closed := false, ms := c.ms,
             msg := m, shape, final, finality }

/-! ## The suggestion arms -/

/-- The background task that builds the library-suggestion index of this process, once
started, with its start time (of `IO.monoMsNow`). -/
initialize suggestionIndexTask : IO.Ref (Option (Task (Except Exception Unit) × Nat)) ←
  IO.mkRef none

/-- The library-suggestion index of this process is built. Otherwise, unless
`repairAction.suggestionIndex` is false, a background task building it is started (when
none runs) by running the registered selector on `g` with no heartbeat cap and no token. -/
def suggestionIndexReady (g : MVarId) : MetaM Bool := do
  if let some (t, _) ← suggestionIndexTask.get then
    unless ← IO.hasFinished t do return false
    if t.get matches .ok _ then return true
    suggestionIndexTask.set none
  unless (← getOptions).get `repairAction.suggestionIndex true do return false
  if (LibrarySuggestions.librarySuggestionsExt.getState (← getEnv)).isNone then return false
  let mctx ← getMCtx
  let lctx ← getLCtx
  let act ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) <|
    Core.wrapAsync (fun (_ : Unit) => (do
      setMCtx mctx
      withLCtx lctx {} (discard <| LibrarySuggestions.select g) : MetaM Unit).run') none
  suggestionIndexTask.set (some (← EIO.asTask (act ()) (prio := .dedicated), ← IO.monoMsNow))
  return false

/-- `suggestionIndexReady g`, and while the build of the index runs, a wait for it until
`waitMs` milliseconds after the start of the build. The bound counts from the start of the
build, not of the call, so that the arms and leaves after a wait that ended without the
index do not wait again. A build that ends with an error is not restarted here. Returns
whether the index is built and the milliseconds waited; no wait when
`repairAction.suggestionIndex` is false. -/
def awaitSuggestionIndex (g : MVarId) (waitMs : Nat) : MetaM (Bool × Nat) := do
  if ← suggestionIndexReady g then return (true, 0)
  unless (← getOptions).get `repairAction.suggestionIndex true do return (false, 0)
  let some (t, start) ← suggestionIndexTask.get | return (false, 0)
  let t0 ← IO.monoMsNow
  let done ← waitUntil t (start + waitMs)
  return (done && t.get matches .ok _, (← IO.monoMsNow) - t0)

/-- Runs the suggestion arm `text` on `g` under `capped` with the heartbeat cap `hb` and the
wall-clock cap `ms`: the arm, then its suggestion (`firstOfLastSuggestions`) alone on `g`,
then the kernel check of that proof. The syntax of the arm carries the source range `r`, so
that its suggestion is laid out for that range. Before the arm, while the build of the
library-suggestion index runs, the arm waits for it (`awaitSuggestionIndex`, bounded by
`repairAction.indexWaitMillis`); the wait is outside the caps. The selector is the
registered one when its index is built, and `LibrarySuggestions.currentFile` otherwise, and
the failure reason then says `index not built`. A failure is final when the run reached
neither cap and the selector was the registered one with its index: the selector, its
premises, the tactic and the goal are then those of the scratch run. The state of the caller
is not changed. -/
def runSuggestionArm (g : MVarId) (text : String) (r : Syntax.Range) (hb ms : Nat)
    (declName? : Option Name) : MetaM ArmResult := do
  let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
    | .ok stx => pure (atRange r stx)
    | .error e => return { text, closed := false, ms := 0, msg := s!"parse: {e}",
                           final := true, finality := "final: the arm does not parse" }
  let waitMs := (← getOptions).get `repairAction.indexWaitMillis indexWaitDefault
  let (ready, waited) ← g.withContext (awaitSuggestionIndex g waitMs)
  let c ← capped hb ms declName? fun tk => do
    unless ready do
      modifyEnv fun env => LibrarySuggestions.librarySuggestionsExt.modifyState env
        fun _ => some ``LibrarySuggestions.currentFile
    let saved ← saveState
    modifyThe Core.State fun s => { s with infoState := { enabled := true } }
    let gs ← (Tactic.run g (Tactic.evalTactic stx)).run'
      { declName? := declName?, errToSorry := false }
    unless gs.isEmpty do return .error s!"{gs.length} goals remain"
    let some sugg := firstOfLastSuggestions (← getThe Core.State).infoState.trees
      | return .error "no suggestion"
    saved.restore
    let .ok sstx := Parser.runParserCategory (← getEnv) `tactic sugg
      | return .error s!"the suggestion {shorten (squash sugg) 40} is not one tactic"
    if hasSorryToken sstx then
      return .error s!"the suggestion {shorten (squash sugg) 40} has sorry"
    return (← closeWith g sstx hb declName? tk).map fun () => sugg
  match c.res with
  | .ok s => return { text := s, arm := text, closed := true, ms := c.ms, msg := "",
                      waitMs := waited }
  | .error m =>
    let (final, finality) := finalityAt c.cap? ready <|
      if ready then "final: no cap reached, the registered selector with its index"
      else "not final: the index was not built, the arm ran with the theorems of the file"
    let msg := if ready then m else s!"{m}; index not built"
    return { text, closed := false, ms := c.ms, msg, final, finality, waitMs := waited }

/-! ## The arms at a leaf -/

/-- Runs the arms of the module docstring on `g` in order, stopping at the first closing arm.
The arguments of `grind [args]` are taken from the tactics `stxs` and
`repairAction.extraNames`; `r` is the edit range. The options are those of the context. -/
def repairGoal (g : MVarId) (stxs : Array Syntax) (r : Syntax.Range) (declName? : Option Name) :
    MetaM (Array ArmResult) := do
  let opts ← getOptions
  let hb := opts.get `repairAction.maxHeartbeats (100000 : Nat)
  let args ← grindArgs g stxs (extraNames opts)
  let mut arms := #[("grind", "grind")]
  unless args.isEmpty do
    arms := arms.push (s!"grind [{", ".intercalate args.toList}]", "grind args")
  let mut out := #[]
  let gms := opts.get `repairAction.grindMillis (600 : Nat)
  for (a, name) in arms do
    let res ← runArm g a name hb gms declName?
    out := out.push res
    if res.closed then return out
  if dispatchAvailable (← getEnv) then
    let res ← runDispatch g r hb (opts.get `repairAction.dispatchMillis (1000 : Nat)) declName?
    out := out.push res
    if res.closed then return out
  let suggestionArms : List (String × Nat) :=
    [("grind? +suggestions", opts.get `repairAction.grindSuggestionsMillis (1000 : Nat)),
     ("try?", opts.get `repairAction.tryMillis (2000 : Nat))]
  for (a, ms) in suggestionArms do
    let res ← runSuggestionArm g a r hb ms declName?
    out := out.push res
    if res.closed then return out
  return out

/-- The head symbol of the type of `g`: the head constant, the user name of the head local,
`∀` or `→` for a binder, or the kind of the term. -/
def goalHead (g : MVarId) : MetaM String := g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  match t with
  | .forallE _ _ b _ => return if b.hasLooseBVars then "∀" else "→"
  | _ =>
    match t.getAppFn with
    | .const c _ => return toString c
    | .fvar f => return toString (← f.getUserName)
    | .sort _ => return "Sort"
    | .lam .. => return "fun"
    | .mvar _ => return "?"
    | _ => return t.getAppFn.ctorName

/-- `text` parses, at the column `col`, to a tactic with the structure of `stx`. -/
def parsesAs (env : Environment) (text : String) (col : Nat) (stx : Syntax) : Bool :=
  match Parser.runParserCategory env `tactic ("".pushn ' ' col ++ text) with
  | .ok t => t.structEq stx
  | .error _ => false

/-- The tactic text `text` laid out to be inserted at the column `col`: a text of one line as
it is; else the text on one line when that parses to the same tactic, else the tactic
pretty-printed for the column `col` when that parses at `col` to the same tactic, else
`text`. A suggestion is laid out for the column of the syntax that made it, which differs from
`col` when the edit range starts after other tactics on its line. -/
def layoutAt (text : String) (col : Nat) : MetaM String := do
  unless text.contains '\n' do return text
  let env ← getEnv
  let .ok stx := Parser.runParserCategory env `tactic text | return text
  let flat := squash text
  if parsesAs env flat col stx then return flat
  let laid := (← PrettyPrinter.ppTactic ⟨stx⟩).pretty (indent := col) (column := col)
  if parsesAs env laid col stx then return laid
  return text

/-- What the action reports at a leaf: the head symbol of its goal, its edit span or the
reason that there is none, and the arms. -/
structure LeafReport where
  /-- Head symbol of the goal (`goalHead`). -/
  head : String
  /-- The edit span, or why there is none. -/
  span : Except String EditSpan
  /-- The arms that ran. -/
  arms : Array ArmResult

/-- `repairGoal` on the main goal before the leaf `l`, in the context and with the options
recorded at the leaf, over the edit span that `editSpan` computes from the tactic nodes
`ss`; no arm runs when there is no edit span. The text of a closing arm is laid out
(`layoutAt`) for the column `col` of the start of the edit span. -/
def repairLeaf (ss : Array Step) (l : Leaf) (col : String.Pos.Raw → Nat) :
    IO (Option LeafReport) := do
  let some g := l.info.goalsBefore.head? | return none
  let some decl := l.info.mctxBefore.findDecl? g | return none
  let ctx := { l.ctx with mctx := l.info.mctxBefore }
  let span := editSpan ss l.range g
  ctx.runMetaM decl.lctx do
    let head ← goalHead g
    match span with
    | .error _ => return some { head, span, arms := #[] }
    | .ok s =>
      let arms ← repairGoal g s.tactics s.range ctx.parentDecl?
      let arms ← arms.mapM fun r => do
        if r.closed then return { r with text := ← layoutAt r.text (col s.range.start) }
        return r
      return some { head, span, arms }

/-- The bracketed tag of a title: the head symbol of the goal, the reported goal shape and,
when no arm closed, the names of the arms whose failure is final (`final: A; B`, the
element left out when there are none). -/
def goalTag (head : String) (rs : Array ArmResult) : String :=
  let shape := match rs.find? (!·.shape.isEmpty) with
    | some r => s!", shape {r.shape}"
    | none => ""
  let finals := (rs.filter fun r => !r.closed && r.final).map (·.arm)
  let final := if finals.isEmpty || rs.any (·.closed) then ""
    else s!", final: {"; ".intercalate finals.toList}"
  s!"[head {head}{shape}{final}]"

/-- The code action reporting `rep` at a leaf on line `line`; `text` converts source ranges. -/
def mkAction (docId : VersionedTextDocumentIdentifier) (text : FileMap) (line : Nat)
    (rep : LeafReport) : CodeAction :=
  let tag := goalTag rep.head rep.arms
  match rep.span, rep.arms.find? (·.closed) with
  | .error why, _ =>
    { title := s!"Repair line {line} {tag}: no closure offered, {why}", kind? := "quickfix" }
  | .ok s, some r =>
    { title := s!"Repair line {line} {tag}: {shorten r.text} (kernel-checked, {r.ms} ms)"
      kind? := "quickfix"
      edit? := some <| .ofTextEdit docId
        { range := text.utf8RangeToLspRange s.range, newText := r.text } }
  | .ok _, none =>
    let arms := rep.arms.map fun r => s!"{r.text} {r.ms} ms ({r.msg})"
    { title := s!"Repair line {line} {tag}: no closing arm; {"; ".intercalate arms.toList}"
      kind? := "quickfix" }

/-- Grind repair code action at the leaves selected by the request range. -/
@[code_action_provider]
def grindRepairProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let lo := text.lspPosToUtf8Pos params.range.start
  let hi := text.lspPosToUtf8Pos params.range.end
  let leaves := (minimalLeaves (collectLeaves snap.infoTree lo hi)).extract 0 3
  let eager := params.range.start != params.range.end
  let ss := steps snap.infoTree
  leaves.filterMapM fun l => do
    let line := (text.utf8RangeToLspRange l.range).start.line + 1
    let compute : IO (Option CodeAction) := do
      let col (p : String.Pos.Raw) := (text.toPosition p).column
      return (← repairLeaf ss l col).map (mkAction doc.versionedIdentifier text line)
    if eager then
      return (← compute).map fun a => { eager := a }
    else
      let empty : CodeAction := { title := s!"Repair line {line}: no goal", kind? := "quickfix" }
      return some { eager := { title := s!"Repair line {line} with grind, catcrypt_auto or try?",
                               kind? := "quickfix" }
                    lazy? := some do return (← compute).getD empty }

end CatCryptCore.RepairAction

end

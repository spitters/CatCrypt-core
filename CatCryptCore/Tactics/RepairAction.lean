/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Lean

/-!
# Grind repair code action

A code action provider that, at a tactic leaf selected by the request range, runs `grind`
and then `grind [names]` on the goal recorded in the info tree of the elaborated file. The
goal is taken from `TacticInfo.goalsBefore` and its metavariable context `mctxBefore`, so no
part of the file is elaborated again; each arm runs under the heartbeat cap
`repairAction.maxHeartbeats`, and a proof it produces is closed over its local context and
checked by the kernel before the arm counts as closing.

* A leaf is a tactic node with an original source range, other than a tactic sequence, that
  lies inside the request range or contains it, and that contains no other such node.
  At most three leaves are treated per request.
* `names` are the identifiers in the leaf's syntax that resolve to global constants and are
  not local hypotheses of the goal, followed by the names in the option
  `repairAction.extraNames` (separated by spaces or commas).
* On a closing arm the action replaces the leaf by the arm's text. When no arm closes, the
  action has no edit and its title lists each arm with its time and outcome.
* The options are read from the options in force at the leaf (`set_option` above the
  declaration), by name, with defaults 100000 heartbeats and no extra names.
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
    repair code action and for its kernel check"
}

register_option repairAction.extraNames : String := {
  defValue := ""
  descr := "names, separated by spaces or commas, added to the `grind [names]` arm of the \
    grind repair code action"
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

/-- Tactic nodes with an original range inside `[lo, hi]` or containing it, with a goal. -/
def collectLeaves (t : InfoTree) (lo hi : String.Pos.Raw) : Array Leaf :=
  t.foldInfo (init := #[]) fun ctx info acc => Id.run do
    let .ofTacticInfo ti := info | acc
    if sequenceKinds.contains ti.stx.getKind then return acc
    if ti.goalsBefore.isEmpty then return acc
    let some r := ti.stx.getRange? (canonicalOnly := true) | acc
    let inside := lo ≤ r.start && r.stop ≤ hi
    let covers := r.start ≤ lo && hi ≤ r.stop
    unless inside || covers do return acc
    acc.push { ctx, info := ti, range := r }

/-- `r` lies inside `s` and differs from it. -/
def Syntax.Range.strictlyInside (r s : Syntax.Range) : Bool :=
  s.start ≤ r.start && r.stop ≤ s.stop && (s.start != r.start || s.stop != r.stop)

/-- The leaves containing no other leaf, the first of each source range only. -/
def minimalLeaves (ls : Array Leaf) : Array Leaf := Id.run do
  let mut out : Array Leaf := #[]
  for l in ls do
    if ls.any (fun m => Syntax.Range.strictlyInside m.range l.range) then continue
    if out.any (fun m => m.range.start == l.range.start && m.range.stop == l.range.stop) then
      continue
    out := out.push l
  return out

/-- Identifiers occurring in `stx`, without repetition, in order of occurrence. -/
partial def identsOf (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  match stx with
  | .ident _ _ n _ => if acc.contains n then acc else acc.push n
  | .node _ _ args => args.foldl (fun a s => identsOf s a) acc
  | _ => acc

/-- Identifiers of `stx` that resolve to a global constant and are not local hypotheses. -/
def leafNames (g : MVarId) (stx : Syntax) : MetaM (Array Name) := g.withContext do
  let lctx ← getLCtx
  (identsOf stx).filterM fun n => do
    if (lctx.findFromUserName? n).isSome then return false
    return (← resolveGlobalName n).any (·.2.isEmpty)

/-- Names of `repairAction.extraNames`. -/
def extraNames (opts : Options) : Array Name :=
  ((opts.get `repairAction.extraNames "").replace "," " ").splitOn " "
    |>.filter (!·.isEmpty) |>.map String.toName |>.toArray

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

/-- Kernel check of `value : type of g`, closed over the local context of `g`. -/
def kernelCheck (g : MVarId) (value : Expr) (hb : Nat) (declName? : Option Name) :
    MetaM (Option String) := g.withContext do
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
  match (← getEnv).addDeclCore (hb * 1000).toUSize maxRec.toUSize decl none with
  | .ok _ => return none
  | .error e => return some s!"kernel: {← (e.toMessageData (← getOptions)).toString}"

/-- First line of `s`, at most `n` characters. -/
def shorten (s : String) (n : Nat := 80) : String :=
  let l := (s.splitOn "\n").headD ""
  if l.length ≤ n then l else (l.take n).toString ++ "…"

/-- Runs the tactic `text` on `g` under the cap `hb`, then checks the proof in the kernel.
The metavariable and environment state is restored afterwards. -/
def runArm (g : MVarId) (text : String) (hb : Nat) (declName? : Option Name) :
    MetaM ArmResult := do
  let t0 ← IO.monoMsNow
  let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
    | .ok stx => pure stx
    | .error e => return { text, closed := false, ms := 0, msg := s!"parse: {e}" }
  let saved ← saveState
  let msg ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) <|
      withCurrHeartbeats do
        let gs ← (Tactic.run g (Tactic.evalTactic stx)).run'
          { declName? := declName?, errToSorry := false }
        unless gs.isEmpty do return some s!"{gs.length} goals remain"
        kernelCheck g (← instantiateMVars (mkMVar g)) hb declName?)
    (fun e => return some (shorten (← e.toMessageData.toString)))
  saved.restore
  let ms := (← IO.monoMsNow) - t0
  return { text, closed := msg.isNone, ms, msg := msg.getD "" }

/-- Runs the arms `grind`, then `grind [names]` when there are names, on the main goal
before the leaf, stopping at the first closing arm. -/
def repairLeaf (l : Leaf) : IO (Array ArmResult) := do
  let some g := l.info.goalsBefore.head? | return #[]
  let some decl := l.info.mctxBefore.findDecl? g | return #[]
  let ctx := { l.ctx with mctx := l.info.mctxBefore }
  ctx.runMetaM decl.lctx do
    let hb := ctx.options.get `repairAction.maxHeartbeats (100000 : Nat)
    let mut names := #[]
    for n in (← leafNames g l.info.stx) ++ extraNames ctx.options do
      unless names.contains n do names := names.push n
    let mut arms := #["grind"]
    unless names.isEmpty do
      arms := arms.push s!"grind [{", ".intercalate (names.map toString).toList}]"
    let mut out := #[]
    for a in arms do
      let r ← runArm g a hb ctx.parentDecl?
      out := out.push r
      if r.closed then break
    return out

/-- The code action reporting the arms `rs` at the leaf spanning `range`. -/
def mkAction (docId : VersionedTextDocumentIdentifier) (line : Nat) (range : Lsp.Range)
    (rs : Array ArmResult) : CodeAction :=
  match rs.find? (·.closed) with
  | some r =>
    { title := s!"Repair line {line}: {r.text} (kernel-checked, {r.ms} ms)"
      kind? := "quickfix"
      edit? := some <| .ofTextEdit docId { range, newText := r.text } }
  | none =>
    let arms := rs.map fun r => s!"{r.text} {r.ms} ms ({r.msg})"
    { title := s!"Repair line {line}: no closing arm; {"; ".intercalate arms.toList}"
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
  leaves.mapM fun l => do
    let range := text.utf8RangeToLspRange l.range
    let line := range.start.line + 1
    let compute : IO CodeAction := do
      return mkAction doc.versionedIdentifier line range (← repairLeaf l)
    if eager then
      return { eager := ← compute }
    else
      return { eager := { title := s!"Repair line {line} with grind", kind? := "quickfix" }
               lazy? := some compute }

end CatCryptCore.RepairAction

end

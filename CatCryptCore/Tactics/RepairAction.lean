/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Lean

/-!
# Grind repair code action

A code action provider that, at a tactic leaf selected by the request range, runs `grind`,
then `grind [names]`, then `catcrypt_auto?` on the goal recorded in the info tree of the
elaborated file, and stops at the first closing arm. The goal is taken from
`TacticInfo.goalsBefore` and its metavariable context `mctxBefore`, so no part of the file
is elaborated again; each arm runs under the heartbeat cap `repairAction.maxHeartbeats`,
and a proof it produces is closed over its local context and checked by the kernel before
the arm counts as closing. The arms `grind` and `grind [names]`, kernel check included, also
run under a cancellation token set at the cap `repairAction.grindMillis`, since a run of
`grind` can exceed any heartbeat cap.

* A leaf is a tactic node with an original source range, other than a tactic sequence, that
  lies inside the request range or contains it, and that contains no other such node.
  At most three leaves are treated per request.
* `names` are the identifiers in the leaf's syntax that resolve to global constants and are
  not local hypotheses of the goal, followed by the names in the option
  `repairAction.extraNames` (separated by spaces or commas).
* The arm `catcrypt_auto?` runs when that tactic parses in the environment of the leaf
  (`dispatchAvailable`); the module names no constant of the dispatcher. It runs under the
  dispatcher's own budgets (`catcrypt_auto.maxHeartbeats` per arm of the dispatcher), with
  `catcrypt_auto.totalMillis` and `catcrypt_auto.maxMillis` cut to the cap
  `repairAction.dispatchMillis`, and the whole arm, kernel check included, runs under a
  cancellation token set at that cap.
* Unless `repairAction.dispatchSuggestions` is set, the arm `catcrypt_auto?` runs with no
  library-suggestion selector in its environment, so that the arms `grind +suggestions` of
  the dispatcher fail at once and the selector's index of the imported theorems, which is
  built on first use in a process and does not stop at the cancellation token, is not built.
* The text of the arm `catcrypt_auto?` is the suggestion it adds to the info tree (its last
  `TryThisInfo` node), and `catcrypt_auto` when there is none.
* On a closing arm the action replaces the leaf by the arm's text. When no arm closes, the
  action has no edit and its title lists each arm with its time and outcome.
* The options are read from the options in force at the leaf (`set_option` above the
  declaration), by name, with defaults 100000 heartbeats, no extra names, caps of 600 ms
  for each arm `grind` and for the arm `catcrypt_auto?`, and no library-suggestion selector.
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

register_option repairAction.dispatchMillis : Nat := {
  defValue := 600
  descr := "wall-clock cap, in milliseconds, of the `catcrypt_auto?` arm of the repair \
    code action"
}

register_option repairAction.grindMillis : Nat := {
  defValue := 600
  descr := "wall-clock cap, in milliseconds, of each arm `grind` and `grind [names]` of the \
    repair code action, kernel check included"
}

register_option repairAction.dispatchSuggestions : Bool := {
  defValue := false
  descr := "keep the library-suggestion selector in the `catcrypt_auto?` arm of the \
    repair code action"
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

/-- Sets `tk` at the time `deadline` (of `IO.monoMsNow`), polling every 5 ms, and returns
without setting it once `stop` is set. -/
partial def watch (tk stop : IO.CancelToken) (deadline : Nat) : IO Unit := do
  if ← stop.isSet then return
  if (← IO.monoMsNow) ≥ deadline then
    tk.set
    return
  IO.sleep 5
  watch tk stop deadline

/-- Runs the tactic `text` on `g` under the heartbeat cap `hb` and a cancellation token set
after `ms` milliseconds, then checks the proof in the kernel under the same token. The token
bounds a run of `grind` that does not reach the heartbeat check. The metavariable and
environment state is restored afterwards. -/
def runArm (g : MVarId) (text : String) (hb ms : Nat) (declName? : Option Name) :
    MetaM ArmResult := do
  let t0 ← IO.monoMsNow
  let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
    | .ok stx => pure stx
    | .error e => return { text, closed := false, ms := 0, msg := s!"parse: {e}" }
  let saved ← saveState
  let tk ← IO.CancelToken.new
  let stop ← IO.CancelToken.new
  let _ ← IO.asTask (prio := .dedicated) (watch tk stop (t0 + ms))
  let msg ← catchAll
    (withTheReader Core.Context
      (fun c => { c with cancelTk? := some tk, maxHeartbeats := hb * 1000 }) <|
      withCurrHeartbeats do
        let gs ← (Tactic.run g (Tactic.evalTactic stx)).run'
          { declName? := declName?, errToSorry := false }
        unless gs.isEmpty do return some s!"{gs.length} goals remain"
        kernelCheck g (← instantiateMVars (mkMVar g)) hb declName? (some tk))
    (fun e => do
      if e.isInterrupt then return some s!"exceeded the cap of {ms} ms"
      return some (shorten (← e.toMessageData.toString)))
  stop.set
  saved.restore
  let ms := (← IO.monoMsNow) - t0
  return { text, closed := msg.isNone, ms, msg := msg.getD "" }

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

/-- `stx` with every node and token given the synthetic source range `r`. -/
partial def atRange (r : Syntax.Range) : Syntax → Syntax
  | .node _ k args => .node (.synthetic r.start r.stop) k (args.map (atRange r))
  | .atom _ v => .atom (.synthetic r.start r.stop) v
  | .ident _ raw n pre => .ident (.synthetic r.start r.stop) raw n pre
  | .missing => .missing

/-- The replacement text of the last `TryThisInfo` node of `t`. -/
partial def lastSuggestion (t : InfoTree) (acc : Option String := none) : Option String :=
  match t with
  | .context _ t => lastSuggestion t acc
  | .node i cs =>
    let acc := match i with
      | .ofCustomInfo ci =>
        ((ci.value.get? Tactic.TryThis.TryThisInfo).map (·.edit.newText)).orElse fun _ => acc
      | _ => acc
    cs.foldl (fun a c => lastSuggestion c a) acc
  | .hole _ => acc

/-- Runs `catcrypt_auto?` on `g` under the dispatcher's budgets cut to `ms` milliseconds,
the heartbeat cap `hb` and a cancellation token set after `ms` milliseconds, then checks
the proof in the kernel under the same token. The syntax of the run carries the source
range `r`. The state is restored afterwards. -/
def runDispatch (g : MVarId) (r : Syntax.Range) (hb ms : Nat) (declName? : Option Name) :
    MetaM ArmResult := do
  let t0 ← IO.monoMsNow
  let some stx := (Parser.runParserCategory (← getEnv) `tactic dispatchText).toOption
    | return { text := "catcrypt_auto", closed := false, ms := 0,
               msg := "catcrypt_auto? is not in the environment" }
  let stx := atRange r stx
  let saved ← saveState
  let tk ← IO.CancelToken.new
  let stop ← IO.CancelToken.new
  let _ ← IO.asTask (prio := .dedicated) (watch tk stop (t0 + ms))
  let opts := capOptions (← getOptions) ms
  let res : Except String (Option String) ← catchAll
    (withTheReader Core.Context
      (fun c => { c with options := opts, cancelTk? := some tk, maxHeartbeats := hb * 1000 }) <|
      withCurrHeartbeats do
        modifyThe Core.State fun s => { s with infoState := { enabled := true } }
        unless (← getOptions).get `repairAction.dispatchSuggestions false do
          modifyEnv fun env =>
            LibrarySuggestions.librarySuggestionsExt.modifyState env fun _ => none
        let gs ← (Tactic.run g (Tactic.evalTactic stx)).run'
          { declName? := declName?, errToSorry := false }
        unless gs.isEmpty do return .error s!"{gs.length} goals remain"
        if let some m ← kernelCheck g (← instantiateMVars (mkMVar g)) hb declName? (some tk) then
          return .error m
        let trees := (← getThe Core.State).infoState.trees
        return .ok (trees.foldl (fun a t => lastSuggestion t a) none))
    (fun e => do
      if e.isInterrupt then return .error s!"exceeded the cap of {ms} ms"
      return .error (shorten (← e.toMessageData.toString)))
  stop.set
  saved.restore
  let dt := (← IO.monoMsNow) - t0
  match res with
  | .ok s => return { text := s.getD "catcrypt_auto", closed := true, ms := dt, msg := "" }
  | .error m => return { text := "catcrypt_auto", closed := false, ms := dt, msg := m }

/-! ## The arms at a leaf -/

/-- Runs the arms `grind`, `grind [names]` (when there are names) and, when the dispatcher
is in the environment, `catcrypt_auto?` on `g`, stopping at the first closing arm. `names`
are the global constants of `stx` and `repairAction.extraNames`; `r` is the source range of
the leaf. The options are those of the context. -/
def repairGoal (g : MVarId) (stx : Syntax) (r : Syntax.Range) (declName? : Option Name) :
    MetaM (Array ArmResult) := do
  let opts ← getOptions
  let hb := opts.get `repairAction.maxHeartbeats (100000 : Nat)
  let mut names := #[]
  for n in (← leafNames g stx) ++ extraNames opts do
    unless names.contains n do names := names.push n
  let mut arms := #["grind"]
  unless names.isEmpty do
    arms := arms.push s!"grind [{", ".intercalate (names.map toString).toList}]"
  let mut out := #[]
  let gms := opts.get `repairAction.grindMillis (600 : Nat)
  for a in arms do
    let res ← runArm g a hb gms declName?
    out := out.push res
    if res.closed then return out
  if dispatchAvailable (← getEnv) then
    out := out.push
      (← runDispatch g r hb (opts.get `repairAction.dispatchMillis (600 : Nat)) declName?)
  return out

/-- `repairGoal` on the main goal before the leaf `l`, in the context and with the options
recorded at the leaf. -/
def repairLeaf (l : Leaf) : IO (Array ArmResult) := do
  let some g := l.info.goalsBefore.head? | return #[]
  let some decl := l.info.mctxBefore.findDecl? g | return #[]
  let ctx := { l.ctx with mctx := l.info.mctxBefore }
  ctx.runMetaM decl.lctx (repairGoal g l.info.stx l.range ctx.parentDecl?)

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
      return { eager := { title := s!"Repair line {line} with grind or catcrypt_auto",
                          kind? := "quickfix" }
               lazy? := some compute }

end CatCryptCore.RepairAction

end

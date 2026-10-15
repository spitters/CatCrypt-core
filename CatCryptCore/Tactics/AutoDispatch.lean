/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Ring
public import CatCryptCore.Tactics.AutoSets
public import CatCryptCore.Tactics.BindVcgen
public import CatCryptCore.Tactics.Triangle
public import CatCryptCore.Tactics.AutoMetrics
public meta import CatCryptCore.Tactics.AutoArms

/-!
# Goal-shape dispatch over the automation sets

`catcrypt_auto` closes the main goal by reading its shape and running, in order,
the closers that apply to that shape. When the goal contains `>>=` it is first
rewritten by `simp only [SPComp.monad_bind_eq]`, so that `do` goals show their
head; the rewrite is kept only when it changes the goal. The shape is read from
the instantiated goal with its `set`/`let` variables replaced by their values
(`zetaReduce`) and, failing a match, from its `whnfR`.

| Shape | Detected head | Arms, in order |
|---|---|---|
| side condition | `SPComp.IsPure _`, `SPComp.NoFail _` | `aesop` over `CatCryptRel` |
| relational | `rHoare _ _ _ _` | `aesop` over `CatCryptRel`; `ssprove_crypto`; `ssprove_crypto_grind` |
| distance inequality | `_ ≤ _` over `ℝ≥0∞` or `ℝ` whose left side is a registered distance or a sum with one as summand, or that mentions a registered head, `prTrue` or `prEvent` | `hop_chain`; `sum_atoms_le`; `gcongr <;> catcrypt_grind`; `catcrypt_grind`; `bound` |
| monotonicity | `f a₁ … aₙ ≤ f b₁ … bₙ` or `<`, the same head on both sides; `Monotone f`, `Antitone f`, `StrictMono f`, `StrictAnti f` | `gcongr_unfold`; `gcongr`; `gcongr <;> catcrypt_grind`; `simp_all`; `grind` |
| heap read | `Heap.get (Heap.set _ _ _) _ = _` (either side), or `=`, `≠`, `¬ _ = _` mentioning `Heap.set` | `grind [Heap.get_set_same, Heap.get_set_other]` |
| game equality | `_ = _` over `SPComp _` | `catcrypt_grind`; `bind_vcgen` |
| other | anything else | `simp_all`; `grind` |

A registered distance is a term that `distView?` of `CatCryptCore.Tactics.AutoArms`
reads as an application of a distance whose triangle lemma carries `@[hop_metric]`,
after unfolding the definitions and equations registered with `@[hop_metric]`; a
term that is not one is read again after `whnfR`. A registered head is the head
constant of a `@[hop_metric]` registration. The registrations of `sdist`,
`Advantage` and `AdvantageA` are in `CatCryptCore.Tactics.AutoMetrics`, which this
module imports; a definition of an advantage or a probability becomes a registered
distance by `@[hop_metric]` on it or on its defining equation.

The `hop_chain` arm receives the arguments that elaborate to a proof of an
unquantified proposition; the `sum_atoms_le` arm closes a sum of atoms against a
sum of atoms with the inequalities of the local context; the `gcongr_unfold` arm
receives the arguments that are identifiers as the definitions to unfold.

`bound` runs under a quarter of the arm budget, and not at all when a local
hypothesis is a `∀`-quantified inequality: `bound` then tries to unify that
hypothesis's conclusion with the goal, which unfolds the game definitions.

`catcrypt_auto [t₁, …, tₙ]` passes the terms `tᵢ` to the arms: to `grind`,
`catcrypt_grind` and `simp_all` as lemma arguments, to `aesop` as
`(add unsafe tᵢ)`, to `hop_chain` as further hop facts, and to `gcongr_unfold`
as definitions to unfold.

Each arm runs under a heartbeat budget of its own, counted from the arm's start:
`catcrypt_auto.maxHeartbeats` heartbeats (default 20000, in the unit of
`maxHeartbeats`), with error recovery off, so that a combinator such as `<;>`
reports the first error of a branch. An arm that fails, leaves a goal open, logs
an error, assigns the goal a term containing `sorry`, or exceeds its budget (a
runtime exception, caught) is undone with its messages, and the next arm runs.
When every arm fails, the error names the shape and each arm with the first line
of its error.

`catcrypt_auto?` behaves as `catcrypt_auto` and adds a "Try this" suggestion with
the closing arm and its arguments, preceded by the `simp only` normalisation when
it changed the goal.
-/

public section

namespace CatCrypt.Tactics.AutoDispatch

open Lean Elab Tactic Meta

meta section

register_option catcrypt_auto.maxHeartbeats : Nat := {
  defValue := 20000
  descr := "heartbeat budget of each arm of `catcrypt_auto`, in the unit of `maxHeartbeats`"
}

/-- The goal shapes `catcrypt_auto` distinguishes. -/
inductive Shape where
  | sideCondition
  | relational
  | distanceBound
  | monotone
  | heapRead
  | gameEquality
  | other
  deriving Inhabited, BEq

/-- The name of a shape, as printed in the error and trace messages. -/
def Shape.name : Shape → String
  | .sideCondition => "IsPure/NoFail side condition"
  | .relational => "relational rHoare judgment"
  | .distanceBound => "distance inequality"
  | .monotone => "monotonicity inequality"
  | .heapRead => "heap read after write"
  | .gameEquality => "SPComp equality"
  | .other => "other"

/-- `e` mentions one of the constants `cs`. -/
def mentionsConst (cs : List Name) (e : Expr) : Bool :=
  (e.find? fun s => match s.constName? with
    | some n => cs.contains n
    | none => false).isSome

/-- The probability constants whose occurrence marks an inequality as a distance
inequality. -/
def probabilityConsts : List Name :=
  [`CatCrypt.Crypto.prTrue, `CatCrypt.Unary.prEvent]

/-- The head constants of the `@[hop_metric]` registrations. -/
def registeredHeads : MetaM (List Name) := do
  return (← AutoArms.hopEntries).toList.map (·.head)

/-- `e` is a registered distance, read directly or after `whnfR`. -/
def isDistance (e : Expr) : MetaM Bool := do
  if (← AutoArms.distView? e).isSome then return true
  return (← AutoArms.distView? (← whnfR e)).isSome

/-- `e` is a registered distance or a sum with a registered distance as a
summand. -/
partial def hasDistanceSummand (e : Expr) : MetaM Bool := do
  let e := e.cleanupAnnotations
  if let some (a, b) := AutoArms.addSides? e then
    return (← hasDistanceSummand a) || (← hasDistanceSummand b)
  isDistance e

/-- `a ≤ b` is a distance inequality: `a` is a registered distance or a sum with
one as summand, or `a` or `b` mentions a registered head or a probability
constant. -/
def isDistanceIneq (a b : Expr) : MetaM Bool := do
  let cs := probabilityConsts ++ (← registeredHeads)
  if mentionsConst cs a || mentionsConst cs b then return true
  hasDistanceSummand a

/-- The monotonicity predicates read as the monotonicity shape. -/
def monotonePreds : List Name :=
  [``Monotone, ``Antitone, ``StrictMono, ``StrictAnti]

/-- `e` is `Heap.get (Heap.set _ _ _) _`. -/
def isGetOfSet (e : Expr) : Bool :=
  e.isAppOfArity ``CatCrypt.Core.Heap.get 2 &&
    (e.getArg! 0).isAppOfArity ``CatCrypt.Core.Heap.set 3

/-- `a` and `b` are applications of the same function to the same number of
arguments. -/
def sameHead (a b : Expr) : Bool :=
  a.getAppNumArgs > 0 && a.getAppNumArgs == b.getAppNumArgs && a.getAppFn == b.getAppFn

/-- The shape of `t`, read from its head; `none` when no shape other than
`other` matches. -/
def shapeOf? (t : Expr) : MetaM (Option Shape) := do
  let t := t.cleanupAnnotations
  match_expr t with
  | CatCrypt.Core.SPComp.IsPure _ _ => return some .sideCondition
  | CatCrypt.Crypto.SPComp.NoFail _ _ => return some .sideCondition
  | CatCrypt.Relational.rHoare _ _ _ _ _ _ => return some .relational
  | LE.le α _ a b =>
    let α ← whnfR α
    if (α.isConstOf ``ENNReal || α.isConstOf ``Real) && (← isDistanceIneq a b) then
      return some .distanceBound
    if sameHead a b then return some .monotone
    return none
  | LT.lt _ _ a b =>
    if sameHead a b then return some .monotone
    return none
  | Eq α a b =>
    if isGetOfSet a || isGetOfSet b then return some .heapRead
    let α ← whnfR α
    if α.isAppOf ``CatCrypt.Core.SPComp then return some .gameEquality
    if mentionsConst [``CatCrypt.Core.Heap.set] t then return some .heapRead
    return none
  | Ne _ _ _ =>
    if mentionsConst [``CatCrypt.Core.Heap.set] t then return some .heapRead
    return none
  | Not p =>
    if p.isAppOfArity ``Eq 3 && mentionsConst [``CatCrypt.Core.Heap.set] p then
      return some .heapRead
    return none
  | _ =>
    if monotonePreds.any t.isAppOf then return some .monotone
    return none

/-- The shape of `t`: the head of `t` with its `let` variables replaced by their
values, else the head of its `whnfR`. -/
def shape (t : Expr) : MetaM Shape := do
  let t ← zetaReduce (← instantiateMVars t)
  if let some s ← shapeOf? t then return s
  if let some s ← shapeOf? (← whnfR t) then return s
  return .other

/-- The terms of the optional argument list `[t₁, …, tₙ]` at position `1` of
the syntax of `catcrypt_auto` or `catcrypt_auto?`. -/
def argsOf (stx : Syntax) : Array Term :=
  if stx[1].getNumArgs == 3 then stx[1][1].getSepArgs.map (⟨·⟩) else #[]

/-- The source text of the term `t`, pretty-printed. -/
def termText (t : Term) : TacticM String := do
  return (← PrettyPrinter.ppTerm t).pretty

/-- Parse `s` as a tactic. -/
def parseTactic (s : String) : TacticM (TSyntax `tactic) := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => return ⟨stx⟩
  | .error e => throwError "catcrypt_auto: cannot parse the arm `{s}`: {e}"

/-! ## Arguments of the `hop_chain` and `gcongr_unfold` arms -/

/-- The source texts of the arguments `ts` that elaborate, in the context of the
goal `g`, to a proof of a proposition that is not `∀`-quantified: the hop facts
`hop_chain` accepts. -/
def hopArgTexts (g : MVarId) (ts : Array Term) : TacticM (Array String) :=
  g.withContext do withoutModifyingState do
    let mut out := #[]
    for t in ts do
      let ok ← try
          let e ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm t none
          let ty ← inferType e
          pure ((← isProp ty) && !(← whnfR ty).isForall)
        catch _ => pure false
      if ok then out := out.push (← termText t)
    return out

/-- The source texts of the arguments `ts` that are identifiers: the definitions
`gcongr_unfold` unfolds. -/
def identArgTexts (ts : Array Term) : TacticM (Array String) :=
  (ts.filter (·.raw.isIdent)).mapM termText

/-- `tac` followed by the list `[t₁, …, tₙ]` of `xs`, or `tac` alone when `xs` is
empty. -/
def withList (tac : String) (xs : Array String) : String :=
  if xs.isEmpty then tac else s!"{tac} [{", ".intercalate xs.toList}]"

/-! ## Arms -/

/-- An arm: the tactic, its heartbeat budget, and the reason it is skipped. -/
structure Arm where
  tac : TSyntax `tactic
  budget : Nat
  skip : Option String := none

/-- The name of a local hypothesis of the goal `g` that is a `∀`-quantified
inequality, if any. -/
def forallIneqHyp? (g : MVarId) : MetaM (Option Name) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isForall then
      let concl ← forallTelescopeReducing ty fun _ b => pure b
      if concl.isAppOfArity ``LE.le 4 || concl.isAppOfArity ``LT.lt 4 then
        return some d.userName
  return none

/-- The arms for a shape on the goal `g`, in the order they are tried, with the
arguments `ts` inserted. Arms are built as text and parsed, so the suggested text
names the rule set and lemmas as written. -/
def arms (sh : Shape) (g : MVarId) (ts : Array Term) (hb : Nat) : TacticM (Array Arm) := do
  let texts ← ts.mapM termText
  let lst := if texts.isEmpty then "" else s!" [{", ".intercalate texts.toList}]"
  let more := if texts.isEmpty then "" else s!", {", ".intercalate texts.toList}"
  let aesopAdd := if texts.isEmpty then ""
    else s!" (add {", ".intercalate (texts.toList.map (s!"unsafe {·}"))})"
  let aesopTxt := s!"aesop (rule_sets := [CatCryptRel]) \
    (config := \{ terminal := true }){aesopAdd}"
  let mk (s : String) : TacticM Arm := do return { tac := ← parseTactic s, budget := hb }
  match sh with
  | .sideCondition => return #[← mk aesopTxt]
  | .relational => return #[← mk aesopTxt, ← mk "ssprove_crypto", ← mk "ssprove_crypto_grind"]
  | .distanceBound =>
    let skip ← match ← forallIneqHyp? g with
      | some n => pure (some s!"skipped: the ∀-quantified inequality {n} is in context, \
          and unifying its conclusion with the goal unfolds the game definitions")
      | none => pure none
    return #[← mk (withList "hop_chain" (← hopArgTexts g ts)), ← mk "sum_atoms_le",
      ← mk s!"(gcongr <;> catcrypt_grind{lst})", ← mk s!"catcrypt_grind{lst}",
      { tac := ← parseTactic "bound", budget := max 1 (hb / 4), skip }]
  | .monotone => return #[← mk (withList "gcongr_unfold" (← identArgTexts ts)), ← mk "gcongr",
      ← mk s!"(gcongr <;> catcrypt_grind{lst})", ← mk s!"simp_all{lst}", ← mk s!"grind{lst}"]
  | .heapRead => return #[← mk s!"grind [CatCrypt.Core.Heap.get_set_same, \
      CatCrypt.Core.Heap.get_set_other{more}]"]
  | .gameEquality => return #[← mk s!"catcrypt_grind{lst}", ← mk "bind_vcgen"]
  | .other => return #[← mk s!"simp_all{lst}", ← mk s!"grind{lst}"]

/-- Run `x` under a budget of `hb` heartbeats (in the unit of `maxHeartbeats`)
counted from its start, with error recovery off. The run is accepted only when
`x` logs no error (a nested `by` block reports its unsolved goals by logging an
error and admitting them) and the goals it starts on are assigned terms without
`sorry`. A rejected run, a failure, an exceeded heartbeat budget or another
runtime exception restores the state, including the message log, and returns the
error on one line, cut at 160 characters. -/
def budgeted (hb : Nat) (x : TacticM Unit) : TacticM (Except String Unit) := do
  let saved ← Tactic.saveState
  let goals ← getGoals
  let log ← Core.getMessageLog
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
      modifyThe Core.State fun s => { s with messages := {} }
      withCurrHeartbeats (Term.withoutErrToSorry (withoutRecover x))
      let new ← Core.getMessageLog
      if let some m := new.toList.find? (·.severity == .error) then
        throwError m!"logged the error: {m.data}"
      for g in goals do
        if (← instantiateMVars (mkMVar g)).hasSorry then
          throwError "the proof term contains sorry"
      modifyThe Core.State fun s => { s with messages := log ++ new }
      return .ok ())
    fun ex => do
      saved.restore
      let msg ← ex.toMessageData.toString
      let line := " ".intercalate ((msg.splitOn "\n").map (·.trimAscii.toString))
      return .error (line.take 160).toString

/-- `e` mentions `Bind.bind`. -/
def mentionsBind (e : Expr) : Bool := mentionsConst [``Bind.bind] e

/-- Close the main goal by the arms of its shape, with the arguments `ts`.
Returns the closing arm, preceded by the `simp only` normalisation when it
changed the goal. `pre` lists the arms already tried by `AutoDispatchExt` on the
shape `preShape`; the error reports them. -/
def run (ts : Array Term) (pre : Array MessageData := #[]) (preShape : String := "") :
    TacticM (TSyntax `tactic) := do
  let hb := catcrypt_auto.maxHeartbeats.get (← getOptions)
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let start ← Tactic.saveState
  setGoals [goal]
  let before ← instantiateMVars (← goal.getType)
  let normStx ← parseTactic "simp only [CatCrypt.Core.SPComp.monad_bind_eq]"
  let mut normalised := false
  if mentionsBind before then
    let s ← Tactic.saveState
    if let .ok () ← budgeted hb (evalTactic normStx) then
      match ← getGoals with
      | [g] =>
        if (← instantiateMVars (← g.getType)) == before then s.restore
        else normalised := true
      | _ => s.restore
  let g ← getMainGoal
  let sh ← g.withContext do shape (← g.getType)
  let mut tried : Array MessageData := #[]
  for arm in ← arms sh g ts hb do
    if let some why := arm.skip then
      tried := tried.push m!"\n  {arm.tac}: {why}"
      continue
    let s ← Tactic.saveState
    let r ← budgeted arm.budget do
      evalTactic arm.tac
      unless (← getGoals).isEmpty do throwError "goals remain open"
    match r with
    | .ok () =>
      setGoals rest
      if normalised then
        return ← `(tactic| ($normStx; $(arm.tac)))
      return arm.tac
    | .error e =>
      s.restore
      tried := tried.push m!"\n  {arm.tac}: {e}"
  start.restore
  let shapes := if pre.isEmpty then m!"goal shape {sh.name}"
    else m!"goal shape {preShape} (arms of AutoDispatchExt), then {sh.name}"
  throwError m!"catcrypt_auto: {shapes}; every arm failed \
    (budget {hb} heartbeats each):{MessageData.joinSep (pre ++ tried).toList ""}"

/-- `catcrypt_auto` closes the main goal by the closers registered for its
shape (see the module docstring), each under the heartbeat budget
`catcrypt_auto.maxHeartbeats` (in the unit of `maxHeartbeats`).
`catcrypt_auto [t₁, …, tₙ]` passes the terms to the `grind`, `simp_all`,
`catcrypt_grind` and `aesop` arms, to `hop_chain` and to `gcongr_unfold`. -/
syntax (name := catcryptAuto) "catcrypt_auto" (" [" term,* "]")? : tactic

/-- `catcrypt_auto?` behaves as `catcrypt_auto` and suggests the closing arm. -/
syntax (name := catcryptAutoTrace) "catcrypt_auto?" (" [" term,* "]")? : tactic

@[tactic catcryptAuto] def evalCatcryptAuto : Tactic := fun stx => do
  discard (run (argsOf stx))

@[tactic catcryptAutoTrace] def evalCatcryptAutoTrace : Tactic := fun stx => do
  let arm ← run (argsOf stx)
  Lean.Meta.Tactic.TryThis.addSuggestion stx arm

end

end CatCrypt.Tactics.AutoDispatch

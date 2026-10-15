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
| advantage bound | `_ ≤ _` over `ℝ≥0∞` or `ℝ` mentioning `Advantage`, `AdvantageA`, `sdist`, `prTrue` or `prEvent` | hop chain; `gcongr <;> catcrypt_grind`; `catcrypt_grind`; `bound` |
| monotonicity | `f a₁ … aₙ ≤ f b₁ … bₙ` or `<`, the same head on both sides | `gcongr`; `gcongr <;> catcrypt_grind`; `simp_all`; `grind` |
| heap read | `Heap.get (Heap.set _ _ _) _ = _` (either side), or `=`, `≠`, `¬ _ = _` mentioning `Heap.set` | `grind [Heap.get_set_same, Heap.get_set_other]` |
| game equality | `_ = _` over `SPComp _` | `catcrypt_grind`; `bind_vcgen` |
| other | anything else | `simp_all`; `grind` |

The hop chain arm applies to `Advantage G₀ Gₙ ≤ ε` and `AdvantageA G₀ Gₙ A ≤ ε`:
it searches the local hypotheses and the arguments for a path of hops
`Advantage Gᵢ Gᵢ₊₁ ≤ εᵢ` (for `AdvantageA`, also `∀ A, AdvantageA Gᵢ Gᵢ₊₁ A ≤ εᵢ`
instantiated at the goal's adversary) from `G₀` to `Gₙ`, chains them by
`Advantage_triangle_chain` or `AdvantageA_triangle_chain`, and closes
`ε₁ + (ε₂ + …) ≤ ε` by `ring` or `catcrypt_grind`.

`bound` runs under a quarter of the arm budget, and not at all when a local
hypothesis is a `∀`-quantified inequality: `bound` then tries to unify that
hypothesis's conclusion with the goal, which unfolds the game definitions.

`catcrypt_auto [t₁, …, tₙ]` passes the terms `tᵢ` to the arms: to `grind`,
`catcrypt_grind` and `simp_all` as lemma arguments, to `aesop` as
`(add unsafe tᵢ)`, and to the hop chain as further hops.

Each arm runs under a heartbeat budget of its own, counted from the arm's start:
`catcrypt_auto.maxHeartbeats` heartbeats (default 20000, in the unit of
`maxHeartbeats`), with error recovery off, so that a combinator such as `<;>`
reports the first error of a branch. An arm that fails, leaves a goal open, or
exceeds its budget (a runtime exception, caught) is undone and the next arm runs.
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
  | advantageBound
  | monotone
  | heapRead
  | gameEquality
  | other
  deriving Inhabited, BEq

/-- The name of a shape, as printed in the error and trace messages. -/
def Shape.name : Shape → String
  | .sideCondition => "IsPure/NoFail side condition"
  | .relational => "relational rHoare judgment"
  | .advantageBound => "advantage/sdist inequality"
  | .monotone => "monotonicity inequality"
  | .heapRead => "heap read after write"
  | .gameEquality => "SPComp equality"
  | .other => "other"

/-- `e` mentions one of the constants `cs`. -/
def mentionsConst (cs : List Name) (e : Expr) : Bool :=
  (e.find? fun s => match s.constName? with
    | some n => cs.contains n
    | none => false).isSome

/-- The constants whose occurrence marks an inequality as an advantage bound. -/
def advantageConsts : List Name :=
  [`CatCrypt.Crypto.Advantage, `CatCrypt.Crypto.AdvantageA, `CatCrypt.Crypto.sdist,
   `CatCrypt.Crypto.prTrue, `CatCrypt.Unary.prEvent]

/-- `e` mentions one of `advantageConsts`. -/
def mentionsAdvantage (e : Expr) : Bool :=
  mentionsConst advantageConsts e

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
    if (α.isConstOf ``ENNReal || α.isConstOf ``Real) &&
        (mentionsAdvantage a || mentionsAdvantage b) then
      return some .advantageBound
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
  | _ => return none

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

/-- `s` is one parenthesised group `( … )`. -/
def isParenGroup (s : String) : Bool := Id.run do
  let cs := s.toList
  unless cs.head? == some '(' && cs.getLast? == some ')' do return false
  let mut depth : Int := 0
  for (c, i) in cs.zipIdx do
    if c == '(' then depth := depth + 1
    if c == ')' then depth := depth - 1
    if depth == 0 && i + 1 < cs.length then return false
  return true

/-- `s` in parentheses when it contains a space and is not one parenthesised
group. -/
def paren (s : String) : String :=
  if s.contains ' ' && !isParenGroup s then s!"({s})" else s

/-! ## Hop chains -/

/-- A hop `Advantage G H ≤ ε` or `AdvantageA G H A ≤ ε`, with the source text of
its proof. -/
structure Hop where
  src : Expr
  dst : Expr
  proof : String
  deriving Inhabited

/-- The games and adversary of `ty` when `ty` is `Advantage G H ≤ _` (adversary
`none`) or `AdvantageA G H A ≤ _`. -/
def hopOf? (ty : Expr) : MetaM (Option (Expr × Expr × Option Expr)) := do
  let ty := (← instantiateMVars ty).cleanupAnnotations
  match_expr ty with
  | LE.le _ _ a _ =>
    match_expr a with
    | CatCrypt.Crypto.AdvantageA _ g h adv => return some (g, h, some adv)
    | CatCrypt.Crypto.Advantage g h => return some (g, h, none)
    | _ => return none
  | _ => return none

/-- The hop of a proof of type `ty` with source text `txt`, at the adversary
`adv?` of the goal: `ty` itself, or `ty` instantiated at the adversary when `ty`
is `∀ A, AdvantageA G H A ≤ _`. -/
def hopAt? (adv? : Option Expr) (advText : String) (ty : Expr) (txt : String) :
    MetaM (Option Hop) := do
  let ty ← instantiateMVars ty
  let direct ← hopOf? ty
  let (inst, txt) ← match direct, adv?, ty with
    | some _, _, _ => pure (direct, txt)
    | none, some adv, .forallE _ _ _ _ =>
      try pure (← hopOf? (← instantiateForall ty #[adv]), s!"{txt} {paren advText}")
      catch _ => pure (none, txt)
    | _, _, _ => pure (none, txt)
  let some (g, h, a?) := inst | return none
  match adv?, a? with
  | some adv, some a =>
    unless ← withReducible (isDefEq adv a) do return none
  | none, none => pure ()
  | _, _ => return none
  return some { src := g, dst := h, proof := txt }

/-- A path of hops from `src` to `dst`, visiting each hop at most once. -/
partial def hopPath (hops : Array Hop) (src dst : Expr) (used : List Nat) :
    MetaM (Option (List Hop)) := do
  for i in [0:hops.size] do
    if used.contains i then continue
    let hop := hops[i]!
    unless ← withReducible (isDefEq hop.src src) do continue
    if ← withReducible (isDefEq hop.dst dst) then return some [hop]
    if let some rest ← hopPath hops hop.dst dst (i :: used) then
      return some (hop :: rest)
  return none

/-- The hop chain arm for the goal `g` and the arguments `ts`, when the goal is
`Advantage G₀ Gₙ ≤ _` or `AdvantageA G₀ Gₙ A ≤ _` and a path of hops from `G₀`
to `Gₙ` exists. -/
def hopChainArm? (g : MVarId) (ts : Array Term) : TacticM (Option String) :=
  g.withContext do withoutModifyingState do
    let some (g₀, gₙ, adv?) ← hopOf? (← g.getType) | return none
    let advText ← match adv? with
      | some a => pure (toString (← ppExpr a))
      | none => pure ""
    let mut hops : Array Hop := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || d.userName.hasMacroScopes then continue
      if let some hop ← hopAt? adv? advText d.type d.userName.toString then
        hops := hops.push hop
    for t in ts do
      let ty ← try
          let e ← Term.withSynthesize <| Term.elabTerm t none
          pure (some (← inferType e))
        catch _ => pure none
      if let some ty := ty then
        if let some hop ← hopAt? adv? advText ty (← termText t) then
          hops := hops.push hop
    let some path ← hopPath hops g₀ gₙ [] | return none
    let mids ← (path.dropLast.map (·.dst)).mapM fun e => do return toString (← ppExpr e)
    let leaves := path.map (paren ·.proof)
    -- `leaves.reverse` is `[lₙ, …, l₁]`; the fold builds `add_le_add l₁ (… lₙ)`.
    let sum := match leaves.reverse with
      | [] => ""
      | [only] => only
      | last :: rest => rest.foldl (fun acc p => s!"add_le_add {p} {paren acc}") last
    let (chain, unfold) := if adv?.isSome then
        (s!"CatCrypt.Crypto.AdvantageA_triangle_chain _ [{", ".intercalate mids}] _ _",
         "CatCrypt.Crypto.advantageA_sum")
      else
        (s!"CatCrypt.Crypto.Advantage_triangle_chain _ [{", ".intercalate mids}] _",
         "CatCrypt.Crypto.advantage_sum")
    return some s!"(refine le_trans ({chain}) ?_; simp only [{unfold}]; \
      refine le_trans ({sum}) ?_; first | exact le_of_eq (by ring) | catcrypt_grind)"

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
  | .advantageBound =>
    let chain ← match ← hopChainArm? g ts with
      | some s => pure #[← mk s]
      | none => pure #[]
    let skip ← match ← forallIneqHyp? g with
      | some n => pure (some s!"skipped: the ∀-quantified inequality {n} is in context, \
          and unifying its conclusion with the goal unfolds the game definitions")
      | none => pure none
    return chain ++ #[← mk s!"(gcongr <;> catcrypt_grind{lst})", ← mk s!"catcrypt_grind{lst}",
      { tac := ← parseTactic "bound", budget := max 1 (hb / 4), skip }]
  | .monotone => return #[← mk "gcongr", ← mk s!"(gcongr <;> catcrypt_grind{lst})",
      ← mk s!"simp_all{lst}", ← mk s!"grind{lst}"]
  | .heapRead => return #[← mk s!"grind [CatCrypt.Core.Heap.get_set_same, \
      CatCrypt.Core.Heap.get_set_other{more}]"]
  | .gameEquality => return #[← mk s!"catcrypt_grind{lst}", ← mk "bind_vcgen"]
  | .other => return #[← mk s!"simp_all{lst}", ← mk s!"grind{lst}"]

/-- Run `x` under a budget of `hb` heartbeats (in the unit of `maxHeartbeats`)
counted from its start, with error recovery off. A failure, including an exceeded
heartbeat budget or another runtime exception, restores the state and returns the
error on one line, cut at 160 characters. -/
def budgeted (hb : Nat) (x : TacticM Unit) : TacticM (Except String Unit) := do
  let saved ← Tactic.saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
      withCurrHeartbeats (Term.withoutErrToSorry (withoutRecover x))
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
`catcrypt_grind` and `aesop` arms and to the hop chain. -/
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

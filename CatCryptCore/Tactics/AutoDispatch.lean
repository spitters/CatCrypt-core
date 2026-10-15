/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Bound
public import CatCryptCore.Tactics.AutoSets
public import CatCryptCore.Tactics.BindVcgen

/-!
# Goal-shape dispatch over the automation sets

`catcrypt_auto` closes the main goal by reading its shape and running, in order,
the closers that apply to that shape. When the goal contains `>>=` it is first
rewritten by `simp only [SPComp.monad_bind_eq]`, so that `do` goals show their
head. The head is read from the instantiated goal and, failing a match, from
its `whnfR`.

| Shape | Detected head | Arms, in order |
|---|---|---|
| side condition | `SPComp.IsPure _`, `SPComp.NoFail _` | `aesop` over `CatCryptRel` |
| relational | `rHoare _ _ _ _` | `aesop` over `CatCryptRel`; `ssprove_crypto`; `ssprove_crypto_grind` |
| advantage bound | `_ ≤ _` over `ℝ≥0∞` or `ℝ` mentioning `Advantage`, `AdvantageA`, `sdist`, `prTrue` or `prEvent` | `gcongr <;> catcrypt_grind`; `catcrypt_grind`; `bound` |
| heap read | `Heap.get (Heap.set _ _ _) _ = _` (either side) | `grind [Heap.get_set_same, Heap.get_set_other]` |
| game equality | `_ = _` over `SPComp _` | `catcrypt_grind`; `bind_vcgen` |
| other | anything else | `simp_all`; `grind` |

Each arm runs under a heartbeat budget of its own, counted from the arm's start:
`catcrypt_auto.maxHeartbeats` heartbeats (default 20000, in the unit of
`maxHeartbeats`). An arm that fails,
leaves a goal open, or exceeds its budget (a runtime exception, caught) is undone
and the next arm runs. When every arm fails, the error names the shape and each
arm with the first line of its error.

`catcrypt_auto?` behaves as `catcrypt_auto` and adds a "Try this" suggestion with
the closing arm, preceded by the `simp only` normalisation when it was applied.
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
  | heapRead
  | gameEquality
  | other
  deriving Inhabited, BEq

/-- The name of a shape, as printed in the error and trace messages. -/
def Shape.name : Shape → String
  | .sideCondition => "IsPure/NoFail side condition"
  | .relational => "relational rHoare judgment"
  | .advantageBound => "advantage/sdist inequality"
  | .heapRead => "heap read after write"
  | .gameEquality => "SPComp equality"
  | .other => "other"

/-- The constants whose occurrence marks an inequality as an advantage bound. -/
def advantageConsts : List Name :=
  [`CatCrypt.Crypto.Advantage, `CatCrypt.Crypto.AdvantageA, `CatCrypt.Crypto.sdist,
   `CatCrypt.Crypto.prTrue, `CatCrypt.Unary.prEvent]

/-- `e` mentions one of `advantageConsts`. -/
def mentionsAdvantage (e : Expr) : Bool :=
  (e.find? fun s => match s.constName? with
    | some n => advantageConsts.contains n
    | none => false).isSome

/-- `e` is `Heap.get (Heap.set _ _ _) _`. -/
def isGetOfSet (e : Expr) : Bool :=
  e.isAppOfArity ``CatCrypt.Core.Heap.get 2 &&
    (e.getArg! 0).isAppOfArity ``CatCrypt.Core.Heap.set 3

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
    return none
  | Eq α a b =>
    if isGetOfSet a || isGetOfSet b then return some .heapRead
    let α ← whnfR α
    if α.isAppOf ``CatCrypt.Core.SPComp then return some .gameEquality
    return none
  | _ => return none

/-- The shape of `t`: the head of `t`, else the head of its `whnfR`. -/
def shape (t : Expr) : MetaM Shape := do
  let t ← instantiateMVars t
  if let some s ← shapeOf? t then return s
  if let some s ← shapeOf? (← whnfR t) then return s
  return .other

set_option hygiene false in
/-- The arms for a shape, in the order they are tried. The quotations are
unhygienic, so the suggested text names the rule set and lemmas as written. -/
def arms : Shape → TacticM (Array (TSyntax `tactic))
  | .sideCondition => return #[
      ← `(tactic| aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))]
  | .relational => return #[
      ← `(tactic| aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })),
      ← `(tactic| ssprove_crypto),
      ← `(tactic| ssprove_crypto_grind)]
  | .advantageBound => return #[
      ← `(tactic| (gcongr <;> catcrypt_grind)),
      ← `(tactic| catcrypt_grind),
      ← `(tactic| bound)]
  | .heapRead => return #[
      ← `(tactic| grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.get_set_other])]
  | .gameEquality => return #[
      ← `(tactic| catcrypt_grind),
      ← `(tactic| bind_vcgen)]
  | .other => return #[
      ← `(tactic| simp_all),
      ← `(tactic| grind)]

/-- Run `x` under a budget of `hb` heartbeats (in the unit of `maxHeartbeats`)
counted from its start. A failure, including an exceeded heartbeat budget or
another runtime exception, restores the state and returns the error on one line,
cut at 160 characters. -/
def budgeted (hb : Nat) (x : TacticM Unit) : TacticM (Except String Unit) := do
  let saved ← Tactic.saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
      withCurrHeartbeats x
      return .ok ())
    fun ex => do
      saved.restore
      let msg ← ex.toMessageData.toString
      let line := " ".intercalate ((msg.splitOn "\n").map (·.trimAscii.toString))
      return .error (line.take 160).toString

set_option hygiene false in
/-- Close the main goal by the arms of its shape. Returns the closing arm,
preceded by the `simp only` normalisation when it was applied. -/
def run : TacticM (TSyntax `tactic) := do
  let hb := catcrypt_auto.maxHeartbeats.get (← getOptions)
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let start ← Tactic.saveState
  setGoals [goal]
  let normStx ← `(tactic| simp only [CatCrypt.Core.SPComp.monad_bind_eq])
  let normalised ← match ← budgeted hb (evalTactic normStx) with
    | .ok () => pure true
    | .error _ => pure false
  let g ← getMainGoal
  let sh ← g.withContext do shape (← g.getType)
  let mut tried : Array MessageData := #[]
  for arm in ← arms sh do
    let s ← Tactic.saveState
    let r ← budgeted hb do
      evalTactic arm
      unless (← getGoals).isEmpty do throwError "goals remain open"
    match r with
    | .ok () =>
      setGoals rest
      if normalised then
        return ← `(tactic| (simp only [CatCrypt.Core.SPComp.monad_bind_eq]; $arm))
      return arm
    | .error e =>
      s.restore
      tried := tried.push m!"\n  {arm}: {e}"
  start.restore
  throwError m!"catcrypt_auto: goal shape {sh.name}; every arm failed \
    (budget {hb} heartbeats each):{MessageData.joinSep tried.toList ""}"

/-- `catcrypt_auto` closes the main goal by the closers registered for its
shape (see the module docstring), each under the heartbeat budget
`catcrypt_auto.maxHeartbeats` (in the unit of `maxHeartbeats`). -/
syntax (name := catcryptAuto) "catcrypt_auto" : tactic

/-- `catcrypt_auto?` behaves as `catcrypt_auto` and suggests the closing arm. -/
syntax (name := catcryptAutoTrace) "catcrypt_auto?" : tactic

@[tactic catcryptAuto] def evalCatcryptAuto : Tactic := fun _ => do
  discard run

@[tactic catcryptAutoTrace] def evalCatcryptAutoTrace : Tactic := fun stx => do
  let arm ← run
  Lean.Meta.Tactic.TryThis.addSuggestion stx arm

end

end CatCrypt.Tactics.AutoDispatch

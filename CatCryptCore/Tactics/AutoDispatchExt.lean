/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatch
public meta import CatCryptCore.Tactics.AutoDispatch
public import CatCryptCore.XDijkstra.Rel.XCombinedAutomation
public meta import CatCryptCore.XDijkstra.Rel.XCombinedAutomation
public import CatCryptCore.XDijkstra.XMvcgenReg
public meta import CatCryptCore.XDijkstra.XMvcgenReg

/-!
# `catcrypt_auto` arms for the XDijkstra judgments and zero advantage

A second elaborator for the syntax of `catcrypt_auto` and `catcrypt_auto?`
(`CatCryptCore.Tactics.AutoDispatch`). It reads the goal shape; on a shape of the
table below it runs the arms in order, each under the heartbeat budget
`catcrypt_auto.maxHeartbeats`. On any other goal it yields to the elaborator of
`AutoDispatch` (by `throwUnsupportedSyntax`). When every arm fails it throws an
error naming the shape and its failed arms, and Lean then runs the elaborator of
`AutoDispatch`, whose error is the one reported if that also fails. On a hybrid
advantage goal the arms of
`AutoDispatch` include the hop chain over the hop hypotheses in context.

| Shape | Detected head | Arms, in order |
|---|---|---|
| coupling | `XRelTripleQ0 _ _ _ _`, `RelSpecTriple _ _ _ _` | `relmvcgen!?` |
| hybrid advantage | `AdvantageA _ _ _ ≤ _` | `advmvcgen!?`; `advmvcgen_dep` with the leaf cascade of `advmvcgen!?` |
| zero advantage | `AdvantageA _ _ _ = 0`, possibly under `∀ A` | `prob_to_rHoare`; `advantage_zero_of_rHoare` with `catcrypt_auto` on the `rHoare` premise |
| extended triple | mentions `XTriple`, `XPT` or `XRelTriple` | `xmvcgen!`, then `omega`, `le_rfl`, `assumption`, `simp_all` or `grind` on each residual |

An arm succeeds only when it closes the goal. The arms are active where this
module is imported.
-/

public section

namespace CatCrypt.Tactics.AutoDispatchExt

open Lean Elab Tactic Meta
open CatCrypt.Tactics.AutoDispatch

meta section

/-- The goal shapes handled by this module. -/
inductive ExtShape where
  | coupling
  | hybridAdvantage
  | zeroAdvantage
  | extendedTriple
  deriving Inhabited, BEq

/-- The constants whose occurrence marks a goal as an extended-triple goal. -/
def tripleConsts : List Name :=
  [``CatCrypt.XDijkstra.XTriple, ``CatCrypt.XDijkstra.XPT, ``CatCrypt.XDijkstra.XRelTriple]

/-- `e` mentions one of the constants `cs`. -/
def mentionsAny (cs : List Name) (e : Expr) : Bool :=
  (e.find? fun s => match s.constName? with
    | some n => cs.contains n
    | none => false).isSome

/-- `e` is `AdvantageA _ _ _ = 0`. -/
def isZeroAdvantage (e : Expr) : Bool :=
  e.isAppOfArity ``Eq 3 && (e.getArg! 1).isAppOf ``CatCrypt.Crypto.AdvantageA

/-- The shape of `t`, read from its head; `none` when `t` has no shape of this
module. -/
def extShapeOf? (t : Expr) : MetaM (Option ExtShape) := do
  let t := (← instantiateMVars t).cleanupAnnotations
  if t.isAppOf ``CatCrypt.XDijkstra.XRelTripleQ0 || t.isAppOf ``CatCrypt.XDijkstra.RelSpecTriple then
    return some .coupling
  if t.isAppOfArity ``LE.le 4 && (t.getArg! 2).isAppOf ``CatCrypt.Crypto.AdvantageA then
    return some .hybridAdvantage
  if isZeroAdvantage t || (t.isForall && isZeroAdvantage t.bindingBody!) then
    return some .zeroAdvantage
  if mentionsAny tripleConsts t then return some .extendedTriple
  return none

set_option hygiene false in
/-- The arms for a shape, in the order they are tried. -/
def extArms : ExtShape → TacticM (Array (TSyntax `tactic))
  | .coupling => return #[← `(tactic| relmvcgen!?)]
  | .hybridAdvantage => return #[
      ← `(tactic| advmvcgen!?),
      ← `(tactic| (advmvcgen_dep <;>
        (try (first | assumption | exact le_rfl | gcongr | norm_num | grind))))]
  | .zeroAdvantage => return #[
      ← `(tactic| prob_to_rHoare),
      ← `(tactic| first
        | exact CatCrypt.Crypto.advantage_zero_of_rHoare _ _ (by catcrypt_auto) _
        | (intro _
           exact CatCrypt.Crypto.advantage_zero_of_rHoare _ _ (by catcrypt_auto) _))]
  | .extendedTriple => return #[
      ← `(tactic| (xmvcgen! <;>
        (first | omega | exact le_rfl | assumption | (simp_all; done) | grind)))]

/-- The name of a shape, as printed in the error messages. -/
def ExtShape.name : ExtShape → String
  | .coupling => "coupling"
  | .hybridAdvantage => "hybrid advantage"
  | .zeroAdvantage => "zero advantage"
  | .extendedTriple => "extended triple"

/-- Close the main goal by the arms of its shape and return the closing arm.
Throws `unsupportedSyntax` when the goal has no shape of this module, and an
error naming the shape and the failed arms when every arm fails; in both cases
Lean then runs the elaborator of `AutoDispatch`. -/
def runExt (_ts : Array Term) : TacticM (TSyntax `tactic) := do
  let goal ← getMainGoal
  let some sh ← goal.withContext do extShapeOf? (← goal.getType)
    | throwUnsupportedSyntax
  let hb := catcrypt_auto.maxHeartbeats.get (← getOptions)
  let rest := (← getGoals).drop 1
  let mut tried : Array MessageData := #[]
  for arm in ← extArms sh do
    let s ← Tactic.saveState
    setGoals [goal]
    let r ← budgeted hb do
      evalTactic arm
      unless (← getGoals).isEmpty do throwError "goals remain open"
    match r with
    | .ok () =>
      setGoals rest
      return arm
    | .error e =>
      s.restore
      tried := tried.push m!"\n  {arm}: {e}"
  throwError m!"catcrypt_auto: goal shape {sh.name} (arms of AutoDispatchExt); \
    every arm failed:{MessageData.joinSep tried.toList ""}"

/-- `catcrypt_auto` on the shapes of this module. -/
@[tactic CatCrypt.Tactics.AutoDispatch.catcryptAuto] def evalCatcryptAutoExt : Tactic :=
  fun stx => do
    discard (runExt (argsOf stx))

/-- `catcrypt_auto?` on the shapes of this module, with the closing arm as
suggestion. -/
@[tactic CatCrypt.Tactics.AutoDispatch.catcryptAutoTrace] def evalCatcryptAutoExtTrace : Tactic :=
  fun stx => do
    let arm ← runExt (argsOf stx)
    Lean.Meta.Tactic.TryThis.addSuggestion stx arm

end

end CatCrypt.Tactics.AutoDispatchExt

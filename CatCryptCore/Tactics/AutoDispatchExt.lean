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
`catcrypt_auto.maxHeartbeats`, and on any other goal, or when every arm fails, it
yields to the elaborator of `AutoDispatch` (by `throwUnsupportedSyntax`), whose
error is the one reported.

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

/-- Close the main goal by the arms of its shape and return the closing arm.
Throws `unsupportedSyntax` when the goal has no shape of this module or every arm
fails, so that the elaborator of `AutoDispatch` runs. -/
def runExt : TacticM (TSyntax `tactic) := do
  let goal ← getMainGoal
  let some sh ← goal.withContext do extShapeOf? (← goal.getType)
    | throwUnsupportedSyntax
  let hb := catcrypt_auto.maxHeartbeats.get (← getOptions)
  let rest := (← getGoals).drop 1
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
    | .error _ => s.restore
  throwUnsupportedSyntax

/-- `catcrypt_auto` on the shapes of this module. -/
@[tactic CatCrypt.Tactics.AutoDispatch.catcryptAuto] def evalCatcryptAutoExt : Tactic := fun _ => do
  discard runExt

/-- `catcrypt_auto?` on the shapes of this module, with the closing arm as
suggestion. -/
@[tactic CatCrypt.Tactics.AutoDispatch.catcryptAutoTrace] def evalCatcryptAutoExtTrace : Tactic := fun stx => do
  let arm ← runExt
  Lean.Meta.Tactic.TryThis.addSuggestion stx arm

end

end CatCrypt.Tactics.AutoDispatchExt

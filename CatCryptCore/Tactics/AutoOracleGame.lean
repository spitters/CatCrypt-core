/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatch
public import CatCryptCore.Tactics.AutoEqnUnfold
public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.CryptoVerif.Game
public meta import CatCryptCore.Tactics.AutoDispatchCore

/-!
# `catcrypt_auto` arms for one call of a keyed oracle game

Goals about one call of the oracle of a `KeyedGame` (`CatCrypt.Crypto.UCTransparent`): an
equality between two calls, read through maps, possibly under binders and hypotheses, and
the preservation of a property along the support of a call.

## Main definitions

* `keyed_unfold` — unfolds the games `G` of the projections `G.oracle`, `G.init`,
  `G.keyDist`, `G.State`, `G.Key` until they are structure literals, and reduces the
  projections.
* `cases_call` — destructures each local call `a : CvCall I` into its tag, index and
  argument.
* `ctor_reduce` — replaces each application of a workspace definition to a constructor by
  the reduct of its unfolding, up to definitional equality, where the equation lemmas of
  `eqn_unfold` do not match because the argument types are stated through an interface
  (`I.Arg o` for `sckaArg o`).
* `keyed_oracle_step [l₁, …]` — introduces the binders, destructures the calls, unfolds
  the games, splits the guards of the calls and closes each branch with `rfl`, `simp`,
  `grind [l₁, …]` or an application of one of the lemmas `lᵢ`; a branch they do not close
  is split on the tag of the call, its locals of type `PUnit` are destructured, and
  `ctor_reduce` and `eqn_unfold` run before the closers are tried again. Each closer runs
  under a cap of `closerHeartbeats` thousand heartbeats, and one that runs out of heartbeats
  counts as failing.
* `keyed_oracle_support [l₁, …]` — the same steps on a goal `∀ z ∈ (G.oracle k s a).support,
  P z`: the guards are split at the membership hypothesis, the image of a map is
  destructured, and each branch closes by an assumption or an application of a lemma `lᵢ`.

The shapes `keyed oracle step` and `keyed oracle support` of the direct stage of
`catcrypt_auto` run the two tactics with the arguments of `catcrypt_auto [t₁, …]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoOracleGame

open Lean Meta Elab Tactic

meta section

/-- The projections of `KeyedGame` whose game `keyed_unfold` unfolds. -/
def keyedProjs : List Name :=
  [``CatCrypt.Crypto.UCTransparent.KeyedGame.oracle,
    ``CatCrypt.Crypto.UCTransparent.KeyedGame.init,
    ``CatCrypt.Crypto.UCTransparent.KeyedGame.keyDist,
    ``CatCrypt.Crypto.UCTransparent.KeyedGame.State,
    ``CatCrypt.Crypto.UCTransparent.KeyedGame.Key]

/-- The head constants, other than the constructor, of the games `G` of the projections of
`KeyedGame` applied to `G` in `e`. -/
def keyedHeads (e : Expr) : MetaM (Array Name) := do
  let ref ← IO.mkRef (#[] : Array Name)
  forEachExpr' e fun t => do
    if let some p := t.getAppFn.constName? then
      if keyedProjs.contains p && t.getAppNumArgs ≥ 3 then
        if let some c := (t.getArg! 2).getAppFn.constName? then
          unless c == ``CatCrypt.Crypto.UCTransparent.KeyedGame.mk ||
              (← ref.get).contains c do
            ref.modify (·.push c)
    return true
  ref.get

/-- The head constants of `keyedHeads` in the goal and its propositional hypotheses. -/
def keyedHeadsGoal (g : MVarId) : MetaM (Array Name) := g.withContext do
  let mut hs ← keyedHeads (← instantiateMVars (← g.getType))
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    for c in ← keyedHeads ty do
      unless hs.contains c do hs := hs.push c
  return hs

/-- Unfold the games of the projections of `KeyedGame` in the main goal and its hypotheses,
at most eight rounds; `true` when a round changed the goal. -/
def keyedUnfoldCore : TacticM Bool := do
  let mut progress := false
  for _ in [0:8] do
    let heads ← keyedHeadsGoal (← getMainGoal)
    if heads.isEmpty then break
    let lemmas : Array (TSyntax ``Parser.Tactic.simpLemma) ←
      heads.mapM fun c => `(Parser.Tactic.simpLemma| $(mkIdent c):term)
    let s ← saveState
    try
      evalTactic (← `(tactic| simp only [$lemmas,*] at *))
      progress := true
    catch _ =>
      s.restore
      break
    if (← getUnsolvedGoals).isEmpty then break
  return progress

/-- `keyed_unfold` unfolds, in the goal and its hypotheses, the games `G` of the projections
`G.oracle`, `G.init`, `G.keyDist`, `G.State` and `G.Key` of `KeyedGame` whose head is a
constant until they are structure literals, reducing the projections; it fails when there is
no such game. -/
syntax (name := keyedUnfoldStx) "keyed_unfold" : tactic

/-- The elaborator of `keyed_unfold`. -/
@[tactic keyedUnfoldStx] def evalKeyedUnfold : Tactic := fun _ => do
  unless ← keyedUnfoldCore do throwError "keyed_unfold: no keyed game to unfold"

/-- A local of `g` whose type is an application of `CvCall`. -/
def findCall? (g : MVarId) : MetaM (Option FVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.cleanupAnnotations.isAppOf ``CatCrypt.Crypto.CryptoVerifLogic.CvCall then
      return some d.fvarId
  return none

/-- Destructure each local `a : CvCall I` of `g` into `⟨o, i, x⟩`; the result holds the new
goal and the tags `o`. -/
partial def casesCall (g : MVarId) (tags : Array Expr := #[]) :
    MetaM (MVarId × Array Expr) := do
  let some a ← findCall? g | return (g, tags)
  let #[s₁] ← g.cases a | throwError "cases_call: a call has more than one constructor"
  let some p := s₁.fields[1]? | throwError "cases_call: a call is not a pair"
  let tags := tags.map s₁.subst.apply
  let #[s₂] ← s₁.mvarId.cases p.fvarId! | throwError "cases_call: an index is not a pair"
  let o := s₂.subst.apply s₁.fields[0]!
  casesCall s₂.mvarId ((tags.map s₂.subst.apply).push o)

/-- `cases_call` destructures each local `a : CvCall I` into its tag, index and argument. -/
syntax (name := casesCallStx) "cases_call" : tactic

/-- The elaborator of `cases_call`. -/
@[tactic casesCallStx] def evalCasesCall : Tactic := fun _ => do
  let g ← getMainGoal
  let (g', _) ← casesCall g
  if g' == g then throwError "cases_call: no local call"
  replaceMainGoal [g']

/-- `t` with each application `f a₁ … aₙ` of a definition `f` outside the library roots
(`AutoDispatch.foreignRoots`), with a constructor at the head of an argument, replaced by
the weak head normal form (`whnfCore`) of its unfolding when that has another head and is
not a stuck match. The result is definitionally equal to `t`. -/
def ctorReduce (t : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform t (post := fun e => do
    let some f := e.getAppFn.constName? | return .continue
    let some (.defnInfo _) := env.find? f | return .continue
    if isInstanceCore env f || env.isProjectionFn f || isMatcherCore env f then
      return .continue
    if let some idx := env.getModuleIdxFor? f then
      if AutoDispatch.foreignRoots.contains (env.header.moduleNames[idx.toNat]!).getRoot then
        return .continue
    let ctorArg := e.getAppArgs.any fun a =>
      match a.getAppFn.constName? with
      | some c => env.isConstructor c
      | none => false
    unless ctorArg do return .continue
    let some u ← unfoldDefinition? e | return .continue
    let u ← whnfCore u
    if u.getAppFn.isLambda || u.isLambda || u.getAppFn == e.getAppFn then return .continue
    if let some c := u.getAppFn.constName? then
      if isMatcherCore env c || isCasesOnRecursor env c then return .continue
    if u.getAppFn.isMVar || u.isProj then return .continue
    return .done u)

/-- Replace the goal and its propositional hypotheses by their `ctorReduce`; `none` when
nothing changes. -/
def ctorReduceGoal (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let mut g := g
  let mut changed := false
  let tgt ← instantiateMVars (← g.getType)
  let tgt' ← ctorReduce tgt
  if tgt' != tgt then
    g ← g.replaceTargetDefEq tgt'
    changed := true
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let ty' ← ctorReduce ty
    if ty' != ty then
      g ← g.replaceLocalDeclDefEq d.fvarId ty'
      changed := true
  return if changed then some g else none

/-- `ctor_reduce` replaces, in the goal and its hypotheses, each application of a
workspace definition to a constructor by the reduct of its unfolding (see `ctorReduce`);
it fails when nothing changes. -/
syntax (name := ctorReduceStx) "ctor_reduce" : tactic

/-- The elaborator of `ctor_reduce`. -/
@[tactic ctorReduceStx] def evalCtorReduce : Tactic := fun _ => do
  let some g ← ctorReduceGoal (← getMainGoal) | throwError "ctor_reduce: nothing to reduce"
  replaceMainGoal [g]

/-- Destructure each local of `g` whose type reduces (`whnfD`) to `PUnit`, so that it is
replaced by the constructor. -/
partial def unitCases (g : MVarId) : MetaM MVarId := do
  let some u ← g.withContext do
      (← getLCtx).findDeclM? fun d => do
        if d.isImplementationDetail then return none
        let ty ← whnfD (← instantiateMVars d.type)
        return if ty.isAppOf ``PUnit then some d.fvarId else none
    | return g
  let #[s] ← g.cases u | return g
  unitCases s.mvarId

/-- Run `tac` on `g` alone; the goals it leaves, or `none` when it fails, also by running out
of heartbeats. The state is restored when it fails. -/
def tryOn (g : MVarId) (tac : TSyntax `tactic) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  tryCatchRuntimeEx
    (do
      setGoals [g]
      evalTactic tac
      return some (← getUnsolvedGoals))
    (fun _ => do
      s.restore
      return none)

/-- The heartbeat cap, in thousands, of one closing tactic of a branch or a premise. -/
def closerHeartbeats : Nat := 4000

/-- Run `x` with at most `closerHeartbeats` thousand heartbeats, and no more than the
heartbeats left to the caller. -/
def capped {β : Type} (x : TacticM β) : TacticM β := do
  let ctx ← readThe Core.Context
  let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
  let cap := closerHeartbeats * 1000
  let cap := if ctx.maxHeartbeats == 0 then cap
    else if ctx.maxHeartbeats ≤ used then 1 else min cap (ctx.maxHeartbeats - used)
  withCurrHeartbeats <| withTheReader Core.Context ({ · with maxHeartbeats := cap }) x

/-- Close `g` by the first tactic of `tacs` that closes it, each under the cap of `capped`;
`false` when none does. -/
def closeBy (g : MVarId) (tacs : Array (TSyntax `tactic)) : TacticM Bool := do
  for t in tacs do
    let s ← saveState
    match ← capped (tryOn g t) with
    | some [] => return true
    | _ => s.restore
  return false

/-- The tactic `first | t₁ | … | tₙ`. -/
def firstOf (ts : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) := do
  let seqs : Array (TSyntax ``Parser.Tactic.tacticSeq) ←
    ts.mapM fun t => `(Parser.Tactic.tacticSeq| $t:tactic)
  `(tactic| first $[| $seqs]*)

/-- `grind [l₁, …]`, or `grind` when there is no lemma. -/
def grindWith (ls : Array Term) : TacticM (TSyntax `tactic) := do
  let gs : Array (TSyntax ``Parser.Tactic.grindParam) ←
    ls.mapM fun l => `(Parser.Tactic.grindParam| $l:term)
  if gs.isEmpty then `(tactic| grind) else `(tactic| grind [$gs,*])

/-- `apply l` followed by `assumption` or `fin` on each new goal. -/
def applyThen (l : Term) (fin : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  let close ← firstOf #[← `(tactic| assumption), fin]
  `(tactic| (apply $l <;> $close))

/-- The closing tactics of a branch of a step goal, with the lemmas `ls`. -/
def stepClosers (ls : Array Term) : TacticM (Array (TSyntax `tactic)) := do
  let fin ← grindWith ls
  let mut out : Array (TSyntax `tactic) := #[
    ← `(tactic| rfl),
    ← `(tactic| (simp only [PMF.pure_map, Prod.map, id]; done)),
    ← `(tactic| (simp only [PMF.pure_map, Prod.map, id]; rfl)),
    ← `(tactic| (simp_all; done)),
    fin]
  for l in ls do
    let fwd ← applyThen l fin
    let bwd ← `(tactic| (apply Eq.symm; $fwd))
    out := out.push fwd
    let inner ← firstOf #[← `(tactic| rfl), fwd, bwd]
    out := out.push (← `(tactic| (congr 1 <;> $inner)))
  return out

/-- The closing tactics of a branch of a support goal with the membership hypothesis `hz`,
with the lemmas `ls`. -/
def supportClosers (hz : Ident) (ls : Array Term) : TacticM (Array (TSyntax `tactic)) := do
  let fin ← grindWith ls
  let mut leaf : Array (TSyntax `tactic) :=
    #[← `(tactic| assumption), ← `(tactic| rfl), ← `(tactic| exact Set.Subset.rfl),
      ← `(tactic| exact fun _ h => h)]
  for l in ls do
    leaf := leaf.push (← applyThen l fin)
  leaf := leaf.push fin
  let leafT ← firstOf leaf
  let hzT : Term := ⟨hz.raw⟩
  let loc ← `(Parser.Tactic.location| at $hzT:term)
  let pureT ← `(tactic| simp only [PMF.support_pure, Set.mem_singleton_iff] $loc:location)
  let substT ← `(tactic| subst $hz)
  let mapT ← `(tactic|
    (obtain ⟨_, _, hzy⟩ := (PMF.mem_support_map_iff _ _ _).1 $hzT; subst hzy))
  return #[
    ← `(tactic| ($pureT; $substT; $leafT)),
    ← `(tactic| ($mapT; $leafT)),
    leafT]

/-- Close each goal of `gs` by `closers`, after a case split on the tag `o` (when it is a
local of the goal) and `eqn_unfold` when they fail; the goals left open. -/
def closeLeaves (gs : List MVarId) (tags : Array Expr)
    (closers : TacticM (Array (TSyntax `tactic))) : TacticM (List MVarId) := do
  let mut left : List MVarId := []
  for g in gs do
    if ← closeBy g (← closers) then continue
    let tag? ← g.withContext do
      tags.findM? fun o => do
        return o.isFVar && ((← getLCtx).find? o.fvarId!).isSome
    match tag? with
    | none => left := left ++ [g]
    | some o =>
      let s ← saveState
      try
        let subs ← g.cases o.fvarId!
        let mut subLeft : List MVarId := []
        for sg in subs do
          let sg₀ ← unitCases sg.mvarId
          let sg₁ := (← ctorReduceGoal sg₀).getD sg₀
          let r ← tryOn sg₁ (← `(tactic| eqn_unfold))
          let sgs := match r with
            | some l => l
            | none => [sg₁]
          for sg' in sgs do
            unless ← closeBy sg' (← closers) do subLeft := subLeft ++ [sg']
        left := left ++ subLeft
      catch _ =>
        s.restore
        left := left ++ [g]
  return left

/-- The lemma arguments of `keyed_oracle_step [l₁, …]` and `keyed_oracle_support [l₁, …]`. -/
def lemmaArgs (stx : Syntax) : Array Term :=
  if stx[1].isNone then #[] else stx[1][1].getSepArgs.map (⟨·⟩)

/-- `keyed_oracle_step [l₁, …]` introduces the binders of the goal, destructures the local
calls (`cases_call`), unfolds the keyed games (`keyed_unfold`), splits the guards of the
calls (`split_ifs`) and closes each branch by `rfl`, `simp`, `grind [l₁, …]` or an
application of a lemma `lᵢ` (directly, or after `congr 1`), after a case split on the tag of
the call and `eqn_unfold` when these fail. The branches it does not close are left as
goals. -/
syntax (name := keyedOracleStepStx) "keyed_oracle_step" (" [" term,* "]")? : tactic

/-- The elaborator of `keyed_oracle_step`. -/
@[tactic keyedOracleStepStx] def evalKeyedOracleStep : Tactic := fun stx => do
  let ls := lemmaArgs stx
  evalTactic (← `(tactic| intros))
  let (g, tags) ← casesCall (← getMainGoal)
  replaceMainGoal [g]
  discard <| keyedUnfoldCore
  if (← getUnsolvedGoals).isEmpty then return
  let gs := match ← tryOn (← getMainGoal) (← `(tactic| split_ifs)) with
    | some gs => gs
    | none => []
  let gs ← if gs.isEmpty then getUnsolvedGoals else pure gs
  setGoals (← closeLeaves gs tags (stepClosers ls))

/-- `keyed_oracle_support [l₁, …]` proves a goal `∀ z ∈ (G.oracle k s a).support, P z`,
possibly under further binders: it introduces the binders, destructures the local calls,
unfolds the keyed games, splits the guards at the membership hypothesis, and closes each
branch after rewriting the membership in a `PMF.pure` or destructuring the image of a
`PMF.map`, by an assumption, `subset_rfl`, an application of a lemma `lᵢ` or
`grind [l₁, …]`, after a case split on the tag of the call and `eqn_unfold` when these fail.
The branches it does not close are left as goals. -/
syntax (name := keyedOracleSupportStx) "keyed_oracle_support" (" [" term,* "]")? : tactic

/-- The membership hypothesis of a support goal: the last propositional local that mentions
`PMF.support`. -/
def supportHyp? (g : MVarId) : MetaM (Option FVarId) := g.withContext do
  let mut r := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Membership.mem && (ty.find? (·.isConstOf ``PMF.support)).isSome then
      r := some d.fvarId
  return r

/-- The elaborator of `keyed_oracle_support`. -/
@[tactic keyedOracleSupportStx] def evalKeyedOracleSupport : Tactic := fun stx => do
  let ls := lemmaArgs stx
  evalTactic (← `(tactic| intros))
  let (g, tags) ← casesCall (← getMainGoal)
  let some hz ← supportHyp? g | throwError "keyed_oracle_support: no membership in a support"
  let hzName ← mkFreshUserName `hz
  let g ← g.rename hz hzName
  replaceMainGoal [g]
  discard <| keyedUnfoldCore
  if (← getUnsolvedGoals).isEmpty then return
  let hzId := mkIdent hzName
  let gs := match ← tryOn (← getMainGoal) (← `(tactic| split_ifs at $hzId:ident)) with
    | some gs => gs
    | none => []
  let gs ← if gs.isEmpty then getUnsolvedGoals else pure gs
  setGoals (← closeLeaves gs tags (supportClosers hzId ls))

end

end CatCrypt.Tactics.AutoOracleGame

catcrypt_auto_shape "keyed oracle step" direct priority 85 :=
  all [mentions [CatCrypt.Crypto.UCTransparent.KeyedGame.oracle],
    any [app Eq, under_forall (app Eq), under_forall (under_forall (app Eq)),
      under_forall (under_forall (under_forall (app Eq))),
      under_forall (under_forall (under_forall (under_forall (app Eq))))]]

catcrypt_auto_shape "keyed oracle support" direct priority 84 :=
  all [mentions [CatCrypt.Crypto.UCTransparent.KeyedGame.oracle], mentions [PMF.support]]

catcrypt_auto_arm "keyed oracle step" order 10 := "keyed_oracle_step%GRIND"

catcrypt_auto_arm "keyed oracle support" order 10 := "keyed_oracle_support%GRIND"

end

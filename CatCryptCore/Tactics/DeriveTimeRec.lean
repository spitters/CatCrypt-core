/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.AutoTime

/-!
# Time theorems of recursive costed trees and costs, with a bound supplied by the user

`derive_time_bound` computes the bound of a costed tree from its structure, and finds no bound
for a costed tree defined by recursion: the recursive call is not unfolded, and no time theorem
of it exists. `derive_time_rec` takes the bound `τ` from the user and proves it by the
recursion's induction.

```
derive_time_rec R.tree using τ                 -- declares R.tree.timeBound_timed
derive_time_rec R using τ                      -- R.timed a costed oracle adversary:
                                               -- declares R.timeBound_timed
derive_time_rec f.timedCost using τ with [ls]  -- declares f.timedCost_le
```

The binders of the costed form that a pattern definition leaves inaccessible are named after
the binders of the source definition at the same place, and a cost companion `xCost` that
follows such a binder after it (`nameBinders`): the binders `L r rCost` of the costed form of
a definition by cases on `L` and `r`. The term `τ` is elaborated in the context of these
binders and of the bound variables that `derive_time_bound` introduces (`T_A` for a binder `A`
into costed trees, `G_k` for a costed tree `k`, `t_f` for a cost companion `f`,
`DeriveTimeBound.withBounds`). It is either the bound itself, a natural number, or a function
whose binders are applied to the binders and bound variables of their names; a binder of `τ`
of a name not among them is applied to the next inaccessible binder of its type. A constant
`τ` defined by recursion (`fun n G_node => halveTime G_node n`, or `askTime` itself) states the
bound by the recursion of the costed form; a closed form is proved from it afterwards.

**Tree mode.** For the costed tree `c = R.tree.timed` (or the costed oracle adversary
`c = R.timed`), defined by structural or well-founded recursion, the theorem states, for all
binders `xs` of `c`, the bound variables and their hypotheses (in the order of
`derive_time_bound`), `SPTree.Timed.stepTime (c xs) ≤ τ …`
(`OracleAdv.Timed.StepTimeBound (c xs) (τ …)` for a costed oracle adversary). It is proved by
the first of these inductions that closes every case:

* the functional induction of `c` (`fun_induction c xs generalizing vs`, with the bound
  variables `vs` generalized), whose cases have `c` unfolded at the root;
* for `c` defined by structural recursion, induction on its recursion argument
  (`Structural.EqnInfo.recArgPos`), with every other binder generalized that is neither a type
  nor an instance nor of a type that mentions the argument (those `induction` generalizes
  itself), and the bound variables; the root occurrence of `c` is rewritten once by its
  equation lemma at that occurrence, fully instantiated (`time_rec_unfold`).

In each case the root occurrence of `τ` is rewritten once in the same way when `τ` is a constant
defined by recursion. The recursive calls of `c` stay folded, since `time_bound` unfolds only
definitions that are not recursive (`AutoTime.unfoldableDef`). `time_bound` proves the case,
the induction hypotheses being local sources of the recursive calls: a source is unified with
the subtree at reducible transparency, its generalized binders by the subtree and its
generalized bound variables by its premises (`AutoTime.findSourceAt`, `closeByContext`), so that
a cost companion that grows at the recursive call (`fun i => 1 + (rCost i.succ + 3)`) gets the
bound of its new value. Before `time_bound`, each compound tree passed to a costed callee
(`fold.tree.timed (keygen.bind g).2 n`) gets its bound in the bound variables of the case
(`time_rec_trees`), so that the callee's time premise on it is closed by that bound and not by
reflexivity. When `time_bound` fails, it is run again after `split_ifs`, which
decides the conditions of the unfolded root that a hypothesis of the case decides (the
functional induction of a definition by well-founded recursion on a condition). The induction
and each case run under their own heartbeat budget `DeriveTimeBound.proofHeartbeats`, a
timeout counted as the failure of the strategy.

For a costed oracle adversary, `time_bound` bounds the step cost `(c xs').1` of a recursive call
in a continuation and the adversary `(c xs').2` separately by the induction hypothesis, so the
bound `τ` must allow the step cost twice (`askTime (n + 1) = 2 * askTime n + 4`).

**Data mode.** For a registered cost `f.timedCost` defined by recursion, the theorem
`f.timedCost_le` states `f.timedCost xs ≤ τ …` under the hypotheses of the cost companions
among the binders. Each case is unfolded at its root as in tree mode; each induction
hypothesis is instantiated at the recursive costs of the goal that do not mention bound
variables, its premises closed by `AutoTime.closeByContext`, and each bound `∀ ys, xCost ys ≤ t`
of a cost companion at the applications `xCost bs` of the goal (`time_rec_ih`), so that the
arithmetic of the case sees the bound of each call of the companion; the registered
costs of the goal are added (`AutoTime.addCostFacts`), and the case is closed by `omega`, by
`omega` after `ring_nf`, by `omega` after `simp only [ls]` (and `ring_nf`), or by `grind [ls]`.
`derive_time_bound` uses the theorem as the bound of the cost (`AutoTime.costLemmas`).

On failure the command lists, for each induction, the first case not closed and the reason.
Mutual recursion is refused.

## Main declarations

* `time_rec_unfold f` — rewrite the root occurrence of `f` once by its equation lemma
* `time_rec_ih f` — instantiate the induction hypotheses at the recursive costs of `f`
* `time_rec_trees` — bound the compound tree arguments of the costed callees of the goal
* `derive_time_rec` — the command
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeRec

open Lean Meta Elab Term Command Tactic
open CatCrypt.Core
open CatCrypt.Tactics.DeriveTimeBound (withBounds proofHeartbeats isOracleTimed)

/-- The tree of a step-prefixed tree takes at most its step time. -/
theorem snd_time_le_of_stepTime {α : Type} {x : ℕ × SPTree.Timed α} {E : ℕ}
    (h : SPTree.Timed.stepTime x ≤ E) : x.2.time ≤ E := by
  simp only [SPTree.Timed.stepTime] at h
  omega

meta section

/-- Whether `c` is defined by structural or well-founded recursion, with the names of its
mutual block. -/
def recBlock? (c : Name) : MetaM (Option (Array Name)) := do
  let env ← getEnv
  if let some i := Structural.eqnInfoExt.find? env c then return some i.declNames
  if let some i := WF.eqnInfoExt.find? env c then return some i.declNames
  return none

/-- The first subterm of `e` (pre-order) that is an application of the constant `f` to at least
`n` arguments with no loose bound variables. -/
def rootApp? (f : Name) (n : Nat) (e : Expr) : Option Expr :=
  e.find? fun s => s.isAppOf f && s.getAppNumArgs ≥ n && !s.hasLooseBVars

/-- The number of leading binders of the type of the constant `f`. -/
def constArity (f : Name) : MetaM Nat := do
  forallTelescope (← getConstInfo f).type fun xs _ => pure xs.size

/-- The names of the leading binders of `ty`. -/
def binderNames : Expr → Array Name
  | .forallE n _ b _ => #[n] ++ binderNames b
  | _ => #[]

/-- `ty` (the type of the costed form of `src`) with each binder of an inaccessible name (a
binder of a pattern definition) named after the binder of `src` at the same place, and each
cost companion `xCost` that follows such a binder `x` named after it: the binders of `ty` and
of `src` are aligned in order, a binder of an accessible name of `ty` that `src` does not have
(a cost companion, a costed tree) aligned with none. -/
def nameBinders (src : Name) (ty : Expr) : MetaM Expr := do
  let some info := (← getEnv).find? src | return ty
  let srcNames := binderNames info.type
  let names := binderNames ty
  let mut out : Array Name := #[]
  let mut j := 0
  let mut prev : Option (Name × Name) := none
  for n in names do
    if !n.hasMacroScopes then
      if let some (old, new) := prev then
        if n == old.appendAfter "Cost" then
          out := out.push (new.appendAfter "Cost")
          prev := none
          continue
      prev := none
      if let some k := (srcNames.extract j srcNames.size).idxOf? n then j := j + k + 1
      out := out.push n
    else
      let new := match srcNames[j]? with
        | some s => if s.hasMacroScopes || names.contains s then n else s
        | none => n
      j := j + 1
      prev := some (n.eraseMacroScopes, new)
      out := out.push new
  return go ty out 0
where
  /-- The binders of `e` from the `i`-th on named by `ns`. -/
  go (e : Expr) (ns : Array Name) (i : Nat) : Expr :=
    match e with
    | .forallE n d b bi => .forallE (ns[i]?.getD n) d (go b ns (i + 1)) bi
    | _ => e

/-- The equation lemmas of `f`: its equations by cases, then its unfolding equation. -/
def eqnLemmas (f : Name) : MetaM (Array Name) := do
  let eqs := (← getEqnsFor? f).getD #[]
  let unf := (← getUnfoldEqnFor? f).toArray
  return eqs ++ unf

/-- Rewrite the occurrence `occ` of `f` in the target of `g` once, by the first equation
lemma of `f` whose left side unifies with `occ` and whose premises are closed by the context.
The equation is fully instantiated, so only the occurrences of `occ` itself change. -/
def rewriteRoot (g : MVarId) (f : Name) (occ : Expr) : MetaM (Option MVarId) := g.withContext do
  for lem in ← eqnLemmas f do
    let s ← saveState
    try
      let pf0 ← mkConstWithFreshMVarLevels lem
      let (ms, _, body) ← forallMetaTelescopeReducing (← inferType pf0)
      let some (_, lhs, _) := body.eq? | throwError "no"
      unless ← isDefEq lhs occ do throwError "no"
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do throwError "no"
        unless ← CatCrypt.Tactics.AutoTime.closeByContext mid (deep := false) do
          mid.assign (← mkDecideProof (← mid.getType))
      let pf ← instantiateMVars (mkAppN pf0 ms)
      if pf.hasExprMVar then throwError "no"
      let r ← g.rewrite (← g.getType) pf
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      return some g'
    catch _ => s.restore
  return none

/-- `time_rec_unfold f` rewrites the root occurrence of the constant `f` in the goal (the first
application of `f` without bound variables) once, by its equation lemma at that occurrence;
the recursive occurrences on the right side of the equation are left folded. -/
syntax (name := timeRecUnfoldStx) "time_rec_unfold " ident : tactic

@[tactic timeRecUnfoldStx] def evalTimeRecUnfold : Tactic := fun stx => do
  let f ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some occ := rootApp? f (← constArity f) tgt
    | throwError "`time_rec_unfold`: no occurrence of `{f}`"
  let some g' ← rewriteRoot g f occ
    | throwError "`time_rec_unfold`: no equation lemma of `{f}` applies to{indentExpr occ}"
  replaceMainGoal [g']

/-- Instantiate the local hypotheses `h : ∀ ys, P → f as ≤ B` at each application `f bs` of the
target without bound variables, the premises closed by `AutoTime.closeByContext`; the
instances are added to the context. Returns the new goal. -/
def instIH (g : MVarId) (f : Name) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let occs := (CatCrypt.Tactics.AutoTime.appsOf tgt #[]).filter fun s =>
    s.isAppOf f && !s.hasLooseBVars
  let mut g := g
  let mut added : Array Expr := #[]
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    for o in occs do
      let s ← saveState
      try
        let (ms, _, body) ← forallMetaTelescopeReducing ld.type
        let some (l, _) := CatCrypt.Tactics.AutoTime.natLe? body | throwError "no"
        unless l.isAppOf f do throwError "no"
        unless ← isDefEq l o do throwError "no"
        for m in ms do
          let mid := m.mvarId!
          if ← mid.isAssigned then continue
          unless ← isProp (← mid.getType) do continue
          unless ← CatCrypt.Tactics.AutoTime.closeByContext mid do throwError "no"
        let pf ← instantiateMVars (mkAppN ld.toExpr ms)
        if pf.hasExprMVar then throwError "no"
        let ty ← instantiateMVars (← inferType pf)
        if added.contains ty then continue
        added := added.push ty
        let (_, g') ← (← g.assert `ih ty pf).intro1P
        g := g'
      catch _ => s.restore
  return g

/-- Instantiate the local hypotheses `h : ∀ ys, x ys ≤ v` on a local function `x` (the bound of
a cost companion) at each application `x bs` of the target without bound variables; the
instances `x bs ≤ v[bs/ys]` are added to the context. Returns the new goal. -/
def instCompanions (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let occs := (CatCrypt.Tactics.AutoTime.appsOf tgt #[]).filter fun s =>
    s.getAppFn.isFVar && s.getAppNumArgs > 0 && !s.hasLooseBVars
  let mut g := g
  let mut added : Array Expr := #[]
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    for o in occs do
      let s ← saveState
      try
        let (ms, _, body) ← forallMetaTelescopeReducing ld.type
        if ms.isEmpty then throwError "no"
        let some (l, _) := CatCrypt.Tactics.AutoTime.natLe? body | throwError "no"
        unless l.getAppFn.isFVar && l.getAppFn == o.getAppFn do throwError "no"
        if ← ms.anyM fun m => do isProp (← inferType m) then throwError "no"
        unless ← isDefEq l o do throwError "no"
        let pf ← instantiateMVars (mkAppN ld.toExpr ms)
        if pf.hasExprMVar then throwError "no"
        let ty ← instantiateMVars (← inferType pf)
        if added.contains ty then
          s.restore
          continue
        added := added.push ty
        let (_, g') ← (← g.assert `hc ty pf).intro1P
        g := g'
      catch _ => s.restore
  return g

/-- `time_rec_ih f` adds the instances of the induction hypotheses at the applications of `f`
in the goal (`instIH`), the instances of the bounds of the cost companions at their
applications in the goal (`instCompanions`), and the registered costs of the goal
(`AutoTime.addCostFacts`). -/
syntax (name := timeRecIHStx) "time_rec_ih " ident : tactic

@[tactic timeRecIHStx] def evalTimeRecIH : Tactic := fun stx => do
  let f ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let g ← instIH (← getMainGoal) f
  let g ← instCompanions g
  let g ← CatCrypt.Tactics.AutoTime.addCostFacts g
  replaceMainGoal [g]

/-- The bounds of the context: each local `x` with a local hypothesis `∀ ys, (x ys).time ≤ v`
(a tree, or a key when `ys` is empty) or `∀ ys, x ys ≤ v` with `ys` not empty (a cost
companion), `v` a local, with `v` and the role of `x`. -/
def ctxBounds : MetaM DeriveTimeBound.Bounds := do
  let mut bs : DeriveTimeBound.Bounds := #[]
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let r? ← forallTelescopeReducing ld.type fun ys body => do
      let some (l, v) := CatCrypt.Tactics.AutoTime.natLe? body | return none
      unless v.isFVar do return none
      if l.isAppOfArity ``SPTree.Timed.time 2 then
        let t := l.appArg!
        let .fvar f := t.getAppFn | return none
        unless t.getAppArgs == ys do return none
        return some (f, v, if ys.isEmpty then DeriveTimeBound.Role.key else .tree)
      let .fvar f := l.getAppFn | return none
      if ys.isEmpty || l.getAppArgs != ys then return none
      return some (f, v, DeriveTimeBound.Role.cost)
    if let some b := r? then bs := bs.push b
  return bs

/-- `e` with its leading `let` and `have` binders instantiated by their values. -/
partial def zetaHead (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => zetaHead (b.instantiate1 v)
  | .mdata _ b => zetaHead b
  | _ => e

/-- Add to the context of `g`, for each argument `t` of an application of a costed callee
`N.timed` in the target that is a tree with no local at its head and no loose bound variable,
the fact `t.time ≤ B`: the bound `B` computed from the bounds of the context (`ctxBounds`,
`DeriveTimeBound.boundTree`) and proved by `time_bound`. A time premise `t.time ≤ ?G` of the
callee's time theorem is then closed by the fact instead of by reflexivity, which would leave
`t.time` an atom. For the tree `t = y.2` of a pair `y` (below `have` binders, as
`derive_reduction` emits a node computation), `B` bounds `stepTime y` (`boundStep`), and the
fact `y.1 ≤ B` is added as well: the step cost `y.1` that the caller charges for the pair. -/
def treeFacts (g : MVarId) : TacticM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let bs ← ctxBounds
  let mut g := g
  let mut seen : Array Expr := #[]
  for s in CatCrypt.Tactics.AutoTime.appsOf tgt #[] do
    let some n := s.getAppFn.constName? | continue
    unless n.lastComponentAsString == "timed" do continue
    for a in s.getAppArgs do
      if a.hasLooseBVars || a.hasExprMVar || a.getAppFn.isFVar || seen.contains a then continue
      unless (← whnfR (← inferType a)).isAppOf ``SPTree.Timed do continue
      seen := seen.push a
      let st ← saveState
      try
        -- the tree `y.2` of a pair `y`: the bound of `stepTime y`, which also bounds `y.1`
        let a' := zetaHead a
        let (lhs, b) ← match CatCrypt.Tactics.AutoTime.sndOf? a' with
          | some y => do
            let b ← DeriveTimeBound.boundStep bs y
            pure (← mkAppM ``SPTree.Timed.stepTime #[y], b)
          | none => do
            let b ← DeriveTimeBound.boundTree bs a
            pure (← mkAppM ``SPTree.Timed.time #[a], b)
        let b ← DeriveTimeBound.normalizeSum (← instantiateMVars b)
        let ty ← mkAppM ``LE.le #[lhs, b]
        let mv ← mkFreshExprSyntheticOpaqueMVar ty
        let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| time_bound)))
        unless gs.isEmpty do throwError "goals remain"
        let pf ← instantiateMVars mv
        -- for a pair `y`, the bounds of `y.2.time` and `y.1`, not of `stepTime y`, which would
        -- become a source of `y` for `time_bound`
        -- the fact on `a` as it stands in the target, its `have` binders kept
        let pfs ← if (CatCrypt.Tactics.AutoTime.sndOf? a').isSome then
            pure #[(← mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.time #[a], b],
                ← mkAppM ``snd_time_le_of_stepTime #[pf]),
              (← inferType (← mkAppM ``CatCrypt.Tactics.AutoTime.fst_le_of_stepTime #[pf]),
                ← mkAppM ``CatCrypt.Tactics.AutoTime.fst_le_of_stepTime #[pf])]
          else pure #[(ty, pf)]
        for (t, p) in pfs do
          let (_, g') ← (← g.assert `htree t p).intro1P
          g := g'
      catch _ => st.restore
  return g

/-- `time_rec_trees` adds the bounds of the compound tree arguments of the costed callees in
the goal (`treeFacts`). -/
syntax (name := timeRecTreesStx) "time_rec_trees" : tactic

@[tactic timeRecTreesStx] def evalTimeRecTrees : Tactic := fun _ => do
  replaceMainGoal [← treeFacts (← getMainGoal)]

/-- The bound `τ` applied to the binders and bound variables `pool` of the names of its
binders; `τ` itself when it is a natural number. A binder of `τ` whose name is not in `pool`
is matched with the next binder of `pool` of an inaccessible name (a binder of a pattern
definition) and of the same type, with the earlier binders of `τ` replaced by their arguments,
which then takes the name in `τ` (the second component). -/
def applyByName (τ : Expr) (pool : Array Expr) : MetaM (Expr × Array (FVarId × Name)) := do
  let ty ← whnf (← inferType τ)
  if ty.isConstOf ``Nat then return (τ, #[])
  forallTelescopeReducing ty fun ys body => do
    unless (← whnf body).isConstOf ``Nat do
      throwError "the bound{indentExpr τ}\nis neither a natural number nor a function into one"
    let mut args : Array Expr := #[]
    let mut renames : Array (FVarId × Name) := #[]
    for y in ys do
      let n := (← y.fvarId!.getUserName).eraseMacroScopes
      let mut found : Option Expr := none
      for p in pool do
        let pn ← p.fvarId!.getUserName
        if !pn.hasMacroScopes && pn == n then found := some p
      if found.isNone then
        for p in pool do
          if found.isSome then break
          if args.contains p then continue
          unless (← p.fvarId!.getUserName).hasMacroScopes do continue
          -- The type of `y` with the earlier binders of `τ` replaced by their arguments.
          let yTy := (← inferType y).replaceFVars (ys.extract 0 args.size) args
          if ← isDefEq (← inferType p) yTy then
            found := some p
            renames := renames.push (p.fvarId!, n)
      let some p := found
        | let names ← pool.mapM fun p => p.fvarId!.getUserName
          throwError "the binder `{n}` of the bound names no binder of the costed form and no \
            bound variable; the names are {names}"
      args := args.push p
    return ((mkAppN τ args).headBeta, renames)

/-- `ty` with the binder of each `(f, n)` of `renames` among the leading binders `all` renamed
to `n`. -/
def renameBinders (ty : Expr) (all : Array Expr) (renames : Array (FVarId × Name)) : Expr :=
  go ty 0
where
  /-- The rename below the `i`-th leading binder. -/
  go (e : Expr) (i : Nat) : Expr :=
    match e with
    | .forallE n d b bi =>
      let n' := match all[i]? with
        | some x => (renames.find? (·.1 == x.fvarId!)).map (·.2) |>.getD n
        | none => n
      .forallE n' d (go b (i + 1)) bi
    | _ => e

/-- The position of the argument on which `c` recurses, when `c` is defined by structural
recursion (`Structural.EqnInfo.recArgPos`); `none` for well-founded recursion. -/
def structRecArg? (c : Name) : MetaM (Option Nat) :=
  return (Structural.eqnInfoExt.find? (← getEnv) c).map (·.recArgPos)

/-- The tactic syntax of the induction strategies: functional induction of `c` at all its
binders with the bound variables generalized, then, when `c` is defined by structural
recursion, structural induction on its recursion argument with all other binders generalized
that are neither types nor instances. -/
def strategies (c : Name) (xs vars : Array Expr) (ids : Array Ident) :
    TermElabM (Array (TSyntax `tactic × Bool)) := do
  let n := xs.size
  let xIds := ids.extract 0 n
  let vIds := ids.extract n (n + vars.size)
  let mut out : Array (TSyntax `tactic × Bool) := #[]
  let fn := mkIdent c
  if vIds.isEmpty then
    out := out.push (← `(tactic| fun_induction @$fn $xIds*), true)
  else
    out := out.push (← `(tactic| fun_induction @$fn $xIds* generalizing $vIds*), true)
  let some p ← structRecArg? c | return out
  for i in [p:min (p + 1) n] do
    let x := xs[i]!
    let ty ← whnf (← inferType x)
    let some (.inductInfo _) := (← getEnv).find? (ty.getAppFn.constName?.getD .anonymous)
      | continue
    -- the binders after `x` that are neither types nor instances, and are not in the type of
    -- `x`: generalized, with every bound variable
    let mut gens : Array Ident := #[]
    for j in [0:n] do
      if j == i then continue
      let y := xs[j]!
      let yty ← inferType y
      if (← inferType x).containsFVar y.fvarId! then continue
      -- a binder whose type mentions `x` is generalized by `induction` itself
      if yty.containsFVar x.fvarId! then continue
      if (← whnf yty).isSort then continue
      if (← isClass? yty).isSome then continue
      if j < i then
        -- a binder before `x` is generalized only when no binder before `x` depends on it
        if (← xs.extract 0 i |>.anyM fun z => do
            return z != y && (← inferType z).containsFVar y.fvarId!) then continue
      gens := gens.push xIds[j]!
    gens := gens ++ vIds
    let xi := xIds[i]!
    if gens.isEmpty then
      out := out.push (← `(tactic| induction $xi:ident), false)
    else
      out := out.push (← `(tactic| induction $xi:ident generalizing $gens*), false)
  return out

/-- Run `k` with a fresh heartbeat count under the budget `proofHeartbeats`; a heartbeat
timeout and any other exception, runtime ones included, become the reason `.error`. -/
def capped {γ : Type} (k : TermElabM γ) : TermElabM (Except MessageData γ) := do
  let cap (c : Core.Context) : Core.Context :=
    { c with maxHeartbeats := proofHeartbeats * 1000 }
  tryCatchRuntimeEx (.ok <$> withCurrHeartbeats (withTheReader Core.Context cap k))
    fun e => do
      if e.isInterrupt then throw e
      return .error e.toMessageData

/-- Run the tactic `tac` on `g` under the heartbeat budget `proofHeartbeats` (`capped`); the
reason when it fails or leaves goals. -/
def runCapped (g : MVarId) (tac : TSyntax `tactic) : TermElabM (Option MessageData) := do
  match ← capped (Tactic.run g (Tactic.evalTactic tac)) with
  | .error why => return some why
  | .ok [] => return none
  | .ok gs => return some m!"goals remain:{gs.map (MessageData.ofGoal ·)}"

/-- The number of error messages logged. -/
def errCount : CoreM Nat :=
  return (← Core.getMessageLog).toList.countP (·.severity == .error)

/-- The mode of the command: a costed tree or a registered cost. -/
inductive Mode where
  /-- A costed tree `R.tree.timed`. -/
  | tree
  /-- A registered cost `f.timedCost`. -/
  | data

/-- State `name` for the recursive definition `c` (a costed tree or a registered cost) with the
bound `τStx`, and prove it by the first induction strategy whose cases are all closed by
`caseTac`. -/
def emitTimeRec (mode : Mode) (c name : Name) (τStx : Term) (caseTac : Option Name → Bool →
    TermElabM (TSyntax `tactic)) : TermElabM Unit := do
  let some block ← recBlock? c
    | throwError "`{c}` is not defined by structural or well-founded recursion; use \
        `derive_time_bound`"
  if block.size > 1 then
    throwError "`{c}` is defined by mutual recursion with {block}, which is not supported"
  if (← getEnv).contains name then throwError "`{name}` is already declared"
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  let oracle ← match mode with
    | .tree => isOracleTimed c
    | .data => pure false
  let src := match mode with
    | .tree =>
      let t := c.getPrefix
      if t.lastComponentAsString == "tree" then t.getPrefix else t
    | .data => c.getPrefix
  forallTelescope (← nameBinders src info.type) fun xs body => do
    match mode with
    | .tree =>
      unless (← whnfR body).isAppOfArity ``Prod 2 do
        throwError "`{c}` is not a step-prefixed tree"
    | .data =>
      unless (← whnfR body).isConstOf ``Nat do throwError "`{c}` is not a cost"
    withBounds xs 0 #[] #[] #[] (oadv := oracle) fun _ vars hyps => do
      let τ ← Term.withSynthesize <| Term.elabTerm τStx none
      let τ ← instantiateMVars τ
      if τ.hasExprMVar then throwError "the bound{indentExpr τ}\nhas unassigned metavariables"
      let (bound, renames) ← applyByName τ (xs ++ vars)
      let x := mkAppN (Lean.mkConst c lvls) xs
      let goal ← match mode with
        | .tree =>
          if oracle then
            mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.StepTimeBound #[x, bound]
          else
            mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.stepTime #[x], bound]
        | .data => mkAppM ``LE.le #[x, bound]
      let all := xs ++ vars ++ hyps
      let ty := renameBinders (← mkForallFVars all goal) all renames
      let ids : Array Ident := (Array.range all.size).map fun i =>
        mkIdent (Name.mkSimple s!"x{i}")
      -- the head constant of the bound when it is defined by recursion: unfolded at the root
      let τHead : Option Name ← match bound.getAppFn.constName? with
        | some n => do
          let r ← recBlock? n
          pure (if r.isSome then some n else none)
        | none => pure none
      let mut reasons : Array MessageData := #[]
      for (ind, unfolded) in ← strategies c xs vars ids do
        let caseT ← caseTac τHead unfolded
        let s ← saveState
        -- the goal in the empty context: the binders of the statement are introduced by
        -- `intro`, and no local of the telescope is visible to the tactics
        let mv ← withLCtx {} {} (mkFreshExprSyntheticOpaqueMVar ty)
        let errs0 ← errCount
        let r ← capped <| Tactic.run mv.mvarId! do
              Tactic.evalTactic (← `(tactic| intro $ids*))
              Tactic.evalTactic ind
        let gs ← match r with
          | .ok gs => pure gs
          | .error why =>
            reasons := reasons.push m!"{ind}: {why}"
            s.restore
            continue
        if (← errCount) != errs0 then
          reasons := reasons.push m!"{ind}: the induction reports errors"
          s.restore
          continue
        let mut fail : Option MessageData := none
        for g in gs do
          if let some why ← runCapped g caseT then
            fail := some m!"{ind}: case `{← g.getTag}`: {why}"
            break
        if let some why := fail then
          reasons := reasons.push why
          s.restore
          continue
        let pf ← instantiateMVars mv
        if pf.hasSorry || pf.hasExprMVar then
          reasons := reasons.push m!"{ind}: the proof is incomplete"
          s.restore
          continue
        addDecl (Declaration.thmDecl
          { name, levelParams := info.levelParams, type := ← instantiateMVars ty, value := pf })
        return
      throwError "`{name}` is not proved:{reasons.foldl (· ++ m!"\n* " ++ ·) m!""}"

/-- `derive_time_rec R.tree using τ` states and proves `R.tree.timeBound_timed`, the bound `τ`
of the time of the recursive costed tree `R.tree.timed`, by induction and `time_bound`;
`derive_time_rec f.timedCost using τ with [ls]` states and proves `f.timedCost_le`, the bound
`τ` of the recursive registered cost `f.timedCost`, the lemmas `ls` used at the arithmetic
leaves (see the module docstring). -/
syntax (name := deriveTimeRecCmd) "derive_time_rec " ident " using " term
  (" with " "[" ident,* "]")? : command

@[command_elab deriveTimeRecCmd]
def elabDeriveTimeRec : CommandElab := fun stx => do
  let τStx : Term := ⟨stx[3]⟩
  let ls : Array Ident := if stx[4].isNone then #[] else
    stx[4][2].getSepArgs.map fun s => ⟨s⟩
  liftTermElabM do
    let t ← realizeGlobalConstNoOverloadWithInfo stx[1]
    if t.lastComponentAsString == "timedCost" then
      let lem : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
        ls.mapM fun l => `(Lean.Parser.Tactic.simpLemma| $l:ident)
      let gp : Array (TSyntax `Lean.Parser.Tactic.grindParam) ←
        ls.mapM fun l => `(Lean.Parser.Tactic.grindParam| $l:ident)
      let fId := mkIdent t
      emitTimeRec .data t (t.appendAfter "_le") τStx fun τHead unfolded => do
        let unfoldF ← unfoldRoot fId unfolded
        let unfoldB ← unfoldBound τHead
        let close ← if lem.isEmpty then
            `(tactic| first | omega | (ring_nf at *; omega) | grind)
          else
            `(tactic| first | omega | (ring_nf at *; omega) |
                (simp only [$lem,*] at *; omega) |
                (simp only [$lem,*] at *; ring_nf at *; omega) | grind [$gp,*])
        `(tactic| ($unfoldF:tactic
                   $unfoldB:tactic
                   time_rec_ih $fId:ident
                   $close:tactic))
    else
      unless ls.isEmpty do throwError "`with [...]` applies to a registered cost only"
      let c := t ++ `timed
      let cId := mkIdent c
      emitTimeRec .tree c (t ++ `timeBound_timed) τStx fun τHead unfolded => do
        let unfoldC ← unfoldRoot cId unfolded
        let unfoldB ← unfoldBound τHead
        `(tactic| ($unfoldC:tactic
                   $unfoldB:tactic
                   try dsimp only
                   time_rec_trees
                   first | time_bound | (split_ifs <;> time_bound) | time_bound))
where
  /-- The root unfolding of the recursive definition, unless the induction unfolded it. -/
  unfoldRoot (f : Ident) (unfolded : Bool) : TermElabM (TSyntax `tactic) :=
    if unfolded then `(tactic| skip) else `(tactic| time_rec_unfold $f:ident)
  /-- The root unfolding of the bound's head constant, when it is defined by recursion. -/
  unfoldBound (τHead : Option Name) : TermElabM (TSyntax `tactic) :=
    match τHead with
    | some n => `(tactic| try time_rec_unfold $(mkIdent n):ident)
    | none => `(tactic| skip)

end

end CatCrypt.Tactics.DeriveTimeRec

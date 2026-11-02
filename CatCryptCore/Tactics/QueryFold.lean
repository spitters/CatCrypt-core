/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public meta import Lean

/-!
# The tactic `query_fold`

`query_fold [names]` proves a query bound by rewriting it to the budget-passing fold
`OracleAdv.Within` of `CatCryptCore.Crypto.OracleProfile`, in three steps.

* The equations of the fold (`within_ret`, `within_rand`, `within_query`, `within_bind`,
  `within_mapQuery`) and the rewrites of the bounds to it (`isQueryBoundBy_iff_within`,
  `isQueryBound_iff_within`, `isQueryBound₂_iff`, `MayOnlyCall`, `isQueryProfile_iff_and`) are
  applied by `simp`. A sequential composition needs no estimate of the budget of its first part:
  the fold of the second part is the postcondition of the first.
* At a tree with no equation, a known bound enters the fold by `within_of_bound` or `within_of_add`.
  The known bounds are the hypotheses, the theorems with the attribute `@[query_fold]` and the names
  listed, and the theorems for `simulate` and `subst`. A premise of a known bound is a goal of the
  same procedure, and a choice of known bound is undone when one of its premises fails. A branch is
  split, a defined head is rewritten by its equations and a variable of a sum type is split when no
  known bound applies.
* An arithmetic goal is closed by `assumption`, `omega`, `simp` or `grind`.

A theorem or definition with the attribute `@[query_fold]`, or a name listed, whose statement is an
equation or an equivalence or which is a definition is used as a rewrite law; any other is used as
a known bound.

An induction stays with the user: the tactic fails at a recursive definition applied to a variable
without a known bound, and it reports the goal it reached.

The module names the theory of `CatCryptCore.Crypto.OracleProfile` by `Name` and imports none of it,
so a user imports that module together with this one.

## References

* T. J. Green, G. Karvounarakis, V. Tannen, *Provenance semirings*, PODS 2007.
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018.

Search words: query bound, cost bound, fold, budget, provenance, tactic.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.QueryFold

public meta section

open Lean Meta Elab Tactic

/-- The attribute of the laws and the known bounds of `query_fold`. -/
register_label_attr query_fold

/-- The name `CatCrypt.Crypto.OracleAdv.s`. -/
def adv (s : Name) : Name := `CatCrypt.Crypto.OracleAdv ++ s

/-- The constant `IsQueryBound₂`. -/
def twoKind : Name := `CatCrypt.Crypto.OracleForking.IsQueryBound₂

/-- The equational laws of the fold and the rewrites of the bounds to it. -/
def foldLaws : Array Name :=
  #[adv `within_ret, adv `within_rand, adv `within_query, adv `within_bind, adv `within_mapQuery,
    adv `isQueryBoundBy_iff_within, adv `isQueryBound_iff_within, adv `isQueryBound₂_iff,
    adv `MayOnlyCall, adv `isQueryProfile_iff_and, `implies_true, `forall_const, `true_and,
    `and_true, `Sum.elim_inl, `Sum.elim_inr, `Function.comp_apply]

/-- The known bounds of the program constructions. -/
def constructionBounds : Array Name :=
  #[adv `isQueryBoundBy_simulate, adv `isQueryBound_simulate, adv `isQueryBound_simulate_mul,
    adv `isQueryBoundBy_subst, adv `isQueryBound_subst, adv `isQueryBound_subst_of_isQueryBoundBy]

/-- The configuration of a run. -/
structure Cfg where
  /-- The rewrite laws. -/
  laws : Array Name
  /-- The simp context of the rewrite laws. -/
  ctx : Simp.Context
  /-- The known bounds among the constants. -/
  bounds : Array Name
  /-- The goal at which the search failed last. -/
  lastOpen : IO.Ref MessageData
  /-- The laws tagged or listed by the user. -/
  userLaws : Array Name

/-- The tree of a query bound or of a fold. -/
def tree? (t : Expr) : Option Expr :=
  let args := t.getAppArgs
  match t.getAppFn.constName? with
  | some n =>
    if n == adv `Within && args.size == 7 then some args[4]!
    else if n == adv `IsQueryBoundBy && args.size == 6 then some args[4]!
    else if n == adv `IsQueryBound && args.size == 5 then some args[3]!
    else if n == adv `MayOnlyCall && args.size == 5 then some args[4]!
    else if n == adv `IsQueryProfile && args.size == 8 then some args[4]!
    else if n == twoKind && args.size == 7 then some args[4]!
    else none
  | none => none

/-- A `simp only` call at the names. -/
def simpOnly (ns : Array Name) : TacticM (TSyntax `tactic) := do
  let lems ← ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  `(tactic| simp only [$[$lems:simpLemma],*])

/-- Runs a tactic at `g` and returns its goals. -/
def runAt (g : MVarId) (t : TSyntax `tactic) : TacticM (List MVarId) := do
  setGoals [g]
  evalTactic t
  pruneSolvedGoals
  getGoals

/-- Closes an arithmetic goal. -/
def leaf (cfg : Cfg) (g : MVarId) : TacticM Unit := do
  let s ← simpOnly (cfg.laws.filter (· != `implies_true))
  let ps ← cfg.userLaws.mapM fun n => `(Lean.Parser.Tactic.grindParam| $(mkCIdent n):ident)
  let gs ← runAt g (← `(tactic| first
    | assumption
    | omega
    | ($s:tactic; omega)
    | ($s:tactic; done)
    | (simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul, List.length_cons] at *; omega)
    | (simp; done)
    | (simp; omega)
    | (simp [*]; done)
    | grind [$[$ps:grindParam],*]))
  unless gs.isEmpty do throwError "query_fold: arithmetic goal left open"

/-- A local variable of a sum type occurring in the target of `g`. -/
def sumVar? (g : MVarId) : MetaM (Option FVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if t.containsFVar d.fvarId && (← whnfR d.type).isAppOf ``Sum then return some d.fvarId
  return none

/-- The bounds that a proof `pf` of the proposition `c` gives: `pf` itself, and its components at a
charge when `c` is a total, two-kind or correlated bound. -/
def boundForms (c pf : Expr) : MetaM (Array Expr) := do
  let some n := c.getAppFn.constName? | return #[pf]
  let one (e : Expr) := mkAppM (adv `IsQueryBound.isQueryBoundBy_one) #[e]
  if n == adv `IsQueryBound then
    return #[pf, ← one pf]
  if n == twoKind then
    let p ← mkAppM ``Iff.mp #[← mkConstWithFreshMVarLevels (adv `isQueryBound₂_iff), pf]
    return #[pf, ← mkAppM ``And.left #[p], ← mkAppM ``And.right #[p]]
  if n == adv `IsQueryProfile then
    return #[pf, ← mkAppM (adv `IsQueryProfile.inl) #[pf], ← mkAppM (adv `IsQueryProfile.inr) #[pf],
      ← one (← mkAppM (adv `IsQueryProfile.total) #[pf])]
  return #[pf]

mutual

/-- Closes the goals `gs` in the order: a bound with an unknown charge or budget, by a known bound;
a goal without metavariables; a premise with an unknown term, from the local context or, under its
binders, by a known bound; an inequality with an unknown side, by unifying its sides; an unknown number, as `0`. -/
partial def solve (cfg : Cfg) (fuel : Nat) (gs : List MVarId) : TacticM Unit := do
  let gs ← gs.filterM fun g => return !(← g.isAssigned)
  if gs.isEmpty then return
  if fuel == 0 then throwError "query_fold: search depth reached"
  let info ← gs.mapM fun g => do
    let t ← instantiateMVars (← g.getType)
    return (g, t, ← isProp t, t.hasExprMVar)
  if let some (g, t, _, _) := info.find? fun (_, t, p, m) => p && m && (tree? t).isSome then
    return ← resolve cfg fuel g t (gs.erase g)
  if let some (g, _, _, _) := info.find? fun (_, _, p, m) => p && !m then
    closeAlone cfg fuel g
    return ← solve cfg fuel (gs.erase g)
  for (g, t, p, m) in info do
    if p && m && !t.isAppOf ``LE.le then
      if ← g.withContext g.assumptionCore then
        return ← solve cfg fuel (gs.erase g)
      if t.isForall then
        let s ← saveState
        let (_, g') ← g.intros
        let t' ← instantiateMVars (← g'.getType)
        if (tree? t').isSome then return ← resolve cfg fuel g' t' (gs.erase g)
        s.restore
  if let some (g, t, _, _) := info.find? fun (_, t, p, m) => p && m && t.isAppOf ``LE.le then
    let args := t.getAppArgs
    if ← isDefEq args[2]! args[3]! then
      g.assign (mkApp (.const ``Nat.le_refl []) args[2]!)
      return ← solve cfg fuel (gs.erase g)
    throwError "query_fold: unknown budget:{indentExpr t}"
  if let some (g, t, _, _) := info.find? fun (_, _, p, _) => !p then
    if t.isConstOf ``Nat then
      g.assign (mkNatLit 0)
      return ← solve cfg fuel (gs.erase g)
    throwError "query_fold: unknown term of type{indentExpr t}"
  throwError "query_fold: unresolved goals"

/-- Resolves the bound `t` with an unknown charge or budget against the local context and the known
bounds, undoing a choice when the goals `rest` fail after it. -/
partial def resolve (cfg : Cfg) (fuel : Nat) (g : MVarId) (t : Expr) (rest : List MVarId) :
    TacticM Unit := g.withContext do
  let some tr := tree? t | throwError "query_fold: no tree"
  let locals := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.toExpr
  let env ← getEnv
  let consts ← (cfg.bounds.filter env.contains).mapM fun n => mkConstWithFreshMVarLevels n
  for e in locals.reverse ++ consts do
    let s ← saveState
    try
      if ← tryBound cfg fuel g t tr e rest then return
    catch _ => pure ()
    s.restore
  throwError "query_fold: no known bound of{indentExpr tr}"

/-- Resolves the bound `t` of the tree `tr` against the known bound `e`. -/
partial def tryBound (cfg : Cfg) (fuel : Nat) (g : MVarId) (t tr e : Expr) (rest : List MVarId) :
    TacticM Bool := do
  let (ms, bis, c) ← withReducible <| forallMetaTelescopeReducing (← inferType e)
  let c ← instantiateMVars c
  let some tr' := tree? c | return false
  match tr.getAppFn.constName?, tr'.getAppFn.constName? with
  | some a, some b => unless a == b do return false
  | _, _ => pure ()
  for f in ← boundForms c (mkAppN e ms) do
    let s ← saveState
    try
      if ← isDefEq (← inferType f) t then
        g.assign f
        for m in ms, bi in bis do
          if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
            m.mvarId!.assign (← synthInstance (← inferType m))
        solve cfg (fuel - 1) (ms.toList.map (·.mvarId!) ++ rest)
        return true
      s.restore
    catch _ => s.restore
  return false

/-- Closes `g`, which shares no metavariable with other goals, by the equations of the fold, then
at a tree by a known bound, a split or the equations of its head, and otherwise by arithmetic. -/
partial def closeAlone (cfg : Cfg) (fuel : Nat) (g : MVarId) : TacticM Unit := do
  let (_, g) ← g.intros
  let (g'?, _) ← simpTarget g cfg.ctx
  let some g' := g'? | return
  if g' != g then return ← solve cfg (fuel - 1) [g']
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  if t.isAppOfArity ``And 2 then
    let a ← mkFreshExprSyntheticOpaqueMVar t.getAppArgs[0]!
    let b ← mkFreshExprSyntheticOpaqueMVar t.getAppArgs[1]!
    g.assign (mkApp4 (.const ``And.intro []) t.getAppArgs[0]! t.getAppArgs[1]! a b)
    closeAlone cfg (fuel - 1) a.mvarId!
    return ← closeAlone cfg (fuel - 1) b.mvarId!
  let attempt (k : TacticM Unit) : TacticM Bool := do
    let s ← saveState
    try k; return true catch _ => s.restore; return false
  let splitSum : TacticM Bool := do
    let some d ← sumVar? g | return false
    for sg in ← g.cases d do closeAlone cfg (fuel - 1) sg.mvarId
    return true
  match tree? t with
  | some tr =>
    let rule (n : Name) (same : Bool := false) : TacticM Unit := do
      let e ← mkConstWithFreshMVarLevels n
      let ty ← inferType e
      let (ms, _, c) ← forallMetaTelescope ty
      unless ← isDefEq c t do throwError "query_fold: rule"
      if same then
        let names := ty.getForallBinderNames
        let some i := names.findIdx? (· == `c₀) | throwError "query_fold: rule"
        let some j := names.findIdx? (· == `c) | throwError "query_fold: rule"
        ms[i]!.mvarId!.assign (← instantiateMVars ms[j]!)
      g.assign (mkAppN e ms)
      solve cfg (fuel - 1) (ms.toList.map (·.mvarId!))
    if ← attempt (rule (adv `within_of_bound) true) then return
    if ← attempt (rule (adv `within_of_bound)) then return
    if ← attempt (rule (adv `within_of_add)) then return
    if ← attempt (do solve cfg (fuel - 1) (← runAt g (← `(tactic| split)))) then return
    if let some f := tr.getAppFn.constName? then
      if !(← isProjectionFn f) && ((← getEnv).find? f).any (·.isDefinition) then
        if ← attempt (do solve cfg (fuel - 1) (← runAt g (← simpOnly #[f]))) then return
    if ← attempt (do unless ← splitSum do throwError "query_fold: no sum") then return
  | none =>
    if ← attempt (leaf cfg g) then return
    if ← attempt (do unless ← splitSum do throwError "query_fold: no sum") then return
  cfg.lastOpen.set (← addMessageContextFull (toMessageData g))
  throwError "query_fold: goal left open"

end

/-- `query_fold [names]` proves a query bound through the budget-passing fold `OracleAdv.Within`:
the equations of the fold, the known bounds (hypotheses, `@[query_fold]`, the names listed) and
arithmetic. -/
syntax (name := queryFoldTac) "query_fold" (" [" Lean.Parser.Term.ident,* "]")? : tactic

/-- The elaborator of `query_fold`. -/
@[tactic queryFoldTac] def evalQueryFold : Tactic := fun stx => do
  let ids := if stx[1].isNone then #[] else stx[1][1].getSepArgs
  let listed ← ids.mapM fun i => resolveGlobalConstNoOverload i
  let tagged ← labelled `query_fold
  let names := tagged ++ listed
  let env ← getEnv
  let isLaw (n : Name) : TacticM Bool := do
    let some ci := env.find? n | return false
    if ci.isDefinition then return true
    forallTelescope ci.type fun _ c => return c.isEq || c.isAppOfArity ``Iff 2
  let userLaws ← names.filterM isLaw
  let laws := (foldLaws ++ userLaws).filter env.contains
  let bounds ← names.filterM fun n => return !(← isLaw n)
  let mut thms : SimpTheorems := {}
  for n in laws do
    let some ci := env.find? n | continue
    if ci.isDefinition then
      -- a predicate is unfolded at arithmetic goals only: a branch condition stays as written
      unless ← forallTelescope ci.type fun _ c => return c.isProp do
        thms ← thms.addDeclToUnfold n
    else thms ← thms.addConst n
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let r ← IO.mkRef m!"none"
  let cfg : Cfg := ⟨laws, ctx, bounds ++ constructionBounds, r, userLaws⟩
  evalTactic (← `(tactic| try simp only [CatCrypt.Crypto.OracleAdv.IsQueryBound,
    CatCrypt.Crypto.OracleAdv.IsQueryBoundBy] at *))
  let mut split : List MVarId := []
  for g in ← getGoals do split := split ++ [← g.casesAnd]
  let g :: rest := split | return
  try
    solve cfg 256 [g]
    setGoals rest
  catch e =>
    throwError "{e.toMessageData}\nlast goal left open:\n{← r.get}"

end

end CatCrypt.Tactics.QueryFold

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public meta import Lean

/-!
# The tactic `query_bound`

`query_bound` proves `A.IsQueryBoundBy c n`, `A.IsQueryBound n`, `MayOnlyCall S A` and
`IsQueryBound₂ A h q` by structural recursion on the tree `A`.

* A leaf `ret` holds at every budget, a sampling node passes the budget to its continuation, and
  a query `d` subtracts `c d` from it.
* A sequential composition `A.bind f` takes a budget `a` of `A` from the estimator `estimates`,
  a syntactic proposal checked by the proof, and gives `n - a` to `f`.
* A branch (`if`, `match`) is split; a definition is unfolded, and a recursive definition at a
  constructor is rewritten by its equations.
* A simulation `simulate impl A s` takes each known bound of `A` at a charge `c₀`, whose value at
  `d` is the budget of the program `impl s d`, until the programs fit that budget.
* Known bounds of a subterm are found in this order: the local context (induction hypotheses
  included), the names listed in `query_bound [names]`, the proposition fields of a structure at
  a projection head (`ROM2INDCCAAdversary.isQueryBoundRO` of `B.run pk c k`), and the theorems
  `Ns.isQueryBoundBy_f`, `Ns.isQueryBound_f`, `Ns.f.isQueryBoundBy`, `Ns.f.isQueryBound` of a head
  `Ns.f`, and `N.isQueryBound_erase` of `(N.timed …).2.erase`. `query_bound only [names]` leaves
  out the last family. A known bound applies at any pointwise larger charge and any larger
  budget, and its premises are closed in turn by this procedure or by the arithmetic leaf. Two
  known bounds whose charges sum to at least the goal charge give a bound at the sum of their
  budgets, so per-oracle counts close a total count.

A budget left as a metavariable is assigned the first proposal that the proof accepts.

An arithmetic leaf is closed by `assumption`, `omega`, `simp` or `grind`; a side condition
`∀ d, c d ≤ c₀ d` splits `d` over a sum signature first.

The tactic fails with a named error at a recursive definition applied to a variable, whose bound
takes an induction, and at an adversary variable with no known bound.

The module names the theory of `CatCryptCore.Crypto.OracleQueryVec` by `Name` and imports none of
it, so a user imports that module together with this one.

Search words: query bound, cost bound, query count, per-oracle count, provenance, tactic.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.QueryBound

public meta section

open Lean Meta Elab Tactic

/-- The name `CatCrypt.Crypto.OracleAdv.s`. -/
def adv (s : Name) : Name := `CatCrypt.Crypto.OracleAdv ++ s

/-- The constant `IsQueryBound₂`. -/
def isQueryBound₂Name : Name := `CatCrypt.Crypto.OracleForking.IsQueryBound₂

/-- Configuration of a run: the names listed by the user and whether the theorems named after a
head definition are looked up. -/
structure Cfg where
  /-- The listed names. -/
  extra : Array Name := #[]
  /-- Whether the theorems named after a head definition are looked up. -/
  named : Bool := true

/-- The charge, adversary and budget of a bound; no charge stands for `IsQueryBound`. -/
def parseBound? (t : Expr) : Option (Option Expr × Expr × Expr) :=
  let args := t.getAppArgs
  match t.getAppFn.constName? with
  | some n =>
    if n == adv `IsQueryBoundBy && args.size == 6 then some (some args[3]!, args[4]!, args[5]!)
    else if n == adv `IsQueryBound && args.size == 5 then some (none, args[3]!, args[4]!)
    else none
  | none => none

/-- The constant charge `1` on the query type of the adversary `A`. -/
def chargeOne (A : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType A)
  return .lam `x ty.getAppArgs[0]! (mkNatLit 1) .default

/-- Applies the theorem `name` to `g`, with the binders in `args` instantiated, and returns the
new goals of its remaining propositional binders in order. -/
def applyRule (g : MVarId) (name : Name) (args : List (Name × Expr) := []) :
    MetaM (List MVarId) := do
  let e ← mkConstWithFreshMVarLevels name
  let t ← inferType e
  let (ms, _, concl) ← forallMetaTelescope t
  let names := t.getForallBinderNames
  for (nm, v) in args do
    let some i := names.findIdx? (· == nm) | throwError "query_bound: {name} has no binder {nm}"
    ms[i]!.mvarId!.assign v
  unless ← isDefEq concl (← g.getType) do
    throwError "query_bound: rule {name} does not apply"
  g.assign (mkAppN e ms)
  let mut out := []
  for m in ms do
    let mid := m.mvarId!
    if !(← mid.isAssigned) && (← isProp (← mid.getType)) then out := out ++ [mid]
  return out

/-- Closes an arithmetic goal. -/
def leaf (g : MVarId) : TacticM Unit := do
  let (_, g) ← g.intros
  let rest ← getGoals
  setGoals [g]
  try
    evalTactic (← `(tactic| first
      | assumption
      | omega
      | (simp only [Sum.elim_inl, Sum.elim_inr, Function.comp]; omega)
      | (simp; done)
      | (simp; omega)
      | (simp [*]; done)
      | grind [Sum.elim]))
    unless (← getGoals).isEmpty do throwError "query_bound: arithmetic leaf left open"
  finally
    setGoals rest

/-- Closes `∀ d, c d ≤ c₀ d`, splitting `d` over the summands of a sum signature when the
arithmetic leaf fails on it. -/
partial def chargeLeaf (g : MVarId) (fuel : Nat := 4) : TacticM Unit := do
  let (d?, g) ← g.intro1
  let rec go (g : MVarId) (d : FVarId) (fuel : Nat) : TacticM Unit := do
    let s ← saveState
    try leaf g
    catch e =>
      s.restore
      let ty ← g.withContext do whnfR (← d.getType)
      unless ty.isAppOf ``Sum && fuel > 0 do throw e
      for sg in ← g.cases d do
        let some (Expr.fvar d') := sg.fields[0]? | throw e
        go sg.mvarId d' (fuel - 1)
  go g d? fuel

/-- The last component of a name, when it is a string. -/
def lastStr : Name → String
  | .str _ s => s
  | _ => ""

/-- The candidate theorems named after the head definition of `A`. -/
def namedSources (A : Expr) : MetaM (List Name) := do
  let some n := A.getAppFn.constName? | return []
  let env ← getEnv
  let mut cs : List Name := []
  let last := lastStr n
  if last == "erase" then
    if let some y := A.appArg!.getAppFn.constName? then
      if y == ``Prod.snd then
        if let some t := A.appArg!.appArg!.getAppFn.constName? then
          cs := [t.getPrefix ++ `isQueryBound_erase]
  cs := cs ++ [Name.str n.getPrefix ("isQueryBoundBy_" ++ last),
    Name.str n.getPrefix ("isQueryBound_" ++ last), n ++ `isQueryBoundBy, n ++ `isQueryBound]
  return cs.filter env.contains

/-- The fields of the structure of a projection at the head of `A`. -/
def fieldSources (A : Expr) : MetaM (List Name) := do
  let some n := A.getAppFn.constName? | return []
  let some info ← getProjectionFnInfo? n | return []
  let s := info.ctorName.getPrefix
  let env ← getEnv
  return (getStructureFields env s).toList.filterMap fun f =>
    let c := s ++ f
    if c != n && env.contains c then some c else none

/-- The known bound terms of `A`: hypotheses, listed names, structure fields and named theorems. -/
def sources (cfg : Cfg) (A : Expr) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let (_, _, c) ← forallMetaTelescopeReducing d.type
    if (parseBound? (← whnfR c)).isSome then out := out.push d.toExpr
  for n in cfg.extra do out := out.push (← mkConstWithFreshMVarLevels n)
  for n in ← fieldSources A do out := out.push (← mkConstWithFreshMVarLevels n)
  if cfg.named then
    for n in ← namedSources A do out := out.push (← mkConstWithFreshMVarLevels n)
  return out

/-- The constant at the head of a tree. -/
def headName (A : Expr) : Option Name := A.getAppFn.constName?

/-- Whether `A` is a branch the tactic splits. -/
def isBranch (A : Expr) : MetaM Bool := do
  if A.isAppOf ``ite || A.isAppOf ``dite then return true
  return (← matchMatcherApp? A).isSome

/-- `A` with its head definition unfolded, the head reduced. A recursive definition stuck on a
variable raises the named error. -/
def unfoldHead? (A : Expr) : MetaM (Option Expr) := do
  let some n := headName A | return none
  let e? ← withDefault (unfoldDefinition? A)
  let some e ← (match e? with | some e => pure (some e) | none => delta? A) | return none
  let e ← whnfCore e
  let recursive := e.find? fun x => match x.constName? with
    | some h => h.isInternal || lastStr h.getPrefix == "brecOn" ||
        lastStr h == "brecOn" || h == ``WellFounded.fix
    | none => false
  if recursive.isSome then
    throwError "query_bound: {n} is a recursive definition applied to a variable; \
      prove its bound by induction and name the theorem"
  return some e

mutual

/-- A proof of a known bound of `A` from the source term `h`, with its charge and budget. The
charge of the source is the goal charge `c` when it is left free. -/
partial def instSource (cfg : Cfg) (h A c : Expr) (fuel : Nat) :
    TacticM (Option (Expr × Expr × Expr)) := do
  let t ← inferType h
  let (ms, _, concl) ← forallMetaTelescopeReducing t
  let concl ← whnfR (← instantiateMVars concl)
  let some (cs?, X, m) := parseBound? concl | return none
  unless ← withReducible (isDefEq X A) do return none
  if let some cs := cs? then
    if (← instantiateMVars cs).isMVar then
      unless ← isDefEq cs c do return none
  for mv in ms do
    let mid := mv.mvarId!
    if ← mid.isAssigned then continue
    unless ← isProp (← mid.getType) do continue
    discharge cfg mid fuel
  let pf ← instantiateMVars (mkAppN h ms)
  if pf.hasExprMVar then return none
  match cs? with
  | some cs => return some (pf, ← instantiateMVars cs, ← instantiateMVars m)
  | none =>
    let pf' ← mkAppM (adv `IsQueryBound.isQueryBoundBy_one) #[pf]
    return some (pf', ← chargeOne A, ← instantiateMVars m)

/-- Closes a premise of a known bound: a bound by the procedure, with a free budget allowed,
any other proposition by the arithmetic leaf. -/
partial def discharge (cfg : Cfg) (g : MVarId) (fuel : Nat) : TacticM Unit := do
  let t ← whnfR (← instantiateMVars (← g.getType))
  if (parseBound? t).isSome then solve cfg g fuel
  else if t.isForall then
    let (_, g') ← g.intros
    let t' ← g'.withContext do whnfR (← instantiateMVars (← g'.getType))
    if (parseBound? t').isSome then solve cfg g' fuel else leaf g'
  else leaf g

/-- Budgets `a` proposed for `A` at the charge `c`, by the syntax of the tree. A proposal is
checked by the proof; an empty list means that the tree has no proposal. -/
partial def estimates (cfg : Cfg) (c A : Expr) (fuel : Nat) : TacticM (List Expr) := do
  if fuel == 0 then return []
  let mut fromSources : List Expr := []
  for h in ← sources cfg A do
    let s ← saveState
    let r ← try instSource cfg h A c (fuel - 1) catch _ => pure none
    let cand := r.map (·.2.2)
    s.restore
    if let some b := cand then
      unless b.hasExprMVar || fromSources.contains b do fromSources := fromSources ++ [b]
  unless fromSources.isEmpty do return fromSources
  let A ← whnfCore A
  let fn := headName A
  let args := A.getAppArgs
  if fn == some (adv `ret) then return [mkNatLit 0]
  if fn == some (adv `rand) then return ← underBinder args.back! fuel
  if fn == some (adv `query) then
    let d := args[args.size - 2]!
    let rest ← underBinder args.back! fuel
    return ← rest.mapM fun b => mkAppM ``HAdd.hAdd #[c.beta #[d], b]
  if fn == some (adv `bind) then
    let as ← estimates cfg c args[args.size - 2]! (fuel - 1)
    let bs ← underBinder args.back! fuel
    let mut out := []
    for a in as do
      for b in bs do out := out ++ [← mkAppM ``HAdd.hAdd #[a, b]]
    return out
  if fn == some (adv `simulate) then
    let X := args[args.size - 2]!
    let c₀ ← mkFreshExprMVar none
    let mut out := []
    for h in ← sources cfg X do
      let s ← saveState
      let r ← try instSource cfg h X c₀ (fuel - 1) catch _ => pure none
      let b := r.map (·.2.2)
      s.restore
      if let some b := b then
        unless b.hasExprMVar || out.contains b do out := out ++ [b]
    return out
  if fn == some (adv `mapQuery) then
    return ← estimates cfg c args.back! (fuel - 1)
  if A.isAppOf ``ite then
    let xs ← estimates cfg c args[3]! (fuel - 1)
    let ys ← estimates cfg c args[4]! (fuel - 1)
    return ← maxes xs ys
  if A.isAppOf ``dite then
    let xs ← underBinder args[3]! fuel
    let ys ← underBinder args[4]! fuel
    return ← maxes xs ys
  if let some ma ← matchMatcherApp? A then
    let mut cur : List Expr := []
    for i in [0:ma.alts.size] do
      let ys ← lambdaBoundedTelescope ma.alts[i]! ma.altNumParams[i]! fun xs b => do
        let r ← estimates cfg c b (fuel - 1)
        return r.filter fun e => !xs.any fun x => e.containsFVar x.fvarId!
      cur ← if i == 0 then pure ys else maxes cur ys
    return cur
  match ← unfoldHead? A with
  | some e => estimates cfg c e (fuel - 1)
  | none => return []
where
  /-- Estimates of the body of a continuation that do not depend on the bound variable. -/
  underBinder (k : Expr) (fuel : Nat) : TacticM (List Expr) := do
    let k ← whnfCore k
    lambdaBoundedTelescope k 1 fun xs b => do
      let r ← estimates cfg c b (fuel - 1)
      return r.filter fun e => !xs.any fun x => e.containsFVar x.fvarId!
  /-- The maxima of two lists of estimates. -/
  maxes (xs ys : List Expr) : TacticM (List Expr) := do
    let mut out := []
    for x in xs do
      for y in ys do
        out := out ++ [← if x == y then pure x else mkAppM ``Max.max #[x, y]]
    return out

/-- Closes a bound goal from a known bound of its adversary. -/
partial def trySources (cfg : Cfg) (g : MVarId) (c A n : Expr) (fuel : Nat) : TacticM Bool := do
  for h in ← sources cfg A do
    let s ← saveState
    try
      if let some (pf, c₀, n₀) ← instSource cfg h A c (fuel - 1) then
        if (← instantiateMVars n).isMVar then
          unless ← (← instantiateMVars n).mvarId!.checkedAssign n₀ do throwError "budget"
        let gs ← applyRule g (adv `isQueryBoundBy_of_le) [(`h, pf), (`c₀, c₀), (`n₀, n₀)]
        match gs with
        | [hc, hn] =>
          chargeLeaf hc
          leaf hn
          return true
        | _ => throwError "query_bound: unexpected goals of the known-bound rule"
    catch _ => pure ()
    s.restore
  trySourcePairs cfg g c A fuel

/-- Closes a bound goal from two known bounds of its adversary at charges summing to at least
the goal charge: per-oracle counts sum to a total count. -/
partial def trySourcePairs (cfg : Cfg) (g : MVarId) (c A : Expr) (fuel : Nat) : TacticM Bool := do
  let hs ← sources cfg A
  for h₁ in hs do
    for h₂ in hs do
      if h₁ == h₂ then continue
      let s ← saveState
      try
        if let some (p₁, c₁, n₁) ← instSource cfg h₁ A c (fuel - 1) then
          if let some (p₂, c₂, n₂) ← instSource cfg h₂ A c (fuel - 1) then
            if !(← isDefEq c₁ c₂) then
              let gs ← applyRule g (adv `isQueryBoundBy_of_add)
                [(`h₁, p₁), (`h₂, p₂), (`c₁, c₁), (`c₂, c₂), (`a, n₁), (`b, n₂)]
              match gs with
              | [hc, hn] =>
                chargeLeaf hc
                leaf hn
                return true
              | _ => throwError "query_bound: unexpected goals of the pair rule"
      catch _ => pure ()
      s.restore
  return false

/-- Solves a goal `IsQueryBoundBy`, `IsQueryBound`, `MayOnlyCall` or `IsQueryBound₂`. -/
partial def solve (cfg : Cfg) (g : MVarId) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "query_bound: depth bound reached"
  let (_, g) ← g.intros
  g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    if t.isAppOf (adv `IsQueryBound) then
      match ← applyRule g (adv `isQueryBound_of_one) with
      | [g'] => return ← solve cfg g' (fuel - 1)
      | _ => throwError "query_bound: unexpected goals"
    if t.isAppOf (adv `MayOnlyCall) then
      let some e ← delta? t | throwError "query_bound: MayOnlyCall does not unfold"
      return ← solve cfg (← g.replaceTargetDefEq e) (fuel - 1)
    if t.isAppOf isQueryBound₂Name then
      for g' in ← applyRule g (adv `isQueryBound₂_of) do solve cfg g' (fuel - 1)
      return
    let some (some c, A, n) := parseBound? t
      | throwError "query_bound: the goal is not a query bound:{indentExpr t}"
    if ← trySources cfg g c A n fuel then return
    solveTree cfg g c A n fuel

/-- The structural step on the tree of the adversary. -/
partial def solveTree (cfg : Cfg) (g : MVarId) (c A n : Expr) (fuel : Nat) : TacticM Unit := do
  if (← instantiateMVars n).isMVar then
    let cands ← estimates cfg c A fuel
    if cands.isEmpty then throwError "query_bound: no budget proposal for{indentExpr A}"
    for b in cands do
      let s ← saveState
      try
        unless ← (← instantiateMVars n).mvarId!.checkedAssign b do throwError "budget"
        return ← solveTree cfg g c A b fuel
      catch _ => s.restore
    throwError "query_bound: no proposed budget closes{indentExpr A}"
  let A' ← whnfCore A
  let args := A'.getAppArgs
  let fn := headName A'
  if fn == some (adv `ret) then
    let [] ← applyRule g (adv `isQueryBoundBy_ret) | throwError "query_bound: unexpected goals"
  else if fn == some (adv `rand) then
    for g' in ← applyRule g (adv `isQueryBoundBy_rand) do solve cfg g' (fuel - 1)
  else if fn == some (adv `query) then
    match ← applyRule g (adv `isQueryBoundBy_query) with
    | [hd, hk] =>
      leaf hd
      solve cfg hk (fuel - 1)
    | _ => throwError "query_bound: unexpected goals"
  else if fn == some (adv `bind) then
    let X := args[args.size - 2]!
    let cands ← estimates cfg c X fuel
    if cands.isEmpty then
      throwError "query_bound: no budget proposal for the first part of a bind:{indentExpr X}"
    let mut err? : Option Exception := none
    for a in cands do
      let s ← saveState
      try
        match ← applyRule g (adv `isQueryBoundBy_bind_sub) [(`a, a)] with
        | [hA, ha, hf] =>
          leaf ha
          solve cfg hA (fuel - 1)
          solve cfg hf (fuel - 1)
          return
        | _ => throwError "query_bound: unexpected goals"
      catch e =>
        err? := some e
        s.restore
    if let some e := err? then throw e
  else if fn == some (adv `simulate) then
    let X := args[args.size - 2]!
    let c₀ ← mkFreshExprMVar none
    let mut err? : Option Exception := none
    for h in ← sources cfg X do
      let s ← saveState
      try
        if let some (pf, c₀', n₀) ← instSource cfg h X c₀ (fuel - 1) then
          match ← applyRule g (adv `isQueryBoundBy_simulate_le)
              [(`hA, pf), (`c₀, c₀'), (`n₀, n₀)] with
          | [hn, himpl] =>
            leaf hn
            solve cfg himpl (fuel - 1)
            return
          | _ => throwError "query_bound: unexpected goals"
      catch e => err? := some e
      s.restore
    if let some e := err? then throw e
    throwError "query_bound: the simulated adversary has no known bound:{indentExpr X}"
  else if fn == some (adv `mapQuery) then
    for g' in ← applyRule g (adv `isQueryBoundBy_mapQuery_comp) do solve cfg g' (fuel - 1)
  else
    let g ← if A' == A then pure g else
      g.replaceTargetDefEq (mkAppN (← g.getType).getAppFn
        ((← g.getType).getAppArgs.set! 4 A'))
    if ← isBranch A' then
      let some gs ← splitTarget? g | throwError "query_bound: the branch does not split"
      for g' in gs do solve cfg g' (fuel - 1)
    else
      match ← try Except.ok <$> unfoldHead? A' catch e => pure (.error e) with
      | .ok (some e) =>
        let t ← g.getType
        let g' ← g.replaceTargetDefEq (mkAppN t.getAppFn (t.getAppArgs.set! 4 e))
        solve cfg g' (fuel - 1)
      | .ok none =>
        throwError "query_bound: no known bound for{indentExpr A'}"
      | .error e =>
        let some h := headName A' | throw e
        let rest ← getGoals
        setGoals [g]
        let ok ← try
            evalTactic (← `(tactic| simp only [$(mkCIdent h):ident]))
            pure true
          catch _ => pure false
        let gs ← getGoals
        setGoals rest
        match ok, gs with
        | true, [g'] => solve cfg g' (fuel - 1)
        | _, _ => throw e

end

/-- The depth bound of `query_bound`. -/
def maxDepth : Nat := 128

/-- A proof of the bound `t`, whose budget may be a metavariable, or `none` when the procedure
fails. -/
def proveBound? (t : Expr) (cfg : Cfg := {}) : TacticM (Option Expr) := do
  let s ← saveState
  let m ← mkFreshExprMVar t
  try
    solve cfg m.mvarId! maxDepth
    return some (← instantiateMVars m)
  catch _ =>
    s.restore
    return none

/-- `query_bound` proves `A.IsQueryBoundBy c n`, `A.IsQueryBound n`, `MayOnlyCall S A` and
`IsQueryBound₂ A h q` by structural recursion on `A`; see the module docstring. -/
syntax (name := queryBoundStx) "query_bound" (" only")? (" [" Lean.Parser.Term.ident,* "]")? :
  tactic

/-- The elaborator of `query_bound`. -/
@[tactic queryBoundStx] def evalQueryBound : Tactic := fun stx => do
  let named := stx[1].isNone
  let names := if stx[2].isNone then #[] else stx[2][1].getSepArgs
  let extra ← names.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  let g ← getMainGoal
  let rest := (← getGoals).tail
  solve { extra, named } g maxDepth
  setGoals rest

end

end CatCrypt.Tactics.QueryBound

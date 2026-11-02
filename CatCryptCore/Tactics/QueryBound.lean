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
  `d` is the budget of the program `impl s d`, until the programs fit that budget. A count `q` of
  `A` with a count `e` of each program gives `q * e` (`isQueryBound_simulate_mul`).
* Known bounds of a subterm are found in this order: the local context (induction hypotheses
  included), the names listed in `query_bound [names]`, the proposition fields of a structure at
  a projection head (`ROM2INDCCAAdversary.isQueryBoundRO` of `B.run pk c k`), and the theorems
  `Ns.isQueryBoundBy_f`, `Ns.isQueryBound_f`, `Ns.isQueryBound₂_f`, `Ns.f.isQueryBoundBy`,
  `Ns.f.isQueryBound` of a head `Ns.f`, and `N.isQueryBound_erase` of `(N.timed …).2.erase`, in the
  namespace of `N` or resolved in the open namespaces. `query_bound only [names]` leaves out the
  last family. A known bound applies at any pointwise larger charge and any larger budget, and its
  premises are closed in turn by this procedure or by the arithmetic leaf; its instance binders are
  synthesized. Two known bounds whose charges sum to at least the goal charge give a bound at the
  sum of their budgets, so per-oracle counts close a total count.
* The named family also holds `Ns.isQueryBoundBy_f_s` and its like (`isQueryBoundBy_encProg_pub`),
  in the module of `f` and in the current file, when the charge of its conclusion is the head of the
  goal charge or a binder. The heads `ret`, `rand`, `query`, `bind`, `simulate`, `mapQuery`, `subst`
  have rules of the structural step and no named lookup; a hypothesis at such a head comes first.
* A premise of a known bound whose budget depends on a free binder is closed after the other
  premises, and a numeric binder free in the tree and the premises (`h` of
  `isQueryBound₂_verifyQueries`) is matched against the goal budget, then taken as `0`.
* A substitution `subst impl A` has the rules of a simulation, by `isQueryBoundBy_subst` and
  `isQueryBound_subst`. The program premise of a simulation or a substitution splits its query over
  a sum signature when the procedure fails on it.
* A hypothesis bounding `query d k` gives `c d ≤ n` and `∀ r, (k r).IsQueryBoundBy c (n - c d)` in
  the context, so an induction hypothesis takes `hA r` as its premise.
* A known bound concluding `IsQueryBound₂ A h q` counts as its two components at `chargeInl` and
  `chargeInr` (`isQueryBound₂_iff`).
* A known bound matches its tree up to reducible unfolding, except that a binder of the bound
  matches an argument whose type agrees with its own at default transparency.
* An erased costed form `(N.timed …).2.erase` with no known bound is rewritten along
  `N.erase_timed` to its uncosted form, when that theorem states an equation with this left side.
* A hypothesis `(query d k).IsQueryBound 0` is `False` and closes any goal.

A budget left as a metavariable is assigned the first proposal that the proof accepts.

An arithmetic leaf is closed by `assumption`, `omega`, `simp` or `grind`, a product with a factor
`l + 1` or `(p :: ps).length` being distributed first; a side condition `∀ d, c d ≤ c₀ d` splits `d`
over a sum signature first. A hypothesis that charges several queries jointly,
`∀ m q, c (inl m) + c (inr q) ≤ 1`, is instantiated at the charges of the leaf, a binder that none
of them assigns taking a term of its type from the context or an instance; so the first query of a
path closes although the second query's argument is not in the goal. A charge given by a defined
function of the project (`keyCost keyJ`) is unfolded at a leaf that the other arms leave open.

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

/-- The closed subterms of `e`. -/
partial def closedSubterms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.hasLooseBVars || acc.contains e then acc else
    let acc := if e.isApp || e.isFVar then acc.push e else acc
    e.getAppArgs.foldl (fun a x => closedSubterms x a) acc

/-- The applications of natural-number type among `es`, arithmetic operations and literals left
out: the charges a goal mentions. -/
def chargeAtoms (es : Array Expr) : MetaM (Array Expr) :=
  es.filterM fun e => do
    if !e.isApp || e.isAppOf ``HAdd.hAdd || e.isAppOf ``HSub.hSub || e.isAppOf ``OfNat.ofNat ||
        e.isAppOf ``HMul.hMul then
      return false
    return (← whnfR (← inferType e)).isConstOf ``Nat

/-- A term of type `T` from `pool`, a pair of two such terms, or a term from an instance
`Inhabited T` or `Nonempty T`. -/
partial def inhabitant? (pool : Array Expr) (T : Expr) (fuel : Nat := 3) : MetaM (Option Expr) := do
  for x in pool do
    if ← withReducible (isDefEq (← inferType x) T) then return some x
  let T' ← whnfR T
  if T'.isAppOfArity ``Prod 2 && fuel > 0 then
    if let some a ← inhabitant? pool T'.getAppArgs[0]! (fuel - 1) then
      if let some b ← inhabitant? pool T'.getAppArgs[1]! (fuel - 1) then
        return some (← mkAppM ``Prod.mk #[a, b])
  if let some i ← synthInstance? (← mkAppM ``Inhabited #[T]) then
    return some (← mkAppOptM ``Inhabited.default #[T, i])
  if let some i ← synthInstance? (← mkAppM ``Nonempty #[T]) then
    return some (← mkAppOptM ``Classical.choice #[T, i])
  return none

/-- The summands of a sum of natural numbers. -/
partial def summands (e : Expr) : List Expr :=
  if e.isAppOfArity ``HAdd.hAdd 6 then summands e.getAppArgs[4]! ++ summands e.getAppArgs[5]!
  else [e]

/-- The instances of a universally quantified hypothesis `h : ∀ xs, s₁ + … + sₖ ≤ b` at the
charges `atoms`. Each summand is matched to an atom or left out, at least one being matched, and
a binder that no match assigns is given a term of its type by `inhabitant?`. -/
def jointInstancesOf (h : Expr) (atoms pool : Array Expr) : MetaM (Array Expr) := do
  let saved ← saveState
  let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType h)
  let concl ← whnfR (← instantiateMVars concl)
  let isBound := concl.isAppOfArity ``LE.le 4 || concl.isAppOfArity ``LT.lt 4
  if ms.isEmpty || !isBound || !concl.getAppArgs[0]!.isConstOf ``Nat then
    saved.restore
    return #[]
  let out ← IO.mkRef (#[] : Array Expr)
  let finish : MetaM Unit := do
    let s ← saveState
    for m in ms do
      let mid := m.mvarId!
      unless ← mid.isAssigned do
        let some x ← inhabitant? pool (← instantiateMVars (← mid.getType)) | continue
        mid.assign x
    let pf ← instantiateMVars (mkAppN h ms)
    s.restore
    unless pf.hasExprMVar do out.modify (·.push pf)
  let rec go : List Expr → Bool → MetaM Unit
    | [], matched => if matched then finish else pure ()
    | x :: xs, matched => do
      if x.hasExprMVar && !x.getAppFn.isMVar then
        for a in atoms do
          let s ← saveState
          if ← withReducible (isDefEq x a) then go xs true
          s.restore
      go xs matched
  go (summands concl.getAppArgs[2]!) false
  let r ← out.get
  saved.restore
  return r

/-- `g` with the instances of `jointInstancesOf` added to its context, for each hypothesis of
the context. A hypothesis `∀ m q, c (inl m) + c (inr q) ≤ 1` charges two queries of one path
jointly; its instance at the charge of the first query has as `q` any term of that type. -/
def addJointInstances (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let sub := closedSubterms tgt
  let atoms ← chargeAtoms sub
  let mut pool : Array Expr := sub.filter fun e => !e.hasExprMVar
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do
      pool := pool.push d.toExpr
      let T ← whnfR d.type
      if T.isAppOfArity ``Prod 2 then
        pool := (pool.push (← mkAppM ``Prod.fst #[d.toExpr])).push (← mkAppM ``Prod.snd #[d.toExpr])
  let mut g := g
  for d in lctx do
    if d.isImplementationDetail || !d.type.isForall then continue
    for pf in ← jointInstancesOf d.toExpr atoms pool do
      (_, g) ← g.note `joint pf
  return g

/-- The function definitions of the project among the constants of `t`, instances, projections
and matchers left out: the defined functions a charge of `t` may be given by. -/
def chargeDefs (t : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let inLibrary (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i =>
      let r := (env.header.moduleNames[i.toNat]!).getRoot
      r == `Init || r == `Std || r == `Lean || r == `Mathlib
    | none => false
  t.getUsedConstants.filterM fun n => do
    let some (.defnInfo info) := env.find? n | return false
    if (privateToUserName n).isInternal || inLibrary n || isMatcherCore env n ||
        (← isInstance n) || (← isProjectionFn n) then
      return false
    forallTelescopeReducing info.type fun _ r => return !r.isSort

/-- Closes `g` by the arithmetic arms with the definitions `chargeDefs` of its target unfolded. -/
def unfoldedLeaf (g : MVarId) : TacticM Unit := do
  let names ← chargeDefs (← instantiateMVars (← g.getType))
  if names.isEmpty then throwError "query_bound: no defined charge"
  let lems ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  setGoals [g]
  evalTactic (← `(tactic| first
    | (simp [$[$lems:simpLemma],*]; done)
    | (simp [$[$lems:simpLemma],*]; omega)
    | (simp only [$[$lems:simpLemma],*]; split <;> omega)))

/-- Closes an arithmetic goal. A goal the first arms leave open is tried with the instances of
`addJointInstances` in its context, with its defined charges unfolded, then by `grind`. -/
def leaf (g : MVarId) : TacticM Unit := do
  let (_, g) ← g.intros
  if (← instantiateMVars (← g.getType)).hasExprMVar then
    unless ← g.withContext g.assumptionCore do
      throwError "query_bound: arithmetic leaf with an unassigned budget"
    return
  let rest ← getGoals
  setGoals [g]
  try
    let s ← saveState
    try
      evalTactic (← `(tactic| first
        | assumption
        | omega
        | (simp only [Sum.elim_inl, Sum.elim_inr, Function.comp]; omega)
        | (simp only [List.length_cons, Nat.succ_mul, Nat.add_mul, Nat.one_mul]; omega)
        | (simp; done)
        | (simp; omega)
        | (simp [*]; done)))
    catch _ =>
      s.restore
      try
        setGoals [← addJointInstances g]
        evalTactic (← `(tactic| first
          | omega
          | (simp only [Sum.elim_inl, Sum.elim_inr, Function.comp]; omega)
          | (simp; omega)))
      catch _ =>
        s.restore
        try
          g.withContext (unfoldedLeaf g)
        catch _ =>
          s.restore
          try evalTactic (← `(tactic| grind [Sum.elim]))
          catch _ =>
            throwError "query_bound: arithmetic leaf left open:{indentExpr (← g.getType)}"
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

/-- The constants `s.isQueryBound_erase` for the trailing parts `s` of the name `p`, resolved in
the current namespaces and open declarations: the query bound of the erased form of `p` stated in
another namespace than `p`. -/
def eraseCompanions (p : Name) : CoreM (List Name) := do
  let comps := p.components
  let mut out : List Name := []
  for i in [0:comps.length] do
    let s := (comps.drop (comps.length - 1 - i)).foldl (· ++ ·) Name.anonymous
    for (c, fields) in ← resolveGlobalName (s ++ `isQueryBound_erase) do
      if fields.isEmpty && !out.contains c then out := out ++ [c]
  return out

/-- A proof of `A = A'` by the theorem `N.erase_timed`, for `A` the erased form
`(N.timed …).2.erase` of a costed definition and `A'` its uncosted form. An erasure theorem of
another shape gives `none`: one whose left side is `A` followed by a map of the result, and one
stating `Erases`. -/
def eraseTimed? (A : Expr) : MetaM (Option Expr) := do
  let some n := A.getAppFn.constName? | return none
  unless lastStr n == "erase" && A.isApp do return none
  let y := if A.appArg!.isAppOf ``Prod.snd then A.appArg!.appArg! else A.appArg!
  let some t := y.getAppFn.constName? | return none
  unless lastStr t == "timed" do return none
  let thm := t.getPrefix ++ `erase_timed
  unless (← getEnv).contains thm do return none
  let s ← saveState
  let e ← mkConstWithFreshMVarLevels thm
  let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
  if let some (_, lhs, _) := (← instantiateMVars concl).eq? then
    if ← withReducible (isDefEq lhs A) then
      let pf ← instantiateMVars (mkAppN e ms)
      unless pf.hasExprMVar do return some pf
  s.restore
  return none

/-- The two components `A.IsQueryBoundBy chargeInl h` and `A.IsQueryBoundBy chargeInr q`, under
the binders of `e`, when `e` concludes the two-kind bound `IsQueryBound₂ A h q`; otherwise empty. -/
def twoKindBounds (e : Expr) : MetaM (Array Expr) := do
  let name := adv `isQueryBound₂_iff
  unless (← getEnv).contains name do return #[]
  forallTelescopeReducing (← inferType e) fun xs c => do
    let c ← whnfR c
    unless c.isAppOf isQueryBound₂Name do return #[]
    let thm ← mkConstWithFreshMVarLevels name
    let (ms, _, concl) ← forallMetaTelescope (← inferType thm)
    let some (lhs, _) := (← instantiateMVars concl).iff? | return #[]
    unless ← isDefEq lhs c do return #[]
    let p ← mkAppM ``Iff.mp #[← instantiateMVars (mkAppN thm ms), mkAppN e xs]
    return #[← mkLambdaFVars xs (← mkAppM ``And.left #[p]),
      ← mkLambdaFVars xs (← mkAppM ``And.right #[p])]

/-- The heads of the trees the structural step has a rule for. A theorem named after one of them
states that rule, and a charge or budget binder of its premises is not determined by the tree. -/
def ruleHeads : List Name :=
  [adv `ret, adv `rand, adv `query, adv `bind, adv `simulate, adv `mapQuery, adv `subst]

/-- The theorems `Ns.isQueryBoundBy_f_s`, `Ns.isQueryBound_f_s`, `Ns.isQueryBound₂_f_s` of the head
`Ns.f`, in the module of `f` and in the current file. -/
def suffixedSources (n : Name) : MetaM (List Name) := do
  let env ← getEnv
  let last := lastStr n
  let pre := (privateToUserName n).getPrefix
  let starts := ["isQueryBoundBy_", "isQueryBound_", "isQueryBound₂_"].map (· ++ last ++ "_")
  let wanted (x : Name) : Bool :=
    let u := privateToUserName x
    u.getPrefix == pre && starts.any fun s => (lastStr u).startsWith s
  let local' := env.constants.foldStage2 (fun acc x _ => if wanted x then x :: acc else acc) []
  let imported := match env.getModuleIdxFor? n with
    | some i => (env.header.moduleData[i.toNat]!).constNames.toList.filter wanted
    | none => []
  return imported ++ local'

/-- Whether the conclusion of the theorem `t` has the charge `c`, or a charge that is a binder of
`t`. A conclusion of the two-kind bound and an unknown charge agree with every charge. -/
def chargeAgrees (c? : Option Expr) (t : Name) : MetaM Bool := do
  let some c := c? | return true
  let c ← instantiateMVars c
  if c.getAppFn.isMVar then return true
  let some info := (← getEnv).find? t | return false
  forallTelescopeReducing info.type fun xs concl => do
    let concl ← whnfR concl
    let some (some cs, _, _) := parseBound? concl | return true
    if xs.contains cs.getAppFn then return true
    return cs.getAppFn.constName? == c.getAppFn.constName?

/-- The candidate theorems named after the head definition of `A`: the theorems `Ns.isQueryBoundBy_f`
and their like, and the theorems of `suffixedSources` at the charge `c?`. -/
def namedSources (A : Expr) (c? : Option Expr := none) : MetaM (List Name) := do
  let some n := A.getAppFn.constName? | return []
  if ruleHeads.contains n then return []
  let env ← getEnv
  let mut cs : List Name := []
  let last := lastStr n
  if last == "erase" then
    if let some y := A.appArg!.getAppFn.constName? then
      if y == ``Prod.snd then
        if let some t := A.appArg!.appArg!.getAppFn.constName? then
          cs := (t.getPrefix ++ `isQueryBound_erase) :: (← eraseCompanions t.getPrefix)
  cs := cs ++ [Name.str n.getPrefix ("isQueryBoundBy_" ++ last),
    Name.str n.getPrefix ("isQueryBound_" ++ last),
    Name.str n.getPrefix ("isQueryBound₂_" ++ last), n ++ `isQueryBoundBy, n ++ `isQueryBound]
  let suffixed ← (← suffixedSources n).filterM (chargeAgrees c?)
  return cs.filter env.contains ++ suffixed

/-- The fields of the structure of a projection at the head of `A`. -/
def fieldSources (A : Expr) : MetaM (List Name) := do
  let some n := A.getAppFn.constName? | return []
  let some info ← getProjectionFnInfo? n | return []
  let s := info.ctorName.getPrefix
  let env ← getEnv
  return (getStructureFields env s).toList.filterMap fun f =>
    let c := s ++ f
    if c != n && env.contains c then some c else none

/-- The known bound terms of `A` at the charge `c?`: hypotheses, listed names, structure fields and
named theorems. -/
def sources (cfg : Cfg) (A : Expr) (c? : Option Expr := none) : MetaM (Array Expr) := do
  let mut es : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let (_, _, c) ← forallMetaTelescopeReducing d.type
    let c ← whnfR c
    if (parseBound? c).isSome || c.isAppOf isQueryBound₂Name then es := es.push d.toExpr
  for n in cfg.extra do es := es.push (← mkConstWithFreshMVarLevels n)
  for n in ← fieldSources A do es := es.push (← mkConstWithFreshMVarLevels n)
  if cfg.named then
    for n in ← namedSources A c? do es := es.push (← mkConstWithFreshMVarLevels n)
  es.foldlM (init := #[]) fun out e => do
    let parts ← twoKindBounds e
    return if parts.isEmpty then out.push e else out ++ parts

/-- The constant at the head of a tree. -/
def headName (A : Expr) : Option Name := A.getAppFn.constName?

/-- The target of the bound goal `g` with its tree replaced by `e`. -/
def withTree (g : MVarId) (e : Expr) : MetaM Expr := do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let args := t.getAppArgs
  unless (parseBound? t).isSome && args.size == 6 do
    throwError "query_bound: the goal is not a bound at a charge:{indentExpr t}"
  return mkAppN t.getAppFn (args.set! 4 e)

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

/-- Unifies the tree `X` of a known bound with the tree `A`: reducibly, and when that fails, by
the same head and arguments, with a metavariable argument assigned when its type agrees at default
transparency. So `A.bake … ?st` with `?st : A.AdvState` takes `st : A.toAdversary.AdvState`. -/
partial def unifyTree (X A : Expr) : MetaM Bool := do
  if ← withReducible (isDefEq X A) then return true
  let X ← instantiateMVars X
  if X.isMVar then
    unless ← withDefault (isDefEq (← inferType X) (← inferType A)) do return false
    return ← X.mvarId!.checkedAssign A
  let xs := X.getAppArgs
  let ys := A.getAppArgs
  if xs.isEmpty || xs.size != ys.size || X.getAppFn.isMVar then return false
  unless ← withReducible (isDefEq X.getAppFn A.getAppFn) do return false
  for x in xs, y in ys do
    unless ← unifyTree x y do return false
  return true

/-- Closes `g` from a hypothesis `(query d k).IsQueryBound 0`, which is `False`. -/
def refuteZeroBudget (g : MVarId) : MetaM Bool := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (none, X, n) := parseBound? (← whnfR (← instantiateMVars d.type)) | continue
    unless (← whnfCore X).isAppOf (adv `query) do continue
    unless (← whnfD n).nat? == some 0 || (← whnfD n).rawNatLit? == some 0 do continue
    unless (← whnfD d.type).isFalse do continue
    g.assign (← mkFalseElim (← g.getType) d.toExpr)
    return true
  return false

/-- `g` with the two components `c d ≤ n` and `∀ r, (k r).IsQueryBoundBy c (n - c d)` added to its
context, for each hypothesis bounding a tree `query d k`, a count and a two-kind bound being read
at their charges. So an induction hypothesis takes `hA r` as its premise, and `c d ≤ n` holds
without a case split on `n`. -/
def noteQueryHyps (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do continue
    let t ← whnfR (← instantiateMVars d.type)
    let forms : Array Expr ← match parseBound? t with
      | some (none, _, _) => pure #[← mkAppM (adv `IsQueryBound.isQueryBoundBy_one) #[d.toExpr]]
      | some (some _, _, _) => pure #[d.toExpr]
      | none => if t.isAppOf isQueryBound₂Name then twoKindBounds d.toExpr else pure #[]
    for pf in forms do
      let some (_, X, _) := parseBound? (← whnfR (← inferType pf)) | continue
      unless (← whnfCore X).isAppOf (adv `query) do continue
      let u ← whnfD (← inferType pf)
      unless u.isAppOfArity ``And 2 do continue
      let (_, g') ← g.note `hd (mkApp3 (mkConst ``And.left) u.appFn!.appArg! u.appArg! pf)
        (some u.appFn!.appArg!)
      let (_, g') ← g'.note `hk (mkApp3 (mkConst ``And.right) u.appFn!.appArg! u.appArg! pf)
        (some u.appArg!)
      g := g'
  return g

mutual

/-- A proof of a known bound of `A` from the source term `h`, with its charge and budget. The
charge of the source is the goal charge `c` when it is left free. A premise whose budget depends
on an unassigned binder is closed after the others, which assign that binder. A numeric binder left
free by the tree and the premises is matched against the goal budget `n?`, then taken as `0`. -/
partial def instSource (cfg : Cfg) (h A c : Expr) (fuel : Nat) (n? : Option Expr := none) :
    TacticM (Option (Expr × Expr × Expr)) := do
  let t ← inferType h
  let (ms, bis, concl) ← forallMetaTelescopeReducing t
  let concl ← whnfR (← instantiateMVars concl)
  let some (cs?, X, m) := parseBound? concl | return none
  unless ← unifyTree X A do return none
  if let some cs := cs? then
    if (← instantiateMVars cs).isMVar then
      unless ← isDefEq cs c do return none
  for mv in ms, bi in bis do
    if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
      let some i ← synthInstance? (← instantiateMVars (← mv.mvarId!.getType)) | return none
      mv.mvarId!.assign i
  for deferred in [false, true] do
    for mv in ms do
      let mid := mv.mvarId!
      if ← mid.isAssigned then continue
      unless ← isProp (← mid.getType) do continue
      let isDeferred := ((← instantiateMVars (← mid.getType)).find? fun e =>
        e.isApp && e.getAppFn.isMVar).isSome
      if deferred || !isDeferred then discharge cfg mid fuel
  if let some n := n? then
    let n ← instantiateMVars n
    unless n.isMVar do discard <| withReducible (isDefEq (← instantiateMVars m) n)
  for mv in ms do
    let mid := mv.mvarId!
    if ← mid.isAssigned then continue
    if (← instantiateMVars (← mid.getType)).isConstOf ``Nat then mid.assign (mkNatLit 0)
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
  let isBound (t : Expr) := (parseBound? t).isSome || t.isAppOf isQueryBound₂Name
  if isBound t then solve cfg g fuel
  else if t.isForall then
    let (_, g') ← g.intros
    let t' ← g'.withContext do whnfR (← instantiateMVars (← g'.getType))
    if isBound t' then solve cfg g' fuel else leaf g'
  else leaf g

/-- Budgets `a` proposed for `A` at the charge `c`, by the syntax of the tree. A proposal is
checked by the proof; an empty list means that the tree has no proposal. -/
partial def estimates (cfg : Cfg) (c A : Expr) (fuel : Nat) : TacticM (List Expr) := do
  if fuel == 0 then return []
  let mut fromSources : List Expr := []
  for h in ← sources cfg A c do
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
  if fn == some (adv `simulate) || fn == some (adv `subst) then
    let off := if fn == some (adv `simulate) then 1 else 0
    let X := args[args.size - 1 - off]!
    let c₀ ← mkFreshExprMVar none
    let mut out := []
    for h in ← sources cfg X do
      let s ← saveState
      let r ← try instSource cfg h X c₀ (fuel - 1) catch _ => pure none
      let b := r.map (·.2.2)
      s.restore
      if let some b := b then
        unless b.hasExprMVar || out.contains b do out := out ++ [b]
    let impl := args[args.size - 2 - off]!
    let cs ← try
        forallBoundedTelescope (← inferType impl) (some 2) fun xs _ => do
          let r ← estimates cfg c (mkAppN impl xs).headBeta (fuel - 1)
          return r.filter fun e => !xs.any fun x => e.containsFVar x.fvarId!
      catch _ => pure []
    let mut products := []
    for b in out do
      for e in cs do products := products ++ [← mkAppM ``HMul.hMul #[b, e]]
    return out ++ products
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
  if let some pf ← eraseTimed? A then
    let some (_, _, rhs) := (← inferType pf).eq? | return []
    return ← estimates cfg c rhs (fuel - 1)
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
  for h in ← sources cfg A c do
    let s ← saveState
    try
      if let some (pf, c₀, n₀) ← instSource cfg h A c (fuel - 1) n then
        if (← instantiateMVars c).isMVar then
          unless ← (← instantiateMVars c).mvarId!.checkedAssign c₀ do throwError "charge"
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
  let hs ← sources cfg A c
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

/-- Closes the premise `∀ …, (impl … d).IsQueryBoundBy c e` of a simulation or a substitution,
splitting the last binder `d` over the summands of a sum signature when the procedure fails on
it. -/
partial def solveImpl (cfg : Cfg) (g : MVarId) (fuel : Nat) : TacticM Unit := do
  let (xs, g) ← g.intros
  let rec go (g : MVarId) (d? : Option FVarId) (depth : Nat) : TacticM Unit := do
    let s ← saveState
    try solve cfg g fuel
    catch e =>
      s.restore
      let some d := d? | throw e
      let ty ← g.withContext do whnfR (← d.getType)
      unless ty.isAppOf ``Sum && depth > 0 do throw e
      for sg in ← g.cases d do
        let some (Expr.fvar d') := sg.fields[0]? | throw e
        go sg.mvarId (some d') (depth - 1)
  go g xs.back? 4

/-- Closes a bound goal of the simulation or substitution `A` at a charge at most `1`, by the
theorem `rule` (`isQueryBound_simulate_mul`, `isQueryBound_subst`): `q` queries, each answered by a
program of at most `e` queries, cost `q * e` queries. -/
partial def simulateMul (cfg : Cfg) (rule : Name) (g : MVarId) (A n : Expr) (fuel : Nat) :
    TacticM Unit := do
  let b ← mkFreshExprMVar (mkConst ``Nat)
  let m ← mkFreshExprMVar (← mkAppM (adv `IsQueryBound) #[A, b])
  match ← applyRule m.mvarId! (adv rule) with
  | [himpl, hA] =>
    solve cfg hA (fuel - 1)
    solveImpl cfg himpl (fuel - 1)
  | _ => throwError "query_bound: unexpected goals of the product rule"
  let pf ← mkAppM (adv `IsQueryBound.isQueryBoundBy_one) #[← instantiateMVars m]
  let n₀ ← instantiateMVars b
  if (← instantiateMVars n).isMVar then
    unless ← (← instantiateMVars n).mvarId!.checkedAssign n₀ do throwError "budget"
  match ← applyRule g (adv `isQueryBoundBy_of_le) [(`h, pf), (`c₀, ← chargeOne A), (`n₀, n₀)] with
  | [hc, hn] =>
    chargeLeaf hc
    leaf hn
  | _ => throwError "query_bound: unexpected goals of the known-bound rule"

/-- Solves a goal `IsQueryBoundBy`, `IsQueryBound`, `MayOnlyCall` or `IsQueryBound₂`. -/
partial def solve (cfg : Cfg) (g : MVarId) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "query_bound: depth bound reached"
  let (_, g) ← g.intros
  g.withContext do
    if ← refuteZeroBudget g then return
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
            solveImpl cfg himpl (fuel - 1)
            return
          | _ => throwError "query_bound: unexpected goals"
      catch e => err? := some e
      s.restore
    let s ← saveState
    try
      return ← simulateMul cfg `isQueryBound_simulate_mul g A' n fuel
    catch _ => s.restore
    if let some e := err? then throw e
    throwError "query_bound: the simulated adversary has no known bound:{indentExpr X}"
  else if fn == some (adv `subst) then
    let X := args.back!
    let c₀ ← mkFreshExprMVar none
    let mut err? : Option Exception := none
    for h in ← sources cfg X do
      let s ← saveState
      try
        if let some (pf, c₀', n₀) ← instSource cfg h X c₀ (fuel - 1) then
          let t ← whnfR (← instantiateMVars (← g.getType))
          let m ← mkFreshExprMVar (mkAppN t.getAppFn (t.getAppArgs.set! 5 n₀))
          match ← applyRule m.mvarId! (adv `isQueryBoundBy_subst)
              [(`cost, c₀'), (`cost', c), (`hA, pf)] with
          | [himpl] =>
            match ← applyRule g (adv `isQueryBoundBy_of_le) [(`h, m), (`c₀, c), (`n₀, n₀)] with
            | [hc, hn] =>
              leaf hn
              chargeLeaf hc
              solveImpl cfg himpl (fuel - 1)
              return
            | _ => throwError "query_bound: unexpected goals"
          | _ => throwError "query_bound: unexpected goals"
      catch e => err? := some e
      s.restore
    let s ← saveState
    try
      return ← simulateMul cfg `isQueryBound_subst g A' n fuel
    catch _ => s.restore
    if let some e := err? then throw e
    throwError "query_bound: the substituted adversary has no known bound:{indentExpr X}"
  else if fn == some (adv `mapQuery) then
    for g' in ← applyRule g (adv `isQueryBoundBy_mapQuery_comp) do solve cfg g' (fuel - 1)
  else
    let g ← if A' == A then pure g else g.replaceTargetDefEq (← withTree g A')
    if ← isBranch A' then
      let some gs ← splitTarget? g | throwError "query_bound: the branch does not split"
      for g' in gs do solve cfg g' (fuel - 1)
    else if let some pf ← eraseTimed? A' then
      let some (ty, _, rhs) := (← inferType pf).eq? | throwError "query_bound: not an equation"
      let motive := Expr.lam `x ty (← withTree g (.bvar 0)) .default
      let g' ← g.replaceTargetEq (← withTree g rhs) (← mkCongrArg motive pf)
      solve cfg g' (fuel - 1)
    else
      match ← try Except.ok <$> unfoldHead? A' catch e => pure (.error e) with
      | .ok (some e) =>
        let g' ← g.replaceTargetDefEq (← withTree g e)
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

/-- The heartbeats, in the unit of `maxHeartbeats`, that one run of `query_bound` may use. -/
def searchBudget : Nat := 60000

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
  let g ← noteQueryHyps (← getMainGoal)
  let rest := (← getGoals).tail
  let ctx ← readThe Core.Context
  let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
  let cap := used + searchBudget * 1000
  let cap := if ctx.maxHeartbeats == 0 then cap else min ctx.maxHeartbeats cap
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := cap })
      (solve { extra, named } g maxDepth))
    fun e => do
      if e.isRuntime && !e.isInterrupt then
        throwError "query_bound: the search exceeded its budget of {searchBudget} heartbeats; \
          list the bounds of the callees or state the bound of the costly subterm"
      throw e
  setGoals rest

end

end CatCrypt.Tactics.QueryBound

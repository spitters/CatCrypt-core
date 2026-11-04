/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.TraceEqLaws
public import CatCryptCore.Crypto.UCInterleave
public import CatCryptCore.NonUniform.Sample
public meta import Lean

/-!
# Tactics for rewriting reactive systems up to trace equivalence

Trace equivalence `R ≈ₜ I` of reactive systems (`TraceEqLaws.lean`) is proved by a step map on
an invariant (`Sys.StepMapOn.traceEq`), by the congruences of the constructions on systems, or by
a chain of known equivalences. The tactics of this file carry out these three proof methods.

* `sys_step_map f Inv (pres := h) using [d₁, …] with pat` proves `R ≈ₜ I`,
  `Realizes R I (fun _ _ => 0)` or `RealizesSim R I S (fun _ _ => 0)` by the step map `f` on
  the invariant `Inv`. It reduces the goal to the four obligations of `Sys.StepMapOn`, closes
  the two initial ones by `rfl` or `simp`, introduces the state, the event and the invariant in
  the two per-event obligations (only the step one when `pres` is given), splits the event on
  the ports (`Sum`) and the state into its components (`Prod`, or by the pattern `pat`), and
  runs on each branch the loop *prune, split, simplify*: the invariant is simplified, split into
  its conjuncts and the variables it determines are substituted (a refuted branch is closed);
  the branch is split on what the real step is stuck on (`blockerOf?`); then `simp_all` with the
  definitions `dᵢ` and the step equations of the constructions on systems (`sysStepSimps`); a
  branch still open is split on what its simplified real computation shows stuck, else by
  `split`. A leaf that stays open is left as a goal tagged by its obligation and the cases of its
  branch (`step.inr.none.pos`), in the simplified form; typically the coupling of a sampled
  value with the simulator's draw.
* `sys_step_pres using [d₁, …] with pat` runs the per-event part alone on a goal
  `∀ t e, Inv t → ∀ q, IsOutcome (R.step t e) q → Inv q.1` (or any goal of the form
  `∀ t e, Inv t → P t e`), so that the preservation of the invariant can be proved in its own
  declaration and passed to `sys_step_map` as `pres`.
* `sys_congr` reduces `R ≈ₜ I` with both sides built by the same construction (a multi-call
  hybrid `π.withSub`, an open system `P.withSub`, the parallel composition `par`, the loopback,
  the relabelling `mapPorts`) to the trace equivalence of the components, recursively, with the
  side goals of the congruence (`IdleAt`, `NoFail`, `Adm`, the idle events). A component pair
  whose sides are equal is closed by reflexivity.
* `trace_eq_chain` closes `R ≈ₜ I` by a path of local hypotheses `A ≈ₜ B`, each usable in both
  directions, from `R` to `I`, composed by transitivity; also behind `Realizes R I (fun _ _ => 0)`
  and `RealizesSim R I S (fun _ _ => 0)`.
* `sys_blocker` reports what the goal is stuck on, as `sys_step_map` reads it.

The case analysis of `sys_step_map` follows the reduction of the real step: a variable is split
only when a constructor at its place lets a `match` of the real step reduce (the `match` is
unfolded to the `casesOn` it is compiled to, so the variable is the one the first case analysis
needs), and a classical `if` is split by `by_cases` on its proposition. The number of branches
is the number of reachable branches of the real step, not the product of the state components.
Heartbeats are counted per declaration: an obligation whose leaves together exceed the budget
is stated as its own declaration (`sys_step_pres`).

## Main results

* `MultiHybrid.tensor_withSub_ofPorts_step_inl`, `MultiHybrid.tensor_withSub_ofPorts_step_inr`:
  the step of a tensor of multi-call hybrids over a system given port by port.
* `sys_step_map`, `sys_step_pres`, `sys_congr`, `trace_eq_chain`, `sys_blocker`: the tactics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

open CatCrypt.Core

variable {σ σ' τ E O E' O' EG OG EG' OG' : Type}

/-- A step of a tensor over a system given port by port, on a left event: an activation of the
left hybrid against the left port. -/
theorem tensor_withSub_ofPorts_step_inl (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') (XL : Sys τ EG OG) (XR : Sys τ EG' OG') (s : σ)
    (s' : σ') (t : τ) (e : E) :
    ((π.tensor π').withSub (Sys.ofPorts XL XR)).step ((s, s'), t) (.inl e) =
      SPComp.map (fun p => (((p.1.1, s'), p.1.2), Sum.inl p.2))
        (π.stepFuel XL (max π.fuel π'.fuel) (s, t) e) :=
  tensor_withSub_step_inl π π' _ XL (fun _ _ => rfl) s s' t e

/-- A step of a tensor over a system given port by port, on a right event: an activation of the
right hybrid against the right port. -/
theorem tensor_withSub_ofPorts_step_inr (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') (XL : Sys τ EG OG) (XR : Sys τ EG' OG') (s : σ)
    (s' : σ') (t : τ) (e : E') :
    ((π.tensor π').withSub (Sys.ofPorts XL XR)).step ((s, s'), t) (.inr e) =
      SPComp.map (fun p => (((s, p.1.1), p.1.2), Sum.inr p.2))
        (π'.stepFuel XR (max π.fuel π'.fuel) (s', t) e) :=
  tensor_withSub_step_inr π π' _ XR (fun _ _ => rfl) s s' t e

end CatCrypt.Crypto.UCTransparent.MultiHybrid

meta section

namespace CatCrypt.Tactics.SysRewrite

open Lean Meta Elab Tactic

initialize registerTraceClass `sys_step_map

/-- The step equations of the constructions on systems, used by `sys_step_map` beside the
definitions given to it: the monadic laws of `SPComp`, the ports of `Sys.ofPorts`, the lazily
keyed systems, the activations of multi-call hybrids and their tensors, the uniform draws, and
the possible outcomes of a uniform draw (`isOutcome_bind_sample_iff`). -/
def sysStepSimps : Array Name := #[
  ``CatCrypt.Core.SPComp.map, ``CatCrypt.Core.SPComp.pure_bind,
  ``CatCrypt.Core.SPComp.bind_assoc,
  ``CatCrypt.Crypto.UCTransparent.Sys.ofPorts_step_inl,
  ``CatCrypt.Crypto.UCTransparent.Sys.ofPorts_step_inr,
  ``CatCrypt.Crypto.UCTransparent.KeyedSys.lazy,
  ``CatCrypt.Crypto.UCTransparent.KeyedSys.lazyStep,
  ``CatCrypt.Crypto.UCTransparent.KeyedSys.ofPorts,
  ``CatCrypt.Crypto.UCTransparent.MultiHybrid.stepFuel,
  ``CatCrypt.Crypto.UCTransparent.MultiHybrid.drive,
  ``CatCrypt.Crypto.UCTransparent.MultiHybrid.idSim,
  ``CatCrypt.Crypto.UCTransparent.MultiHybrid.idSim_stepFuel,
  ``CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor_withSub_ofPorts_step_inl,
  ``CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor_withSub_ofPorts_step_inr,
  ``CatCrypt.Crypto.UCTransparent.Simulator.ofMultiHybrid,
  ``CatCrypt.NonUniform.ofPMF_uniformFintype, ``CatCrypt.NonUniform.sampleFrom_uniform,
  ``CatCrypt.Crypto.UCTransparent.isOutcome_bind_sample_iff]

/-- The inductive type at the head of `ty` after reducible unfolding. -/
def inductHead? (ty : Expr) : MetaM (Option InductiveVal) := do
  let ty ← whnfR ty
  let .const n _ := ty.getAppFn | return none
  let some (.inductInfo i) := (← getEnv).find? n | return none
  return some i

/-- A type is split by `sys_step_map` when it is an inductive type with at least two
constructors, no indices and no recursive occurrence, and is not a proposition. -/
def isSplittable (ty : Expr) : MetaM Bool := do
  let some i ← inductHead? ty | return false
  if i.isRec || i.numIndices != 0 || i.ctors.length < 2 then return false
  return !(← isProp ty)

/-- A type is destructured by `sys_step_map` when it is a pair or the unit type. -/
def isTuple (ty : Expr) : MetaM Bool := do
  let some i ← inductHead? ty | return false
  return i.name == ``Prod || i.name == ``PUnit || i.name == ``PProd || i.name == ``MProd

/-- What the reduction of a term is stuck on: a free variable of splittable type, or a
proposition whose decision is not a constructor (a classical `if`). -/
inductive Blocker where
  /-- A free variable of splittable type. -/
  | var (x : FVarId)
  /-- A proposition without free bound variables whose decision is stuck. -/
  | decide (p : Expr)

/-- The free variable of splittable type `x`, if `e` is one. -/
def splittableFVar? (e : Expr) : MetaM (Option Blocker) := do
  if e.isFVar && (← isSplittable (← inferType e)) then return some (.var e.fvarId!)
  return none

/-- `c` is an operation of `SPComp` (`bind`, `map`, `pure`, `sample`, …): the head normal
form of the steps stops there, at the monadic structure of a step. -/
def isSPCompOp (c : Name) : Bool :=
  (`CatCrypt.Core.SPComp).isPrefixOf c

/-- The head normal form of `e` above the monadic structure: `whnfCore`, projections of
structure values, and unfolding of definitions, stopping at a `match`, an `if`, a recursor and an
operation of `SPComp`. -/
partial def whnfAbove (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if fuel = 0 then return e
  let e ← whnfCore e
  let env ← getEnv
  match e.getAppFn with
  | .proj _ i s =>
    let s' ← whnf s
    let some v ← projectCore? s' i | return e
    whnfAbove (mkAppN v e.getAppArgs).headBeta (fuel - 1)
  | .const c _ =>
    if isMatcherCore env c || c == ``ite || c == ``dite || isSPCompOp c ||
        isCasesOnRecursor env c then return e
    if let some (.recInfo _) := env.find? c then return e
    let some e' ← (try unfoldDefinition? e catch _ => pure none) | return e
    whnfAbove e' (fuel - 1)
  | _ => return e

/-- The head normal form of `e` above the monadic structure (`whnfAbove`), with each `if`
whose decision is a hypothesis replaced by its branch. -/
partial def whnfDecided (e : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let e ← whnfAbove e
  if fuel = 0 then return e
  let .const c _ := e.getAppFn | return e
  unless c == ``ite || c == ``dite do return e
  let args := e.getAppArgs
  let (some p, some t, some f) := (args[1]?, args[3]?, args[4]?) | return e
  if let some h ← findLocalDeclWithType? p then
    return ← whnfDecided (if c == ``dite then (mkApp t (.fvar h)).headBeta else t) (fuel - 1)
  if let some h ← findLocalDeclWithType? (mkNot p) then
    return ← whnfDecided (if c == ``dite then (mkApp f (.fvar h)).headBeta else f) (fuel - 1)
  return e

/-- What `e` is stuck on, if anything. The head normal form above the monadic structure
(`whnfAbove`) is read: a bind or a map is stuck on its first computation; a stuck `match` is
unfolded to the `casesOn` it is compiled to, so that the variable found is the discriminant on
which the first case analysis of the `match` is stuck, not merely one of its discriminants; a
recursor is stuck on its major premise; an `if` on its decision, which is stuck on a variable or
is, for a classical `if`, the decision of its proposition. At most `fuel` steps. -/
partial def blockerOf? (e : Expr) (fuel : Nat) : MetaM (Option Blocker) := do
  if fuel = 0 || e.hasLooseBVars then return none
  let e ← whnfAbove e
  if e.isFVar then return ← splittableFVar? e
  let .const c lvls := e.getAppFn | return none
  let env ← getEnv
  let args := e.getAppArgs
  if c == ``ite || c == ``dite then
    let (some p, some inst, some t, some f) := (args[1]?, args[2]?, args[3]?, args[4]?)
      | return none
    if let some h ← findLocalDeclWithType? p then
      let t := if c == ``dite then (mkApp t (.fvar h)).headBeta else t
      return ← blockerOf? t (fuel - 1)
    if let some h ← findLocalDeclWithType? (mkNot p) then
      let f := if c == ``dite then (mkApp f (.fvar h)).headBeta else f
      return ← blockerOf? f (fuel - 1)
    if let some b ← blockerOf? inst (fuel - 1) then return some b
    if p.hasLooseBVars || p.hasMVar then return none
    -- only a classical decision is split as a proposition; a computable one is left to `simp`
    let .const ic _ := (← whnfAbove inst).getAppFn | return none
    unless ic == ``Classical.choice || ic == ``Classical.propDecidable do return none
    return some (.decide p)
  if isSPCompOp c then
    for a in args do
      unless (← inferType a).isSort || a.isLambda do
        if (← whnfR (← inferType a)).isAppOf ``CatCrypt.Core.SPComp then
          return ← blockerOf? a (fuel - 1)
    return none
  if isMatcherCore env c then
    let info ← getConstInfo c
    let body ← whnfCore ((info.instantiateValueLevelParams! lvls).beta args)
    if body == e then return none
    return ← blockerOf? body (fuel - 1)
  let major? : Option Expr ←
    if let some (.recInfo r) := env.find? c then pure args[r.getMajorIdx]?
    else if isCasesOnRecursor env c then do
      let .str ind _ := c | return none
      let some (.inductInfo i) := env.find? ind | return none
      pure args[i.numParams + 1 + i.numIndices]?
    else pure none
  let some m := major? | return none
  let m ← instantiateMVars m
  if m.isFVar then return ← splittableFVar? m
  let m' ← whnfDecided m
  if m' != m && (← isConstructorApp m') then
    return ← blockerOf? (mkAppN e.getAppFn (args.map fun a => if a == m then m' else a)) (fuel - 1)
  blockerOf? m (fuel - 1)

/-- `e` is an application of a `match`, an `if`, a `casesOn` or a recursor: a place where a
simplified goal can be stuck. -/
def isCaseApp (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ =>
    isMatcherCore env c || c == ``ite || c == ``dite || isCasesOnRecursor env c ||
      (env.find? c matches some (.recInfo _))
  | _ => false

/-- The closed case applications (`isCaseApp`) of `e`, outermost first, each shared subterm
visited once. -/
def caseApps (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let acc ← IO.mkRef #[]
  e.forEachWhere (fun a => a.isApp && !a.hasLooseBVars && isCaseApp env a)
    fun a => acc.modify (·.push a)
  acc.get

/-- The real computation of a per-event goal: the left side of the step equation
`SPComp.map _ (R.step t e) = I.step (f t) e`, or the computation `c` of `IsOutcome c q` in the
preservation `∀ q, IsOutcome (R.step t e) q → Inv q.1`; otherwise the goal. -/
def realComp (tgt : Expr) : Expr :=
  if let some (_, l, _) := tgt.eq? then l
  else match tgt.find? fun a => a.isAppOfArity ``CatCrypt.Crypto.UCTransparent.IsOutcome 3 &&
      !a.appFn!.hasLooseBVars with
    | some a => a.appFn!.appArg!
    | none => tgt

/-- What the real computation of `e` (`realComp`) is stuck on: with `eager`, read through its
definitions (`blockerOf?`); otherwise at the first stuck case analysis (`isCaseApp`) that the
simplified computation shows, outermost first. -/
def firstBlocker? (e : Expr) (eager : Bool) : MetaM (Option Blocker) := do
  let c := realComp (← instantiateMVars e)
  if eager then return ← blockerOf? c 16
  for a in ← caseApps c do
    if let some b ← blockerOf? a 8 then return some b
  return none

/-- Case analysis on `x` in `g`, the new goals tagged by the constructors. -/
def casesTagged (g : MVarId) (x : FVarId) : MetaM (List MVarId) := do
  let tag ← g.getTag
  let subs ← g.cases x
  subs.toList.mapM fun s => do
    if let some c := s.ctorName then s.mvarId.setTag (Name.mkStr tag c.getString!)
    return s.mvarId

/-- Split the free variable `x` of `g` recursively over pairs and the unit type. -/
partial def destruct (g : MVarId) (x : FVarId) : MetaM MVarId := do
  unless ← g.withContext (do isTuple (← x.getType)) do return g
  let tag ← g.getTag
  let #[s] ← g.cases x | return g
  s.mvarId.setTag tag
  let mut g := s.mvarId
  for f in s.fields do
    if f.isFVar then g ← destruct g f.fvarId!
  return g

/-- Split the free variable `x` of `g` recursively over sums (the ports of an event). -/
partial def splitPorts (g : MVarId) (x : FVarId) : MetaM (List MVarId) := do
  let isSum ← g.withContext do
    let some i ← inductHead? (← x.getType) | return false
    return i.name == ``Sum || i.name == ``PUnit
  unless isSum do return [g]
  let tag ← g.getTag
  let subs ← g.cases x
  let mut out := []
  for s in subs do
    if let some c := s.ctorName then s.mvarId.setTag (Name.mkStr tag c.getString!)
    let mut gs := [s.mvarId]
    for f in s.fields do
      if f.isFVar then
        gs := (← gs.mapM fun g => splitPorts g f.fvarId!).flatten
    out := out ++ gs
  return out

/-- Run `tac` on `g`; on failure `g` is unchanged. The goals left by `tac`. -/
def runOn (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  let s ← saveState
  setGoals [g]
  try
    Term.withoutErrToSorry tac
    getUnsolvedGoals
  catch _ =>
    s.restore
    return [g]

/-- The case analyses of a branch on what the goal `g` is stuck on: the constructors of a
variable, or the two cases of a decision. -/
def splitBlocker? (g : MVarId) (eager : Bool) : TacticM (Option (List MVarId)) := do
  let some b ← g.withContext (do firstBlocker? (← g.getType) eager) | return none
  try
    match b with
    | .var x => some <$> casesTagged g x
    | .decide p =>
      let tag ← g.getTag
      let s ← g.byCases p `hdec
      let gp := s.1.mvarId
      let gn := s.2.mvarId
      gp.setTag (Name.mkStr tag "pos")
      gn.setTag (Name.mkStr tag "neg")
      return some [gp, gn]
  catch _ => return none

/-- The hypotheses of `g` named `inv`: the invariant and its parts. -/
def invHyps (g : MVarId) : MetaM (Array FVarId) := do
  return (← g.getDecl).lctx.foldl (init := #[]) fun acc d =>
    if d.userName == `inv && !d.isImplementationDetail then acc.push d.fvarId else acc

/-- Split the conjunctions among the hypotheses `inv` of `g`, each part named `inv`. -/
partial def splitInv (g : MVarId) : MetaM MVarId := do
  for h in ← invHyps g do
    let ty ← g.withContext do whnfR (← instantiateMVars (← h.getType))
    if ty.isAppOfArity ``And 2 then
      let #[s] ← g.cases h | return g
      let mut g' := s.mvarId
      for f in s.fields do
        if f.isFVar then g' ← g'.rename f.fvarId! `inv
      return ← splitInv g'
  return g

/-- Prune a branch by its invariant: simplify the hypotheses `inv` of `g` with `ctx`, split
their conjunctions and substitute the variables they determine. `none` when the invariant is
refuted. -/
def pruneInv (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (g : MVarId) :
    MetaM (Option MVarId) := do
  let hs ← invHyps g
  if hs.isEmpty then return some g
  let s ← saveState
  try
    let (some (_, g'), _) ← simpGoal g ctx simprocs (fvarIdsToSimp := hs)
        (simplifyTarget := false)
      | return none
    let g' ← splitInv g'
    let g' ← try substVars g' catch _ => pure g'
    return some g'
  catch _ =>
    s.restore
    return some g

/-- The steps of a leaf of `sys_step_map`: the closing simplification and the pruning by the
invariant. -/
structure LeafSteps where
  /-- The closing simplification. -/
  simp : TacticM Unit
  /-- The pruning by the invariant (`pruneInv`). -/
  prune : MVarId → MetaM (Option MVarId)

/-- The loop *prune, split, then simplify* on one leaf, with at most `depth` case analyses
along a branch: pruning by the invariant, case analysis on the free variables that block the
reduction of the goal as long as there are any, then the closing simplification; when the goal
stays open, case analysis on a blocking variable of the simplified goal, else `split`. The
goals left open. -/
partial def solveLeaf (st : LeafSteps) (g : MVarId) (depth : Nat) : TacticM (List MVarId) := do
  let tag ← g.getTag
  let some g ← st.prune g | do
    trace[sys_step_map] "{tag}: refuted by the invariant"
    return []
  g.setTag tag
  if depth > 0 then
    if let some subs ← splitBlocker? g true then
      trace[sys_step_map] "{tag}: split on the real step"
      return (← subs.mapM fun g => solveLeaf st g (depth - 1)).flatten
  let gs ← runOn g st.simp
  trace[sys_step_map] "{tag}: simp, {gs.length} left"
  let [g] := gs | return gs
  if depth = 0 then return [g]
  if let some subs ← splitBlocker? g false then
    trace[sys_step_map] "{tag}: split"
    return (← subs.mapM fun g => solveLeaf st g (depth - 1)).flatten
  let gs ← runOn g (evalTactic (← `(tactic| split)))
  if gs == [g] then return [g]
  trace[sys_step_map] "{tag}: split by `split`"
  gs.forM fun g => g.setTag tag
  return (← gs.mapM fun g => solveLeaf st g (depth - 1)).flatten

/-- The maximal number of case analyses along a branch of `sys_step_map`. -/
def maxDepth : Nat := 12

/-- The per-event obligation `g` (`pres` or `step`): introduce the state, the event and the
invariant, destructure the state (by `pat`, or over pairs), split the event on its ports, and
run `solveLeaf` on each case. -/
def perEvent (st : LeafSteps) (pat : Option (TSyntax `Lean.Parser.Tactic.rcasesPatMed))
    (g : MVarId) : TacticM (List MVarId) := do
  let tag := (← g.getTag).eraseMacroScopes
  let (#[t, _, _], g) ← g.introN 3 [`sysState, `sysEvent, `inv] | failure
  g.setTag tag
  let gs ← match pat with
    | some p =>
      setGoals [g]
      evalTactic (← `(tactic| rcases $(mkIdent `sysState):ident with $p:rcasesPatMed))
      let gs ← getUnsolvedGoals
      gs.forM fun g' => g'.setTag tag
      pure gs
    | none => pure [← destruct g t]
  let gs ← gs.mapM fun g => do
    let some e := (← g.getDecl).lctx.findFromUserName? `sysEvent | return [g]
    splitPorts g e.fvarId
  return (← gs.flatten.mapM fun g => solveLeaf st g maxDepth).flatten

/-- Reduce a goal `Realizes R I (fun _ _ => 0)` or `RealizesSim R I S (fun _ _ => 0)` to
`R ≈ₜ I`, resp. `R ≈ₜ S.withSub I`. -/
def toTraceEq : TacticM Unit := do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isAppOf ``CatCrypt.Crypto.UCTransparent.RealizesSim then
    evalTactic (← `(tactic| refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.realizesSim ?_))
  else if tgt.isAppOf ``CatCrypt.Crypto.UCTransparent.Realizes then
    evalTactic (← `(tactic| refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.realizes ?_))

/-- The simp arguments of `sys_step_map`: those given, then `sysStepSimps`. -/
def simpArgs (args : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    Array (TSyntax `Lean.Parser.Tactic.simpLemma) :=
  args ++ sysStepSimps.map fun n => ⟨mkNode ``Lean.Parser.Tactic.simpLemma
    #[mkNullNode, mkNullNode, mkIdent n]⟩

/-- The steps of a leaf of `sys_step_map` for the simp arguments `all`: `simp_all` with them,
and the pruning by the invariant simplified with them. -/
def leafSteps (all : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM LeafSteps := do
  let stx ← `(tactic| simp [$all,*])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  return { simp := evalTactic (← `(tactic| simp_all [$all,*]))
           prune := pruneInv ctx simprocs }

/-- The per-event part of `sys_step_map` on a goal
`∀ t e, Inv t → ∀ q, IsOutcome (R.step t e) q → Inv q.1` (the preservation of an invariant):
see the module docstring. -/
syntax (name := sysStepPres) "sys_step_pres"
  (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? (" with " Lean.Parser.Tactic.rcasesPatMed)? :
  tactic

/-- `sys_step_map f Inv using [d₁, …] with pat` proves trace equivalence (or a realization at
distance `0`) by the step map `f` on the invariant `Inv`; see the module docstring. With
`(pres := h)`, the preservation of the invariant is `h`. The open leaves are left as goals
tagged `init_inv`, `init_map`, `pres.…` and `step.…`. -/
syntax (name := sysStepMap) "sys_step_map " term:max ppSpace term:max
  (" (" &"pres" " := " term ")")?
  (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? (" with " Lean.Parser.Tactic.rcasesPatMed)? :
  tactic

/-- The simp arguments and the pattern of the optional clauses `using` and `with` at `u` and
`w`. -/
def clauses (u w : Syntax) :
    Array (TSyntax `Lean.Parser.Tactic.simpLemma) ×
      Option (TSyntax `Lean.Parser.Tactic.rcasesPatMed) :=
  (simpArgs (if u.isNone then #[] else u[2].getSepArgs.map (⟨·⟩)),
    if w.isNone then none else some ⟨w[1]⟩)

@[tactic sysStepPres] def evalSysStepPres : Tactic := fun stx => do
  let (all, pat) := clauses stx[1] stx[2]
  let g :: rest ← getGoals | throwError "no goals to be proved"
  let st ← leafSteps all
  g.setTag `pres
  let gs ← perEvent st pat g
  setGoals (gs ++ rest)

@[tactic sysStepMap] def evalSysStepMap : Tactic := fun stx => do
  let f : Term := ⟨stx[1]⟩
  let inv : Term := ⟨stx[2]⟩
  let pres? : Option Term := if stx[3].isNone then none else some ⟨stx[3][3]⟩
  let (all, pat) := clauses stx[4] stx[5]
  let initTac : TacticM Unit := do
    evalTactic (← `(tactic|
      first | rfl | trivial | (simp [$all,*]; done) | (simp_all [$all,*]; done)))
  let g :: rest ← getGoals | throwError "no goals to be proved"
  setGoals [g]
  let st ← leafSteps all
  toTraceEq
  match pres? with
  | some h => evalTactic (← `(tactic|
      refine CatCrypt.Crypto.UCTransparent.Sys.StepMapOn.traceEq (Inv := $inv) (f := $f)
        ⟨?init_inv, ?init_map, $h, ?step⟩))
  | none => evalTactic (← `(tactic|
      refine CatCrypt.Crypto.UCTransparent.Sys.StepMapOn.traceEq (Inv := $inv) (f := $f)
        ⟨?init_inv, ?init_map, ?pres, ?step⟩))
  let gs ← getGoals
  let (gi, gm, gp, gst) ← match gs with
    | [gi, gm, gp, gst] => pure (gi, gm, [gp], gst)
    | [gi, gm, gst] => pure (gi, gm, [], gst)
    | _ => throwError "sys_step_map: unexpected goals after the step map"
  gi.setTag `init_inv; gm.setTag `init_map; gst.setTag `step
  let gi ← runOn gi initTac
  let gm ← runOn gm initTac
  let gp ← gp.mapM fun g => do g.setTag `pres; perEvent st pat g
  let gst ← perEvent st pat gst
  setGoals (gi ++ gm ++ gp.flatten ++ gst ++ rest)

/-! ### Congruence and chains -/

/-- The sides `R` and `I` of a goal `R ≈ₜ I`. -/
def traceEqSides? (tgt : Expr) : Option (Expr × Expr) :=
  if tgt.isAppOfArity ``CatCrypt.Crypto.UCTransparent.Sys.TraceEq 6 then
    some (tgt.getArg! 4, tgt.getArg! 5)
  else none

/-- The congruence lemma of `Sys.TraceEq` for a construction head, as the text of a `refine`
whose hole `?h` (and `?hY` for the parallel composition) is the equivalence of the components. -/
def congrFor? (c : Name) : Option (TacticM Unit) :=
  if c == ``CatCrypt.Crypto.UCTransparent.MultiHybrid.withSub then some do
    evalTactic (← `(tactic|
      refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.withSub _ ?idle ?idleX ?idleY ?h))
  else if c == ``CatCrypt.Crypto.UCTransparent.Open.withSub then some do
    evalTactic (← `(tactic|
      refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.withSub_open _ ?admX ?admY ?h))
  else if c == ``CatCrypt.Crypto.UCTransparent.Sys.mapPorts then some do
    evalTactic (← `(tactic| refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.mapPorts ?h _ _))
  else if c == ``CatCrypt.Crypto.UCTransparent.Sys.loopback then some do
    evalTactic (← `(tactic|
      refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.loopback ?idle ?idleR ?idleI ?h _ _))
  else if c == ``CatCrypt.Crypto.UCTransparent.Sys.par then some do
    evalTactic (← `(tactic|
      refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.par ?noFailY ?noFailX' ?idleL ?idleR
        ?idleX ?idleX' ?idleY ?idleY' ?h ?hY))
  else none

/-- One round of `sys_congr` on `g`: reflexivity when the sides are equal up to reducible
unfolding, else the congruence of their common construction head, recursively on the
component goals. The goals left: the side goals and the component goals with different
heads. -/
partial def congrGoal (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (r, i) := traceEqSides? tgt | return [g]
  if ← withReducible (isDefEq r i) then
    g.assign (← mkAppM ``CatCrypt.Crypto.UCTransparent.Sys.TraceEq.refl #[r])
    return []
  let (.const cr _, .const ci _) := (r.getAppFn, i.getAppFn) | return [g]
  unless cr == ci do return [g]
  let some tac := congrFor? cr | return [g]
  let gs ← runOn g tac
  if gs == [g] then return [g]
  let mut out := []
  for g' in gs do
    if (traceEqSides? (← instantiateMVars (← g'.getType))).isSome then
      out := out ++ (← congrGoal g')
    else
      let closed ← runOn g' (evalTactic (← `(tactic| assumption)))
      out := out ++ closed
  return out

/-- `sys_congr` reduces `R ≈ₜ I`, where `R` and `I` are built by the same construction
(`MultiHybrid.withSub`, `Open.withSub`, `Sys.par`, `Sys.loopback`, `Sys.mapPorts`), to the
trace equivalence of their components, recursively; equal components are closed by reflexivity,
and the side goals of the congruences (idle events, `IdleAt`, `NoFail`, `Adm`) are closed by
`assumption` or left. Fails when no congruence applies. -/
syntax (name := sysCongr) "sys_congr" : tactic

@[tactic sysCongr] def evalSysCongr : Tactic := fun _ => do
  let g :: rest ← getGoals | throwError "no goals to be proved"
  let gs ← congrGoal g
  if gs == [g] then throwError "sys_congr: no congruence of trace equivalence applies"
  setGoals (gs ++ rest)

/-- A path of trace equivalences from `src` to `dst` among the edges `es` (each an equation
`A ≈ₜ B` with its proof, usable in both directions), as a proof of `src ≈ₜ dst`, by
breadth-first search; the nodes are compared up to reducible unfolding. -/
def chainProof? (es : Array (Expr × Expr × Expr)) (src dst : Expr) : MetaM (Option Expr) := do
  let edges := es.flatMap fun (a, b, p) => #[(a, b, p, false), (b, a, p, true)]
  let mut frontier : Array (Expr × Expr) :=
    #[(src, ← mkAppM ``CatCrypt.Crypto.UCTransparent.Sys.TraceEq.refl #[src])]
  let mut seen : Array Expr := #[src]
  for _ in [0:es.size + 1] do
    let mut next := #[]
    for (n, pn) in frontier do
      if ← withReducible (isDefEq n dst) then return some pn
      for (a, b, p, rev) in edges do
        if ← withReducible (isDefEq n a) then
          if ← seen.anyM fun m => withReducible (isDefEq m b) then continue
          let p ← if rev then mkAppM ``CatCrypt.Crypto.UCTransparent.Sys.TraceEq.symm #[p]
            else pure p
          next := next.push (b, ← mkAppM ``CatCrypt.Crypto.UCTransparent.Sys.TraceEq.trans #[pn, p])
          seen := seen.push b
    if next.isEmpty then return none
    frontier := next
  return none

/-- `trace_eq_chain` closes `R ≈ₜ I`, or `Realizes R I (fun _ _ => 0)`, or
`RealizesSim R I S (fun _ _ => 0)`, by a path of local hypotheses `A ≈ₜ B` from `R` to `I`, each
usable in both directions, composed by transitivity (reflexivity for the empty path). -/
syntax (name := traceEqChain) "trace_eq_chain" : tactic

@[tactic traceEqChain] def evalTraceEqChain : Tactic := fun _ => do
  toTraceEq
  withMainContext do
    let g ← getMainGoal
    let some (r, i) := traceEqSides? (← instantiateMVars (← g.getType))
      | throwError "trace_eq_chain: the goal is not a trace equivalence"
    let mut es := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let some (a, b) := traceEqSides? (← instantiateMVars d.type) then
        es := es.push (a, b, d.toExpr)
    let some p ← chainProof? es r i
      | throwError "trace_eq_chain: no path of trace equivalences in the context"
    g.assign p
    replaceMainGoal []

/-- `sys_blocker` reports what the reduction of the goal is stuck on, as `sys_step_map` reads
it: a variable to split, or a decision. -/
syntax (name := sysBlocker) "sys_blocker" : tactic

@[tactic sysBlocker] def evalSysBlocker : Tactic := fun _ => withMainContext do
  let tgt ← getMainTarget
  for eager in [true, false] do
    match ← firstBlocker? tgt eager with
    | some (.var x) => logInfo m!"stuck on the variable {Expr.fvar x}"
    | some (.decide p) => logInfo m!"stuck on the decision of {p}"
    | none => logInfo m!"not stuck"

end CatCrypt.Tactics.SysRewrite

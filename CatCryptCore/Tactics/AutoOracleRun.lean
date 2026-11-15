/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoOracleGame
public import CatCryptCore.Crypto.OracleGameUpToBad
public import CatCryptCore.Crypto.OracleRunMapBad
public import CatCryptCore.Crypto.OracleAdversaryEager
public import CatCryptCore.Crypto.KDFLazyEager

/-!
# `catcrypt_auto` arms for equalities of oracle runs

Goals about whole runs `OracleAdv.run O A s` of an oracle adversary against a stateful oracle:
an equality of two runs, possibly read through `PMF.map` or at a point, the identical-until-bad
equality of two runs read through state maps, the acceptance probability of two keyed games, a
run with a key drawn at its first triggering call, and an invariant along the support of a run.
Each tactic applies the lemma of the run, fills the arguments that unification with the goal
does not fix by candidates, and passes the per-call premises to `oracle_run_leaf`, which ends
with the keyed-oracle tactics of `CatCryptCore.Tactics.AutoOracleGame`.

## Main definitions

* `oracle_run_leaf [l₁, …]` — closes a per-call premise: an assumption, reflexivity, the
  monad laws of `PMF.pure` followed by `solve_by_elim`, `simp_all`, `grind`, an application of
  a lemma `lᵢ`, `keyed_oracle_step` or `keyed_oracle_support`, with the lemmas `lᵢ`.
* `oracle_run_eq [l₁, …] with N` — `OracleAdv.run_eq_run_of_inv`, after peeling equal maps and
  equal points off both sides; maps `PMF.map f`, `PMF.map g` that are not definitionally equal
  leave the premise `f = g`, and start states that are not definitionally equal the premise
  `s = s'`. The invariant `N`, when given, is tried first; then the abstractions of the start
  state in the hypotheses, the lemmas `lᵢ` that are predicates on states, and `fun _ => True`.
* `oracle_run_off_bad [l₁, …] with bad` — `OracleAdv.run_map_eq_off_bad`, with `bad` given,
  a Boolean predicate among the `lᵢ`, or the abstraction of the outcome in a hypothesis
  `b t = false`.
* `oracle_run_accept [l₁, …] with V` — `KeyedGame.accept_eq_of_kernel` at the identity kernel,
  with the invariant `V` given, a predicate among the `lᵢ`, or `fun _ => True`.
* `oracle_run_trigger [l₁, …]` — `OracleAdv.run_eq_bind_run_of_trigger`, with the predicates
  `P`, `c`, `N` taken among the `lᵢ`, the hypotheses and `fun _ => True`; a map `PMF.map f`
  inside a `PMF.bind` is moved outside it (`PMF.map_bind`) and equal maps are peeled off first.
* `oracle_run_support [l₁, …] with Inv` — `OracleAdv.run_support_inv` on a goal
  `∀ z ∈ (run O A s).support, Φ z`, with `Inv` given or computed from `Φ` by abstracting `z.2`.
* `eager_draw_auto U use [l₁, …]` — `eager_draw U use` followed by `oracle_run_leaf`.

A predicate candidate among the `lᵢ` is also taken among the local variables of the goal.
The shapes `oracle run equality` and `oracle run support` of the direct stage of
`catcrypt_auto` run these tactics with the arguments of `catcrypt_auto [t₁, …]`, and
`FiatShamirROM.run_eager_of_step` where it is in the environment; a term argument that is not
a lemma or a definition reaches them through the `"*"` arm. Each closing tactic of a premise
runs under a cap of `closerHeartbeats` thousand heartbeats.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoOracleRun

open Lean Meta Elab Tactic

meta section

/-- The terms of the optional list `[t₁, …]` at position `i` of `stx`. -/
def listArgs (stx : Syntax) (i : Nat) : Array Term :=
  if stx[i].isNone then #[] else stx[i][1].getSepArgs.map (⟨·⟩)

/-- The term of the optional `with t` at position `i` of `stx`. -/
def withArg? (stx : Syntax) (i : Nat) : Option Term :=
  if stx[i].isNone then none else some ⟨stx[i][1]⟩

/-- Run `tac` on `g` alone; the goals it leaves, or `none` when it fails, with the state
restored. -/
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

/-- The heartbeat cap, in thousands, of one closing tactic of a premise. -/
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

/-- Close `g` by the first tactic of `tacs` that closes it; `false` when none does. -/
def closeBy (g : MVarId) (tacs : Array (TSyntax `tactic)) : TacticM Bool := do
  for t in tacs do
    let s ← saveState
    match ← capped (tryOn g t) with
    | some [] => return true
    | _ => s.restore
  return false

/-- `grind [l₁, …]`, or `grind` when there is no lemma. -/
def grindWith (ls : Array Term) : TacticM (TSyntax `tactic) := do
  let gs : Array (TSyntax ``Parser.Tactic.grindParam) ←
    ls.mapM fun l => `(Parser.Tactic.grindParam| $l:term)
  if gs.isEmpty then `(tactic| grind) else `(tactic| grind [$gs,*])

/-- `simp_all [l₁, …]`, or `simp_all` when there is no lemma. -/
def simpAllWith (ls : Array Term) : TacticM (TSyntax `tactic) := do
  let ss : Array (TSyntax ``Parser.Tactic.simpLemma) ←
    ls.mapM fun l => `(Parser.Tactic.simpLemma| $l:term)
  if ss.isEmpty then `(tactic| simp_all) else `(tactic| simp_all [$ss,*])

/-- The list `[l₁, …]` of the keyed-oracle tactics, empty when there is no lemma. -/
def keyedStep (ls : Array Term) (support : Bool) : TacticM (TSyntax `tactic) := do
  match support, ls.isEmpty with
  | false, true => `(tactic| keyed_oracle_step)
  | false, false => `(tactic| keyed_oracle_step [$ls,*])
  | true, true => `(tactic| keyed_oracle_support)
  | true, false => `(tactic| keyed_oracle_support [$ls,*])

/-- The closing tactics of a per-call premise, with the lemmas `ls`. -/
def leafClosers (ls : Array Term) : TacticM (Array (TSyntax `tactic)) := do
  let gl ← ls.filterM fun l => do
    unless l.raw.isIdent do return true
    try
      let n ← realizeGlobalConstNoOverload l.raw
      return (← getReducibilityStatus n) != .reducible
    catch _ => return true
  let fin ← grindWith gl
  let finS ← `(Parser.Tactic.tacticSeq| $fin:tactic)
  let sa ← simpAllWith ls
  let ks ← keyedStep gl false
  let ku ← keyedStep gl true
  let mut out : Array (TSyntax `tactic) := #[
    ← `(tactic| with_reducible assumption), ← `(tactic| with_reducible rfl),
    ← `(tactic| (intros; (try beta_reduce); first | with_reducible assumption | trivial)),
    ← `(tactic|
      (intros; simp only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, Prod.mk.eta, id];
        first | with_reducible rfl | solve_by_elim))]
  for l in ls do
    out := out.push (← `(tactic|
      (intros; (try beta_reduce); apply $l <;> first | assumption | $finS)))
    out := out.push (← `(tactic|
      (intros; (try beta_reduce); apply Eq.symm; apply $l <;> first | assumption | $finS)))
  let unf ← if ls.isEmpty then `(tactic| skip) else do
    let ss : Array (TSyntax ``Parser.Tactic.simpLemma) ←
      ls.mapM fun l => `(Parser.Tactic.simpLemma| $l:term)
    `(tactic| try simp only [$ss,*])
  out := out ++ #[
    ← `(tactic| exact (PMF.map_id _).symm),
    ← `(tactic| (refine funext fun _ => ?_; (try beta_reduce); $sa; done)),
    ← `(tactic| (refine funext fun _ => ?_; (try beta_reduce); $fin)),
    ← `(tactic| (intros; (try beta_reduce); $sa; done)),
    ← `(tactic| (intros; (try beta_reduce); $fin)),
    ← `(tactic| ($ks; done)),
    ← `(tactic| ($ku; done)),
    ← `(tactic| (intros; $unf; congr 1; funext; $sa; done)),
    ← `(tactic| (intros; $unf; intros; exact absurd rfl ‹_›)),
    ← `(tactic| (intros; simp only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, Prod.mk.eta,
        id_eq, id]; first | rfl | ($ks; done) | $finS))]
  return out

/-- `oracle_run_leaf [l₁, …]` closes a per-call premise of a run lemma by an assumption,
reflexivity, `simp_all [l₁, …]`, `grind [l₁, …]`, an application of a lemma `lᵢ` with its
premises closed by assumptions or `grind`, `keyed_oracle_step [l₁, …]` or
`keyed_oracle_support [l₁, …]`, after introducing the binders and reducing beta-redexes; it
fails when none closes the goal. -/
syntax (name := oracleRunLeafStx) "oracle_run_leaf" (" [" term,* "]")? : tactic

/-- The elaborator of `oracle_run_leaf`. -/
@[tactic oracleRunLeafStx] def evalOracleRunLeaf : Tactic := fun stx => do
  let g ← getMainGoal
  unless ← closeBy g (← leafClosers (listArgs stx 1)) do
    throwError "oracle_run_leaf: no closing tactic"

/-- Close every goal by `oracle_run_leaf [ls]`; the goals left open. -/
def leafAll (ls : Array Term) (failFast : Bool := false) : TacticM (List MVarId) := do
  let closers ← leafClosers ls
  let mut left := []
  for g in ← getUnsolvedGoals do
    unless ← closeBy g closers do
      left := left ++ [g]
      if failFast then return left
  return left

/-! ### Reading the goal -/

/-- `e` is an application of `OracleAdv.run`. -/
def isRun (e : Expr) : Bool := e.isAppOfArity ``CatCrypt.Crypto.OracleAdv.run 7

/-- Replace a goal `F p x = F q x` or `PMF.map f p = PMF.map f q` by `p = q`, repeatedly. -/
partial def peel (g : MVarId) : MetaM MVarId := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (_, l, r) := t.cleanupAnnotations.eq? | return g
  let l := l.cleanupAnnotations
  let r := r.cleanupAnnotations
  if l.isAppOfArity ``DFunLike.coe 6 && r.isAppOfArity ``DFunLike.coe 6 then
    let cl := l.appFn!.appFn!
    let cr := r.appFn!.appFn!
    let x := l.appArg!
    if (← isDefEq cl cr) && (← isDefEq x r.appArg!) then
      let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq l.appFn!.appArg! r.appFn!.appArg!)
      g.assign (← mkCongrFun (← mkCongrArg cl h) x)
      return ← peel h.mvarId!
  if l.isAppOfArity ``PMF.map 4 && r.isAppOfArity ``PMF.map 4 then
    if ← isDefEq l.appFn! r.appFn! then
      let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq l.appArg! r.appArg!)
      g.assign (← mkCongrArg l.appFn! h)
      return ← peel h.mvarId!
  return g

/-- Replace a goal `PMF.map f p = PMF.map g q` over the same types by the goals `f = g` and
`p = q`; `none` when the goal is not of this form. -/
def congrMap? (g : MVarId) : MetaM (Option (MVarId × MVarId)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (_, l, r) := t.cleanupAnnotations.eq? | return none
  let l := l.cleanupAnnotations
  let r := r.cleanupAnnotations
  unless l.isAppOfArity ``PMF.map 4 && r.isAppOfArity ``PMF.map 4 do return none
  unless ← isDefEq (l.getArg! 0) (r.getArg! 0) do return none
  unless ← isDefEq (l.getArg! 1) (r.getArg! 1) do return none
  let hf ← mkFreshExprSyntheticOpaqueMVar (← mkEq (l.getArg! 2) (r.getArg! 2))
  let hp ← mkFreshExprSyntheticOpaqueMVar (← mkEq l.appArg! r.appArg!)
  g.assign (← mkCongr (← mkCongrArg l.appFn!.appFn! hf) hp)
  return some (hf.mvarId!, hp.mvarId!)

/-- `peel`, then, at a goal `PMF.map f p = PMF.map g q` whose maps are not definitionally
equal, `peel` of `p = q`: the goal of the outcomes and the goals `f = g` of the maps. -/
def peelMaps (g : MVarId) : MetaM (MVarId × List MVarId) := do
  let g ← peel g
  match ← congrMap? g with
  | some (hf, hp) => return (← peel hp, [hf])
  | none => return (g, [])

/-- The predicates `fun t => H[s := t]` for the propositional hypotheses `H` of `g` in which
`s` occurs. -/
def abstractHyps (g : MVarId) (s : Expr) : MetaM (Array Expr) := g.withContext do
  let sTy ← inferType s
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let a ← kabstract ty s
    if a.hasLooseBVars then out := out.push (Expr.lam `t sTy a .default)
  return out

/-- The arity of `t` as a predicate (`some (n, true)` for `X₁ → … → Xₙ → Prop`,
`some (n, false)` for `X₁ → … → Xₙ → Bool`), or `none`. -/
def predArity (t : Term) : TacticM (Option (Nat × Bool)) := withoutModifyingState do
  try
    let e ← Term.withoutErrToSorry <|
      Term.withSynthesize (postpone := .partial) <| Term.elabTerm t none
    let ty ← instantiateMVars (← inferType e)
    forallTelescopeReducing ty fun xs b => do
      let b ← whnfR b
      if xs.isEmpty then return none
      if b.isSort && b.sortLevel! == Level.zero then return some (xs.size, true)
      if b.isConstOf ``Bool then return some (xs.size, false)
      return none
  catch _ => return none

/-- The terms of `ls` that are predicates of arity `n` with values in `Prop` (`prop`) or
`Bool`, followed by the local variables of the main goal that are such predicates. -/
def predsOf (ls : Array Term) (n : Nat) (prop : Bool) : TacticM (Array Term) := do
  let mut out ← ls.filterM fun l => return (← predArity l) == some (n, prop)
  let g ← getMainGoal
  let locals ← g.withContext do
    let mut r : Array Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || d.isLet then continue
      let ok ← forallTelescopeReducing d.type fun xs b => do
        let b ← whnfR b
        return xs.size == n &&
          (if prop then b.isSort && b.sortLevel! == Level.zero else b.isConstOf ``Bool)
      if ok then r := r.push d.toExpr
    return r
  for e in locals do
    out := out.push (← g.withContext (Term.exprToSyntax e))
  return out

/-- Try `pre`, then `refine lem`, then `oracle_run_leaf [ls]` on each new goal, for each
argument tuple of `cands` in order, both as stated and after `apply Eq.symm` when `symm` is
set. The goals of the first tuple that closes every premise are none; when no tuple closes
them, the goals left by the first tuple for which `refine` succeeds; an error when `refine`
fails for every tuple. -/
def tryLemma (name : String) (ls : Array Term) (cands : Array (Array Term)) (symm : Bool)
    (mk : Array Term → TacticM (TSyntax `tactic)) : TacticM Unit := do
  let start ← saveState
  let apply (flip : Bool) (c : Array Term) : TacticM Bool := do
    start.restore
    capped <| tryCatchRuntimeEx
      (do
        if flip then evalTactic (← `(tactic| apply Eq.symm))
        evalTactic (← mk c)
        return true)
      (fun _ => return false)
  let mut first? : Option (Bool × Array Term) := none
  for flip in (if symm then #[false, true] else #[false]) do
    for c in cands do
      unless ← apply flip c do continue
      if first?.isNone then first? := some (flip, c)
      let left ← leafAll ls (failFast := true)
      if left.isEmpty then return
  match first? with
  | some (flip, c) =>
    discard <| apply flip c
    setGoals (← leafAll ls)
  | none =>
    start.restore
    throwError "{name}: the lemma does not apply to the goal"

/-! ### Run equality -/

/-- `oracle_run_eq [l₁, …] with N` proves `run O' A s = run O A s'` (or its symmetric form),
read through maps `PMF.map f`, `PMF.map g` and at equal points, by
`OracleAdv.run_eq_run_of_inv O O' N` with the premises closed by `oracle_run_leaf [l₁, …]`;
maps that are not definitionally equal add the premise `f = g`, and start states that are not
definitionally equal the premise `s = s'`. The invariant `N` is tried first; then the
abstractions of `s` in the hypotheses, the lemmas `lᵢ` that are predicates, and
`fun _ => True`. The premises it does not close are left as goals. -/
syntax (name := oracleRunEqStx) "oracle_run_eq" (" [" term,* "]")? (" with " term)? : tactic

/-- The elaborator of `oracle_run_eq`. -/
@[tactic oracleRunEqStx] def evalOracleRunEq : Tactic := fun stx => do
  let ls := listArgs stx 1
  evalTactic (← `(tactic| intros))
  let (g, maps) ← peelMaps (← getMainGoal)
  replaceMainGoal (g :: maps)
  let some (_, l, r) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq?
    | throwError "oracle_run_eq: the goal is not an equality"
  unless isRun l.cleanupAnnotations && isRun r.cleanupAnnotations do
    throwError "oracle_run_eq: the goal is not an equality of runs"
  let s := l.cleanupAnnotations.getArg! 6
  let mut ns : Array Term := #[]
  if let some n := withArg? stx 2 then ns := ns.push n
  for e in ← abstractHyps g s do ns := ns.push (← Term.exprToSyntax e)
  ns := ns ++ (← predsOf ls 1 true)
  ns := ns.push (← `(fun _ => True))
  tryLemma "oracle_run_eq" ls (ns.map (#[·])) true fun c => do
    let n := c[0]!
    `(tactic| first
      | refine CatCrypt.Crypto.OracleAdv.run_eq_run_of_inv _ _ $n ?_ ?_ _ _ ?_
      | refine (CatCrypt.Crypto.OracleAdv.run_eq_run_of_inv _ _ $n ?_ ?_ _ _ ?_).trans
          (congrArg (CatCrypt.Crypto.OracleAdv.run _ _) ?_))

/-! ### Identical until bad -/

/-- `oracle_run_off_bad [l₁, …] with bad` proves
`(run O₁ A s₁).map (Prod.map id f₁) (a, t) = (run O₂ A s₂).map (Prod.map id f₂) (a, t)`, or
its form quantified over `s₁ s₂ a t` and the hypotheses, by `OracleAdv.run_map_eq_off_bad`,
with the premises closed by `oracle_run_leaf [l₁, …]`. Without `bad`, the predicates tried are
the Boolean predicates among the `lᵢ` and the abstractions of `t` in the hypotheses
`b t = false`. The premises it does not close are left as goals. -/
syntax (name := oracleRunOffBadStx) "oracle_run_off_bad" (" [" term,* "]")? (" with " term)? :
  tactic

/-- The abstractions `fun u => e[t := u]` of the hypotheses `e = false` of `g` that mention the
outcome `t` of the point `(a, t)` of the left side of the goal. -/
def offBadHyps (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let some (_, l, _) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq?
    | return #[]
  let l := l.cleanupAnnotations
  unless l.isAppOfArity ``DFunLike.coe 6 do return #[]
  let pt := l.appArg!
  unless pt.isAppOfArity ``Prod.mk 4 do return #[]
  let t := pt.getArg! 3
  let tTy ← inferType t
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, e, f) := ty.eq? | continue
    unless f.isConstOf ``Bool.false do continue
    let a ← kabstract e t
    if a.hasLooseBVars then out := out.push (Expr.lam `u tTy a .default)
  return out

/-- The elaborator of `oracle_run_off_bad`. -/
@[tactic oracleRunOffBadStx] def evalOracleRunOffBad : Tactic := fun stx => do
  let ls := listArgs stx 1
  let g ← getMainGoal
  unless (CatCrypt.Tactics.AutoDispatch.mentionsConst [``CatCrypt.Crypto.OracleAdv.run]
      (← instantiateMVars (← g.getType))) do
    throwError "oracle_run_off_bad: the goal mentions no run"
  let mut bs : Array Term := #[]
  if let some b := withArg? stx 2 then bs := bs.push b
  bs := bs ++ (← predsOf ls 1 false)
  for e in ← offBadHyps g do bs := bs.push (← Term.exprToSyntax e)
  tryLemma "oracle_run_off_bad" ls (bs.map (#[·])) false fun c => do
    let b := c[0]!
    `(tactic| first
      | refine CatCrypt.Crypto.OracleAdv.run_map_eq_off_bad _ _ _ _ $b ?_ ?_ ?_ _ _ _ ?_ _ _ ?_
      | refine CatCrypt.Crypto.OracleAdv.run_map_eq_off_bad _ _ _ _ $b ?_ ?_ ?_ _)

/-! ### Keyed games -/

/-- `oracle_run_accept [l₁, …] with V` proves `G.accept B = G'.accept B` for keyed games with
the same keys and states by `KeyedGame.accept_eq_of_kernel` at the kernel `PMF.pure` and the
key map `id`, with the premises closed by `oracle_run_leaf [l₁, …]`. Without `V`, the
invariants tried are the predicates among the `lᵢ` and `fun _ => True`. The premises it does
not close are left as goals. -/
syntax (name := oracleRunAcceptStx) "oracle_run_accept" (" [" term,* "]")? (" with " term)? :
  tactic

/-- The elaborator of `oracle_run_accept`. -/
@[tactic oracleRunAcceptStx] def evalOracleRunAccept : Tactic := fun stx => do
  let ls := listArgs stx 1
  let lem := `CatCrypt.Crypto.KeyedGame.accept_eq_of_kernel
  unless (← getEnv).contains lem do
    throwError "oracle_run_accept: `{lem}` is not in the environment"
  evalTactic (← `(tactic| intros))
  let some (_, l, _) := (← instantiateMVars (← getMainGoalType)).cleanupAnnotations.eq?
    | throwError "oracle_run_accept: the goal is not an equality"
  unless l.cleanupAnnotations.isAppOf ``CatCrypt.Crypto.UCTransparent.KeyedGame.accept do
    throwError "oracle_run_accept: the goal is not an equality of acceptance probabilities"
  let mut vs : Array Term := #[]
  if let some v := withArg? stx 2 then vs := vs.push v
  vs := vs ++ (← predsOf ls 1 true)
  vs := vs.push (← `(fun _ => True))
  let lemId := mkIdent lem
  tryLemma "oracle_run_accept" ls (vs.map (#[·])) true fun c => do
    let v := c[0]!
    let g ← getMainGoal
    let some (_, l, r) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq?
      | throwError "oracle_run_accept: the goal is not an equality"
    let some gl := l.cleanupAnnotations.getAppArgs[2]?
      | throwError "oracle_run_accept: no game"
    let some gr := r.cleanupAnnotations.getAppArgs[2]?
      | throwError "oracle_run_accept: no game"
    let gl ← g.withContext (Term.exprToSyntax gl)
    let gr ← g.withContext (Term.exprToSyntax gr)
    `(tactic| refine $lemId $gl $gr id ?_ PMF.pure $v ?_ ?_ ?_ ?_ _)
where
  getMainGoalType : TacticM Expr := do (← getMainGoal).getType

/-! ### A key drawn at its first triggering call -/

/-- `oracle_run_trigger [l₁, …]` proves `run O A s = μ.bind fun k => run (Ok k) A s` by
`OracleAdv.run_eq_bind_run_of_trigger μ O Ok P c N`, with the premises closed by
`oracle_run_leaf [l₁, …]`, after `PMF.map_bind` from right to left and the peeling of maps of
`oracle_run_eq`, so that it also proves
`(run O A s).map f = μ.bind fun k => (run (Ok k) A s).map f`. The states before the draw `P`
are tried among the abstractions of `s` in the hypotheses, the unary predicates among the
`lᵢ` and `fun _ => True`; the trigger `c` among the binary predicates of the `lᵢ` (a Boolean
`c` as `fun s d => c s d = true`), and the states after the draw `N` among the binary
predicates of the `lᵢ`. The premises it does not close are left as goals. -/
syntax (name := oracleRunTriggerStx) "oracle_run_trigger" (" [" term,* "]")? : tactic

/-- The elaborator of `oracle_run_trigger`. -/
@[tactic oracleRunTriggerStx] def evalOracleRunTrigger : Tactic := fun stx => do
  let ls := listArgs stx 1
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| try simp only [← PMF.map_bind]))
  let (g, maps) ← peelMaps (← getMainGoal)
  replaceMainGoal (g :: maps)
  let some (_, l, _) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq?
    | throwError "oracle_run_trigger: the goal is not an equality"
  unless isRun l.cleanupAnnotations do
    throwError "oracle_run_trigger: the left side is not a run"
  let s := l.cleanupAnnotations.getArg! 6
  let mut ps : Array Term := #[← `(fun _ => True)]
  for e in ← abstractHyps g s do ps := ps.push (← Term.exprToSyntax e)
  ps := ps ++ (← predsOf ls 1 true)
  let mut bin ← predsOf ls 2 true
  let mut cs := bin
  for n in ← predsOf ls 1 true do bin := bin.push (← `(fun _ => $n))
  for e in ← abstractHyps g s do
    let n ← Term.exprToSyntax e
    bin := bin.push (← `(fun _ => $n))
  for c in ← predsOf ls 2 false do cs := cs.push (← `(fun s d => $c s d = true))
  let mut tuples : Array (Array Term) := #[]
  for p in ps do
    for c in cs do
      for n in bin do
        tuples := tuples.push #[p, c, n]
  tryLemma "oracle_run_trigger" ls tuples false fun t => do
    let (p, c, n) := (t[0]!, t[1]!, t[2]!)
    `(tactic| refine CatCrypt.Crypto.OracleAdv.run_eq_bind_run_of_trigger _ _ _ $p $c $n
      ?_ ?_ ?_ ?_ ?_ ?_ _ _ ?_)

/-! ### Invariants along a run -/

/-- The goal `∀ z, z ∈ (run O A s).support → Φ z`: binders and premise. -/
def isSupportGoal (t : Expr) : Bool :=
  match t with
  | .forallE _ _ (.forallE _ dom _ _) _ =>
    CatCrypt.Tactics.AutoDispatch.mentionsConst [``CatCrypt.Crypto.OracleAdv.run] dom &&
      CatCrypt.Tactics.AutoDispatch.mentionsConst [``PMF.support] dom
  | _ => false

/-- The invariant `fun t => Φ[z.2 := t]` of a goal `∀ z, z ∈ (run O A s).support → Φ z` in
which `z` occurs only as `z.2`. -/
def supportInv (t : Expr) : MetaM Expr := do
  let .forallE n zTy body bi := t | throwError "run_inv: not a support goal"
  withLocalDecl n bi zTy fun z => do
    let b := body.instantiate1 z
    let .forallE _ _ φ _ := b | throwError "run_inv: not a support goal"
    if φ.hasLooseBVars then throwError "run_inv: the conclusion uses the membership"
    let zTy' ← whnf zTy
    unless zTy'.isAppOfArity ``Prod 2 do throwError "run_inv: the outcome is not a pair"
    withLocalDeclD `t (zTy'.getArg! 1) fun tv => do
      let φ' := φ.replace fun e =>
        if (e.isAppOfArity ``Prod.snd 3 && e.appArg! == z) then some tv
        else match e with
          | .proj ``Prod 1 x => if x == z then some tv else none
          | _ => none
      if φ'.containsFVar z.fvarId! then
        throwError "run_inv: the conclusion uses the output of the run"
      mkLambdaFVars #[tv] φ'

/-- `oracle_run_support [l₁, …] with Inv` proves `∀ z ∈ (run O A s).support, Φ z`, possibly
under further binders, by `OracleAdv.run_support_inv O Inv`, with the premises closed by
`oracle_run_leaf [l₁, …]`. Without `Inv`, the invariant is `fun t => Φ[z.2 := t]`, when `z`
occurs in `Φ` only as `z.2`. The premises it does not close are left as goals. -/
syntax (name := oracleRunSupportStx) "oracle_run_support" (" [" term,* "]")? (" with " term)? :
  tactic

/-- The elaborator of `oracle_run_support`. -/
@[tactic oracleRunSupportStx] def evalOracleRunSupport : Tactic := fun stx => do
  let ls := listArgs stx 1
  for _ in [0:16] do
    let t ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
    if isSupportGoal t || !t.isForall then break
    evalTactic (← `(tactic| intro))
  let t ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  unless isSupportGoal t do throwError "oracle_run_support: not a goal over the support of a run"
  let inv ← match withArg? stx 2 with
    | some i => pure i
    | none => do Term.exprToSyntax (← (← getMainGoal).withContext (supportInv t))
  tryLemma "oracle_run_support" ls #[#[inv]] false fun c => do
    let i := c[0]!
    `(tactic| refine CatCrypt.Crypto.OracleAdv.run_support_inv _ $i ?_ _ _ ?_)

/-! ### Eager sampling -/

/-- `eager_draw_auto U use [l₁, …]` is `eager_draw U use [l₁, …]` followed by
`oracle_run_leaf [l₁, …]` on each side condition. -/
syntax (name := eagerDrawAuto)
  "eager_draw_auto " term:max ppSpace term:max (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| eager_draw_auto $U $use $[[$ts?,*]]?) => do
    let ts : Array Lean.Ident := (ts?.map (·.getElems)).getD #[]
    let tms : Array Term := ts.map (⟨·.raw⟩)
    `(tactic| (eager_draw $U $use [$[$ts:ident],*]) <;> oracle_run_leaf [$tms,*])

end

end CatCrypt.Tactics.AutoOracleRun

catcrypt_auto_shape "oracle run equality" direct priority 88 :=
  any [all [mentions [CatCrypt.Crypto.OracleAdv.run],
      any [app Eq, under_forall (app Eq), under_forall (under_forall (app Eq)),
        under_forall (under_forall (under_forall (app Eq))),
        under_forall (under_forall (under_forall (under_forall (app Eq))))]],
    arg Eq/3 at 1 (app CatCrypt.Crypto.UCTransparent.KeyedGame.accept)]

catcrypt_auto_shape "oracle run support" direct priority 87 :=
  all [mentions [CatCrypt.Crypto.OracleAdv.run], mentions [PMF.support]]

catcrypt_auto_arm "oracle run equality" order 10 := "(oracle_run_eq%GRIND; done)"
catcrypt_auto_arm "oracle run equality" order 20 := "(oracle_run_off_bad%GRIND; done)"
catcrypt_auto_arm "oracle run equality" order 30
    needs [CatCrypt.Crypto.KeyedGame.accept_eq_of_kernel] :=
  "(oracle_run_accept%GRIND; done)"
catcrypt_auto_arm "oracle run equality" order 40 := "(oracle_run_trigger%GRIND; done)"
catcrypt_auto_arm "oracle run equality" order 50
    needs [CatCrypt.Crypto.FiatShamirROM.run_eager_of_step] :=
  "(refine CatCrypt.Crypto.FiatShamirROM.run_eager_of_step _ _ _ _ ?_ ?_ _ _ ?_ <;>
    oracle_run_leaf%GRIND)"

catcrypt_auto_arm "oracle run support" order 10 := "(oracle_run_support%GRIND; done)"

catcrypt_auto_arm "*" order 30 := "first
  | (oracle_run_eq%GRIND with (%TERM); done)
  | (oracle_run_off_bad%GRIND with (%TERM); done)
  | (oracle_run_accept%GRIND with (%TERM); done)
  | (oracle_run_support%GRIND with (%TERM); done)"

end

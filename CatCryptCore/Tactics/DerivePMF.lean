/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryDist
public import CatCryptCore.Tactics.DeriveTimed

/-!
# Costed forms of distribution-valued reductions

With this module imported, `derive_timed R` also takes a reduction `R` whose result is a
distribution `PMF α` written as a sampling program, or a computation `SPComp α` whose body is
`liftPMF p` of such a program `p`. Its costed form is a costed oracle tree over the empty
interface, `R.timed : … → ℕ × OracleAdv.Timed Empty Empty α`, whose time counts every sample
and every oracle step of the program.

## The rule

The class is the distributions built from

* `PMF.pure a`, `PMF.bind p f`, `PMF.map f p` (also through the `Monad PMF` instance: `pure`,
  `>>=`, `<$>`);
* uniform sampling `PMF.uniformFintype β`;
* the run `OracleAdv.run O A s` of an oracle tree `A` (a tree binder of `R`, a function into
  trees applied, or any tree that `derive_timed` translates) against a stateful oracle
  `O : S → D → PMF (R × S)` given as a function: a constant, a partial application or a
  `fun s d => …`, whose body at fresh `s` and `d` is again in the class; in `A`, a tree-valued
  field `D.f` of a structure binder `D` of `R` (an adversary given as a structure with its run
  and its query bound, `D.run x`), whose type does not mention `D`, is an adversary with a costed
  form: it becomes a further binder `D_f` of the tree, after the binders of `R`, which
  `derive_timed` translates as a tree binder (a costed tree, and for a function its cost
  companion `D_fCost`);
* `if`, `if h :`, a `match` with a motive constant in its discriminants, and a `let`;
* a call of a non-recursive definition whose body is in the class, unfolded with its
  arguments bound once (`bindArgs`), as `derive_timed` unfolds a data definition;

and, for a computation, `liftPMF p` of such a `p`.

Such a distribution is reflected into an oracle tree over the empty interface (`reflect`),
`R.pmfTree : … → OracleAdv Empty Empty α`, node by node: `PMF.pure a` is `ret a`, `PMF.bind p f`
is `OracleAdv.bind`, `PMF.map f p` is the bind of the tree of `p` with `ret ∘ f`, a uniform
sample is one `rand` node returning its sample, and `OracleAdv.run O A s` is the simulation
`OracleAdv.simulate (R.pmfStep ys) A s` whose program `R.pmfStep ys s d` is the tree of `O s d`:
a definition over the locals `ys` that the step mentions (`R.pmfStep_2`, … for further runs),
whose costed form `derive_timed` derives on demand with its own erasure theorem, as for a
handler of a simulation (also of a state that holds functions, such as the table
`D → Option H` of `roOracle`); an `if` or a `match` is the same `if` or `match` over the trees of
its branches. The theorem
`R.dist_pmfTree : (R.pmfTree xs).dist = R xs` (for a computation,
`liftPMF (R.pmfTree xs).dist = R xs`) is assembled from the lemmas `OracleAdv.dist_*_of` of
`CatCryptCore.Crypto.OracleAdversaryDist`, one per node, and checked by the kernel.

`derive_timed` then derives the costed form of the tree `R.pmfTree` by the rules of
`CatCryptCore.Tactics.DeriveTimed` (binders, cost companions, field paths, the pricing of data),
and `R.timed` is that costed form, `R.pmfTree.timed`, so that

* each sample is a `rand` node at its unit;
* each oracle call of `A` is answered by the costed program of the oracle's step function at
  that query (`OracleAdv.Timed.simulate`), priced by the rules of `derive_timed` (the lookup
  and the update of a table at the costs of their code or their registered costs, the fresh
  value of a lazily sampled oracle at one `rand` node), so that the time of the run is the time
  of `A` plus the times of the steps it asks (`OracleAdv.Timed.timeBound_simulate` and its
  variants);
* `liftPMF p` is the costed tree of `p`, not one sampling node at one unit;
* the output map of `PMF.map f p` is priced per leaf as the data `f x` of a `ret` node.

The erasure theorem is the equality of output distributions,
`R.erase_timed : (R.timed xs').2.erase.dist = R xs` (for a computation,
`liftPMF (R.timed xs').2.erase.dist = R xs`), where `xs` is `xs'` with the costed binders erased
and the cost companions dropped, as for `derive_timed`; by `OracleAdv.run_map_fst_eq_dist` it is
the output of the run of the erased tree against any oracle. For each abstracted field `D.f` it
takes the hypothesis `∀ ys, (D_f ys).erase = D.f ys` that the erased costed tree is the field,
the form in which a costed adversary is related to an adversary structure.

No cost parameter is introduced: a primitive's cost is its registered or derived cost, and a
function binder of `R` has its cost companion, as in `derive_timed`.

A distribution outside the class is refused, with a message that names the construct:

* a distribution given as a parameter (a binder of type `PMF β`, a function binder into `PMF β`
  applied, a field of a structure binder valued in `PMF β`): it has no sampling program;
* a measure without a sampling program: a construction of `Mathlib` other than those above
  (`PMF.ofFintype`, `PMF.normalize`, `PMF.bernoulli`, `PMF.uniformOfFinset`), a definition
  without a value;
* a recursive definition valued in `PMF`, a `match` whose motive depends on its discriminants or
  whose alternatives do not reduce on their patterns (overlapping patterns);
* a computation whose body is not `liftPMF` of a distribution.

The extension is an elaborator of the syntax of `derive_timed`, tried before the elaborator of
`CatCryptCore.Tactics.DeriveTimed`; it declines any other reduction, which that elaborator then
derives or refuses.

## Main definitions

* `reflect` — the oracle tree over the empty interface of a distribution in the class, with the
  proof that its distribution is the given one
* `derivePMF` — `R.pmfTree`, `R.dist_pmfTree`, then `derive_timed R.pmfTree`, `R.timed` and
  `R.erase_timed`
-/

public section

meta section

namespace CatCrypt.Tactics.DerivePMF

open Lean Elab Meta Term Command
open CatCrypt.Tactics.DeriveTimed

/-- A refusal of the reflection, with the prefix of `derive_timed`. -/
def failP {β : Type} (what : MessageData) : MetaM β :=
  throwError m!"derive_timed: {what}"

/-- The type `α` of a distribution type `PMF α`. -/
def pmfArg? (t : Expr) : MetaM (Option Expr) := do
  let t ← instantiateMVars t
  if t.isAppOfArity ``PMF 1 then return some t.appArg!
  let t ← whnfR t
  if t.isAppOfArity ``PMF 1 then return some t.appArg!
  return none

/-- The oracle-tree type `OracleAdv Empty Empty α`. -/
def emptyTreeTy (α : Expr) : Expr :=
  mkApp3 (Lean.mkConst ``CatCrypt.Crypto.OracleAdv) (Lean.mkConst ``Empty) (Lean.mkConst ``Empty) α

/-- `OracleAdv.dist t` of a tree `t : OracleAdv Empty Empty α`. -/
def distE (α t : Expr) : Expr :=
  mkApp2 (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.dist) α t

/-- The maximal nesting of unfolded definitions of the reflection: the option
`derive_timed.maxDepth` of `derive_timed`. -/
def reflectDepth : CoreM Nat := maxDepth

/-- The constants of `PMF` that the reflection reads as sampling programs. -/
def pmfProgramConsts : Array Name :=
  #[``PMF.pure, ``PMF.bind, ``PMF.map, ``PMF.uniformFintype]

/-- The context of the reflection: the nesting of unfolded definitions, the binders of the
reduction, and the tree-valued fields of structure binders run against an oracle, recorded for
abstraction (`fieldOfBinder?`). -/
structure RCtx where
  depth : Nat := 0
  top : Array FVarId := #[]
  fields : IO.Ref (Array Expr)
  /-- The reduction, whose oracle steps are named `R.pmfStep`, `R.pmfStep_2`, … -/
  base : Name
  /-- The number of oracle steps named so far. -/
  steps : IO.Ref Nat
  /-- The universe parameters of the reduction. -/
  levelParams : List Name := []

/-- The field `S.f D` of a structure binder `D` of the reduction heading the tree `A`
(`D.run x y`), when its type is a tree or a function into trees that does not mention `D`. -/
def fieldOfBinder? (top : Array FVarId) (A : Expr) : MetaM (Option Expr) := do
  let A := A.consumeMData.headBeta
  let f := A.getAppFn
  let args := A.getAppArgs
  let (fld, D) ← match f with
    | .const pc lvls =>
      let some info ← getProjectionFnInfo? pc | return none
      if info.fromClass || args.size ≤ info.numParams then return none
      pure (mkAppN (.const pc lvls) (args.extract 0 (info.numParams + 1)), args[info.numParams]!)
    | .proj _ _ D => pure (f, D)
    | _ => return none
  let .fvar dv := D | return none
  unless top.contains dv do return none
  let ty ← inferType fld
  if ty.containsFVar dv then return none
  let isTree ← forallTelescopeReducing ty fun _ b => return (← treeTy? b).isSome
  return if isTree then some fld else none

/-- The free variables of `e` and of their types, in the order of the local context. -/
def closureFVars (e : Expr) : MetaM (Array Expr) := do
  let mut set := (collectFVars {} e).fvarSet
  let mut todo := set.toArray
  while !todo.isEmpty do
    let fv := todo.back!
    todo := todo.pop
    let ty ← instantiateMVars (← fv.getType)
    for fv' in (collectFVars {} ty).fvarIds do
      unless set.contains fv' do
        set := set.insert fv'
        todo := todo.push fv'
  let lctx ← getLCtx
  let decls := set.toArray.filterMap lctx.find?
  return (decls.qsort (·.index < ·.index)).map (·.toExpr)

/-- The field applications `S.f ps D` without loose bound variables among the subterms of `e`. -/
partial def fieldApps (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let mut acc := acc
  if !e.hasLooseBVars then
    match e.getAppFn, e with
    | .const pc _, _ =>
      if let some info ← getProjectionFnInfo? pc then
        if !info.fromClass && e.getAppNumArgs == info.numParams + 1 && !acc.contains e then
          acc := acc.push e
    | _, .proj _ _ (.fvar _) => if !acc.contains e then acc := acc.push e
    | _, _ => pure ()
  match e with
  | .app f a => fieldApps a (← fieldApps f acc)
  | .lam _ t b _ | .forallE _ t b _ => fieldApps b (← fieldApps t acc)
  | .letE _ t v b _ => fieldApps b (← fieldApps v (← fieldApps t acc))
  | .mdata _ b | .proj _ _ b => fieldApps b acc
  | _ => return acc

/-- The tree-valued fields of structure binders of the reduction that occur in the tree `A`
(`D.run x` in `withVerify x (D.run x)`), by `fieldOfBinder?`. -/
def fieldsIn (top : Array FVarId) (A : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for e in ← fieldApps A #[] do
    if let some fld ← fieldOfBinder? top e then
      unless out.contains fld do out := out.push fld
  return out

mutual

/-- **The reflection of a distribution.** For `e : PMF α` in the class of the module
docstring, a tree `t : OracleAdv Empty Empty α` and a proof of `t.dist = e`. -/
partial def reflect (rc : RCtx) (e : Expr) : TermElabM (Expr × Expr) := do
  let e := e.consumeMData.headBeta
  let some α ← pmfArg? (← inferType e)
    | failP m!"internal: `{e}` is not a distribution"
  match e with
  | .letE n t v b _ =>
    unless ← keepsLet t v do return ← reflect rc (b.instantiate1 v)
    withLetDecl n t v fun x => do
      let (tb, pb) ← reflect rc (b.instantiate1 x)
      return (← mkLetFVars #[x] tb, ← mkLetFVars #[x] pb)
  | .fvar _ =>
    failP m!"a distribution given as a parameter: `{e}` is a binder of type `PMF {α}`, which \
      has no sampling program from which its time is derived"
  | .mdata _ b => reflect rc b
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar _ =>
      failP m!"a distribution given as a parameter: `{e}` applies the binder `{f}`, a function \
        into distributions without a sampling program from which its time is derived"
    | .const c _ => reflectConst rc e c args α
    | .proj S i _ =>
      failP m!"a distribution given as a parameter: `{e}` is the field {i} of a structure \
        `{S}`, without a sampling program from which its time is derived"
    | _ => failP m!"the distribution `{e}` is not a sampling program"
  | _ => failP m!"the distribution `{e}` is not a sampling program"

/-- The reflection of a distribution headed by the constant `c`. -/
partial def reflectConst (rc : RCtx) (e : Expr) (c : Name) (args : Array Expr) (α : Expr) :
    TermElabM (Expr × Expr) := do
  let E := Lean.mkConst ``Empty
  if c == ``PMF.pure && args.size == 2 then
    let a := args[1]!
    let t := mkApp4 (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.ret) E E α a
    return (t, mkApp2 (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.dist_ret) α a)
  if c == ``PMF.bind && args.size == 4 then
    let β := args[0]!
    let p := args[2]!
    let (tp, hp) ← reflect rc p
    let (k, f, hf) ← reflectFn rc args[3]! β
    let t := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.bind) #[E, E, β, α, tp, k]
    let h := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.dist_bind_of)
      #[β, α, tp, k, p, f, hp, hf]
    return (t, h)
  if c == ``PMF.map && args.size == 4 then
    let β := args[0]!
    let g := args[2]!
    let p := args[3]!
    let (tp, hp) ← reflect rc p
    let k ← withLocalDeclD `x β fun x => do
      mkLambdaFVars #[x] (mkApp4 (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.ret) E E α
        (mkApp g x).headBeta)
    let t := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.bind) #[E, E, β, α, tp, k]
    let h := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.dist_map_of) #[β, α, tp, p, g, hp]
    return (t, h)
  if c == ``PMF.uniformFintype && args.size == 3 then
    -- One sample: a `rand` node returning its sample.
    let k ← withLocalDeclD `x α fun x => do
      mkLambdaFVars #[x] (mkApp4 (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.ret) E E α x)
    let t := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.rand) #[E, E, α, α, e, k]
    return (t, mkApp2 (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.dist_sample_of) α e)
  if c == ``CatCrypt.Crypto.OracleAdv.run && args.size == 7 then
    return ← reflectRun rc e args α
  if c == ``ite && args.size == 5 then
    let (tt, ht) ← reflect rc args[3]!
    let (te, he) ← reflect rc args[4]!
    let t := mkApp5 (Lean.mkConst ``ite [Level.succ Level.one]) (emptyTreeTy α) args[1]! args[2]!
      tt te
    let h := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.dist_ite_of)
      #[α, args[1]!, args[2]!, tt, te, args[3]!, args[4]!, ht, he]
    return (t, h)
  if c == ``dite && args.size == 5 then
    let cnd := args[1]!
    let (tt, pt, ht) ← reflectFn rc args[3]! cnd
    let ncnd := mkNot cnd
    let (te, pe, he) ← reflectFn rc args[4]! ncnd
    let t := mkApp5 (Lean.mkConst ``dite [Level.succ Level.one]) (emptyTreeTy α) cnd args[2]! tt
      te
    let h := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.dist_dite_of)
      #[α, cnd, args[2]!, tt, te, pt, pe, ht, he]
    return (t, h)
  if ← isMatcher c then
    return ← reflectMatch rc e α
  -- A method of a class (`>>=`, `pure`, `<$>` of `Monad PMF`): its instance's value.
  if let some info ← getProjectionFnInfo? c then
    if info.fromClass then
      if let some e' ← unfoldProjInst? e then
        return ← reflect rc e'.headBeta
      failP m!"the class method `{c}` in `{e}` does not reduce through its instance to a \
        sampling program"
    failP m!"a distribution given as a parameter: `{e}` is the field `{c}` of a structure, \
      without a sampling program from which its time is derived"
  if c.getRoot == `PMF then
    failP m!"a measure without a sampling program: `{e}` is the distribution `{c}`, which is \
      not among the sampling constructs `PMF.pure`, `PMF.bind`, `PMF.map`, \
      `PMF.uniformFintype`"
  let env ← getEnv
  if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
    failP m!"the distribution `{e}` is a call of the recursive definition `{c}`, which the \
      reflection does not unfold"
  if let some (.recInfo _) := env.find? c then
    failP m!"the distribution `{e}` is a case analysis by the recursor `{c}`, which the \
      reflection does not read; write it as a `match` with constructor patterns"
  let some (.defnInfo d) := env.find? c
    | failP m!"a measure without a sampling program: `{c}` in `{e}` has no definition"
  if rc.depth ≥ (← reflectDepth) then
    failP m!"the distribution `{e}` unfolds deeper than {rc.depth} definitions (option \
      derive_timed.maxDepth)"
  let v := d.value.instantiateLevelParams d.levelParams e.getAppFn.constLevels!
  let body ← bindArgs v args 0
  reflect { rc with depth := rc.depth + 1 } body

/-- The reflection of a function `f : X → PMF γ` (a continuation of a bind, a branch of a
dependent `if`): the tree function, the function as a lambda, and the pointwise proof
`∀ x, (k x).dist = f x`. -/
partial def reflectFn (rc : RCtx) (f X : Expr) : TermElabM (Expr × Expr × Expr) :=
  withLocalDeclD `x X fun x => do
    let b := (mkApp f x).headBeta
    let (t, h) ← reflect rc b
    return (← mkLambdaFVars #[x] t, ← mkLambdaFVars #[x] b, ← mkLambdaFVars #[x] h)

/-- The reflection of the run `OracleAdv.run O A s`: the simulation of `A` by the trees of
the steps `O s d`, at fresh `s` and `d`. -/
partial def reflectRun (rc : RCtx) (e : Expr) (args : Array Expr) (_α : Expr) :
    TermElabM (Expr × Expr) := do
  let D := args[0]!
  let R := args[1]!
  let β := args[2]!
  let S := args[3]!
  let O := args[4]!
  let A := args[5]!
  let s₀ := args[6]!
  for fld in ← fieldsIn rc.top A do
    rc.fields.modify fun fs => if fs.contains fld then fs else fs.push fld
  if O.consumeMData.headBeta.getAppFn.isFVar then
    failP m!"a distribution given as a parameter: the oracle `{O}` of the run `{e}` is a \
      binder, a step function without a sampling program from which its time is derived"
  let (implLam, hO) ← withLocalDeclD `s S fun s => withLocalDeclD `d D fun d => do
    let (t, h) ← reflect rc (mkApp2 O s d).headBeta
    return (← mkLambdaFVars #[s, d] t, ← mkLambdaFVars #[s, d] h)
  -- The step is a definition over the locals it mentions, whose costed form `derive_timed`
  -- derives on demand, with its own erasure theorem (that of a handler of a costed state).
  let k ← rc.steps.modifyGet fun n => (n + 1, n + 1)
  let stepName := rc.base ++ Name.mkSimple (if k == 1 then "pmfStep" else s!"pmfStep_{k}")
  let implLam ← zetaReduce (← instantiateMVars implLam)
  let fvs ← closureFVars implLam
  addTimedDef stepName rc.levelParams (← mkForallFVars fvs (← inferType implLam))
    (← mkLambdaFVars fvs implLam)
  let impl := mkAppN (Lean.mkConst stepName (rc.levelParams.map mkLevelParam)) fvs
  let E := Lean.mkConst ``Empty
  let t := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.simulate)
    #[D, R, E, E, β, S, impl, A, s₀]
  let h := mkAppN (Lean.mkConst ``CatCrypt.Crypto.OracleAdv.dist_simulate_of)
    #[β, D, R, S, impl, O, hO, A, s₀]
  return (t, h)

/-- The reflection of a `match` with a motive constant in its discriminants: the same match
over the trees of its alternatives, and the match over their proofs, which holds when each
alternative reduces on its pattern. -/
partial def reflectMatch (rc : RCtx) (e : Expr) (α : Expr) : TermElabM (Expr × Expr) := do
  let some app ← matchMatcherApp? e
    | failP m!"the match `{e}` is not a matcher application"
  unless app.remaining.isEmpty do
    failP m!"the match `{e}` is applied to further arguments"
  if app.discrInfos.any (·.hName?.isSome) then
    failP m!"the match `{e}` names the equations of its discriminants"
  let constMotive ← lambdaTelescope app.motive fun xs b => do
    return !b.hasAnyFVar (xs.contains <| .fvar ·)
  unless constMotive do
    failP m!"the match `{e}` has a motive that depends on its discriminants"
  let some uPos := app.uElimPos?
    | failP m!"the match `{e}` eliminates only into propositions"
  let treeTy := emptyTreeTy α
  let motive' ← lambdaTelescope app.motive fun xs _ => mkLambdaFVars xs treeTy
  let mut alts' := #[]
  let mut pfs := #[]
  for alt in app.alts, n in app.altNumParams do
    let (a', p') ← forallBoundedTelescope (← inferType alt) n fun ys _ => do
      let (t, h) ← reflect rc (mkAppN alt ys).headBeta
      return (← mkLambdaFVars ys t, ← mkLambdaFVars ys h)
    alts' := alts'.push a'
    pfs := pfs.push p'
  let lvls := app.matcherLevels.set! uPos ((Level.succ Level.one))
  let tree := mkAppN (Lean.mkConst app.matcherName lvls.toList)
    (app.params ++ #[motive'] ++ app.discrs ++ alts')
  -- The proof: the matcher at the motive `fun ds => (match ds over trees).dist = match ds`.
  let motiveP ← lambdaTelescope app.motive fun xs _ => do
    let tr := mkAppN (Lean.mkConst app.matcherName lvls.toList)
      (app.params ++ #[motive'] ++ xs ++ alts')
    let src := mkAppN (Lean.mkConst app.matcherName app.matcherLevels.toList)
      (app.params ++ #[app.motive] ++ xs ++ app.alts)
    mkLambdaFVars xs (← mkEq (distE α tr) src)
  let lvlsP := app.matcherLevels.set! uPos Level.zero
  let pf := mkAppN (Lean.mkConst app.matcherName lvlsP.toList)
    (app.params ++ #[motiveP] ++ app.discrs ++ pfs)
  unless ← isTypeCorrect pf do
    failP m!"the match `{e}` has an alternative that does not reduce on its pattern \
      (overlapping patterns); write it with constructor patterns"
  return (tree, pf)

end

/-- The shape of a reduction for this module: valued in `PMF`, or a computation whose body is
`liftPMF` of a distribution. -/
inductive Shape where
  | pmf
  | lift
  deriving Inhabited, BEq

/-- The eta-expanded value of the definition `c`, as `derive_timed` reads it. -/
def etaValue (c : Name) : TermElabM (Option (ConstantInfo × Expr)) := do
  let env ← getEnv
  let some info := env.find? c | return none
  let .defnInfo d := info | return none
  let value ← lambdaTelescope d.value fun xs b => do
    withTypeBinders (← instantiateForall info.type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta
  return some (info, value)

/-- The shape of the definition `c`, when this module derives it. -/
def shape? (c : Name) : TermElabM (Option Shape) := do
  let some (_, value) ← etaValue c | return none
  lambdaTelescope value fun _ b => do
    let b := b.consumeMData
    if (← pmfArg? (← inferType b)).isSome then return some .pmf
    if b.isAppOfArity `CatCrypt.Crypto.liftPMF 2 then
      if (← pmfArg? (← inferType b.appArg!)).isSome then return some .lift
    return none

/-- Add the theorem `name : type := value`. -/
def addThm (name : Name) (levelParams : List Name) (type value : Expr) : TermElabM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  addDecl (.thmDecl { name, levelParams, type, value })

/-- The proof of `f = g` from `h : ∀ ys, f ys = g ys`, for functions of `n` arguments. -/
partial def funextN (f g h : Expr) (n : Nat) : MetaM Expr := do
  if n == 0 then return h
  let fty ← whnf (← inferType f)
  let .forallE nm d _ _ := fty | throwError "derive_timed: internal: `{f}` is not a function"
  let inner ← withLocalDeclD nm d fun y => do
    mkLambdaFVars #[y] (← funextN (mkApp f y).headBeta (mkApp g y).headBeta (mkApp h y) (n - 1))
  mkAppM ``funext #[inner]

/-- **The costed form of a distribution-valued reduction.** Reflect the body of `c` into the
tree `c.pmfTree` with `c.dist_pmfTree`, derive `c.pmfTree.timed`, and state `c.timed` (the costed
form `c.pmfTree.timed`) with `c.erase_timed`. A tree-valued field `D.f` of a structure binder `D`
run against an oracle is a further binder `D_f` of `c.pmfTree`, after the binders of `c`;
`c.erase_timed` takes for each the hypothesis that its erased costed tree is `D.f`. -/
def derivePMF (suffix : Name) (c : Name) (sh : Shape) : TermElabM Unit := do
  let some (info, value) ← etaValue c | failP m!"`{c}` has no definition to translate"
  let env ← getEnv
  if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
    failP m!"`{c}` is a recursive definition valued in `PMF`, which the reflection does not \
      unfold: a distribution defined by recursion over a tree has no sampling program of a \
      fixed shape; write it as the run of the tree against an oracle"
  let levels := info.levelParams.map mkLevelParam
  let treeName := c ++ `pmfTree
  let distName := c ++ `dist_pmfTree
  let timedName := c ++ suffix
  let eraseName := c ++ Name.mkSimple ("erase_" ++ suffix.toString)
  for n in [treeName, distName, timedName, eraseName] do
    if (← getEnv).contains n then failP m!"`{n}` already exists"
  -- The reflection, under the binders of `c`; the fields of structure binders run against an
  -- oracle are abstracted (`fieldAbs`, over the binders of `c`).
  let (tType, tValue, dType, dValue, α, fieldAbs) ← lambdaTelescope value fun xs b => do
    let b := b.consumeMData
    let p := if sh == .lift then b.appArg! else b
    let some α ← pmfArg? (← inferType p) | failP m!"internal: `{c}` is not a distribution"
    let fr ← IO.mkRef (#[] : Array Expr)
    let sr ← IO.mkRef 0
    let rc : RCtx :=
      { top := xs.map (·.fvarId!), fields := fr, base := c, steps := sr
        levelParams := info.levelParams }
    let (t, h) ← reflect rc p
    let flds ← fr.get
    let decls ← flds.mapM fun fld => do
      let nm := match fld.getAppFn, fld with
        | .const pc _, _ => pc.getString!
        | _, .proj _ i _ => s!"f{i}"
        | _, _ => "f"
      let base : Option FVarId := match fld with
        | .app _ (.fvar d) => some d
        | .proj _ _ (.fvar d) => some d
        | _ => none
      let bn : String ← match base with
        | some d => (·.toString) <$> d.getUserName
        | none => pure "x"
      return (Name.mkSimple (bn ++ "_" ++ nm), ← inferType fld)
    withLocalDeclsDND decls fun fs => do
      let t' := t.replace fun e => match flds.idxOf? e with
        | some i => if h : i < fs.size then some fs[i] else none
        | none => none
      let tType ← mkForallFVars (xs ++ fs) (emptyTreeTy α)
      let tValue ← mkLambdaFVars (xs ++ fs) t'
      let call := mkAppN (Lean.mkConst treeName levels) (xs ++ flds)
      let lhs := distE α call
      let lhs ← if sh == .lift then mkAppM `CatCrypt.Crypto.liftPMF #[lhs] else pure lhs
      let dType ← mkForallFVars xs (← mkEq lhs (mkAppN (Lean.mkConst c levels) xs))
      let h ← if sh == .lift then do
          let lift ← withLocalDeclD `μ (← mkAppM ``PMF #[α]) fun μ => do
            mkLambdaFVars #[μ] (← mkAppM `CatCrypt.Crypto.liftPMF #[μ])
          mkAppM ``congrArg #[lift, h]
        else pure h
      let dValue ← mkLambdaFVars xs h
      return (tType, tValue, dType, dValue, α.abstract xs, flds.map (·.abstract xs), xs.size)
  let (fieldAbs, nxs) := fieldAbs
  let αAbs := α
  addTimedDef treeName info.levelParams tType tValue
  try addThm distName info.levelParams dType dValue
  catch ex => failP m!"internal: the reflection of `{c}` does not check: {ex.toMessageData}"
  -- The costed form of the tree, by the rules of `derive_timed`.
  try deriveTimed { suffix } treeName
  catch ex =>
    throwError m!"derive_timed: while deriving the costed form of the sampling program \
      `{treeName}` of `{c}`:\n{ex.toMessageData}"
  let env ← getEnv
  let treeTimed := treeName ++ suffix
  let treeErase := treeName ++ Name.mkSimple ("erase_" ++ suffix.toString)
  let some tinfo := env.find? treeTimed | failP m!"internal: `{treeTimed}` is missing"
  let some einfo := env.find? treeErase | failP m!"internal: `{treeErase}` is missing"
  -- `c.timed` is the costed form of the tree.
  addTimedDef timedName info.levelParams tinfo.type (Lean.mkConst treeTimed levels)
  -- `c.erase_timed`: the distribution of the erased costed tree is `c`, under the hypotheses
  -- that the erased costed trees of the abstracted fields are the fields.
  let (eType, eValue) ← forallTelescope einfo.type fun bs eq => do
    let some (_, lhs, rhs) := eq.eq?
      | failP m!"internal: `{treeErase}` is not an equation"
    unless rhs.isAppOf treeName do
      failP m!"the costed form of the sampling program of `{c}` has a result holding \
        functions, whose erasure theorem is not an equation of trees"
    let args := rhs.getAppArgs
    let xsArgs := args.extract 0 nxs
    let flds := fieldAbs.map (·.instantiateRev xsArgs)
    let α := αAbs.instantiateRev xsArgs
    -- One hypothesis per abstracted field: `∀ ys, erased ys = D.f ys`.
    let hypTys ← (flds.zipIdx).mapM fun (fld, i) => do
      let er := args[nxs + i]!
      forallTelescopeReducing (← inferType fld) fun ys _ => do
        mkForallFVars ys (← mkEq (mkAppN er ys).headBeta (mkAppN fld ys))
    let hypDecls := hypTys.zipIdx.map fun (ty, i) =>
      (Name.mkSimple s!"h{i + 1}", fun (_ : Array Expr) => pure ty)
    withLocalDeclsD hypDecls fun hs => do
      let lhs' := lhs.replace fun x =>
        if x.isConstOf treeTimed then some (Lean.mkConst timedName levels) else none
      let wrap (t : Expr) : MetaM Expr := do
        let d := distE α t
        if sh == .lift then mkAppM `CatCrypt.Crypto.liftPMF #[d] else pure d
      let dl ← wrap lhs'
      let ty ← mkForallFVars (bs ++ hs) (← mkEq dl (mkAppN (Lean.mkConst c levels) xsArgs))
      -- `lhs = rhs`, then `rhs = c.pmfTree xs flds` field by field, then `c.dist_pmfTree`.
      let mut pf := mkAppN (Lean.mkConst treeErase levels) bs
      let mut cur := args
      for i in [0:flds.size] do
        let n ← forallTelescopeReducing (← inferType flds[i]!) fun ys _ => pure ys.size
        let hfun ← funextN args[nxs + i]! flds[i]! hs[i]! n
        let pos := nxs + i
        let curNow := cur
        let motive ← withLocalDeclD `g (← inferType flds[i]!) fun g => do
          mkLambdaFVars #[g] (mkAppN (Lean.mkConst treeName levels) (curNow.set! pos g))
        pf ← mkEqTrans pf (← mkCongrArg motive hfun)
        cur := cur.set! pos flds[i]!
      let tvar ← withLocalDeclD `t (emptyTreeTy α) fun t => do mkLambdaFVars #[t] (← wrap t)
      let h1 ← mkCongrArg tvar pf
      let h ← mkEqTrans h1 (mkAppN (Lean.mkConst distName levels) xsArgs)
      return (ty, ← mkLambdaFVars (bs ++ hs) h)
  try addThm eraseName info.levelParams eType eValue
  catch ex => failP m!"internal: the erasure theorem of `{c}` does not check: {ex.toMessageData}"

/-- `derive_timed R` for a distribution-valued `R` (or a computation `liftPMF p`): see the
module docstring. Any other reduction is left to the elaborator of `derive_timed` in
`CatCryptCore.Tactics.DeriveTimed`. -/
@[command_elab CatCrypt.Tactics.DeriveTimed.deriveTimedCmd]
def elabDeriveTimedPMF : CommandElab := fun stx => do
  let suffix := if stx[1].getNumArgs == 5 then stx[1][3].getId else `timed
  let id := stx[2]
  let done ← liftTermElabM do
    let c ← realizeGlobalConstNoOverload id
    let some sh ← shape? c | return false
    derivePMF suffix c sh
    return true
  unless done do throwUnsupportedSyntax

end CatCrypt.Tactics.DerivePMF

end

end

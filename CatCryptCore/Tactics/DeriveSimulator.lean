/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCost
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Costed forms of bundled simulators

`derive_simulator S` takes a definition `S` whose value is a bundled simulator `Simulator …` of
`UCSimulator.lean` and defines its costed form `S.timed : … → Simulator.Timed …`, proves its
erasure theorem `S.erase_timed : … → (S.timed …).Erases (S …)` and its time theorem
`S.timeBound_timed : … → (S.timed …).TimeBound B`, with the naming of `derive_reduction`.

## Reading the simulator

The value of `S` is read as a term of three constructions, by its head constant:

| head                                | costed form                                  |
|---|---|
| `Simulator.ofMultiHybrid π h`       | `Simulator.Timed.ofMultiHybrid πT`           |
| `S₁.comp S₂`                        | `Simulator.Timed.comp T₁ T₂`                 |
| `Simulator.tensor π π' h h'`        | `Simulator.tensor.timed π π' πT π'T`         |
| `c as`, `c` with a costed form      | `c.timed …`                                  |
| any other definition                | its unfolding, read again                    |

The middle view of a composite is that of the `comp` application. A definition `c` has a costed
form when `c.timed`, `c.erase_timed` and `c.timeBound_timed` exist, so that a simulator derived
earlier is reused.

A multi-call simulator `π` is costed by its head constant:

* `π₁.tensor π₂` is the costed tensor `MultiHybrid.Timed.tensor` of the costed components;
* an application of a definition `f` with a costed form `f.timed`, or whose value is a
  structure instance, is the instance of `f.timed` that `f.erase_timed` erases to `π`; the
  command runs `derive_reduction f` and `derive_time_bound f.step.tree` for the three steps
  when they are missing;
* an application of any other definition is unfolded and read again;
* a term without a head constant (a binder `S`) is a costed binder `ST : MultiHybrid.Timed …`
  with the hypotheses `ST.Erases S` and `ST.TimeBound a b c`.

## Binders and hypotheses

The theorems instantiated along the term (the erasure theorems and step theorems of the
costed multi-call simulators, the theorems of `UCSimulatorCost.lean`, the theorems of costed
forms derived earlier) are applied to metavariables unified with the term. The binders that
unification leaves open become binders of the generated declarations: the data binders
(costed primitives, costed binders) of `S.timed` after the binders of `S` that are not
propositions or that the costed form mentions; the propositions (compile equations of
primitives, erasure hypotheses of costed binders) hypotheses of `S.erase_timed`; the bound
variables (implicit) and their hypotheses binders of `S.timeBound_timed`. A hypothesis whose
type is that of an earlier one is shared with it.

The bound of `S.timeBound_timed` is the bound of the construction: the largest bound of the
steps for a costed multi-call simulator, the sum of the bounds for a composite; it is
simplified by `max 0 a = a`, `max a a = a`, associativity of `+`, numeral arithmetic and the
maxima of comparable numerals, with the monotonicity of the time bound
(`Simulator.Timed.TimeBound.mono`).

## Main definitions

* `derive_simulator S` — define `S.timed`, prove `S.erase_timed` and `S.timeBound_timed`
-/

public section

namespace CatCrypt.Tactics.DeriveSimulator

open Lean Meta Elab Term Command
open CatCrypt.Crypto.UCTransparent

meta section

/-- A bundled simulator read as a term of the constructions of the costed mirror. -/
inductive Node where
  /-- `Simulator.ofMultiHybrid π h`. -/
  | leaf (S π h : Expr)
  /-- `S₁.comp S₂`. -/
  | comp (S : Expr) (n₁ n₂ : Node)
  /-- `Simulator.tensor π π' h h'`. -/
  | tensor (S π π' h h' : Expr)
  /-- An application of a simulator `c` with a costed form `c.timed`, `c.erase_timed` and
  `c.timeBound_timed`. -/
  | derived (S : Expr) (c : Name)

/-- Read the simulator `e` as a term of `Simulator.ofMultiHybrid`, `Simulator.comp`,
`Simulator.tensor` and simulators with a costed form, unfolding any other head constant once
and retrying. -/
partial def parse (e : Expr) : MetaM Node := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  let args := e.getAppArgs
  match e.getAppFn with
  | .const n _ =>
    if n == ``Simulator.ofMultiHybrid && args.size == 9 then
      return .leaf e args[7]! args[8]!
    if n == ``Simulator.comp && args.size == 11 then
      return .comp e (← parse args[9]!) (← parse args[10]!)
    if n == ``Simulator.tensor && args.size == 18 then
      return .tensor e args[14]! args[15]! args[16]! args[17]!
    let env ← getEnv
    if env.contains (n ++ `timed) && env.contains (n ++ `erase_timed) &&
        env.contains (n ++ `timeBound_timed) then
      return .derived e n
    match ← unfoldDefinition? e with
    | some e' => parse e'
    | none => throwError "derive_simulator: `{e}` is not built from `Simulator.ofMultiHybrid`, \
        `Simulator.comp` and `Simulator.tensor`"
  | _ => throwError "derive_simulator: `{e}` is not built from `Simulator.ofMultiHybrid`, \
      `Simulator.comp` and `Simulator.tensor`"

/-- The multi-call simulators of a node. -/
def Node.hybrids : Node → Array Expr
  | .leaf _ π _ => #[π]
  | .comp _ n₁ n₂ => n₁.hybrids ++ n₂.hybrids
  | .derived .. => #[]
  | .tensor _ π π' _ _ => #[π, π']

/-- How a multi-call simulator is read. -/
inductive HView where
  /-- `π.tensor π'`. -/
  | tensor (π π' : Expr)
  /-- An application of `f`, which has a costed form or is defined by a structure instance. -/
  | leaf (f : Name)
  /-- The unfolding of the head constant. -/
  | unfold (e : Expr)
  /-- A term without a head constant (a binder): a costed binder with the hypotheses of its
  erasure and of its time bound. -/
  | opaque

/-- How the multi-call simulator `π` is read. -/
def hview (π : Expr) : MetaM HView := do
  let π := (← instantiateMVars π).consumeMData.headBeta
  let .const f _ := π.getAppFn | return .opaque
  if f == ``MultiHybrid.tensor && π.getAppNumArgs == 12 then
    return .tensor π.getAppArgs[10]! π.getAppArgs[11]!
  if (← getEnv).contains (f ++ `timed) then return .leaf f
  let some e ← unfoldDefinition? π
    | throwError "derive_simulator: `{π}` has no costed form and cannot be unfolded"
  let e := e.consumeMData.headBeta
  if e.getAppFn.isConstOf ``MultiHybrid.mk then return .leaf f
  return .unfold e

/-- The head constants of the leaves of the multi-call simulator `π`. -/
partial def hybridLeaves (π : Expr) : MetaM (Array Name) := do
  match ← hview π with
  | .tensor p p' => return (← hybridLeaves p) ++ (← hybridLeaves p')
  | .leaf f => return #[f]
  | .unfold e => hybridLeaves e
  | .opaque => return #[]

/-- The steps of a multi-call simulator. -/
def steps : Array Name := #[`start, `resume, `finish]

/-- Bind the metavariables `ms`, from the `i`-th on, as locals of the same names with the given
binder infos, each assigned to its local. -/
partial def withMVarsAsFVars {α : Type} (ms : Array (MVarId × BinderInfo)) (i : Nat)
    (acc : Array Expr) (k : Array Expr → TermElabM α) : TermElabM α := do
  if h : i < ms.size then
    let (m, bi) := ms[i]
    let ty ← instantiateMVars (← m.getType)
    let n := (← m.getDecl).userName
    let n := if n.isAnonymous then `x else n
    withLocalDecl n bi ty fun x => do
      m.assign x
      withMVarsAsFVars ms (i + 1) (acc.push x) k
  else k acc

/-- The theorem or definition `n` applied to metavariables, with its explicit binders assigned
to `args` in order and its type unified with `expected?`: the instance and its type. -/
def applyConst (n : Name) (args : Array Expr) (expected? : Option Expr := none) :
    MetaM (Expr × Expr) := do
  let c ← mkConstWithFreshMVarLevels n
  let (ms, bis, ty) ← forallMetaTelescopeReducing (← inferType c)
  let mut j := 0
  for m in ms, bi in bis do
    if bi.isExplicit then
      let some a := args[j]? | throwError "derive_simulator: too few arguments for `{n}`"
      j := j + 1
      unless ← isDefEq (← inferType m) (← inferType a) do
        throwError "derive_simulator: the argument `{a}` of `{n}` has \
          type{indentExpr (← inferType a)}\nexpected{indentExpr (← inferType m)}"
      m.mvarId!.assign a
  if let some ex := expected? then
    unless ← isDefEq ty ex do
      throwError "derive_simulator: `{n}` has type{indentExpr ty}\nexpected{indentExpr ex}"
  for m in ms do
    unless ← m.mvarId!.isAssigned do
      throwError "derive_simulator: an argument of `{n}` is not determined{indentExpr ty}"
  return (← instantiateMVars (mkAppN c ms), ← instantiateMVars ty)

/-- Unify the hypothesis `m` with one of `hyps` of the same type, or add it to `hyps`. -/
def shareHyp (hyps : IO.Ref (Array (MVarId × BinderInfo))) (m : MVarId) : MetaM Unit := do
  let ty ← m.getType
  for (h, _) in ← hyps.get do
    let s ← saveState
    if ← isDefEq ty (← h.getType) then
      m.assign (mkMVar h)
      return
    s.restore
  hyps.modify (·.push (m, .default))

/-- Record the binders `ms` of an instantiated theorem that unification left open: each
proposition in `hyps` (shared with an earlier hypothesis of the same type), each other binder
in `rest` with the binder info `bi`. -/
def recordOpen (rest hyps : IO.Ref (Array (MVarId × BinderInfo))) (bi : BinderInfo)
    (ms : Array Expr) : MetaM Unit := do
  for m in ms do
    if !(← m.mvarId!.isAssigned) && (← isProp (← inferType m)) then
      shareHyp hyps m.mvarId!
  for m in ms do
    if !(← m.mvarId!.isAssigned) && !(← isProp (← inferType m)) then
      rest.modify (·.push (m.mvarId!, bi))

/-- The erasure theorem `thm`, a statement `Erases A x`, instantiated at `x := target`: the
costed value `A` and the proof. -/
def instErasure (prims hyps : IO.Ref (Array (MVarId × BinderInfo))) (thm : Name)
    (target : Expr) : MetaM (Expr × Expr) := do
  let c ← mkConstWithFreshMVarLevels thm
  let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType c)
  let concl ← instantiateMVars concl
  unless ← isDefEq concl.appArg! target do
    throwError "derive_simulator: the erasure theorem `{thm}` does not erase \
      to{indentExpr target}"
  recordOpen prims hyps .default ms
  return (← instantiateMVars concl.appFn!.appArg!, ← instantiateMVars (mkAppN c ms))

/-- The costed form of a multi-call simulator `π` and its erasure proof; the binders left open
are recorded in `prims` (data) and `hyps` (propositions). -/
partial def costHybrid (prims hyps : IO.Ref (Array (MVarId × BinderInfo))) (π : Expr) :
    MetaM (Expr × Expr) := do
  match ← hview π with
  | .unfold e => costHybrid prims hyps e
  | .opaque =>
    let ty ← whnfR (← inferType π)
    let base ← match (← instantiateMVars π).consumeMData with
      | .fvar x => x.getUserName
      | _ => pure `π
    let A ← mkFreshExprMVar (mkAppN (mkConst ``MultiHybrid.Timed) ty.getAppArgs)
      (userName := base.appendAfter "T")
    prims.modify (·.push (A.mvarId!, .default))
    let h ← mkFreshExprMVar (← mkAppM ``MultiHybrid.Timed.Erases #[A, π])
      (userName := base.appendAfter "_erases")
    shareHyp hyps h.mvarId!
    return (A, ← instantiateMVars h)
  | .tensor p p' =>
    let (A, pA) ← costHybrid prims hyps p
    let (A', pA') ← costHybrid prims hyps p'
    let (T, _) ← applyConst ``MultiHybrid.Timed.tensor #[p, p', A, A']
    let (pf, _) ← applyConst ``MultiHybrid.Timed.tensor_erases #[pA, pA']
      (← mkAppM ``MultiHybrid.Timed.Erases #[T, π])
    return (T, pf)
  | .leaf f => instErasure prims hyps (f ++ `erase_timed) π

/-- The costed simulator of the node and its erasure proof. -/
partial def costNode (prims hyps : IO.Ref (Array (MVarId × BinderInfo))) :
    Node → MetaM (Expr × Expr)
  | .derived S c => instErasure prims hyps (c ++ `erase_timed) S
  | .leaf S π h => do
    let (A, pA) ← costHybrid prims hyps π
    let (T, _) ← applyConst ``Simulator.Timed.ofMultiHybrid #[A] (← timedTy S)
    let (pf, _) ← applyConst ``Simulator.ofMultiHybrid.erase_timed #[pA, h]
      (← mkAppM ``Simulator.Timed.Erases #[T, S])
    return (T, pf)
  | .comp S n₁ n₂ => do
    let (T₁, p₁) ← costNode prims hyps n₁
    let (T₂, p₂) ← costNode prims hyps n₂
    let T ← mkAppM ``Simulator.Timed.comp #[T₁, T₂]
    let (pf, _) ← applyConst ``Simulator.comp.erase_timed #[p₁, p₂]
      (← mkAppM ``Simulator.Timed.Erases #[T, S])
    return (T, pf)
  | .tensor S π π' h h' => do
    let (A, pA) ← costHybrid prims hyps π
    let (A', pA') ← costHybrid prims hyps π'
    let (T, _) ← applyConst ``Simulator.tensor.timed #[π, π', A, A'] (← timedTy S)
    let (pf, _) ← applyConst ``Simulator.tensor.erase_timed #[pA, pA', h, h']
      (← mkAppM ``Simulator.Timed.Erases #[T, S])
    return (T, pf)
where
  /-- The costed type of the simulator `S`. -/
  timedTy (S : Expr) : MetaM Expr := do
    let ty ← whnfR (← inferType S)
    return mkAppN (mkConst ``Simulator.Timed) ty.getAppArgs

/-- A proof of `A.TimeBound a b c` for the costed multi-call simulator `A`: from the step
theorems `f.step.tree.timeBound_timed` of a costed form `f.timed`, from
`MultiHybrid.Timed.tensor_timeBound` for a costed tensor, and from a hypothesis for a costed
binder; the bound variables and hypotheses are recorded in `bounds` and `hyps`. -/
partial def timeHybrid (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (A : Expr) :
    MetaM Expr := do
  let A ← instantiateMVars A
  let .const f _ := A.getAppFn | do
    let nat := Lean.mkConst ``Nat
    let base ← match A with
      | .fvar x => x.getUserName
      | _ => pure `π
    let a ← mkFreshExprMVar nat (userName := base.appendAfter "_start")
    let b ← mkFreshExprMVar nat (userName := base.appendAfter "_resume")
    let c ← mkFreshExprMVar nat (userName := base.appendAfter "_finish")
    for m in #[a, b, c] do bounds.modify (·.push (m.mvarId!, .implicit))
    let h ← mkFreshExprMVar (← mkAppM ``MultiHybrid.Timed.TimeBound #[A, a, b, c])
      (userName := base.appendAfter "_time")
    shareHyp hyps h.mvarId!
    instantiateMVars h
  if f == ``MultiHybrid.Timed.tensor && A.getAppNumArgs == 14 then
    let args := A.getAppArgs
    let p ← timeHybrid bounds hyps args[12]!
    let p' ← timeHybrid bounds hyps args[13]!
    return (← applyConst ``MultiHybrid.Timed.tensor_timeBound #[args[10]!, args[11]!, p, p']).1
  let f := f.getPrefix
  let targs := A.getAppArgs
  let mut pfs := #[]
  let mut bs := #[]
  for st in steps do
    let thm ← mkConstWithFreshMVarLevels (f ++ st ++ `tree ++ `timeBound_timed)
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType thm)
    for i in [0:targs.size] do
      unless ← isDefEq ms[i]! targs[i]! do
        throwError "derive_simulator: `{thm}` does not take the arguments of `{A}`"
    let sM := ms[targs.size]!
    let aM := ms[targs.size + 1]!
    recordOpen bounds hyps .implicit (ms.extract (targs.size + 2) ms.size)
    let B ← instantiateMVars concl.appArg!
    if B.findMVar? (fun m => m == sM.mvarId! || m == aM.mvarId!) |>.isSome then
      throwError "derive_simulator: the bound of `{thm}` depends on the input of the step"
    let sTy ← instantiateMVars (← inferType sM)
    let aTy ← instantiateMVars (← inferType aM)
    let pf ← withLocalDeclD `s sTy fun s =>
      withLocalDeclD `a aTy fun a => do
        sM.mvarId!.assign s
        aM.mvarId!.assign a
        mkLambdaFVars #[s, a] (← instantiateMVars (mkAppN thm ms))
    pfs := pfs.push pf
    bs := bs.push B
  let pf ← mkAppM ``And.intro #[pfs[0]!, ← mkAppM ``And.intro #[pfs[1]!, pfs[2]!]]
  mkExpectedTypeHint pf (← mkAppM ``MultiHybrid.Timed.TimeBound #[A, bs[0]!, bs[1]!, bs[2]!])

/-- The time-bound proof of the costed simulator `T` of the node. -/
partial def timeNode (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (T : Expr) :
    Node → MetaM Expr
  | .derived _ c => do
    let thm ← mkConstWithFreshMVarLevels (c ++ `timeBound_timed)
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType thm)
    let concl ← instantiateMVars concl
    unless ← isDefEq concl.appFn!.appArg! (← instantiateMVars T) do
      throwError "derive_simulator: the time theorem `{c ++ `timeBound_timed}` does not \
        bound{indentExpr T}"
    recordOpen bounds hyps .implicit ms
    instantiateMVars (mkAppN thm ms)
  | .leaf .. => do
    let T ← instantiateMVars T
    let pA ← timeHybrid bounds hyps T.appArg!
    let t ← mkFreshExprMVar (mkConst ``Nat)
    return (← applyConst ``Simulator.ofMultiHybrid.timeBound_timed #[pA]
      (← mkAppM ``Simulator.Timed.TimeBound #[T, t])).1
  | .comp _ n₁ n₂ => do
    let T ← instantiateMVars T
    let p₁ ← timeNode bounds hyps T.appFn!.appArg! n₁
    let p₂ ← timeNode bounds hyps T.appArg! n₂
    let t ← mkFreshExprMVar (mkConst ``Nat)
    return (← applyConst ``Simulator.comp.timeBound_timed #[p₁, p₂]
      (← mkAppM ``Simulator.Timed.TimeBound #[T, t])).1
  | .tensor _ π π' _ _ => do
    let T ← instantiateMVars T
    let args := T.getAppArgs
    let pA ← timeHybrid bounds hyps args[args.size - 2]!
    let pA' ← timeHybrid bounds hyps args[args.size - 1]!
    let t ← mkFreshExprMVar (mkConst ``Nat)
    return (← applyConst ``Simulator.tensor.timeBound_timed #[π, π', pA, pA']
      (← mkAppM ``Simulator.Timed.TimeBound #[T, t])).1

/-- The bound `B` of the time proof `pf` simplified, with the proof of the simplified bound. -/
def simplifyBound (pf B : Expr) : MetaM (Expr × Expr) := do
  let ctx ← Simp.Context.ofNames [``Nat.zero_max, ``Nat.max_zero, ``max_self, ``Nat.add_assoc,
    ``max_eq_left, ``max_eq_right] true
  let (r, _) ← simp B ctx (simprocs := #[← Simp.getSimprocs])
  match r.proof? with
  | some p =>
    return (← mkAppM ``Simulator.Timed.TimeBound.mono #[pf, ← mkAppM ``le_of_eq #[p]], r.expr)
  | none => return (pf, r.expr)

/-- Define `c.timed` and prove `c.erase_timed` and `c.timeBound_timed` for a simulator `c`
whose costed multi-call simulators have their costed forms and step theorems. -/
def deriveSimulator (c : Name) : TermElabM Unit := do
  let info ← getConstInfoDefn c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun bnds _ => do
    let S := mkAppN (mkConst c lvls) bnds
    let node ← parse S
    let prims ← IO.mkRef #[]
    let ehyps ← IO.mkRef #[]
    let (T, epf) ← costNode prims ehyps node
    withMVarsAsFVars (← prims.get) 0 #[] fun primFvs => do
    let T ← instantiateMVars T
    let mut kept := #[]
    for b in bnds do
      if !(← isProp (← inferType b)) || T.containsFVar b.fvarId! then kept := kept.push b
    let timedBs := kept ++ primFvs
    let tName := c ++ `timed
    CatCrypt.Tactics.DeriveTimed.addTimedDef tName info.levelParams
      (← mkForallFVars timedBs (← inferType T)) (← mkLambdaFVars timedBs T)
    let Tc := mkAppN (mkConst tName lvls) timedBs
    withMVarsAsFVars (← ehyps.get) 0 #[] fun hypFvs => do
      let epf ← instantiateMVars epf
      if epf.hasExprMVar then throwError "derive_simulator: the erasure proof is incomplete"
      let eBs := bnds ++ primFvs ++ hypFvs
      let ety ← mkForallFVars eBs (← mkAppM ``Simulator.Timed.Erases #[Tc, S])
      let evalue ← mkLambdaFVars eBs epf
      let eName := c ++ `erase_timed
      addDecl (Declaration.thmDecl
        { name := eName, levelParams := info.levelParams, type := ety, value := evalue })
    let bounds ← IO.mkRef #[]
    let thyps ← IO.mkRef #[]
    let tpf ← timeNode bounds thyps T node
    let (tpf, B) ← simplifyBound tpf (← instantiateMVars (← inferType tpf)).appArg!
    withMVarsAsFVars ((← bounds.get) ++ (← thyps.get)) 0 #[] fun tFvs => do
      let tpf ← instantiateMVars tpf
      let B ← instantiateMVars B
      if tpf.hasExprMVar then throwError "derive_simulator: the time proof is incomplete"
      let tBs := timedBs ++ tFvs
      let tty ← mkForallFVars tBs (← mkAppM ``Simulator.Timed.TimeBound #[Tc, B])
      let tvalue ← mkLambdaFVars tBs tpf
      let bName := c ++ `timeBound_timed
      addDecl (Declaration.thmDecl
        { name := bName, levelParams := info.levelParams, type := tty, value := tvalue })

/-- The head constants of the costed multi-call simulators of `c`. -/
def hybridHeads (c : Name) : TermElabM (Array Name) := do
  let info ← getConstInfoDefn c
  forallTelescope info.type fun xs _ => do
    let node ← parse (mkAppN (mkConst c (info.levelParams.map mkLevelParam)) xs)
    let mut heads := #[]
    for π in node.hybrids do
      for f in ← hybridLeaves π do
        unless heads.contains f do heads := heads.push f
    return heads

end

/-- `derive_simulator S` defines the costed form `S.timed` of a bundled simulator `S` built
from `Simulator.ofMultiHybrid`, `Simulator.comp` and `Simulator.tensor`, and proves its erasure
theorem `S.erase_timed` and its time theorem `S.timeBound_timed`. -/
syntax (name := deriveSimulatorCmd) "derive_simulator " ident : command

/-- Elaborate `derive_simulator S`: derive the costed forms and step theorems of the costed
multi-call simulators of `S` that are missing, then the costed form of `S`. -/
@[command_elab deriveSimulatorCmd]
meta def elabDeriveSimulator : CommandElab := fun stx => do
  let c ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let heads ← liftTermElabM <| hybridHeads c
  for f in heads do
    unless (← getEnv).contains (f ++ `timed) do
      elabCommand (← `(command| derive_reduction $(mkCIdent f)))
    for st in steps do
      let t := f ++ st ++ `tree
      unless (← getEnv).contains (t ++ `timeBound_timed) do
        elabCommand (← `(command| derive_time_bound $(mkCIdent t)))
  let env ← getEnv
  let needed := heads.flatMap fun f =>
    #[f ++ `timed, f ++ `erase_timed] ++ steps.map (f ++ · ++ `tree ++ `timeBound_timed)
  let missing := needed.filter (!env.contains ·)
  unless missing.isEmpty do
    throwError "derive_simulator: `{c}` needs the declarations {missing.toList}, which are not \
      derived"
  liftTermElabM <| deriveSimulator c

end CatCrypt.Tactics.DeriveSimulator

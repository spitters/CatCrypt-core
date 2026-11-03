/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostMono
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Costed forms of bundled simulators

`derive_simulator S` takes a definition `S` whose value is a bundled simulator `Simulator …` of
`UCSimulator.lean` and defines its costed form `S.timed : … → Simulator.Timed …`, proves its
erasure theorem `S.erase_timed : … → (S.timed …).Erases (S …)` and its time theorem
`S.timeBound_timed : … → (S.timed …).TimeBound B`, with the naming of `derive_reduction`.

## Reading the simulator

The value of `S` is read as a term of five constructions, by its head constant:

| head                                | costed form                                  |
|---|---|
| `Simulator.ofMultiHybrid π h`       | `.ofMultiHybrid πT` or `.ofMultiHybridHat εs πT` |
| `S₁.comp S₂`                        | `Simulator.Timed.comp T₁ T₂`                 |
| `Simulator.tensor π π' h h'`        | `Simulator.tensor.timed π π' πT π'T`         |
| `S₀.mapPorts f g hf hg`             | `Simulator.Timed.mapPorts T₀ f g`            |
| `S₀.mono hVev hVout hWev hWout`     | `Simulator.Timed.mono T₀ V' W'`              |
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
* when `f.erase_timed` states `MultiHybrid.Timed.ErasesHat` (the state of `f` holds functions,
  so its costed form runs on costed states and events), the leaf is
  `Simulator.Timed.ofMultiHybridHat` with the erasure maps of that statement, also when `π` is
  a definition that unfolds to an application of `f` (a protocol simulator defined as a loop
  `Prog.loopMulti` of a party program, costed by `Prog.loopMulti.timed`); its time is
  `f.timeBoundGraded_timed` or `f.timeBoundInv_timed` (a time bound on the states of an
  invariant) when it exists, else the time theorem from the step theorems
  `f.step.treeHat.timeBound_timed` when their bounds and hypotheses do not depend on the state;
  otherwise the command refuses it, with an error that names these theorems; such a leaf is not
  accepted inside a tensor;
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
type is that of an earlier one is shared with it. A hypothesis of the time theorem that bounds
a costed machine with a constant head is refused: the time of the simulator being certified is
proved, and only a costed binder or a cost companion of a parameter is taken as a hypothesis.

The bound of `S.timeBound_timed` is the bound of the construction: the largest bound of the
steps for a costed multi-call simulator, the sum of the bounds for a composite, the bound of the
simulator for a relabelled one; it is simplified by `max 0 a = a`, `max a a = a`, associativity
of `+`, numeral arithmetic and the maxima of comparable numerals, with the monotonicity of the
time bound (`Simulator.Timed.TimeBound.mono`).

When a leaf has a graded time theorem `f.timeBoundGraded_timed` (its `j`-th step costs at most
`a + b * j`, as for a loop whose state grows with the activations, `Prog.loopMulti`), its step
theorems are not required and the time theorem is the graded one, `S.timeBoundGraded_timed : … → (S.timed …).TimeBoundGraded a b`: the
graded rules of `UCSimulatorCostGraded.lean` for leaves, composites and relabellings, and the
time bound with no growth for the other nodes (`Simulator.Timed.TimeBound.timeBoundGraded`).

When a leaf also has a size-graded time theorem `f.timeBoundSized_timed` (its step on `x` costs
at most `a + b * j + c * s x`, as for a loop whose body works on data of the size of the event,
`Prog.loopMulti.timeBoundSized_timed`), the command proves in addition
`S.timeBoundSized_timed : … → (S.timed …).TimeBoundSized sE sO a b c`, with the sizes `sE` of
the outer events and `sO` of the answers as implicit binders: the size-graded rules of
`UCSimulatorCostSized.lean` for leaves, composites (size `0` on the middle interface) and
relabellings, and the graded bound with the constant `0` of the size for the other nodes
(`Simulator.Timed.TimeBoundGraded.timeBoundSized`).

## Main definitions

* `derive_simulator S` — define `S.timed`, prove `S.erase_timed` and `S.timeBound_timed`
  (or `S.timeBoundGraded_timed`, and `S.timeBoundSized_timed` for a leaf with a size-graded
  time theorem)
* `derive_hybrid_time R` — prove `R.timeBound_timed` for the costed form `R.timed` of a hybrid
  machine (`Hybrid.Timed` or `MultiHybrid.Timed`) from the time theorems of its steps, the trees
  `R.st.tree` or, for a costed form on costed states, `R.st.treeHat`
* `derive_simulator (suffix := s) S` — the same with the costed forms and theorems named by `s`
  in place of `timed` (`S.s`, `S.erase_s`, `S.timeBoundGraded_s`), reading those of its
  multi-call simulators and deriving the missing ones by `derive_reduction (suffix := s)`; a leaf
  takes a graded or invariant time theorem (`f.timeBoundGraded_s`, `f.timeBoundInv_s`) or step
  theorems `f.st.tree.timeBound_s`, which `derive_time_bound` does not state
-/

public section

namespace CatCrypt.Tactics.DeriveSimulator

open Lean Meta Elab Term Command
open CatCrypt.Crypto.UCTransparent

meta section

/-- The suffix `s` of the costed forms that `derive_simulator` reads and defines (`c.s`,
`c.erase_s`, `c.timeBound_s`), the option `derive_simulator.suffix` that
`derive_simulator (suffix := s)` sets; `timed` by default. -/
def sfx : CoreM Name :=
  return (← getOptions).get `derive_simulator.suffix `timed

/-- The name `pre_s` of a theorem about the costed form of suffix `s = sfx` (`erase_timed`,
`timeBound_timed` at the default suffix). -/
def sfxName (pre : String) : CoreM Name :=
  return Name.mkSimple (pre ++ "_" ++ (← sfx).toString)

/-- A bundled simulator read as a term of the constructions of the costed mirror. -/
inductive Node where
  /-- `Simulator.ofMultiHybrid π h`. -/
  | leaf (S π h : Expr)
  /-- `S₁.comp S₂`. -/
  | comp (S : Expr) (n₁ n₂ : Node)
  /-- `Simulator.tensor π π' h h'`. -/
  | tensor (S π π' h h' : Expr)
  /-- `S₀.mapPorts f g hf hg`. -/
  | mapPorts (S : Expr) (n : Node) (f g hf hg : Expr)
  /-- `S₀.mono hVev hVout hWev hWout`. -/
  | mono (S : Expr) (n : Node) (hVev hVout hWev hWout : Expr)
  /-- An application of a simulator `c` with a costed form `c.timed`, `c.erase_timed` and
  `c.timeBound_timed`. -/
  | derived (S : Expr) (c : Name)

/-- Read the simulator `e` as a term of `Simulator.ofMultiHybrid`, `Simulator.comp`,
`Simulator.tensor`, `Simulator.mapPorts`, `Simulator.mono` and simulators with a costed form,
unfolding any other head constant once and retrying. -/
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
    if n == ``Simulator.mapPorts && args.size == 14 then
      return .mapPorts e (← parse args[9]!) args[10]! args[11]! args[12]! args[13]!
    if n == ``Simulator.mono && args.size == 13 then
      return .mono e (← parse args[6]!) args[9]! args[10]! args[11]! args[12]!
    let env ← getEnv
    if env.contains (n ++ (← sfx)) && env.contains (n ++ (← sfxName "erase")) &&
        env.contains (n ++ (← sfxName "timeBound")) then
      return .derived e n
    match ← unfoldDefinition? e with
    | some e' => parse e'
    | none => throwError "derive_simulator: `{e}` is not built from `Simulator.ofMultiHybrid`, \
        `Simulator.comp`, `Simulator.tensor`, `Simulator.mapPorts` and `Simulator.mono`"
  | _ => throwError "derive_simulator: `{e}` is not built from `Simulator.ofMultiHybrid`, \
      `Simulator.comp`, `Simulator.tensor`, `Simulator.mapPorts` and `Simulator.mono`"

/-- The multi-call simulators of a node. -/
def Node.hybrids : Node → Array Expr
  | .leaf _ π _ => #[π]
  | .comp _ n₁ n₂ => n₁.hybrids ++ n₂.hybrids
  | .mapPorts _ n .. => n.hybrids
  | .mono _ n .. => n.hybrids
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

/-- Whether the erasure theorem `f.erase_timed` states `MultiHybrid.Timed.ErasesHat`: the
costed form of `f` runs on costed states and events. -/
def isHat (f : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? (f ++ (← sfxName "erase")) | return false
  forallTelescopeReducing ci.type fun _ concl =>
    return concl.getAppFn.isConstOf ``MultiHybrid.Timed.ErasesHat

/-- The steps of the costed form of `f` are the trees `f.st.treeHat` when it runs on costed
states, `f.st.tree` otherwise. -/
def treeName (f : Name) : MetaM Name := do
  if (← getEnv).contains (f ++ `start ++ `treeHat ++ (← sfx)) then return `treeHat
  return `tree

/-- How the multi-call simulator `π` is read. -/
def hview (π : Expr) : MetaM HView := do
  let π := (← instantiateMVars π).consumeMData.headBeta
  let .const f _ := π.getAppFn | return .opaque
  if f == ``MultiHybrid.tensor && π.getAppNumArgs == 12 then
    return .tensor π.getAppArgs[10]! π.getAppArgs[11]!
  if (← getEnv).contains (f ++ (← sfx)) then return .leaf f
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

/-- The erasure theorem `thm`, a statement `Erases A x` or `ErasesHat … εs A x`, instantiated
at `x := target`: the conclusion, the costed value `A` and the proof. -/
def instErasure (prims hyps : IO.Ref (Array (MVarId × BinderInfo))) (thm : Name)
    (target : Expr) : MetaM (Expr × Expr × Expr) := do
  let c ← mkConstWithFreshMVarLevels thm
  let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType c)
  let concl ← instantiateMVars concl
  unless ← isDefEq concl.appArg! target do
    throwError "derive_simulator: the erasure theorem `{thm}` does not erase \
      to{indentExpr target}"
  recordOpen prims hyps .default ms
  return (← instantiateMVars concl, ← instantiateMVars concl.appFn!.appArg!,
    ← instantiateMVars (mkAppN c ms))

/-- The costed form of a multi-call simulator `π` on plain states and its erasure proof; the
binders left open are recorded in `prims` (data) and `hyps` (propositions). -/
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
  | .leaf f =>
    if ← isHat f then
      throwError "derive_simulator: the costed form of `{f}` runs on costed states; it is \
        accepted at a leaf `Simulator.ofMultiHybrid`, not inside a tensor"
    let (_, A, pf) ← instErasure prims hyps (f ++ (← sfxName "erase")) π
    return (A, pf)

/-- The multi-call simulator `π`, unfolded until its head constant `f` has a costed form, when
that costed form runs on costed states (`isHat f`): `f` and the unfolded term. A loop of a
party program (`Prog.loopMulti`, costed by `Prog.loopMulti.timed`) behind the definitions of a
protocol is read this way. -/
partial def hatLeaf? (π : Expr) : MetaM (Option (Name × Expr)) := do
  let π := (← instantiateMVars π).consumeMData.headBeta
  let .const f _ := π.getAppFn | return none
  if (← getEnv).contains (f ++ (← sfx)) then
    return if ← isHat f then some (f, π) else none
  if f == ``MultiHybrid.tensor then return none
  match ← unfoldDefinition? π with
  | some e => hatLeaf? e
  | none => return none

/-- The type of costed simulators of the type of the simulator `S`. -/
def timedTy (S : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType S)
  return mkAppN (mkConst ``Simulator.Timed) ty.getAppArgs

/-- The costed simulator of the node and its erasure proof. -/
partial def costNode (prims hyps : IO.Ref (Array (MVarId × BinderInfo))) :
    Node → MetaM (Expr × Expr)
  | .derived S c => do
    let (_, T, pf) ← instErasure prims hyps (c ++ (← sfxName "erase")) S
    return (T, pf)
  | .leaf S π h => do
    if let some (f, π') ← hatLeaf? π then
      let (concl, A, pA) ← instErasure prims hyps (f ++ (← sfxName "erase")) π'
      let a := concl.getAppArgs
      let (T, _) ← applyConst ``Simulator.Timed.ofMultiHybridHat
        #[a[10]!, a[11]!, a[12]!, a[13]!, a[14]!, A] (← timedTy S)
      let (pf, _) ← applyConst ``Simulator.ofMultiHybridHat.erase_timed #[pA, h]
        (← mkAppM ``Simulator.Timed.Erases #[T, S])
      return (T, pf)
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
  | .mapPorts S n f g hf hg => do
    let (T₀, p₀) ← costNode prims hyps n
    let (T, _) ← applyConst ``Simulator.Timed.mapPorts #[T₀, f, g] (← timedTy S)
    let (pf, _) ← applyConst ``Simulator.mapPorts.erase_timed #[p₀, f, g, hf, hg]
      (← mkAppM ``Simulator.Timed.Erases #[T, S])
    return (T, pf)
  | .mono S n hVev hVout hWev hWout => do
    let (T₀, p₀) ← costNode prims hyps n
    let ts := (← timedTy S).getAppArgs
    let T ← mkAppM ``Simulator.Timed.mono #[T₀, ts[4]!, ts[5]!]
    let (pf, _) ← applyConst ``Simulator.mono.erase_timed #[p₀, hVev, hVout, hWev, hWout]
      (← mkAppM ``Simulator.Timed.Erases #[T, S])
    return (T, pf)
  | .tensor S π π' h h' => do
    let (A, pA) ← costHybrid prims hyps π
    let (A', pA') ← costHybrid prims hyps π'
    let (T, _) ← applyConst ``Simulator.tensor.timed #[π, π', A, A'] (← timedTy S)
    let (pf, _) ← applyConst ``Simulator.tensor.erase_timed #[pA, pA', h, h']
      (← mkAppM ``Simulator.Timed.Erases #[T, S])
    return (T, pf)

/-- The binder names of the head constant of `A` at its arguments, without macro scopes. -/
def argNames (A : Expr) : MetaM (Array Name) := do
  let .const c _ := A.getAppFn | return #[]
  let ci ← getConstInfo c
  return (ci.type.getForallBinderNames.toArray.extract 0 A.getAppNumArgs).map
    (·.eraseMacroScopes)

/-- Assign to the binders `ms` of the theorem `thm` (with binder names `thmNames`) the arguments
`targs` of a costed machine (with binder names `tNames`), each to the binder of the same name,
or to the binder at the same position when no binder of `thm` has that name: the indices of
the binders assigned. -/
def matchArgs (thm : Expr) (tNames : Array Name) (thmNames : List Name) (ms targs : Array Expr) :
    MetaM (Array Nat) := do
  let thmNames := thmNames.toArray.map (·.eraseMacroScopes)
  let mut used : Array Nat := #[]
  for i in [0:targs.size] do
    let byName := match tNames[i]? with
      | some n => (List.range (min thmNames.size ms.size)).find? fun j =>
          thmNames[j]! == n && !used.contains j
      | none => none
    let j := byName.getD i
    if used.contains j || ms.size ≤ j then
      throwError "derive_simulator: `{thm}` does not take the arguments of the costed machine"
    unless ← isDefEq ms[j]! targs[i]! do
      throwError "derive_simulator: `{thm}` does not take the argument `{targs[i]!}`"
    used := used.push j
  return used

/-- The time bound `tb A B₁ ⋯ Bₙ` of the costed machine `A`, an application of `f.timed`, from
the step theorems `f.st.tr.timeBound_timed` (`tr` is `tree` or `treeHat`) of the steps `sts`,
each a bound `∀ s a, … ≤ Bᵢ` that does not depend on the state or the input of the step, nor do
its hypotheses. The arguments of `A` go to the binders of the step theorem of the same names
(`matchArgs`), the state and the input to the first two binders left; the other binders are
recorded in `bounds` and `hyps`. -/
def stepsTimeBound (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (tb f : Name)
    (sts : Array Name) (A : Expr) : MetaM Expr := do
  let targs := A.getAppArgs
  let tr ← treeName f
  let tNames ← argNames A
  let mut pfs := #[]
  let mut bs := #[]
  for st in sts do
    let thm ← mkConstWithFreshMVarLevels (f ++ st ++ tr ++ (← sfxName "timeBound"))
    let thmTy ← inferType thm
    let (ms, _, concl) ← forallMetaTelescopeReducing thmTy
    unless targs.size + 2 ≤ ms.size do
      throwError "derive_simulator: `{thm}` does not take the arguments of `{A}` and the \
        inputs of the step"
    let used ← matchArgs thm tNames thmTy.getForallBinderNames ms targs
    let free := (List.range ms.size).filter (!used.contains ·)
    let (some si, some ai) := (free[0]?, free[1]?)
      | throwError "derive_simulator: `{thm}` does not take the inputs of the step"
    let sM := ms[si]!
    let aM := ms[ai]!
    let onStep (e : Expr) : Bool :=
      (e.findMVar? fun m => m == sM.mvarId! || m == aM.mvarId!).isSome
    let rest := (free.drop 2).toArray.map (ms[·]!)
    let B ← instantiateMVars concl.appArg!
    let mut stateDep := onStep B
    for m in rest do
      if onStep (← instantiateMVars (← inferType m)) then stateDep := true
    if stateDep then
      throwError "derive_simulator: the bound of `{thm}` or a hypothesis of it depends on the \
        state or the input of the step"
    recordOpen bounds hyps .implicit rest
    let sTy ← instantiateMVars (← inferType sM)
    let aTy ← instantiateMVars (← inferType aM)
    let pf ← withLocalDeclD `s sTy fun s =>
      withLocalDeclD `a aTy fun a => do
        sM.mvarId!.assign s
        aM.mvarId!.assign a
        mkLambdaFVars #[s, a] (← instantiateMVars (mkAppN thm ms))
    pfs := pfs.push pf
    bs := bs.push B
  let some last := pfs.back? | throwError "derive_simulator: no steps"
  let pf ← pfs.pop.foldrM (fun p acc => mkAppM ``And.intro #[p, acc]) last
  mkExpectedTypeHint pf (← mkAppM tb (#[A] ++ bs))

/-- A proof of `A.TimeBound a b c` for the costed multi-call simulator `A` on plain states: from
the step theorems of a costed form `f.timed`, from `MultiHybrid.Timed.tensor_timeBound` for a
costed tensor, and from a hypothesis for a costed binder; the bound variables and hypotheses
are recorded in `bounds` and `hyps`. -/
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
  try
    stepsTimeBound bounds hyps ``MultiHybrid.Timed.TimeBound f steps A
  catch e =>
    throwError "derive_simulator: the costed form of `{f}` has no time bound independent of the \
      state. Prove `{f ++ (← sfxName "timeBoundGraded")}` (a step after `i` activations costs at \
      most `a + b * i`) before this command:{indentD e.toMessageData}"

/-- A proof of `A.TimeBoundInv Inv a b c` for the costed multi-call simulator `A` on costed
states, an application of `f.timed`: the theorem `f.timeBoundInv_timed` when it exists; else
the plain time theorem from the step theorems of `f`, when their bounds do not depend on the
state. Otherwise the leaf has no time bound and the command refuses it: an assumed bound of the
machine being certified is not a certificate. -/
def timeHybridHat (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (A : Expr) :
    MetaM Expr := do
  let A ← instantiateMVars A
  let .const ft _ := A.getAppFn | throwError "derive_simulator: `{A}` is not a costed form"
  let f := ft.getPrefix
  let env ← getEnv
  let inv := f ++ (← sfxName "timeBoundInv")
  if env.contains inv then
    let thm ← mkConstWithFreshMVarLevels inv
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType thm)
    let concl ← instantiateMVars concl
    unless ← isDefEq (concl.getArg! 5) A do
      throwError "derive_simulator: `{inv}` does not bound{indentExpr A}"
    recordOpen bounds hyps .implicit ms
    return ← instantiateMVars (mkAppN thm ms)
  try
    let pf ← stepsTimeBound bounds hyps ``MultiHybrid.Timed.TimeBound f steps A
    mkAppM ``MultiHybrid.Timed.TimeBoundInv.of_timeBound #[pf]
  catch e =>
    throwError "derive_simulator: the costed form of `{f}` runs on costed states and has no time \
      bound on them. Prove `{f ++ (← sfxName "timeBoundGraded")}` (a step after `i` activations \
      costs at most `a + b * i`) or `{inv}` (a bound on the states of an invariant) \
      before this command:{indentD e.toMessageData}"

/-- The time-bound predicates of costed machines, with the position of the machine among their
arguments. -/
def timeBoundHeads : Array (Name × Nat) :=
  #[(``MultiHybrid.Timed.TimeBound, 5), (``MultiHybrid.Timed.TimeBoundInv, 5),
    (``MultiHybrid.Timed.TimeBoundGraded, 5), (``MultiHybrid.Timed.TimeBoundSized, 5),
    (``Simulator.Timed.TimeBound, 6), (``Simulator.Timed.TimeBoundGraded, 6),
    (``Simulator.Timed.TimeBoundSized, 6)]

/-- Refuse a hypothesis of a time theorem that bounds the time of a costed machine with a constant
head: such a machine belongs to the simulator being certified, and its bound is to be proved. A
bound on a costed binder (a local head) or on a cost companion of a parameter is left as a
hypothesis. -/
def refuseAssumedBounds (c : Name) (hyps : Array (MVarId × BinderInfo)) : MetaM Unit := do
  for (m, _) in hyps do
    unless ← m.isAssigned do
      let ty ← instantiateMVars (← m.getType)
      let .const h _ := ty.getAppFn | continue
      let some (_, i) := timeBoundHeads.find? (·.1 == h) | continue
      let .const ft _ := (ty.getArg! i).getAppFn | continue
      let f := ft.getPrefix
      throwError "derive_simulator: the time theorem of `{c}` would assume the time bound of its \
        own costed form:{indentExpr ty}\nProve `{f ++ (← sfxName "timeBoundGraded")}` or \
        `{f ++ (← sfxName "timeBoundInv")}` before this command, or the bound of the simulator \
        that contains it."

/-- The time-bound proof of the costed simulator `T` of the node. -/
partial def timeNode (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (T : Expr) :
    Node → MetaM Expr
  | .derived _ c => do
    let tb := c ++ (← sfxName "timeBound")
    let thm ← mkConstWithFreshMVarLevels tb
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType thm)
    let concl ← instantiateMVars concl
    unless ← isDefEq concl.appFn!.appArg! (← instantiateMVars T) do
      throwError "derive_simulator: the time theorem `{tb}` does not \
        bound{indentExpr T}"
    recordOpen bounds hyps .implicit ms
    instantiateMVars (mkAppN thm ms)
  | .leaf .. => do
    let T ← instantiateMVars T
    let t ← mkFreshExprMVar (mkConst ``Nat)
    if T.isAppOf ``Simulator.Timed.ofMultiHybridHat then
      let pA ← timeHybridHat bounds hyps T.appArg!
      return (← applyConst ``Simulator.ofMultiHybridHat.timeBound_timed #[pA]
        (← mkAppM ``Simulator.Timed.TimeBound #[T, t])).1
    let pA ← timeHybrid bounds hyps T.appArg!
    return (← applyConst ``Simulator.ofMultiHybrid.timeBound_timed #[pA]
      (← mkAppM ``Simulator.Timed.TimeBound #[T, t])).1
  | .comp _ n₁ n₂ => do
    let T ← instantiateMVars T
    let p₁ ← timeNode bounds hyps T.appFn!.appArg! n₁
    let p₂ ← timeNode bounds hyps T.appArg! n₂
    let t ← mkFreshExprMVar (mkConst ``Nat)
    return (← applyConst ``Simulator.comp.timeBound_timed #[p₁, p₂]
      (← mkAppM ``Simulator.Timed.TimeBound #[T, t])).1
  | .mapPorts _ n f g _ _ => do
    let T ← instantiateMVars T
    let args := T.getAppArgs
    let p ← timeNode bounds hyps args[args.size - 3]! n
    let t ← mkFreshExprMVar (mkConst ``Nat)
    return (← applyConst ``Simulator.mapPorts.timeBound_timed #[p, f, g]
      (← mkAppM ``Simulator.Timed.TimeBound #[T, t])).1
  | .mono _ n .. => do
    let T ← instantiateMVars T
    let args := T.getAppArgs
    let p ← timeNode bounds hyps args[args.size - 3]! n
    return (← applyConst ``Simulator.mono.timeBound_timed
      #[p, args[args.size - 2]!, args[args.size - 1]!]).1
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

/-- The graded time theorem `f.timeBoundGraded_timed` of the costed multi-call simulator of a
leaf `T` (`Simulator.Timed.ofMultiHybrid A` or `ofMultiHybridHat … A`, `A` an application of
`f.timed`), when it exists. -/
def gradedThm? (T : Expr) : MetaM (Option Name) := do
  let T ← instantiateMVars T
  unless T.isAppOf ``Simulator.Timed.ofMultiHybridHat ||
      T.isAppOf ``Simulator.Timed.ofMultiHybrid do return none
  let .const ft _ := T.appArg!.getAppFn | return none
  let g := ft.getPrefix ++ (← sfxName "timeBoundGraded")
  return if (← getEnv).contains g then some g else none

/-- Whether a leaf of the costed simulator `T` of the node has a graded time theorem. -/
partial def nodeGraded (T : Expr) : Node → MetaM Bool
  | .leaf .. => return (← gradedThm? T).isSome
  | .comp _ n₁ n₂ => do
    let T ← instantiateMVars T
    return (← nodeGraded T.appFn!.appArg! n₁) || (← nodeGraded T.appArg! n₂)
  | .mapPorts _ n .. | .mono _ n .. => do
    let T ← instantiateMVars T
    let args := T.getAppArgs
    nodeGraded args[args.size - 3]! n
  | _ => return false

/-- The graded time-bound proof `T.TimeBoundGraded a b` of the costed simulator `T` of the
node: a leaf with a graded time theorem `f.timeBoundGraded_timed` by it, a composite, a
relabelling and a change of views by their graded rules, any other node by its time bound with no
growth. -/
partial def timeNodeGraded (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (T : Expr) :
    Node → MetaM Expr
  | n@(.leaf ..) => do
    let T ← instantiateMVars T
    let some g ← gradedThm? T
      | return (← applyConst ``Simulator.Timed.TimeBound.timeBoundGraded
          #[← timeNode bounds hyps T n]).1
    let A := T.appArg!
    let thm ← mkConstWithFreshMVarLevels g
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType thm)
    let concl ← instantiateMVars concl
    unless ← isDefEq (concl.getArg! 5) A do
      throwError "derive_simulator: `{g}` does not bound{indentExpr A}"
    recordOpen bounds hyps .implicit ms
    let pA ← instantiateMVars (mkAppN thm ms)
    let rule := if T.isAppOf ``Simulator.Timed.ofMultiHybridHat then
      ``Simulator.ofMultiHybridHat.timeBoundGraded_timed
      else ``Simulator.ofMultiHybrid.timeBoundGraded_timed
    let a ← mkFreshExprMVar (mkConst ``Nat)
    let b ← mkFreshExprMVar (mkConst ``Nat)
    return (← applyConst rule #[pA] (← mkAppM ``Simulator.Timed.TimeBoundGraded #[T, a, b])).1
  | .comp _ n₁ n₂ => do
    let T ← instantiateMVars T
    let p₁ ← timeNodeGraded bounds hyps T.appFn!.appArg! n₁
    let p₂ ← timeNodeGraded bounds hyps T.appArg! n₂
    return (← applyConst ``Simulator.comp.timeBoundGraded_timed #[p₁, p₂]).1
  | .mapPorts _ n f g _ _ => do
    let T ← instantiateMVars T
    let args := T.getAppArgs
    let p ← timeNodeGraded bounds hyps args[args.size - 3]! n
    return (← applyConst ``Simulator.mapPorts.timeBoundGraded_timed #[p, f, g]).1
  | .mono _ n .. => do
    let T ← instantiateMVars T
    let args := T.getAppArgs
    let p ← timeNodeGraded bounds hyps args[args.size - 3]! n
    return (← applyConst ``Simulator.mono.timeBoundGraded_timed
      #[p, args[args.size - 2]!, args[args.size - 1]!]).1
  | n => do
    return (← applyConst ``Simulator.Timed.TimeBound.timeBoundGraded
      #[← timeNode bounds hyps T n]).1

/-- The constants `a`, `b` of the graded time proof `pf` simplified, with the proof of the
simplified bound. -/
def simplifyGraded (pf a b : Expr) : MetaM (Expr × Expr × Expr) := do
  let ctx ← Simp.Context.ofNames [``Nat.zero_max, ``Nat.max_zero, ``max_self, ``Nat.add_assoc,
    ``max_eq_left, ``max_eq_right, ``Nat.add_zero, ``Nat.zero_add] true
  let simpLe (x : Expr) : MetaM (Expr × Expr) := do
    let (r, _) ← simp x ctx (simprocs := #[← Simp.getSimprocs])
    match r.proof? with
    | some p => return (← mkAppM ``le_of_eq #[p], r.expr)
    | none => return (← mkAppM ``le_refl #[x], x)
  let (ha, a') ← simpLe a
  let (hb, b') ← simpLe b
  return (← mkAppM ``Simulator.Timed.TimeBoundGraded.mono #[pf, ha, hb], a', b')

/-- The size-graded time theorem `f.timeBoundSized_timed` of the costed multi-call simulator of
a leaf `T` (`Simulator.Timed.ofMultiHybrid A` or `ofMultiHybridHat … A`, `A` an application of
`f.timed`), when it exists. -/
def sizedThm? (T : Expr) : MetaM (Option Name) := do
  let T ← instantiateMVars T
  unless T.isAppOf ``Simulator.Timed.ofMultiHybridHat ||
      T.isAppOf ``Simulator.Timed.ofMultiHybrid do return none
  let .const ft _ := T.appArg!.getAppFn | return none
  let g := ft.getPrefix ++ (← sfxName "timeBoundSized")
  return if (← getEnv).contains g then some g else none

/-- Whether a leaf of the costed simulator `T` of the node has a size-graded time theorem. -/
partial def nodeSized (T : Expr) : Node → MetaM Bool
  | .leaf .. => return (← sizedThm? T).isSome
  | .comp _ n₁ n₂ => do
    let T ← instantiateMVars T
    return (← nodeSized T.appFn!.appArg! n₁) || (← nodeSized T.appArg! n₂)
  | .mapPorts _ n .. | .mono _ n .. => do
    let T ← instantiateMVars T
    let args := T.getAppArgs
    nodeSized args[args.size - 3]! n
  | _ => return false

/-- The port types `E O EG OG V W` of the costed simulator `T`. -/
def portTypes (T : Expr) : MetaM (Array Expr) := do
  return (← whnf (← inferType T)).getAppArgs

/-- The function `fun _ => 0` on `ty`. -/
def constZero (ty : Expr) : MetaM Expr :=
  withLocalDeclD `x ty fun x => mkLambdaFVars #[x] (mkNatLit 0)

/-- The proof of `∀ x, s x ≤ s x` for `s` on `ty`. -/
def leSelf (s ty : Expr) : MetaM Expr :=
  withLocalDeclD `x ty fun x => do mkLambdaFVars #[x] (← mkAppM ``le_refl #[mkApp s x])

/-- The size-graded time-bound proof `T.TimeBoundSized sE sO a b c` of the costed simulator `T`
of the node: a leaf with a size-graded time theorem `f.timeBoundSized_timed` by it, a composite
by its rule with the size `0` on the middle interface, a relabelling and a change of views by
their rules, any other node by its graded time bound with the constant `0` of the size. -/
partial def timeNodeSized (bounds hyps : IO.Ref (Array (MVarId × BinderInfo)))
    (T sE sO : Expr) (n : Node) : MetaM Expr := do
  let T ← instantiateMVars T
  let lift : MetaM Expr := do
    return (← applyConst ``Simulator.Timed.TimeBoundGraded.timeBoundSized
      #[← timeNodeGraded bounds hyps T n, sE, sO]).1
  match n with
  | .leaf .. =>
    let some g ← sizedThm? T | lift
    let A := T.appArg!
    let thm ← mkConstWithFreshMVarLevels g
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType thm)
    let concl ← instantiateMVars concl
    unless ← isDefEq (concl.getArg! 5) A do
      throwError "derive_simulator: `{g}` does not bound{indentExpr A}"
    let rule := if T.isAppOf ``Simulator.Timed.ofMultiHybridHat then
      ``Simulator.ofMultiHybridHat.timeBoundSized_timed
      else ``Simulator.ofMultiHybrid.timeBoundSized_timed
    let a ← mkFreshExprMVar (mkConst ``Nat)
    let b ← mkFreshExprMVar (mkConst ``Nat)
    let c ← mkFreshExprMVar (mkConst ``Nat) .natural `c
    let (pf, _) ← applyConst rule #[← instantiateMVars (mkAppN thm ms)]
      (← mkAppM ``Simulator.Timed.TimeBoundSized #[T, sE, sO, a, b, c])
    recordOpen bounds hyps .implicit ms
    return pf
  | .comp _ n₁ n₂ =>
    let T₁ := T.appFn!.appArg!
    let ts ← portTypes T₁
    let p₁ ← timeNodeSized bounds hyps T₁ sE (← constZero ts[3]!) n₁
    let p₂ ← timeNodeSized bounds hyps T.appArg! (← constZero ts[2]!) sO n₂
    return (← applyConst ``Simulator.comp.timeBoundSized_timed #[p₁, p₂]).1
  | .mapPorts _ n₀ f g _ _ =>
    let args := T.getAppArgs
    let T₀ := args[args.size - 3]!
    let sM ← mkFreshExprMVar (← mkArrow (← portTypes T₀)[0]! (mkConst ``Nat)) .natural `sM
    let p ← timeNodeSized bounds hyps T₀ sM sO n₀
    let sE' ← mkFreshExprMVar (← inferType sE)
    let a ← mkFreshExprMVar (mkConst ``Nat)
    let b ← mkFreshExprMVar (mkConst ``Nat)
    let c ← mkFreshExprMVar (mkConst ``Nat)
    let (pf, _) ← applyConst ``Simulator.mapPorts.timeBoundSized_timed #[p, f, g]
      (← mkAppM ``Simulator.Timed.TimeBoundSized #[T, sE', sO, a, b, c])
    unless ← isDefEq sE' sE do
      throwError "derive_simulator: the size of the relabelled events{indentExpr sE'}\n\
        is not the size{indentExpr sE}"
    return pf
  | .mono _ n₀ .. =>
    let args := T.getAppArgs
    let p ← timeNodeSized bounds hyps args[args.size - 3]! sE sO n₀
    return (← applyConst ``Simulator.mono.timeBoundSized_timed
      #[p, args[args.size - 2]!, args[args.size - 1]!]).1
  | _ => lift

/-- The constants `a`, `b`, `c` of the size-graded time proof `pf` of `T` at the sizes `sE`, `sO`
simplified, with the proof of the simplified bound. -/
def simplifySized (pf T sE sO a b c : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let ctx ← Simp.Context.ofNames [``Nat.zero_max, ``Nat.max_zero, ``max_self, ``Nat.add_assoc,
    ``max_eq_left, ``max_eq_right, ``Nat.add_zero, ``Nat.zero_add] true
  let simpLe (x : Expr) : MetaM (Expr × Expr) := do
    let (r, _) ← simp x ctx (simprocs := #[← Simp.getSimprocs])
    match r.proof? with
    | some p => return (← mkAppM ``le_of_eq #[p], r.expr)
    | none => return (← mkAppM ``le_refl #[x], x)
  let (ha, a') ← simpLe a
  let (hb, b') ← simpLe b
  let (hc, c') ← simpLe c
  let ts ← portTypes T
  return (← mkAppM ``Simulator.Timed.TimeBoundSized.mono
    #[pf, ha, hb, hc, ← leSelf sE ts[0]!, ← leSelf sO ts[3]!], a', b', c')

/-- Prove `c.timeBoundSized_timed` for the costed form `Tc` (the costed simulator `T` with the
binders `timedBs`) of the simulator `c` of the node, when a leaf has a size-graded time
theorem: the sizes of the outer events and answers and the open binders of the leaf theorems
become implicit binders, their propositions hypotheses. -/
def deriveSized (c : Name) (levelParams : List Name) (T Tc : Expr) (timedBs : Array Expr)
    (node : Node) : TermElabM Unit := do
  unless ← nodeSized T node do return
  let ts ← portTypes T
  let sE ← mkFreshExprMVar (← mkArrow ts[0]! (mkConst ``Nat)) .natural `sE
  let sO ← mkFreshExprMVar (← mkArrow ts[3]! (mkConst ``Nat)) .natural `sO
  let bounds ← IO.mkRef #[]
  let thyps ← IO.mkRef #[]
  let tpf ← timeNodeSized bounds thyps T sE sO node
  refuseAssumedBounds c (← thyps.get)
  let ty ← instantiateMVars (← inferType tpf)
  let args := ty.getAppArgs
  let (tpf, a, b, k) ← simplifySized tpf T (← instantiateMVars sE) (← instantiateMVars sO)
    args[args.size - 3]! args[args.size - 2]! args[args.size - 1]!
  let tpf ← instantiateMVars tpf
  let mut recorded := #[]
  for (m, bi) in (← bounds.get) ++ (← thyps.get) do
    unless ← m.isAssigned do recorded := recorded.push (m, bi)
  let mut data := #[]
  let mut props := #[]
  for m in ← getMVars tpf do
    unless recorded.any (·.1 == m) do
      if ← isProp (← m.getType) then props := props.push (m, BinderInfo.default)
      else data := data.push (m, BinderInfo.implicit)
  withMVarsAsFVars (data ++ recorded ++ props) 0 #[] fun tFvs => do
    let tpf ← instantiateMVars tpf
    if tpf.hasExprMVar then throwError "derive_simulator: the sized time proof is incomplete"
    let tBs := timedBs ++ tFvs
    let concl ← mkAppM ``Simulator.Timed.TimeBoundSized #[Tc, ← instantiateMVars sE,
      ← instantiateMVars sO, ← instantiateMVars a, ← instantiateMVars b, ← instantiateMVars k]
    let tty := (← mkForallFVars tBs concl).replace fun e =>
      if e.isAppOfArity ``id 2 then some e.appArg! else none
    addDecl (Declaration.thmDecl
      { name := c ++ (← sfxName "timeBoundSized"), levelParams, type := tty,
        value := ← mkLambdaFVars tBs tpf })

/-- Define `c.timed` and prove `c.erase_timed` and `c.timeBound_timed` for a simulator `c`
whose costed multi-call simulators have their costed forms and step theorems; when a leaf has a
graded time theorem (`f.timeBoundGraded_timed`, a step from a state after `j` activations
costing at most `a + b * j`), the time theorem is the graded one, `c.timeBoundGraded_timed`. -/
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
    let tName := c ++ (← sfx)
    CatCrypt.Tactics.DeriveTimed.addTimedDef tName info.levelParams
      (← mkForallFVars timedBs (← inferType T)) (← mkLambdaFVars timedBs T)
    let Tc := mkAppN (mkConst tName lvls) timedBs
    withMVarsAsFVars (← ehyps.get) 0 #[] fun hypFvs => do
      let epf ← instantiateMVars epf
      if epf.hasExprMVar then throwError "derive_simulator: the erasure proof is incomplete"
      let eBs := bnds ++ primFvs ++ hypFvs
      let ety ← mkForallFVars eBs (← mkAppM ``Simulator.Timed.Erases #[Tc, S])
      let evalue ← mkLambdaFVars eBs epf
      let eName := c ++ (← sfxName "erase")
      addDecl (Declaration.thmDecl
        { name := eName, levelParams := info.levelParams, type := ety, value := evalue })
    let bounds ← IO.mkRef #[]
    let thyps ← IO.mkRef #[]
    if ← nodeGraded T node then
      let tpf ← timeNodeGraded bounds thyps T node
      refuseAssumedBounds c (← thyps.get)
      let ty ← instantiateMVars (← inferType tpf)
      let (tpf, a, b) ← simplifyGraded tpf ty.appFn!.appArg! ty.appArg!
      withMVarsAsFVars ((← bounds.get) ++ (← thyps.get)) 0 #[] fun tFvs => do
        let tpf ← instantiateMVars tpf
        if tpf.hasExprMVar then throwError "derive_simulator: the time proof is incomplete"
        let tBs := timedBs ++ tFvs
        let tty ← mkForallFVars tBs (← mkAppM ``Simulator.Timed.TimeBoundGraded
          #[Tc, ← instantiateMVars a, ← instantiateMVars b])
        addDecl (Declaration.thmDecl
          { name := c ++ (← sfxName "timeBoundGraded"), levelParams := info.levelParams,
            type := tty,
            value := ← mkLambdaFVars tBs tpf })
      deriveSized c info.levelParams T Tc timedBs node
      return
    let tpf ← timeNode bounds thyps T node
    refuseAssumedBounds c (← thyps.get)
    let (tpf, B) ← simplifyBound tpf (← instantiateMVars (← inferType tpf)).appArg!
    withMVarsAsFVars ((← bounds.get) ++ (← thyps.get)) 0 #[] fun tFvs => do
      let tpf ← instantiateMVars tpf
      let B ← instantiateMVars B
      if tpf.hasExprMVar then throwError "derive_simulator: the time proof is incomplete"
      let tBs := timedBs ++ tFvs
      let tty ← mkForallFVars tBs (← mkAppM ``Simulator.Timed.TimeBound #[Tc, B])
      let tvalue ← mkLambdaFVars tBs tpf
      let bName := c ++ (← sfxName "timeBound")
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

/-- Prove `R.timeBound_timed : ∀ xs, (R.timed xs).TimeBound B₁ ⋯ Bₙ` for a costed hybrid machine
`R.timed`, a `Hybrid.Timed` (steps `pre`, `post`) or a `MultiHybrid.Timed` (steps `start`,
`resume`, `finish`), from the step theorems `R.st.tree.timeBound_timed`, or
`R.st.treeHat.timeBound_timed` for a costed form on costed states; the binders of the step
theorems left open become implicit binders and hypotheses of the theorem. -/
def deriveHybridTime (R : Name) : TermElabM Unit := do
  let tName := R ++ `timed
  let info ← getConstInfo tName
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs ty => do
    let ty ← whnfR ty
    let (tb, sts) ←
      if ty.isAppOf ``Hybrid.Timed then pure (``Hybrid.Timed.TimeBound, #[`pre, `post])
      else if ty.isAppOf ``MultiHybrid.Timed then pure (``MultiHybrid.Timed.TimeBound, steps)
      else throwError "derive_hybrid_time: `{tName}` is not a `Hybrid.Timed` or a \
        `MultiHybrid.Timed`{indentExpr ty}"
    let A := mkAppN (mkConst tName lvls) xs
    let bounds ← IO.mkRef #[]
    let hyps ← IO.mkRef #[]
    let pf ← stepsTimeBound bounds hyps tb R sts A
    withMVarsAsFVars ((← bounds.get) ++ (← hyps.get)) 0 #[] fun tFvs => do
      let pf ← instantiateMVars pf
      if pf.hasExprMVar then throwError "derive_hybrid_time: the time proof is incomplete"
      let tBs := xs ++ tFvs
      addDecl (Declaration.thmDecl
        { name := R ++ `timeBound_timed, levelParams := info.levelParams,
          type := ← mkForallFVars tBs (← inferType pf), value := ← mkLambdaFVars tBs pf })

end

/-- `derive_hybrid_time R` proves the time theorem `R.timeBound_timed` of the costed form
`R.timed` of a hybrid machine (`Hybrid.Timed` or `MultiHybrid.Timed`) from the time theorems
`R.st.tree.timeBound_timed` (or `R.st.treeHat.timeBound_timed`) of its steps. -/
syntax (name := deriveHybridTimeCmd) "derive_hybrid_time " ident : command

/-- Elaborate `derive_hybrid_time R`. -/
@[command_elab deriveHybridTimeCmd]
meta def elabDeriveHybridTime : CommandElab := fun stx => do
  let R ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM <| deriveHybridTime R

/-- `derive_simulator S` defines the costed form `S.timed` of a bundled simulator `S` built
from `Simulator.ofMultiHybrid`, `Simulator.comp`, `Simulator.tensor`, `Simulator.mapPorts` and
`Simulator.mono`, and proves its erasure theorem `S.erase_timed` and its time theorem
`S.timeBound_timed`. `derive_simulator (suffix := s) S` reads and defines the costed forms named
by `s` in place of `timed` (`S.s`, `S.erase_s`, `S.timeBound_s`, `f.timeBoundGraded_s`), and
derives the missing costed forms of its multi-call simulators by
`derive_reduction (suffix := s)`. -/
syntax (name := deriveSimulatorCmd) "derive_simulator " ("(" &"suffix" " := " ident ") ")?
  ident : command

/-- Elaborate `derive_simulator S`: derive the costed forms and step theorems of the costed
multi-call simulators of `S` that are missing, then the costed form of `S`. The step theorems of
a leaf are not required when it runs on costed states, whose time comes from
`f.timeBoundInv_timed`, `f.timeBoundGraded_timed` or its step theorems, or when it has a graded
time theorem `f.timeBoundGraded_timed`. -/
@[command_elab deriveSimulatorCmd]
meta def elabDeriveSimulator : CommandElab := fun stx => do
  -- The optional group `(suffix := s)` is a node of five children when present.
  let s := if stx[1].getNumArgs == 5 then stx[1][3].getId else `timed
  withScope (fun sc => { sc with opts := sc.opts.set `derive_simulator.suffix s }) do
  let c ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  let heads ← liftTermElabM <| hybridHeads c
  let erase := Name.mkSimple ("erase_" ++ s.toString)
  let tb := Name.mkSimple ("timeBound_" ++ s.toString)
  let graded := Name.mkSimple ("timeBoundGraded_" ++ s.toString)
  for f in heads do
    unless (← getEnv).contains (f ++ s) do
      elabCommand (← `(command| derive_reduction (suffix := $(mkIdent s)) $(mkCIdent f)))
    let hat ← liftTermElabM <| isHat f
    let isGraded := (← getEnv).contains (f ++ graded)
    let tr ← liftTermElabM <| treeName f
    -- `derive_time_bound` states the time theorems of the costed forms `timed`.
    if s == `timed then
      for st in steps do
        let t := f ++ st ++ tr
        unless (← getEnv).contains (t ++ tb) || hat || isGraded do
          elabCommand (← `(command| derive_time_bound $(mkCIdent t)))
  let env ← getEnv
  let needed ← heads.filterM fun f => return !(← liftTermElabM <| isHat f)
  let needed := needed.flatMap fun f =>
    #[f ++ s, f ++ erase] ++
      (if env.contains (f ++ graded) then #[]
       else steps.map (f ++ · ++ `tree ++ tb))
  let missing := needed.filter (!env.contains ·)
  unless missing.isEmpty do
    throwError "derive_simulator: `{c}` needs the declarations {missing.toList}, which are not \
      derived"
  liftTermElabM <| deriveSimulator c

end CatCrypt.Tactics.DeriveSimulator

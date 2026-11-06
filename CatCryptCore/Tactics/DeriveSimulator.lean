/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostMono
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StatePotential

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

When a leaf has a potential time bound `f.potentialBound_timed` (`derive_hybrid_time (potential)
f`, `StatePotential.lean`), the command proves instead `S.timeBoundPot_timed : … →
(S.timed …).TimeBoundPot gE gO hEG hO a b d` and, when the outer ports have instances of
`ImportSize` and `PotLeSize`, the certificate `S.potCert_timed : … → (S.timed …).PotCert a b c d`.
The rule, over the constructions above: a potential leaf by
`Simulator.ofMultiHybrid.timeBoundPot_timed` (or its form on costed states when the port
erasures are identities); a composite by `Simulator.comp.timeBoundPot_timed` with the least
`κ ≤ κMax` (`16`) for which the middle interface conserves import, `gEM ≤ hEM + κ` and
`gM ≤ hM + κ`, closed by simplification and `omega` on the measures; a relabelling by
`Simulator.mapPorts.timeBoundPot_timed`; a change of views by `Simulator.mono.timeBoundPot_timed`;
a subterm without a potential leaf through the instance theorems
`Simulator.Timed.TimeBoundGraded.timeBoundPot` and `Simulator.Timed.TimeBound.timeBoundPot`.
A composite whose middle interface does not conserve import (a factor that creates import at an
answer, by copying its state into it) is refused with the four measures of the interface.

## Main definitions

* `derive_simulator S` — define `S.timed`, prove `S.erase_timed` and `S.timeBound_timed`
  (or `S.timeBoundGraded_timed`, and `S.timeBoundSized_timed` for a leaf with a size-graded
  time theorem)
* `derive_hybrid_time R` — prove `R.timeBound_timed` for the costed form `R.timed` of a hybrid
  machine (`Hybrid.Timed` or `MultiHybrid.Timed`) from the time theorems of its steps, the trees
  `R.st.tree` or, for a costed form on costed states, `R.st.treeHat`
* `derive_hybrid_time (potential) R` — define the potential time bound `R.potentialBound_timed`
  of the costed multi-call simulator `R.timed` (rule and class in `StatePotential.lean`)
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

/-- Whether `a` and `b` are definitionally equal with the constant `c` kept folded. -/
def isDefEqFolding (c : Name) (a b : Expr) : MetaM Bool :=
  withCanUnfoldPred (fun cfg info => if info.name == c then pure false
    else canUnfoldDefault cfg info) (isDefEq a b)

/-- Close the hypothesis `m` of the form `∀ xs, L ≤ t`, where `t` is an open bound and `L` does
not depend on `xs`, by `t := L` and `fun xs => le_refl L`: the least bound of a cost that the
machine fixes to a constant. Other hypotheses are left open. -/
def closeConstBound (m : MVarId) : MetaM Unit := do
  if ← m.isAssigned then return
  let ty ← instantiateMVars (← m.getType)
  forallTelescopeReducing ty fun xs body => do
    let some (_, L, t) := body.headBeta.le? | return
    let L ← instantiateMVars L.headBeta
    let .mvar tm ← instantiateMVars t | return
    if ← tm.isAssigned then return
    if L.hasAnyFVar (xs.contains <| .fvar ·) then return
    if (L.findMVar? (· == tm)).isSome then return
    let s ← saveState
    unless ← isDefEq (.mvar tm) L do s.restore; return
    let pf ← mkLambdaFVars xs (← mkAppM ``le_refl #[L])
    unless ← isDefEq (← inferType pf) ty do s.restore; return
    m.assign pf

/-- The time bound `tb A B₁ ⋯ Bₙ` of the costed machine `A`, an application of `f.timed`, from
the step theorems `f.st.tr.timeBound_timed` (`tr` is `tree` or `treeHat`) of the steps `sts`.
The conclusion of each step theorem is unified with the component of `tb A` of its step at a
fresh state and input, with the step tree `f.st.tr.timed` kept folded: the binders of the step
theorem take the arguments that the machine passes to its step tree, and the state and the
input are the binders unified with the fresh ones. A hypothesis `∀ xs, L ≤ t` with `L`
constant closes by `t := L` (`closeConstBound`); the other binders left open are recorded in
`bounds` and `hyps`. The bound and these binders do not depend on the state or the input. -/
def stepsTimeBound (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (tb f : Name)
    (sts : Array Name) (A : Expr) : MetaM Expr := do
  let tr ← treeName f
  let tbA ← mkAppM tb #[A]
  let (bms, _, _) ← forallMetaTelescopeReducing (← inferType tbA)
  unless bms.size == sts.size do
    throwError "derive_simulator: `{tb}` does not take one bound per step"
  let mut P ← whnfD (mkAppN tbA bms)
  let mut pfs := #[]
  for st in sts, i in [0:sts.size] do
    let comp ← if i + 1 < sts.size then
        let some (p, q) := P.and? | throwError "derive_simulator: `{tb}` is not a conjunction"
        P ← whnfD q
        pure p
      else pure P
    let (sa, _, body) ← forallMetaTelescopeReducing comp (some 2)
    let (some sM, some aM) := (sa[0]?, sa[1]?)
      | throwError "derive_simulator: the step `{st}` of `{tb}` takes no state and input"
    let thm ← mkConstWithFreshMVarLevels (f ++ st ++ tr ++ (← sfxName "timeBound"))
    let (ms, bis, concl) ← forallMetaTelescopeReducing (← inferType thm)
    unless ← isDefEqFolding (f ++ st ++ tr ++ (← sfx)) (← instantiateMVars concl) body do
      throwError "derive_simulator: `{thm}` does not bound the step `{st}` of{indentExpr A}"
    let (.mvar sm, .mvar am) := (← instantiateMVars sM, ← instantiateMVars aM)
      | throwError "derive_simulator: `{thm}` bounds the step `{st}` only at some states or \
          inputs"
    if sm == am then
      throwError "derive_simulator: `{thm}` bounds the step `{st}` only at some states or inputs"
    for m in ms, bi in bis do
      if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
        if let some inst ← synthInstance? (← instantiateMVars (← inferType m)) then
          discard <| isDefEq m inst
    for m in ms do closeConstBound m.mvarId!
    let onStep (e : Expr) : Bool := (e.findMVar? fun m => m == sm || m == am).isSome
    let rest ← ms.filterM fun m => do
      let m' ← instantiateMVars m
      return m'.isMVar && m'.mvarId! != sm && m'.mvarId! != am
    let B ← instantiateMVars bms[i]!
    let mut stateDep := onStep B
    for m in rest do
      if onStep (← instantiateMVars (← inferType m)) then stateDep := true
    if stateDep then
      throwError "derive_simulator: the bound of `{thm}` or a hypothesis of it depends on the \
        state or the input of the step"
    recordOpen bounds hyps .implicit rest
    let sTy ← instantiateMVars (← sm.getType)
    let aTy ← instantiateMVars (← am.getType)
    let pf ← withLocalDeclD `s sTy fun s =>
      withLocalDeclD `a aTy fun a => do
        sm.assign s
        am.assign a
        mkLambdaFVars #[s, a] (← instantiateMVars (mkAppN thm ms))
    pfs := pfs.push pf
  let some last := pfs.back? | throwError "derive_simulator: no steps"
  let pf ← pfs.pop.foldrM (fun p acc => mkAppM ``And.intro #[p, acc]) last
  mkExpectedTypeHint pf (← instantiateMVars (mkAppN tbA bms))

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

/-! ### Potential time bounds -/

/-- The value of a closed numeral expression built from numerals, `+`, `*` and `max`. -/
partial def natVal? (e : Expr) : MetaM (Option Nat) := do
  if let some n ← evalNat e |>.run then return some n
  let e := e.headBeta
  if e.isAppOfArity ``Max.max 4 then
    let (some a, some b) := (← natVal? (e.getArg! 2), ← natVal? (e.getArg! 3)) | return none
    return some (max a b)
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (some a, some b) := (← natVal? (e.getArg! 4), ← natVal? (e.getArg! 5)) | return none
    return some (a + b)
  return none

/-- The linear form of a step bound over the locals `deps` (the state and the input): a numeral
part, the terms not mentioning `deps`, and the sum of the numeral coefficients of the terms that
mention them. A sum adds; a multiple by a numeral scales; a `max`, an `if` and a match are bounded
by the larger numeral part, both symbolic parts and the larger coefficient; a truncated difference
by its left side; a term with a fact `t = r` or `t ≤ r` in `facts` by the form of `r`; any other
term mentioning `deps` is an atom of coefficient `1`. -/
partial def linForm (deps : Array Expr) (facts : Array (Expr × Expr)) (e : Expr) :
    MetaM (Nat × Array Expr × Nat) := do
  let e ← instantiateMVars e.headBeta
  if let some n ← natVal? e then return (n, #[], 0)
  if !deps.any (fun d => e.containsFVar d.fvarId!) then return (0, #[e], 0)
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (n₁, s₁, k₁) ← linForm deps facts (e.getArg! 4)
    let (n₂, s₂, k₂) ← linForm deps facts (e.getArg! 5)
    return (n₁ + n₂, s₁ ++ s₂, k₁ + k₂)
  if e.isAppOfArity ``HMul.hMul 6 then
    if let some c ← evalNat (e.getArg! 4) |>.run then
      let (n, s, k) ← linForm deps facts (e.getArg! 5)
      return (c * n, s.map fun t => mkNatMul (mkNatLit c) t, c * k)
    if let some c ← evalNat (e.getArg! 5) |>.run then
      let (n, s, k) ← linForm deps facts (e.getArg! 4)
      return (c * n, s.map fun t => mkNatMul (mkNatLit c) t, c * k)
  if e.isAppOfArity ``HSub.hSub 6 then return ← linForm deps facts (e.getArg! 4)
  let two (a b : Expr) : MetaM (Nat × Array Expr × Nat) := do
    let (n₁, s₁, k₁) ← linForm deps facts a
    let (n₂, s₂, k₂) ← linForm deps facts b
    return (max n₁ n₂, s₁ ++ s₂, max k₁ k₂)
  if e.isAppOfArity ``Max.max 4 then return ← two (e.getArg! 2) (e.getArg! 3)
  if e.isAppOfArity ``ite 5 then return ← two (e.getArg! 3) (e.getArg! 4)
  for (l, r) in facts do
    if l == e then return ← linForm deps facts r
  return (0, #[], 1)

/-- The facts `t = r` and `t ≤ r` over `ℕ` of the local context. -/
def natFacts : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (t, l, r) := ty.eq? then
      if t.isConstOf ``Nat then out := out.push (l, r)
    else if let some (t, l, r) := ty.le? then
      if t.isConstOf ``Nat then out := out.push (l, r)
  return out

/-- The fields `(cost, step)` of the costed multi-call simulator and the input type of each step:
`start` on `E`, `resume` and `finish` on `OG`. -/
def potSteps : Array (Name × Name × Name × Nat) :=
  #[(`start, ``MultiHybrid.Timed.startCost, ``MultiHybrid.Timed.start, 1),
    (`resume, ``MultiHybrid.Timed.resumeCost, ``MultiHybrid.Timed.resume, 4),
    (`finish, ``MultiHybrid.Timed.finishCost, ``MultiHybrid.Timed.finish, 4)]

/-- The step theorem `R.st.tr.timeBound_timed` of a step of the costed form `A` of `R`, unified with
the time of the step at a fresh state and input: the bound and the proof as functions of the state
and the input. The binders left open are recorded in `bounds` and `hyps`; they do not mention the
state or the input. -/
def potStepBound (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (R st cost tree : Name)
    (A σ X : Expr) : MetaM (Expr × Expr) := do
  let tr ← treeName R
  let thmN := R ++ st ++ tr ++ (← sfxName "timeBound")
  unless (← getEnv).contains thmN do
    throwError "derive_hybrid_time (potential): the step theorem `{thmN}` is missing; run \
      `derive_time_bound {R ++ st ++ tr}` first"
  let thm ← mkConstWithFreshMVarLevels thmN
  let (ms, bis, concl) ← forallMetaTelescopeReducing (← inferType thm)
  let sM ← mkFreshExprMVar σ
  let xM ← mkFreshExprMVar X
  let lhs ← mkAppM ``CatCrypt.Core.SPTree.Timed.stepTime
    #[← mkAppM ``Prod.mk #[← mkAppM cost #[A, sM, xM], ← mkAppM tree #[A, sM, xM]]]
  let BM ← mkFreshExprMVar (mkConst ``Nat)
  unless ← isDefEqFolding (R ++ st ++ tr ++ (← sfx)) (← instantiateMVars concl)
      (← mkAppM ``LE.le #[lhs, BM]) do
    throwError "derive_hybrid_time (potential): `{thmN}` does not bound the step `{st}` \
      of{indentExpr A}"
  let (.mvar sm, .mvar xm) := (← instantiateMVars sM, ← instantiateMVars xM)
    | throwError "derive_hybrid_time (potential): `{thmN}` bounds the step `{st}` only at some \
        states or inputs"
  for m in ms, bi in bis do
    if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
      if let some inst ← synthInstance? (← instantiateMVars (← inferType m)) then
        discard <| isDefEq m inst
  for m in ms do closeConstBound m.mvarId!
  let rest ← ms.filterM fun m => do
    let m' ← instantiateMVars m
    return m'.isMVar && m'.mvarId! != sm && m'.mvarId! != xm
  for m in rest do
    if ((← instantiateMVars (← inferType m)).findMVar? fun v => v == sm || v == xm).isSome then
      throwError "derive_hybrid_time (potential): a hypothesis of `{thmN}` depends on the state \
        or the input of the step"
  recordOpen bounds hyps .implicit rest
  withLocalDeclD `s σ fun s => withLocalDeclD `x X fun x => do
    sm.assign s
    xm.assign x
    let B ← mkLambdaFVars #[s, x] (← instantiateMVars BM)
    let pf ← mkLambdaFVars #[s, x] (← instantiateMVars (mkAppN thm ms))
    return (B, pf)

/-- The measure `fun x => k + pot x` on `X`. -/
def recvMeasure (X : Expr) (k : Nat) : MetaM Expr :=
  withLocalDeclD `x X fun x => do
    mkLambdaFVars #[x] (← mkAppM ``HAdd.hAdd #[mkNatLit k,
      ← mkAppM ``StatePotential.pot #[x]])

/-- The measure `pot` on `X` when `pass` holds, `fun _ => 0` otherwise. -/
def passMeasure (X : Expr) (pass : Bool) : MetaM Expr :=
  withLocalDeclD `x X fun x => do
    mkLambdaFVars #[x] (← if pass then mkAppM ``StatePotential.pot #[x] else pure (mkNatLit 0))

/-- The field goals `init`, `start`, `resume`, `finish` of the potential time bound
`A.PotentialBound gE gO hEG hO a b` with the invariant `inv` and the potential `pot` of `σ`. -/
def potFields (A σ gE gO hEG hO a b : Expr) : MetaM (Expr × Array Expr) := do
  let c ← mkConstWithFreshMVarLevels ``MultiHybrid.Timed.PotentialBound.mk
  let (ms, _, ty) ← forallMetaTelescopeReducing (← inferType c)
  let target ← mkAppM ``MultiHybrid.Timed.PotentialBound #[A, gE, gO, hEG, hO, a, b]
  unless ← isDefEq ty target do throwError "derive_hybrid_time (potential): no potential bound"
  let n := ms.size
  let inv ← withLocalDeclD `s σ fun s => do mkLambdaFVars #[s] (← mkAppM ``StatePotential.inv #[s])
  let pot ← withLocalDeclD `s σ fun s => do mkLambdaFVars #[s] (← mkAppM ``StatePotential.pot #[s])
  discard <| isDefEq ms[n - 6]! inv
  discard <| isDefEq ms[n - 5]! pot
  let mut goals := #[]
  for i in [n - 4:n] do
    let g ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType ms[i]!))
    ms[i]!.mvarId!.assign g
    goals := goals.push g
  return (← instantiateMVars (mkAppN c ms), goals)

open CatCrypt.Tactics.StatePotential in
/-- Prove the potential clause of the field goal `g` (`∀ s x, inv s → time ∧ clause`), leaving the
time part: the time goal, after introducing the state, the input and the invariant. -/
def potClausePart (defs : Array Name) (g : Expr) (time : Bool) :
    TermElabM (Option (MVarId × Expr × Expr)) := do
  let (fvs, g') ← g.mvarId!.introN 3
  g'.withContext do
  let [gt, gc] ← g'.apply (mkConst ``And.intro [])
    | throwError "derive_hybrid_time (potential): a field is not a conjunction"
  clauseClose defs gc
  if time then return some (gt, mkFVar fvs[0]!, mkFVar fvs[1]!)
  return none

open CatCrypt.Tactics.StatePotential CatCrypt.Tactics.AutoTime in
/-- Prove the time part `gt : stepTime … ≤ a + b * (pot s + g x)` from the step bound `pf`. -/
def potTimePart (gt : MVarId) (pf s x : Expr) : TermElabM Unit := gt.withContext do
  let pf := pf.beta #[s, x]
  let some (_, _, B) := (← instantiateMVars (← inferType pf)).le?
    | throwError "derive_hybrid_time (potential): the step theorem is not a bound"
  let some (_, _, R) := (← instantiateMVars (← gt.getType)).le?
    | throwError "derive_hybrid_time (potential): the time goal is not a bound"
  let h ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[B, R])
  gt.assign (← mkAppM ``le_trans #[pf, h])
  let some g ← simpAll #[] h.mvarId! | return
  let g ← splitHyps g
  let g ← addCostFacts g
  let g ← addLengthFacts g
  omegaWithFacts g

open CatCrypt.Tactics.StatePotential in
/-- Define `R.potentialBound_timed` (see the module docstring of `StatePotential.lean` for the
rule and its class of simulators). -/
def derivePotential (R : Name) : TermElabM Unit := do
  let tName := R ++ (← sfx)
  let info ← getConstInfo tName
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs ty => do
  let ty ← whnfR ty
  unless ty.isAppOfArity ``MultiHybrid.Timed 5 do
    throwError "derive_hybrid_time (potential): `{tName}` is not a \
      `MultiHybrid.Timed`{indentExpr ty}"
  let tys := ty.getAppArgs
  let σ := tys[0]!
  for T in tys do
    if (← synthInstance? (← mkAppM ``StatePotential #[T])).isNone then
      throwError "derive_hybrid_time (potential): no instance `StatePotential {T}`; the potential \
        of a state or the import of a message of this type is to be given by an instance"
  let A := mkAppN (mkConst tName lvls) xs
  let bounds ← IO.mkRef #[]
  let hyps ← IO.mkRef #[]
  let mut stepBs := #[]
  for (st, cost, tree, xi) in potSteps do
    stepBs := stepBs.push (← potStepBound bounds hyps R st cost tree A σ tys[xi]!)
  withMVarsAsFVars ((← bounds.get) ++ (← hyps.get)) 0 #[] fun tFvs => do
  let stepBs ← stepBs.mapM fun (B, pf) => return (← instantiateMVars B, ← instantiateMVars pf)
  let defs := (← treeDefs R).push tName
  -- the constants `a`, `b` from the linear forms of the step bounds
  let mut nA := 0
  let mut syms : Array Expr := #[]
  let mut kB := 0
  for (B, _) in stepBs, (_, _, _, xi) in potSteps do
    let (n, sy, k) ← withLocalDeclD `s σ fun s => withLocalDeclD `x tys[xi]! fun x => do
      let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[B.beta #[s, x], mkNatLit 0])
      let g ← CatCrypt.Tactics.AutoTime.addCostFacts g.mvarId!
      let g ← CatCrypt.Tactics.AutoTime.addLengthFacts g
      g.withContext do linForm #[s, x] (← natFacts) (B.beta #[s, x])
    nA := max nA n
    for t in sy do unless syms.contains t do syms := syms.push t
    kB := max kB k
  let a ← syms.foldlM (fun acc t => mkAppM ``HAdd.hAdd #[acc, t]) (mkNatLit nA)
  let b := mkNatLit kB
  -- the search of the imports created and of the measures passed on
  let tryClause (i : Nat) (κE κO : Nat) (pE pO : Bool) : TermElabM Bool := do
    let s ← saveState
    try
      let (_, goals) ← potFields A σ (← recvMeasure tys[1]! κE) (← recvMeasure tys[4]! κO)
        (← passMeasure tys[3]! pE) (← passMeasure tys[2]! pO) a b
      discard <| potClausePart defs goals[i + 1]! false
      s.restore
      return true
    catch _ =>
      s.restore
      return false
  let least (i : Nat) (pE pO : Bool) : TermElabM (Option Nat) := do
    let ok (k : Nat) := if i == 0 then tryClause i k 0 pE pO else tryClause i 0 k pE pO
    unless ← ok κMax do return none
    let mut lo := 0
    let mut hi := κMax
    while lo < hi do
      let mid := (lo + hi) / 2
      if ← ok mid then hi := mid else lo := mid + 1
    return some lo
  let mut found : Option (Nat × Nat × Bool × Bool) := none
  for (pE, pO) in [(true, true), (true, false), (false, true), (false, false)] do
    let some kE ← least 0 pE pO | continue
    let some kR ← least 1 pE pO | continue
    let some kF ← least 2 pE pO | continue
    found := some (kE, max kR kF, pE, pO)
    break
  let some (κE, κO, pE, pO) := found | do
    for i in [0:3] do
      let (_, goals) ← potFields A σ (← recvMeasure tys[1]! κMax) (← recvMeasure tys[4]! κMax)
        (← passMeasure tys[3]! false) (← passMeasure tys[2]! false) a b
      try discard <| potClausePart defs goals[i + 1]! false
      catch e =>
        throwError "derive_hybrid_time (potential): the potential clause of the step \
          `{potSteps[i]!.1}` of `{R}`, `Φ s' + h y ≤ Φ s + (κ + pot x)`, does not close for \
          `κ = {κMax}` and the measures `0` passed on:{indentD e.toMessageData}"
    throwError "derive_hybrid_time (potential): no potential bound of `{R}`"
  let gE ← recvMeasure tys[1]! κE
  let gO ← recvMeasure tys[4]! κO
  let hEG ← passMeasure tys[3]! pE
  let hO ← passMeasure tys[2]! pO
  let (val, goals) ← potFields A σ gE gO hEG hO a b
  -- init
  if let some g0 ← simpAll defs goals[0]!.mvarId! then potClose g0
  for i in [0:3] do
    let some (gt, s, x) ← potClausePart defs goals[i + 1]! true | unreachable!
    try potTimePart gt (stepBs[i]!.2) s x
    catch e =>
      throwError "derive_hybrid_time (potential): the step bound of `{potSteps[i]!.1}` of `{R}`, \
        {indentExpr (stepBs[i]!.1)}\nis not bounded by `a + b * (Φ s + g x)` with \
        `a = {a}`, `b = {b}`: a term of it is not a summand of the potential of the state or of \
        the input{indentD e.toMessageData}"
  let val ← instantiateMVars val
  if val.hasExprMVar then throwError "derive_hybrid_time (potential): the proof is incomplete"
  let bs := xs ++ tFvs
  CatCrypt.Tactics.DeriveTimed.addTimedDef (R ++ (← sfxName "potentialBound"))
    info.levelParams (← mkForallFVars bs (← inferType val)) (← mkLambdaFVars bs val)

/-- The potential time bound `f.potentialBound_timed` of the costed multi-call simulator of a leaf
`T` (`A` an application of `f.timed`), when it exists. -/
def potThm? (T : Expr) : MetaM (Option Name) := do
  let T ← instantiateMVars T
  unless T.isAppOf ``Simulator.Timed.ofMultiHybridHat ||
      T.isAppOf ``Simulator.Timed.ofMultiHybrid do return none
  let .const ft _ := T.appArg!.getAppFn | return none
  let g := ft.getPrefix ++ (← sfxName "potentialBound")
  return if (← getEnv).contains g then some g else none

/-- Whether a leaf of the costed simulator `T` of the node has a potential time bound. -/
partial def nodePot (T : Expr) : Node → MetaM Bool
  | .leaf .. => return (← potThm? T).isSome
  | .comp _ n₁ n₂ => do
    let T ← instantiateMVars T
    return (← nodePot T.appFn!.appArg! n₁) || (← nodePot T.appArg! n₂)
  | .mapPorts _ n .. | .mono _ n .. => do
    let T ← instantiateMVars T
    let args := T.getAppArgs
    nodePot args[args.size - 3]! n
  | _ => return false

/-- The measures and constants `gE gO hEG hO a b d` of a proof of `T.TimeBoundPot …`. -/
def potArgs (pf : Expr) : MetaM (Array Expr) := do
  let ty ← instantiateMVars (← inferType pf)
  return ty.getAppArgs.extract 7 14

open CatCrypt.Tactics.StatePotential in
/-- Prove `∀ m, g m ≤ h m + κ` over `X` by simplification and `omega`, or fail. -/
def measureLe (X g h : Expr) (κ : Nat) : TermElabM (Option Expr) := do
  let ty ← withLocalDeclD `m X fun m => do
    mkForallFVars #[m] (← mkAppM ``LE.le #[g.beta #[m],
      ← mkAppM ``HAdd.hAdd #[h.beta #[m], mkNatLit κ]])
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  let s ← saveState
  try
    let (_, g') ← mv.mvarId!.intro1
    if let some g'' ← simpAll #[] g' then
      let gs ← Tactic.run g'' (Tactic.evalTactic (← `(tactic| omega)))
      unless gs.isEmpty do throwError "open"
    return some (← instantiateMVars mv)
  catch _ =>
    s.restore
    return none

/-- The theorem `n` applied to metavariables, its type unified with `expected` first and its
explicit binders then assigned to `args` in order. -/
def applyConstE (n : Name) (args : Array Expr) (expected : Expr) : MetaM Expr := do
  let c ← mkConstWithFreshMVarLevels n
  let (ms, bis, ty) ← forallMetaTelescopeReducing (← inferType c)
  unless ← isDefEq ty expected do
    throwError "derive_simulator: `{n}` has type{indentExpr ty}\nexpected{indentExpr expected}"
  let mut j := 0
  for m in ms, bi in bis do
    if bi.isExplicit then
      let some a := args[j]? | throwError "derive_simulator: too few arguments for `{n}`"
      j := j + 1
      unless ← isDefEq (← inferType m) (← inferType a) do
        throwError "derive_simulator: the argument `{a}` of `{n}` has \
          type{indentExpr (← inferType a)}\nexpected{indentExpr (← inferType m)}"
      m.mvarId!.assign a
  for m in ms do
    unless ← m.mvarId!.isAssigned do
      throwError "derive_simulator: an argument of `{n}` is not determined{indentExpr ty}"
  instantiateMVars (mkAppN c ms)

/-- The potential time-bound proof `T.TimeBoundPot gE gO hEG hO a b d` of the costed simulator
`T` of the node: a leaf with a potential time bound `f.potentialBound_timed` by
`Simulator.ofMultiHybrid.timeBoundPot_timed` (or its form on costed states, whose port erasures are
identities) with no import created; a composite by `Simulator.comp.timeBoundPot_timed` with the
least `κ ≤ κMax` for which the middle interface conserves import (`gEM ≤ hEM + κ`,
`gM ≤ hM + κ`, by simplification and `omega` on the measures); a relabelling by
`Simulator.mapPorts.timeBoundPot_timed` with the import `gM ∘ f` of the events and the import
`pot` of the outputs when `pot (g o) ≤ hM o` closes, else `0`; a change of views by
`Simulator.mono.timeBoundPot_timed`; a subterm with no potential leaf by the instance theorems
`Simulator.Timed.TimeBoundGraded.timeBoundPot` or `Simulator.Timed.TimeBound.timeBoundPot`. -/
partial def timeNodePot (bounds hyps : IO.Ref (Array (MVarId × BinderInfo))) (T : Expr)
    (n : Node) : TermElabM Expr := do
  let T ← instantiateMVars T
  unless ← nodePot T n do
    if ← nodeGraded T n then
      return (← applyConst ``Simulator.Timed.TimeBoundGraded.timeBoundPot
        #[← timeNodeGraded bounds hyps T n]).1
    return (← applyConst ``Simulator.Timed.TimeBound.timeBoundPot
      #[← timeNode bounds hyps T n]).1
  match n with
  | .leaf .. =>
    let some g ← potThm? T | throwError "derive_simulator: no potential bound"
    let A := T.appArg!
    let thm ← mkConstWithFreshMVarLevels g
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType thm)
    let concl ← instantiateMVars concl
    unless ← isDefEq (concl.getArg! 5) A do
      throwError "derive_simulator: `{g}` does not bound{indentExpr A}"
    recordOpen bounds hyps .implicit ms
    let P ← instantiateMVars (mkAppN thm ms)
    let ps := concl.getAppArgs
    let expected ← mkAppM ``Simulator.Timed.TimeBoundPot
      #[T, ps[6]!, ps[7]!, ps[8]!, ps[9]!, ps[10]!, ps[11]!, mkNatLit 0]
    if T.isAppOf ``Simulator.Timed.ofMultiHybridHat then
      let ta := T.getAppArgs
      let εs := ta.extract (ta.size - 6) (ta.size - 1)
      for ε in #[εs[1]!, εs[2]!, εs[3]!, εs[4]!] do
        let dom := (← inferType ε).bindingDomain!
        unless ← isDefEq ε (← withLocalDeclD `x dom fun x => mkLambdaFVars #[x] x) do
          throwError "derive_simulator: the potential bound `{g}` is on costed events; its \
            port erasure{indentExpr ε}\nis not the identity"
      return ← applyConstE ``Simulator.ofMultiHybridHat.timeBoundPot_timed #[P] expected
    return (← applyConst ``Simulator.ofMultiHybrid.timeBoundPot_timed #[P] expected).1
  | .comp _ n₁ n₂ =>
    let p₁ ← timeNodePot bounds hyps T.appFn!.appArg! n₁
    let p₂ ← timeNodePot bounds hyps T.appArg! n₂
    let a₁ ← potArgs p₁
    let a₂ ← potArgs p₂
    let ts ← portTypes T.appFn!.appArg!
    let mut found := none
    for κ in [0:CatCrypt.Tactics.StatePotential.κMax + 1] do
      let some hE ← measureLe ts[2]! a₂[0]! a₁[2]! κ | continue
      let some hA ← measureLe ts[3]! a₁[1]! a₂[3]! κ | continue
      found := some (hE, hA)
      break
    let some (hE, hA) := found
      | throwError "derive_simulator: the middle interface of the composite{indentExpr T}\n\
          does not conserve import up to `κ ≤ {CatCrypt.Tactics.StatePotential.κMax}` per \
          message: the inner \
          factor receives events of import{indentExpr a₂[0]!}\nwhere the outer factor passes \
          on{indentExpr a₁[2]!}\n\
          and the outer factor receives answers of import{indentExpr a₁[1]!}\nwhere the inner \
          factor passes on{indentExpr a₂[3]!}"
    return (← applyConst ``Simulator.comp.timeBoundPot_timed #[p₁, p₂, hE, hA]).1
  | .mapPorts _ n₀ f g _ _ =>
    let args := T.getAppArgs
    let p ← timeNodePot bounds hyps args[args.size - 3]! n₀
    let ps ← potArgs p
    let ts ← portTypes T
    let gE ← withLocalDeclD `e ts[0]! fun e => do mkLambdaFVars #[e] (ps[0]!.beta #[f.beta #[e]])
    let hf ← withLocalDeclD `e ts[0]! fun e => do
      mkLambdaFVars #[e] (← mkAppM ``le_refl #[ps[0]!.beta #[f.beta #[e]]])
    let OM := (← inferType g).bindingDomain!
    let pot ← passMeasure ts[1]! true
    let gpot ← withLocalDeclD `o OM fun o => do mkLambdaFVars #[o] (pot.beta #[g.beta #[o]])
    let (hO, hg) ← match ← (do
        if (← synthInstance? (← mkAppM ``StatePotential #[ts[1]!])).isNone then return none
        measureLe OM gpot ps[3]! 0) with
      | some h => pure (pot, ← withLocalDeclD `o OM fun o => do
          mkLambdaFVars #[o] (← mkAppM ``le_of_le_of_eq #[mkApp h o,
            ← mkAppM ``Nat.add_zero #[ps[3]!.beta #[o]]]))
      | none => pure (← passMeasure ts[1]! false, ← withLocalDeclD `o OM fun o => do
          mkLambdaFVars #[o] (← mkAppM ``Nat.zero_le #[ps[3]!.beta #[o]]))
    let expected ← mkAppM ``Simulator.Timed.TimeBoundPot
      #[T, gE, ps[1]!, ps[2]!, hO, ps[4]!, ps[5]!, ps[6]!]
    return ← applyConstE ``Simulator.mapPorts.timeBoundPot_timed #[p, f, g, hf, hg] expected
  | .mono _ n₀ .. =>
    let args := T.getAppArgs
    let p ← timeNodePot bounds hyps args[args.size - 3]! n₀
    return (← applyConst ``Simulator.mono.timeBoundPot_timed
      #[p, args[args.size - 2]!, args[args.size - 1]!]).1
  | _ => throwError "derive_simulator: no potential rule"

/-- Prove `c.timeBoundPot_timed` and, when the outer ports have instances of `ImportSize` and
`PotLeSize`, `c.potCert_timed`, for the costed form `Tc` of `c` when a leaf has a potential time
bound: the potential rules of `timeNodePot`; the certificate passes on no import at the outer
ports (`Simulator.Timed.TimeBoundPot.mono`) and has the import measures at most `k + pot` with the
least `k ≤ κMax`, linear in the size with the constant `k + 1` (`ImportLinear.of_le_pot`). -/
def derivePot (c : Name) (levelParams : List Name) (T Tc : Expr) (timedBs : Array Expr)
    (node : Node) : TermElabM Unit := do
  let bounds ← IO.mkRef #[]
  let thyps ← IO.mkRef #[]
  let tpf ← timeNodePot bounds thyps T node
  refuseAssumedBounds c (← thyps.get)
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
    if tpf.hasExprMVar then throwError "derive_simulator: the potential time proof is incomplete"
    let tBs := timedBs ++ tFvs
    let ps ← potArgs tpf
    let concl ← mkAppM ``Simulator.Timed.TimeBoundPot #[Tc, ps[0]!, ps[1]!, ps[2]!, ps[3]!,
      ps[4]!, ps[5]!, ps[6]!]
    let pf ← mkExpectedTypeHint tpf concl
    addDecl (Declaration.thmDecl
      { name := c ++ (← sfxName "timeBoundPot"), levelParams,
        type := ← mkForallFVars tBs concl, value := ← mkLambdaFVars tBs pf })
    let ts ← portTypes T
    let some _ ← synthInstance? (← mkAppM ``ImportSize #[ts[0]!]) | return
    let some _ ← synthInstance? (← mkAppM ``ImportSize #[ts[3]!]) | return
    let pot (X : Expr) := passMeasure X true
    let some _ ← synthInstance? (← mkAppOptM ``PotLeSize #[ts[0]!, none, none]) | return
    let some _ ← synthInstance? (← mkAppOptM ``PotLeSize #[ts[3]!, none, none]) | return
    let mut found := none
    for k in [0:CatCrypt.Tactics.StatePotential.κMax + 1] do
      let kE ← withLocalDeclD `e ts[0]! fun e => do
        mkLambdaFVars #[e] (← mkAppM ``HAdd.hAdd #[mkNatLit k, (← pot ts[0]!).beta #[e]])
      let kO ← withLocalDeclD `o ts[3]! fun o => do
        mkLambdaFVars #[o] (← mkAppM ``HAdd.hAdd #[mkNatLit k, (← pot ts[3]!).beta #[o]])
      let some hE ← measureLe ts[0]! ps[0]! kE 0 | continue
      let some hO ← measureLe ts[3]! ps[1]! kO 0 | continue
      found := some (k, hE, hO)
      break
    let some (k, hE, hO) := found
      | throwError "derive_simulator: the import measures of `{c}` are not at most `k + pot` for \
          `k ≤ {CatCrypt.Tactics.StatePotential.κMax}`:{indentExpr ps[0]!}{indentExpr ps[1]!}"
    let fix (X h : Expr) : MetaM Expr := withLocalDeclD `x X fun x => do
      mkLambdaFVars #[x] (← mkAppM ``le_of_le_of_eq #[mkApp h x, ← mkAppM ``Nat.add_zero
        #[← mkAppM ``HAdd.hAdd #[mkNatLit k, ← mkAppM ``StatePotential.pot #[x]]]])
    let hL ← mkAppM ``ImportLinear.of_le_pot #[mkNatLit k, ← fix ts[0]! hE, ← fix ts[3]! hO]
    let zero (X : Expr) := passMeasure X false
    let zle (X h : Expr) : MetaM Expr := withLocalDeclD `x X fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Nat.zero_le #[h.beta #[x]])
    let lle (X h : Expr) : MetaM Expr := withLocalDeclD `x X fun x => do
      mkLambdaFVars #[x] (← mkAppM ``le_refl #[h.beta #[x]])
    let pf0 ← mkAppOptM ``Simulator.Timed.TimeBoundPot.mono
      #[none, none, none, none, none, none, none, none, none, none, none, none,
        some (← zero ts[2]!),
        none, some (← zero ts[1]!), none, none, none, none, none, none, some pf,
        some (← mkAppM ``le_refl #[ps[4]!]), some (← mkAppM ``le_refl #[ps[5]!]),
        some (← mkAppM ``le_refl #[ps[6]!]), some (← lle ts[0]! ps[0]!),
        some (← lle ts[3]! ps[1]!), some (← zle ts[2]! ps[2]!), some (← zle ts[1]! ps[3]!)]
    let cty ← mkAppM ``Simulator.Timed.PotCert #[Tc, ps[4]!, ps[5]!, mkNatLit (k + 1), ps[6]!]
    let p₁ := (← whnfD cty).appArg!
    let p₂ := (← whnfD (p₁.beta #[ps[0]!])).appArg!
    let cert ← mkAppOptM ``Exists.intro #[none, some p₁, some ps[0]!,
      some (← mkAppOptM ``Exists.intro #[none, some p₂, some ps[1]!,
        some (← mkAppM ``And.intro #[pf0, hL])])]
    addDecl (Declaration.thmDecl
      { name := c ++ (← sfxName "potCert"), levelParams,
        type := ← mkForallFVars tBs cty, value := ← mkLambdaFVars tBs
          (← mkExpectedTypeHint cert cty) })

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
    if ← nodePot T node then
      derivePot c info.levelParams T Tc timedBs node
      return
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
syntax (name := deriveHybridTimeCmd) "derive_hybrid_time " ("(" &"potential" ") ")? ident :
  command

/-- Elaborate `derive_hybrid_time R` and `derive_hybrid_time (potential) R`. -/
@[command_elab deriveHybridTimeCmd]
meta def elabDeriveHybridTime : CommandElab := fun stx => do
  let R ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  if stx[1].getNumArgs == 0 then liftTermElabM <| deriveHybridTime R
  else liftTermElabM <| derivePotential R

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

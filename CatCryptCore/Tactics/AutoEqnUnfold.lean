/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatchCore
public meta import CatCryptCore.Tactics.AutoDispatchCore

/-!
# One-step unfolding of recursive definitions applied to constructors

`eqn_unfold` rewrites, in the goal and in the local hypotheses, each application
`f a₁ … aₙ` of a definition `f` by pattern matching (structural or well-founded recursion,
or a non-recursive definition by `match`) whose argument at a pattern position of one of
the equation lemmas of `f` has a constructor at its head. The rewriting uses exactly the
equation lemmas of these definitions that have a pattern position (`f.eq_1`, `f.eq_2`, …,
obtained with `Lean.Meta.getEqnsFor?`), so an application to a variable is not rewritten
and the rewriting does not loop.

* A definition qualifies when it has a value, is not an instance, a structure projection
  or a matcher, and is not from a module of `AutoDispatch.foreignRoots` (the core and
  library roots).
* An argument has a constructor at its head when its head constant is a constructor, it
  is a natural number literal, it is `n + k` with `k` a positive literal, or its weak head
  normal form at instance transparency has one of these forms.
* A pattern position of an equation lemma `∀ xs, f p₁ … pₙ = r` is an index `i` with `pᵢ`
  not one of the variables `xs`.

The rewriting is `simp only` with these equation lemmas, at the goal and at the hypotheses
that contain such an application, for two rounds, so that an application exposed by the
first round is rewritten too. The tactic fails at once when no such application exists.
-/

@[expose] public section

meta section

namespace CatCrypt.Tactics.AutoEqnUnfold

open Lean Meta Elab Tactic

/-- The equation lemmas of `f` that have a pattern position, with the pattern positions of
each; empty when `f` is not a definition of the workspace by pattern matching. -/
def patternEqns (f : Name) : MetaM (Array (Name × Array Nat)) := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? f | return #[]
  if isInstanceCore env f || env.isProjectionFn f || isMatcherCore env f then return #[]
  if let some idx := env.getModuleIdxFor? f then
    let root := (env.header.moduleNames[idx.toNat]!).getRoot
    if AutoDispatch.foreignRoots.contains root then return #[]
  let some eqns ← getEqnsFor? f | return #[]
  let mut out := #[]
  for e in eqns do
    let ty := (← getConstInfo e).type
    let pos ← forallTelescopeReducing ty fun xs body => do
      let lhs ← match body.eq?, body.iff? with
        | some (_, l, _), _ => pure l
        | none, some (l, _) => pure l
        | none, none => return #[]
      unless lhs.getAppFn.isConstOf f do return #[]
      let args := lhs.getAppArgs
      let mut pos := #[]
      for i in [0:args.size] do
        unless args[i]!.isFVar && xs.contains args[i]! do pos := pos.push i
      return pos
    unless pos.isEmpty do out := out.push (e, pos)
  return out

/-- `a` is a natural number literal, `Nat.succ _`, or `_ + k` with `k` a positive
literal. -/
def isNatCtorForm (a : Expr) : Bool :=
  match a.nat? with
  | some _ => true
  | none =>
    a.isAppOfArity ``Nat.succ 1 || a.isRawNatLit ||
      (a.isAppOfArity ``HAdd.hAdd 6 && (a.appArg!.nat?.getD 0) > 0)

/-- `a` has a constructor at its head (see the module docstring). -/
def isCtorHead (a : Expr) : MetaM Bool := do
  let a := a.cleanupAnnotations
  let isCtor (t : Expr) : MetaM Bool := do
    if isNatCtorForm t then return true
    let some c := t.getAppFn.constName? | return false
    return (← getEnv).isConstructor c
  if ← isCtor a then return true
  if a.hasLooseBVars || a.hasExprMVar then return false
  isCtor (← withReducibleAndInstances (whnf a))

/-- The state of one collection: the equation lemmas found, and the pattern equation
lemmas of each constant already examined. -/
structure Found where
  /-- The equation lemmas to rewrite with. -/
  lemmas : Std.HashSet Name := {}
  /-- The pattern equation lemmas of each constant examined. -/
  cache : Std.HashMap Name (Array (Name × Array Nat)) := {}

/-- The equation lemmas of the applications in `e` of a qualifying definition to a
constructor at a pattern position, added to `st`. -/
def collect (e : Expr) (st : Found) : MetaM Found := do
  let ref ← IO.mkRef st
  forEachExpr' e fun t => do
    if !t.isApp then return true
    let some f := t.getAppFn.constName? | return true
    let st ← ref.get
    let eqns ← match st.cache[f]? with
      | some r => pure r
      | none =>
        let r ← patternEqns f
        ref.set { st with cache := st.cache.insert f r }
        pure r
    if eqns.isEmpty then return true
    let args := t.getAppArgs
    for (eq, pos) in eqns do
      if (← ref.get).lemmas.contains eq then continue
      for i in pos do
        if h : i < args.size then
          if ← isCtorHead args[i] then
            ref.modify fun s => { s with lemmas := s.lemmas.insert eq }
            break
    return true
  ref.get

/-- One round of `eqn_unfold` on `g`: `none` when no application qualifies, otherwise
the goal after rewriting (`none` inside when it is closed). -/
def eqnUnfoldRound (g : MVarId) : MetaM (Option (Option MVarId)) := g.withContext do
  let mut st : Found := {}
  let tgt ← instantiateMVars (← g.getType)
  st ← collect tgt st
  let atTarget := !st.lemmas.isEmpty
  let mut hyps := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let n := st.lemmas.size
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    st ← collect ty st
    if st.lemmas.size > n then hyps := hyps.push d.fvarId
  if st.lemmas.isEmpty then return none
  let mut thms : SimpTheorems := {}
  for n in st.lemmas do
    thms ← thms.addConst n
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx (fvarIdsToSimp := hyps) (simplifyTarget := atTarget)
  return some (r.map (·.2))

/-- `eqn_unfold` rewrites the applications of recursive definitions to constructors in
the goal and the hypotheses by their equation lemmas (see the module docstring); it fails
when there is none. -/
syntax (name := eqnUnfoldStx) "eqn_unfold" : tactic

/-- The elaborator of `eqn_unfold`. -/
@[tactic eqnUnfoldStx] def evalEqnUnfold : Tactic := fun _ => do
  let g ← getMainGoal
  let some r ← eqnUnfoldRound g |
    throwError "eqn_unfold: no recursive definition applied to a constructor"
  let some g := r | replaceMainGoal []
  let some r ← eqnUnfoldRound g | replaceMainGoal [g]
  replaceMainGoal r.toList

end CatCrypt.Tactics.AutoEqnUnfold

end

end

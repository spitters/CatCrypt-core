/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.RGraphInterp
public import CatCryptCore.Complexity.D.RespB.Basic

/-!
# The tactic `resp_b`

`resp_b` proves a goal `t.RespB R` (`Tm.RespB`, respect of a base relation by a term of D) for a
concrete term `t`. It is the first step of a free theorem of D: the abstraction theorem with
cost (`Tm.abstraction_cost`) turns `t.RespB R` into related results at equal cost.

The procedure works on one goal at a time.

* A goal `t.RespB R` is closed by a hypothesis when there is one. Otherwise `t` is reduced to
  weak head normal form; when its head is a constructor of `Tm`, the goal is unfolded by the
  equations of `Tm.RespB` (`simp only`), which unfold every constructor of the term down to the
  subterms that are not constructors (applications of definitions, variables of the
  meta-level); these become goals `s.RespB R` of the same procedure.
* A conjunction is split, `True` is closed, and the binders of a goal `∀ j, …` are introduced.
* Every other goal is an obligation: `Prim.RespB R p` of a primitive operation, the discreteness
  `∀ v v', R f v v' → v = v'` of a value that is branched on, written or sent, the reflexivity
  `R f x x` of a literal or a sampled, read or received value, `Sig.PosEq R S` of a fold, or
  `t.RespB R` of a term that is not a constructor. It is closed by `assumption`, else by
  `solve_by_elim` with the `@[resp_b]` lemmas and the arguments, else by
  `simp_all` with the `@[resp_b]` equations and equivalences, the arguments and the unfolding of
  `Prim.RespB` and `Sig.PosEq`.

An obligation that none of these closes stops the procedure with an error that states it.
`resp_b [t₁, …, tₙ]` adds the terms `tᵢ` to `solve_by_elim` and `simp_all`.

The registry is seeded here with the identity extension lemmas `Ty.relB_iff_eq`,
`Sig.fldRelB_iff_eq`, `ISig.fldRelB_iff_eq` and `Sig.posEq_of_iff_eq`: under a hypothesis
`∀ f a b, R f a b ↔ a = b` they close every obligation of a primitive. The lemmas of a
particular relation are registered in or above the module of the relation.

## Main definitions

* `resp_b`, `resp_b [t₁, …, tₙ]` — the tactic.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

attribute [resp_b] Ty.relB_iff_eq Sig.fldRelB_iff_eq ISig.fldRelB_iff_eq Sig.posEq_of_iff_eq

namespace RespBTac

meta section

/-- `resp_b` proves `t.RespB R` for a concrete term `t` of D: it unfolds `Tm.RespB` along the
constructors of `t`, splits the conjunctions and closes each remaining obligation by an
assumption, by `solve_by_elim` with the `@[resp_b]` lemmas, or by `simp_all` with the
`@[resp_b]` equations and equivalences. `resp_b [t₁, …, tₙ]` adds the terms `tᵢ` to both.
It fails with an error naming the first obligation it does not close. -/
syntax (name := respB) "resp_b" (" [" term,* "]")? : tactic

open Lean Meta Elab Tactic

/-- Whether the conclusion of the constant `n`, after its binders, is an equation or an
equivalence. -/
def isRewriteLemma (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return false
  forallTelescopeReducing ci.type fun _ c => do
    let c ← whnfR c
    return c.isAppOfArity ``Iff 2 || c.isAppOfArity ``Eq 3

/-- Whether the head of `e` is a constructor of `Tm`. -/
def isTmCtor (e : Expr) : MetaM Bool := do
  let .const n _ := e.getAppFn | return false
  match (← getEnv).find? n with
  | some (.ctorInfo ci) => return ci.induct == ``Tm
  | _ => return false

/-- Runs `tac` on the goal `g` alone; keeps its effect and returns `true` when it closes `g`,
restores the state and returns `false` otherwise. -/
def closes (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    evalTactic tac
    if (← getGoals).isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- The lemmas of an obligation: the rules of `solve_by_elim` and the rewrite rules of
`simp_all`. -/
structure Lemmas where
  /-- The rules of `solve_by_elim`: the registered lemmas and the arguments. -/
  rules : Array Term
  /-- The rewrite rules of `simp_all`: the registered equations and equivalences, the
  arguments, and the definitions `Prim.RespB` and `Sig.PosEq`. -/
  rewrites : Array Term

/-- Closes the obligation `g`, whose statement before its binders were introduced is `ty`, or
fails with an error that states `ty`. -/
def closeObligation (L : Lemmas) (ty : Expr) (g : MVarId) : TacticM Unit := do
  let rules ← L.rules.mapM fun t => `(Lean.Parser.Tactic.SolveByElim.arg| $t:term)
  let rewrites ← L.rewrites.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let tacs : Array (TSyntax `tactic) := #[
    ← `(tactic| assumption),
    ← `(tactic| solve_by_elim (maxDepth := 24) [$rules,*]),
    ← `(tactic| simp_all [$rewrites,*])]
  for tac in tacs do
    if ← closes g tac then return
  throwError "resp_b: no registered lemma closes the obligation{indentExpr ty}"

/-- The procedure of `resp_b` on one goal. -/
partial def respBGoal (L : Lemmas) (g : MVarId) : TacticM Unit := do
  let ty0 ← instantiateMVars (← g.getType)
  let (_, g) ← g.intros
  g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return
  if ty.isAppOfArity ``And 2 then
    let a := ty.getArg! 0
    let b := ty.getArg! 1
    let ga ← mkFreshExprSyntheticOpaqueMVar a
    let gb ← mkFreshExprSyntheticOpaqueMVar b
    g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
    respBGoal L ga.mvarId!
    respBGoal L gb.mvarId!
    return
  if ty.isAppOfArity ``Tm.RespB 4 then
    if ← closes g (← `(tactic| assumption)) then return
    let t ← whnfD (ty.getArg! 3)
    if ← isTmCtor t then
      let g ← g.replaceTargetDefEq (mkAppN ty.getAppFn (ty.getAppArgs.set! 3 t))
      setGoals [g]
      evalTactic (← `(tactic| simp only [Tm.RespB, and_true, true_and, implies_true]))
      for g' in ← getGoals do
        respBGoal L g'
      return
  closeObligation L ty0 g

/-- The registered lemmas and the arguments of a call of `resp_b`. -/
def lemmasOf (extra : Array Term) : TacticM Lemmas := do
  let names := respBExt.getState (← getEnv)
  let mut rules : Array Term := #[]
  let mut rewrites : Array Term := #[]
  for n in names do
    let id : Term := mkCIdent n
    rules := rules.push id
    if ← isRewriteLemma n then
      rewrites := rewrites.push id
  rewrites := rewrites ++ #[mkCIdent ``Prim.RespB, mkCIdent ``Sig.PosEq]
  return { rules := rules ++ extra, rewrites := rewrites ++ extra }

/-- The elaborator of `resp_b`. -/
@[tactic respB] def evalRespB : Tactic := fun stx => do
  let extra : Array Term := match stx with
    | `(tactic| resp_b [$ts,*]) => ts.getElems
    | _ => #[]
  let L ← lemmasOf extra
  let g ← getMainGoal
  let rest := (← getGoals).drop 1
  respBGoal L g
  setGoals rest

end

end RespBTac

end CatCrypt.Complexity.D

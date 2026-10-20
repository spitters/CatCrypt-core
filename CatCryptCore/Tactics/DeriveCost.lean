/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed

/-!
# Derived costs of recursive data functions

`derive_cost f` takes a computable data function `f`, recursive or not, and defines its cost
`f.timedCost` by the cost rules of `CatCryptCore.Tactics.DeriveTimed`. The cost takes the
arguments of `f`, each function-typed argument followed by its cost companion, and returns
`ℕ`; this is the convention of a registered cost, so `derive_timed` and `derive_reduction`
price every call of `f` through `f.timedCost` from then on.

## The body

The body priced is the one Lean keeps for the equation lemmas of `f`: for a structural or
well-founded recursion, the definition before its compilation to a recursor, in which the
recursive calls are applications of the constant `f`. For a non-recursive `f` it is the
definition itself.

## Cost rules

The rules are those of `derive_timed` for data terms (call-by-value):

* a call costs one plus the callee's cost at its arguments plus the costs of its arguments;
  a recursive call of `f` is priced by `f.timedCost` itself, so the cost is defined by the
  recursion of `f`, settled by Lean as a structural or well-founded recursion;
* a call of a function-typed parameter is priced by its cost companion;
* `if` and `match` cost one, plus the condition or the discriminants, plus the branch taken;
* constructors, literals, projections, casts and variables are free.

A class method on a local instance has no definition to price. `derive_cost (unit := m₁ … mₙ) f`
charges each listed method `mᵢ` on a local instance one unit plus its arguments; the listing
is a trusted statement about those methods, in the way a registered primitive cost is.

## What is refused

`f` whose result is a tree of a registered kind (use `derive_timed`), a callee that is
recursive or opaque and has no cost, a class method on a local instance that is not listed in
`unit`, and every refusal of the data rules of `derive_timed`. A cost whose recursion Lean
cannot settle is refused with Lean's reason.

The derivation reads the body of the equation lemmas as Ironwood's `assert_efficient` does
(D.-E. Hopwood, `Zcash/Meta/Efficient.lean`, dual-licensed under the MIT and Apache-2.0
licences).

## Main definitions

* `derive_cost f`, `derive_cost (unit := m₁ … mₙ) f` — define the cost `f.timedCost`
-/

public section

meta section

namespace CatCrypt.Tactics.DeriveCost

open Lean Elab Meta Term Command
open CatCrypt.Tactics.DeriveTimed

/-- The applications `m ps inst` in `e` of a method `m` of `units` to its parameters and a
local instance `inst`, without loose bound variables. -/
partial def unitPrefixes (units : Array Name) (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut acc := acc
      if let .const m _ := f then
        if units.contains m then
          if let some info ← getProjectionFnInfo? m then
            if h : info.numParams < args.size then
              let p := mkAppN f (args.extract 0 (info.numParams + 1))
              if args[info.numParams].consumeMData.isFVar && !p.hasLooseBVars &&
                  !acc.contains p then
                acc := acc.push p
      acc ← go f acc
      for a in args do acc ← go a acc
      return acc
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ s => go s acc
    | _ => return acc
  go e #[]

/-- Price `b` in `ctx` with each prefix of `ps` standing for a local function whose cost
companion is zero, so that each call of a listed method costs one plus its arguments. -/
def costWithUnits (ctx : Ctx) (ps : Array Expr) (b : Expr) : TermElabM Expr := do
  let rec go (i : Nat) (ctx : Ctx) (b : Expr) (us : Array (Expr × Expr)) : TermElabM Expr := do
    if h : i < ps.size then
      let p := ps[i]
      let t ← inferType p
      withLocalDeclD `unitMethod t fun u => do
        let zero ← forallTelescope (← whnfR t) fun ys _ => mkLambdaFVars ys (mkNatLit 0)
        let ctx := { ctx with locals := ctx.locals.insert u.fvarId! ⟨.fn, u, some zero⟩ }
        go (i + 1) ctx (b.replace fun s => if s == p then some u else none) (us.push (u, p))
    else
      let c ← costOf ctx b
      let c := us.foldl (fun c (u, p) => c.replaceFVar u p) c
      return (← Core.betaReduce c)
  go 0 ctx b #[]

/-- Derive and add the cost `c.timedCost` of the data function `c`, charging the class
methods `units` on local instances one unit. -/
def deriveCost (units : Array Name) (c : Name) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | throwError "derive_cost: unknown constant `{c}`"
  let costName := c ++ `timedCost
  if env.contains costName then throwError "derive_cost: `{costName}` already exists"
  let body ← match Structural.eqnInfoExt.find? env c, WF.eqnInfoExt.find? env c, info with
    | some i, _, _ => pure i.value
    | _, some i, _ => pure i.value
    | _, _, .defnInfo d => pure d.value
    | _, _, _ => throwError "derive_cost: `{c}` has no definition to price"
  -- Eta-expand to all binders of the type.
  let value ← lambdaTelescope body fun xs b => do
    forallTelescope (← instantiateForall info.type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta
  let (cType, cValue) ← lambdaTelescope value fun xs b => do
    if (← treeTy? (← inferType b)).isSome then
      throwError "derive_cost: the result of `{c}` is a tree; use `derive_timed`"
    for x in xs do
      if (← classify (← inferType x)) matches .tree | .treeFn then
        throwError "derive_cost: the binder `{x}` of `{c}` is a tree; use `derive_timed`"
    withBinders {} xs fun ctx bs _ => do
      let cType ← mkForallFVars bs (mkConst ``Nat)
      let ps ← unitPrefixes units b
      -- The recursive calls are priced through `costName`, declared for the derivation only.
      let saved ← getEnv
      addDecl (.axiomDecl
        { name := costName, levelParams := info.levelParams, type := cType, isUnsafe := false })
      let cost ← try costWithUnits ctx ps b finally setEnv saved
      let cost ← instantiateMVars cost
      if cost.hasMVar then throwError "derive_cost: the cost of `{c}` has unassigned universes"
      return (cType, ← mkLambdaFVars bs cost)
  addTimedDef costName info.levelParams cType cValue

/-- `derive_cost f` defines the cost `f.timedCost` of the data function `f` by the recursion
of `f`; `derive_cost (unit := m₁ … mₙ) f` charges the class methods `mᵢ` on local instances
one unit. -/
syntax (name := deriveCostCmd) "derive_cost " ("(" &"unit" " := " ident+ ") ")? ident : command

@[command_elab deriveCostCmd]
def elabDeriveCost : CommandElab := fun stx => do
  liftTermElabM do
    -- The optional group `(unit := m₁ … mₙ)` is a node of five children when present.
    let units ← if stx[1].getNumArgs == 5 then
        stx[1][3].getArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
      else pure #[]
    deriveCost units (← realizeGlobalConstNoOverloadWithInfo stx[2])

end CatCrypt.Tactics.DeriveCost

end

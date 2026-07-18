/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Deep.RawCode
import CatCryptCore.Deep.Eval
import Lean

/-!
# Reflection: `SPComp` → `RawCode`

An elaboration-time reifier that turns a shallow `SPComp α` program (built
from the six core constructors `SPComp.pure`, `SPComp.bind`, `SPComp.sample`,
`SPComp.get`, `SPComp.set`, `SPComp.fail`, and/or `do`-notation) into the
corresponding syntactic `RawCode α` term.

## Usage

```lean
def myProg : SPComp Bool := do
  let b ← SPComp.sample Bool
  SPComp.set myLoc b
  return b

def myProgRaw : RawCode Bool := rawCode% myProg
```

## Translation

| `SPComp` constructor           | `RawCode` image                                                    |
|---|---|
| `SPComp.pure a`               | `RawCode.ret a`                                                     |
| `SPComp.bind c k`             | `RawCode.bind (reify c) (fun x => reify (k x))`                     |
| `SPComp.sample α`             | `RawCode.sample α`                                                  |
| `SPComp.get ℓ`                | `RawCode.bind (RawCode.get ℓ) (fun x => RawCode.ret x.down)`        |
| `SPComp.set ℓ v`              | `RawCode.bind (RawCode.put ℓ v) (fun _ => RawCode.ret ())`          |
| `SPComp.fail`                 | `RawCode.fail`                                                      |

The `get`/`set` cases use an extra `RawCode.bind` because `RawCode.get` returns
`RawCode (ULift ℓ.ty)` (the universe-polymorphic deep embedding lifts the
location type), while `SPComp.get` returns `SPComp ℓ.ty`. The post-composition
with `RawCode.ret ∘ ULift.down` re-lands at the author's expected type.

The reifier pattern-matches on weak-head-normal heads; the `Monad SPComp`
instance unfolds under `whnf`, so programs written with `do`-notation or `>>=`
land on the `SPComp.bind` / `SPComp.pure` heads automatically.

## Scope

Handles the six canonical constructors directly. Any other `SPComp`-typed
subterm — a call to an abstract primitive `f a : SPComp β`, a locally-bound
oracle `f : α → SPComp β`, or an opaque constant that does not delta-unfold to a
constructor — is reflected as `RawCode.embed`, an opaque leaf holding the shallow
subterm. Since `RawCode.eval (embed c) = c` definitionally, the reified program
still round-trips, and `IsValid.embed` supplies its validity proof. The reifier
never fails on an `SPComp`-typed term. (A structured `RawCode.oracleCall` image
is also available for opaque heads that are intended to be linked later via
`substOracle`; it is not the default because its `eval` is `SPComp.fail`, so it
does not round-trip.)

## Correctness

For any `SPComp` program built from the canonical constructors, evaluation of
the reified form reduces definitionally (up to the pure-right monad law for
`get`/`set`) to the original shallow program. The built-in `simp` lemmas in
`Deep/Eval.lean` (`eval_ret`, `eval_bind`, `eval_get`, `eval_put`, `eval_sample`,
`eval_fail`) normalize round-trip identities.
-/

namespace CatCrypt.Deep.Reflect

open Lean Meta Elab Term

/-- Reduce to a form whose head is an `SPComp` constructor.  We `whnfR` first
    (which does not unfold `SPComp.bind`/`SPComp.pure`, since they are not
    `@[reducible]`).  If the head is a type-class bind/pure (from do-notation /
    `>>=`) we re-project through the instance with full `whnf`.  If the head is
    any other definition — a top-level `def game : SPComp α`, an abbreviation, a
    scheme-field projection — we delta-unfold it and retry, so a named program
    reflects as readily as an inline one.  The six `SPComp` constructors are
    matched *before* the unfold fallback, so they stay opaque and reflection
    stops at them rather than collapsing into the `Heap → SDistr` body. -/
private partial def normalizeHead (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Bind.bind, _) | (``Pure.pure, _) =>
    -- Project the `Monad SPComp` instance to expose the `SPComp.bind`/`SPComp.pure`
    -- head, at `.instances` transparency so the (regular, non-reducible) `SPComp`
    -- constructor is not itself unfolded into its `Heap → SDistr` body.
    withTransparency .instances (whnf e)
  | (``CatCrypt.Core.SPComp.pure, _) | (``CatCrypt.Core.SPComp.bind, _)
  | (``CatCrypt.Core.SPComp.sample, _) | (``CatCrypt.Core.SPComp.get, _)
  | (``CatCrypt.Core.SPComp.set, _) | (``CatCrypt.Core.SPComp.fail, _) =>
    pure e
  | _ =>
    match ← Meta.unfoldDefinition? e with
    | some e' => normalizeHead e'
    | none => pure e

/-- Recursively rewrite an `SPComp α` expression into a `RawCode α` term. -/
partial def reifySPComp (e : Expr) : MetaM Expr := do
  let e ← normalizeHead e
  match e.getAppFnArgs with
  | (``CatCrypt.Core.SPComp.pure, args) =>
    -- `SPComp.pure {α} (a : α) : SPComp α` — 2 explicit+implicit args
    if args.size ≥ 2 then
      let α := args[0]!
      let a := args[1]!
      mkAppOptM ``CatCrypt.Deep.RawCode.ret #[some α, some a]
    else
      throwError "reifySPComp: SPComp.pure is not fully applied:{indentExpr e}"
  | (``CatCrypt.Core.SPComp.bind, args) =>
    -- `SPComp.bind {α β} (c : SPComp α) (f : α → SPComp β) : SPComp β` — 4 args
    if args.size ≥ 4 then
      let α := args[0]!
      let β := args[1]!
      let c := args[2]!
      let k := args[3]!
      let c' ← reifySPComp c
      let k' ← Meta.lambdaTelescope k fun xs body => do
        let body' ← reifySPComp body
        Meta.mkLambdaFVars xs body'
      mkAppOptM ``CatCrypt.Deep.RawCode.bind #[some α, some β, some c', some k']
    else
      throwError "reifySPComp: SPComp.bind is not fully applied:{indentExpr e}"
  | (``CatCrypt.Core.SPComp.sample, args) =>
    -- `SPComp.sample (α : Type*) [Fintype α] [Nonempty α] : SPComp α` — 3 args
    if args.size ≥ 3 then
      let α := args[0]!
      -- let Lean re-synthesize the Fintype / Nonempty instances for RawCode
      mkAppOptM ``CatCrypt.Deep.RawCode.sample #[some α, none, none]
    else
      throwError "reifySPComp: SPComp.sample is not fully applied:{indentExpr e}"
  | (``CatCrypt.Core.SPComp.get, args) =>
    -- `SPComp.get (ℓ : Location) : SPComp ℓ.ty` — 1 arg
    -- `RawCode.get (ℓ : Location) : RawCode (ULift ℓ.ty)`
    -- Post-compose with `ret ∘ ULift.down` to land at `RawCode ℓ.ty`.
    if args.size ≥ 1 then
      let ℓ := args[0]!
      let tyTm ← mkAppM ``CatCrypt.Core.Location.ty #[ℓ]
      let liftedTyTm ← mkAppM ``ULift #[tyTm]
      let getRaw ← mkAppOptM ``CatCrypt.Deep.RawCode.get #[some ℓ]
      let k ← Meta.withLocalDeclD `x liftedTyTm fun x => do
        let xDown ← mkAppM ``ULift.down #[x]
        let ret ← mkAppOptM ``CatCrypt.Deep.RawCode.ret #[some tyTm, some xDown]
        Meta.mkLambdaFVars #[x] ret
      mkAppOptM ``CatCrypt.Deep.RawCode.bind #[some liftedTyTm, some tyTm, some getRaw, some k]
    else
      throwError "reifySPComp: SPComp.get is not fully applied:{indentExpr e}"
  | (``CatCrypt.Core.SPComp.set, args) =>
    -- `SPComp.set (ℓ : Location) (v : ℓ.ty) : SPComp Unit` — 2 args
    -- `RawCode.put (ℓ : Location) (v : ℓ.ty) : RawCode (ULift Unit)`
    if args.size ≥ 2 then
      let ℓ := args[0]!
      let v := args[1]!
      let unitTm := Expr.const ``Unit []
      let liftedUnit ← mkAppM ``ULift #[unitTm]
      let unitVal := Expr.const ``Unit.unit []
      let putRaw ← mkAppOptM ``CatCrypt.Deep.RawCode.put #[some ℓ, some v]
      let k ← Meta.withLocalDeclD `_u liftedUnit fun u => do
        let ret ← mkAppOptM ``CatCrypt.Deep.RawCode.ret #[some unitTm, some unitVal]
        Meta.mkLambdaFVars #[u] ret
      mkAppOptM ``CatCrypt.Deep.RawCode.bind #[some liftedUnit, some unitTm, some putRaw, some k]
    else
      throwError "reifySPComp: SPComp.set is not fully applied:{indentExpr e}"
  | (``CatCrypt.Core.SPComp.fail, args) =>
    -- `SPComp.fail {α} : SPComp α` — 1 implicit arg
    if args.size ≥ 1 then
      let α := args[0]!
      mkAppOptM ``CatCrypt.Deep.RawCode.fail #[some α]
    else
      throwError "reifySPComp: SPComp.fail is not fully applied:{indentExpr e}"
  | _ =>
    -- Opaque / abstract head: the expression is `SPComp`-typed but its head is
    -- none of the six canonical constructors and it does not delta-unfold to one
    -- (an abstract primitive `f a : SPComp β`, a locally-bound `f : α → SPComp β`,
    -- an opaque constant). Reflect it as an `embed` leaf carrying the shallow
    -- subterm verbatim. `RawCode.eval` sends `embed c` back to `c` definitionally,
    -- so the reified program round-trips; `IsValid.embed` gives it an automatic
    -- validity proof. The reifier therefore never fails on an `SPComp`-typed term.
    let ty ← inferType e
    match ty.getAppFnArgs with
    | (``CatCrypt.Core.SPComp, #[β]) =>
      mkAppOptM ``CatCrypt.Deep.RawCode.embed #[some β, some e]
    | _ =>
      throwError "reifySPComp: expected an `SPComp`-typed subterm to reflect:{indentExpr e}"

/-- `rawCode% e` elaborates `e` as an `SPComp α` and reifies it to a
    `RawCode α` term at elaboration time. -/
elab "rawCode% " e:term : term => do
  let e' ← elabTerm e none
  let e' ← instantiateMVars e'
  reifySPComp e'

end CatCrypt.Deep.Reflect

/-! ## Smoke tests

`rawCode%` accepts either an inline `SPComp` expression or a named program: its
head is reduced with `whnfR`, the `Monad SPComp` instance is projected at
`.instances` transparency for do-notation / `>>=`, and any other definition (a
top-level `def game : SPComp α`, an abbreviation, a scheme-field projection) is
delta-unfolded and retried — while the six `SPComp` constructors stay opaque, so
reflection stops at them instead of collapsing into the `Heap → SDistr` body. A
subterm whose head is none of these after unfolding (a call to an abstract
primitive `f a`, a locally-bound oracle, an opaque constant) is reflected as an
`embed` leaf and round-trips through `eval`.
-/

section SmokeTest

open CatCrypt.Core CatCrypt.Deep

/-- Sample-then-return, inlined in `rawCode%`. -/
private noncomputable def deepCoin : RawCode Bool :=
  rawCode% (SPComp.bind (SPComp.sample Bool) (fun b => SPComp.pure b))

/-- Failure. -/
private noncomputable def deepFail : RawCode Bool :=
  rawCode% (SPComp.fail : SPComp Bool)

/-- `pure` applied directly. -/
private noncomputable def deepPure : RawCode Nat :=
  rawCode% (SPComp.pure 42)

/-- A top-level `def` written in do-notation reflects without inlining: the
    reifier unfolds `smokeGame` and projects the monad instance, stopping at the
    `SPComp` constructors. -/
private noncomputable def smokeGame : SPComp Bool := do
  let b ← SPComp.sample Bool
  SPComp.pure (xor b true)

private noncomputable def smokeGameRaw : RawCode Bool := rawCode% smokeGame

/-- The reflected named program evaluates back to the original shallow game. -/
private theorem smokeGame_reflect : smokeGameRaw.eval = smokeGame := by
  simp [smokeGameRaw, RawCode.eval, smokeGame]

/-- A named oracle *family* reflects under a binder: `fun m => rawCode% (f m)`
    unfolds `f` applied to the bound `m`. -/
private noncomputable def smokeOracle : Bool → SPComp Bool := fun m => do
  let k ← SPComp.sample Bool
  SPComp.pure (xor k m)

private noncomputable def smokeOracleRaw : Bool → RawCode Bool :=
  fun m => rawCode% (smokeOracle m)

/-! ### Reflecting abstract-primitive games

An abstract `f : Bool → SPComp Bool` models a call to a primitive the game does
not implement. `rawCode%` reflects `f true` as an `embed` leaf instead of
throwing, and the reflected program round-trips through `eval`. -/

variable (f : Bool → SPComp Bool)

/-- A game calling an abstract primitive reflects to a `RawCode` (does not throw):
    `f true` becomes an `embed` leaf, the trailing `SPComp.pure` a `ret`. -/
private noncomputable def deepAbstract : RawCode Bool :=
  rawCode% (SPComp.bind (f true) (fun b => SPComp.pure b))

/-- `eval` round-trips the abstract-primitive game to the original shallow term.
    Definitional: `eval (embed (f true)) = f true` and `eval (ret b) = pure b`,
    then η collapses `fun b => SPComp.pure b` to `SPComp.pure`. -/
private theorem deepAbstract_reflect :
    (deepAbstract f).eval = SPComp.bind (f true) SPComp.pure := rfl

/-- Concrete and opaque heads coexist: `sample Bool` reflects to `RawCode.sample`,
    the following abstract `f b` to an `embed` leaf. -/
private noncomputable def deepMixed : RawCode Bool :=
  rawCode% (SPComp.bind (SPComp.sample Bool) (fun b => f b))

/-- The mixed game round-trips: the `sample` and the embedded `f b` both evaluate
    back to their shallow images. -/
private theorem deepMixed_reflect :
    (deepMixed f).eval = SPComp.bind (SPComp.sample Bool) (fun b => f b) := rfl

end SmokeTest

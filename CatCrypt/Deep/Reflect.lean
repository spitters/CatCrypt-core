/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Code
import CatCrypt.Deep.RawCode
import CatCrypt.Deep.Eval
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

Handles the six canonical constructors. Unknown subterms raise a descriptive
elaboration error rather than emitting an opaque `oracleCall` — a future
extension could plumb user-annotated oracle procedures automatically.

## Correctness

For any `SPComp` program built from the canonical constructors, evaluation of
the reified form reduces definitionally (up to the pure-right monad law for
`get`/`set`) to the original shallow program. The built-in `simp` lemmas in
`Deep/Eval.lean` (`eval_ret`, `eval_bind`, `eval_get`, `eval_put`, `eval_sample`,
`eval_fail`) normalize round-trip identities.
-/

namespace CatCrypt.Deep.Reflect

open Lean Meta Elab Term

/-- Reduce to a form where the head is a `SPComp`-constructor.  We use
    `whnfR` first (which doesn't unfold `SPComp.bind`/`SPComp.pure` since
    they aren't `@[reducible]`), then if the head is a type-class bind/pure
    (from do-notation / `>>=`), we re-project through the instance with
    full `whnf`. -/
private def normalizeHead (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Bind.bind, _) | (``Pure.pure, _) =>
    whnf e
  | _ => pure e

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
    throwError "reifySPComp: unsupported head (expected SPComp.pure / .bind / .sample / .get / .set / .fail after whnf):{indentExpr e}"

/-- `rawCode% e` elaborates `e` as an `SPComp α` and reifies it to a
    `RawCode α` term at elaboration time. -/
elab "rawCode% " e:term : term => do
  let e' ← elabTerm e none
  let e' ← instantiateMVars e'
  reifySPComp e'

end CatCrypt.Deep.Reflect

/-! ## Smoke tests

The `rawCode%` macro currently requires its argument to be an inline `SPComp`
expression whose head is a visible `SPComp` constructor (or reduces to one
under `whnf`).  Top-level `def` references that beta-reduce past `SPComp.bind`
to the underlying `Heap → SDistr …` function body are not yet recognized —
that's a planned refinement (by making the reifier unfold regular definitions
selectively while keeping `SPComp.*` opaque).  In practice this means inline
your program in the `rawCode%` call or pre-reduce via `show`.
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

end SmokeTest

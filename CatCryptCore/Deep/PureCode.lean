/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.RawCode
import CatCryptCore.Deep.Eval
import CatCryptCore.Deep.Reflect

/-!
# Syntactic purity: state-free deep code evaluates to `IsPure`

This file provides the syntactic backend for `SPComp.IsPure` goals:

* `RawCode.StateFree` — an inductive predicate marking code built only from
  `ret` / `bind` / `sample` / `fail` (no `get`, no `put`, no `oracleCall`,
  no `embed`).
* `RawCode.eval_isPure_of_stateFree` — soundness: state-free code evaluates
  to a heap-independent (`IsPure`) computation.
* `ssprove_ispure_reflect` — a tactic that reifies the program of an
  `SPComp.IsPure` goal into `RawCode` via `Reflect.reifySPComp` and changes
  the goal to `IsPure` of the reified code's `eval` (definitional, since the
  reflection equations `eval_ret` / `eval_bind` / `eval_sample` / `eval_fail`
  are all `rfl`).
* `ssprove_statefree` — constructor search discharging `StateFree` goals.

## Representation choice: `Prop`, not `Bool`

`RawCode.bind` binds its continuation as a function `k : α → RawCode β`
(HOAS-style), so a `Bool`-valued structural decider cannot traverse it: there
is no way to inspect `k` without an argument, and no way to enumerate `α` in
general. We therefore use an inductive predicate whose `bind` rule quantifies
over all continuation values (`∀ b, StateFree (k b)`), exactly mirroring the
existing `RawCode.NoOracleCall`. The tactic establishes it by constructor
search (`apply`/`intro` cascade) instead of `decide`.

## Hierarchy

Syntactically state-free is strictly stronger than `IsPure`: e.g.
`get ℓ >>= fun _ => ret 0` is semantically heap-independent (hence `IsPure`)
but not `StateFree`. `IsPure` in turn is strictly stronger than any
support-level fact. Sampling and failure are compatible with purity; only
`get`/`put` (and opaque code: `oracleCall`, `embed`) break the syntactic
criterion.
-/

set_option autoImplicit false

namespace CatCrypt.Deep

open CatCrypt.Core

universe u

namespace RawCode

/-- A `RawCode` tree is *state-free* when it is built only from
    `ret`, `bind`, `sample`, and `fail` — no heap access (`get`/`put`)
    and no opaque code (`oracleCall`, `embed`).

    The `bind` rule quantifies over all continuation values, since the
    continuation is a function (the free monad binds via Lean functions). -/
inductive StateFree : {α : Type u} → RawCode α → Prop where
  | ret {α : Type u} (a : α) : StateFree (.ret a)
  | bind {α β : Type u} {c : RawCode β} {k : β → RawCode α}
      (hc : StateFree c) (hk : ∀ b, StateFree (k b)) : StateFree (.bind c k)
  | sample {T : Type u} [Fintype T] [Nonempty T] : StateFree (.sample T)
  | fail {α : Type u} : StateFree (@RawCode.fail α)

/-- **Soundness of the syntactic purity criterion**: state-free code
    evaluates to a heap-independent computation.

    Induction over the `StateFree` derivation; each case is the matching
    `IsPure` combinator (`pure_isPure` / `bind_isPure` / `sample_isPure` /
    `fail_isPure`). -/
theorem eval_isPure_of_stateFree {α : Type u} {c : RawCode α}
    (h : StateFree c) : SPComp.IsPure c.eval := by
  induction h with
  | ret a => exact SPComp.pure_isPure a
  | bind _ _ ih_c ih_k => exact SPComp.bind_isPure ih_c ih_k
  | sample => exact SPComp.sample_isPure _
  | fail => exact SPComp.fail_isPure

end RawCode

/-! ## Tactic front-end

`ssprove_ispure_reflect` does the reflection step; `ssprove_statefree`
discharges the resulting `StateFree` side goal. They are combined into
`ssprove_ispure_syn` in `CatCrypt.Tactics.VC`. -/

open Lean Meta Elab Tactic in
/-- Reify the program `c` of an `SPComp.IsPure c` goal into `RawCode` and
    change the goal to `SPComp.IsPure r.eval` where `r = rawCode% c`.
    The change is definitional because the reflection equations for
    `ret`/`bind`/`sample`/`fail` (and `get`/`set`) hold by `rfl`.

    Fails (cleanly, for `first`-fallback) when the program contains
    unreifiable subterms: applications of abstract functions, `embed`,
    oracle calls, `ite`, or anything whose head is not an `SPComp`
    constructor after `whnf`. -/
elab "ssprove_ispure_reflect" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (_, c) := tgt.app2? ``CatCrypt.Core.SPComp.IsPure
    | throwError "ssprove_ispure_reflect: goal is not of the form `SPComp.IsPure c`:{indentExpr tgt}"
  let r ← Reflect.reifySPComp c
  let evalR ← mkAppM ``CatCrypt.Deep.RawCode.eval #[r]
  let newTgt ← mkAppM ``CatCrypt.Core.SPComp.IsPure #[evalR]
  let goal ← goal.change newTgt
  replaceMainGoal [goal]

/-- Discharge a `RawCode.StateFree c` goal for `c` built from
    `ret` / `bind` / `sample` / `fail` by constructor search. -/
macro "ssprove_statefree" : tactic =>
  `(tactic| repeat' first
      | exact CatCrypt.Deep.RawCode.StateFree.ret _
      | apply CatCrypt.Deep.RawCode.StateFree.sample
      | exact CatCrypt.Deep.RawCode.StateFree.fail
      | apply CatCrypt.Deep.RawCode.StateFree.bind
      | intro _)

/-! ## Smoke tests -/

section SmokeTest

/-- Sample-bind-ret is state-free. -/
example : RawCode.StateFree
    (RawCode.bind (RawCode.sample Bool) (fun b => RawCode.ret b)) := by
  ssprove_statefree

/-- Fail is state-free. -/
example : RawCode.StateFree (@RawCode.fail Bool) := by
  ssprove_statefree

/-- Soundness applied to a concrete tree. -/
example : SPComp.IsPure
    (RawCode.bind (RawCode.sample Bool) (fun b => RawCode.ret b)).eval := by
  apply RawCode.eval_isPure_of_stateFree
  ssprove_statefree

/-- `get` is NOT state-free: the constructor search must fail. -/
example (ℓ : CatCrypt.Core.Location) :
    ¬ RawCode.StateFree (RawCode.get ℓ) := by
  intro h; cases h

/-- Full pipeline on a shallow program: reflect, apply soundness, search. -/
example : SPComp.IsPure
    (SPComp.bind (SPComp.sample Bool) (fun b => SPComp.pure b)) := by
  ssprove_ispure_reflect
  apply RawCode.eval_isPure_of_stateFree
  ssprove_statefree

/-- The `first`-style fallback closes an abstract program: reflection either
    discharges it or falls through to the hypothesis. -/
example (A : SPComp Bool) (hA : SPComp.IsPure A) : SPComp.IsPure A := by
  first | (ssprove_ispure_reflect; done) | exact hA

end SmokeTest

end CatCrypt.Deep

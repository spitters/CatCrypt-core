/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Deep.RawCode

/-!
# Deterministic Code Predicate

This file provides the `IsDeterministic` predicate for `RawCode`,
identifying computations that never use `sample` or `fail`.

## Main definitions

* `IsDeterministic` - Predicate: code never uses `sample` or `fail`
* `DetCode` - Bundled deterministic code with proof

## Motivation

CatCrypt code is defined in terms of `RawCode`, which supports probabilistic
sampling. However, many extracted programs (from hax) are purely deterministic:
they only use `ret`, `bind`, `get`, and `put`. This predicate identifies
such programs, enabling reasoning about determinism in cryptographic proofs.
-/

namespace CatCrypt.Deep

open CatCrypt.Core

universe u

/-! ## IsDeterministic Predicate

A `RawCode` computation is deterministic if it never uses `sample` or `fail`.
This is an inductive predicate that closely mirrors the structure of `ValidCode`
but without the location constraints and without the `sample`/`fail` cases. -/

/-- A computation is deterministic if it only uses `ret`, `bind`, `get`, and `put`.
    No probabilistic sampling or failure is allowed. -/
inductive IsDeterministic : {α : Type u} → RawCode α → Prop where
  | ret {α : Type u} (a : α) : IsDeterministic (RawCode.ret a)
  | bind {α β : Type u} (c : RawCode α) (k : α → RawCode β)
      (hc : IsDeterministic c) (hk : ∀ a, IsDeterministic (k a)) :
      IsDeterministic (RawCode.bind c k)
  | get (ℓ : Core.Location) : IsDeterministic (RawCode.get ℓ)
  | put (ℓ : Core.Location) (v : ℓ.ty) : IsDeterministic (RawCode.put ℓ v)
  -- Note: no case for `sample`, `fail`, or `oracleCall`

/-! ## Properties of IsDeterministic -/

/-- Deterministic code never starts with `fail`. -/
theorem IsDeterministic.not_fail {α : Type u} : ¬IsDeterministic (RawCode.fail (α := α)) := by
  intro h; cases h

/-- Deterministic code never starts with `sample`. -/
theorem IsDeterministic.not_sample {T : Type u} [Fintype T] [Nonempty T] :
    ¬IsDeterministic (RawCode.sample T) := by
  intro h; cases h

/-- Deterministic code never starts with `oracleCall`. -/
theorem IsDeterministic.not_oracleCall {op : ℕ} {dom codom : Type u} {x : dom} :
    ¬IsDeterministic (RawCode.oracleCall op dom codom x) := by
  intro h; cases h

/-- If `bind c k` is deterministic, then `c` is deterministic. -/
theorem IsDeterministic.of_bind_left {α β : Type u} {c : RawCode α} {k : α → RawCode β}
    (h : IsDeterministic (RawCode.bind c k)) : IsDeterministic c := by
  cases h with
  | bind _ _ hc _ => exact hc

/-- If `bind c k` is deterministic, then `k a` is deterministic for all `a`. -/
theorem IsDeterministic.of_bind_right {α β : Type u} {c : RawCode α} {k : α → RawCode β}
    (h : IsDeterministic (RawCode.bind c k)) : ∀ a, IsDeterministic (k a) := by
  cases h with
  | bind _ _ _ hk => exact hk

/-- Deterministic code has a nonempty return type.
    This follows because every deterministic code form produces a value:
    `ret a` has `a`, `get` returns `ULift ℓ.ty` (inhabited), `put` returns `ULift Unit`,
    and `bind` inherits from its continuation. -/
theorem IsDeterministic.nonempty {α : Type u} {c : RawCode α}
    (h : IsDeterministic c) : Nonempty α := by
  induction h with
  | ret a => exact ⟨a⟩
  | bind _ _ _ _ ih_c ih_k =>
    exact ih_k (Classical.choice ih_c)
  | get ℓ => exact ⟨⟨default⟩⟩
  | put _ _ => exact ⟨⟨()⟩⟩

/-! ## Combinators for Deterministic Code

Helper combinators that maintain the `IsDeterministic` predicate. -/

/-- A deterministic computation bundled with its proof. -/
structure DetCode (α : Type u) where
  code : RawCode α
  isDet : IsDeterministic code

namespace DetCode

/-- Pure return is deterministic. -/
def ret {α : Type u} (a : α) : DetCode α where
  code := .ret a
  isDet := .ret a

/-- Bind preserves determinism. -/
def bind {α β : Type u} (x : DetCode α) (f : α → DetCode β) : DetCode β where
  code := .bind x.code fun a => (f a).code
  isDet := .bind x.code (fun a => (f a).code) x.isDet (fun a => (f a).isDet)

/-- Get is deterministic. -/
def get (ℓ : Core.Location) : DetCode (ULift ℓ.ty) where
  code := .get ℓ
  isDet := .get ℓ

/-- Put is deterministic. -/
def put (ℓ : Core.Location) (v : ℓ.ty) : DetCode (ULift Unit) where
  code := .put ℓ v
  isDet := .put ℓ v

end DetCode

end CatCrypt.Deep

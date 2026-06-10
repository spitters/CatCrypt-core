/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Relational.Rules

/-!
# Synchronization Tactics

This file provides tactics for synchronous relational reasoning,
where both sides of a relational judgment execute the same operation.

## Main tactics

* `ssprove_sync` - apply synchronous rule when both sides have same head
* `ssprove_sync_eq` - sync with equality postcondition (heap equality invariant)
* `ssprove_code_simpl` - simplify bind/pure chains in SPComp
* `ssprove_sync_bij` - bijection coupling for sampling

## Implementation Notes

The tactics try each rule in sequence until one succeeds:
1. `rHoare_sample_same` - when both sides sample from the same distribution
2. `rHoare_get_sync` - when both sides read from the same location
3. `rHoare_set_sync` - when both sides write to the same location
4. `rHoare_ret_same` - when both sides return the same pure value

## References

* SSProve: theories/Crypt/package/pkg_rhl.v
-/

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational
open CatCrypt.Core
open CatCrypt.Prob

/-- `ssprove_sync` applies the appropriate synchronous rule when both
sides of a relational judgment have the same head operation.

Supported operations:
- `sample`: applies `rHoare_sample_same`
- `get`: applies `rHoare_get_sync` with `rfl` for the sync condition
- `set`: applies `rHoare_set_sync` with `assumption` for the invariant
- `ret`/`pure`: applies `rHoare_ret_same`

Example:
```
theorem sync_sample : rHoare Φ (SPComp.sample α) (SPComp.sample α)
    (fun a h₁ b h₂ => Φ h₁ h₂ ∧ a = b) := by
  ssprove_sync
```
-/
macro "ssprove_sync" : tactic => `(tactic| (
  first
  | apply rHoare_sample_same
  | apply rHoare_get_sync <;> [intro h₁ h₂ _; rfl]
  | apply rHoare_set_sync <;> [intro h₁ h₂ _; assumption]
  | apply rHoare_ret_same
  | fail "ssprove_sync: no matching rule (expected sample, get, set, or ret)"
))

/-- `ssprove_sync_eq` applies synchronous rules that establish equality
between the results on both sides, using heap equality as the invariant.

This version assumes the precondition implies heap equality (h₁ = h₂)
and uses `rw [heq]` to discharge synchronization conditions.

Example:
```
theorem sync_get_eq : rHoare (fun h₁ h₂ => h₁ = h₂)
    (SPComp.get l) (SPComp.get l)
    (fun v₁ h₁ v₂ h₂ => h₁ = h₂ ∧ v₁ = v₂) := by
  ssprove_sync_eq
```
-/
macro "ssprove_sync_eq" : tactic => `(tactic| (
  first
  | apply rHoare_sample_same
  | apply rHoare_get_sync <;> [intro h₁ h₂ heq; rw [heq]]
  | apply rHoare_set_sync <;> [intro h₁ h₂ heq; rw [heq]]
  | apply rHoare_ret <;> [intro h₁ h₂ _; constructor <;> [rfl; rfl]]
  | fail "ssprove_sync_eq: no matching rule"
))

-- Note: ssprove_code_simpl is defined in CatCrypt.Tactics.Basic to avoid duplication

/-- `ssprove_sync_bij f` applies bijection coupling for sampling.

When both sides sample from uniform distributions and the samples
are related by a bijection `f`, this tactic establishes that the
postcondition holds with `f a = b`.

Example:
```
theorem sync_bij : rHoare Φ (SPComp.sample α) (SPComp.sample β)
    (fun a h₁ b h₂ => Φ h₁ h₂ ∧ f a = b) := by
  ssprove_sync_bij f
```
-/
macro "ssprove_sync_bij" f:term : tactic => `(tactic| (
  apply rHoare_sample_bij _ _ $f
))

/-- `ssprove_sync_get` applies the synchronized get rule.

This generates a subgoal requiring the precondition to imply
that both heaps have the same value at the location.
-/
macro "ssprove_sync_get" : tactic => `(tactic| (
  first
  | apply rHoare_get_sync
  | fail "ssprove_sync_get: goal is not a synchronized get"
))

/-- `ssprove_sync_set` applies the synchronized set rule.

This generates a subgoal requiring the precondition to be preserved
after setting the same value on both heaps.
-/
macro "ssprove_sync_set" : tactic => `(tactic| (
  first
  | apply rHoare_set_sync
  | fail "ssprove_sync_set: goal is not a synchronized set"
))

/-- `ssprove_sync_ret` applies the return rule for same values. -/
macro "ssprove_sync_ret" : tactic => `(tactic| (
  first
  | apply rHoare_ret_same
  | fail "ssprove_sync_ret: goal is not a synchronized ret"
))

/-- `ssprove_sync_sample` applies the diagonal coupling for same distribution. -/
macro "ssprove_sync_sample" : tactic => `(tactic| (
  first
  | apply rHoare_sample_same
  | fail "ssprove_sync_sample: goal is not a synchronized sample"
))

/-- `ssprove_bind` applies the bind rule for sequential composition.

This decomposes a bind into two subgoals:
1. The first computation satisfies an intermediate postcondition
2. The continuations satisfy the final postcondition given the intermediate one
-/
macro "ssprove_bind" : tactic => `(tactic| (
  first
  | apply rHoare_bind
  | fail "ssprove_bind: goal is not a bind composition"
))

/-- `ssprove_conseq` applies the consequence rule.

This allows strengthening the precondition and weakening the postcondition.
Generates two subgoals for the pre/post implications and the inner judgment.
-/
macro "ssprove_conseq" : tactic => `(tactic| (
  first
  | apply rHoare_conseq
  | fail "ssprove_conseq: could not apply consequence rule"
))

/-! ## Contract Tactics

Contract tactics eliminate redundant operations in SPComp programs.
They rewrite the goal using the contract lemmas from Rules.lean.
-/

/-- `ssprove_contract_get_lhs` contracts duplicate gets on the left side of a relational judgment.

This rewrites `x ← get l; y ← get l; f x y` to `x ← get l; f x x` on the left side.

Example:
```
theorem example : rHoare Φ (do let x ← SPComp.get l; let y ← SPComp.get l; f x y) c₂ Ψ := by
  ssprove_contract_get_lhs
  -- Goal is now: rHoare Φ (do let x ← SPComp.get l; f x x) c₂ Ψ
```
-/
macro "ssprove_contract_get_lhs" : tactic => `(tactic| (
  conv => arg 2; rw [contract_get]
))

/-- `ssprove_contract_get_rhs` contracts duplicate gets on the right side of a relational judgment.

This rewrites `x ← get l; y ← get l; f x y` to `x ← get l; f x x` on the right side.

Example:
```
theorem example : rHoare Φ c₁ (do let x ← SPComp.get l; let y ← SPComp.get l; f x y) Ψ := by
  ssprove_contract_get_rhs
  -- Goal is now: rHoare Φ c₁ (do let x ← SPComp.get l; f x x) Ψ
```
-/
macro "ssprove_contract_get_rhs" : tactic => `(tactic| (
  conv => arg 3; rw [contract_get]
))

/-- `ssprove_contract_put_lhs` contracts duplicate puts on the left side of a relational judgment.

This rewrites `put l v; put l v'; k` to `put l v'; k` on the left side.

Example:
```
theorem example : rHoare Φ (do SPComp.set l v; SPComp.set l v'; k) c₂ Ψ := by
  ssprove_contract_put_lhs
  -- Goal is now: rHoare Φ (do SPComp.set l v'; k) c₂ Ψ
```
-/
macro "ssprove_contract_put_lhs" : tactic => `(tactic| (
  conv => arg 2; rw [contract_put]
))

/-- `ssprove_contract_put_rhs` contracts duplicate puts on the right side of a relational judgment.

This rewrites `put l v; put l v'; k` to `put l v'; k` on the right side.

Example:
```
theorem example : rHoare Φ c₁ (do SPComp.set l v; SPComp.set l v'; k) Ψ := by
  ssprove_contract_put_rhs
  -- Goal is now: rHoare Φ c₁ (do SPComp.set l v'; k) Ψ
```
-/
macro "ssprove_contract_put_rhs" : tactic => `(tactic| (
  conv => arg 3; rw [contract_put]
))

/-- `ssprove_contract_put_get_lhs` contracts put followed by get on the left side.

This rewrites `put l v; x ← get l; f x` to `put l v; f v` on the left side.
-/
macro "ssprove_contract_put_get_lhs" : tactic => `(tactic| (
  conv => arg 2; rw [contract_put_get]
))

/-- `ssprove_contract_put_get_rhs` contracts put followed by get on the right side.

This rewrites `put l v; x ← get l; f x` to `put l v; f v` on the right side.
-/
macro "ssprove_contract_put_get_rhs" : tactic => `(tactic| (
  conv => arg 3; rw [contract_put_get]
))

/-! ## Swap Tactics

Swap tactics allow reordering independent operations in a computation.
This is useful when the order of operations on the left and right sides differ.
-/

/-- `ssprove_swap_lhs` swaps independent operations on the left side of a relational judgment.

The tactic applies `rHoare_swap_lhs` which requires proving that the two code sequences
are equal as functions from Heap. The equality is typically discharged by one of:
- `SPComp.swap_sample_sample` - for swapping two samples
- `SPComp.swap_sample_get` - for swapping sample and get
- `SPComp.swap_get_sample` - for swapping get and sample

Example:
```
theorem example : rHoare Φ (do let y ← SPComp.sample β; let x ← SPComp.sample α; f x y) c₂ Ψ := by
  ssprove_swap_lhs (SPComp.swap_sample_sample α β f)
  -- Goal is now: rHoare Φ (do let x ← SPComp.sample α; let y ← SPComp.sample β; f x y) c₂ Ψ
```
-/
macro "ssprove_swap_lhs" eq:term : tactic => `(tactic| (
  apply rHoare_swap_lhs $eq
))

/-- `ssprove_swap_rhs` swaps independent operations on the right side of a relational judgment.

The tactic applies `rHoare_swap_rhs` which requires proving that the two code sequences
are equal as functions from Heap.

Example:
```
theorem example : rHoare Φ c₁ (do let y ← SPComp.sample β; let x ← SPComp.sample α; f x y) Ψ := by
  ssprove_swap_rhs (SPComp.swap_sample_sample α β f)
  -- Goal is now: rHoare Φ c₁ (do let x ← SPComp.sample α; let y ← SPComp.sample β; f x y) Ψ
```
-/
macro "ssprove_swap_rhs" eq:term : tactic => `(tactic| (
  apply rHoare_swap_rhs $eq
))

/-- `ssprove_swap_sample_lhs` swaps two consecutive samples on the left side.

This is a convenience tactic that automatically applies the sample-sample swap lemma.
It handles the case where you have:
  `do let y ← sample β; let x ← sample α; f x y`
and want to rewrite it to:
  `do let x ← sample α; let y ← sample β; f x y`

Example:
```
theorem example : rHoare Φ (do let y ← SPComp.sample β; let x ← SPComp.sample α; f x y) c₂ Ψ := by
  ssprove_swap_sample_lhs
  -- Goal is now: rHoare Φ (do let x ← SPComp.sample α; let y ← SPComp.sample β; f x y) c₂ Ψ
```
-/
macro "ssprove_swap_sample_lhs" : tactic => `(tactic| (
  apply rHoare_swap_lhs
  intro h
  apply SPComp.swap_sample_sample
))

/-- `ssprove_swap_sample_rhs` swaps two consecutive samples on the right side.

This is a convenience tactic that automatically applies the sample-sample swap lemma.
-/
macro "ssprove_swap_sample_rhs" : tactic => `(tactic| (
  apply rHoare_swap_rhs
  intro h
  apply SPComp.swap_sample_sample
))

/-- `ssprove_swap_sample_get_lhs` swaps a sample followed by a get on the left side.

This handles the case where you have:
  `do let x ← sample α; let v ← get l; f x v`
and want to rewrite it to:
  `do let v ← get l; let x ← sample α; f x v`
-/
macro "ssprove_swap_sample_get_lhs" : tactic => `(tactic| (
  apply rHoare_swap_lhs
  intro h
  apply SPComp.swap_sample_get
))

/-- `ssprove_swap_sample_get_rhs` swaps a sample followed by a get on the right side. -/
macro "ssprove_swap_sample_get_rhs" : tactic => `(tactic| (
  apply rHoare_swap_rhs
  intro h
  apply SPComp.swap_sample_get
))

/-- `ssprove_swap_get_sample_lhs` swaps a get followed by a sample on the left side.

This handles the case where you have:
  `do let v ← get l; let x ← sample α; f v x`
and want to rewrite it to:
  `do let x ← sample α; let v ← get l; f v x`
-/
macro "ssprove_swap_get_sample_lhs" : tactic => `(tactic| (
  apply rHoare_swap_lhs
  intro h
  apply SPComp.swap_get_sample
))

/-- `ssprove_swap_get_sample_rhs` swaps a get followed by a sample on the right side. -/
macro "ssprove_swap_get_sample_rhs" : tactic => `(tactic| (
  apply rHoare_swap_rhs
  intro h
  apply SPComp.swap_get_sample
))

/-- `ssprove_swap_get_get_lhs` swaps two consecutive gets on the left side.
    Gets from different locations can be reordered. -/
macro "ssprove_swap_get_get_lhs" : tactic => `(tactic| (
  apply rHoare_swap_lhs
  intro h
  apply SPComp.swap_get_get
))

/-- `ssprove_swap_get_get_rhs` swaps two consecutive gets on the right side. -/
macro "ssprove_swap_get_get_rhs" : tactic => `(tactic| (
  apply rHoare_swap_rhs
  intro h
  apply SPComp.swap_get_get
))

/-- `ssprove_swap_set_sample_lhs` swaps a set followed by a sample on the left side. -/
macro "ssprove_swap_set_sample_lhs" : tactic => `(tactic| (
  apply rHoare_swap_lhs
  intro h
  apply SPComp.swap_set_sample
))

/-- `ssprove_swap_set_sample_rhs` swaps a set followed by a sample on the right side. -/
macro "ssprove_swap_set_sample_rhs" : tactic => `(tactic| (
  apply rHoare_swap_rhs
  intro h
  apply SPComp.swap_set_sample
))

/-- `ssprove_swap_sample_set_lhs` swaps a sample followed by a set on the left side. -/
macro "ssprove_swap_sample_set_lhs" : tactic => `(tactic| (
  apply rHoare_swap_lhs
  intro h
  apply SPComp.swap_sample_set
))

/-- `ssprove_swap_sample_set_rhs` swaps a sample followed by a set on the right side. -/
macro "ssprove_swap_sample_set_rhs" : tactic => `(tactic| (
  apply rHoare_swap_rhs
  intro h
  apply SPComp.swap_sample_set
))

/-! ## Swap Sequence Tactics

These tactics apply a sequence of swap operations in order.
They are ported from Rocq SSProve's `ssprove_swap_seq_lhs` and `ssprove_swap_seq_rhs`.
-/

/-- `ssprove_swap_seq_lhs [eq₁, eq₂, ...]` applies a sequence of swap lemmas on the left side.

Each element in the list should be a proof that swaps two operations.
The swaps are applied in order from left to right.

Example:
```
theorem example : rHoare Φ (do
    let z ← SPComp.sample γ
    let y ← SPComp.sample β
    let x ← SPComp.sample α
    f x y z) c₂ Ψ := by
  ssprove_swap_seq_lhs [SPComp.swap_sample_sample γ β _, SPComp.swap_sample_sample γ α _]
  -- Goal is now: rHoare Φ (do let x ← sample α; let y ← sample β; let z ← sample γ; f x y z) c₂ Ψ
```
-/
macro "ssprove_swap_seq_lhs" "[" eqs:term,* "]" : tactic => do
  let tacticList ← eqs.getElems.toList.mapM fun eq => `(tactic| ssprove_swap_lhs $eq)
  let tactics : Array (Lean.TSyntax `tactic) := tacticList.toArray
  `(tactic| ($[$tactics]*))

/-- `ssprove_swap_seq_rhs [eq₁, eq₂, ...]` applies a sequence of swap lemmas on the right side.

Each element in the list should be a proof that swaps two operations.
The swaps are applied in order from left to right.

Example:
```
theorem example : rHoare Φ c₁ (do
    let z ← SPComp.sample γ
    let y ← SPComp.sample β
    let x ← SPComp.sample α
    f x y z) Ψ := by
  ssprove_swap_seq_rhs [SPComp.swap_sample_sample γ β _, SPComp.swap_sample_sample γ α _]
  -- Goal is now: rHoare Φ c₁ (do let x ← sample α; let y ← sample β; let z ← sample γ; f x y z) Ψ
```
-/
macro "ssprove_swap_seq_rhs" "[" eqs:term,* "]" : tactic => do
  let tacticList ← eqs.getElems.toList.mapM fun eq => `(tactic| ssprove_swap_rhs $eq)
  let tactics : Array (Lean.TSyntax `tactic) := tacticList.toArray
  `(tactic| ($[$tactics]*))

/-- `ssprove_swap_samples_lhs n` repeatedly swaps samples on the left side `n` times.

This is useful when you have multiple samples that need to be reordered and all are
of the sample-sample type.

Example:
```
theorem example : rHoare Φ (do
    let y ← SPComp.sample β
    let x ← SPComp.sample α
    f x y) c₂ Ψ := by
  ssprove_swap_samples_lhs 1
  -- Goal is now: rHoare Φ (do let x ← sample α; let y ← sample β; f x y) c₂ Ψ
```
-/
macro "ssprove_swap_samples_lhs" n:num : tactic =>
  `(tactic| iterate $n ssprove_swap_sample_lhs)

/-- `ssprove_swap_samples_rhs n` repeatedly swaps samples on the right side `n` times. -/
macro "ssprove_swap_samples_rhs" n:num : tactic =>
  `(tactic| iterate $n ssprove_swap_sample_rhs)

/-- `ssprove_swap_auto_lhs` tries to automatically apply a single swap on the left side.

It tries each swap rule in sequence until one succeeds:
1. sample-sample swap
2. sample-get swap
3. get-sample swap
4. get-get swap
5. set-sample swap
6. sample-set swap

This tactic is useful when you don't want to specify which swap to apply.
-/
macro "ssprove_swap_auto_lhs" : tactic => `(tactic| (
  first
  | ssprove_swap_sample_lhs
  | ssprove_swap_sample_get_lhs
  | ssprove_swap_get_sample_lhs
  | ssprove_swap_get_get_lhs
  | ssprove_swap_set_sample_lhs
  | ssprove_swap_sample_set_lhs
  | fail "ssprove_swap_auto_lhs: no applicable swap rule"
))

/-- `ssprove_swap_auto_rhs` tries to automatically apply a single swap on the right side.

It tries each swap rule in sequence until one succeeds.
-/
macro "ssprove_swap_auto_rhs" : tactic => `(tactic| (
  first
  | ssprove_swap_sample_rhs
  | ssprove_swap_sample_get_rhs
  | ssprove_swap_get_sample_rhs
  | ssprove_swap_get_get_rhs
  | ssprove_swap_set_sample_rhs
  | ssprove_swap_sample_set_rhs
  | fail "ssprove_swap_auto_rhs: no applicable swap rule"
))

/-- `ssprove_swap_auto_seq_lhs n` automatically applies up to `n` swaps on the left side.

This repeatedly calls `ssprove_swap_auto_lhs` until either `n` swaps have been applied
or no more swaps are applicable.
-/
macro "ssprove_swap_auto_seq_lhs" n:num : tactic =>
  `(tactic| iterate $n (try ssprove_swap_auto_lhs))

/-- `ssprove_swap_auto_seq_rhs n` automatically applies up to `n` swaps on the right side. -/
macro "ssprove_swap_auto_seq_rhs" n:num : tactic =>
  `(tactic| iterate $n (try ssprove_swap_auto_rhs))

/-! ## One-Sided Sampling Tactics

These tactics handle random sampling on one side only, analogous to
EasyCrypt's `rnd{1}` and `rnd{2}`.
-/

/-- `ssprove_rnd_lhs` consumes a sampling operation on the left side.

When the left side starts with `sample σ >>= f`, this introduces a
universal quantifier over the sampled value and continues with `f a`.

Example:
```
-- Goal: rHoare Φ (SPComp.sample Bool >>= f) c₂ Ψ
-- After ssprove_rnd_lhs:
-- Goal: ∀ a, rHoare Φ (f a) c₂ Ψ
```
-/
macro "ssprove_rnd_lhs" : tactic => `(tactic| (
  first
  | (apply rHoare_sample_l; intro _)
  | fail "ssprove_rnd_lhs: left side does not start with sampling"
))

/-- `ssprove_rnd_rhs` consumes a sampling operation on the right side.

When the right side starts with `sample σ >>= f`, this introduces a
universal quantifier over the sampled value and continues with `f a`.

Example:
```
-- Goal: rHoare Φ c₁ (SPComp.sample Bool >>= f) Ψ
-- After ssprove_rnd_rhs:
-- Goal: ∀ a, rHoare Φ c₁ (f a) Ψ
```
-/
macro "ssprove_rnd_rhs" : tactic => `(tactic| (
  first
  | (apply rHoare_sample_r; intro _)
  | fail "ssprove_rnd_rhs: right side does not start with sampling"
))

/-! ## Combined Coupling Step Tactics

These combine bind + coupling + intro into a single tactic step.
-/

/-- `ssprove_bij_step f` applies a bijection coupling step.

When both sides of an rHoare goal sample, this combines:
1. `rHoare_bind` with the appropriate intermediate postcondition
2. `rHoare_sample_bij` with bijection `f`
3. `intro` for the sampled values

After this tactic, the goal becomes: for all `a`, prove the continuation
with the left side using `a` and the right side using `f a`.

Example:
```
-- Goal: rHoare Φ (sample Bool >>= k₁) (sample Bool >>= k₂) Ψ
ssprove_bij_step (xorBij m)
-- Goal: ∀ a, rHoare Φ (k₁ a) (k₂ (xorBij m a)) Ψ
```
-/
macro "ssprove_bij_step" f:term : tactic => `(tactic| (
  first
  | (apply rHoare_bij_step $f; intro _)
  | fail "ssprove_bij_step: could not apply bijection coupling step"
))

/-- `ssprove_same_step` applies a same-distribution coupling step.

When both sides of an rHoare goal sample from the same distribution, this
combines bind + diagonal coupling + intro.

Example:
```
-- Goal: rHoare Φ (sample Bool >>= k₁) (sample Bool >>= k₂) Ψ
ssprove_same_step
-- Goal: ∀ a, rHoare Φ (k₁ a) (k₂ a) Ψ
```
-/
macro "ssprove_same_step" : tactic => `(tactic| (
  first
  | (apply rHoare_same_step; intro _)
  | fail "ssprove_same_step: could not apply same-distribution coupling step"
))

end CatCrypt.Tactics

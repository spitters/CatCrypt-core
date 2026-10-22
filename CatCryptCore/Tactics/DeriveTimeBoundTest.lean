/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Tests for `derive_time_bound`

A DDH-style reduction and a reduction with two adversary calls, whose time theorems
`B.tree.timeBound_timed` are stated and proved by `derive_time_bound`, and a reduction with a
`let` of a function field of a structure binder applied to an argument, whose cost is charged
once.

## Main results

* `ddhRed.tree.timeBound_timed`, `twoCall.tree.timeBound_timed` and
  `letRed.tree.timeBound_timed`, emitted by the command
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundTest

open CatCrypt.Core

/-- On a DDH triple, mask `m` with `gz` and a fresh uniform `r` and call the adversary. -/
noncomputable def ddhRed {G : Type} [Fintype G] [Nonempty G] (mul : G → G → G) (m : G)
    (A : G × G × G → SPComp Bool) (gx gy gz : G) : SPComp Bool := do
  let r ← SPComp.sample G
  let b ← A (gx, gy, mul m (mul gz r))
  return !b

derive_reduction ddhRed

derive_time_bound ddhRed.tree

/-- Two calls of `A`, then one call of `B`. -/
noncomputable def twoCall (A : Bool → SPComp Bool) (B : Bool → ℕ → SPComp ℕ) : SPComp ℕ := do
  let x ← A true
  let y ← A x
  B (x && y) 3

derive_reduction twoCall

derive_time_bound twoCall.tree

/-- A structure with a function field. -/
structure Kit (W : Type) where
  /-- A data function. -/
  f : W → W

/-- A `let` of the field `deps.f` applied to `a`, used twice. -/
noncomputable def letRed {W : Type} (deps : Kit W) (a : W) (A : W × W → SPComp Bool) :
    SPComp Bool := do
  let x := deps.f a
  A (x, x)

derive_reduction letRed

derive_time_bound letRed.tree

/-- The time theorem of `letRed` charges the cost of `deps.f a` once. -/
example {W : Type} (deps : Kit W) (a : W) (A : W × W → SPTree.Timed Bool) (ACost : W × W → ℕ)
    (f : W → W) (fCost : W → ℕ) {T t c : ℕ} (hA : ∀ x, (A x).time ≤ T)
    (hAc : ∀ x, ACost x ≤ c) (hf : ∀ x, fCost x ≤ t) :
    SPTree.Timed.stepTime (letRed.tree.timed deps a A ACost f fCost) ≤ t + c + T + 2 :=
  letRed.tree.timeBound_timed deps a A ACost f fCost hA hAc hf

end CatCrypt.Tactics.DeriveTimeBoundTest

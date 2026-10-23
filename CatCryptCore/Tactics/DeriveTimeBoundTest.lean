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
once. Two reductions sample an index and pass a function of it to the adversary, at a cost
that the registered closed form of the function's cost companion makes independent of the
index: `List.replicate.timedCost_le` in `padRed`, `digits7.timedCost_eq` in `digitRed`.

## Main results

* `ddhRed.tree.timeBound_timed`, `twoCall.tree.timeBound_timed`,
  `letRed.tree.timeBound_timed`, `padRed.tree.timeBound_timed` and
  `digitRed.tree.timeBound_timed`, emitted by the command
* `digits7.timedCost_eq` — computing `t` digits costs `4 t + 1`
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

/-- Sample an index and pass `n` copies of it to the adversary. -/
noncomputable def padRed (n : ℕ) (A : List ℕ → SPComp Bool) : SPComp Bool := do
  let i ← SPComp.sample (Fin 4)
  A (List.replicate n i.val)

derive_reduction padRed

derive_time_bound padRed.tree

/-- The time theorem of `padRed` bounds the cost of `List.replicate n i` by `3 n + 1`
(`List.replicate.timedCost_le`), for every sampled index `i`. -/
example (n : ℕ) (A : List ℕ → SPTree.Timed Bool) (ACost : List ℕ → ℕ) {T c : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ c) :
    SPTree.Timed.stepTime (padRed.tree.timed n A ACost) ≤ 3 * n + c + T + 10 := by
  have := padRed.tree.timeBound_timed n A ACost hA hAc
  omega

/-- The `t` low base-7 digits of `a`. -/
def digits7 : ℕ → ℕ → List ℕ
  | 0, _ => []
  | t + 1, a => a % 7 :: digits7 t (a / 7)

derive_cost digits7

/-- Computing `t` digits costs `4 t + 1`, for every value. -/
theorem digits7.timedCost_eq (t a : ℕ) : digits7.timedCost t a = 4 * t + 1 := by
  induction t generalizing a with
  | zero => rw [digits7.timedCost]
  | succ t ih => rw [digits7.timedCost, ih]; omega

/-- Sample an index and pass its `t` low base-7 digits to the adversary. -/
noncomputable def digitRed (t : ℕ) (A : List ℕ → SPComp Bool) : SPComp Bool := do
  let i ← SPComp.sample (Fin 49)
  A (digits7 t i.val)

derive_reduction digitRed

derive_time_bound digitRed.tree

/-- The time theorem of `digitRed` charges `4 t + 1` for the digits (`digits7.timedCost_eq`),
for every sampled index. -/
example (t : ℕ) (A : List ℕ → SPTree.Timed Bool) (ACost : List ℕ → ℕ) {T c : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ c) :
    SPTree.Timed.stepTime (digitRed.tree.timed t A ACost) ≤ c + 4 * t + T + 4 :=
  digitRed.tree.timeBound_timed t A ACost hA hAc

end CatCrypt.Tactics.DeriveTimeBoundTest

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
import CatCryptCore.Tactics.DeriveTimeBound
import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.ForMathlib.ListLength
public import CatCryptCore.Tactics.StdCosts
import CatCryptCore.Tactics.DeriveCost

/-!
# Tests for `derive_time_bound`

A DDH-style reduction and a reduction with two adversary calls, whose time theorems
`B.tree.timeBound_timed` are stated and proved by `derive_time_bound`, and a reduction with a
`let` of a function field of a structure binder applied to an argument, whose cost is charged
once. Two reductions sample an index and pass a function of it to the adversary, at a cost
that the registered closed form of the function's cost companion makes independent of the
index: `List.replicate.timedCost_le` in `padRed`, `digits7.timedCost_eq` in `digitRed`. Their
majorant forms `R.tree.timeBound_timed_maj` bound the adversary's cost companion by its majorant
at the bound of the length of the list it receives (`List.length_replicate`, `digits7_length`).
A pure step over a nested state structure (`PureStep.stepRed`: a flag test, a match on the
event, and on a tick a match on the head statement whose alternatives test flags, match with a
wildcard alternative and update the state with record updates) has its time theorem proved
along its bound.

## Main results

* `ddhRed.tree.timeBound_timed`, `twoCall.tree.timeBound_timed`,
  `letRed.tree.timeBound_timed`, `padRed.tree.timeBound_timed`,
  `digitRed.tree.timeBound_timed` and `PureStep.stepRed.tree.timeBound_timed`, emitted by the
  command
* `padRed.tree.timeBound_timed_maj`, `digitRed.tree.timeBound_timed_maj`, emitted by the command
  in majorant form
* `digits7.timedCost_eq` — computing `t` digits costs `4 t + 1`
* `digits7_length` — `t` digits form a list of length `t`
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

/-- The majorant form of the time theorem of `padRed` charges the majorant of `ACost` at `n`, the
length of `List.replicate n i`, for every sampled index `i`. -/
example (n : ℕ) (A : List ℕ → SPTree.Timed Bool) (ACost : List ℕ → ℕ) {T : ℕ} {M : ℕ → ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hM : Monotone M) (hAc : ∀ x, ACost x ≤ M x.length) :
    SPTree.Timed.stepTime (padRed.tree.timed n A ACost) ≤ M n + 3 * n + T + 10 := by
  have := padRed.tree.timeBound_timed_maj n A ACost hA hM hAc
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

/-- The `t` low base-7 digits form a list of length `t`. -/
@[length_bound]
theorem digits7_length (t a : ℕ) : (digits7 t a).length = t := by
  induction t generalizing a with
  | zero => simp [digits7]
  | succ t ih => simp [digits7, ih]

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

/-- The majorant form of the time theorem of `digitRed` charges the majorant of `ACost` at `t`,
the length of the digits (`digits7_length`), for every sampled index. -/
example (t : ℕ) (A : List ℕ → SPTree.Timed Bool) (ACost : List ℕ → ℕ) {T : ℕ} {M : ℕ → ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hM : Monotone M) (hAc : ∀ x, ACost x ≤ M x.length) :
    SPTree.Timed.stepTime (digitRed.tree.timed t A ACost) ≤ M t + 4 * t + T + 4 := by
  have := digitRed.tree.timeBound_timed_maj t A ACost hA hM hAc
  omega

namespace PureStep

/-- A statement. -/
inductive Stmt where
  | skip
  | put (x : ℕ) (k : Stmt)
  | out (x : ℕ) (k : Stmt)
  | inp (x : ℕ) (k : Stmt)

/-- A configuration: the statement, its environment and a flag. -/
structure Cfg where
  /-- The statement. -/
  cur : Stmt
  /-- The environment. -/
  env : ℕ → List ℕ
  /-- A flag. -/
  got : Bool

/-- A state: the configuration, a start flag, a buffer and an input queue. -/
structure St where
  /-- The configuration. -/
  cfg : Cfg
  /-- Whether the state is started. -/
  started : Bool
  /-- The buffer. -/
  buf : List ℕ
  /-- The input queue. -/
  iq : ℕ → List ℕ

/-- An event. -/
inductive Ev where
  | inp (h v : ℕ)
  | tick

/-- One step on the event `e`. -/
def step (s : St) (e : Ev) : St × Option ℕ :=
  if s.started then
    match e with
    | .inp h v => ({ s with iq := fun i => s.iq i ++ [h + v] }, none)
    | .tick =>
      match s.cfg.cur with
      | .skip => ({ s with buf := [] }, none)
      | .put x k => ({ s with cfg := { s.cfg with cur := k, env := fun i => s.cfg.env i ++ [x] } },
          none)
      | .out x k =>
        if s.cfg.got then ({ s with cfg := { s.cfg with cur := k }, buf := s.buf ++ [x] }, some x)
        else
          match s.buf.head? with
          | some 0 => ({ s with cfg := { s.cfg with cur := k }, buf := s.buf ++ s.buf }, none)
          | _ => ({ s with cfg := { s.cfg with cur := k } }, none)
      | .inp x k =>
        match s.iq x with
        | [] => ({ s with buf := s.buf ++ [x] }, none)
        | v :: _ => ({ s with cfg := { s.cfg with cur := k, got := true }, buf := v :: s.buf },
            some v)
  else ({ s with started := true }, none)

/-- The step as a computation. -/
noncomputable def stepRed (s : St) (e : Ev) : SPComp (St × Option ℕ) :=
  SPComp.pure (step s e)

derive_reduction stepRed

derive_time_bound stepRed.tree

end PureStep

end CatCrypt.Tactics.DeriveTimeBoundTest

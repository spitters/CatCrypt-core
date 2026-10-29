/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoTime
import CatCryptCore.Core.SPTree

/-!
# Tests for a match with a wildcard arm and for the recursor of `Bool`

Minimal reductions of two shapes:

* a callee whose result holds functions and is computed by a definition by cases on a query,
  whose `reveal` branch matches a status of four constructors with one explicit arm and a
  wildcard arm (the shape of `revealFin` reached through `stepResult` in `sigImpl`). Lean
  compiles the wildcard match to a sparse `casesOn`; its costed value is the match of the
  costed values of the branches, the wildcard branch costed once;
* trees, numbers and states with function fields chosen by `Bool.rec` at a constant motive
  (the form of `Bool.or`, `Bool.and` and `Bool.not`), translated as the `if` on the major
  premise.

## Main results

* `sRed.timeBound` — the time of the costed form of `sRed`
* `bTree.timeBound` — the time of the costed form of `bTree`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedSparseRecTest

open CatCrypt.Core

/-- A session status with four constructors. -/
inductive Sts where
  | running
  | accepted (sid : ℕ)
  | rejected
  | expired

/-- A session. -/
structure SSess where
  /-- The status. -/
  status : Sts
  /-- Whether the key was revealed. -/
  revealed : Bool

/-- A game state with function fields. -/
structure SGState where
  /-- The session of each index. -/
  sessions : ℕ → Option SSess
  /-- The key of each session identifier. -/
  tbl : ℕ → ℕ

/-- A query. -/
inductive SQry where
  | reveal (k : ℕ)
  | reset
  | read (k : ℕ)

/-- The reply and next state of `reveal k`: a match on the status with a wildcard arm. -/
def revealS (g : SGState) (k : ℕ) : Option ℕ × SGState :=
  match g.sessions k with
  | some s =>
    match s.status with
    | .accepted sid =>
      (some (g.tbl sid), ⟨Function.update g.sessions k (some ⟨s.status, true⟩), g.tbl⟩)
    | _ => (none, g)
  | none => (none, g)

/-- The reply and next state of a query, by cases on the query with a wildcard answer. -/
def stepS (g : SGState) : SQry → Option ℕ → Option ℕ × SGState
  | .reveal k, _ => revealS g k
  | .reset, _ => (none, ⟨fun _ => none, g.tbl⟩)
  | .read k, _ => (some (g.tbl k), g)

/-- A callee returning the step result. -/
noncomputable def sImpl (g : SGState) (d : SQry) : SPTree (Option ℕ × SGState) :=
  .ret (stepS g d (some 0))

/-- A reduction running the callee and passing its result to a distinguisher. -/
noncomputable def sRed (g : SGState) (d : SQry) (D : Option ℕ × SGState → SPTree Bool) :
    SPTree Bool :=
  (sImpl g d).bind D

derive_timed sRed

example (g : SGState) (d : SQry) (D : Option ℕ × SGState → SPTree.Timed Bool)
    (DCost : Option ℕ × SGState → ℕ) (sessionsCost tblCost : ℕ → ℕ) :
    (sRed.timed g d D DCost sessionsCost tblCost).2.erase = sRed g d fun y => (D y).erase :=
  sRed.erase_timed g d D DCost sessionsCost tblCost

/-- The time of the costed form of `sRed`: the distinguisher, its cost, companions of the
two fields of the state and twenty steps. -/
theorem sRed.timeBound (g : SGState) (d : SQry) (D : Option ℕ × SGState → SPTree.Timed Bool)
    (DCost : Option ℕ × SGState → ℕ) (sessionsCost tblCost : ℕ → ℕ) {T a p q : ℕ}
    (hD : ∀ y, (D y).time ≤ T) (hd : ∀ y, DCost y ≤ a) (hp : ∀ x, sessionsCost x ≤ p)
    (hq : ∀ x, tblCost x ≤ q) :
    SPTree.Timed.stepTime (sRed.timed g d D DCost sessionsCost tblCost) ≤
      T + a + 2 * p + 2 * q + 20 := by
  cases d with
  | reveal k =>
    simp only [sRed.timed, sImpl.timed, SPTree.Timed.bind, SPTree.Timed.stepTime,
      SPTree.Timed.delay]
    time_bound
  | reset =>
    simp only [sRed.timed, sImpl.timed, SPTree.Timed.bind, SPTree.Timed.stepTime,
      SPTree.Timed.delay]
    time_bound
  | read k =>
    simp only [sRed.timed, sImpl.timed, SPTree.Timed.bind, SPTree.Timed.stepTime,
      SPTree.Timed.delay]
    time_bound

/-- A tree chosen by the recursor of `Bool`. -/
noncomputable def bTree (b : Bool) (x : ℕ) (D : ℕ → SPTree Bool) : SPTree Bool :=
  Bool.rec (motive := fun _ => SPTree Bool) (D x) ((SPTree.ret (x + 1)).bind D) b

derive_timed bTree

/-- The time of the costed form of `bTree`: the distinguisher, its cost and four steps. -/
theorem bTree.timeBound (b : Bool) (x : ℕ) (D : ℕ → SPTree.Timed Bool) (DCost : ℕ → ℕ)
    {T a : ℕ} (hD : ∀ y, (D y).time ≤ T) (hd : ∀ y, DCost y ≤ a) :
    SPTree.Timed.stepTime (bTree.timed b x D DCost) ≤ T + a + 4 := by
  simp only [bTree.timed, SPTree.Timed.stepTime, SPTree.Timed.delay]
  time_bound

/-- A number chosen by the recursor of `Bool`. -/
noncomputable def bData (b : Bool) (x : ℕ) (D : ℕ → SPTree Bool) : SPTree Bool :=
  (SPTree.ret (Bool.rec (motive := fun _ => ℕ) x (x * 2) b)).bind D

derive_timed bData

/-- A state with function fields chosen by the recursor of `Bool`. -/
noncomputable def bState (b : Bool) (g : SGState) (D : SGState → SPTree Bool) : SPTree Bool :=
  (SPTree.ret (Bool.rec (motive := fun _ => SGState) g ⟨fun _ => none, g.tbl⟩ b)).bind D

derive_timed bState

end CatCrypt.Tactics.DeriveTimedSparseRecTest

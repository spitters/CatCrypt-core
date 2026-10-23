/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Crypto.UCConcrete
import CatCryptCore.Core.SPTree

/-!
# Tests for a state chosen by `if` and a callee defined by cases

Minimal reductions of two shapes:

* a state structure with function fields chosen by an `if` on a handler's answer
  (`if g = 0 then s.corrupt uid else s`), returned by a tree and then read and updated (the
  shape of `pakeLazyReduction`), and the same choice after two updates through `Option.map`
  followed by a further update (the shape of `opaqueL2Reduction`): the erasure theorem is
  closed by pushing the projections through the `if`, decomposing both sides under the
  binders of the continuations and splitting the `if`s;
* a callee whose result holds functions and is computed by a definition by cases with a
  wildcard (the shape of `stepResult` reached through `finR` in `sigImpl`), whose matcher is
  compiled to the recursor of the query type: its costed value is the match of the costed
  values of the branches.

## Main results

* `iteLeakRed.timeBound` — the time of the costed form of `iteLeakRed`
* `recRed.timeBound` — the time of the costed form of `recRed`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedIteRecTest

open CatCrypt.Core CatCrypt.Crypto.UCConcrete

/-! ## A state chosen by `if` -/

/-- A state with function fields. -/
structure IState where
  /-- The password of each user. -/
  pwdFile : ℕ → Option ℕ
  /-- The corrupted users. -/
  corrupted : ℕ → Bool

/-- The state with `uid` corrupted. -/
def IState.corrupt (s : IState) (uid : ℕ) : IState :=
  ⟨s.pwdFile, Function.update s.corrupted uid true⟩

/-- Whether `uid` is corrupted. -/
def IState.isCorrupted (s : IState) (uid : ℕ) : Bool := s.corrupted uid

/-- A state chosen by an `if` on the handler's answer, read and passed to the distinguisher. -/
noncomputable def iteRed (handler : ℕ → SPTree ℕ) (uid : ℕ)
    (Z : Env (Unit × IState) ((Unit ⊕ ℕ) × IState))
    (dist : (Unit ⊕ ℕ) × IState → SPTree Bool) : SPTree Bool :=
  .load Z.heap <|
    let s := Z.input.2
    (handler uid).bind fun g =>
    let s₂ := if g = 0 then s.corrupt uid else s
    (handler g).bind fun k =>
    if s₂.isCorrupted uid then .ret false else dist (Sum.inr k, s₂)

derive_timed iteRed

/-- The state with the password of `sid` removed. -/
def IState.setStatus (s : IState) (sid : ℕ) : IState :=
  ⟨Function.update s.pwdFile sid none, s.corrupted⟩

/-- The state chosen by an `if` returned by a tree with the handler's key, then read and
updated in the output step. -/
noncomputable def iteRetRed (handler : ℕ → SPTree ℕ) (uid : ℕ)
    (Z : Env (Unit × IState) ((Unit ⊕ ℕ) × IState))
    (dist : (Unit ⊕ ℕ) × IState → SPTree Bool) : SPTree Bool :=
  .load Z.heap <|
    let s := Z.input.2
    ((handler uid).bind fun g =>
      let s₂ := if g = 0 then s.corrupt uid else s
      (handler g).bind fun k => .ret (s₂, k)).bind fun r =>
    if r.1.isCorrupted uid then .ret false else dist (Sum.inr r.2, r.1.setStatus uid)

derive_timed iteRetRed

example (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ) (uid : ℕ)
    (Z : Env (Unit × IState) ((Unit ⊕ ℕ) × IState))
    (dist : (Unit ⊕ ℕ) × IState → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × IState → ℕ)
    (inputHat : Unit × ((ℕ → Option ℕ) × (ℕ → ℕ)) × (ℕ → Bool) × (ℕ → ℕ)) :
    (iteRetRed.timed handler handlerCost uid Z dist distCost inputHat).2.erase =
      iteRetRed (fun x => (handler x).erase) uid Z (fun y => (dist y).erase) :=
  iteRetRed.erase_timed handler handlerCost uid Z dist distCost inputHat

/-- The state chosen by an `if` read before it is returned by a tree, then updated in the output
step. -/
noncomputable def iteLeakRed (handler : ℕ → SPTree ℕ) (uid : ℕ)
    (Z : Env (Unit × IState) ((Unit ⊕ ℕ) × IState))
    (dist : (Unit ⊕ ℕ) × IState → SPTree Bool) : SPTree Bool :=
  .load Z.heap <|
    let s := Z.input.2
    ((handler uid).bind fun g =>
      let s₂ := if g = 0 then s.corrupt uid else s
      (handler g).bind fun k => .ret (s₂, k, s₂.isCorrupted uid)).bind fun r =>
    if r.2.2 then .ret false else dist (Sum.inr r.2.1, r.1.setStatus uid)

derive_timed iteLeakRed

example (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ) (uid : ℕ)
    (Z : Env (Unit × IState) ((Unit ⊕ ℕ) × IState))
    (dist : (Unit ⊕ ℕ) × IState → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × IState → ℕ)
    (inputHat : Unit × ((ℕ → Option ℕ) × (ℕ → ℕ)) × (ℕ → Bool) × (ℕ → ℕ)) :
    (iteLeakRed.timed handler handlerCost uid Z dist distCost inputHat).2.erase =
      iteLeakRed (fun x => (handler x).erase) uid Z (fun y => (dist y).erase) :=
  iteLeakRed.erase_timed handler handlerCost uid Z dist distCost inputHat

/-- The time of the costed form of `iteLeakRed`: the heap reset, two handler calls, the
distinguisher, the companion of `corrupted` read from `inputHat`, and forty steps. -/
theorem iteLeakRed.timeBound (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ) (uid : ℕ)
    (Z : Env (Unit × IState) ((Unit ⊕ ℕ) × IState))
    (dist : (Unit ⊕ ℕ) × IState → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × IState → ℕ)
    (inputHat : Unit × ((ℕ → Option ℕ) × (ℕ → ℕ)) × (ℕ → Bool) × (ℕ → ℕ))
    {t c T a p : ℕ} (hH : ∀ x, (handler x).time ≤ t) (hh : ∀ x, handlerCost x ≤ c)
    (hD : ∀ y, (dist y).time ≤ T) (hd : ∀ y, distCost y ≤ a)
    (hp : ∀ x, inputHat.2.2.2 x ≤ p) :
    SPTree.Timed.stepTime (iteLeakRed.timed handler handlerCost uid Z dist distCost inputHat) ≤
      Z.heap.data.keys.card + 2 * t + 2 * c + T + a + p + 40 := by
  have key : ∀ {β : Type} (P : ℕ × SPTree.Timed β) (f : β → ℕ × SPTree.Timed Bool),
      SPTree.Timed.stepTime P ≤ 2 * t + c + p + 20 →
      (∀ x, SPTree.Timed.stepTime (f x) ≤ T + a + 8) →
      0 + (1 + Z.heap.data.keys.card + (1 + handlerCost uid + P.1 + (P.2.bind f).1 +
        (P.2.bind f).2.time)) ≤ Z.heap.data.keys.card + 2 * t + 2 * c + T + a + p + 40 := by
    intro β P f hP hf
    have hq := SPTree.Timed.stepTime_bind_le P.2 f _ hf
    have := hh uid
    simp only [SPTree.Timed.stepTime] at hq hP
    omega
  simp only [iteLeakRed.timed, SPTree.Timed.stepTime, SPTree.Timed.time_load]
  refine key _ _ ?_ (fun r => ?_)
  · refine (SPTree.Timed.stepTime_bind_le _ _ (t + c + p + 10) fun g => ?_).trans
      (by have := hH uid; omega)
    have := hp uid
    have := hH g
    have := hh g
    have assoc : ∀ a b x y : ℕ, a + (b + x) + y = a + b + x + y := fun _ _ _ _ => by omega
    by_cases hg : g = 0
    · simp only [if_pos hg, ↓reduceDIte, SPTree.Timed.stepTime]
      rw [assoc]
      refine (SPTree.Timed.prefix_bind_le _ _ _ (p + 5) fun k => ?_).trans ?_
      · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]; omega
      · omega
    · simp only [if_neg hg, SPTree.Timed.stepTime]
      rw [assoc]
      refine (SPTree.Timed.prefix_bind_le _ _ _ (p + 5) fun k => ?_).trans ?_
      · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]; omega
      · omega
  · time_bound

/-- A state whose session field holds optional records. -/
structure MState where
  /-- The password of each user. -/
  pwdFile : ℕ → Option ℕ
  /-- The record of each session. -/
  sessions : ℕ → Option ℕ
  /-- The corrupted users. -/
  corrupted : ℕ → Bool

/-- The state with a session `sid` of user `uid`. -/
def MState.addSession (s : MState) (sid uid : ℕ) : MState :=
  ⟨s.pwdFile, Function.update s.sessions sid (some uid), s.corrupted⟩

/-- The state with the record of `sid` incremented. -/
def MState.incGuess (s : MState) (sid : ℕ) : MState :=
  ⟨s.pwdFile, Function.update s.sessions sid ((s.sessions sid).map fun r => r + 1),
    s.corrupted⟩

/-- The state with the record of `sid` doubled. -/
def MState.setStatus (s : MState) (sid : ℕ) : MState :=
  ⟨s.pwdFile, Function.update s.sessions sid ((s.sessions sid).map fun r => r * 2),
    s.corrupted⟩

/-- The state with `uid` corrupted. -/
def MState.corrupt (s : MState) (uid : ℕ) : MState :=
  ⟨s.pwdFile, s.sessions, Function.update s.corrupted uid true⟩

/-- The output state chosen by an `if` on a tree's answer after two updates through
`Option.map`, then passed to the distinguisher (the shape of `opaqueL2Reduction`). -/
noncomputable def optRed (handler : ℕ → SPTree Bool) (sid uid : ℕ → ℕ) (st : ℕ → MState)
    (a : ℕ) (dist : ℕ × MState → SPTree Bool) : SPTree Bool :=
  (handler (sid a)).bind fun tr =>
    let s₁ := ((st a).addSession (sid a) (uid a)).incGuess (sid a)
    let s₂ := (if tr then s₁.setStatus (sid a) else s₁).corrupt (uid a)
    (SPTree.ret (((s₂.pwdFile (uid a)).getD 0), s₂.setStatus (sid a))).bind dist

derive_timed optRed

/-! ## A callee defined by cases -/

/-- A query. -/
inductive Qry where
  /-- Increment entry `k`. -/
  | inc (k : ℕ)
  /-- Reset the table. -/
  | reset
  /-- Read entry `k`. -/
  | read (k : ℕ)

/-- A state with a function field. -/
structure FState where
  /-- The table. -/
  tbl : ℕ → ℕ

/-- The reply and next state of `inc k`. -/
def incFin (g : FState) (k : ℕ) : ℕ × FState :=
  (g.tbl k, ⟨Function.update g.tbl k (g.tbl k + 1)⟩)

/-- The reply and next state of `reset`. -/
def resetFin (_g : FState) : ℕ × FState := (0, ⟨fun _ => 0⟩)

/-- The reply and next state of `read k`. -/
def readFin (g : FState) (k : ℕ) : ℕ × FState := (g.tbl k, g)

/-- The reply and next state of a query, by cases on the query with a wildcard answer. -/
def stepR (g : FState) : Qry → Option ℕ → ℕ × FState
  | .inc k, _ => incFin g k
  | .reset, _ => resetFin g
  | .read k, _ => readFin g k

/-- The step result with its reply incremented. -/
def finStep (g : FState) (d : Qry) (σ : Option ℕ) : ℕ × FState :=
  let x := stepR g d σ
  (x.1 + 1, x.2)

/-- A callee returning the step result. -/
noncomputable def recImpl (g : FState) (d : Qry) : SPTree (ℕ × FState) :=
  .ret (finStep g d none)

derive_timed recImpl

/-- The callee `recImpl'`, a step at the answer `some 0`, derived through its caller. -/
noncomputable def recImpl' (g : FState) (d : Qry) : SPTree (ℕ × FState) :=
  .ret (finStep g d (some 0))

/-- A reduction running the callee and passing its result to a distinguisher. -/
noncomputable def recRed (g : FState) (d : Qry) (D : ℕ × FState → SPTree Bool) : SPTree Bool :=
  (recImpl' g d).bind D

derive_timed recRed

example (g : FState) (d : Qry) (D : ℕ × FState → SPTree.Timed Bool) (DCost : ℕ × FState → ℕ)
    (tblCost : ℕ → ℕ) :
    (recRed.timed g d D DCost tblCost).2.erase = recRed g d fun y => (D y).erase :=
  recRed.erase_timed g d D DCost tblCost

/-- The time of the costed form of `recRed`: the distinguisher, its cost, four companions of
the table (the step result is read twice) and twenty steps. -/
theorem recRed.timeBound (g : FState) (d : Qry) (D : ℕ × FState → SPTree.Timed Bool)
    (DCost : ℕ × FState → ℕ) (tblCost : ℕ → ℕ) {T a p : ℕ} (hD : ∀ y, (D y).time ≤ T)
    (hd : ∀ y, DCost y ≤ a) (hp : ∀ x, tblCost x ≤ p) :
    SPTree.Timed.stepTime (recRed.timed g d D DCost tblCost) ≤ T + a + 4 * p + 20 := by
  cases d with
  | inc k =>
    have := hp k
    simp only [recRed.timed, recImpl'.timed, SPTree.Timed.bind, SPTree.Timed.stepTime,
      SPTree.Timed.delay]
    time_bound
  | reset =>
    simp only [recRed.timed, recImpl'.timed, SPTree.Timed.bind, SPTree.Timed.stepTime,
      SPTree.Timed.delay]
    time_bound
  | read k =>
    have := hp k
    simp only [recRed.timed, recImpl'.timed, SPTree.Timed.bind, SPTree.Timed.stepTime,
      SPTree.Timed.delay]
    time_bound

end CatCrypt.Tactics.DeriveTimedIteRecTest

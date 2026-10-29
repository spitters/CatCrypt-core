/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Crypto.UCConcrete

/-!
# Tests of `time_bound` on costed forms with let-bound states

A miniature of a gated prefix (three handler calls, four let-bound states with function fields,
an environment input) whose costed form, derived by `derive_timed`, binds each state and its
cost companion by `have`. `time_bound` proves the time theorems with the states kept as
let-bound locals and the companions bounded once each.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoTimeLetsTest

open CatCrypt.Core CatCrypt.Crypto.UCConcrete


/-- A state with function fields. -/
structure LSState where
  /-- The password of each user. -/
  pwd : ℕ → Option ℕ
  /-- The guess count of each session. -/
  sess : ℕ → Option ℕ
  /-- The corrupted users. -/
  corr : ℕ → Bool

/-- A new session. -/
def LSState.addS (s : LSState) (sid : ℕ) : LSState :=
  ⟨s.pwd, Function.update s.sess sid (some 0), s.corr⟩

/-- The guess count of `sid` incremented. -/
def LSState.inc (s : LSState) (sid : ℕ) : LSState :=
  ⟨s.pwd, Function.update s.sess sid ((s.sess sid).map (· + 1)), s.corr⟩

/-- The record of `sid` set to `v`. -/
def LSState.setS (s : LSState) (sid v : ℕ) : LSState :=
  ⟨s.pwd, Function.update s.sess sid ((s.sess sid).map fun _ => v), s.corr⟩

/-- The user `uid` corrupted. -/
def LSState.corrupt (s : LSState) (uid : ℕ) : LSState :=
  ⟨s.pwd, s.sess, Function.update s.corr uid true⟩

/-- Whether a guess on `sid` is honoured. -/
def lsAllowed (s : LSState) (sid : ℕ) : Bool :=
  (s.sess sid).elim false fun n => n == 0

/-- Whether a guess on `sid` for `uid` is honoured and equals the password. -/
def lsVerdict (s : LSState) (sid uid : ℕ) (g : Option ℕ) : Bool :=
  lsAllowed s sid && (match g, s.pwd uid with
    | some a, some b => decide (a = b)
    | _, _ => false)

/-- The gated prefix in miniature. -/
noncomputable def lsRed (handler : ℕ → SPTree ℕ) (hb : ℕ → SPTree Bool) (sid uid : ℕ)
    (Z : Env (Unit × LSState) ((Unit ⊕ ℕ) × LSState))
    (dist : (Unit ⊕ ℕ) × LSState → SPTree Bool) : SPTree Bool :=
  .load Z.heap <|
    (let s := Z.input.2
     let s₁ := s.addS sid
     (handler sid).bind fun g =>
     let guess : Option ℕ := if g = 0 then none else some g
     let s₂ := if guess.isSome && lsAllowed s₁ sid then s₁.inc sid else s₁
     let s₃ := if lsVerdict s₁ sid uid guess then s₂.setS sid 2
       else if guess.isSome then s₂.setS sid 1 else s₂
     (hb (if lsVerdict s₁ sid uid guess then 1 else 0)).bind fun doC =>
     let s₄ := if doC then s₃.corrupt uid else s₃
     (handler uid).bind fun k => .ret (s₄, k)).bind fun r =>
    if r.1.corr uid then .ret false else dist (Sum.inr r.2, r.1)

set_option maxHeartbeats 1000000 in
derive_timed lsRed

noncomputable def lsRed2 (handler : ℕ → SPTree ℕ) (hb : ℕ → SPTree Bool) (sid uid : ℕ)
    (Z : Env (Unit × LSState) ((Unit ⊕ ℕ) × LSState))
    (dist : (Unit ⊕ ℕ) × LSState → SPTree Bool) : SPTree Bool :=
  .load Z.heap <|
    (let s := Z.input.2
     let s₁ := s.addS sid
     (handler sid).bind fun g =>
     let guess : Option ℕ := if g = 0 then none else some g
     let s₂ := if guess.isSome && lsAllowed s₁ sid then s₁.inc sid else s₁
     let s₃ := if lsVerdict s₁ sid uid guess then s₂.setS sid 2
       else if guess.isSome then s₂.setS sid 1 else s₂
     (hb (if lsVerdict s₁ sid uid guess then 1 else 0)).bind fun doC =>
     let s₄ := if doC then s₃.corrupt uid else s₃
     (handler uid).bind fun k => .ret (s₄, k)).bind fun r =>
    if r.2 = 0 then .ret false else dist (Sum.inr r.2, r.1)

set_option maxHeartbeats 1000000 in
derive_timed lsRed2

theorem lsRed.timeBound (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ)
    (hb : ℕ → SPTree.Timed Bool) (hbCost : ℕ → ℕ) (sid uid : ℕ)
    (Z : Env (Unit × LSState) ((Unit ⊕ ℕ) × LSState))
    (dist : (Unit ⊕ ℕ) × LSState → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × LSState → ℕ)
    (inputHat : Unit × ((ℕ → Option ℕ) × (ℕ → ℕ)) × ((ℕ → Option ℕ) × (ℕ → ℕ)) ×
      (ℕ → Bool) × (ℕ → ℕ))
    {t c T a w p r : ℕ} (hH : ∀ x, (handler x).time ≤ t) (hh : ∀ x, handlerCost x ≤ c)
    (hB : ∀ x, (hb x).time ≤ t) (hbc : ∀ x, hbCost x ≤ c)
    (hD : ∀ y, (dist y).time ≤ T) (hd : ∀ y, distCost y ≤ a)
    (hw : ∀ x, inputHat.2.1.2 x ≤ w) (hp : ∀ x, inputHat.2.2.1.2 x ≤ p)
    (hr : ∀ x, inputHat.2.2.2.2 x ≤ r) :
    SPTree.Timed.stepTime (lsRed.timed handler handlerCost hb hbCost sid uid Z dist distCost
      inputHat) ≤ Z.heap.data.keys.card + 3 * t + 3 * c + T + a + 2 * w + 4 * p + r + 200 := by
  time_bound

theorem lsRed2.timeBound (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ)
    (hb : ℕ → SPTree.Timed Bool) (hbCost : ℕ → ℕ) (sid uid : ℕ)
    (Z : Env (Unit × LSState) ((Unit ⊕ ℕ) × LSState))
    (dist : (Unit ⊕ ℕ) × LSState → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × LSState → ℕ)
    (inputHat : Unit × ((ℕ → Option ℕ) × (ℕ → ℕ)) × ((ℕ → Option ℕ) × (ℕ → ℕ)) ×
      (ℕ → Bool) × (ℕ → ℕ))
    {t c T a w p r : ℕ} (hH : ∀ x, (handler x).time ≤ t) (hh : ∀ x, handlerCost x ≤ c)
    (hB : ∀ x, (hb x).time ≤ t) (hbc : ∀ x, hbCost x ≤ c)
    (hD : ∀ y, (dist y).time ≤ T) (hd : ∀ y, distCost y ≤ a)
    (hw : ∀ x, inputHat.2.1.2 x ≤ w) (hp : ∀ x, inputHat.2.2.1.2 x ≤ p)
    (hr : ∀ x, inputHat.2.2.2.2 x ≤ r) :
    SPTree.Timed.stepTime (lsRed2.timed handler handlerCost hb hbCost sid uid Z dist distCost
      inputHat) ≤ Z.heap.data.keys.card + 3 * t + 3 * c + T + a + 2 * w + 4 * p + r + 200 := by
  time_bound

end CatCrypt.Tactics.AutoTimeLetsTest

end

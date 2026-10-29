/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Crypto.KEM.FOTransformTimed

/-!
# Tests of `time_bound` on callee time theorems and of `allret_bound`

The goal shapes of the handlers of the FO transform (`FOTransformTimed`):

* a costed program followed by its lift `liftP`, bounded through the time theorem
  `liftP.timeBound_timed` of the callee from a step-prefixed bound of the program;
* one query of `simImplFO.timed`, whose answer costs `Sum.rec (fun _ => 0) (fun _ => 0) r` and
  whose calls of `simImpl.timed` are bounded by `simImpl.timeBound` and
  `simImpl.isQueryBound_erase`;
* the leaf invariants of `simImpl.timed` and `simImplFO.timed`: the table companions of the
  returned states exceed the bound of those received by at most `3`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.FOTransform

open OracleAdv.Timed

variable {PK M C R K : Type} [Nonempty R] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype K] [Nonempty K]

omit [Nonempty R] [Nonempty M] [DecidableEq M] [DecidableEq C] in
example {β γ : Type} (X : ℕ × OracleAdv.Timed (M × C) Bool β)
    (f : β → ℕ × OracleAdv.Timed (M ⊕ (M × C)) (R ⊕ Bool) γ) {N q : ℕ}
    (hX : StepTimeBound X N) (hq : X.2.erase.IsQueryBound q) (hf : ∀ x, StepTimeBound (f x) 2) :
    StepTimeBound (delay 1 (delay (2 + X.1 + (liftP.timed (R := R) X.2).1)
      ((liftP.timed (R := R) X.2).2.bind f))) (N + q + 5) := by
  time_bound

omit [Nonempty M] in
example (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (m : M) (LDCost : C → ℕ) (LQCost : M × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) :
    StepTimeBound (simImplFO.timed (R := R) cstar kstar st (.inl (.inl m)) LDCost LQCost)
      (2 * b + 19) := by
  time_bound

omit [Nonempty M] in
example (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (d : (M ⊕ (M × C)) ⊕ C) (LDCost : C → ℕ) (LQCost : M × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) :
    StepTimeBound (simImplFO.timed (R := R) cstar kstar st d LDCost LQCost) (2 * b + 19) := by
  rcases d with (m | q) | c
  · time_bound
  · time_bound
  · time_bound

omit [Nonempty M] in
example (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (d : (M × C) ⊕ C) (LDCost : C → ℕ) (LQCost : M × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) :
    AllRet (fun y => (∀ x, y.2.1.2 x ≤ b + 3) ∧ (∀ x, y.2.2.1.2 x ≤ b + 3))
      (FOTransformU.simImpl.timed cstar kstar st d LDCost LQCost).2 := by
  allret_bound

omit [Nonempty M] in
example (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (d : (M ⊕ (M × C)) ⊕ C) (LDCost : C → ℕ) (LQCost : M × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) :
    AllRet (fun y => (∀ x, y.2.1.2 x ≤ b + 3) ∧ (∀ x, y.2.2.1.2 x ≤ b + 3))
      (simImplFO.timed (R := R) cstar kstar st d LDCost LQCost).2 := by
  allret_bound

end CatCrypt.Crypto.KEM.FOTransform

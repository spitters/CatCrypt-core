/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Complexity.TimeBoundCharge

/-!
# Tests of the charge bounds read by the fold rule

The fold rule (`time_fold`) reads PolyFun's charge bound `FreeM.IsChargeBound` of the image of a
costed tree (`FreeM.IsChargeBoundUnder` along `spAllows` for `SPTree`) through the records
registered in `CatCryptCore.Complexity.TimeBoundCharge`, in both directions: a charge bound in
the context is a time bound, and a charge-bound goal is proved as a time bound.

* costed oracle adversaries: a time bound from a charge bound, a charge bound from a time bound,
  and the charge bound of a step-prefixed adversary that binds into a binder adversary bounded by
  charge bounds;
* costed `SPTree`s: the same with `IsChargeBoundUnder` along `spAllows`;
* costed oracle programs: both directions, with the record of the vector charge in scope.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.TimeBoundChargeTest

open CatCrypt.Core CatCrypt.Crypto PFunctor PFunctor.FreeM

/-! ## Costed oracle adversaries -/

example (A : OracleAdv.Timed ℕ Bool Bool) (T : ℕ)
    (hA : (OracleAdv.Timed.toFreeMT A).IsChargeBound OracleAdv.Timed.tickCost T) :
    A.TimeBound T := by
  time_fold

example (A : OracleAdv.Timed ℕ Bool Bool) (T : ℕ) (hA : A.TimeBound T) :
    (OracleAdv.Timed.toFreeMT A).IsChargeBound OracleAdv.Timed.tickCost T := by
  time_fold

/-- Query `x`, charging `aCost` at the answer, then run the binder adversary `A` and return the
conjunction of its bit with the answer. -/
def oaBind (A : ℕ → OracleAdv.Timed ℕ Bool Bool) (aCost : Bool → ℕ) (x : ℕ) :
    ℕ × OracleAdv.Timed ℕ Bool Bool :=
  (2, .query x (fun r => aCost r + ((A x).bind fun b => (1, .ret (b && r))).1)
    fun r => ((A x).bind fun b => (1, .ret (b && r))).2)

example (A : ℕ → OracleAdv.Timed ℕ Bool Bool) (aCost : Bool → ℕ) (x : ℕ) {T t : ℕ}
    (hA : ∀ a, (OracleAdv.Timed.toFreeMT (A a)).IsChargeBound OracleAdv.Timed.tickCost T)
    (ha : ∀ r, aCost r ≤ t) :
    (OracleAdv.Timed.stepToFreeMT (oaBind A aCost x)).IsChargeBound OracleAdv.Timed.tickCost
      (T + t + 4) := by
  time_fold

/-! ## Costed `SPTree`s -/

example (s : SPTree.Timed ℕ) (T : ℕ)
    (hs : (SPTree.Timed.toFreeMT s).IsChargeBoundUnder SPTree.tickCost SPTree.spAllows T) :
    s.TimeBound T := by
  time_fold

example (s : SPTree.Timed ℕ) (T : ℕ) (hs : s.TimeBound T) :
    (SPTree.Timed.toFreeMT s).IsChargeBoundUnder SPTree.tickCost SPTree.spAllows T := by
  time_fold

/-- Sample a bit; on heads run the binder tree `A` at it and charge `gCost` at its result. -/
noncomputable def spBind (A : Bool → SPTree.Timed ℕ) (gCost : ℕ → ℕ) : SPTree.Timed ℕ :=
  .sample Bool inferInstance ⟨true⟩
    (fun b => (if b then (A b).bind fun n => (gCost n, .ret n) else (0, .ret 0)).1)
    fun b => (if b then (A b).bind fun n => (gCost n, .ret n) else (0, .ret 0)).2

example (A : Bool → SPTree.Timed ℕ) (gCost : ℕ → ℕ) {T t : ℕ}
    (hA : ∀ b,
      (SPTree.Timed.toFreeMT (A b)).IsChargeBoundUnder SPTree.tickCost SPTree.spAllows T)
    (hg : ∀ n, gCost n ≤ t) :
    (SPTree.Timed.toFreeMT (spBind A gCost)).IsChargeBoundUnder SPTree.tickCost
      SPTree.spAllows (T + t + 1) := by
  time_fold

/-! ## Costed oracle programs -/

example (p : OracleProg.Timed ℕ Bool Bool) (T : ℕ)
    (hp : (OracleProg.Timed.toFreeMT p).IsChargeBound OracleProg.tickCost T) :
    p.TimeBound T := by
  time_fold

example (p : OracleProg.Timed ℕ Bool Bool) (T : ℕ) (hp : p.TimeBound T) :
    (OracleProg.Timed.toFreeMT p).IsChargeBound OracleProg.tickCost T := by
  time_fold

end CatCrypt.Complexity.TimeBoundChargeTest

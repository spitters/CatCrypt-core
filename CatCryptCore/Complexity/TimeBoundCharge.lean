/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Crypto.Signatures.OracleProgTimedFree
public import CatCryptCore.Quantum.QTreeKindFree
public import CatCryptCore.Quantum.QROM.QAdvTreeKindFree

/-!
# Time bounds of the tree kinds as charge bounds

Each tree kind with a time certificate has a ticked image, a tree of a polynomial functor with a
tick node after every direction, and a structural time bound. This module states, for each kind,
that the structural time bound is PolyFun's charge bound `FreeM.IsChargeBound` of the ticked
image under the kind's charge `tickCost`. For `SPTree` the charge bound is taken along the answers
that `spAllows` admits (`FreeM.IsChargeBoundUnder`), since its sampling nodes over a distribution
quantify over the support only. The laws of `IsChargeBound` (`bind`, `mono`, `liftM`, `mapLens`,
`isChargeBound_prod_iff`) apply to every time bound through these equivalences.

## Main results

* `PFunctor.FreeM.isChargeBound_nat_iff_sub` — a natural-number charge bound with `s` spent is
  `s ≤ B` and the charge bound of budget `B - s` from nothing spent
* `CatCrypt.Crypto.OracleAdv.Timed.timeBound_iff_isChargeBound`,
  `CatCrypt.Crypto.OracleAdv.Timed.stepTimeBound_iff_isChargeBound` — costed oracle adversaries
* `CatCrypt.Crypto.OracleProg.Timed.timeBound_iff_isChargeBound`,
  `CatCrypt.Crypto.OracleProg.Timed.stepTimeBound_iff_isChargeBound` — costed oracle programs
* `CatCrypt.Core.SPTree.Timed.timeBound_iff_isChargeBoundUnder`,
  `CatCrypt.Core.SPTree.Timed.le_and_timeBound_iff_isChargeBoundUnder` — costed `SPTree`s
* `CatCrypt.Quantum.ReactiveUC.QInstrT.timeBound_iff_isChargeBound`,
  `CatCrypt.Quantum.ReactiveUC.QInstrT.stepTimeBound_iff_isChargeBound` — costed instruments
* `CatCrypt.Quantum.QROM.QAdvT.timeBound_iff_isChargeBound`,
  `CatCrypt.Quantum.QROM.QAdvT.stepTimeBound_iff_isChargeBound`,
  `CatCrypt.Quantum.QROM.QAdvMRT.timeBound_iff_isChargeBound`,
  `CatCrypt.Quantum.QROM.QAdvMRT.stepTimeBound_iff_isChargeBound` — costed circuits
-/

@[expose] public section

namespace PFunctor.FreeM

variable {P : PFunctor} {α : Type*}

/-- A natural-number charge bound with `s` spent is `s ≤ B` and the charge bound of budget
`B - s` from nothing spent. -/
theorem isChargeBound_nat_iff_sub (x : FreeM P α) (c : P.A → ℕ) (B s : ℕ) :
    x.IsChargeBound c B s ↔ s ≤ B ∧ x.IsChargeBound c (B - s) := by
  rw [isChargeBound_iff_isRollBound_orderedSub, isChargeBound_iff_isRollBound_nat]

end PFunctor.FreeM

open PFunctor

namespace CatCrypt.Crypto.OracleAdv.Timed

variable {D R α : Type}

/-- The time bound of a costed adversary is the charge bound `n` of its tick tree. -/
theorem timeBound_iff_isChargeBound (A : Timed D R α) (n : ℕ) :
    A.TimeBound n ↔ (toFreeMT A).IsChargeBound tickCost n :=
  (timeBound_iff_isRollBound A n).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

/-- The step time bound of a step-prefixed costed adversary is the charge bound `n` of its tick
tree. -/
theorem stepTimeBound_iff_isChargeBound (x : ℕ × Timed D R α) (n : ℕ) :
    StepTimeBound x n ↔ (stepToFreeMT x).IsChargeBound tickCost n := by
  rw [stepTimeBound_iff_wpFold_chargeUnder, OpSpec.chargeUnder_true,
    ← FreeM.isRollBound_iff_wpFold_charge, FreeM.isChargeBound_iff_isRollBound_nat]

end CatCrypt.Crypto.OracleAdv.Timed

namespace CatCrypt.Crypto.OracleProg.Timed

variable {I O α : Type}

/-- The time bound of a costed oracle program is the charge bound `n` of its tick tree. -/
theorem timeBound_iff_isChargeBound (p : Timed I O α) (n : ℕ) :
    p.TimeBound n ↔ (toFreeMT p).IsChargeBound tickCost n :=
  (timeBound_iff_isRollBound p n).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

/-- The step time bound of a step-prefixed costed oracle program is the charge bound `n` of its
tick tree. -/
theorem stepTimeBound_iff_isChargeBound (x : ℕ × Timed I O α) (n : ℕ) :
    StepTimeBound x n ↔ (stepToFreeMT x).IsChargeBound tickCost n :=
  (stepTimeBound_iff_isRollBound x n).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

end CatCrypt.Crypto.OracleProg.Timed

namespace CatCrypt.Core.SPTree.Timed

variable {α : Type}

/-- The time bound of a costed `SPTree` is the charge bound `t` of its tick tree along the
answers that `spAllows` admits. -/
theorem timeBound_iff_isChargeBoundUnder (s : SPTree.Timed α) (t : ℕ) :
    s.TimeBound t ↔ (toFreeMT s).IsChargeBoundUnder tickCost spAllows t := by
  rw [timeBound_iff_wpFold_charge_restrict, FreeM.isChargeBoundUnder_iff_restrict]
  exact ((FreeM.isChargeBound_iff_isRollBound_nat _ _ _).trans
    (FreeM.isRollBound_iff_wpFold_charge _ _ _)).symm

/-- The step cost followed by a time bound on the tree is the charge bound `n` of the
step-prefixed tick tree along the answers that `spAllows` admits. -/
theorem le_and_timeBound_iff_isChargeBoundUnder (x : ℕ × SPTree.Timed α) (n : ℕ) :
    (x.1 ≤ n ∧ x.2.TimeBound (n - x.1)) ↔
      (stepToFreeMT x).IsChargeBoundUnder tickCost spAllows n := by
  rw [le_and_timeBound_iff_wpFold_charge_restrict, FreeM.isChargeBoundUnder_iff_restrict]
  exact ((FreeM.isChargeBound_iff_isRollBound_nat _ _ _).trans
    (FreeM.isRollBound_iff_wpFold_charge _ _ _)).symm

end CatCrypt.Core.SPTree.Timed

namespace CatCrypt.Quantum.ReactiveUC.QInstrT

open CatCrypt.Crypto.Party

variable {A : Type} [Fintype A] {α : Type} {B : α → Type} [∀ a, Fintype (B a)]

/-- The time bound of a costed instrument is the charge bound `n` of its tick tree. -/
theorem timeBound_iff_isChargeBound (x : QInstrT A α B) (n : ℕ) :
    ProgE.Bound Costed.weight x.toTree n (fun _ => True) ↔
      (toFreeMT x).IsChargeBound tickCost n :=
  (timeBound_iff_isRollBound x n).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

/-- The step time bound of a step-prefixed costed instrument is the charge bound `n` of its tick
tree. -/
theorem stepTimeBound_iff_isChargeBound (x : ℕ × QInstrT A α B) (n : ℕ) :
    StepTimeBound x n ↔ (stepToFreeMT x).IsChargeBound tickCost n :=
  (stepTimeBound_iff_isRollBound x n).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

end CatCrypt.Quantum.ReactiveUC.QInstrT

namespace CatCrypt.Quantum.QROM.QAdvT

variable {m n w q : ℕ}

/-- The time bound of a costed circuit is the charge bound `T` of its tick tree under the
weight of its gate set. -/
theorem timeBound_iff_isChargeBound (A : QAdvT m n w q) (T : ℕ) :
    A.time ≤ T ↔ (toFreeMT A).IsChargeBound (CircOp.tickCost A.S.weight) T :=
  (timeBound_iff_isRollBound A T).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

/-- The step time bound of a step-prefixed costed circuit is the charge bound `T` of its tick
tree under the weight of its gate set. -/
theorem stepTimeBound_iff_isChargeBound (x : ℕ × QAdvT m n w q) (T : ℕ) :
    StepTimeBound x T ↔ (stepToFreeMT x).IsChargeBound (CircOp.tickCost x.2.S.weight) T :=
  (stepTimeBound_iff_isRollBound x T).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

end CatCrypt.Quantum.QROM.QAdvT

namespace CatCrypt.Quantum.QROM.QAdvMRT

variable {m n w q k c a : ℕ}

/-- The time bound of a costed multi-round circuit is the charge bound `T` of its tick tree under
the weight of its gate set. -/
theorem timeBound_iff_isChargeBound (A : QAdvMRT m n w q k c a) (T : ℕ) :
    A.time ≤ T ↔ (toFreeMT A).IsChargeBound (CircOp.tickCost A.S.weight) T :=
  (timeBound_iff_isRollBound A T).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

/-- The step time bound of a step-prefixed costed multi-round circuit is the charge bound `T` of
its tick tree under the weight of its gate set. -/
theorem stepTimeBound_iff_isChargeBound (x : ℕ × QAdvMRT m n w q k c a) (T : ℕ) :
    StepTimeBound x T ↔ (stepToFreeMT x).IsChargeBound (CircOp.tickCost x.2.S.weight) T :=
  (stepTimeBound_iff_isRollBound x T).trans (FreeM.isChargeBound_iff_isRollBound_nat _ _ _).symm

end CatCrypt.Quantum.QROM.QAdvMRT

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QAdvTreeKind
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Container.CodeCost

/-!
# Costed QROM circuits as free monads with tick nodes

A costed circuit of the circuit tree kinds is a straight-line program: the gates of the word of
each unitary, an oracle call between two unitaries of a segment, and, in a multi-round circuit,
a classical round between two segments. Its image in the free monad of the signature
`CircSigT G R = CircSig G R + SPTree.TickSig` has a node `gate g` for each gate `g : G`, a node
`oracle` for each oracle call and a node `round r` for each classical round `r : R`, each with
one direction; the tick positions `tick n` charge `n` units. The charge `CircOp.tickCost wt` is
the weight `wt g` at a gate, one unit at an oracle call and at a round, and `n` at `tick n`. A
step-prefixed costed circuit `(c, A)` has the image of `A` behind the tick `c`.

The time `QAdvT.time` and `QAdvMRT.time` of a costed circuit is the charge fold of its image,
so that the time bounds and the step time bounds `StepTimeBound` of the two kinds are PolyFun's
subtractive roll bound and the bound on the worst-case charge fold of these images.

Search words: quantum circuit tree kind, costed circuit, QROM adversary, free monad, tick node,
roll bound, charge fold, budget.

## Main definitions

* `CircOp`, `CircSig`, `CircSigT`, `CircOp.tickCost` — the operations of a circuit, the
  signatures and the charge
* `CircOp.word`, `CircOp.segs`, `CircOp.rounds` — the trees of a word of gates, of a segment
  and of a multi-round chain of segments
* `QAdvT.toFreeMT`, `QAdvT.stepToFreeMT`, `QAdvMRT.toFreeMT`, `QAdvMRT.stepToFreeMT` — the tick
  trees of costed circuits

## Main results

* `QAdvT.cost_toFreeMT`, `QAdvMRT.cost_toFreeMT` — the time is the charge fold of the tick tree
* `QAdvT.timeBound_iff_wpFold_charge`, `QAdvT.timeBound_iff_isRollBound`,
  `QAdvT.stepTimeBound_iff_wpFold_charge`, `QAdvT.stepTimeBound_iff_isRollBound` — the time
  bound and the step time bound of a costed circuit are the charge-fold bound and the roll bound
  of its tick tree
* `QAdvMRT.timeBound_iff_wpFold_charge`, `QAdvMRT.timeBound_iff_isRollBound`,
  `QAdvMRT.stepTimeBound_iff_wpFold_charge`, `QAdvMRT.stepTimeBound_iff_isRollBound` — the same
  for multi-round circuits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open PFunctor PFunctor.FreeM CatCrypt.Container CatCrypt.Core CatCrypt.Complexity.HandlerCost

namespace CatCrypt.Quantum.QROM

/-- The operations of a costed circuit: a gate `g`, an oracle call, a classical round `r`. -/
inductive CircOp (G R : Type) : Type where
  /-- Apply the gate `g`. -/
  | gate (g : G)
  /-- Call the oracle. -/
  | oracle
  /-- Run the classical round `r`. -/
  | round (r : R)

/-- The polynomial functor of circuit operations, each with one direction. -/
abbrev CircSig (G R : Type) : PFunctor.{0, 0} := ⟨CircOp G R, fun _ => PUnit⟩

/-- The polynomial functor of costed circuits: `CircSig G R` with tick positions. -/
abbrev CircSigT (G R : Type) : PFunctor.{0, 0} := CircSig G R + SPTree.TickSig

/-- Every position of `CircSigT G R` has a direction. -/
instance CircSigT.nonempty_B {G R : Type} (a : (CircSigT G R).A) :
    Nonempty ((CircSigT G R).B a) := by
  rcases a with a | a <;> exact ⟨PUnit.unit⟩

namespace CircOp

variable {G R : Type}

/-- The charge of a position of `CircSigT G R`: the weight `wt g` at a gate, one unit at an
oracle call and at a round, `n` at `tick n`. -/
def tickCost (wt : G → ℕ) : (CircSigT G R).A → ℕ
  | .inl (.gate g) => wt g
  | .inl .oracle => 1
  | .inl (.round _) => 1
  | .inr n => n

/-- The word of gates `l` followed by the tree `k`. -/
def word {β : Type} : List G → FreeM (CircSigT G R) β → FreeM (CircSigT G R) β
  | [], k => k
  | g :: l, k => .liftBind (P := CircSigT G R) (.inl (.gate g)) fun _ => word l k

/-- The segment of the words `W 0, …, W q` separated by oracle calls, followed by the tree
`k`. -/
def segs {β : Type} : (q : ℕ) → (Fin (q + 1) → List G) → FreeM (CircSigT G R) β →
    FreeM (CircSigT G R) β
  | 0, W, k => word (W 0) k
  | q + 1, W, k => word (W 0) <| .liftBind (P := CircSigT G R) (.inl .oracle) fun _ =>
      segs q (fun j => W j.succ) k

/-- The segments `seg 0, …, seg k`, each of `q` oracle calls, separated by the classical rounds
`r 0, …, r (k - 1)`. -/
def rounds (q : ℕ) : (k : ℕ) → (Fin (k + 1) → Fin (q + 1) → List G) → (Fin k → R) →
    FreeM (CircSigT G R) Unit
  | 0, seg, _ => segs q (seg 0) (.pure ())
  | k + 1, seg, r => segs q (seg 0) <| .liftBind (P := CircSigT G R) (.inl (.round (r 0)))
      fun _ => rounds q k (fun i => seg i.succ) (fun i => r i.succ)

/-- The charge fold of a word is the sum of the weights of its gates plus the charge fold of
the continuation. -/
theorem cost_word (wt : G → ℕ) {β : Type} (l : List G) (k : FreeM (CircSigT G R) β) :
    cost (tickCost wt) (word l k) = ((l.map wt).sum : ℕ) + cost (tickCost wt) k := by
  induction l with
  | nil => simp [word]
  | cons g l ih =>
    rw [word, cost_liftBind, ciSup_const, ih]
    simp only [tickCost, List.map_cons, List.sum_cons, Nat.cast_add, add_assoc]

/-- The charge fold of a segment is the sum of the weights of its words plus one unit per
oracle call plus the charge fold of the continuation. -/
theorem cost_segs (wt : G → ℕ) {β : Type} (q : ℕ) (W : Fin (q + 1) → List G)
    (k : FreeM (CircSigT G R) β) :
    cost (tickCost wt) (segs q W k) =
      ((∑ j, ((W j).map wt).sum + q : ℕ) : ℕ∞) + cost (tickCost wt) k := by
  induction q generalizing k with
  | zero => rw [segs, cost_word]; simp
  | succ q ih =>
    rw [segs, cost_word, cost_liftBind, ciSup_const, ih]
    simp only [tickCost, Fin.sum_univ_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- The charge fold of a multi-round chain is the sum of the weights of its words plus one unit
per oracle call and one unit per round. -/
theorem cost_rounds (wt : G → ℕ) (q k : ℕ) (seg : Fin (k + 1) → Fin (q + 1) → List G)
    (r : Fin k → R) :
    cost (tickCost wt) (rounds q k seg r) =
      ((∑ i, ∑ j, ((seg i j).map wt).sum + (k + 1) * q + k : ℕ) : ℕ∞) := by
  induction k with
  | zero => rw [rounds, cost_segs, cost_pure]; simp
  | succ k ih =>
    rw [rounds, cost_segs, cost_liftBind, ciSup_const, ih]
    simp only [tickCost, Fin.sum_univ_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    ring

end CircOp

/-! ## Costed single-run circuits -/

namespace QAdvT

variable {m n w q : ℕ}

/-- The costed circuit `A` as a tree of `CircSigT A.S.G Empty`: its segment of words and oracle
calls. -/
def toFreeMT (A : QAdvT m n w q) : FreeM (CircSigT A.S.G Empty) Unit :=
  CircOp.segs q A.circ.gates (.pure ())

/-- The step-prefixed costed circuit `(c, A)` as a tree: the tick `c` followed by the tick tree
of `A`. -/
def stepToFreeMT (x : ℕ × QAdvT m n w q) : FreeM (CircSigT x.2.S.G Empty) Unit :=
  .liftBind (P := CircSigT x.2.S.G Empty) (.inr x.1) fun _ => toFreeMT x.2

/-- The time of a costed circuit is the charge fold of its tick tree. -/
theorem cost_toFreeMT (A : QAdvT m n w q) :
    cost (CircOp.tickCost A.S.weight) (toFreeMT A) = A.time := by
  rw [toFreeMT, CircOp.cost_segs, cost_pure, add_zero, Nat.cast_inj]
  simp [time, QAdv.Timed.time, QAdv.Timed.gateTime, GateSet.cost]

/-- The time bound of a costed circuit is the bound `T` on the worst-case charge fold of its
tick tree. -/
theorem timeBound_iff_wpFold_charge (A : QAdvT m n w q) (T : ℕ) :
    A.time ≤ T ↔
      FreeM.wpFold (OpSpec.charge fun a => ((CircOp.tickCost A.S.weight a : ℕ) : ℕ∞))
        (toFreeMT A) (fun _ => 0) ≤ T := by
  change _ ↔ cost (CircOp.tickCost A.S.weight) (toFreeMT A) ≤ T
  rw [cost_toFreeMT, Nat.cast_le]

/-- The time bound of a costed circuit is the subtractive roll bound with charge
`CircOp.tickCost` on its tick tree. -/
theorem timeBound_iff_isRollBound (A : QAdvT m n w q) (T : ℕ) :
    A.time ≤ T ↔
      (toFreeMT A).IsRollBound T (fun a b => CircOp.tickCost A.S.weight a ≤ b)
        (fun a b => b - CircOp.tickCost A.S.weight a) := by
  rw [timeBound_iff_wpFold_charge, FreeM.isRollBound_iff_wpFold_charge]

/-- The step time bound of a step-prefixed costed circuit is the bound `T` on the worst-case
charge fold of its tick tree. -/
theorem stepTimeBound_iff_wpFold_charge (x : ℕ × QAdvT m n w q) (T : ℕ) :
    StepTimeBound x T ↔
      FreeM.wpFold (OpSpec.charge fun a => ((CircOp.tickCost x.2.S.weight a : ℕ) : ℕ∞))
        (stepToFreeMT x) (fun _ => 0) ≤ T := by
  change _ ↔ cost (CircOp.tickCost x.2.S.weight) (stepToFreeMT x) ≤ T
  rw [stepToFreeMT, cost_liftBind, ciSup_const, cost_toFreeMT]
  simp only [CircOp.tickCost, StepTimeBound]
  norm_cast

/-- The step time bound of a step-prefixed costed circuit is the subtractive roll bound with
charge `CircOp.tickCost` on its tick tree. -/
theorem stepTimeBound_iff_isRollBound (x : ℕ × QAdvT m n w q) (T : ℕ) :
    StepTimeBound x T ↔
      (stepToFreeMT x).IsRollBound T (fun a b => CircOp.tickCost x.2.S.weight a ≤ b)
        (fun a b => b - CircOp.tickCost x.2.S.weight a) := by
  rw [stepTimeBound_iff_wpFold_charge, FreeM.isRollBound_iff_wpFold_charge]

end QAdvT

/-! ## Costed multi-round circuits -/

namespace QAdvMRT

variable {m n w q k c a : ℕ}

/-- The costed multi-round circuit `A` as a tree of `CircSigT A.S.G (ClassicalRound _ c a)`:
its segments separated by its classical rounds. -/
def toFreeMT (A : QAdvMRT m n w q k c a) :
    FreeM (CircSigT A.S.G (ClassicalRound (m * n * w) c a)) Unit :=
  CircOp.rounds q k A.seg A.rounds

/-- The step-prefixed costed multi-round circuit `(c', A)` as a tree: the tick `c'` followed by
the tick tree of `A`. -/
def stepToFreeMT (x : ℕ × QAdvMRT m n w q k c a) :
    FreeM (CircSigT x.2.S.G (ClassicalRound (m * n * w) c a)) Unit :=
  .liftBind (P := CircSigT x.2.S.G (ClassicalRound (m * n * w) c a)) (.inr x.1) fun _ =>
    toFreeMT x.2

/-- The time of a costed multi-round circuit is the charge fold of its tick tree. -/
theorem cost_toFreeMT (A : QAdvMRT m n w q k c a) :
    cost (CircOp.tickCost A.S.weight) (toFreeMT A) = A.time := by
  rw [toFreeMT, CircOp.cost_rounds, Nat.cast_inj]
  simp [time, GateSet.cost]

/-- The time bound of a costed multi-round circuit is the bound `T` on the worst-case charge
fold of its tick tree. -/
theorem timeBound_iff_wpFold_charge (A : QAdvMRT m n w q k c a) (T : ℕ) :
    A.time ≤ T ↔
      FreeM.wpFold (OpSpec.charge fun a => ((CircOp.tickCost A.S.weight a : ℕ) : ℕ∞))
        (toFreeMT A) (fun _ => 0) ≤ T := by
  change _ ↔ cost (CircOp.tickCost A.S.weight) (toFreeMT A) ≤ T
  rw [cost_toFreeMT, Nat.cast_le]

/-- The time bound of a costed multi-round circuit is the subtractive roll bound with charge
`CircOp.tickCost` on its tick tree. -/
theorem timeBound_iff_isRollBound (A : QAdvMRT m n w q k c a) (T : ℕ) :
    A.time ≤ T ↔
      (toFreeMT A).IsRollBound T (fun a b => CircOp.tickCost A.S.weight a ≤ b)
        (fun a b => b - CircOp.tickCost A.S.weight a) := by
  rw [timeBound_iff_wpFold_charge, FreeM.isRollBound_iff_wpFold_charge]

/-- The step time bound of a step-prefixed costed multi-round circuit is the bound `T` on the
worst-case charge fold of its tick tree. -/
theorem stepTimeBound_iff_wpFold_charge (x : ℕ × QAdvMRT m n w q k c a) (T : ℕ) :
    StepTimeBound x T ↔
      FreeM.wpFold (OpSpec.charge fun a => ((CircOp.tickCost x.2.S.weight a : ℕ) : ℕ∞))
        (stepToFreeMT x) (fun _ => 0) ≤ T := by
  change _ ↔ cost (CircOp.tickCost x.2.S.weight) (stepToFreeMT x) ≤ T
  rw [stepToFreeMT, cost_liftBind, ciSup_const, cost_toFreeMT]
  simp only [CircOp.tickCost, StepTimeBound]
  norm_cast

/-- The step time bound of a step-prefixed costed multi-round circuit is the subtractive roll
bound with charge `CircOp.tickCost` on its tick tree. -/
theorem stepTimeBound_iff_isRollBound (x : ℕ × QAdvMRT m n w q k c a) (T : ℕ) :
    StepTimeBound x T ↔
      (stepToFreeMT x).IsRollBound T (fun a b => CircOp.tickCost x.2.S.weight a ≤ b)
        (fun a b => b - CircOp.tickCost x.2.S.weight a) := by
  rw [stepTimeBound_iff_wpFold_charge, FreeM.isRollBound_iff_wpFold_charge]

end QAdvMRT

end CatCrypt.Quantum.QROM

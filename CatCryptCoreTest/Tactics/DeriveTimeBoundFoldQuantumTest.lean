/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Quantum.QTreeKindFree
public import CatCryptCore.Quantum.QROM.QAdvTreeKindFree

/-!
# Tests of the fold rule of `derive_time_bound` on the quantum kinds

Fresh costed trees of the kinds `QInstrT`, `QAdvT` and `QAdvMRT`, bounded by the fold rule:

* `qBind.timed`: the bind `QInstrT.bind` of two binder instruments behind `placeLeft`, by
  `derive_time_bound`; the placement enters through its law
  (`QInstrT.wpFold_toFreeMT_placeLeft_le`) and the bind through `QInstrT.wpFold_stepToFreeMT_bind`;
* `qAbs.timed`: the oracle absorption `QAdvT.absorb` of a binder circuit with step cost
  `f x + 3`, by `derive_time_bound`; the absorption enters through its law
  (`QAdvT.wpFold_toFreeMT_absorb_le`, from `QAdvT.time_absorb`);
* `mrField`: a multi-round circuit that is a field of a structure binder, by `time_fold` under
  the time bound of the field;
* negative: a bound one below the computed one is refused, and a step cost that depends on the
  outcome of an instrument through an unregistered function is refused with the cost named.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundFoldQuantumTest

open CatCrypt.Quantum.ReactiveUC CatCrypt.Quantum.QROM CatCrypt.Crypto.Party

/-! ## Costed instruments -/

/-- The name of the costed instrument `qBind.timed`. -/
def qBind : Unit := ()

/-- One unit, then the bind of the binder instrument `w` with the binder instruments `v a`,
charging `vCost a` at its outcome `a`, placed on the left of `C`. -/
noncomputable def qBind.timed {d : ℕ} (B C : Type) [Fintype B] [Fintype C]
    (w : QInstrT (Fin d × B) Bool fun _ => Fin d × B)
    (v : Bool → QInstrT (Fin d × B) ℕ fun _ => Fin d × B) (vCost : Bool → ℕ) :
    ℕ × QInstrT (Fin d × (B × C)) ℕ fun _ => Fin d × (B × C) :=
  QInstrT.delay 1 ((QInstrT.bind w fun a => (vCost a, v a)).1,
    QInstrT.placeLeft B C inferInstance inferInstance ℕ
      (QInstrT.bind w fun a => (vCost a, v a)).2)

derive_time_bound qBind

example {d : ℕ} (B C : Type) [Fintype B] [Fintype C]
    (w : QInstrT (Fin d × B) Bool fun _ => Fin d × B)
    (v : Bool → QInstrT (Fin d × B) ℕ fun _ => Fin d × B) (vCost : Bool → ℕ) {S T t : ℕ}
    (hw : ProgE.Bound Costed.weight w.toTree S fun _ => True)
    (hv : ∀ a, ProgE.Bound Costed.weight (v a).toTree T fun _ => True)
    (hc : ∀ a, vCost a ≤ t) :
    QInstrT.StepTimeBound (qBind.timed B C w v vCost) (S + T + t + 1) :=
  (qBind.timeBound_timed B C w v vCost hw hv hc).mono (by omega)

/-! ## Costed circuits -/

/-- The name of the costed circuit `qAbs.timed`. -/
def qAbs : Unit := ()

/-- The binder circuit `A x` with the oracle `G` absorbed, after the step cost `f x + 3`. -/
noncomputable def qAbs.timed {m n w q : ℕ} [NeZero n] (f : ℕ → ℕ) (A : ℕ → QAdvT m n w q)
    (G : Fin m → Fin n) (x : ℕ) : ℕ × QAdvT m n w 0 :=
  (f x + 3, QAdvT.absorb (A x) G)

derive_time_bound qAbs

example {m n w q : ℕ} [NeZero n] (f : ℕ → ℕ) (A : ℕ → QAdvT m n w q) (G : Fin m → Fin n)
    (x : ℕ) {T t : ℕ} (hf : ∀ y, f y ≤ t) (hA : ∀ y, (A y).time ≤ T) :
    QAdvT.StepTimeBound (qAbs.timed f A G x) (t + T + 3) :=
  (qAbs.timeBound_timed f A G x hf hA).mono (by omega)

/-- A structure with a field of multi-round circuits. -/
structure MRS (m n w q k c a : ℕ) where
  /-- The circuit at an index. -/
  circ : ℕ → QAdvMRT m n w q k c a

/-- The circuit of the field of `S` at `x + 1`, after the step cost `cst x + 1`. -/
noncomputable def mrField {m n w q k c a : ℕ} (S : MRS m n w q k c a) (cst : ℕ → ℕ) (x : ℕ) :
    ℕ × QAdvMRT m n w q k c a :=
  (cst x + 1, S.circ (x + 1))

example {m n w q k c a : ℕ} (S : MRS m n w q k c a) (cst : ℕ → ℕ) (x : ℕ) {T t : ℕ}
    (hS : ∀ y, (S.circ y).time ≤ T) (hc : ∀ y, cst y ≤ t) :
    QAdvMRT.StepTimeBound (mrField S cst x) (t + T + 1) := by
  time_fold

/-! ## Refusals -/

/-- A bound one below the computed bound is refused. -/
example : True := by
  fail_if_success
    have : ∀ {m n w q : ℕ} [NeZero n] (f : ℕ → ℕ) (A : ℕ → QAdvT m n w q) (G : Fin m → Fin n)
        (x : ℕ) {T t : ℕ} (_hf : ∀ y, f y ≤ t) (_hA : ∀ y, (A y).time ≤ T),
        QAdvT.StepTimeBound (qAbs.timed f A G x) (t + T + 2) := by
      intros
      time_fold
  trivial

/-- A step cost outside the registered costs: the weight of an outcome through a function the
rule does not read. -/
def outWeight : Bool → ℕ
  | true => 7
  | false => 0

/--
error: no bound of the charge
  outWeight a
-/
#guard_msgs (substring := true) in
example {d : ℕ} (w : QInstrT (Fin d) Bool fun _ => Fin d)
    (v : Bool → QInstrT (Fin d) ℕ fun _ => Fin d) {S T : ℕ}
    (hw : ProgE.Bound Costed.weight w.toTree S fun _ => True)
    (hv : ∀ a, ProgE.Bound Costed.weight (v a).toTree T fun _ => True) :
    QInstrT.StepTimeBound (QInstrT.bind w fun a => (outWeight a, v a)) (S + T + 7) := by
  time_fold

end CatCrypt.Tactics.DeriveTimeBoundFoldQuantumTest

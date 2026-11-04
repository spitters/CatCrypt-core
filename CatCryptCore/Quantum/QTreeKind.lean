/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizesMem
public import CatCryptCore.Quantum.QSimTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimedStructure

/-!
# Quantum instruments as a tree kind of `derive_timed`

A subinstrument `SubInstrument A A α` is, after reducible unfolding, the dependent
subinstrument `DSubInstrument A α (fun _ => A)`. This module registers dependent subinstruments
as a tree kind of `CatCryptCore.Tactics.DeriveTimed` (the quantum tree kind), so that
`derive_timed`, `derive_timed_structure` and `derive_reduction` price quantum instruments and
give time certificates of quantum reductions and of structures with subinstrument fields.

The costed instrument `QInstrT A α B` is the costed quantum computation `QTreeT A α`: a program
of operations on `A` with ticks. Its parameters are those of `DSubInstrument A α B`; the output
system `B` enters only through the erasure `QInstrT.erase`, which is the erasure
`QTreeT.erase` of the costed computation when `B` is the constant family `fun _ => A`, and the
failing subinstrument otherwise. The time bound of a step-prefixed costed instrument is
`QInstrT.StepTimeBound`: the step cost followed by the bound `ProgE.Bound Costed.weight` of the
costed computation.

The kind `qInstrKind` has the node `SubInstrument.pure` (costed `ProgE.ret`) and the
combinators `SubInstrument.bind` (costed `ProgE.bind`, the step cost of the continuation as a
tick), `placeLeft` and `placeRight` (the costed computation with each operation framed and
relabelled, `QInstrT.place`). A subinstrument given by a constant has no node and is refused;
in a reduction it is a binder or a field of a binder, priced by its cost companion.

Search words: quantum tree kind, costed instrument, costed subinstrument, derive_timed, time
certificate, quantum reduction, costed placement.

## Main definitions

* `QInstrT`, `QInstrT.erase`, `QInstrT.delay`, `QInstrT.StepTimeBound` — costed instruments
* `QInstrT.ret`, `QInstrT.bind`, `QInstrT.place`, `QInstrT.placeLeft`, `QInstrT.placeRight`
* `qInstrKind` — the tree kind, registered by `register_tree_kind`

## Main results

* `QInstrT.erase_bind`, `QInstrT.erase_placeLeft`, `QInstrT.erase_placeRight` — erasure
  commutes with sequencing and placement
* `QInstrT.stepTimeBound_ret`, `QInstrT.stepTimeBound_delay_bind`, `QInstrT.bound_placeLeft`,
  `QInstrT.bound_placeRight` — step time bounds of returns, sequencing and placement
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum CatCrypt.Crypto.Party

/-- A costed instrument with the parameters of `DSubInstrument A α B`: a costed quantum
computation on `A`, in `Type 1` as the costed trees of the tree kinds. -/
structure QInstrT (A : Type) [Fintype A] (α : Type) (B : α → Type) [∀ a, Fintype (B a)] :
    Type 1 where
  /-- The costed quantum computation. -/
  toTree : QTreeT A α

namespace QInstrT

variable {A : Type} [Fintype A] {α β : Type}

open Classical in
/-- The erasure of a costed instrument: the erased costed computation when the output family
is the constant family `fun _ => A`, the failing subinstrument otherwise. -/
noncomputable def erase {B : α → Type} [iB : ∀ a, Fintype (B a)] (x : QInstrT A α B) :
    DSubInstrument A α B :=
  if h : B = fun _ => A then
    cast (by
        subst h
        exact congrArg (@DSubInstrument A _ α (fun _ => A)) (Subsingleton.elim _ _))
      (QTreeT.erase (R := A) x.toTree)
  else DSubInstrument.fail

/-- The step cost `c` added in front of a step-prefixed costed instrument. -/
def delay {B : α → Type} [∀ a, Fintype (B a)] (c : ℕ) (x : ℕ × QInstrT A α B) :
    ℕ × QInstrT A α B :=
  (c + x.1, x.2)

/-- `StepTimeBound x T`: the step cost of `x` followed by its costed computation takes time at
most `T`. -/
def StepTimeBound {B : α → Type} [∀ a, Fintype (B a)] (x : ℕ × QInstrT A α B) (n : ℕ) :
    Prop :=
  x.1 ≤ n ∧ ProgE.Bound Costed.weight x.2.toTree (n - x.1) fun _ => True

/-- The costed instrument that returns `a`. -/
def ret (A : Type) [Fintype A] (α : Type) (B : α → Type) [∀ a, Fintype (B a)] (a : α) :
    QInstrT A α B :=
  ⟨ProgE.ret a⟩

/-- Run `x`, then continue with `f` on its outcome; the step cost of `f a` is a tick in front of
its costed instrument. -/
def bind (x : QInstrT A α fun _ => A) (f : α → ℕ × QInstrT A β fun _ => A) :
    ℕ × QInstrT A β fun _ => A :=
  (0, ⟨x.toTree.bind fun a => ProgE.tick (f a).1 (f a).2.toTree⟩)

/-- An operation framed by `C` and relabelled along `e`; a tick is kept. -/
noncomputable def placeOp {A' : Type} [Fintype A'] (C : Type) [Fintype C] (e : A × C ≃ A') :
    Costed (SubInstrument A A ℕ) → Costed (SubInstrument A' A' ℕ)
  | .op q => .op (relabel e (q.frame C))
  | .tick c => .tick c

/-- The costed computation `x` with each operation framed by `C` and relabelled along `e`. -/
noncomputable def place {A' : Type} [Fintype A'] (C : Type) [Fintype C] (e : A × C ≃ A')
    (x : QInstrT A α fun _ => A) : QInstrT A' α fun _ => A' :=
  ⟨ProgE.mapOp (placeOp C e) x.toTree⟩

/-- The costed form of `placeLeft`. -/
noncomputable def placeLeft {d : ℕ} (B C : Type) (iB : Fintype B) (iC : Fintype C) (α : Type)
    (w : QInstrT (Fin d × B) α fun _ => Fin d × B) :
    QInstrT (Fin d × (B × C)) α fun _ => Fin d × (B × C) :=
  place C (Equiv.prodAssoc (Fin d) B C) w

/-- The costed form of `placeRight`. -/
noncomputable def placeRight {d : ℕ} (B C : Type) (iB : Fintype B) (iC : Fintype C) (α : Type)
    (s : QInstrT (Fin d × C) α fun _ => Fin d × C) :
    QInstrT (Fin d × (B × C)) α fun _ => Fin d × (B × C) :=
  place B (placeR (Fin d) B C) s

/-- Unfolding lemma of `erase` at the constant output family. -/
theorem erase_const (x : QInstrT A α fun _ => A) : x.erase = QTreeT.erase x.toTree := by
  simp [erase]

/-- Erasure of a return. -/
@[simp] theorem erase_ret (a : α) :
    (ret A α (fun _ => A) a).erase = (SubInstrument.pure a : SubInstrument A A α) := by
  rw [erase_const]
  rfl

/-- Erasure commutes with sequencing. -/
theorem erase_bind (x : QInstrT A α fun _ => A) (f : α → ℕ × QInstrT A β fun _ => A) :
    (bind x f).2.erase = SubInstrument.bind x.erase fun a => (f a).2.erase := by
  simp only [erase_const, bind, QTreeT.erase_bind, QTreeT.erase_tick]

/-- Erasure commutes with placement. -/
theorem erase_place {A' : Type} [Fintype A'] (C : Type) [Fintype C] (e : A × C ≃ A')
    (x : QInstrT A α fun _ => A) :
    (place C e x).erase = relabel e (x.erase.frame C) := by
  have hfail : relabel e ((SubInstrument.fail : SubInstrument A A α).frame C) =
      SubInstrument.fail := by
    rw [SubInstrument.frame_fail]
    exact DSubInstrument.ext <| funext fun _ => LinearMap.ext fun _ => by ext; rfl
  obtain ⟨t⟩ := x
  simp only [erase_const, place]
  induction t with
  | ret a =>
    simp only [ProgE.mapOp, QTreeT.erase_ret, SubInstrument.frame_pure, relabel_pure]
  | recv k ih => exact hfail.symm
  | send o p ih => exact o.elim
  | opN q k ih =>
    have hop : ∀ {R : Type} [Fintype R] (q : SubInstrument R R ℕ) (k : ℕ → QTreeT R α),
        QTreeT.erase (ProgE.opN (.op q) k) = q.bind fun n => QTreeT.erase (k n) :=
      fun _ _ => rfl
    have htick : ∀ {R : Type} [Fintype R] (c : ℕ) (k : ℕ → QTreeT R α),
        QTreeT.erase (ProgE.opN (.tick c) k) = QTreeT.erase (k 0) := fun _ k =>
      SubInstrument.pure_bind 0 fun n => QTreeT.erase (k n)
    cases q with
    | op q =>
      simp only [ProgE.mapOp, placeOp, hop, ih, SubInstrument.frame_bind, relabel_bind]
    | tick c => simp only [ProgE.mapOp, placeOp, htick, ih]
  | fail => exact hfail.symm

/-- Placement keeps the weight of every costed operation. -/
theorem weight_placeOp {A' : Type} [Fintype A'] (C : Type) [Fintype C] (e : A × C ≃ A')
    (q : Costed (SubInstrument A A ℕ)) : Costed.weight (placeOp C e q) = Costed.weight q := by
  cases q <;> rfl

/-- Placement keeps the time bounds of a costed instrument. -/
theorem bound_place {A' : Type} [Fintype A'] (C : Type) [Fintype C] (e : A × C ≃ A')
    (x : QInstrT A α fun _ => A) (t : ℕ) (P : α → Prop) :
    ProgE.Bound Costed.weight (place C e x).toTree t P ↔
      ProgE.Bound Costed.weight x.toTree t P := by
  simp only [place, ProgE.bound_mapOp, weight_placeOp]

/-- Erasure commutes with `placeLeft`. -/
theorem erase_placeLeft {d : ℕ} (B C : Type) [iB : Fintype B] [iC : Fintype C] (α : Type)
    (w : QInstrT (Fin d × B) α fun _ => Fin d × B) :
    (placeLeft B C iB iC α w).erase = ReactiveUC.placeLeft B C w.erase := by
  rw [placeLeft, erase_place]
  rfl

/-- Erasure commutes with `placeRight`. -/
theorem erase_placeRight {d : ℕ} (B C : Type) [iB : Fintype B] [iC : Fintype C] (α : Type)
    (s : QInstrT (Fin d × C) α fun _ => Fin d × C) :
    (placeRight B C iB iC α s).erase = ReactiveUC.placeRight B C s.erase := by
  rw [placeRight, erase_place]
  rfl

/-- Erasure of a step-prefixed costed instrument commutes with `if`. -/
theorem erase_snd_ite {B : α → Type} [∀ a, Fintype (B a)] (c : Prop) [Decidable c]
    (x y : ℕ × QInstrT A α B) :
    (if c then x else y).2.erase = if c then x.2.erase else y.2.erase := by
  split <;> rfl

/-- Erasure of a step-prefixed costed instrument commutes with a dependent `if`. -/
theorem erase_snd_dite {B : α → Type} [∀ a, Fintype (B a)] (c : Prop) [Decidable c]
    (x : c → ℕ × QInstrT A α B) (y : ¬c → ℕ × QInstrT A α B) :
    (if h : c then x h else y h).2.erase = if h : c then (x h).2.erase else (y h).2.erase := by
  split <;> rfl

/-- Erasure of a costed instrument commutes with `if`. -/
theorem erase_ite {B : α → Type} [∀ a, Fintype (B a)] (c : Prop) [Decidable c]
    (x y : QInstrT A α B) :
    (if c then x else y).erase = if c then x.erase else y.erase := by
  split <;> rfl

/-- A step time bound holds at every larger time. -/
theorem StepTimeBound.mono {B : α → Type} [∀ a, Fintype (B a)] {x : ℕ × QInstrT A α B}
    {n n' : ℕ} (h : StepTimeBound x n) (hn : n ≤ n') : StepTimeBound x n' :=
  ⟨h.1.trans hn, h.2.mono (by omega) fun _ h => h⟩

/-- A return, with step cost `0`, takes time `0`. -/
theorem stepTimeBound_ret (B : α → Type) [∀ a, Fintype (B a)] (a : α) :
    StepTimeBound (0, ret A α B a) 0 :=
  ⟨le_rfl, trivial⟩

/-- The step cost `c` followed by `x` of time at most `t` and then by step-prefixed costed
instruments `f a` of time at most `u` takes time at most `c + t + u`. -/
theorem stepTimeBound_delay_bind (c : ℕ) (x : QInstrT A α fun _ => A)
    (f : α → ℕ × QInstrT A β fun _ => A) {t u : ℕ}
    (hx : ProgE.Bound Costed.weight x.toTree t fun _ => True)
    (hf : ∀ a, StepTimeBound (f a) u) : StepTimeBound (delay c (bind x f)) (c + t + u) := by
  refine ⟨by simp only [delay, bind]; omega, ?_⟩
  have hb := ProgE.Bound.bind (u := u) (P := fun _ => True) (p := x.toTree)
    (f := fun a => ProgE.tick (f a).1 (f a).2.toTree)
    (hx.mono le_rfl fun a _ => ⟨(hf a).1, fun _ => (hf a).2⟩)
  simp only [delay, bind]
  exact hb.mono (by omega) fun _ h => h

/-- Placement on the left keeps the time bounds of a costed instrument. -/
theorem bound_placeLeft {d : ℕ} (B C : Type) [iB : Fintype B] [iC : Fintype C] (α : Type)
    (w : QInstrT (Fin d × B) α fun _ => Fin d × B) (t : ℕ) (P : α → Prop) :
    ProgE.Bound Costed.weight (placeLeft B C iB iC α w).toTree t P ↔
      ProgE.Bound Costed.weight w.toTree t P :=
  bound_place _ _ _ _ _

/-- Placement on the right keeps the time bounds of a costed instrument. -/
theorem bound_placeRight {d : ℕ} (B C : Type) [iB : Fintype B] [iC : Fintype C] (α : Type)
    (s : QInstrT (Fin d × C) α fun _ => Fin d × C) (t : ℕ) (P : α → Prop) :
    ProgE.Bound Costed.weight (placeRight B C iB iC α s).toTree t P ↔
      ProgE.Bound Costed.weight s.toTree t P :=
  bound_place _ _ _ _ _

end QInstrT

open CatCrypt.Tactics.DeriveTimed in
/-- Dependent subinstruments `DSubInstrument A α B`, the reducible unfolding of
`SubInstrument A A α`: the node `SubInstrument.pure` and the combinators `SubInstrument.bind`,
`placeLeft` and `placeRight`. -/
meta def qInstrKind : TreeKind where
  noun := "quantum instrument"
  tree := ``_root_.Quantum.DSubInstrument
  nParams := 5
  timed := ``CatCrypt.Quantum.ReactiveUC.QInstrT
  erase := ``CatCrypt.Quantum.ReactiveUC.QInstrT.erase
  delay := ``CatCrypt.Quantum.ReactiveUC.QInstrT.delay
  nodes := #[
    ⟨``_root_.Quantum.SubInstrument.pure, ``CatCrypt.Quantum.ReactiveUC.QInstrT.ret, #[.data]⟩]
  combinators := #[
    ⟨``_root_.Quantum.SubInstrument.bind, ``CatCrypt.Quantum.ReactiveUC.QInstrT.bind,
      #[.tree, .pairFn 1], true⟩,
    ⟨``CatCrypt.Quantum.ReactiveUC.placeLeft, ``CatCrypt.Quantum.ReactiveUC.QInstrT.placeLeft,
      #[.keep, .keep, .keep, .keep, .keep, .tree], false⟩,
    ⟨``CatCrypt.Quantum.ReactiveUC.placeRight, ``CatCrypt.Quantum.ReactiveUC.QInstrT.placeRight,
      #[.keep, .keep, .keep, .keep, .keep, .tree], false⟩]
  eraseLemmas := #[``CatCrypt.Quantum.ReactiveUC.QInstrT.erase_ret,
    ``CatCrypt.Quantum.ReactiveUC.QInstrT.delay, ``CatCrypt.Quantum.ReactiveUC.QInstrT.erase_bind,
    ``CatCrypt.Quantum.ReactiveUC.QInstrT.erase_placeLeft,
    ``CatCrypt.Quantum.ReactiveUC.QInstrT.erase_placeRight,
    ``CatCrypt.Quantum.ReactiveUC.QInstrT.erase_snd_ite,
    ``CatCrypt.Quantum.ReactiveUC.QInstrT.erase_snd_dite]
  hatLemmas := #[``Prod.mk.eta, ``CatCrypt.Tactics.DeriveTimed.fst_ite,
    ``CatCrypt.Tactics.DeriveTimed.snd_ite, ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk,
    ``CatCrypt.Quantum.ReactiveUC.QInstrT.erase_ite]
  stepTimeBound := some ``CatCrypt.Quantum.ReactiveUC.QInstrT.StepTimeBound

end CatCrypt.Quantum.ReactiveUC

register_tree_kind CatCrypt.Quantum.ReactiveUC.qInstrKind

namespace CatCrypt.Quantum.ReactiveUC.QTreeKindTest

open _root_.Quantum CatCrypt.Crypto.Party

/-- A quantum step machine: an initial state and a quantum step on the register `R`. -/
structure QStep (R : Type) [Fintype R] (σ : Type) where
  /-- Initial state. -/
  init : σ
  /-- The quantum step from a state. -/
  step : σ → SubInstrument R R σ

derive_timed_structure QStep

/-- Unfolding lemma of `QStep.Timed.TimeBound`: the cost of computing each step followed by its
run, a conjunct of the quantum tree kind. -/
theorem QStep.Timed.timeBound_iff {R : Type} [Fintype R] {σ : Type} (A' : QStep.Timed R σ)
    (T : ℕ) :
    A'.TimeBound T ↔ ∀ s, QInstrT.StepTimeBound (A'.stepCost s, A'.step s) T :=
  Iff.rfl

/-- A step machine on `Fin d × B` placed on the left of `Fin d × (B × C)`. -/
noncomputable def QStep.placeL {d : ℕ} (B C : Type) [Fintype B] [Fintype C] {σ : Type}
    (S : QStep (Fin d × B) σ) : QStep (Fin d × (B × C)) σ where
  init := S.init
  step s := (placeLeft B C (S.step s)).bind fun t => SubInstrument.pure t

derive_reduction QStep.placeL

/-- The time of the left placement: one unit for the call of the step, then the step. -/
theorem QStep.placeL.timeBound {d : ℕ} (B C : Type) [Fintype B] [Fintype C] {σ : Type}
    (S : QStep (Fin d × B) σ) (step : σ → QInstrT (Fin d × B) σ fun _ => Fin d × B)
    (stepCost : σ → ℕ) (T : ℕ) (h : ∀ s, QInstrT.StepTimeBound (stepCost s, step s) T) :
    (QStep.placeL.timed B C S step stepCost).TimeBound (1 + T) := by
  intro s
  obtain ⟨h1, h2⟩ := h s
  refine ⟨?_, ?_⟩
  · simp only [QStep.placeL.timed, QStep.placeL.step.tree.timed, QInstrT.delay,
      QInstrT.bind]
    omega
  · simp only [QStep.placeL.timed, QStep.placeL.step.tree.timed, QInstrT.delay,
      QInstrT.bind]
    have hb := ProgE.Bound.bind (u := 0) (P := fun _ => True)
      (p := (QInstrT.placeLeft B C inferInstance inferInstance σ (step s)).toTree)
      (f := fun a => ProgE.tick 0
        (QInstrT.ret (Fin d × (B × C)) σ (fun _ => Fin d × (B × C)) a).toTree)
      ((QInstrT.bound_place _ _ _ _ _).2
        (h2.mono le_rfl fun _ _ => ⟨le_rfl, fun _ => trivial⟩))
    exact hb.mono (by omega) fun _ h => h

/-- A step machine on `Fin d × C` placed on the right of `Fin d × (B × C)`. -/
noncomputable def QStep.placeR {d : ℕ} (B C : Type) [Fintype B] [Fintype C] {σ : Type}
    (S : QStep (Fin d × C) σ) : QStep (Fin d × (B × C)) σ where
  init := S.init
  step s := placeRight B C (S.step s)

derive_reduction QStep.placeR

end CatCrypt.Quantum.ReactiveUC.QTreeKindTest

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QPullbackCascade
public import CatCryptCore.Quantum.QSysCat

/-!
# Quantum parallel composition with private registers as a context over environments with memory

The **quantum parallel composition** `QSys.par X Y` of a system `X` with private register `H` and
a system `Y` with private register `H'` runs on the sum interface: an event `inl e` activates
`X` on the left factor of the private register `H × H'`, an event `inr e'` activates `Y` on the
right factor, and the output carries the tag of the event. Its step is the parallel composition
`QRSys.par` of the two systems placed on the joint register `Fin d × (H × H')`.

Each component sees the other through a simulator with a private register. The simulator
`QSys.parSimL O Y idle` in front of the hole `X` answers a left event by passing it to the hole;
on a right event it runs `Y` on its own register, activates the hole on the idle event `idle`
and discards the answer. When `X` is idle at `idle` (`QSys.IdleAt`: the step at `idle` leaves the
state and the registers unchanged), the state map that adds the empty pending output is a step
map from `X.par Y` to the attachment of the simulator to `X` (`QSys.par_stepMap_attachQ`); the
views agree by `qviewQ_eq_of_stepMap`. The two one-hole contexts `- ∥ Y` and `X ∥ -` are
therefore quantum pullbacks over environments with memory (`QSys.parLeft`, `QSys.parRight`),
with the idle systems as admissible systems: the private register of the other component moves
to the environment memory.

The **composition theorem** for the quantum parallel composition (`QRealizesQB.par`): if `X`
realizes `X'` with bound `bX` and `Y` realizes `Y'` with bound `bY`, against environments with
quantum memory, and the left systems are idle at `idleL` and the right ones at `idleR`, then
`X.par Y` realizes `X'.par Y'` with the bound `bX` at the environment that absorbs `Y` plus `bY`
at the environment that absorbs `X'`. The idle event is the quantum analogue of
`MultiHybrid.IdleAt` in the classical `realizes_par`: an environment runs a fixed number of
rounds, each activating the hole once, so a round spent on the other component activates the
hole on an event that does nothing.

Search words: quantum parallel composition, private register, quantum context, pullback,
composition theorem, idle event, environment with quantum memory, simulator absorption.

## Main definitions

* `QSys.par`, `QSys.IdleAt`, `QSys.parSimL`, `QSys.parSimR`, `QSys.parLeft`, `QSys.parRight`

## Main results

* `qloopQ_stepMap`, `qviewQ_eq_of_stepMap` — views of environments with memory under step maps
* `QSys.par_stepMap_attachQ`, `QSys.par_stepMap_attachQL`
* `QRealizesQB.par_left`, `QRealizesQB.par_right`, `QRealizesQB.par`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open CatCrypt.Crypto.UCTransport (QSysObj)
open scoped ENNReal

/-! ## Views of environments with memory under step maps -/

section StepMap

variable {H K : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {τ υ ζ E O : Type} {d : ℕ}

omit [DecidableEq H] [DecidableEq K] in
/-- A state map that commutes with the steps of two systems commutes with their joint runs
against an environment with memory. -/
theorem qloopQ_stepMap {S₁ : QSys H τ E O d} {S₂ : QSys H υ E O d} {f : τ → υ}
    (hf : ∀ t e, (S₁.step t e).bind (fun p => SubInstrument.pure (f p.1, p.2)) = S₂.step (f t) e)
    (Z : QStratQ K ζ E O d) (n : ℕ) (z : ζ) (t : τ) :
    (qloopQ S₁ Z n (z, t)).bind (fun c => SubInstrument.pure (c.1, f c.2)) =
      qloopQ S₂ Z n (z, f t) := by
  induction n generalizing z t with
  | zero => simp only [qloopQ, SubInstrument.pure_bind]
  | succ n ih =>
    simp only [qloopQ, ← hf, SubInstrument.frame_bind, SubInstrument.frame_pure,
      SubInstrument.bind_assoc, SubInstrument.pure_bind, ih]

/-- **Views of environments with memory are invariant under step maps.** A step map between two
systems with the same initial private basis state keeps the view of every environment with
memory. -/
theorem qviewQ_eq_of_stepMap {S₁ : QSys H τ E O d} {S₂ : QSys H υ E O d} {f : τ → υ}
    (hf : QRSys.StepMap S₁.toQRSys S₂.toQRSys f) (hr : S₁.initReg = S₂.initReg)
    (Z : QStratQ K ζ E O d) : qviewQ S₁ Z = qviewQ S₂ Z := by
  have hi : S₂.init = f S₁.init := hf.init_map.symm
  simp only [qviewQ, hr, hi, ← qloopQ_stepMap hf.step, SubInstrument.bind_assoc,
    SubInstrument.pure_bind]

end StepMap

/-! ## The quantum parallel composition and its simulators -/

namespace QSys

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
variable {τ υ E O E' O' : Type} {d : ℕ}

/-- The parallel composition of quantum systems with separate private registers: an event
`inl e` activates `X` on the left factor of the private register `H × H'`, an event `inr e'`
activates `Y` on the right factor, and the output carries the tag of the event. -/
def par (X : QSys H τ E O d) (Y : QSys H' υ E' O' d) :
    QSys (H × H') (τ × υ) (E ⊕ E') (O ⊕ O') d where
  init := (X.init, Y.init)
  initReg := (X.initReg, Y.initReg)
  step := (QRSys.par (R := Fin d × (H × H'))
    ⟨X.init, fun t e => placeLeft H H' (X.step t e)⟩
    ⟨Y.init, fun u e => placeRight H H' (Y.step u e)⟩).step

/-- The system `X` is idle at the event `g` with output `o`: the step at `g` keeps the state,
leaves the registers unchanged and answers `o`. -/
def IdleAt (X : QSys H τ E O d) (g : E) (o : O) : Prop :=
  ∀ t, X.step t g = SubInstrument.pure (t, o)

/-- The system `Y` as a simulator with private register `H'` in front of a hole with events `E`
and outputs `O`: a left event is passed to the hole; a right event runs `Y`, activates the hole
on `idle` and keeps the output of `Y` as the pending answer, which replaces the answer of the
hole. -/
def parSimL (O : Type) (Y : QSys H' υ E' O' d) {E : Type} (idle : E) :
    QSimQ H' (υ × Option O') (E ⊕ E') (O ⊕ O') E O d where
  init := (Y.init, none)
  initReg := Y.initReg
  pre s := Sum.elim (fun e => SubInstrument.pure ((s.1, none), e))
    (fun e' => (Y.step s.1 e').bind fun p => SubInstrument.pure ((p.1, some p.2), idle))
  post s o := SubInstrument.pure ((s.1, none), s.2.elim (Sum.inl o) Sum.inr)

/-- The system `X` as a simulator with private register `H` in front of a hole with events `E'`
and outputs `O'`: a right event is passed to the hole; a left event runs `X`, activates the hole
on `idle` and keeps the output of `X` as the pending answer, which replaces the answer of the
hole. -/
def parSimR (O' : Type) (X : QSys H τ E O d) {E' : Type} (idle : E') :
    QSimQ H (τ × Option O) (E ⊕ E') (O ⊕ O') E' O' d where
  init := (X.init, none)
  initReg := X.initReg
  pre s := Sum.elim
    (fun e => (X.step s.1 e).bind fun p => SubInstrument.pure ((p.1, some p.2), idle))
    (fun e' => SubInstrument.pure ((s.1, none), e'))
  post s o' := SubInstrument.pure ((s.1, none), s.2.elim (Sum.inr o') Sum.inl)

omit [DecidableEq H] [DecidableEq H'] in
/-- If `X` is idle at `idle`, adding the empty pending output is a step map from `X.par Y` to
`X` with the simulator `parSimL O Y idle` attached. -/
theorem par_stepMap_attachQ (X : QSys H τ E O d) (Y : QSys H' υ E' O' d) (idle : E) {oX : O}
    (hX : X.IdleAt idle oX) :
    QRSys.StepMap (X.par Y).toQRSys ((parSimL O Y idle).attachQ X).toQRSys
      (fun c => (c.1, (c.2, none))) where
  init_map := rfl
  step c e := by
    cases e with
    | inl e =>
      simp only [toQRSys, par, QRSys.par_step_inl, QSimQ.attachQ_step, parSimL, Sum.elim_inl,
        placeLeft, placeRight, SubInstrument.frame_pure, relabel_pure,
        SubInstrument.bind_assoc, SubInstrument.pure_bind, Option.elim_none]
    | inr e =>
      simp only [toQRSys, par, QRSys.par_step_inr, QSimQ.attachQ_step, parSimL, Sum.elim_inr,
        hX c.1, placeLeft, placeRight, SubInstrument.frame_pure, SubInstrument.frame_bind,
        relabel_pure, relabel_bind, SubInstrument.bind_assoc, SubInstrument.pure_bind,
        Option.elim_some]

omit [DecidableEq H] [DecidableEq H'] in
/-- If `Y` is idle at `idle`, adding the empty pending output is a step map from `X.par Y` to
`Y` with the simulator `parSimR O' X idle` attached on the left. -/
theorem par_stepMap_attachQL (X : QSys H τ E O d) (Y : QSys H' υ E' O' d) (idle : E')
    {oY : O'} (hY : Y.IdleAt idle oY) :
    QRSys.StepMap (X.par Y).toQRSys ((parSimR O' X idle).attachQL Y).toQRSys
      (fun c => ((c.1, none), c.2)) where
  init_map := rfl
  step c e := by
    cases e with
    | inl e =>
      simp only [toQRSys, par, QRSys.par_step_inl, QSimQ.attachQL_step, parSimR, Sum.elim_inl,
        hY c.2, placeLeft, placeRight, SubInstrument.frame_pure, SubInstrument.frame_bind,
        relabel_pure, relabel_bind, SubInstrument.bind_assoc, SubInstrument.pure_bind,
        Option.elim_some]
    | inr e =>
      simp only [toQRSys, par, QRSys.par_step_inr, QSimQ.attachQL_step, parSimR, Sum.elim_inr,
        placeLeft, placeRight, SubInstrument.frame_pure, relabel_pure,
        SubInstrument.bind_assoc, SubInstrument.pure_bind, Option.elim_none]

/-- The parallel context with the hole on the left, `- ∥ Y`, as a pullback over environments
with memory: the private register of `Y` moves to the environment memory, and the admissible
systems are those idle at `idle`. -/
def parLeft (O : Type) (Y : QSys H' υ E' O' d) {E : Type} (idle : E) :
    QEnvPullbackQ E O (E ⊕ E') (O ⊕ O') d where
  map X := { H := X.H × H', τ := X.τ × υ, sys := X.sys.par Y }
  Mem K := K × H'
  memFin _ _ _ := inferInstance
  memDec _ _ _ := inferInstance
  Ctx ζ := ζ × (υ × Option O')
  pull Z := (parSimL O Y idle).absorb Z
  out c := c.1
  Adm X := ∃ o, X.sys.IdleAt idle o
  view_map := by
    rintro X ⟨o, hX⟩ K _ _ ζ Z
    exact (qviewQ_eq_of_stepMap (par_stepMap_attachQ X.sys Y idle hX) rfl Z).trans
      (QSimQ.qviewQ_attachQ _ _ Z)

/-- The parallel context with the hole on the right, `X ∥ -`, as a pullback over environments
with memory: the private register of `X` moves to the environment memory, and the admissible
systems are those idle at `idle`. -/
def parRight (O' : Type) (X : QSys H τ E O d) {E' : Type} (idle : E') :
    QEnvPullbackQ E' O' (E ⊕ E') (O ⊕ O') d where
  map Y := { H := H × Y.H, τ := τ × Y.τ, sys := X.par Y.sys }
  Mem K := K × H
  memFin _ _ _ := inferInstance
  memDec _ _ _ := inferInstance
  Ctx ζ := ζ × (τ × Option O)
  pull Z := (parSimR O' X idle).absorb Z
  out c := c.1
  Adm Y := ∃ o, Y.sys.IdleAt idle o
  view_map := by
    rintro Y ⟨o, hY⟩ K _ _ ζ Z
    exact (qviewQ_eq_of_stepMap (par_stepMap_attachQL X Y.sys idle hY) rfl Z).trans
      (QSimQ.qviewQ_attachQL _ _ Z)

end QSys

/-! ## The composition theorem for the quantum parallel composition -/

namespace QRealizesQB

variable {H H' H₁ H₂ : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂]
variable {τ υ τ₁ υ₂ E O E' O' : Type} {d : ℕ}

/-- **Congruence of the parallel composition, left component.** If `X` realizes `X'` with bound
`b`, both idle at `idle`, then `X.par Y` realizes `X'.par Y` with bound `b` at the environment
that absorbs `Y`. -/
theorem par_left {X : QSys H τ E O d} {X' : QSys H₁ τ₁ E O d} (Y : QSys H' υ E' O' d)
    (idle : E) {oX oX' : O} (hXi : X.IdleAt idle oX) (hX'i : X'.IdleAt idle oX')
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    (h : QRealizesQB X X' b) :
    QRealizesQB (X.par Y) (X'.par Y)
      fun K _ _ ζ Z => b (K × H') (ζ × (υ × Option O')) ((QSys.parSimL O Y idle).absorb Z) :=
  (QSys.parLeft O Y idle).realizes_map (X := { H := H, τ := τ, sys := X })
    (Y := { H := H₁, τ := τ₁, sys := X' }) ⟨oX, hXi⟩ ⟨oX', hX'i⟩ h

/-- **Congruence of the parallel composition, right component.** If `Y` realizes `Y'` with bound
`b`, both idle at `idle`, then `X.par Y` realizes `X.par Y'` with bound `b` at the environment
that absorbs `X`. -/
theorem par_right (X : QSys H τ E O d) {Y : QSys H' υ E' O' d} {Y' : QSys H₂ υ₂ E' O' d}
    (idle : E') {oY oY' : O'} (hYi : Y.IdleAt idle oY) (hY'i : Y'.IdleAt idle oY')
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E' O' d → ℝ≥0∞}
    (h : QRealizesQB Y Y' b) :
    QRealizesQB (X.par Y) (X.par Y')
      fun K _ _ ζ Z => b (K × H) (ζ × (τ × Option O)) ((QSys.parSimR O' X idle).absorb Z) :=
  (QSys.parRight O' X idle).realizes_map (X := { H := H', τ := υ, sys := Y })
    (Y := { H := H₂, τ := υ₂, sys := Y' }) ⟨oY, hYi⟩ ⟨oY', hY'i⟩ h

/-- **Composition theorem for the quantum parallel composition.** If `X` realizes `X'` with
bound `bX` and `Y` realizes `Y'` with bound `bY`, against environments with memory, the left
systems idle at `idleL` and the right ones at `idleR`, then `X.par Y` realizes `X'.par Y'` with
the bound `bX` at the environment that absorbs `Y` plus `bY` at the environment that absorbs
`X'`. -/
theorem par {X : QSys H τ E O d} {X' : QSys H₁ τ₁ E O d} {Y : QSys H' υ E' O' d}
    {Y' : QSys H₂ υ₂ E' O' d} (idleL : E) (idleR : E') {oX oX' : O} {oY oY' : O'}
    (hXi : X.IdleAt idleL oX) (hX'i : X'.IdleAt idleL oX')
    (hYi : Y.IdleAt idleR oY) (hY'i : Y'.IdleAt idleR oY')
    {bX : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    {bY : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E' O' d →
      ℝ≥0∞}
    (hX : QRealizesQB X X' bX) (hY : QRealizesQB Y Y' bY) :
    QRealizesQB (X.par Y) (X'.par Y') fun K _ _ ζ Z =>
      bX (K × H') (ζ × (υ × Option O')) ((QSys.parSimL O Y idleL).absorb Z) +
        bY (K × H₁) (ζ × (τ₁ × Option O)) ((QSys.parSimR O' X' idleR).absorb Z) :=
  (hX.par_left Y idleL hXi hX'i).trans (hY.par_right X' idleR hYi hY'i)

end QRealizesQB

end CatCrypt.Quantum.ReactiveUC

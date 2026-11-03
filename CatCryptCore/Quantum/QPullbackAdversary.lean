/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QPullbackCascade

/-!
# Quantum adversary systems and the quantum dummy-adversary theorem

A **quantum adversary system** `A : QAdvSys N α AI AP Lk Lk' d` sits between the environment
and the adversary ports of a quantum system with events `P ⊕ AP` and outputs `Oh × Lk`. It has
classical state `α` and a private register `N`; from an adversary input `AI` of the environment
it produces an adversary event `AP` of the system (`act`), and from a leakage `Lk` of the system
the leakage `Lk'` shown to the environment (`out`), each a subinstrument on the environment
register and `N`. Honest events and honest outputs pass unchanged. It is the quantum analogue of
the classical `AdvSys` of `CatCrypt.Crypto.UCTransparent`.

The adversary is a simulator with a private register (`QAdvSys.toQSimQ`). Attaching it to a
system (`QSys.attachAdv`) is `QSimQ.attachQ`, absorbing it into an environment with quantum
memory (`QAdvSys.absorb`) is `QSimQ.absorb`, and the pair is a memory pullback
(`QAdvSys.toQEnvPullbackQ`, a `QEnvPullbackQ`): the view of `Z` against `R.attachAdv A` is the
view of `A.absorb Z` against `R` (`qviewQ_attachAdv`), and realization with an
environment-dependent bound is preserved by attaching an adversary (`QRealizesQB.attachAdv`).

**Concurrent quantum UC emulation against adversary systems.** `QUCEmulatesSysB R F b` holds
when for every quantum adversary system `A` there is a quantum adversary system `S` (the
simulator) such that `R.attachAdv A` realizes `F.attachAdv S` against environments with memory,
with the bound `b` at the environment that absorbs `A`.

**Quantum dummy-adversary theorem.** The forwarding adversary `QAdvSys.dummy` is the identity
simulator, so attaching it does not change views (`qviewQ_attachAdv_dummy`).
* `qucEmulatesSysB_of_realizes`: if `R` realizes `F.attachAdv S`, then `R` emulates `F` against
  every adversary system `A`, with simulator `S.comp A` (`A` cascaded into `S`) and the bound at
  the environment that absorbs `A`.
* `QUCEmulatesSysB.realizes_dummy`: emulation against every adversary system gives a simulator
  `S` such that `R` realizes `F.attachAdv S` with the bound at the environment that absorbs the
  dummy adversary.
* `qucEmulatesSysB_iff_realizes_of_le`: when absorbing the dummy adversary does not increase the
  bound, emulation against every adversary system holds iff `R` realizes `F.attachAdv S` for some
  simulator `S`.

Search words: quantum adversary, dummy adversary, concurrent UC, private register, pullback,
simulator, environment with quantum memory, adversary absorption.

## Main definitions

* `QAdvSys`, `QAdvSys.toQSimQ`, `QAdvSys.absorb`, `QAdvSys.toQEnvPullbackQ`, `QAdvSys.dummy`,
  `QAdvSys.comp`, `QSys.attachAdv`
* `QUCEmulatesSysAgainst`, `QUCEmulatesSysB`

## Main results

* `qviewQ_attachAdv`, `QRealizesQB.attachAdv`, `qviewQ_attachAdv_dummy`, `qviewQ_attachAdv_comp`
* `qucEmulatesSysB_of_realizes`, `QUCEmulatesSysB.realizes_dummy`,
  `qucEmulatesSysB_iff_realizes_of_le`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open CatCrypt.Crypto.UCTransport (QSysObj)
open scoped ENNReal

/-! ## Quantum adversary systems -/

/-- A quantum adversary system with classical state `α` and private register `N`: from an
adversary input `AI` of the environment it produces an adversary event `AP` of the system
(`act`), and from a leakage `Lk` of the system the leakage `Lk'` shown to the environment
(`out`), each acting on the environment register `Fin d` and on `N`. -/
structure QAdvSys (N : Type) [Fintype N] (α AI AP Lk Lk' : Type) (d : ℕ) where
  /-- Initial classical state. -/
  init : α
  /-- Initial basis state of the private register. -/
  initReg : N
  /-- From an adversary input, the adversary event of the system. -/
  act : α → AI → SubInstrument (Fin d × N) (Fin d × N) (α × AP)
  /-- From a leakage of the system, the leakage shown to the environment. -/
  out : α → Lk → SubInstrument (Fin d × N) (Fin d × N) (α × Lk')

namespace QAdvSys

variable {N N₁ N₂ : Type} [Fintype N] [DecidableEq N] [Fintype N₁] [DecidableEq N₁]
  [Fintype N₂] [DecidableEq N₂]
variable {α σ AI AP AF Lk Lk' LF P Oh : Type} {d : ℕ}

/-- The event of the system for an event of the environment: honest events pass unchanged,
adversary inputs go through `act`. -/
def pre (A : QAdvSys N α AI AP Lk Lk' d) (a : α) :
    P ⊕ AI → SubInstrument (Fin d × N) (Fin d × N) (α × (P ⊕ AP))
  | .inl p => SubInstrument.pure (a, .inl p)
  | .inr i => (A.act a i).bind fun b => SubInstrument.pure (b.1, .inr b.2)

/-- The output shown to the environment: the honest output unchanged, the leakage through
`out`. -/
def post (A : QAdvSys N α AI AP Lk Lk' d) (a : α) (o : Oh × Lk) :
    SubInstrument (Fin d × N) (Fin d × N) (α × (Oh × Lk')) :=
  (A.out a o.2).bind fun r => SubInstrument.pure (r.1, (o.1, r.2))

/-- The adversary system as a simulator with private register `N` between the environment
interface `(P ⊕ AI, Oh × Lk')` and the system interface `(P ⊕ AP, Oh × Lk)`. -/
def toQSimQ (A : QAdvSys N α AI AP Lk Lk' d) :
    QSimQ N α (P ⊕ AI) (Oh × Lk') (P ⊕ AP) (Oh × Lk) d where
  init := A.init
  initReg := A.initReg
  pre := A.pre
  post := A.post

/-- The environment `Z` with memory `K` with the adversary system `A` absorbed: it runs `A`
against the adversary ports of the system; its memory is `K` beside the register of `A`. -/
def absorb {K ζ : Type} [Fintype K] (A : QAdvSys N α AI AP Lk Lk' d)
    (Z : QStratQ K ζ (P ⊕ AI) (Oh × Lk') d) : QStratQ (K × N) (ζ × α) (P ⊕ AP) (Oh × Lk) d :=
  A.toQSimQ.absorb Z

/-- Adversary absorption as a pullback over environments with memory: the adversary attached to
the system, the adversary absorbed into the environment, its register added to the memory. -/
def toQEnvPullbackQ (P Oh : Type) (A : QAdvSys N α AI AP Lk Lk' d) :
    QEnvPullbackQ (P ⊕ AP) (Oh × Lk) (P ⊕ AI) (Oh × Lk') d :=
  (A.toQSimQ (P := P) (Oh := Oh)).toQEnvPullbackQ

/-- The forwarding (dummy) adversary: adversary inputs and leakages pass unchanged. -/
def dummy (AP Lk : Type) : QAdvSys Unit Unit AP AP Lk Lk d where
  init := ()
  initReg := ()
  act _ i := SubInstrument.pure ((), i)
  out _ l := SubInstrument.pure ((), l)

/-- The adversary system `A` cascaded into the adversary system `S`: adversary inputs go
through `A` and then `S`, leakages through `S` and then `A`; the registers are paired. -/
def comp (S : QAdvSys N₂ σ AP AF LF Lk d) (A : QAdvSys N₁ α AI AP Lk Lk' d) :
    QAdvSys (N₁ × N₂) (α × σ) AI AF LF Lk' d where
  init := (A.init, S.init)
  initReg := (A.initReg, S.initReg)
  act c i := (placeLeft N₁ N₂ (A.act c.1 i)).bind fun a =>
    (placeRight N₁ N₂ (S.act c.2 a.2)).bind fun b => SubInstrument.pure ((a.1, b.1), b.2)
  out c l := (placeRight N₁ N₂ (S.out c.2 l)).bind fun b =>
    (placeLeft N₁ N₂ (A.out c.1 b.2)).bind fun a => SubInstrument.pure ((a.1, b.1), a.2)

/-- The dummy adversary is the identity simulator. -/
theorem toQSimQ_dummy :
    (dummy AP Lk : QAdvSys Unit Unit AP AP Lk Lk d).toQSimQ (P := P) (Oh := Oh) = QSimQ.id := by
  simp only [toQSimQ, QSimQ.id, QSimQ.mk.injEq, true_and]
  constructor
  · funext a e
    cases e <;> simp [pre, dummy]
  · funext a o
    simp [post, dummy]

omit [DecidableEq N₁] [DecidableEq N₂] in
/-- The simulator of a cascade of adversary systems is the composite of their simulators. -/
theorem toQSimQ_comp (S : QAdvSys N₂ σ AP AF LF Lk d) (A : QAdvSys N₁ α AI AP Lk Lk' d) :
    (S.comp A).toQSimQ (P := P) (Oh := Oh) = A.toQSimQ.comp S.toQSimQ := by
  simp only [toQSimQ, QSimQ.comp, QSimQ.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · funext c e
    cases e
    · simp [pre, placeLeft, placeRight, relabel_pure]
    · simp [pre, comp, placeLeft, placeRight, SubInstrument.frame_bind, relabel_bind,
        relabel_pure, SubInstrument.bind_assoc]
  · funext c o
    simp [post, comp, placeLeft, placeRight, SubInstrument.frame_bind, relabel_bind,
      relabel_pure, SubInstrument.bind_assoc]

end QAdvSys

/-! ## Attaching an adversary system -/

namespace QSys

variable {H N : Type} [Fintype H] [Fintype N]
variable {τ α AI AP Lk Lk' P Oh : Type} {d : ℕ}

/-- The system `R` with the quantum adversary system `A` attached to its adversary ports: its
private register pairs the register of `R` with the register of `A`. -/
def attachAdv (R : QSys H τ (P ⊕ AP) (Oh × Lk) d) (A : QAdvSys N α AI AP Lk Lk' d) :
    QSys (H × N) (τ × α) (P ⊕ AI) (Oh × Lk') d :=
  A.toQSimQ.attachQ R

end QSys

section Attach

variable {H H' N N₁ N₂ K : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype N] [DecidableEq N] [Fintype N₁] [DecidableEq N₁] [Fintype N₂] [DecidableEq N₂]
  [Fintype K] [DecidableEq K]
variable {τ υ φ α σ ζ AI AP AF Lk Lk' LF P Oh : Type} {d : ℕ}

/-- **Adversary absorption.** The view of `Z` against `R.attachAdv A` is the view of the
environment `A.absorb Z` against `R`, projected to the state of `Z`. -/
theorem qviewQ_attachAdv (R : QSys H τ (P ⊕ AP) (Oh × Lk) d) (A : QAdvSys N α AI AP Lk Lk' d)
    (Z : QStratQ K ζ (P ⊕ AI) (Oh × Lk') d) :
    qviewQ (R.attachAdv A) Z = (qviewQ R (A.absorb Z)).bind fun c => SubInstrument.pure c.1 :=
  QSimQ.qviewQ_attachQ _ _ _

/-- Attaching the dummy adversary does not change the view. -/
theorem qviewQ_attachAdv_dummy (R : QSys H τ (P ⊕ AP) (Oh × Lk) d)
    (Z : QStratQ K ζ (P ⊕ AP) (Oh × Lk) d) :
    qviewQ (R.attachAdv (QAdvSys.dummy AP Lk)) Z = qviewQ R Z := by
  rw [QSys.attachAdv, QAdvSys.toQSimQ_dummy, QSimQ.qviewQ_attachQ, simViewQ_id]

/-- Attaching `S` and then `A` has the view of attaching the cascade `S.comp A`. -/
theorem qviewQ_attachAdv_comp (F : QSys H' φ (P ⊕ AF) (Oh × LF) d)
    (S : QAdvSys N₂ σ AP AF LF Lk d) (A : QAdvSys N₁ α AI AP Lk Lk' d)
    (Z : QStratQ K ζ (P ⊕ AI) (Oh × Lk') d) :
    qviewQ ((F.attachAdv S).attachAdv A) Z = qviewQ (F.attachAdv (S.comp A)) Z := by
  rw [QSys.attachAdv, QSys.attachAdv, QSys.attachAdv, QAdvSys.toQSimQ_comp,
    QSimQ.qviewQ_attachQ, QSimQ.qviewQ_attachQ, simViewQ_comp]
  simp only [simViewQ]
  rw [QSimQ.qviewQ_attachQ]
  rfl

/-- Realization against environments with memory is unchanged by attaching the dummy adversary
to the real system. -/
theorem QRealizesQB_attachAdv_dummy_iff (R : QSys H τ (P ⊕ AP) (Oh × Lk) d)
    (I : QSys H' υ (P ⊕ AP) (Oh × Lk) d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AP) (Oh × Lk) d → ℝ≥0∞) :
    QRealizesQB (R.attachAdv (QAdvSys.dummy AP Lk)) I b ↔ QRealizesQB R I b := by
  simp only [QRealizesQB, qviewQ_attachAdv_dummy]

/-- **Attaching an adversary.** If `R` realizes `I` against environments with memory with bound
`b`, then `R.attachAdv A` realizes `I.attachAdv A` with bound `b` at the environment that absorbs
`A`. -/
theorem QRealizesQB.attachAdv {R : QSys H τ (P ⊕ AP) (Oh × Lk) d}
    {I : QSys H' υ (P ⊕ AP) (Oh × Lk) d}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AP) (Oh × Lk) d → ℝ≥0∞}
    (h : QRealizesQB R I b) (A : QAdvSys N α AI AP Lk Lk' d) :
    QRealizesQB (R.attachAdv A) (I.attachAdv A)
      fun K _ _ ζ Z => b (K × N) (ζ × α) (A.absorb Z) :=
  (A.toQEnvPullbackQ P Oh).realizes_map (X := { H := H, τ := τ, sys := R })
    (Y := { H := H', τ := υ, sys := I }) trivial trivial h

/-- Realization behind the simulator of an adversary system is realization of the ideal system
with that adversary system attached. -/
theorem QRealizesSimQB_iff_attachAdv (R : QSys H τ (P ⊕ AP) (Oh × Lk) d)
    (F : QSys H' φ (P ⊕ AF) (Oh × LF) d) (S : QAdvSys N σ AP AF LF Lk d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AP) (Oh × Lk) d → ℝ≥0∞) :
    QRealizesSimQB R F S.toQSimQ b ↔ QRealizesQB R (F.attachAdv S) b :=
  QRealizesSimQB_iff_attachQ R F _ b

end Attach

/-! ## Concurrent quantum UC emulation against adversary systems -/

section Emulation

variable {H H' N : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype N] [DecidableEq N]
variable {τ φ α AI AP AF Lk Lk' LF P Oh : Type} {d : ℕ}

/-- Emulation of `F` by `R` against the quantum adversary system `A`: some quantum adversary
system `S` (the simulator) makes `R.attachAdv A` realize `F.attachAdv S` against environments
with memory, with bound `bound`. -/
def QUCEmulatesSysAgainst (R : QSys H τ (P ⊕ AP) (Oh × Lk) d)
    (F : QSys H' φ (P ⊕ AF) (Oh × LF) d) (A : QAdvSys N α AI AP Lk Lk' d)
    (bound : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AI) (Oh × Lk') d → ℝ≥0∞) : Prop :=
  ∃ (NS : Type) (_ : Fintype NS) (_ : DecidableEq NS) (σ : Type)
    (S : QAdvSys NS σ AI AF LF Lk' d), QRealizesQB (R.attachAdv A) (F.attachAdv S) bound

/-- Concurrent quantum UC emulation with adversaries and simulators as quantum reactive systems
with private registers: for every quantum adversary system `A`, emulation against `A` with the
bound `b` at the environment that absorbs `A`. -/
def QUCEmulatesSysB (R : QSys H τ (P ⊕ AP) (Oh × Lk) d) (F : QSys H' φ (P ⊕ AF) (Oh × LF) d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AP) (Oh × Lk) d → ℝ≥0∞) : Prop :=
  ∀ (N : Type) [Fintype N] [DecidableEq N] (α AI Lk' : Type) (A : QAdvSys N α AI AP Lk Lk' d),
    QUCEmulatesSysAgainst R F A fun K _ _ ζ Z => b (K × N) (ζ × α) (A.absorb Z)

/-- **Quantum dummy-adversary theorem, realization to emulation.** If `R` realizes
`F.attachAdv S` with bound `b`, then for every adversary system `A` the real world
`R.attachAdv A` realizes `F.attachAdv (S.comp A)` with `b` at the environment that absorbs
`A`. -/
theorem qucEmulatesSysB_of_realizes {NS σ : Type} [Fintype NS] [DecidableEq NS]
    {R : QSys H τ (P ⊕ AP) (Oh × Lk) d} {F : QSys H' φ (P ⊕ AF) (Oh × LF) d}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AP) (Oh × Lk) d → ℝ≥0∞}
    (S : QAdvSys NS σ AP AF LF Lk d) (h : QRealizesQB R (F.attachAdv S) b) :
    QUCEmulatesSysB R F b := by
  intro N _ _ α AI Lk' A
  refine ⟨_, inferInstance, inferInstance, _, S.comp A, fun K _ _ ζ Z => ?_⟩
  rw [← qviewQ_attachAdv_comp]
  exact h.attachAdv A K ζ Z

/-- Emulation against the dummy adversary is a realization of `F.attachAdv S` by `R` for some
simulator `S`. -/
theorem qucEmulatesSysAgainst_dummy_iff (R : QSys H τ (P ⊕ AP) (Oh × Lk) d)
    (F : QSys H' φ (P ⊕ AF) (Oh × LF) d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AP) (Oh × Lk) d → ℝ≥0∞) :
    QUCEmulatesSysAgainst R F (QAdvSys.dummy AP Lk) b ↔
      ∃ (NS : Type) (_ : Fintype NS) (_ : DecidableEq NS) (σ : Type)
        (S : QAdvSys NS σ AP AF LF Lk d), QRealizesQB R (F.attachAdv S) b := by
  simp only [QUCEmulatesSysAgainst, QRealizesQB_attachAdv_dummy_iff]

/-- **Quantum dummy-adversary theorem, emulation to realization.** Emulation against every
adversary system with bound `b` gives a simulator `S` such that `R` realizes `F.attachAdv S`
with bound `b` at the environment that absorbs the dummy adversary. -/
theorem QUCEmulatesSysB.realizes_dummy {R : QSys H τ (P ⊕ AP) (Oh × Lk) d}
    {F : QSys H' φ (P ⊕ AF) (Oh × LF) d}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AP) (Oh × Lk) d → ℝ≥0∞}
    (h : QUCEmulatesSysB R F b) :
    ∃ (NS : Type) (_ : Fintype NS) (_ : DecidableEq NS) (σ : Type)
      (S : QAdvSys NS σ AP AF LF Lk d), QRealizesQB R (F.attachAdv S)
        fun K _ _ ζ Z => b (K × Unit) (ζ × Unit) ((QAdvSys.dummy AP Lk).absorb Z) :=
  (qucEmulatesSysAgainst_dummy_iff R F _).1 (h Unit Unit AP Lk (QAdvSys.dummy AP Lk))

/-- **Quantum dummy-adversary theorem for environment-dependent bounds.** If absorbing the dummy
adversary does not increase the bound `b`, emulation against every quantum adversary system with
bound `b` holds iff `R` realizes `F.attachAdv S` with bound `b` for some simulator `S`. -/
theorem qucEmulatesSysB_iff_realizes_of_le (R : QSys H τ (P ⊕ AP) (Oh × Lk) d)
    (F : QSys H' φ (P ⊕ AF) (Oh × LF) d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (P ⊕ AP) (Oh × Lk) d → ℝ≥0∞)
    (hb : ∀ (K : Type) [Fintype K] [DecidableEq K] (ζ : Type)
      (Z : QStratQ K ζ (P ⊕ AP) (Oh × Lk) d),
      b (K × Unit) (ζ × Unit) ((QAdvSys.dummy AP Lk).absorb Z) ≤ b K ζ Z) :
    QUCEmulatesSysB R F b ↔
      ∃ (NS : Type) (_ : Fintype NS) (_ : DecidableEq NS) (σ : Type)
        (S : QAdvSys NS σ AP AF LF Lk d), QRealizesQB R (F.attachAdv S) b := by
  constructor
  · intro h
    obtain ⟨NS, _, _, σ, S, hS⟩ := h.realizes_dummy
    exact ⟨NS, inferInstance, inferInstance, σ, S, fun K _ _ ζ Z => le_trans (hS K ζ Z) (hb K ζ Z)⟩
  · rintro ⟨_, _, _, _, S, hS⟩
    exact qucEmulatesSysB_of_realizes S hS

end Emulation

end CatCrypt.Quantum.ReactiveUC

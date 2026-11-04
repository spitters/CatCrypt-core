/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QPullbackCascade
public import CatCryptCore.Quantum.QSimTimed

/-!
# Quantum time certificates of environments with quantum memory

A costed quantum environment with memory `K` (`QStratQ.Timed K ζ E O d`) is an environment with
quantum memory (`QStratQ`, `QRealizesMem.lean`) whose steps `next` and `obs` are costed quantum
computations (`QTreeT`, `QSimTimed.lean`) on the interface register and the memory register. It
erases to the environment `QStratQ.Timed.erase ZT` of the erased steps. Its time bound
`ZT.TimeBound Inv n o` bounds, from a state of the invariant `Inv`, each `next` activation by `n`
and each `obs` activation by `o` (`ProgE.Bound Costed.weight`: one unit for an operation, `c` for a
tick of `c`), the steps returning states of `Inv`.

An environment `Z` has time `(n, o, q)` (`QEnvTimeBound Z ZT n o q`) when the costed environment
`ZT` erases to `Z`, its activations are bounded by `n` and `o` on some invariant, and `Z` makes at
most `q` activations (`Z.rounds ≤ q`). These are the quantities bounded: the time of each `next`
activation, the time of each `obs` activation, and the number of activations. The view of a
quantum environment returns its final state, and realization (`QRealizesQB`) bounds the diamond
distance of the views, which ranges over all final measurements; the environment carries no
distinguisher whose time would be bounded.

`QRealizesQBTime R I n o q b` is realization against the environments with memory of time
`(n, o, q)`.

Search words: quantum time certificate, costed quantum environment, quantum environment,
environment with quantum memory, activation time, activation count, costed pullback,
composition theorem.

## Main definitions

* `QStratQ.Timed`, `QStratQ.Timed.erase`, `QStratQ.Timed.Erases`, `QStratQ.Timed.TimeBound`:
  costed quantum environments with memory, erasure and time bound.
* `QEnvTimeBound Z ZT n o q`: the time of a quantum environment with memory.
* `QRealizesQBTime R I n o q b`: realization against the environments of time `(n, o, q)`.

## Main results

* `QEnvTimeBound.mono`: the time of an environment holds at larger bounds.
* `QRealizesQB.realizesQBTime`: a realization is a realization against the environments of every
  time.
* `QRealizesQBTime.mono`: realization against the environments of a time holds against the
  environments of a smaller time.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum CatCrypt.Crypto.Party
open CatCrypt.Crypto.UCTransport (QSysObj)
open scoped ENNReal

/-! ## Costed quantum environments with memory -/

/-- A costed quantum environment with state `ζ` and memory register `K`: its steps are costed
quantum computations on the interface register `Fin d` and the memory register. -/
structure QStratQ.Timed (K : Type) [Fintype K] (ζ E O : Type) (d : ℕ) where
  /-- Number of activations. -/
  rounds : ℕ
  /-- Initial environment state. -/
  init : ζ
  /-- Initial basis state of the memory register. -/
  initReg : K
  /-- Costed choice of the next event. -/
  next : ζ → QTreeT (Fin d × K) (ζ × E)
  /-- Costed observation of an output. -/
  obs : ζ → O → QTreeT (Fin d × K) ζ

namespace QStratQ.Timed

variable {K : Type} [Fintype K] {ζ E O : Type} {d : ℕ}

/-- The erasure of a costed environment: the environment of the erased steps. -/
def erase (ZT : QStratQ.Timed K ζ E O d) : QStratQ K ζ E O d where
  rounds := ZT.rounds
  init := ZT.init
  initReg := ZT.initReg
  next z := (ZT.next z).erase
  obs z o := (ZT.obs z o).erase

/-- `ZT.Erases Z`: the environment `Z` is the erasure of the costed environment `ZT`. -/
def Erases (ZT : QStratQ.Timed K ζ E O d) (Z : QStratQ K ζ E O d) : Prop :=
  ZT.erase = Z

/-- A costed environment erases to its erasure. -/
theorem erases_erase (ZT : QStratQ.Timed K ζ E O d) : ZT.Erases ZT.erase :=
  Eq.refl _

/-- The time bound of a costed environment on the states of the invariant `Inv`: the initial
state satisfies `Inv`, and from a state of `Inv` a `next` activation costs at most `n`, an `obs`
activation at most `o`, both returning states of `Inv`. -/
def TimeBound (ZT : QStratQ.Timed K ζ E O d) (Inv : ζ → Prop) (n o : ℕ) : Prop :=
  Inv ZT.init ∧
    (∀ z, Inv z → ProgE.Bound Costed.weight (ZT.next z) n fun y => Inv y.1) ∧
    ∀ z g, Inv z → ProgE.Bound Costed.weight (ZT.obs z g) o Inv

/-- A time bound holds at larger bounds. -/
theorem TimeBound.mono {ZT : QStratQ.Timed K ζ E O d} {Inv : ζ → Prop} {n o n' o' : ℕ}
    (h : ZT.TimeBound Inv n o) (hn : n ≤ n') (ho : o ≤ o') : ZT.TimeBound Inv n' o' :=
  ⟨h.1, fun z hz => (h.2.1 z hz).mono hn fun _ h => h,
    fun z g hz => (h.2.2 z g hz).mono ho fun _ h => h⟩

end QStratQ.Timed

/-! ## The time of a quantum environment with memory -/

/-- The quantum environment `Z` with memory `K` has time `(n, o, q)`: the costed environment `ZT`
erases to `Z`, on some invariant each `next` activation of `ZT` costs at most `n` and each `obs`
activation at most `o`, and `Z` makes at most `q` activations. -/
structure QEnvTimeBound {K : Type} [Fintype K] {ζ E O : Type} {d : ℕ} (Z : QStratQ K ζ E O d)
    (ZT : QStratQ.Timed K ζ E O d) (n o q : ℕ) : Prop where
  /-- The costed environment erases to `Z`. -/
  erases : ZT.Erases Z
  /-- The time of an activation. -/
  timeBound : ∃ Inv : ζ → Prop, ZT.TimeBound Inv n o
  /-- The number of activations. -/
  rounds_le : Z.rounds ≤ q

/-- The time of an environment holds at larger bounds. -/
theorem QEnvTimeBound.mono {K : Type} [Fintype K] {ζ E O : Type} {d : ℕ}
    {Z : QStratQ K ζ E O d} {ZT : QStratQ.Timed K ζ E O d} {n o q n' o' q' : ℕ}
    (h : QEnvTimeBound Z ZT n o q) (hn : n ≤ n') (ho : o ≤ o') (hq : q ≤ q') :
    QEnvTimeBound Z ZT n' o' q' where
  erases := h.erases
  timeBound := h.timeBound.imp fun _ hI => hI.mono hn ho
  rounds_le := h.rounds_le.trans hq

/-! ## Realization against time-bounded quantum environments -/

section RealizesTime

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
variable {τ υ E O : Type} {d : ℕ}

/-- `R` realizes `I` with the environment-dependent bound `b` against every quantum environment
with memory of time `(n, o, q)`. -/
def QRealizesQBTime (R : QSys H τ E O d) (I : QSys H' υ E O d) (n o q : ℕ)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞) :
    Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ζ : Type) (Z : QStratQ K ζ E O d)
    (ZT : QStratQ.Timed K ζ E O d), QEnvTimeBound Z ZT n o q →
      cpDist (qviewQ R Z) (qviewQ I Z) ≤ b K ζ Z

/-- A realization against environments with memory is a realization against the environments of
every time. -/
theorem QRealizesQB.realizesQBTime {R : QSys H τ E O d} {I : QSys H' υ E O d}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    (h : QRealizesQB R I b) (n o q : ℕ) : QRealizesQBTime R I n o q b :=
  fun K _ _ ζ Z _ _ => h K ζ Z

/-- Realization against the environments of time `(n', o', q')` is realization against the
environments of every smaller time `(n, o, q)`. -/
theorem QRealizesQBTime.mono {R : QSys H τ E O d} {I : QSys H' υ E O d} {n o q n' o' q' : ℕ}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    (h : QRealizesQBTime R I n' o' q' b) (hn : n ≤ n') (ho : o ≤ o') (hq : q ≤ q') :
    QRealizesQBTime R I n o q b :=
  fun K _ _ ζ Z ZT hT => h K ζ Z ZT (hT.mono hn ho hq)

end RealizesTime

end CatCrypt.Quantum.ReactiveUC

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QSimTimed

/-!
# Running time of the simulator programs of the quantum one-time pad

The costed forms of the simulator programs `QOTP.Reactive.simP` and `QOTP.Insecure.simP` of
`QOTP.lean`, as costed loop simulators (`QProg.loopQSim.timed`, `QProg.loopQSimQ.timed`) of the
priced simulator bodies: each iteration charges the cost of its quantum operation (`twirlCost n`
for the twirl, `qCost n` for the EPR preparation or the Bell measurement) as a tick before the
unit-cost body. An iteration costs at most that charge plus `3` (a receive, one operation, a
send), so each step of the simulator costs at most twice as much. No module imports this file.

Search words: quantum one-time pad, simulator program, time certificate, costed loop simulator.

## Main definitions

* `QOTP.Reactive.simP.timed`, `QOTP.Insecure.simP.timed`: the costed simulators.

## Main results

* `QOTP.Reactive.simP.erase_timed`, `QOTP.Reactive.simP.timeBound_timed`.
* `QOTP.Insecure.simP.erase_timed`, `QOTP.Insecure.simP.timeBound_timed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party.Protocols.QOTP

open CatCrypt.Core _root_.Quantum CatCrypt.Quantum.ReactiveUC

namespace Reactive

/-- An iteration of the simulator body costs at most `3` units at the unit weight. -/
theorem simBody_bound (n : ℕ) (s : Unit) :
    ProgE.Bound (fun _ => 1) (simBody n s) 3 fun _ => True := by
  refine ⟨by omega, fun e => ?_⟩
  rcases e with e | (_ | _ | _ | _)
  all_goals simp only [ProgE.bind, QProg.opE, QProg.op, ProgE.sendE, ProgE.bind_eq,
    Nat.add_one_sub_one, ProgE.Bound, Nat.one_le_ofNat, true_and, and_self]
  intro m
  split <;> simp only [ProgE.bind, ProgE.Bound, le_refl, and_self]

/-- **The costed simulator program of the quantum one-time pad**: the loop simulator of the
simulator body priced at `twirlCost n` per iteration. -/
noncomputable def simP.timed (twirlCost : ℕ → ℕ) (n : ℕ) :=
  QProg.loopQSim.timed (ProgE.priced (fun _ => twirlCost n) (simBody n)) ()

/-- **Erasure of the costed simulator program**: it erases to `simP n`. -/
theorem simP.erase_timed (twirlCost : ℕ → ℕ) (n : ℕ) :
    (simP.timed twirlCost n).Erases ProgE.erase (simP n) := by
  have h := QProg.loopQSim.erase_timed (ProgE.priced (fun _ => twirlCost n) (simBody n)) ()
  simp only [ProgE.erase_priced] at h
  exact h

/-- **Running time of the costed simulator program**: each step costs at most
`2 * (twirlCost n + 3)`. -/
theorem simP.timeBound_timed (twirlCost : ℕ → ℕ) (n : ℕ) :
    (simP.timed twirlCost n).TimeBound
      (fun p => ProgE.Bound Costed.weight p (twirlCost n + 3) fun _ => True)
      (2 * (twirlCost n + 3)) (2 * (twirlCost n + 3)) :=
  QProg.loopQSim.timeBound_timed trivial fun s _ => by
    simp only [ProgE.priced, ProgE.tick, ProgE.Bound, Costed.weight]
    refine ⟨by omega, fun _ => ?_⟩
    rw [ProgE.bound_costed, show twirlCost n + 3 - twirlCost n = 3 by omega]
    exact simBody_bound n s

end Reactive

namespace Insecure

open CatCrypt.Quantum.QOTPInsecure (eprSim)

/-- An iteration of the EPR simulator body costs at most `3` units at the unit weight. -/
theorem simBody_bound (n : ℕ) (s : CatCrypt.Quantum.QOTPInsecure.IPhase) :
    ProgE.Bound (fun _ => 1) (simBody n s) 3 fun _ => True := by
  refine ⟨by omega, fun e => ?_⟩
  rcases e with (_ | _) | (_ | _ | _) <;> cases s
  all_goals simp only [ProgE.bind, QProg.opE, QProg.op, ProgE.sendE, ProgE.bind_eq,
    Nat.add_one_sub_one, ProgE.Bound, Nat.one_le_ofNat, true_and]
  all_goals first
    | trivial
    | (intro m; split <;> simp only [ProgE.bind, ProgE.Bound, ProgE.pure_eq, le_refl, true_and])

/-- **The costed EPR simulator program**: the loop simulator with a private register of the
simulator body priced at `qCost n` per iteration, the cost of the EPR preparation or the Bell
measurement. -/
noncomputable def simP.timed (qCost : ℕ → ℕ) (n : ℕ) :=
  QProg.loopQSimQ.timed (ProgE.priced (fun _ => qCost n) (simBody n)) .idle (eprSim n).initReg

/-- **Erasure of the costed EPR simulator program**: it erases to `simP n`. -/
theorem simP.erase_timed (qCost : ℕ → ℕ) (n : ℕ) :
    (simP.timed qCost n).Erases ProgE.erase (simP n) := by
  have h := QProg.loopQSimQ.erase_timed (ProgE.priced (fun _ => qCost n) (simBody n)) .idle
    (eprSim n).initReg
  simp only [ProgE.erase_priced] at h
  exact h

/-- **Running time of the costed EPR simulator program**: each step costs at most
`2 * (qCost n + 3)`. -/
theorem simP.timeBound_timed (qCost : ℕ → ℕ) (n : ℕ) :
    (simP.timed qCost n).TimeBound
      (fun p => ProgE.Bound Costed.weight p (qCost n + 3) fun _ => True)
      (2 * (qCost n + 3)) (2 * (qCost n + 3)) :=
  QProg.loopQSimQ.timeBound_timed trivial fun s _ => by
    simp only [ProgE.priced, ProgE.tick, ProgE.Bound, Costed.weight]
    refine ⟨by omega, fun _ => ?_⟩
    rw [ProgE.bound_costed, show qCost n + 3 - qCost n = 3 by omega]
    exact simBody_bound n s

end Insecure

end CatCrypt.Crypto.Party.Protocols.QOTP

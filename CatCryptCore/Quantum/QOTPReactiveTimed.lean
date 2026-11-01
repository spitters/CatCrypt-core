/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QSimTimed

/-!
# Running time of the simulator of the reactive quantum one-time pad

The costed form of the simulator `qotpSim n` of `QOTPReactive.lean`: a real event is translated
at no cost, and on the ideal output `aborted` the twirl of the interface register costs a tick of
`twirlCost n` units and one operation. No module imports this file.

Search words: quantum one-time pad, simulator, time certificate, cost of a twirl.

## Main definitions

* `QOTPReactive.simPostT`: the costed translation of an ideal output.
* `QOTPReactive.qotpSim.timed`: the costed simulator.

## Main results

* `QOTPReactive.qotpSim.erase_timed`: the costed simulator erases to `qotpSim n`.
* `QOTPReactive.qotpSim.timeBound_timed`: a `pre` step costs `0`, a `post` step at most
  `twirlCost n + 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.QOTPReactive

open _root_.Quantum CatCrypt.Crypto.Party CatCrypt.Quantum.ReactiveUC

/-- The costed translation of an ideal output: on `aborted`, a tick of `twirlCost n` units and
the twirl of the interface register. -/
noncomputable def simPostT (twirlCost : ℕ → ℕ) (n : ℕ) : IOut → QTreeT (Reg n) (Unit × Out)
  | .leak _ => .ret ((), .sent)
  | .received => .ret ((), .received)
  | .aborted =>
    ProgE.tick (twirlCost n) ((QTreeT.opE (twirlOp n)).bind fun _ => .ret ((), .aborted))
  | .ignored => .ret ((), .ignored)

/-- **The costed simulator of the quantum one-time pad**, with the cost `twirlCost n` of the
twirl. -/
noncomputable def qotpSim.timed (twirlCost : ℕ → ℕ) (n : ℕ) :
    QSim.Timed Unit Event Out IEvent IOut (2 ^ n) where
  init := ()
  pre _ e := .ret ((), simEvent e)
  post _ o := simPostT twirlCost n o

/-- **Erasure of the costed simulator**: it erases to `qotpSim n`. -/
theorem qotpSim.erase_timed (twirlCost : ℕ → ℕ) (n : ℕ) :
    (qotpSim.timed twirlCost n).Erases _root_.id (qotpSim n) := by
  refine ⟨rfl, fun _ e => ?_, fun _ o => ?_⟩
  · simp [QSim.Timed.erase, qotpSim.timed, qotpSim]
  · cases o <;>
      simp [QSim.Timed.erase, qotpSim.timed, simPostT, qotpSim, simPost, QTreeT.erase_bind]

/-- **Running time of the costed simulator**: a `pre` step costs `0`, a `post` step at most
`twirlCost n + 1`, a tick for the twirl and the twirl itself. -/
theorem qotpSim.timeBound_timed (twirlCost : ℕ → ℕ) (n : ℕ) :
    (qotpSim.timed twirlCost n).TimeBound (fun _ => True) 0 (twirlCost n + 1) := by
  refine ⟨trivial, fun _ _ _ => trivial, fun _ o _ => ?_⟩
  cases o with
  | aborted =>
    simp only [qotpSim.timed, simPostT, ProgE.tick, ProgE.Bound, Costed.weight]
    refine ⟨by omega, fun _ => ?_⟩
    rw [show twirlCost n + 1 - twirlCost n = 1 + 0 by omega]
    exact ProgE.Bound.bind ((QTreeT.bound_opE _).mono le_rfl fun _ _ => trivial)
  | _ => trivial

end CatCrypt.Quantum.QOTPReactive

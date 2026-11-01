/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.LoopTimed
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# `derive_simulator` on a loop simulator

A fixture of `derive_simulator` at a simulator whose multi-call simulator is a loop of a party
program (`Prog.loopMulti`) behind a definition: each iteration receives an outer event, calls
the subroutine twice and emits an outer output. The command reads the leaf as the costed loop
`Prog.loopMulti.timed` on costed residual programs and takes its graded time from
`Prog.loopMulti.timeBoundGraded_timed`, giving `twoCallSim.timeBoundGraded_timed`.

A second fixture, `logSim`, is a loop whose state grows with the activations: each iteration
records the event in a list.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSimulatorLoopTest

open CatCrypt.Crypto.Party CatCrypt.Crypto.UCTransparent Prog

/-- An iteration of the fixture: receive `e`, call with `e` and with `e + a₁`, and output
`f e a₁ a₂`. -/
def twoCallBody (f : ℕ → ℕ → ℕ → ℕ) (s : Unit) : Prog (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) Unit :=
  ProgE.bind recvO fun e => call e fun a₁ => call (e + a₁) fun a₂ =>
    ProgE.bind (outE (f e a₁ a₂)) fun _ => .ret s

/-- The fixture loop as a multi-call simulator with fuel `2`. -/
noncomputable def twoCallProt (f : ℕ → ℕ → ℕ → ℕ) :
    MultiHybrid (Prog (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) Unit) ℕ ℕ ℕ ℕ :=
  loopMulti (twoCallBody f) () 2

/-- The fixture simulator. -/
noncomputable def twoCallSim (V W : PubView ℕ ℕ) (f : ℕ → ℕ → ℕ → ℕ)
    (h : (twoCallProt f).Opaque V W) : Simulator ℕ ℕ ℕ ℕ V W :=
  Simulator.ofMultiHybrid (twoCallProt f) h

derive_simulator twoCallSim

/-- An iteration of the growing fixture: receive `e`, call with `e`, output the answer plus the
number of events recorded, and record `e`. -/
def logBody (s : List ℕ) : Prog (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) (List ℕ) :=
  ProgE.bind recvO fun e => call e fun a =>
    ProgE.bind (outE (a + s.length)) fun _ => .ret (e :: s)

/-- The growing fixture loop as a multi-call simulator with fuel `1`. -/
noncomputable def logProt : MultiHybrid (Prog (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) (List ℕ)) ℕ ℕ ℕ ℕ :=
  loopMulti logBody [] 1

/-- The growing fixture simulator. -/
noncomputable def logSim (V W : PubView ℕ ℕ) (h : logProt.Opaque V W) :
    Simulator ℕ ℕ ℕ ℕ V W :=
  Simulator.ofMultiHybrid logProt h

derive_simulator logSim

end CatCrypt.Tactics.DeriveSimulatorLoopTest

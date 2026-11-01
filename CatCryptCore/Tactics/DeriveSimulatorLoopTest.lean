/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.LoopTimed
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.PartyDerive

/-!
# `derive_simulator` on a loop simulator

A fixture of `derive_simulator` at a simulator whose multi-call simulator is a loop of a party
program (`Prog.loopMulti`) behind a definition: each iteration receives an outer event, calls
the subroutine twice and emits an outer output. The command reads the leaf as the costed loop
`Prog.loopMulti.timed` on costed residual programs and takes its graded time from
`Prog.loopMulti.timeBoundGraded_timed`, giving `twoCallSim.timeBoundGraded_timed`.

A second fixture, `logSim`, is a loop whose state grows with the activations: each iteration
records the event in a list.

A third fixture, `echoSim`, is a loop whose work in an activation is the size of the answer it
receives: each iteration calls with the event and, on the answer `a`, works `a` units before it
outputs `a`. The command also proves the size-graded time theorem
`echoSim.timeBoundSized_timed`, and `echoSim_certificate` bounds each activation by `8` plus the
answer it handles.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSimulatorLoopTest

open CatCrypt.Core CatCrypt.Crypto.Party CatCrypt.Crypto.UCTransparent Prog

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

/-- The costed body of the growing fixture: an iteration charges the length of the list. -/
noncomputable def logBodyT : List ℕ → ProgE (Costed (SPComp ℕ)) (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) (List ℕ) :=
  ProgE.priced List.length logBody

/-- An iteration of the growing fixture takes four units and records one event. -/
theorem logBody_bound (s : List ℕ) :
    ProgE.Bound (fun _ => 1) (logBody s) 4 (fun s' => s'.length ≤ s.length + 1) := by
  party_derive

/-- The costed body of the growing fixture erases to `logBody`. -/
theorem logBodyT_erase (s : List ℕ) : ProgE.eraseT ProgE.sampleTree (logBodyT s) = logBody s :=
  ProgE.eraseT_sampleTree_priced _ _ s (by
    unfold logBody
    exact ProgE.allOps_bind allOps_recvO fun _ => allOps_call fun _ =>
      ProgE.allOps_bind allOps_outE fun _ => trivial)

/-- The graded bound of the growing fixture: after `i` iterations the list holds at most `i`
events, and the `i`-th iteration costs at most `4 + i`. -/
theorem logBodyT_loopBoundGraded :
    ProgE.LoopBoundGraded (ProgE.weightT ProgE.sampleTree) logBodyT []
      (fun i s => s.length ≤ i) 4 1 :=
  ProgE.LoopBoundGraded.sampleTree
    (ProgE.priced_loopBoundGraded List.length logBody [] (fun i s => s.length ≤ i) 4 1 0
      (by simp) (fun i s hs => by omega)
      (fun i s hs => (logBody_bound s).mono le_rfl fun s' hs' => by omega))

/-- **Time certificate of the growing fixture**: its costed form erases to `logSim` and its
`j`-th activation costs at most `9 + 2 j`. -/
theorem logSim_certificate (V W : PubView ℕ ℕ) (h : logProt.Opaque V W) :
    (logSim.timed V W _ ProgE.sampleTree logBodyT).Erases (logSim V W h) ∧
      (logSim.timed V W _ ProgE.sampleTree logBodyT).TimeBoundGraded 9 2 :=
  ⟨logSim.erase_timed V W h _ _ _ logBodyT_erase,
    logSim.timeBoundGraded_timed V W _ _ _ logBodyT_loopBoundGraded⟩

/-- An iteration of the sized fixture: receive `e`, call with `e`, and output the answer. -/
def echoBody (s : Unit) : Prog (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) Unit :=
  ProgE.bind recvO fun e => call e fun a => ProgE.bind (outE a) fun _ => .ret s

/-- The sized fixture loop as a multi-call simulator with fuel `1`. -/
noncomputable def echoProt : MultiHybrid (Prog (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) Unit) ℕ ℕ ℕ ℕ :=
  loopMulti echoBody () 1

/-- The sized fixture simulator. -/
noncomputable def echoSim (V W : PubView ℕ ℕ) (h : echoProt.Opaque V W) :
    Simulator ℕ ℕ ℕ ℕ V W :=
  Simulator.ofMultiHybrid echoProt h

derive_simulator echoSim

/-- The costed body of the sized fixture: on the answer `a`, a tick of `a` units before the
output. -/
def echoBodyT (s : Unit) : ProgE (Costed (SPComp ℕ)) (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) Unit :=
  .recv fun
    | .inl e => .send (.inl e) (.recv fun
        | .inr a => ProgE.tick a (.send (.inr a) (.ret s))
        | .inl _ => .fail)
    | .inr _ => .fail

/-- The costed body of the sized fixture erases to `echoBody`. -/
theorem echoBodyT_erase (s : Unit) :
    ProgE.eraseT ProgE.sampleTree (echoBodyT s) = echoBody s := by
  simp only [ProgE.eraseT, echoBodyT, echoBody, recvO, call, callK, outE, ProgE.bind,
    ProgE.erase, ProgE.tick, ProgE.mapOp]
  congr 1
  funext x
  rcases x with e | e
  · simp only [ProgE.bind, ProgE.erase, ProgE.mapOp]
    congr 2
    funext y
    rcases y with a | a <;> rfl
  · rfl

/-- The size-graded bound of the sized fixture: an iteration costs four units and, on the answer
`a`, the budget `a` of its activation. -/
theorem echoBodyT_loopBoundSized :
    ProgE.LoopBoundSized (ProgE.weightT ProgE.sampleTree) echoBodyT () (fun _ _ => True) 4 0
      (Sum.elim (fun e => 1 * (fun _ => 0) e) (fun x => 1 * (fun a => a) x)) := by
  refine ⟨trivial, fun i s _ => ?_⟩
  refine ⟨by omega, fun x => ?_⟩
  rcases x with e | e
  · refine ⟨by omega, by omega, fun y => ?_⟩
    rcases y with a | a
    · trivial
    · refine ⟨?_, fun _ => ⟨?_, trivial⟩⟩
      · simp [ProgE.weightT, ProgE.runT, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      · simp [ProgE.weightT, ProgE.runT, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  · trivial

/-- **Time certificate of the sized fixture**: its costed form erases to `echoSim`, and an
activation on an outer event costs at most `8`, one on the answer `a` at most `8 + a`. -/
theorem echoSim_certificate (V W : PubView ℕ ℕ) (h : echoProt.Opaque V W) :
    (echoSim.timed V W _ ProgE.sampleTree echoBodyT).Erases (echoSim V W h) ∧
      (echoSim.timed V W _ ProgE.sampleTree echoBodyT).TimeBoundSized (fun _ => 0) (fun a => a)
        8 0 1 :=
  ⟨echoSim.erase_timed V W h _ _ _ echoBodyT_erase,
    echoSim.timeBoundSized_timed V W _ _ _ echoBodyT_loopBoundSized⟩

end CatCrypt.Tactics.DeriveSimulatorLoopTest

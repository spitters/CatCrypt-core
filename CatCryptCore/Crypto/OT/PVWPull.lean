/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.PVWHonest
public import CatCryptCore.Crypto.UCWake
public import CatCryptCore.Crypto.UCChannelLift

/-!
# The PVW dual-mode OT with both parties honest, in pull form

**Ideal functionality.** `FOTSched otChoose` (`OT/FOTSched.lean`): the scheduled transfer of `m`
message pairs, with the sender and the receiver on the honest port and the scheduler on the
adversary port. A receiver activation outputs the value the adversary has delivered, once.

**Real protocol.** `pvwPull crs code decode`: the two parties of the Peikert–Vaikuntanathan–Waters
dual-mode OT (`OT/PVWOTSquare.lean`) with the CRS `crs` over the secure channel
`FChan ChannelCap.secure`, closed by the silent wake `Sys.wakeCloseSilent`. The receiver with
choices `c` draws `r` and sends `recvMsg crs c r`; the sender, once it holds the key and its
message pairs `x`, draws `ρ` and sends `senderMsg crs code k x ρ`. A delivery of the channel
activates the parties, which read the channel, in the same activation; the answer to the
adversary is the delivery's own answer. The receiver decrypts the ciphertexts with
`recvOut decode c r`, stores the result, and outputs it once at its next activation (pull form).
Every sender activation outputs `false`.

**Simulator.** `(idSim InEv InOut).tensor simP`: the honest port is forwarded to
`FOTSched otChoose`, and `simP` runs on the adversary port. `simP` keeps the stage of the message
in flight and the channel's cursor; it obtains the presence of the inputs by a poll of the
scheduler, answers the channel's `poll`, `deliver` and `drop` from these, and at the delivery of
the ciphertexts issues `deliverRecv`. It never issues `deliverSend`.

**Bound.** `0` for every CRS when `decode` inverts `code` (`pvwPull_realizesSim`): the channel
shows only the presence of a message, and the stored output is `otChoose x c` by correctness
(`recvOut_senderMsg`).

## Main definitions

* `Sys.wakeCloseSilent`: the wake closure whose delivery answers on the adversary port.
* `partyP`, `realP`, `pvwPull`: the parties in pull form and the protocol.
* `PStage`, `SStP`, `simP`: the simulator on the adversary port.

## Main results

* `pvwPull_realizesSim`: both parties honest, pull form, distance `0`, behind
  `Simulator.tensor (idSim InEv InOut) simP`.
* `pvwPull_idleAt`, `simP_idleAt`: the idle adversary event, for `RealizesSim.modular_withChan`.
-/

@[expose] public section

set_option autoImplicit false

/-! ## The silent wake

Upstream target: `CatCryptCore/Crypto/UCWake.lean`. -/

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

namespace Sys

variable {τ EH EA OH OA W : Type}

/-- **The silent wake closure** of `R` with the delivery map `dlv`: an honest event is an honest
event of `R`; an adversary event `a` with `dlv a = none` is an adversary event of `R`; an
adversary event `a` with `dlv a = some w` is a step of `R` on `a` followed, in the same
activation, by a step of `R` on the wake `w`, whose output is discarded: the answer is the answer
of `R` to `a`. -/
noncomputable def wakeCloseSilent (R : Sys τ ((EH ⊕ W) ⊕ EA) (OH ⊕ OA)) (dlv : EA → Option W) :
    Sys τ (EH ⊕ EA) (OH ⊕ OA) where
  init := R.init
  step t e := match e with
    | .inl h => R.step t (.inl (.inl h))
    | .inr a => match dlv a with
      | none => R.step t (.inr a)
      | some w => SPComp.bind (R.step t (.inr a)) fun p =>
          SPComp.map (fun q => (q.1, p.2)) (R.step p.1 (.inl (.inr w)))

variable (R : Sys τ ((EH ⊕ W) ⊕ EA) (OH ⊕ OA)) (dlv : EA → Option W) (t : τ)

/-- Unfolding lemma of `Sys.wakeCloseSilent`: an honest event. -/
theorem wakeCloseSilent_step_inl (h : EH) :
    (R.wakeCloseSilent dlv).step t (.inl h) = R.step t (.inl (.inl h)) := rfl

/-- Unfolding lemma of `Sys.wakeCloseSilent`: an adversary event that is not a delivery. -/
theorem wakeCloseSilent_step_none (a : EA) (ha : dlv a = none) :
    (R.wakeCloseSilent dlv).step t (.inr a) = R.step t (.inr a) := by
  simp [wakeCloseSilent, ha]

/-- Unfolding lemma of `Sys.wakeCloseSilent`: a delivery to `w`. -/
theorem wakeCloseSilent_step_some (a : EA) (w : W) (ha : dlv a = some w) :
    (R.wakeCloseSilent dlv).step t (.inr a) =
      SPComp.bind (R.step t (.inr a)) fun p =>
        SPComp.map (fun q => (q.1, p.2)) (R.step p.1 (.inl (.inr w))) := by
  simp [wakeCloseSilent, ha]

end Sys

end CatCrypt.Crypto.UCTransparent

namespace CatCrypt.Crypto.OT.PVWPull

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.Relational CatCrypt.Crypto.OT.PVW
open CatCrypt.Crypto.OT.PVWHonest
open CatCrypt.NonUniform CatCrypt.Examples
open CatCrypt.Crypto.Choreography (ChannelCap)
open CatCrypt.Crypto.UCCoupling (stepPost realizes_zero_of_coupling)
open scoped ENNReal

variable {gp : GroupParam} {m : ℕ} {M : Type}

/-! ## The parties in pull form -/

variable (gp m M) in
/-- The state of the parties in pull form: the state of the PVW parties and the receiver's stored
output. -/
abbrev QSt := PSt gp m M × Option (Fin m → M)

/-- The first step of an activation of the parties in pull form: a receiver activation after the
receiver's choice outputs the stored output and clears it; every other event is the step of
`pStart`, the stored output unchanged. -/
noncomputable def qStart (crs : CRS gp) (code : M → gp.G) (st : QSt gp m M) (e : InEv m M ⊕ Unit) :
    SPComp (QSt gp m M × (ChanHEv (V gp m) ⊕ InOut m M)) :=
  match e, st.1.rc with
  | .inl (.inr _), some _ => SPComp.pure ((st.1, none), .inr (.inr st.2))
  | e, _ => SPComp.map (fun p => ((p.1, st.2), p.2)) (pStart crs code st.1 e)

/-- The step of the parties in pull form on an answer of the channel: received ciphertexts are
decrypted and stored, and the activation outputs `false`; every other answer is the step of
`pResume`, the stored output unchanged. -/
noncomputable def qResume (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (st : QSt gp m M) (o : ChanHOut (V gp m)) :
    SPComp (QSt gp m M × (ChanHEv (V gp m) ⊕ InOut m M)) :=
  match st.1.ph, o with
  | .recv, .got (some (.inr ct)) =>
    SPComp.pure (({ st.1 with done := true, ph := .idle },
      st.1.rc.map fun p => recvOut decode p.1 p.2 ct), .inr (.inl false))
  | _, o => SPComp.map (fun p => ((p.1, st.2), p.2)) (pResume crs code decode st.1 o)

/-- **The PVW parties in pull form** with the CRS `crs` over the channel: the parties of
`partyH`, except that the receiver stores the decrypted ciphertexts and outputs them once at its
next activation. -/
noncomputable def partyP (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) :
    MultiHybrid (QSt gp m M) (InEv m M ⊕ Unit) (InOut m M) (ChanHEv (V gp m))
      (ChanHOut (V gp m)) where
  init := (PSt.init, none)
  fuel := 1
  start := qStart crs code
  resume := qResume crs code decode
  finish st _ := SPComp.pure (({ st.1 with ph := .idle }, st.2), .inl false)
  start_noFail st e := by
    unfold qStart
    split
    · exact SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail ((partyH crs code decode).start_noFail _ _)
        fun _ => SPComp.pure_noFail _
  resume_noFail st o := by
    unfold qResume
    split
    · exact SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail ((partyH crs code decode).resume_noFail _ _)
        fun _ => SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The parties in pull form over the secure channel, before the wake closure: the parties on the
honest port with their wakes, the channel's adversary port forwarded. -/
noncomputable def realP (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) :
    Sys ((QSt gp m M × Unit) × ChanSt (V gp m)) ((InEv m M ⊕ Unit) ⊕ ChanAEv (V gp m))
      (InOut m M ⊕ ChanAOut (V gp m) Unit) :=
  ((partyP crs code decode).tensor
    (MultiHybrid.idSim (ChanAEv (V gp m)) (ChanAOut (V gp m) Unit))).withSub (chanH gp m)

/-- **The PVW protocol with both parties honest, in pull form**: `realP` closed by the silent
wake, so that a delivery of the channel activates the parties and answers the adversary with the
delivery's own answer. -/
noncomputable def pvwPull (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) :
    Sys ((QSt gp m M × Unit) × ChanSt (V gp m)) (InEv m M ⊕ ChanAEv (V gp m))
      (InOut m M ⊕ ChanAOut (V gp m) Unit) :=
  (realP crs code decode).wakeCloseSilent dlvH

/-! ## The simulator on the adversary port -/

/-- The stage of the message in flight, in pull form. -/
inductive PStage where
  /-- The key is not yet delivered: in transit once the receiver has chosen. -/
  | kWait
  /-- The key is dropped. -/
  | kLost
  /-- The key is received; the ciphertexts are in transit once the sender has its input. -/
  | cWait
  /-- The ciphertexts are dropped. -/
  | cLost
  /-- The ciphertexts are received. -/
  | fin
  deriving DecidableEq

/-- Whether the sender has received the key. -/
def PStage.keyGot : PStage → Bool
  | .kWait | .kLost => false
  | _ => true

/-- The number of messages in transit at the stage `g`, given whether the sender's input (`a`)
and the receiver's choice (`b`) have arrived. -/
def simLenP (g : PStage) (a b : Bool) : ℕ :=
  match g with
  | .kWait => if b then 1 else 0
  | .cWait => if a then 1 else 0
  | _ => 0

/-- The stage after a delivery (`drop = false`) or a drop of the channel. -/
def nextP (drop : Bool) (g : PStage) (a b : Bool) : PStage :=
  match g with
  | .kWait => if b then (if drop then .kLost else .cWait) else .kWait
  | .cWait => if a then (if drop then .cLost else .fin) else .cWait
  | g => g

/-- The awaited answer of the simulator's activation. -/
inductive QPh where
  /-- No call is pending. -/
  | idle
  /-- The input status, for a poll of the channel. -/
  | aPoll
  /-- The input status, for a delivery (`false`) or a drop (`true`) of the channel. -/
  | aDel (drop : Bool)
  /-- The acknowledgement of the delivery of the receiver's output. -/
  | aRecv

/-- The state of the simulator: the stage of the message in flight, the channel's cursor and the
phase. -/
structure SStP where
  /-- The stage of the message in flight. -/
  g : PStage
  /-- The number of messages shown to the adversary. -/
  cur : ℕ
  /-- The phase of the activation. -/
  ph : QPh

variable (gp m) in
/-- The decisions of the simulator. -/
abbrev PDec := SchedEv ⊕ ChanAOut (V gp m) Unit

/-- The simulator's first step. -/
def simPStart (s : SStP) : ChanAEv (V gp m) → SStP × PDec gp m
  | .idle => (s, .inr .ack)
  | .poll => ({ s with ph := .aPoll }, .inl .poll)
  | .deliver => ({ s with ph := .aDel false }, .inl .poll)
  | .drop => ({ s with ph := .aDel true }, .inl .poll)
  | .tamper _ => (s, .inr .ack)

/-- The simulator's decision after the input status `(a, b)` at a delivery (`d = false`) or a
drop: the delivery of the ciphertexts issues `deliverRecv`. -/
def delDec (d : Bool) (s : SStP) (a b : Bool) : SStP × PDec gp m :=
  match d, s.g, a with
  | false, .cWait, true => (⟨.fin, s.cur - 1, .aRecv⟩, .inl .deliverRecv)
  | _, _, _ => (⟨nextP d s.g a b, s.cur - 1, .idle⟩, .inr .ack)

/-- The simulator's step on an answer of the scheduler. -/
def simPResume (s : SStP) : SchedOut → SStP × PDec gp m
  | .status a b => match s.ph with
    | .aPoll =>
      ({ s with cur := min (s.cur + 1) (simLenP s.g a b), ph := .idle },
        .inr (.leak (if s.cur < simLenP s.g a b then some (.inr ()) else none)))
    | .aDel d => delDec d s a b
    | _ => ({ s with ph := .idle }, .inr .ack)
  | .ack => ({ s with ph := .idle }, .inr .ack)

variable (gp m) in
/-- **The simulator on the adversary port** over the scheduler of `FOTSched otChoose`. It answers
the channel's adversary events from the stage of the message in flight and the input status that
a poll of the scheduler reports, and issues `deliverRecv` at the delivery of the ciphertexts. -/
noncomputable def simP : MultiHybrid SStP (ChanAEv (V gp m)) (ChanAOut (V gp m) Unit) SchedEv
    SchedOut where
  init := ⟨.kWait, 0, .idle⟩
  fuel := 1
  start s e := SPComp.pure (simPStart s e)
  resume s o := SPComp.pure (simPResume s o)
  finish s _ := SPComp.pure ({ s with ph := .idle }, .ack)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-! ## The coupling -/

/-- The messages in transit at the stage `g`. -/
@[simp] def queueP (crs : CRS gp) (code : M → gp.G) (xo : Option (Fin m → M × M))
    (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar))) (g : PStage) (ρ : SRand gp m) :
    List (V gp m) :=
  match g with
  | .kWait => keyMsg crs rc
  | .cWait => ctMsg crs code xo rc ρ
  | _ => []

/-- The number of messages in transit is `simLenP` once the receiver has chosen at every stage
past the key. -/
theorem queueP_length (crs : CRS gp) (code : M → gp.G) (xo : Option (Fin m → M × M))
    (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar))) (g : PStage) (ρ : SRand gp m)
    (h1 : g ≠ .kWait → rc.isSome) :
    (queueP crs code xo rc g ρ).length = simLenP g xo.isSome rc.isSome := by
  cases g <;> rcases xo with _ | x <;> rcases rc with _ | ⟨c, r⟩ <;> simp_all [keyMsg, ctMsg,
    simLenP]

/-- The next message not yet shown, on the secure channel, is a bare presence notice exactly
when the cursor is below the number of messages in transit. -/
theorem pollLeak_secure (l : List (V gp m)) (k : ℕ) :
    FChan.pollLeak ChannelCap.secure (fun _ => ()) ⟨l, k, []⟩ =
      if k < l.length then some (.inr ()) else none := by
  simp [FChan.pollLeak, ChannelCap.secure, List.head?_drop, List.getElem?_map]
  split_ifs <;> simp_all
  rfl

/-- The state of the protocol at the stage `g`, with the inputs `xo` and `rc`, the sender's
randomness `ρ`, the cursor `cur` and the receiver's stored output `ob`. -/
def realOfP (crs : CRS gp) (code : M → gp.G) (xo : Option (Fin m → M × M))
    (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar))) (g : PStage) (ρ : SRand gp m)
    (cur : ℕ) (ob : Option (Fin m → M)) : (QSt gp m M × Unit) × ChanSt (V gp m) :=
  (((⟨xo, if g.keyGot then rc.map (fun p => recvMsg crs p.1 p.2) else none,
      g.keyGot && xo.isSome, rc, decide (g = .fin), .idle⟩, ob), ()),
    ⟨queueP crs code xo rc g ρ, cur, []⟩)

/-- The state of the simulator over `FOTSched otChoose` at the stage `g`. -/
def idealOfP (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : PStage) (cur : ℕ) (ob : Option (Fin m → M)) :
    (Unit × SStP) × SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M) :=
  (((), ⟨g, cur, .idle⟩), ⟨xo, rc.map Prod.fst, ob, decide (g = .fin), false⟩)

/-- The reachable stages: the key is sent once the receiver has chosen, the ciphertexts once the
sender has its input, the cursor is at most the number of messages in transit, and an output is
stored only after the ciphertexts are received. -/
def WFP (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : PStage) (cur : ℕ) (ob : Option (Fin m → M)) : Prop :=
  (g ≠ .kWait → rc.isSome) ∧ (g = .cLost ∨ g = .fin → xo.isSome) ∧
    cur ≤ simLenP g xo.isSome rc.isSome ∧ (ob.isSome → g = .fin)

/-- The relation of the protocol's states and the simulator's states over `FOTSched otChoose`. -/
def HRelP (crs : CRS gp) (code : M → gp.G) (t : (QSt gp m M × Unit) × ChanSt (V gp m))
    (u : (Unit × SStP) × SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M)) : Prop :=
  ∃ xo rc g ρ cur ob, t = realOfP crs code xo rc g ρ cur ob ∧ u = idealOfP xo rc g cur ob ∧
    WFP xo rc g cur ob

/-- Unfolding lemma of `realP`: a step on an input or a wake. -/
theorem realP_step_inl (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) (st : QSt gp m M)
    (u : Unit) (ch : ChanSt (V gp m)) (e : InEv m M ⊕ Unit) :
    (realP crs code decode).step ((st, u), ch) (.inl e) =
      SPComp.map (fun p => (((p.1.1, u), p.1.2), Sum.inl p.2))
        ((partyP crs code decode).stepFuel FChan.honSys 1 (st, ch) e) := by
  rw [realP, MultiHybrid.tensor_withSub_step_inl _ _ (chanH gp m) FChan.honSys (fun _ _ => rfl)]
  rfl

/-- Unfolding lemma of `realP`: a step on an adversary event of the channel. -/
theorem realP_step_inr (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) (st : QSt gp m M)
    (u : Unit) (ch : ChanSt (V gp m)) (a : ChanAEv (V gp m)) :
    (realP crs code decode).step ((st, u), ch) (.inr a) =
      SPComp.pure (((st, u), (FChan.advStep ChannelCap.secure (fun _ => ()) ch a).1),
        .inr (FChan.advStep ChannelCap.secure (fun _ => ()) ch a).2) := by
  rw [realP, MultiHybrid.tensor_withSub_step_inr _ _ (chanH gp m) (FChan.advSys _ _)
    (fun _ _ => rfl), MultiHybrid.idSim_stepFuel]
  simp [FChan.advSys, SPComp.map, SPComp.pure_bind]

variable (gp m M) in
/-- The simulated ideal system: `(idSim InEv InOut).tensor simP` over `FOTSched otChoose`. -/
noncomputable abbrev idealP :
    Sys ((Unit × SStP) × SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M))
      (InEv m M ⊕ ChanAEv (V gp m)) (InOut m M ⊕ ChanAOut (V gp m) Unit) :=
  ((MultiHybrid.idSim (InEv m M) (InOut m M)).tensor (simP gp m)).withSub (FOTSched otChoose)

/-- Unfolding lemma of the simulated ideal system: a step on an input. -/
theorem idealP_step_inl (s : SStP) (t : SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M))
    (e : InEv m M) :
    (idealP gp m M).step (((), s), t) (.inl e) =
      SPComp.map (fun q => ((((), s), q.1), Sum.inl q.2))
        ((Sys.ofPorts FOTSched.sendSys FOTSched.recvSys).step t e) := by
  rw [idealP, MultiHybrid.tensor_withSub_step_inl _ _ _
    (Sys.ofPorts FOTSched.sendSys FOTSched.recvSys) (fun _ _ => rfl), MultiHybrid.idSim_stepFuel]
  simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- Unfolding lemma of the simulated ideal system: a step on an adversary event of the
channel. -/
theorem idealP_step_inr (s : SStP) (t : SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M))
    (a : ChanAEv (V gp m)) :
    (idealP gp m M).step (((), s), t) (.inr a) =
      SPComp.map (fun p => ((((), p.1.1), p.1.2), Sum.inr p.2))
        ((simP gp m).stepFuel (FOTSched.schedSys otChoose) 1 (s, t) a) := by
  rw [idealP, MultiHybrid.tensor_withSub_step_inr _ _ _ (FOTSched.schedSys otChoose)
    (fun _ _ => rfl)]
  rfl

/-- The step on a drop of the channel. -/
theorem step_drop (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : PStage) (ρ : SRand gp m) (cur : ℕ) (ob : Option (Fin m → M))
    (hwf : WFP xo rc g cur ob) :
    rHoare eqPre ((pvwPull crs code decode).step (realOfP crs code xo rc g ρ cur ob) (.inr .drop))
      ((idealP gp m M).step (idealOfP xo rc g cur ob) (.inr .drop))
      (stepPost (HRelP crs code)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  rw [pvwPull, Sys.wakeCloseSilent_step_none _ _ _ _ rfl]
  refine couple_eq (realOfP crs code xo rc (nextP true g xo.isSome rc.isSome) ρ (cur - 1) ob)
    (idealOfP xo rc (nextP true g xo.isSome rc.isSome) (cur - 1) ob) (.inr .ack) ?_ ?_
    ⟨xo, rc, _, ρ, _, ob, rfl, rfl, ?_⟩
  · cases g
    case kWait =>
      rcases rc with _ | ⟨c, r⟩ <;>
        simp [realOfP, realP_step_inr, FChan.advStep, FChan.popTo, keyMsg, nextP, PStage.keyGot,
          ChannelCap.secure]
    case cWait =>
      obtain ⟨⟨c, r⟩, rfl⟩ : ∃ p, rc = some p := Option.isSome_iff_exists.mp (h1 (by simp))
      rcases xo with _ | x <;>
        simp [realOfP, realP_step_inr, FChan.advStep, FChan.popTo, ctMsg, nextP, PStage.keyGot,
          ChannelCap.secure]
    all_goals
      simp [realOfP, realP_step_inr, FChan.advStep, FChan.popTo, nextP, ChannelCap.secure]
      rfl
  · cases g <;> simp only [idealOfP, idealP_step_inr, MultiHybrid.stepFuel, simP, simPStart,
      simPResume, delDec, nextP, MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep,
      SPComp.map, SPComp.pure_bind, Option.isSome_map] <;> (try split_ifs) <;> rfl
  · cases g <;> rcases xo with _ | x <;> rcases rc with _ | ⟨c, r⟩ <;>
      simp_all [WFP, simLenP, nextP]

/-- The step on an adversary event of the channel other than a delivery. -/
theorem step_quiet (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : PStage) (ρ : SRand gp m) (cur : ℕ) (ob : Option (Fin m → M))
    (hwf : WFP xo rc g cur ob) (a : ChanAEv (V gp m)) (ha : dlvH a = none) :
    rHoare eqPre ((pvwPull crs code decode).step (realOfP crs code xo rc g ρ cur ob) (.inr a))
      ((idealP gp m M).step (idealOfP xo rc g cur ob) (.inr a)) (stepPost (HRelP crs code)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  rw [pvwPull, Sys.wakeCloseSilent_step_none _ _ _ _ ha]
  cases a with
  | idle =>
    refine couple_eq (realOfP crs code xo rc g ρ cur ob) (idealOfP xo rc g cur ob) (.inr .ack)
      ?_ ?_ ⟨xo, rc, g, ρ, cur, ob, rfl, rfl, h1, h2, h3, h4⟩
    · simp [realOfP, realP_step_inr, FChan.advStep]
    · simp [idealOfP, idealP_step_inr, MultiHybrid.stepFuel, simP, simPStart,
        MultiHybrid.drive, SPComp.map, SPComp.pure_bind]
  | poll =>
    refine couple_eq (realOfP crs code xo rc g ρ (min (cur + 1) (simLenP g xo.isSome rc.isSome))
        ob)
      (idealOfP xo rc g (min (cur + 1) (simLenP g xo.isSome rc.isSome)) ob)
      (.inr (.leak (if cur < simLenP g xo.isSome rc.isSome then some (.inr ()) else none))) ?_ ?_
      ⟨xo, rc, g, ρ, _, ob, rfl, rfl, h1, h2, min_le_right _ _, h4⟩
    · simp only [realOfP, realP_step_inr, FChan.advStep, pollLeak_secure,
        queueP_length crs code xo rc g ρ h1]
    · simp [idealOfP, idealP_step_inr, MultiHybrid.stepFuel, simP, simPStart, simPResume,
        MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
  | deliver => simp [dlvH] at ha
  | drop => exact step_drop crs code decode xo rc g ρ cur ob ⟨h1, h2, h3, h4⟩
  | tamper v =>
    refine couple_eq (realOfP crs code xo rc g ρ cur ob) (idealOfP xo rc g cur ob) (.inr .ack)
      ?_ ?_ ⟨xo, rc, g, ρ, cur, ob, rfl, rfl, h1, h2, h3, h4⟩
    · simp [realOfP, realP_step_inr, FChan.advStep, ChannelCap.secure]
    · simp [idealOfP, idealP_step_inr, MultiHybrid.stepFuel, simP, simPStart,
        MultiHybrid.drive, SPComp.map, SPComp.pure_bind]

/-- The real side of a delivery with no message in transit: the wake reads nothing. -/
theorem real_deliver_empty (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : PStage) (ρ : SRand gp m) (cur : ℕ) (ob : Option (Fin m → M))
    (hk : ¬(g = .kWait ∧ rc.isSome)) (hc : ¬(g = .cWait ∧ xo.isSome)) :
    SPComp.bind ((realP crs code decode).step (realOfP crs code xo rc g ρ cur ob) (.inr .deliver))
        (fun p => SPComp.map (fun q => (q.1, p.2))
          ((realP crs code decode).step p.1 (.inl (.inr ())))) =
      SPComp.pure (realOfP crs code xo rc g ρ (cur - 1) ob, .inr .ack) := by
  cases g
  case kWait =>
    obtain rfl : rc = none := by simpa using hk
    simp [realOfP, keyMsg, realP_step_inr, realP_step_inl, FChan.advStep, FChan.popTo, partyP,
      qStart, qResume, pStart, pResume, MultiHybrid.stepFuel, MultiHybrid.drive, FChan.honSys,
      FChan.honStep, SPComp.map, SPComp.pure_bind]
  case cWait =>
    obtain rfl : xo = none := by simpa using hc
    simp [realOfP, ctMsg, realP_step_inr, realP_step_inl, FChan.advStep, FChan.popTo, partyP,
      qStart, qResume, pStart, pResume, MultiHybrid.stepFuel, MultiHybrid.drive, FChan.honSys,
      FChan.honStep, SPComp.map, SPComp.pure_bind]
  all_goals
    simp [realOfP, realP_step_inr, realP_step_inl, FChan.advStep, FChan.popTo, partyP,
      qStart, qResume, pStart, pResume, MultiHybrid.stepFuel, MultiHybrid.drive, FChan.honSys,
      FChan.honStep, SPComp.map, SPComp.pure_bind]

/-- The ideal side of a delivery with no message in transit. -/
theorem ideal_deliver_empty (xo : Option (Fin m → M × M))
    (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar))) (g : PStage) (cur : ℕ)
    (ob : Option (Fin m → M)) (hk : ¬(g = .kWait ∧ rc.isSome)) (hc : ¬(g = .cWait ∧ xo.isSome)) :
    (idealP gp m M).step (idealOfP xo rc g cur ob) (.inr .deliver) =
      SPComp.pure (idealOfP xo rc g (cur - 1) ob, .inr .ack) := by
  have hd : delDec (gp := gp) (m := m) false ⟨g, cur, .aDel false⟩ xo.isSome
      (rc.map Prod.fst).isSome =
      (⟨g, cur - 1, .idle⟩, .inr .ack) := by
    cases g <;> simp_all [delDec, nextP]
  simp only [idealOfP, idealP_step_inr, MultiHybrid.stepFuel, simP, simPStart,
    MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, simPResume, hd, SPComp.map,
    SPComp.pure_bind]

/-- The step on a delivery of the channel, which wakes the parties. -/
theorem step_deliver (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (hcode : ∀ a, decode (code a) = a)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : PStage) (ρ : SRand gp m) (cur : ℕ) (ob : Option (Fin m → M))
    (hwf : WFP xo rc g cur ob) :
    rHoare eqPre
      ((pvwPull crs code decode).step (realOfP crs code xo rc g ρ cur ob) (.inr .deliver))
      ((idealP gp m M).step (idealOfP xo rc g cur ob) (.inr .deliver))
      (stepPost (HRelP crs code)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  rw [pvwPull, Sys.wakeCloseSilent_step_some (realP crs code decode) dlvH _ .deliver () rfl]
  by_cases hk : g = .kWait ∧ rc.isSome
  · obtain ⟨rfl, hrc⟩ := hk
    obtain ⟨⟨c, r⟩, rfl⟩ := Option.isSome_iff_exists.mp hrc
    obtain rfl : ob = none := by cases ob <;> simp_all
    have hI : (idealP gp m M).step (idealOfP xo (some (c, r)) .kWait cur none) (.inr .deliver) =
        SPComp.pure (idealOfP xo (some (c, r)) .cWait (cur - 1) none, .inr .ack) := by
      rcases xo with _ | x <;>
        simp [idealOfP, idealP_step_inr, MultiHybrid.stepFuel, simP, simPStart, simPResume,
          delDec, nextP, MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, SPComp.map,
          SPComp.pure_bind]
    have hc : cur - 1 = 0 := by simp [simLenP] at h3; omega
    rcases xo with _ | x
    · refine couple_eq (realOfP crs code none (some (c, r)) .cWait ρ (cur - 1) none) _ _ ?_ hI
        ⟨none, some (c, r), .cWait, ρ, cur - 1, none, rfl, rfl, by simp, by simp,
          by simp [simLenP, hc], by simp⟩
      simp [realOfP, realP_step_inr, realP_step_inl, FChan.advStep, FChan.popTo, keyMsg, ctMsg,
        partyP, qStart, qResume, pStart, pResume, sendIf, MultiHybrid.stepFuel,
        MultiHybrid.drive, FChan.honSys, FChan.honStep, PStage.keyGot, SPComp.map,
        SPComp.pure_bind]
    · refine couple_eq_sample
        (fun ρ' => realOfP crs code (some x) (some (c, r)) .cWait ρ' (cur - 1) none) _ _ ?_ hI
        fun ρ' => ⟨some x, some (c, r), .cWait, ρ', cur - 1, none, rfl, rfl, by simp, by simp,
          by simp [simLenP, hc], by simp⟩
      simp [realOfP, realP_step_inr, realP_step_inl, FChan.advStep, FChan.popTo, keyMsg, ctMsg,
        partyP, qStart, qResume, pStart, pResume, sendIf, MultiHybrid.stepFuel,
        MultiHybrid.drive, FChan.honSys, FChan.honStep, PStage.keyGot, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]
  by_cases hc : g = .cWait ∧ xo.isSome
  · obtain ⟨rfl, hxo⟩ := hc
    obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hxo
    obtain ⟨⟨c, r⟩, rfl⟩ : ∃ p, rc = some p := Option.isSome_iff_exists.mp (h1 (by simp))
    obtain rfl : ob = none := by cases ob <;> simp_all
    have hcur : cur - 1 = 0 := by simp [simLenP] at h3; omega
    refine couple_eq (realOfP crs code (some x) (some (c, r)) .fin ρ (cur - 1)
        (some (otChoose x c)))
      (idealOfP (some x) (some (c, r)) .fin (cur - 1) (some (otChoose x c))) (.inr .ack) ?_ ?_
      ⟨some x, some (c, r), .fin, ρ, cur - 1, some (otChoose x c), rfl, rfl, by simp, by simp,
        by simp [simLenP, hcur], by simp⟩
    · simp [realOfP, realP_step_inr, realP_step_inl, FChan.advStep, FChan.popTo, ctMsg,
        partyP, qStart, qResume, pStart, MultiHybrid.stepFuel, MultiHybrid.drive, FChan.honSys,
        FChan.honStep, PStage.keyGot, SPComp.map, SPComp.pure_bind,
        recvOut_senderMsg crs code decode hcode]
    · simp [idealOfP, idealP_step_inr, MultiHybrid.stepFuel, simP, simPStart, simPResume,
        delDec, MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, SPComp.map,
        SPComp.pure_bind]
  · exact couple_eq (realOfP crs code xo rc g ρ (cur - 1) ob) (idealOfP xo rc g (cur - 1) ob)
      (.inr .ack) (real_deliver_empty crs code decode xo rc g ρ cur ob hk hc)
      (ideal_deliver_empty xo rc g cur ob hk hc)
      ⟨xo, rc, g, ρ, cur - 1, ob, rfl, rfl, h1, h2, by omega, h4⟩

/-- The step on the receiver's input. -/
theorem step_recv (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : PStage) (ρ : SRand gp m) (cur : ℕ) (ob : Option (Fin m → M))
    (hwf : WFP xo rc g cur ob) (c : Fin m → Bool) :
    rHoare eqPre
      ((pvwPull crs code decode).step (realOfP crs code xo rc g ρ cur ob) (.inl (.inr c)))
      ((idealP gp m M).step (idealOfP xo rc g cur ob) (.inl (.inr c)))
      (stepPost (HRelP crs code)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  rw [pvwPull, Sys.wakeCloseSilent_step_inl]
  rcases rc with _ | ⟨c₀, r₀⟩
  · obtain rfl : g = .kWait := by
      by_contra hg
      simpa using h1 hg
    obtain rfl : ob = none := by cases ob <;> simp_all
    refine couple_eq_sample (fun r => realOfP crs code xo (some (c, r)) .kWait ρ cur none)
      (((), ⟨.kWait, cur, .idle⟩), ⟨xo, some c, none, false, false⟩)
      (.inl (.inr none)) ?_ ?_
      fun r => ⟨xo, some (c, r), .kWait, ρ, cur, none, rfl, by simp [idealOfP], by simp, by simp,
        by simp_all [simLenP], by simp⟩
    · simp [realOfP, realP_step_inl, MultiHybrid.stepFuel, partyP, qStart, qResume, pStart,
        pResume, MultiHybrid.drive, FChan.honSys, FChan.honStep, keyMsg, PStage.keyGot,
        SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [idealOfP, idealP_step_inl, FOTSched.recvSys, FOTSched.recvStep, SPComp.map,
        SPComp.pure_bind]
  · refine couple_eq (realOfP crs code xo (some (c₀, r₀)) g ρ cur none)
      (idealOfP xo (some (c₀, r₀)) g cur none) (.inl (.inr ob)) ?_ ?_
      ⟨xo, some (c₀, r₀), g, ρ, cur, none, rfl, rfl, h1, h2, h3, by simp⟩
    · simp [realOfP, realP_step_inl, MultiHybrid.stepFuel, partyP, qStart,
        MultiHybrid.drive, SPComp.map, SPComp.pure_bind]
    · simp [idealOfP, idealP_step_inl, FOTSched.recvSys, FOTSched.recvStep, SPComp.map,
        SPComp.pure_bind]

/-- The step on the sender's input. -/
theorem step_send (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : PStage) (ρ : SRand gp m) (cur : ℕ) (ob : Option (Fin m → M))
    (hwf : WFP xo rc g cur ob) (x : Fin m → M × M) :
    rHoare eqPre
      ((pvwPull crs code decode).step (realOfP crs code xo rc g ρ cur ob) (.inl (.inl x)))
      ((idealP gp m M).step (idealOfP xo rc g cur ob) (.inl (.inl x)))
      (stepPost (HRelP crs code)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  rw [pvwPull, Sys.wakeCloseSilent_step_inl]
  rcases xo with _ | x₀
  · have hI : (idealP gp m M).step (idealOfP none rc g cur ob) (.inl (.inl x)) =
        SPComp.pure (idealOfP (some x) rc g cur ob, .inl (.inl false)) := by
      simp [idealOfP, idealP_step_inl, FOTSched.sendSys, FOTSched.sendStep, SPComp.map,
        SPComp.pure_bind]
    by_cases hg : g = .cWait
    · subst hg
      obtain ⟨⟨c, r⟩, rfl⟩ : ∃ p, rc = some p := Option.isSome_iff_exists.mp (h1 (by simp))
      refine couple_eq_sample (fun ρ' => realOfP crs code (some x) (some (c, r)) .cWait ρ' cur ob)
        (idealOfP (some x) (some (c, r)) .cWait cur ob) (.inl (.inl false)) ?_ hI
        fun ρ' => ⟨some x, some (c, r), .cWait, ρ', cur, ob, rfl, rfl, by simp, by simp,
          by simp_all [simLenP], h4⟩
      simp [realOfP, realP_step_inl, MultiHybrid.stepFuel, partyP, qStart, qResume, pStart,
        pResume, sendIf, MultiHybrid.drive, FChan.honSys, FChan.honStep, ctMsg, PStage.keyGot,
        SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · refine couple_eq (realOfP crs code (some x) rc g ρ cur ob) (idealOfP (some x) rc g cur ob)
        (.inl (.inl false)) ?_ hI ⟨some x, rc, g, ρ, cur, ob, rfl, rfl, h1, by simp, ?_, h4⟩
      · cases g <;> simp_all [realOfP, realP_step_inl, MultiHybrid.stepFuel, partyP, qStart,
          pStart, sendIf, MultiHybrid.drive, PStage.keyGot, SPComp.map, SPComp.pure_bind]
      · cases g <;> simp_all [simLenP]
  · refine couple_eq (realOfP crs code (some x₀) rc g ρ cur ob) (idealOfP (some x₀) rc g cur ob)
      (.inl (.inl false)) ?_ ?_ ⟨some x₀, rc, g, ρ, cur, ob, rfl, rfl, h1, h2, h3, h4⟩
    · cases g <;> simp [realOfP, realP_step_inl, MultiHybrid.stepFuel, partyP, qStart, pStart,
        sendIf, MultiHybrid.drive, PStage.keyGot, SPComp.map, SPComp.pure_bind]
    · simp [idealOfP, idealP_step_inl, FOTSched.sendSys, FOTSched.sendStep, SPComp.map,
        SPComp.pure_bind]

/-! ## The square -/

/-- **The PVW dual-mode OT with both parties honest, in pull form.** Ideal functionality:
`FOTSched otChoose`, the scheduled transfer of `m` message pairs. Real protocol:
`pvwPull crs code decode`, the PVW parties with the CRS `crs` over the secure channel, closed by
the silent wake; the receiver outputs the decrypted ciphertexts once, at its next activation.
Simulator: `Simulator.tensor (idSim InEv InOut) simP`, which forwards the honest port to `F` and
answers the channel's adversary events from the stage of the message in flight and the input
status of `F`, issuing `deliverRecv` at the delivery of the ciphertexts. Distance `0`, for every
CRS and every honest view `VH`, when `decode` inverts `code`. -/
theorem pvwPull_realizesSim {VH : PubView (InEv m M) (InOut m M)} (crs : CRS gp)
    (code : M → gp.G) (decode : gp.G → M) (hcode : ∀ a, decode (code a) = a) :
    RealizesSim (pvwPull (m := m) crs code decode) (FOTSched otChoose)
      (Simulator.tensor (MultiHybrid.idSim (InEv m M) (InOut m M)) (simP gp m)
        (MultiHybrid.idSim_opaque VH) (MultiHybrid.opaque_eqView _)) (fun _ _ => 0) := by
  refine (realizes_zero_of_coupling (R := pvwPull (m := m) crs code decode)
    (I := idealP gp m M) (rel := HRelP crs code) ⟨?_, ?_⟩).1
  · exact ⟨none, none, .kWait, Classical.arbitrary _, 0, none, by
      simp [realOfP, pvwPull, Sys.wakeCloseSilent, realP, partyP, MultiHybrid.withSub,
        MultiHybrid.tensor, PSt.init, PStage.keyGot, keyMsg]; rfl,
      rfl, by simp, by simp, by simp [simLenP], by simp⟩
  · rintro t u e ⟨xo, rc, g, ρ, cur, ob, rfl, rfl, hwf⟩
    rcases e with (x | c) | a
    · exact step_send crs code decode xo rc g ρ cur ob hwf x
    · exact step_recv crs code decode xo rc g ρ cur ob hwf c
    · cases a with
      | deliver => exact step_deliver crs code decode hcode xo rc g ρ cur ob hwf
      | idle => exact step_quiet crs code decode xo rc g ρ cur ob hwf _ rfl
      | poll => exact step_quiet crs code decode xo rc g ρ cur ob hwf _ rfl
      | drop => exact step_quiet crs code decode xo rc g ρ cur ob hwf _ rfl
      | tamper v => exact step_quiet crs code decode xo rc g ρ cur ob hwf _ rfl

/-- The protocol in pull form is idle at the channel's `idle`. -/
theorem pvwPull_idleAt (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) :
    MultiHybrid.IdleAt (pvwPull (m := m) crs code decode) (.inr .idle) (.inr .ack) := by
  rintro ⟨⟨st, u⟩, ch⟩
  rw [pvwPull, Sys.wakeCloseSilent_step_none _ _ _ _ rfl, realP_step_inr]
  rfl

/-- The simulated functionality is idle at the channel's `idle`. -/
theorem simP_idleAt :
    MultiHybrid.IdleAt (idealP gp m M) (.inr .idle) (.inr .ack) := by
  rintro ⟨⟨⟨⟩, s⟩, t⟩
  simp [idealP_step_inr, MultiHybrid.stepFuel, simP, simPStart, MultiHybrid.drive, SPComp.map,
    SPComp.pure_bind]

end CatCrypt.Crypto.OT.PVWPull

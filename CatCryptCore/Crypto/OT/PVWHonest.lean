/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.PVWOTSquare
public import CatCryptCore.Crypto.UCChannel
public import CatCryptCore.Crypto.UCWake
public import CatCryptCore.Crypto.UCCoupling

/-!
# The PVW dual-mode OT with both parties honest, over a channel, with activation on delivery

**Ideal functionality.** `FOTSched otChoose` (`OT/FOTSched.lean`): the scheduled transfer of `m`
message pairs, with the sender and the receiver on the honest port and the scheduler on the
adversary port. The receiver obtains `otChoose x c` only after the adversary delivers it.

**Real protocol.** The two parties of the Peikert–Vaikuntanathan–Waters dual-mode OT
(`OT/PVWOTSquare.lean`) with the CRS `crs`, one multi-call hybrid (`partyH`) over the secure
channel `FChan ChannelCap.secure` carrying the receiver's key and the sender's ciphertexts; the
adversary port of the channel is forwarded. The receiver with choices `c` draws `r` and sends
`recvMsg crs c r`. On the wake, a party reads the channel: the sender stores the key and, once it
holds its message pairs `x`, draws `ρ` and sends `senderMsg crs code k x ρ`; the receiver decrypts
the ciphertexts with `recvOut decode c r`. The sender sends as well when its input arrives after
the key. Every activation of the sender outputs `false`, the completion notice that `F` holds
back while the adversary does not deliver it. The wake closure `Sys.wakeClose dlvH cutH`
(`UCWake.lean`) makes the channel's `deliver` activate the parties with the wake in the same
activation.

**Simulator.** `simH` forwards the inputs to the honest port of `FOTSched otChoose`. It keeps the
stage of the message in flight (`Stage`) and the channel's cursor, and obtains the presence of the
inputs by a poll of the scheduler: the key is in transit once the receiver has chosen, the
ciphertexts once the key is received and the sender has its input. It answers the channel's
`poll`, `deliver` and `drop` from these; at the wake that reads the ciphertexts it delivers the
receiver's output on `F` and passes on the output of a receiver activation. It reads no input
value (`simH_opaque`, inputs hidden, wakes and adversary events public).

**Bound.** `0` for every CRS (`pvwH_realizesSim`, `pvwH_wake_realizesSim`): the channel shows
only the presence of a message, and the receiver's output is `otChoose x c` by correctness
(`recvOut_senderMsg`). No mode of the CRS and no DDH hop is used.

## Main definitions

* `PSt`, `partyH`, `realH`: the parties and the protocol over the channel.
* `Stage`, `SSt`, `simH`, `pvwSimH`: the simulator.
* `dlvH`, `cutH`: the deliveries and the cut-off of the wake closure.

## Main results

* `pvwH_realizesSim`: both parties honest, distance `0`.
* `pvwH_wake_realizesSim`: the same with activation on delivery, distance `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.PVWHonest

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.Relational CatCrypt.Crypto.OT.PVW
open CatCrypt.NonUniform CatCrypt.Examples
open CatCrypt.Crypto.Choreography (ChannelCap)
open scoped ENNReal

variable {gp : GroupParam} {m : ℕ} {M : Type}

/-! ## The channel and the parties -/

variable (gp m) in
/-- A message on the channel: the receiver's key or the sender's ciphertexts. -/
abbrev V := Key gp m ⊕ Cts gp m

variable (gp m) in
/-- The secure channel for the messages of the protocol, which shows only their presence. -/
noncomputable abbrev chanH : Sys (ChanSt (V gp m)) (ChanHEv (V gp m) ⊕ ChanAEv (V gp m))
    (ChanHOut (V gp m) ⊕ ChanAOut (V gp m) Unit) :=
  FChan ChannelCap.secure fun _ : V gp m => ()

variable (m M) in
/-- The inputs of the parties: the sender's message pairs and the receiver's choices. -/
abbrev InEv := (Fin m → M × M) ⊕ (Fin m → Bool)

variable (m M) in
/-- The outputs of the parties: the sender's completion bit and the receiver's output. -/
abbrev InOut := Bool ⊕ Option (Fin m → M)

/-- The awaited answer of the parties' activation. -/
inductive PPh where
  /-- No call is pending. -/
  | idle
  /-- The receiver's send of its key. -/
  | sendK
  /-- The sender's send of its ciphertexts. -/
  | sendC
  /-- A receive on the channel after a wake. -/
  | recv

variable (gp m M) in
/-- The state of the two parties. -/
structure PSt where
  /-- The sender's message pairs. -/
  xo : Option (Fin m → M × M)
  /-- The key the sender has received. -/
  kS : Option (Key gp m)
  /-- Whether the sender has sent its ciphertexts. -/
  sent : Bool
  /-- The receiver's choices and randomness. -/
  rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar))
  /-- Whether the receiver has output. -/
  done : Bool
  /-- The phase of the activation. -/
  ph : PPh

/-- The initial state of the parties. -/
def PSt.init : PSt gp m M := ⟨none, none, false, none, false, .idle⟩

/-- The sender's send: with its message pairs `x` and a received key `k`, and not sent before, it
draws `ρ` and sends `senderMsg crs code k x ρ`; otherwise it outputs `false`. -/
noncomputable def sendIf (crs : CRS gp) (code : M → gp.G) (st : PSt gp m M) :
    SPComp (PSt gp m M × (ChanHEv (V gp m) ⊕ InOut m M)) :=
  match st.xo, st.kS, st.sent with
  | some x, some k, false => SPComp.bind (SPComp.sample (SRand gp m)) fun ρ =>
      SPComp.pure ({ st with sent := true, ph := .sendC },
        .inl (.send (.inr (senderMsg crs code k x ρ))))
  | _, _, _ => SPComp.pure ({ st with ph := .idle }, .inr (.inl false))

/-- The first step of an activation of the parties. -/
noncomputable def pStart (crs : CRS gp) (code : M → gp.G) (st : PSt gp m M) :
    InEv m M ⊕ Unit → SPComp (PSt gp m M × (ChanHEv (V gp m) ⊕ InOut m M))
  | .inl (.inl x) => sendIf crs code { st with xo := st.xo.or (some x) }
  | .inl (.inr c) => match st.rc with
    | some _ => SPComp.pure (st, .inr (.inr none))
    | none => SPComp.bind (SPComp.sample (Fin m → gp.Scalar)) fun r =>
        SPComp.pure ({ st with rc := some (c, r), ph := .sendK },
          .inl (.send (.inl (recvMsg crs c r))))
  | .inr _ => SPComp.pure ({ st with ph := .recv }, .inl .recv)

/-- The step of the parties on an answer of the channel. -/
noncomputable def pResume (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (st : PSt gp m M) (o : ChanHOut (V gp m)) :
    SPComp (PSt gp m M × (ChanHEv (V gp m) ⊕ InOut m M)) :=
  match st.ph, o with
  | .recv, .got (some (.inl k)) => sendIf crs code { st with kS := st.kS.or (some k) }
  | .recv, .got (some (.inr ct)) =>
    SPComp.pure ({ st with done := true, ph := .idle },
      .inr (.inr (st.rc.map fun p => recvOut decode p.1 p.2 ct)))
  | .sendK, _ => SPComp.pure ({ st with ph := .idle }, .inr (.inr none))
  | _, _ => SPComp.pure ({ st with ph := .idle }, .inr (.inl false))

/-- `sendIf` never fails. -/
theorem sendIf_noFail (crs : CRS gp) (code : M → gp.G) (st : PSt gp m M) :
    SPComp.NoFail (sendIf crs code st) := by
  unfold sendIf
  split
  · exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail
      fun _ => SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

/-- **The PVW parties** with the CRS `crs` over the channel. The receiver's input `c` draws `r`
and sends the key `recvMsg crs c r`. On the wake a party receives from the channel: a key is
stored by the sender, which sends its ciphertexts once it also holds its message pairs; the
ciphertexts are decrypted by the receiver, which outputs `recvOut decode c r`. -/
noncomputable def partyH (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) :
    MultiHybrid (PSt gp m M) (InEv m M ⊕ Unit) (InOut m M) (ChanHEv (V gp m))
      (ChanHOut (V gp m)) where
  init := PSt.init
  fuel := 1
  start := pStart crs code
  resume := pResume crs code decode
  finish st _ := SPComp.pure ({ st with ph := .idle }, .inl false)
  start_noFail st e := by
    rcases e with (x | c) | _
    · exact sendIf_noFail crs code _
    · simp only [pStart]
      split
      · exact SPComp.pure_noFail _
      · exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail
          fun _ => SPComp.pure_noFail _
    · exact SPComp.pure_noFail _
  resume_noFail st o := by
    unfold pResume
    split
    · exact sendIf_noFail crs code _
    all_goals exact SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- **The PVW protocol with both parties honest** over the secure channel: the parties on the
honest port with their wakes, the channel's adversary port forwarded. -/
noncomputable def realH (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) :
    Sys ((PSt gp m M × Unit) × ChanSt (V gp m)) ((InEv m M ⊕ Unit) ⊕ ChanAEv (V gp m))
      (InOut m M ⊕ ChanAOut (V gp m) Unit) :=
  ((partyH crs code decode).tensor
    (MultiHybrid.idSim (ChanAEv (V gp m)) (ChanAOut (V gp m) Unit))).withSub (chanH gp m)

/-! ## The simulator -/

/-- The stage of the message in flight, in the simulator. -/
inductive Stage where
  /-- The key is not yet delivered: in transit once the receiver has chosen. -/
  | kWait
  /-- The key is in the sender's inbox. -/
  | kIn
  /-- The key is dropped. -/
  | kLost
  /-- The key is received; the ciphertexts are in transit once the sender has its input. -/
  | cWait
  /-- The ciphertexts are in the receiver's inbox. -/
  | cIn
  /-- The ciphertexts are dropped. -/
  | cLost
  /-- The ciphertexts are received. -/
  | fin
  deriving DecidableEq

/-- Whether the sender has received the key. -/
def Stage.keyGot : Stage → Bool
  | .cWait | .cIn | .cLost | .fin => true
  | _ => false

/-- The awaited answer of the simulator's activation. -/
inductive SPh where
  /-- No call is pending. -/
  | idle
  /-- The answer to a forwarded input. -/
  | fwd
  /-- The input status, for a poll of the channel. -/
  | aPoll
  /-- The input status, for a delivery (`false`) or a drop (`true`) of the channel. -/
  | aDel (drop : Bool)
  /-- The acknowledgement of the delivery of the receiver's output. -/
  | wR1
  /-- The receiver's output. -/
  | wR2

/-- The state of the simulator: the stage of the message in flight, the channel's cursor and the
phase. -/
structure SSt where
  /-- The stage of the message in flight. -/
  g : Stage
  /-- The number of messages shown to the adversary. -/
  cur : ℕ
  /-- The phase of the activation. -/
  ph : SPh

/-- The number of messages in transit at the stage `g`, given whether the sender's input (`a`)
and the receiver's choice (`b`) have arrived. -/
def simLen (g : Stage) (a b : Bool) : ℕ :=
  match g with
  | .kWait => if b then 1 else 0
  | .cWait => if a then 1 else 0
  | _ => 0

/-- The stage after a delivery (`drop = false`) or a drop of the channel. -/
def nextStage (drop : Bool) (g : Stage) (a b : Bool) : Stage :=
  match g with
  | .kWait => if b then (if drop then .kLost else .kIn) else .kWait
  | .cWait => if a then (if drop then .cLost else .cIn) else .cWait
  | g => g

/-- The choice the simulator gives the ideal functionality for the receiver, which has already
chosen. -/
def dummyC : Fin m → Bool := fun _ => false

variable (gp m M) in
/-- The decisions of the simulator. -/
abbrev SDec := ((InEv m M ⊕ SchedEv) ⊕ (InOut m M ⊕ ChanAOut (V gp m) Unit))

/-- The simulator's first step. -/
def simStart (s : SSt) : (InEv m M ⊕ Unit) ⊕ ChanAEv (V gp m) → SSt × SDec (gp := gp) m M
  | .inl (.inl e) => ({ s with ph := .fwd }, .inl (.inl e))
  | .inl (.inr _) => match s.g with
    | .kIn => ({ s with g := .cWait }, .inr (.inl (.inl false)))
    | .cIn => ({ s with g := .fin, ph := .wR1 }, .inl (.inr .deliverRecv))
    | _ => (s, .inr (.inl (.inl false)))
  | .inr .idle => (s, .inr (.inr .ack))
  | .inr .poll => ({ s with ph := .aPoll }, .inl (.inr .poll))
  | .inr .deliver => ({ s with ph := .aDel false }, .inl (.inr .poll))
  | .inr .drop => ({ s with ph := .aDel true }, .inl (.inr .poll))
  | .inr (.tamper _) => (s, .inr (.inr .ack))

/-- The simulator's step on an answer of the ideal functionality. -/
def simResume (s : SSt) : InOut m M ⊕ SchedOut → SSt × SDec (gp := gp) m M
  | .inl o => match s.ph with
    | .fwd | .wR2 => ({ s with ph := .idle }, .inr (.inl o))
    | .wR1 => ({ s with ph := .wR2 }, .inl (.inl (.inr dummyC)))
    | _ => ({ s with ph := .idle }, .inr (.inl (.inl false)))
  | .inr a => match s.ph, a with
    | .aPoll, .status x y =>
      ({ s with cur := min (s.cur + 1) (simLen s.g x y), ph := .idle },
        .inr (.inr (.leak (if s.cur < simLen s.g x y then some (.inr ()) else none))))
    | .aDel d, .status x y =>
      ({ s with g := nextStage d s.g x y, cur := s.cur - 1, ph := .idle }, .inr (.inr .ack))
    | .wR1, _ => ({ s with ph := .wR2 }, .inl (.inl (.inr dummyC)))
    | _, _ => ({ s with ph := .idle }, .inr (.inl (.inl false)))

variable (gp m M) in
/-- **The simulator** over `FOTSched otChoose`, both parties honest. It forwards the inputs; it
answers the channel's adversary events from the stage of the message in flight and the input
status that a poll of the scheduler reports; at the wake that reads the ciphertexts it delivers
the receiver's output and passes on the output of a receiver activation. -/
noncomputable def simH :
    MultiHybrid SSt ((InEv m M ⊕ Unit) ⊕ ChanAEv (V gp m)) (InOut m M ⊕ ChanAOut (V gp m) Unit)
      (InEv m M ⊕ SchedEv) (InOut m M ⊕ SchedOut) where
  init := ⟨.kWait, 0, .idle⟩
  fuel := 2
  start s e := SPComp.pure (simStart s e)
  resume s o := SPComp.pure (simResume s o)
  finish s _ := SPComp.pure ({ s with ph := .idle }, .inl (.inl false))
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- **Opacity of the simulator**: inputs related by `hidView`, wakes and adversary events public.
It forwards the inputs, and its other decisions depend on its state and the adversary port. -/
theorem simH_opaque :
    (simH gp m M).Opaque ((IKNPSquare.hidView.wake Unit).sum PubView.eqView)
      (IKNPSquare.hidView.sum PubView.eqView) := by
  have hrefl : ∀ d : SDec gp m M, PubView.StepRel
      (((IKNPSquare.hidView : PubView (InEv m M) (InOut m M)).wake Unit).sum
        (PubView.eqView : PubView (ChanAEv (V gp m)) (ChanAOut (V gp m) Unit)))
      ((IKNPSquare.hidView : PubView (InEv m M) (InOut m M)).sum
        (PubView.eqView : PubView SchedEv SchedOut)) d d := by
    rintro ((g | g) | (o | o))
    · exact Sum.LiftRel.inl trivial
    · exact Sum.LiftRel.inr rfl
    · exact Sum.LiftRel.inl trivial
    · exact Sum.LiftRel.inr rfl
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    refine rHoare_ret fun _ _ h => ⟨h, ?_⟩
    cases he with
    | inl h =>
      cases h with
      | inl _ => exact ⟨rfl, Sum.LiftRel.inl trivial⟩
      | inr h => subst h; exact ⟨rfl, hrefl _⟩
    | inr h => subst h; exact ⟨rfl, hrefl _⟩
  · rintro s _ o o' rfl ho
    refine rHoare_ret fun _ _ h => ⟨h, ?_⟩
    cases ho with
    | inl _ =>
      simp only [simResume]
      split <;> exact ⟨rfl, Sum.LiftRel.inl trivial⟩
    | inr h => subst h; exact ⟨rfl, hrefl _⟩
  · rintro s _ o o' rfl _
    exact rHoare_ret fun _ _ h => ⟨h, rfl, Sum.LiftRel.inl trivial⟩

variable (gp m M) in
/-- The simulator `simH` as a simulator. -/
noncomputable def pvwSimH :
    Simulator ((InEv m M ⊕ Unit) ⊕ ChanAEv (V gp m)) (InOut m M ⊕ ChanAOut (V gp m) Unit)
      (InEv m M ⊕ SchedEv) (InOut m M ⊕ SchedOut)
      ((IKNPSquare.hidView.wake Unit).sum PubView.eqView)
      (IKNPSquare.hidView.sum PubView.eqView) :=
  Simulator.ofMultiHybrid (simH gp m M) simH_opaque

/-! ## The coupling -/

/-- The key on the channel for the receiver's choices and randomness. -/
def keyMsg (crs : CRS gp) : Option ((Fin m → Bool) × (Fin m → gp.Scalar)) → List (V gp m)
  | some p => [.inl (recvMsg crs p.1 p.2)]
  | none => []

/-- The ciphertexts on the channel for the sender's input, the receiver's choices and
randomness, and the sender's randomness `ρ`. -/
def ctMsg (crs : CRS gp) (code : M → gp.G) :
    Option (Fin m → M × M) → Option ((Fin m → Bool) × (Fin m → gp.Scalar)) → SRand gp m →
      List (V gp m)
  | some x, some p, ρ => [.inr (senderMsg crs code (recvMsg crs p.1 p.2) x ρ)]
  | _, _, _ => []

/-- The state of the protocol at the stage `g`, with the inputs `xo` and `rc`, the sender's
randomness `ρ` and the cursor `cur`. -/
def realOf (crs : CRS gp) (code : M → gp.G) (xo : Option (Fin m → M × M))
    (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar))) (g : Stage) (ρ : SRand gp m)
    (cur : ℕ) : (PSt gp m M × Unit) × ChanSt (V gp m) :=
  ((⟨xo, if g.keyGot then rc.map (fun p => recvMsg crs p.1 p.2) else none,
      g.keyGot && xo.isSome, rc, decide (g = .fin), .idle⟩, ()),
    ⟨match g with
      | .kWait => keyMsg crs rc
      | .cWait => ctMsg crs code xo rc ρ
      | _ => [],
     cur,
     match g with
      | .kIn => keyMsg crs rc
      | .cIn => ctMsg crs code xo rc ρ
      | _ => []⟩)

/-- The state of the simulator over `FOTSched otChoose` at the stage `g`. -/
def idealOf (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : Stage) (cur : ℕ) :
    SSt × SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M) :=
  (⟨g, cur, .idle⟩, ⟨xo, rc.map Prod.fst, none, decide (g = .fin), false⟩)

/-- The reachable stages: the key is sent once the receiver has chosen, the ciphertexts once the
sender has its input, and the cursor is at most the number of messages in transit. -/
def WF (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : Stage) (cur : ℕ) : Prop :=
  (g ≠ .kWait → rc.isSome) ∧ (g = .cIn ∨ g = .cLost ∨ g = .fin → xo.isSome) ∧
    cur ≤ simLen g xo.isSome rc.isSome

/-- The relation of the protocol's states and the simulator's states over `FOTSched otChoose`. -/
def HRel (crs : CRS gp) (code : M → gp.G) (t : (PSt gp m M × Unit) × ChanSt (V gp m))
    (u : SSt × SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M)) : Prop :=
  ∃ xo rc g ρ cur, t = realOf crs code xo rc g ρ cur ∧ u = idealOf xo rc g cur ∧ WF xo rc g cur

open CatCrypt.Crypto.UCCoupling (stepPost realizes_zero_of_coupling)

/-- Two point masses with related states and equal outputs are coupled. -/
theorem couple_pure {τ υ O : Type} {rel : τ → υ → Prop} {t' : τ} {u' : υ} {o o' : O}
    (h : rel t' u') (ho : o = o') :
    rHoare eqPre (SPComp.pure (t', o)) (SPComp.pure (u', o')) (stepPost rel) :=
  rHoare_ret fun _ _ hh => ⟨hh, h, ho⟩

/-- A uniform draw followed by a point mass is coupled with a point mass when every drawn value
gives a related state and the same output. -/
theorem couple_sample {τ υ O α : Type} [Fintype α] [Nonempty α] {rel : τ → υ → Prop}
    (g : α → τ × O) {u' : υ} {o : O} (h : ∀ a, rel (g a).1 u' ∧ (g a).2 = o) :
    rHoare eqPre (SPComp.bind (SPComp.sample α) fun a => SPComp.pure (g a))
      (SPComp.pure (u', o)) (stepPost rel) := by
  rw [← dead_sample (α := α) (SPComp.pure (u', o))]
  exact rHoare_bind (rHoare_refl _) fun a b => rHoare_ret fun _ _ hh => by
    obtain ⟨rfl, rfl⟩ := hh
    exact ⟨rfl, (h a).1, (h a).2⟩

/-- Two computations equal to point masses with related states and equal outputs are
coupled. -/
theorem couple_eq {τ υ O : Type} {rel : τ → υ → Prop} {R : SPComp (τ × O)} {I : SPComp (υ × O)}
    (t' : τ) (u' : υ) (o : O) (hR : R = SPComp.pure (t', o)) (hI : I = SPComp.pure (u', o))
    (h : rel t' u') : rHoare eqPre R I (stepPost rel) := by
  rw [hR, hI]
  exact couple_pure h rfl

/-- A computation equal to a uniform draw followed by a point mass is coupled with a point mass
when every drawn value gives a related state, with equal outputs. -/
theorem couple_eq_sample {τ υ O α : Type} [Fintype α] [Nonempty α] {rel : τ → υ → Prop}
    {R : SPComp (τ × O)} {I : SPComp (υ × O)} (G : α → τ) (u' : υ) (o : O)
    (hR : R = SPComp.bind (SPComp.sample α) fun a => SPComp.pure (G a, o))
    (hI : I = SPComp.pure (u', o)) (h : ∀ a, rel (G a) u') : rHoare eqPre R I (stepPost rel) := by
  rw [hR, hI]
  exact couple_sample (fun a => (G a, o)) fun a => ⟨h a, rfl⟩

/-- Unfolding lemma of `realH`: a step on an input or a wake. -/
theorem realH_step_inl (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) (st : PSt gp m M)
    (u : Unit) (ch : ChanSt (V gp m)) (e : InEv m M ⊕ Unit) :
    (realH crs code decode).step ((st, u), ch) (.inl e) =
      SPComp.map (fun p => (((p.1.1, u), p.1.2), Sum.inl p.2))
        ((partyH crs code decode).stepFuel FChan.honSys 1 (st, ch) e) := by
  rw [realH, MultiHybrid.tensor_withSub_step_inl _ _ (chanH gp m) FChan.honSys (fun _ _ => rfl)]
  rfl

/-- Unfolding lemma of `realH`: a step on an adversary event of the channel. -/
theorem realH_step_inr (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) (st : PSt gp m M)
    (u : Unit) (ch : ChanSt (V gp m)) (a : ChanAEv (V gp m)) :
    (realH crs code decode).step ((st, u), ch) (.inr a) =
      SPComp.pure (((st, u), (FChan.advStep ChannelCap.secure (fun _ => ()) ch a).1),
        .inr (FChan.advStep ChannelCap.secure (fun _ => ()) ch a).2) := by
  rw [realH, MultiHybrid.tensor_withSub_step_inr _ _ (chanH gp m) (FChan.advSys _ _)
    (fun _ _ => rfl), MultiHybrid.idSim_stepFuel]
  simp [FChan.advSys, SPComp.map, SPComp.pure_bind]

/-- The ideal side of a delivery (`d = false`) or a drop (`d = true`) of the channel. -/
theorem sim_step_pop (xo : Option (Fin m → M × M))
    (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar))) (g : Stage) (cur : ℕ) (d : Bool) :
    ((simH gp m M).withSub (FOTSched otChoose)).step (idealOf xo rc g cur)
        (.inr (bif d then .drop else .deliver)) =
      SPComp.pure (idealOf xo rc (nextStage d g xo.isSome rc.isSome) (cur - 1), .inr .ack) := by
  have h : (simStart (gp := gp) (m := m) (M := M) ⟨g, cur, .idle⟩
      (.inr (bif d then .drop else .deliver))) = (⟨g, cur, .aDel d⟩, .inl (.inr .poll)) := by
    cases d <;> rfl
  simp only [MultiHybrid.withSub, simH, h, idealOf, SPComp.pure_bind]
  simp [MultiHybrid.drive, simResume, FOTSched, FOTSched.schedSys, FOTSched.schedStep,
    SPComp.map, SPComp.pure_bind]
  cases g <;> simp [nextStage] <;> split_ifs <;> simp

/-- The real side of a delivery (`d = false`) or a drop (`d = true`) of the channel. -/
theorem real_step_pop (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : Stage) (ρ : SRand gp m) (cur : ℕ) (hwf : WF xo rc g cur) (d : Bool) :
    (realH crs code decode).step (realOf crs code xo rc g ρ cur)
        (.inr (bif d then .drop else .deliver)) =
      SPComp.pure (realOf crs code xo rc (nextStage d g xo.isSome rc.isSome) ρ (cur - 1),
        .inr .ack) := by
  obtain ⟨h1, h2, -⟩ := hwf
  have hpop : ∀ ch : ChanSt (V gp m),
      FChan.advStep ChannelCap.secure (fun _ => ()) ch (bif d then .drop else .deliver) =
        (FChan.popTo ch (bif d then [] else ch.queue.head?.toList), .ack) := by
    intro ch; cases d <;> rfl
  simp only [realOf, realH_step_inr, hpop]
  cases g <;> rcases xo with _ | x <;> rcases rc with _ | ⟨c, r⟩ <;> cases d <;>
    simp_all [FChan.popTo, keyMsg, ctMsg, nextStage, Stage.keyGot]

/-- The step on a delivery (`d = false`) or a drop (`d = true`) of the channel. -/
theorem step_pop (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : Stage) (ρ : SRand gp m) (cur : ℕ) (hwf : WF xo rc g cur) (d : Bool) :
    rHoare eqPre
      ((realH crs code decode).step (realOf crs code xo rc g ρ cur)
        (.inr (bif d then .drop else .deliver)))
      (((simH gp m M).withSub (FOTSched otChoose)).step (idealOf xo rc g cur)
        (.inr (bif d then .drop else .deliver)))
      (stepPost (HRel crs code)) := by
  refine couple_eq _ _ _ (real_step_pop crs code decode xo rc g ρ cur hwf d)
    (sim_step_pop xo rc g cur d) ⟨xo, rc, _, ρ, _, rfl, rfl, ?_⟩
  obtain ⟨h1, h2, h3⟩ := hwf
  cases g <;> rcases xo with _ | x <;> rcases rc with _ | ⟨c, r⟩ <;> cases d <;>
    simp_all [WF, simLen, nextStage]

/-- The step on an adversary event of the channel. -/
theorem step_adv (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : Stage) (ρ : SRand gp m) (cur : ℕ) (hwf : WF xo rc g cur) (a : ChanAEv (V gp m)) :
    rHoare eqPre ((realH crs code decode).step (realOf crs code xo rc g ρ cur) (.inr a))
      (((simH gp m M).withSub (FOTSched otChoose)).step (idealOf xo rc g cur) (.inr a))
      (stepPost (HRel crs code)) := by
  obtain ⟨h1, h2, h3⟩ := hwf
  cases a with
  | idle =>
    refine couple_eq (realOf crs code xo rc g ρ cur) (idealOf xo rc g cur) (.inr .ack) ?_ ?_
      ⟨xo, rc, g, ρ, cur, rfl, rfl, h1, h2, h3⟩
    · simp [realOf, realH_step_inr, FChan.advStep]
    · simp [MultiHybrid.withSub, simH, simStart, MultiHybrid.drive, idealOf, SPComp.pure_bind]
  | poll =>
    refine couple_eq (realOf crs code xo rc g ρ (min (cur + 1) (simLen g xo.isSome rc.isSome)))
      (idealOf xo rc g (min (cur + 1) (simLen g xo.isSome rc.isSome)))
      (.inr (.leak (if cur < simLen g xo.isSome rc.isSome then some (.inr ()) else none))) ?_ ?_
      ⟨xo, rc, g, ρ, _, rfl, rfl, h1, h2, min_le_right _ _⟩
    · cases g <;> rcases xo with _ | x <;> rcases rc with _ | ⟨c, r⟩ <;>
        rcases cur with _ | _ | cur <;>
        simp_all [realOf, realH_step_inr, FChan.advStep, FChan.pollLeak, keyMsg, ctMsg, simLen,
          ChannelCap.wireLeak, ChannelCap.secure, Stage.keyGot]
    · simp [MultiHybrid.withSub, simH, simStart, simResume, MultiHybrid.drive, idealOf,
        FOTSched, FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
  | deliver => exact step_pop crs code decode xo rc g ρ cur ⟨h1, h2, h3⟩ false
  | drop => exact step_pop crs code decode xo rc g ρ cur ⟨h1, h2, h3⟩ true
  | tamper v =>
    refine couple_eq (realOf crs code xo rc g ρ cur) (idealOf xo rc g cur) (.inr .ack) ?_ ?_
      ⟨xo, rc, g, ρ, cur, rfl, rfl, h1, h2, h3⟩
    · simp [realOf, realH_step_inr, FChan.advStep, ChannelCap.secure]
    · simp [MultiHybrid.withSub, simH, simStart, MultiHybrid.drive, idealOf, SPComp.pure_bind]

/-- The step on the receiver's input. -/
theorem step_recv (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : Stage) (ρ : SRand gp m) (cur : ℕ) (hwf : WF xo rc g cur) (c : Fin m → Bool) :
    rHoare eqPre
      ((realH crs code decode).step (realOf crs code xo rc g ρ cur) (.inl (.inl (.inr c))))
      (((simH gp m M).withSub (FOTSched otChoose)).step (idealOf xo rc g cur)
        (.inl (.inl (.inr c))))
      (stepPost (HRel crs code)) := by
  obtain ⟨h1, h2, h3⟩ := hwf
  rcases rc with _ | ⟨c₀, r₀⟩
  · obtain rfl : g = .kWait := by
      by_contra hg
      simpa using h1 hg
    refine couple_eq_sample (fun r => realOf crs code xo (some (c, r)) .kWait ρ cur)
      (⟨.kWait, cur, .idle⟩, ⟨xo, some c, none, false, false⟩) (.inl (.inr none)) ?_ ?_
      fun r => ⟨xo, some (c, r), .kWait, ρ, cur, rfl, rfl, by simp, by simp,
        by simp_all [simLen]⟩
    · simp [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart, pResume,
        MultiHybrid.drive, FChan.honSys, FChan.honStep, keyMsg, Stage.keyGot, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]
    · simp [MultiHybrid.withSub, simH, simStart, simResume, MultiHybrid.drive, idealOf,
        FOTSched, FOTSched.recvSys, FOTSched.recvStep, SPComp.map, SPComp.pure_bind]
  · refine couple_eq (realOf crs code xo (some (c₀, r₀)) g ρ cur)
      (idealOf xo (some (c₀, r₀)) g cur) (.inl (.inr none)) ?_ ?_
      ⟨xo, some (c₀, r₀), g, ρ, cur, rfl, rfl, h1, h2, h3⟩
    · simp [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart,
        MultiHybrid.drive, SPComp.map, SPComp.pure_bind]
    · simp [MultiHybrid.withSub, simH, simStart, simResume, MultiHybrid.drive, idealOf,
        FOTSched, FOTSched.recvSys, FOTSched.recvStep, SPComp.map, SPComp.pure_bind]

/-- The step on the sender's input. -/
theorem step_send (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : Stage) (ρ : SRand gp m) (cur : ℕ) (hwf : WF xo rc g cur) (x : Fin m → M × M) :
    rHoare eqPre
      ((realH crs code decode).step (realOf crs code xo rc g ρ cur) (.inl (.inl (.inl x))))
      (((simH gp m M).withSub (FOTSched otChoose)).step (idealOf xo rc g cur)
        (.inl (.inl (.inl x))))
      (stepPost (HRel crs code)) := by
  obtain ⟨h1, h2, h3⟩ := hwf
  rcases xo with _ | x₀
  · have hI : ((simH gp m M).withSub (FOTSched otChoose)).step (idealOf none rc g cur)
        (.inl (.inl (.inl x))) = SPComp.pure (idealOf (some x) rc g cur, .inl (.inl false)) := by
      simp [MultiHybrid.withSub, simH, simStart, simResume, MultiHybrid.drive, idealOf,
        FOTSched, FOTSched.sendSys, FOTSched.sendStep, SPComp.map, SPComp.pure_bind]
    by_cases hg : g = .cWait
    · subst hg
      obtain ⟨⟨c, r⟩, rfl⟩ : ∃ p, rc = some p := Option.isSome_iff_exists.mp (h1 (by simp))
      refine couple_eq_sample (fun ρ' => realOf crs code (some x) (some (c, r)) .cWait ρ' cur)
        (idealOf (some x) (some (c, r)) .cWait cur) (.inl (.inl false)) ?_ hI
        fun ρ' => ⟨some x, some (c, r), .cWait, ρ', cur, rfl, rfl, by simp, by simp,
          by simp_all [simLen]⟩
      simp [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart, pResume, sendIf,
        MultiHybrid.drive, FChan.honSys, FChan.honStep, ctMsg, Stage.keyGot, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]
    · refine couple_eq (realOf crs code (some x) rc g ρ cur) (idealOf (some x) rc g cur)
        (.inl (.inl false)) ?_ hI ⟨some x, rc, g, ρ, cur, rfl, rfl, h1, by simp, ?_⟩
      · cases g <;> simp_all [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart,
          sendIf, MultiHybrid.drive, Stage.keyGot, SPComp.map, SPComp.pure_bind]
      · cases g <;> simp_all [simLen]
  · refine couple_eq (realOf crs code (some x₀) rc g ρ cur) (idealOf (some x₀) rc g cur)
      (.inl (.inl false)) ?_ ?_ ⟨some x₀, rc, g, ρ, cur, rfl, rfl, h1, h2, h3⟩
    · cases g <;> simp [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart, sendIf,
        MultiHybrid.drive, Stage.keyGot, SPComp.map, SPComp.pure_bind]
    · simp [MultiHybrid.withSub, simH, simStart, simResume, MultiHybrid.drive, idealOf,
        FOTSched, FOTSched.sendSys, FOTSched.sendStep, SPComp.map, SPComp.pure_bind]

/-- The step on the wake. -/
theorem step_wake (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (hcode : ∀ a, decode (code a) = a)
    (xo : Option (Fin m → M × M)) (rc : Option ((Fin m → Bool) × (Fin m → gp.Scalar)))
    (g : Stage) (ρ : SRand gp m) (cur : ℕ) (hwf : WF xo rc g cur) (w : Unit) :
    rHoare eqPre
      ((realH crs code decode).step (realOf crs code xo rc g ρ cur) (.inl (.inr w)))
      (((simH gp m M).withSub (FOTSched otChoose)).step (idealOf xo rc g cur) (.inl (.inr w)))
      (stepPost (HRel crs code)) := by
  obtain ⟨h1, h2, h3⟩ := hwf
  by_cases hk : g = .kIn
  · subst hk
    obtain ⟨⟨c, r⟩, rfl⟩ : ∃ p, rc = some p := Option.isSome_iff_exists.mp (h1 (by simp))
    have hI : ((simH gp m M).withSub (FOTSched otChoose)).step (idealOf xo (some (c, r)) .kIn cur)
        (.inl (.inr w)) =
          SPComp.pure (idealOf xo (some (c, r)) .cWait cur, .inl (.inl false)) := by
      simp [MultiHybrid.withSub, simH, simStart, MultiHybrid.drive, idealOf, SPComp.pure_bind]
    have hc : cur = 0 := by simpa [simLen] using h3
    subst hc
    rcases xo with _ | x
    · refine couple_eq (realOf crs code none (some (c, r)) .cWait ρ 0)
        (idealOf none (some (c, r)) .cWait 0) (.inl (.inl false)) ?_ hI
        ⟨none, some (c, r), .cWait, ρ, 0, rfl, rfl, by simp, by simp, by simp [simLen]⟩
      simp [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart, pResume, sendIf,
        MultiHybrid.drive, FChan.honSys, FChan.honStep, keyMsg, ctMsg, Stage.keyGot,
        SPComp.map, SPComp.pure_bind]
    · refine couple_eq_sample (fun ρ' => realOf crs code (some x) (some (c, r)) .cWait ρ' 0)
        (idealOf (some x) (some (c, r)) .cWait 0) (.inl (.inl false)) ?_ hI
        fun ρ' => ⟨some x, some (c, r), .cWait, ρ', 0, rfl, rfl, by simp, by simp,
          by simp [simLen]⟩
      simp [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart, pResume, sendIf,
        MultiHybrid.drive, FChan.honSys, FChan.honStep, keyMsg, ctMsg, Stage.keyGot,
        SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  by_cases hc : g = .cIn
  · subst hc
    obtain ⟨⟨c, r⟩, rfl⟩ : ∃ p, rc = some p := Option.isSome_iff_exists.mp (h1 (by simp))
    obtain ⟨x, rfl⟩ : ∃ x, xo = some x := Option.isSome_iff_exists.mp (h2 (by simp))
    refine couple_eq (realOf crs code (some x) (some (c, r)) .fin ρ cur)
      (idealOf (some x) (some (c, r)) .fin cur) (.inl (.inr (some (otChoose x c)))) ?_ ?_
      ⟨some x, some (c, r), .fin, ρ, cur, rfl, rfl, by simp, by simp, by simp_all [simLen]⟩
    · have hcur : cur = 0 := by simpa [simLen] using h3
      subst hcur
      simp [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart, pResume,
        MultiHybrid.drive, FChan.honSys, FChan.honStep, ctMsg, Stage.keyGot, SPComp.map,
        SPComp.pure_bind, recvOut_senderMsg crs code decode hcode]
    · simp [MultiHybrid.withSub, simH, simStart, simResume, MultiHybrid.drive, idealOf,
        FOTSched, FOTSched.schedSys, FOTSched.schedStep, FOTSched.recvSys, FOTSched.recvStep,
        SPComp.map, SPComp.pure_bind]
  · refine couple_eq (realOf crs code xo rc g ρ cur) (idealOf xo rc g cur) (.inl (.inl false))
      ?_ ?_ ⟨xo, rc, g, ρ, cur, rfl, rfl, h1, h2, h3⟩
    · cases g <;> simp_all [realOf, realH_step_inl, MultiHybrid.stepFuel, partyH, pStart,
        pResume, MultiHybrid.drive, FChan.honSys, FChan.honStep, SPComp.map, SPComp.pure_bind]
    · cases g <;> simp_all [MultiHybrid.withSub, simH, simStart, MultiHybrid.drive, idealOf,
        SPComp.pure_bind]

/-! ## The squares -/

/-- **The PVW dual-mode OT with both parties honest, before the wake closure.** Ideal
functionality: `FOTSched otChoose`, the scheduled transfer of `m` message pairs. Real protocol:
`realH crs code decode`, the PVW parties with the CRS `crs` over the secure channel, inputs and
wakes on the honest port, the channel's adversary port forwarded. Simulator: `pvwSimH`, which
forwards the inputs and answers the channel from the stage of the message in flight and the input
status of `F`. Distance `0`, for every CRS, when `decode` inverts `code`. -/
theorem pvwH_realizesSim (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (hcode : ∀ a, decode (code a) = a) :
    RealizesSim (realH (m := m) crs code decode) (FOTSched otChoose) (pvwSimH gp m M)
      (fun _ _ => 0) := by
  refine (realizes_zero_of_coupling (rel := HRel crs code) ⟨?_, ?_⟩).1
  · exact ⟨none, none, .kWait, Classical.arbitrary _, 0, by simp [realOf, realH, partyH,
      MultiHybrid.withSub, MultiHybrid.tensor, PSt.init, Stage.keyGot, keyMsg]; rfl,
      rfl, by simp, by simp, by simp [simLen]⟩
  · rintro t u e ⟨xo, rc, g, ρ, cur, rfl, rfl, hwf⟩
    rcases e with ((x | c) | w) | a
    · exact step_send crs code decode xo rc g ρ cur hwf x
    · exact step_recv crs code decode xo rc g ρ cur hwf c
    · exact step_wake crs code decode hcode xo rc g ρ cur hwf w
    · exact step_adv crs code decode xo rc g ρ cur hwf a

/-- The deliveries of the wake closure: the channel's `deliver` wakes the parties. -/
def dlvH : ChanAEv (V gp m) → Option Unit
  | .deliver => some ()
  | _ => none

/-- The answer to a wake that would need a second pass. -/
def cutH (_ : Unit) : InOut m M ⊕ ChanAOut (V gp m) Unit := .inl (.inl false)

/-- The idle event: the channel's `idle`. -/
def idleH : (InEv m M ⊕ ChanAEv (V gp m)) ⊕ Unit := .inl (.inr .idle)

/-- The protocol is idle at the channel's `idle`. -/
theorem realH_idleAt (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M) :
    MultiHybrid.IdleAt (realH (m := m) crs code decode) (wakeEv dlvH (idleH (m := m) (M := M))).2
      (.inr .ack) := by
  rintro ⟨⟨st, u⟩, ch⟩
  simp [wakeEv, dlvH, idleH, realH_step_inr, FChan.advStep]

/-- The simulator over any subroutine is idle at the channel's `idle`. -/
theorem simH_idleAt {υ : Type} (X : Sys υ (InEv m M ⊕ SchedEv) (InOut m M ⊕ SchedOut)) :
    MultiHybrid.IdleAt ((simH gp m M).withSub X) (wakeEv dlvH (idleH (m := m) (M := M))).2
      (.inr .ack) := by
  rintro ⟨s, u⟩
  simp [wakeEv, dlvH, idleH, MultiHybrid.withSub, simH, simStart, MultiHybrid.drive,
    SPComp.pure_bind]

/-- **The PVW dual-mode OT with both parties honest, with activation on delivery.** Ideal
functionality: `FOTSched otChoose`, the scheduled transfer of `m` message pairs. Real protocol:
the wake closure of `realH crs code decode`, in which the channel's delivery activates the
parties in the same activation: the sender stores the key and sends its ciphertexts, the receiver
decrypts and outputs. Simulator: the wake closure of `pvwSimH`; inputs hidden, wakes public.
Distance `0`, for every CRS, when `decode` inverts `code`. -/
theorem pvwH_wake_realizesSim (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (hcode : ∀ a, decode (code a) = a) :
    RealizesSim ((realH (m := m) crs code decode).wakeClose dlvH cutH) (FOTSched otChoose)
      ((pvwSimH gp m M).wakeClose dlvH (fun _ _ h => congrArg dlvH h) cutH
        (fun _ => Sum.LiftRel.inl trivial)) (fun _ _ => 0) :=
  RealizesSim.wakeClose dlvH _ cutH _ idleH _ _ (realH_idleAt crs code decode)
    (simH_idleAt (FOTSched otChoose)) (pvwH_realizesSim crs code decode hcode)

end CatCrypt.Crypto.OT.PVWHonest

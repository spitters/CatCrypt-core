/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCWake
public import CatCryptCore.Crypto.OT.FOTSched
public import CatCryptCore.Crypto.UCChannelLift
public import CatCryptCore.Crypto.OTExtension.IKNPSquare

/-!
# IKNP over scheduled base OTs and a channel, with activation on delivery

**Ideal functionality.** `FOTSched otChoose` (both parties honest) and
`FOTSchedSH otChoose leak` (a semi-honest corrupt party, `leak = leakSend` or
`leakRecv otChoose`): the scheduled transfer of `m` message pairs of `OT/FOTSched.lean`, whose
adversary delivers the receiver's output and, for a corrupt party, reads that party's view (its
input, and for the receiver its delivered output) on the adversary port.

**Real protocol.** IKNP with `κ ≥ 1` base OTs. The sender and the receiver are one multi-call
hybrid (`partyW`) over `κ` scheduled base OTs `FOTSchedPar (Fin κ) baseOut` beside the secure
channel `FChan ChannelCap.secure`, whose adversary ports are forwarded. The receiver's input `r`
gives the column pairs of `T` and `T + r` to the base OTs; the sender's input `x` gives the bits
of its secret `s` as choices. On the wake `wakeS i` the sender fetches the column of base OT `i`;
once it holds every column it sends the masked message pairs. On the wake `wakeR` the receiver
reads the message and outputs its unmasked messages. The randomness `(T, s)` is drawn at the first
input of a party (`iknpW`). A semi-honest corruption is an adversary event that shows the corrupt
party's completed view: the sender's secret and columns once it has sent (`iknpRealS`), the
receiver's matrix, the masked message pairs and its output once it has received them
(`iknpRealR`). The wake closure `Sys.wakeClose dlvW` of `CatCryptCore/Crypto/UCWake.lean` makes the
delivery of base OT `i` activate the sender with `wakeS i` and the delivery of the channel
activate the receiver with `wakeR`, in the same activation.

**Simulators.** `simW` forwards the inputs to the honest port of the ideal functionality. It
simulates the base OTs from the input status that the functionality reports and the channel with
every message replaced by a fixed value. At the wake that completes the sender's columns it sends
the simulated message, and at the wake of the receiver that reads it it delivers the output on the
functionality and passes it on. It is opaque for the view with inputs hidden and wakes and
adversary events public (`simW_opaque`). Against a corrupt sender (`iknpSimSW`) it draws the
sender's view by `iknpSimS` at the sender's completing wake; against a corrupt receiver
(`iknpSimRW`) it takes the receiver's choices and output from the leak port at the receiver's wake
and completes the view by `iknpSimR`.

**Proof.** With fixed randomness the parties refine an abstract system on the public flags and
the inputs (`view_realW_eq`, by a state map with an invariant). The abstract system reads the
randomness only where it completes an exposed view, so the draw moves there
(`KeyedSys.view_lazy`). From there the abstract system realizes the simulated functionality at
distance `0` when the simulator's draw couples with the exposed view (`lazyA_realizes`): the
uniform columns for the sender (`iknpSView_sample`), the uniform pads for the receiver
(`crRView_sample`) after the correlation-robust hash hop (`lazyR_realizes_cr`).

## Main definitions

* `partyW`, `realW`, `iknpW`: the parties, with fixed and with drawn randomness.
* `ASt`, `aStep`, `aKeyed`: the abstract system.
* `simW`: the simulator; `iknpSimH`, `iknpSimSW`, `iknpSimRW` for the three cases.
* `iknpWakeCRRed`: the reduction of an environment to the correlation-robust hash game.
* `dlvW`, `cutW`: the deliveries and the cut-off of the wake closure.

## Main results

* `iknpH_realizesSim`, `iknpH_wake_realizesSim`: both parties honest, distance `0`.
* `iknpS_realizesSim`, `iknpS_wake_realizesSim`: a semi-honest corrupt sender, distance `0`.
* `iknpR_realizesSim`, `iknpR_wake_realizesSim`: a semi-honest corrupt receiver, bound
  `CRHash_Advantage H (iknpWakeCRRed H Z)`.
* `iknpW_wakeClose`: the wake closure of a realization behind `simW`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete

variable {τ υ ζ E O : Type}

/-- The state `x` with its proof of `Inv` if `Inv x` holds, and `d` otherwise. -/
private noncomputable def liftInvW (Inv : τ → Prop) (d : {t // Inv t}) (x : τ) : {t // Inv t} := by
  classical exact if h : Inv x then ⟨x, h⟩ else d

/-- The system `R` on the states satisfying `Inv`: each new state that fails `Inv` is replaced by
the initial state. -/
private noncomputable def restrictInvW (R : Sys τ E O) (Inv : τ → Prop) (h : Inv R.init) :
    Sys {t // Inv t} E O where
  init := ⟨R.init, h⟩
  step t e := SPComp.map (fun p => (liftInvW Inv ⟨R.init, h⟩ p.1, p.2)) (R.step t.1 e)

/-- Two systems related by a state map `f` have equal views when `f` sends the initial state to
the initial state and commutes with single steps from the states satisfying an invariant `Inv`,
which holds initially and at every state a step from a state satisfying it reaches. -/
theorem view_eq_of_stepMap_on (R : Sys τ E O) (I : Sys υ E O) (Inv : τ → Prop)
    (f : τ → υ) (hInv : Inv R.init) (hinit : f R.init = I.init)
    (hpres : ∀ t e, Inv t → ∃ (α : Type) (c : SPComp α) (g : α → τ × O),
      R.step t e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧ ∀ a, Inv (g a).1)
    (hstep : ∀ t e, Inv t → SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = I.step (f t) e)
    (Z : Strat ζ E O) : view R Z = view I Z := by
  have hnorm : ∀ (t : {t // Inv t}) e,
      SPComp.map (fun p => ((liftInvW Inv ⟨R.init, hInv⟩ p.1).1, p.2)) (R.step t.1 e) =
        R.step t.1 e := by
    intro t e
    obtain ⟨α, c, g, hc, hg⟩ := hpres t.1 e t.2
    rw [hc]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, liftInvW, dite_eq_left (hg _)]
  have h₁ := view_eq_of_stepMap (restrictInvW R Inv hInv) R Subtype.val rfl (fun t e => by
      have h := hnorm t e
      simp only [restrictInvW, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] at h ⊢
      exact h) Z
  have h₂ := view_eq_of_stepMap (restrictInvW R Inv hInv) I (fun t => f t.1) hinit (fun t e => by
      rw [← hstep t.1 e t.2]
      conv => rhs; rw [← hnorm t e]
      simp only [restrictInvW, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]) Z
  rw [← h₁, h₂]

end CatCrypt.Crypto.UCTransparent

namespace CatCrypt.Crypto.OT.IKNPWake

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform CatCrypt.Relational
open CatCrypt.Crypto.OT.IKNPSquare
open CatCrypt.Crypto.Choreography (ChannelCap)
open scoped ENNReal

variable {κ m : ℕ} {M : Type}

/-! ## Ports and subroutines -/

/-- A base-OT message pair: two columns. -/
abbrev BPair (m : ℕ) := (Fin m → Bool) × (Fin m → Bool)

/-- The output of a base OT: the column selected by the choice bit. -/
def baseOut (p : BPair m) (b : Bool) : Fin m → Bool := if b then p.2 else p.1

/-- The message of the IKNP sender: the masked message pairs. -/
abbrev Msg (m : ℕ) (M : Type) := Fin m → M × M

/-- The leakage of a message on the channel: nothing beyond its presence. -/
def msgLeak (_ : Msg m M) : Unit := ()

/-- The `κ` scheduled base OTs, one copy of `FOTSched baseOut` per index. -/
noncomputable def baseG (κ m : ℕ) :=
  FOTSchedPar (Fin κ) (baseOut (m := m))

/-- The secure channel for the message of the sender. -/
noncomputable def chanC (m : ℕ) (M : Type) :=
  FChan ChannelCap.secure (msgLeak (m := m) (M := M))

/-- The honest events of the base OTs. -/
abbrev HEv (κ m : ℕ) := (Fin κ × BPair m) ⊕ (Fin κ × Bool)

/-- The honest outputs of the base OTs. -/
abbrev HOut (m : ℕ) := Bool ⊕ Option (Fin m → Bool)

/-- The adversary events of the base OTs and of the channel. -/
abbrev AEv (κ m : ℕ) (M : Type) := (Fin κ × SchedEv) ⊕ ChanAEv (Msg m M)

/-- The adversary outputs of the base OTs and of the channel. -/
abbrev AOut (m : ℕ) (M : Type) := SchedOut ⊕ ChanAOut (Msg m M) Unit

/-- The inputs of IKNP: the sender's message pairs and the receiver's choices. -/
abbrev InEv (m : ℕ) (M : Type) := (Fin m → M × M) ⊕ (Fin m → Bool)

/-- The outputs of IKNP: the sender's completion bit and the receiver's output. -/
abbrev InOut (m : ℕ) (M : Type) := Bool ⊕ Option (Fin m → M)

/-- The wakes: the sender for the base OT `i`, and the receiver for the channel. -/
inductive WakeEv (κ : ℕ) where
  /-- The sender is woken by the delivery of the base OT `i`. -/
  | wakeS (i : Fin κ)
  /-- The receiver is woken by the delivery of the channel. -/
  | wakeR

/-- The state of the base OTs beside the channel. -/
abbrev SubSt (κ m : ℕ) (M : Type) :=
  (Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) × ChanSt (Msg m M)

/-! ## The parties -/

/-- The phase of an activation of the parties: which answer is awaited. -/
inductive Ph (κ : ℕ) where
  /-- No call is pending. -/
  | idle
  /-- The sender's choice bit to the base OT `j`. -/
  | sIn (j : ℕ)
  /-- The receiver's column pair to the base OT `j`. -/
  | rIn (j : ℕ)
  /-- The sender's fetch of the column of the base OT `i`. -/
  | fetch (i : Fin κ)
  /-- The sender's send on the channel. -/
  | sendY
  /-- The receiver's receive on the channel. -/
  | recvY

/-- The state of the two IKNP parties. -/
structure PSt (κ m : ℕ) (M : Type) where
  /-- The sender's message pairs. -/
  xo : Option (Fin m → M × M)
  /-- The receiver's choices. -/
  ro : Option (Fin m → Bool)
  /-- The columns the sender has fetched. -/
  cols : Fin κ → Option (Fin m → Bool)
  /-- Whether the sender has sent its message. -/
  ysent : Bool
  /-- The message the receiver has received. -/
  yrecv : Option (Fin m → M × M)
  /-- The phase of the activation. -/
  ph : Ph κ

/-- The initial state of the parties. -/
def PSt.init : PSt κ m M := ⟨none, none, fun _ => none, false, none, .idle⟩

/-- Whether every column is present. -/
def allCols (c : Fin κ → Option (Fin m → Bool)) : Bool := decide (∀ i, (c i).isSome = true)

/-- The fetched columns as a matrix. -/
def colsVal (c : Fin κ → Option (Fin m → Bool)) : Fin κ → Fin m → Bool :=
  fun i => (c i).getD fun _ => false

/-- The sender's choice bit to the base OT `j`. -/
def sCall (k : IKNPKey κ m) (j : ℕ) (h : j < κ) : HEv κ m ⊕ ChanHEv (Msg m M) :=
  .inl (.inr (⟨j, h⟩, k.2 ⟨j, h⟩))

/-- The receiver's column pair to the base OT `j`. -/
def rCall (k : IKNPKey κ m) (r : Fin m → Bool) (j : ℕ) (h : j < κ) :
    HEv κ m ⊕ ChanHEv (Msg m M) :=
  .inl (.inl (⟨j, h⟩, iknpBaseIn k.1 r ⟨j, h⟩))

/-- The view of the sender once it has sent its message: its secret and its columns. -/
def sviewOf (k : IKNPKey κ m) (st : PSt κ m M) : Option (IKNPSenderView κ m Unit) :=
  match st.xo with
  | some _ => if st.ysent then some (k.2, (), colsVal st.cols) else none
  | none => none

section Parties

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L)

/-- The view of the receiver once it has received the message: its matrix, the masked message
pairs and its output. -/
def rviewOf (k : IKNPKey κ m) (st : PSt κ m M) :
    Option (IKNPReceiverView κ m M Unit × (Fin m → M)) :=
  match st.ro, st.yrecv with
  | some r, some y => some ((k.1, (), y), iknpRecvOut H r k.1 y)
  | _, _ => none

/-- The answer of the parties to a corruption event `p`: `ans` of the corrupt party's views. -/
def peekAns (k : IKNPKey κ m) (st : PSt κ m M) (p : P) : L :=
  ans ((sviewOf k st).map φS) ((rviewOf H k st).map φR) p

/-- The first step of an activation of the parties with randomness `k = (T, s)`. -/
def pStart [NeZero κ] (k : IKNPKey κ m) (st : PSt κ m M) :
    ((InEv m M ⊕ WakeEv κ) ⊕ P) →
      PSt κ m M × ((HEv κ m ⊕ ChanHEv (Msg m M)) ⊕ (InOut m M ⊕ L))
  | .inl (.inl (.inl x)) => match st.xo with
    | some _ => (st, .inr (.inl (.inl false)))
    | none => ({ st with xo := some x, ph := .sIn 0 }, .inl (sCall k 0 (NeZero.pos κ)))
  | .inl (.inl (.inr r)) => match st.ro with
    | some _ => (st, .inr (.inl (.inr none)))
    | none => ({ st with ro := some r, ph := .rIn 0 }, .inl (rCall k r 0 (NeZero.pos κ)))
  | .inl (.inr (.wakeS i)) => match st.xo with
    | some _ => ({ st with ph := .fetch i }, .inl (.inl (.inr (i, k.2 i))))
    | none => (st, .inr (.inl (.inl false)))
  | .inl (.inr .wakeR) => match st.ro with
    | some _ => ({ st with ph := .recvY }, .inl (.inr .recv))
    | none => (st, .inr (.inl (.inr none)))
  | .inr p => (st, .inr (.inr (peekAns H φS φR ans k st p)))

/-- The sender's step on the fetched column `q` of the base OT `i`: the column is kept, and the
masked message pairs are sent once every column is present. -/
def pFetch (k : IKNPKey κ m) (st : PSt κ m M) (i : Fin κ) (q : Fin m → Bool) :
    PSt κ m M × ((HEv κ m ⊕ ChanHEv (Msg m M)) ⊕ (InOut m M ⊕ L)) :=
  let c := Function.update st.cols i (some q)
  match st.xo with
  | some x =>
    if allCols c && !st.ysent then
      ({ st with cols := c, ysent := true, ph := .sendY },
        .inl (.inr (.send (iknpSenderMsg H x k.2 (colsVal c)))))
    else ({ st with cols := c, ph := .idle }, .inr (.inl (.inl false)))
  | none => ({ st with cols := c, ph := .idle }, .inr (.inl (.inl false)))

/-- The step of the parties on the answer `o` of a call. -/
def pResume (k : IKNPKey κ m) (st : PSt κ m M) (o : HOut m ⊕ ChanHOut (Msg m M)) :
    PSt κ m M × ((HEv κ m ⊕ ChanHEv (Msg m M)) ⊕ (InOut m M ⊕ L)) :=
  match st.ph with
  | .sIn j =>
    if h : j + 1 < κ then ({ st with ph := .sIn (j + 1) }, .inl (sCall k (j + 1) h))
    else ({ st with ph := .idle }, .inr (.inl (.inl false)))
  | .rIn j =>
    if h : j + 1 < κ then
      ({ st with ph := .rIn (j + 1) }, .inl (rCall k (st.ro.getD fun _ => false) (j + 1) h))
    else ({ st with ph := .idle }, .inr (.inl (.inr none)))
  | .fetch i => match o with
    | .inl (.inr (some q)) => pFetch H k st i q
    | _ => ({ st with ph := .idle }, .inr (.inl (.inl false)))
  | .sendY => ({ st with ph := .idle }, .inr (.inl (.inl false)))
  | .recvY => match o with
    | .inr (.got (some y)) =>
      ({ st with yrecv := some y, ph := .idle },
        .inr (.inl (.inr (some (iknpRecvOut H (st.ro.getD fun _ => false) k.1 y)))))
    | _ => ({ st with ph := .idle }, .inr (.inl (.inr none)))
  | .idle => (st, .inr (.inl (.inl false)))

/-- **The IKNP parties** with randomness `k = (T, s)` over the base OTs beside the channel. The
receiver's input `r` gives the column pairs of `T` and `T + r` to the `κ` base OTs; the sender's
input `x` gives the bits of `s` as choices. On the wake `wakeS i` the sender fetches the column
of the base OT `i`, and once it holds every column it sends the masked message pairs; on the
wake `wakeR` the receiver reads the message and outputs its unmasked messages. A corruption
event is answered by `ans` of the corrupt party's views. -/
noncomputable def partyW [NeZero κ] (k : IKNPKey κ m) :
    MultiHybrid (PSt κ m M) ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L)
      (HEv κ m ⊕ ChanHEv (Msg m M)) (HOut m ⊕ ChanHOut (Msg m M)) where
  init := PSt.init
  fuel := κ + 1
  start st e := SPComp.pure (pStart H φS φR ans k st e)
  resume st o := SPComp.pure (pResume (L := L) H k st o)
  finish st _ := SPComp.pure ({ st with ph := .idle }, .inl (.inl false))
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The relabelling that moves the corruption events to the adversary port. -/
def peekEv : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P) → ((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M
  | .inl e => .inl (.inl e)
  | .inr (.inl a) => .inr a
  | .inr (.inr p) => .inl (.inr p)

/-- The relabelling that moves the answers of corruption events to the adversary port. -/
def peekOut : (InOut m M ⊕ L) ⊕ AOut m M → InOut m M ⊕ (AOut m M ⊕ L)
  | .inl (.inl o) => .inl o
  | .inl (.inr l) => .inr (.inr l)
  | .inr a => .inr (.inl a)

/-- **The IKNP protocol with randomness `k`**: the parties over the `κ` base OTs beside the
channel, the adversary ports of both forwarded, the corruption events on the adversary port. -/
noncomputable def realW [NeZero κ] (k : IKNPKey κ m) :
    Sys ((PSt κ m M × Unit) × SubSt κ m M) ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
      (InOut m M ⊕ (AOut m M ⊕ L)) :=
  (((partyW H φS φR ans k).tensor (MultiHybrid.idSim (AEv κ m M) (AOut m M))).withSub
    ((baseG κ m).withChan (chanC m M))).mapPorts peekEv peekOut

end Parties

/-! ## Activations of the parties against the base OTs and the channel -/

/-- The honest port of the base OTs beside the channel. -/
noncomputable abbrev subL (κ m : ℕ) (M : Type) :
    Sys (SubSt κ m M) (HEv κ m ⊕ ChanHEv (Msg m M)) (HOut m ⊕ ChanHOut (Msg m M)) :=
  Sys.chanPortL (Sys.ofPorts FOTSched.sendSys.indexed FOTSched.recvSys.indexed) FChan.honSys
    (baseG κ m).init (chanC m M).init

/-- The adversary port of the base OTs beside the channel. -/
noncomputable abbrev subR (κ m : ℕ) (M : Type) :
    Sys (SubSt κ m M) (AEv κ m M) (AOut m M) :=
  Sys.chanPortR (FOTSched.schedSys (baseOut (m := m))).indexed
    (FChan.advSys ChannelCap.secure msgLeak) (baseG κ m).init (chanC m M).init

/-- A step of the base OTs beside the channel on an honest event is a step of `subL`. -/
theorem sub_step_inl (t : SubSt κ m M) (e : HEv κ m ⊕ ChanHEv (Msg m M)) :
    ((baseG κ m).withChan (chanC m M)).step t (.inl e) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((subL κ m M).step t e) :=
  Sys.withChan_step_inl (fun _ _ => rfl) (fun _ _ => rfl) t e

/-- A step of the base OTs beside the channel on an adversary event is a step of `subR`. -/
theorem sub_step_inr (t : SubSt κ m M) (e : AEv κ m M) :
    ((baseG κ m).withChan (chanC m M)).step t (.inr e) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((subR κ m M).step t e) :=
  Sys.withChan_step_inr (fun _ _ => rfl) (fun _ _ => rfl) t e

/-- Unfolding lemma of `subL`: the sender's choice bit to the base OT `i`. -/
theorem subL_step_recv (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) (ch : ChanSt (Msg m M))
    (i : Fin κ) (b : Bool) :
    (subL κ m M).step (c, ch) (.inl (.inr (i, b))) =
      SPComp.pure ((Function.update c i (FOTSched.recvStep (c i) b).1, ch),
        .inl (.inr (FOTSched.recvStep (c i) b).2)) := by
  simp [subL, Sys.chanPortL, FOTSched.recvSys, SPComp.map, SPComp.pure_bind]

/-- Unfolding lemma of `subL`: the receiver's column pair to the base OT `i`. -/
theorem subL_step_send (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) (ch : ChanSt (Msg m M))
    (i : Fin κ) (p : BPair m) :
    (subL κ m M).step (c, ch) (.inl (.inl (i, p))) =
      SPComp.pure ((Function.update c i (FOTSched.sendStep (c i) p).1, ch),
        .inl (.inl (FOTSched.sendStep (c i) p).2)) := by
  simp [subL, Sys.chanPortL, FOTSched.sendSys, SPComp.map, SPComp.pure_bind]

/-- Unfolding lemma of `subL`: an honest event of the channel. -/
theorem subL_step_chan (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) (ch : ChanSt (Msg m M))
    (e : ChanHEv (Msg m M)) :
    (subL κ m M).step (c, ch) (.inr e) =
      SPComp.pure ((c, (FChan.honStep ch e).1), .inr (FChan.honStep ch e).2) := by
  simp [subL, Sys.chanPortL, FChan.honSys, SPComp.map, SPComp.pure_bind]

/-- The base OTs after the sender's choice bits to the base OTs `j, j + 1, …`. -/
def sUpd (k : IKNPKey κ m) (j : ℕ) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) :
    Fin κ → SchedSt (BPair m) Bool (Fin m → Bool) :=
  fun i => if j ≤ i.val then (FOTSched.recvStep (c i) (k.2 i)).1 else c i

/-- The base OTs after the receiver's column pairs to the base OTs `j, j + 1, …`. -/
def rUpd (k : IKNPKey κ m) (r : Fin m → Bool) (j : ℕ)
    (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) :
    Fin κ → SchedSt (BPair m) Bool (Fin m → Bool) :=
  fun i => if j ≤ i.val then (FOTSched.sendStep (c i) (iknpBaseIn k.1 r i)).1 else c i

section Drive

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L) [NeZero κ] (k : IKNPKey κ m)

/-- Unfolding lemma of `partyW`: the first step. -/
@[simp] theorem partyW_start (st : PSt κ m M) (e : (InEv m M ⊕ WakeEv κ) ⊕ P) :
    (partyW H φS φR ans k).start st e = SPComp.pure (pStart H φS φR ans k st e) := rfl

/-- Unfolding lemma of `partyW`: the step on an answer. -/
@[simp] theorem partyW_resume (st : PSt κ m M) (o : HOut m ⊕ ChanHOut (Msg m M)) :
    (partyW H φS φR ans k).resume st o = SPComp.pure (pResume (L := L) H k st o) := rfl

omit [NeZero κ] in
/-- The sender's next choice bit. -/
theorem pResume_sIn {st : PSt κ m M} {j : ℕ} (hst : st.ph = .sIn j) (h1 : j + 1 < κ)
    (o : HOut m ⊕ ChanHOut (Msg m M)) :
    pResume (L := L) H k st o = ({ st with ph := .sIn (j + 1) }, .inl (sCall k (j + 1) h1)) := by
  simp [pResume, hst, h1]

omit [NeZero κ] in
/-- The sender's last choice bit. -/
theorem pResume_sIn_last {st : PSt κ m M} {j : ℕ} (hst : st.ph = .sIn j) (h1 : ¬j + 1 < κ)
    (o : HOut m ⊕ ChanHOut (Msg m M)) :
    pResume (L := L) H k st o = ({ st with ph := .idle }, .inr (.inl (.inl false))) := by
  simp [pResume, hst, h1]

omit [NeZero κ] in
/-- The receiver's next column pair. -/
theorem pResume_rIn {st : PSt κ m M} {j : ℕ} {r : Fin m → Bool} (hst : st.ph = .rIn j)
    (hr : st.ro = some r) (h1 : j + 1 < κ) (o : HOut m ⊕ ChanHOut (Msg m M)) :
    pResume (L := L) H k st o = ({ st with ph := .rIn (j + 1) }, .inl (rCall k r (j + 1) h1)) := by
  simp [pResume, hst, h1, hr]

omit [NeZero κ] in
/-- The receiver's last column pair. -/
theorem pResume_rIn_last {st : PSt κ m M} {j : ℕ} (hst : st.ph = .rIn j) (h1 : ¬j + 1 < κ)
    (o : HOut m ⊕ ChanHOut (Msg m M)) :
    pResume (L := L) H k st o = ({ st with ph := .idle }, .inr (.inl (.inr none))) := by
  simp [pResume, hst, h1]

omit [AddCommGroup M] [NeZero κ] in
/-- Unfolding lemma of `subL` at a choice bit of the sender. -/
theorem subL_step_sCall (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (j : ℕ) (hj : j < κ) :
    (subL κ m M).step (c, ch) (sCall k j hj) =
      SPComp.pure ((Function.update c ⟨j, hj⟩ (FOTSched.recvStep (c ⟨j, hj⟩) (k.2 ⟨j, hj⟩)).1, ch),
        .inl (.inr (FOTSched.recvStep (c ⟨j, hj⟩) (k.2 ⟨j, hj⟩)).2)) :=
  subL_step_recv c ch _ _

omit [AddCommGroup M] [NeZero κ] in
/-- Unfolding lemma of `subL` at a column pair of the receiver. -/
theorem subL_step_rCall (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (r : Fin m → Bool) (j : ℕ) (hj : j < κ) :
    (subL κ m M).step (c, ch) (rCall k r j hj) =
      SPComp.pure ((Function.update c ⟨j, hj⟩
        (FOTSched.sendStep (c ⟨j, hj⟩) (iknpBaseIn k.1 r ⟨j, hj⟩)).1, ch),
        .inl (.inl (FOTSched.sendStep (c ⟨j, hj⟩) (iknpBaseIn k.1 r ⟨j, hj⟩)).2)) :=
  subL_step_send c ch _ _

omit [AddCommGroup M] [NeZero κ] in
/-- One more choice bit of the sender in `sUpd`. -/
theorem sUpd_succ (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) (j : ℕ) (hj : j < κ) :
    sUpd k (j + 1) (Function.update c ⟨j, hj⟩ (FOTSched.recvStep (c ⟨j, hj⟩) (k.2 ⟨j, hj⟩)).1) =
      sUpd k j c := by
  funext i
  simp only [sUpd, Function.update_apply]
  split_ifs <;> grind [Fin.ext_iff]

omit [AddCommGroup M] [NeZero κ] in
/-- The last choice bit of the sender in `sUpd`. -/
theorem sUpd_last (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) (j : ℕ) (hj : j < κ)
    (h1 : ¬j + 1 < κ) :
    Function.update c ⟨j, hj⟩ (FOTSched.recvStep (c ⟨j, hj⟩) (k.2 ⟨j, hj⟩)).1 = sUpd k j c := by
  funext i
  simp only [sUpd, Function.update_apply]
  split_ifs <;> grind [Fin.ext_iff]

omit [AddCommGroup M] [NeZero κ] in
/-- One more column pair of the receiver in `rUpd`. -/
theorem rUpd_succ (r : Fin m → Bool) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (j : ℕ) (hj : j < κ) :
    rUpd k r (j + 1) (Function.update c ⟨j, hj⟩
      (FOTSched.sendStep (c ⟨j, hj⟩) (iknpBaseIn k.1 r ⟨j, hj⟩)).1) = rUpd k r j c := by
  funext i
  simp only [rUpd, Function.update_apply]
  split_ifs <;> grind [Fin.ext_iff]

omit [AddCommGroup M] [NeZero κ] in
/-- The last column pair of the receiver in `rUpd`. -/
theorem rUpd_last (r : Fin m → Bool) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (j : ℕ) (hj : j < κ) (h1 : ¬j + 1 < κ) :
    Function.update c ⟨j, hj⟩ (FOTSched.sendStep (c ⟨j, hj⟩) (iknpBaseIn k.1 r ⟨j, hj⟩)).1 =
      rUpd k r j c := by
  funext i
  simp only [rUpd, Function.update_apply]
  split_ifs <;> grind [Fin.ext_iff]

/-- The sender's choice bits to the base OTs `j, …, κ - 1`, in one activation. -/
theorem drive_sIn : ∀ (n j : ℕ) (hj : j < κ), κ ≤ j + n → ∀ (st : PSt κ m M), st.ph = .sIn j →
    ∀ (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) (ch : ChanSt (Msg m M)),
    (partyW H φS φR ans k).drive (subL κ m M) n st (.inl (sCall k j hj)) (c, ch) =
      SPComp.pure ({ st with ph := .idle }, (sUpd k j c, ch), .inl (.inl false)) := by
  intro n
  induction n with
  | zero => intro j hj h; omega
  | succ n ih =>
    intro j hj hn st hst c ch
    simp only [MultiHybrid.drive, subL_step_sCall, SPComp.pure_bind, partyW_resume]
    by_cases h1 : j + 1 < κ
    · rw [pResume_sIn H k hst h1]
      dsimp only
      rw [ih (j + 1) h1 (by omega) _ rfl, sUpd_succ]
    · rw [pResume_sIn_last H k hst h1]
      simp only [MultiHybrid.drive, sUpd_last k c j hj h1]

/-- The receiver's column pairs to the base OTs `j, …, κ - 1`, in one activation. -/
theorem drive_rIn (r : Fin m → Bool) : ∀ (n j : ℕ) (hj : j < κ), κ ≤ j + n →
    ∀ (st : PSt κ m M), st.ph = .rIn j → st.ro = some r →
    ∀ (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) (ch : ChanSt (Msg m M)),
    (partyW H φS φR ans k).drive (subL κ m M) n st (.inl (rCall k r j hj)) (c, ch) =
      SPComp.pure ({ st with ph := .idle }, (rUpd k r j c, ch), .inl (.inr none)) := by
  intro n
  induction n with
  | zero => intro j hj h; omega
  | succ n ih =>
    intro j hj hn st hst hr c ch
    simp only [MultiHybrid.drive, subL_step_rCall, SPComp.pure_bind, partyW_resume]
    by_cases h1 : j + 1 < κ
    · rw [pResume_rIn H k hst hr h1]
      dsimp only
      rw [ih (j + 1) h1 (by omega) { st with ph := .rIn (j + 1) } rfl hr, rUpd_succ]
    · rw [pResume_rIn_last H k hst h1]
      simp only [MultiHybrid.drive]
      rw [rUpd_last k r c j hj h1]

end Drive

/-! ## The abstract system

The abstract system keeps the public flags of the run, the parties' inputs and the channel with
every message replaced by a fixed value. It reads the key only where a corrupt party's view is
completed: at the wake of the sender that completes its columns (`lS`) and at the wake of the
receiver that reads the message (`lR`). -/

/-- The state of the abstract system. -/
structure ASt (κ m : ℕ) (M LS LR : Type) where
  /-- The sender's message pairs. -/
  xo : Option (Fin m → M × M)
  /-- The receiver's choices. -/
  ro : Option (Fin m → Bool)
  /-- The base OTs whose output has been delivered. -/
  dR : Fin κ → Bool
  /-- The columns the sender has fetched. -/
  col : Fin κ → Bool
  /-- Whether the sender has sent its message. -/
  ysent : Bool
  /-- The channel, each message replaced by a fixed value. -/
  ch : ChanSt (Msg m M)
  /-- Whether the receiver has received the message. -/
  yrecv : Bool
  /-- The completed view of the sender, as the corruption exposes it. -/
  lvS : Option LS
  /-- The completed view of the receiver, as the corruption exposes it. -/
  lvR : Option LR

/-- The initial abstract state. -/
def ASt.init {LS LR : Type} : ASt κ m M LS LR :=
  ⟨none, none, fun _ => false, fun _ => false, false, FChan.initSt, false, none, none⟩

/-- Whether every flag is set. -/
def allB (c : Fin κ → Bool) : Bool := decide (∀ i, c i = true)

/-- The fixed value that replaces each message on the abstract channel. -/
def y0 [Zero M] : Msg m M := fun _ => (0, 0)

/-- Every message of the channel replaced by `y0`. -/
def mapC [Zero M] (ch : ChanSt (Msg m M)) : ChanSt (Msg m M) :=
  ⟨ch.queue.map fun _ => y0, ch.cursor, ch.inbox.map fun _ => y0⟩

/-- The output of a sender activation. -/
abbrev outS {L : Type} : InOut m M ⊕ (AOut m M ⊕ L) := .inl (.inl false)

/-- The output of an adversary activation of the base OTs. -/
abbrev outA {L : Type} (o : SchedOut) : InOut m M ⊕ (AOut m M ⊕ L) := .inr (.inl (.inl o))

section Abstract

variable [Zero M] {LS LR P L : Type} (ans : Option LS → Option LR → P → L)

/-- Whether the wake `wakeS i` completes the sender's columns. -/
def revealS (a : ASt κ m M LS LR) (i : Fin κ) : Bool :=
  a.xo.isSome && a.ro.isSome && a.dR i && !a.col i && allB (Function.update a.col i true) &&
    !a.ysent

/-- Whether the wake `wakeR` gives the receiver its message for the first time. -/
def revealR (a : ASt κ m M LS LR) : Bool :=
  a.ro.isSome && a.xo.isSome && !a.ch.inbox.isEmpty && a.lvR.isNone

/-- The abstract step on the wake of the sender for the base OT `i`. -/
def aWakeS (vS : (Fin m → M × M) → (Fin m → Bool) → LS) (a : ASt κ m M LS LR) (i : Fin κ) :
    ASt κ m M LS LR :=
  match a.xo, a.ro with
  | some x, some r =>
    if a.dR i && !a.col i then
      if allB (Function.update a.col i true) && !a.ysent then
        { a with col := Function.update a.col i true, ysent := true,
                 ch := (FChan.honStep a.ch (.send y0)).1, lvS := some (vS x r) }
      else { a with col := Function.update a.col i true }
    else a
  | _, _ => a

/-- The abstract step on the wake of the receiver. -/
def aWakeR (vR : (Fin m → M × M) → (Fin m → Bool) → LR) (a : ASt κ m M LS LR) {L : Type} :
    ASt κ m M LS LR × (InOut m M ⊕ (AOut m M ⊕ L)) :=
  match a.ro with
  | none => (a, .inl (.inr none))
  | some r => match a.ch.inbox with
    | [] => (a, .inl (.inr none))
    | _ :: rest => match a.xo with
      | some x =>
        ({ a with ch := ⟨a.ch.queue, a.ch.cursor, rest⟩, yrecv := true,
                  lvR := a.lvR.or (some (vR x r)) }, .inl (.inr (some (otChoose x r))))
      | none => ({ a with ch := ⟨a.ch.queue, a.ch.cursor, rest⟩, yrecv := true }, .inl (.inr none))

/-- The abstract step on an adversary event of the base OT `i`. -/
def aSched (a : ASt κ m M LS LR) (i : Fin κ) {L : Type} :
    SchedEv → ASt κ m M LS LR × (InOut m M ⊕ (AOut m M ⊕ L))
  | .idle => (a, outA .ack)
  | .poll => (a, outA (.status a.ro.isSome a.xo.isSome))
  | .deliverRecv =>
    if a.ro.isSome && a.xo.isSome && !a.dR i then
      ({ a with dR := Function.update a.dR i true }, outA .ack)
    else (a, outA .ack)
  | .deliverSend => (a, outA .ack)

/-- **The abstract step** with the leaks `vS` and `vR` of the completed views. -/
def aStep (vS : (Fin m → M × M) → (Fin m → Bool) → LS)
    (vR : (Fin m → M × M) → (Fin m → Bool) → LR) (a : ASt κ m M LS LR) :
    (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P) → ASt κ m M LS LR × (InOut m M ⊕ (AOut m M ⊕ L))
  | .inl (.inl (.inl x)) => ({ a with xo := a.xo.or (some x) }, outS)
  | .inl (.inl (.inr r)) => ({ a with ro := a.ro.or (some r) }, .inl (.inr none))
  | .inl (.inr (.wakeS i)) => (aWakeS vS a i, outS)
  | .inl (.inr .wakeR) => aWakeR vR a
  | .inr (.inl (.inl (i, ev))) => aSched a i ev
  | .inr (.inl (.inr d)) =>
    ({ a with ch := (FChan.advStep ChannelCap.secure msgLeak a.ch d).1 },
      .inr (.inl (.inr (FChan.advStep ChannelCap.secure msgLeak a.ch d).2)))
  | .inr (.inr p) => (a, .inr (.inr (ans a.lvS a.lvR p)))

/-- **The abstract system** with the key `k ← K`, read through `lS` at the wake that completes
the sender's columns when `uS`, and through `lR` at the wake that gives the receiver its message
when `uR`. -/
noncomputable def aKeyed {K : Type} [Inhabited K]
    (lS : K → (Fin m → M × M) → (Fin m → Bool) → LS)
    (lR : K → (Fin m → M × M) → (Fin m → Bool) → LR) (uS uR : Bool) :
    KeyedSys K (ASt κ m M LS LR) ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
      (InOut m M ⊕ (AOut m M ⊕ L)) where
  init := ASt.init
  step k a e := SPComp.pure (aStep ans (lS k) (lR k) a e)
  step₀ a e := SPComp.pure (aStep ans (lS default) (lR default) a e)
  uses a e := match e with
    | .inl (.inr (.wakeS i)) => uS && revealS a i
    | .inl (.inr .wakeR) => uR && revealR a
    | _ => false

/-- The sender's wake reads the leak only when it completes the sender's columns. -/
theorem aWakeS_congr {vS vS' : (Fin m → M × M) → (Fin m → Bool) → LS} {a : ASt κ m M LS LR}
    {i : Fin κ} (h : revealS a i = false) : aWakeS vS a i = aWakeS vS' a i := by
  unfold aWakeS
  rcases hx : a.xo with _ | x <;> rcases hr : a.ro with _ | r
  · rfl
  · rfl
  · rfl
  · simp only [revealS, hx, hr, Option.isSome_some, Bool.true_and] at h
    split_ifs with h1 h2
    · simp only [Bool.and_eq_true] at h1 h2
      simp [h1, h2] at h
    · rfl
    · rfl

omit [Zero M] in
/-- The receiver's wake reads the leak only when it gives the receiver its message for the first
time. -/
theorem aWakeR_congr {vR vR' : (Fin m → M × M) → (Fin m → Bool) → LR} {a : ASt κ m M LS LR}
    (h : revealR a = false) {L : Type} :
    aWakeR vR a (L := L) = aWakeR vR' a (L := L) := by
  unfold aWakeR
  rcases hr : a.ro with _ | r
  · rfl
  · rcases hi : a.ch.inbox with _ | ⟨y, rest⟩
    · rfl
    · rcases hx : a.xo with _ | x
      · rfl
      · rcases hl : a.lvR with _ | l
        · simp [revealR, hr, hx, hi, hl] at h
        · rfl

/-- An activation of the abstract system that does not read the key steps as `step₀`. -/
theorem aKeyed_hind {K : Type} [Inhabited K] (lS : K → (Fin m → M × M) → (Fin m → Bool) → LS)
    (lR : K → (Fin m → M × M) → (Fin m → Bool) → LR) (uS uR : Bool)
    (hS : uS = false → ∀ k, lS k = lS default) (hR : uR = false → ∀ k, lR k = lR default)
    (k : K) (a : ASt κ m M LS LR) (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
    (hu : (aKeyed (L := L) ans lS lR uS uR).uses a e = false) :
    (aKeyed ans lS lR uS uR).step k a e = (aKeyed ans lS lR uS uR).step₀ a e := by
  simp only [aKeyed]
  congr 1
  rcases e with ((x | r) | (i | _)) | (⟨i, ev⟩ | d) | p
  · rfl
  · rfl
  · simp only [aStep]
    cases huS : uS
    · rw [hS huS k]
    · simp only [aKeyed, huS, Bool.true_and] at hu
      rw [aWakeS_congr hu]
  · simp only [aStep]
    cases huR : uR
    · rw [hR huR k]
    · simp only [aKeyed, huR, Bool.true_and] at hu
      exact aWakeR_congr hu
  · rfl
  · rfl
  · rfl

end Abstract

/-! ## The parties refine the abstract system -/

section Bridge

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L) [NeZero κ] (k : IKNPKey κ m)

/-- The column the sender obtains from the base OT `i`: the column of `T` or of `T + r`
selected by the bit `s i`. -/
def qcol (r : Fin m → Bool) (i : Fin κ) : Fin m → Bool := baseOut (iknpBaseIn k.1 r i) (k.2 i)

/-- The message of the sender with the inputs `x`, `r` and the randomness `k`. -/
def yk (x : Fin m → M × M) (r : Fin m → Bool) : Msg m M :=
  iknpSenderMsg H x k.2 (otChoose (iknpBaseIn k.1 r) k.2)

/-- The abstraction of a state of the parties over the base OTs and the channel. -/
def absOf (t : (PSt κ m M × Unit) × SubSt κ m M) : ASt κ m M LS LR :=
  ⟨t.1.1.xo, t.1.1.ro, fun i => (t.2.1 i).dRecv, fun i => (t.1.1.cols i).isSome, t.1.1.ysent,
    mapC t.2.2, t.1.1.yrecv.isSome, (sviewOf k t.1.1).map φS, (rviewOf H k t.1.1).map φR⟩

/-- The invariant of the parties over the base OTs and the channel with randomness `k`: the
base OTs hold the inputs of `k`, a delivered column is in the inbox until it is fetched, the
sender has sent once it holds every column, and the channel carries at most the one message of
the sender. -/
structure InvS (st : PSt κ m M) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) : Prop where
  /-- No call is pending. -/
  ph : st.ph = .idle
  /-- The base OTs hold the receiver's column pairs. -/
  sent : ∀ i, (c i).sent = st.ro.map fun r => iknpBaseIn k.1 r i
  /-- The base OTs hold the sender's choice bits. -/
  chosen : ∀ i, (c i).chosen = st.xo.map fun _ => k.2 i
  /-- A base OT is delivered only with both inputs. -/
  dRecv : ∀ i, (c i).dRecv = true → st.xo.isSome ∧ st.ro.isSome
  /-- A delivered column is in the inbox until it is fetched. -/
  inbox : ∀ i, (c i).inbox =
    if (c i).dRecv && (st.cols i).isNone then st.ro.map (fun r => qcol k r i) else none
  /-- A fetched column is the delivered one. -/
  cols : ∀ i, (st.cols i).isSome → (c i).dRecv ∧ st.cols i = st.ro.map fun r => qcol k r i
  /-- The sender has sent once it holds every column. -/
  ysent : st.ysent = allCols st.cols
  /-- The channel carries the sender's message. -/
  msgs : ∀ v ∈ ch.queue ++ ch.inbox, ∃ x r, st.xo = some x ∧ st.ro = some r ∧ v = yk H k x r
  /-- The channel carries at most one message, and none before it is sent or after it is
  received. -/
  count : (ch.queue ++ ch.inbox).length ≤ (if st.ysent && st.yrecv.isNone then 1 else 0)
  /-- The receiver received the sender's message. -/
  yrecv : ∀ y, st.yrecv = some y → ∃ x r, st.xo = some x ∧ st.ro = some r ∧ y = yk H k x r
  /-- The receiver receives only a sent message. -/
  yrecvSent : st.yrecv.isSome → st.ysent

/-- The invariant on a state of the parties' system. -/
def Inv (t : (PSt κ m M × Unit) × SubSt κ m M) : Prop := InvS H k t.1.1 t.2.1 t.2.2

/-- A step of the parties' system on a party event is an activation of the parties against
`subL`. -/
theorem realW_step_inl (st : PSt κ m M) (s : SubSt κ m M) (e : InEv m M ⊕ WakeEv κ) :
    (realW H φS φR ans k).step ((st, ()), s) (.inl e) =
      SPComp.map (fun q => (((q.1.1, ()), q.1.2), peekOut (.inl q.2)))
        ((partyW H φS φR ans k).stepFuel (subL κ m M) (κ + 1) (st, s) (.inl e)) := by
  simp only [realW, Sys.mapPorts, Sys.relabel, peekEv]
  rw [MultiHybrid.tensor_withSub_step_inl _ _ _ (subL κ m M) sub_step_inl]
  simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, MultiHybrid.idSim_fuel]
  rfl

/-- A step of the parties' system on a corruption event is an activation of the parties
against `subL`. -/
theorem realW_step_peek (st : PSt κ m M) (s : SubSt κ m M) (p : P) :
    (realW H φS φR ans k).step ((st, ()), s) (.inr (.inr p)) =
      SPComp.map (fun q => (((q.1.1, ()), q.1.2), peekOut (.inl q.2)))
        ((partyW H φS φR ans k).stepFuel (subL κ m M) (κ + 1) (st, s) (.inr p)) := by
  simp only [realW, Sys.mapPorts, Sys.relabel, peekEv]
  rw [MultiHybrid.tensor_withSub_step_inl _ _ _ (subL κ m M) sub_step_inl]
  simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, MultiHybrid.idSim_fuel]
  rfl

/-- A step of the parties' system on an adversary event is a step of `subR`. -/
theorem realW_step_adv (st : PSt κ m M) (s : SubSt κ m M) (a : AEv κ m M) :
    (realW H φS φR ans k).step ((st, ()), s) (.inr (.inl a)) =
      SPComp.map (fun q => (((st, ()), q.1), .inr (.inl q.2))) ((subR κ m M).step s a) := by
  simp only [realW, Sys.mapPorts, Sys.relabel, peekEv]
  rw [MultiHybrid.tensor_withSub_step_inr _ _ _ (subR κ m M) sub_step_inr,
    MultiHybrid.idSim_stepFuel]
  simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, peekOut]

/-- The leak of the completed sender's view under `φS`. -/
def lSv (k : IKNPKey κ m) (_x : Fin m → M × M) (r : Fin m → Bool) : LS := φS (iknpSView k r)

/-- The leak of the completed receiver's view under `φR`. -/
def lRv (k : IKNPKey κ m) (x : Fin m → M × M) (r : Fin m → Bool) : LR := φR (iknpRView H k x r)

/-- The refinement claim at one event: the parties' step is a point mass whose state satisfies
the invariant and abstracts to the abstract step. -/
def Refines (t : (PSt κ m M × Unit) × SubSt κ m M)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) : Prop :=
  ∃ t', (realW H φS φR ans k).step t e =
      SPComp.pure (t', (aStep ans (lSv φS k) (lRv H φR k) (absOf H φS φR k t) e).2) ∧
    Inv H k t' ∧ absOf H φS φR k t' = (aStep ans (lSv φS k) (lRv H φR k) (absOf H φS φR k t) e).1

omit [AddCommGroup M] [NeZero κ] in
/-- With at least one base OT, the columns are not all present when none is. -/
theorem allCols_false_of_xo (st : PSt κ m M) [NeZero κ] (hc : ∀ i, (st.cols i).isSome = false) :
    allCols st.cols = false := by
  simp only [allCols, decide_eq_false_iff_not, not_forall]
  exact ⟨⟨0, NeZero.pos κ⟩, by simp [hc]⟩

/-- Refinement at the sender's input. -/
theorem refines_x (st : PSt κ m M) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (hI : InvS H k st c ch) (x : Fin m → M × M) :
    Refines H φS φR ans k ((st, ()), (c, ch)) (.inl (.inl (.inl x))) := by
  rcases hx : st.xo with _ | x₀
  · have hdR : ∀ i, (c i).dRecv = false := fun i => by
      cases h : (c i).dRecv
      · rfl
      · simpa [hx] using (hI.dRecv i h).1
    have hcol : ∀ i, (st.cols i).isSome = false := fun i => by
      cases h : (st.cols i).isSome
      · rfl
      · simpa [hdR i] using (hI.cols i h).1
    have hys : st.ysent = false := by rw [hI.ysent]; exact allCols_false_of_xo st hcol
    have hyr : st.yrecv = none := by
      cases h : st.yrecv with
      | none => rfl
      | some y => obtain ⟨_, _, h', _⟩ := hI.yrecv y h; simp [hx] at h'
    have hch : ch.queue ++ ch.inbox = [] := by
      have := hI.count
      simp only [hys, Bool.false_and, Bool.false_eq_true, ite_false, Nat.le_zero,
        List.length_eq_zero_iff] at this
      exact this
    refine ⟨(({ st with xo := some x, ph := .idle }, ()), (sUpd k 0 c, ch)), ?_, ?_, ?_⟩
    · rw [realW_step_inl]
      simp only [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart, hx]
      rw [drive_sIn H φS φR ans k (κ + 1) 0 (NeZero.pos κ) (by omega) _ rfl c ch]
      simp [SPComp.map, SPComp.pure_bind, aStep, peekOut]
    · exact {
        ph := rfl
        sent := fun i => by simp [sUpd, FOTSched.recvStep, hI.sent]
        chosen := fun i => by simp [sUpd, FOTSched.recvStep, hI.chosen, hx]
        dRecv := fun i => by simp [sUpd, FOTSched.recvStep, hdR]
        inbox := fun i => by simp [sUpd, FOTSched.recvStep, hdR]
        cols := fun i h => by simp [hcol i] at h
        ysent := hI.ysent
        msgs := by simp [hch]
        count := by simp [hch]
        yrecv := by simp [hyr]
        yrecvSent := by simp [hyr] }
    · simp [absOf, aStep, hx, sviewOf, hys, sUpd, FOTSched.recvStep, rviewOf, hyr]
  · refine ⟨((st, ()), (c, ch)), ?_, hI, ?_⟩
    · rw [realW_step_inl]
      simp [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart, hx, MultiHybrid.drive,
        SPComp.map, aStep, peekOut]
    · simp [absOf, aStep, hx]

/-- Refinement at the receiver's input. -/
theorem refines_r (st : PSt κ m M) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (hI : InvS H k st c ch) (r : Fin m → Bool) :
    Refines H φS φR ans k ((st, ()), (c, ch)) (.inl (.inl (.inr r))) := by
  rcases hr : st.ro with _ | r₀
  · have hdR : ∀ i, (c i).dRecv = false := fun i => by
      cases h : (c i).dRecv
      · rfl
      · simpa [hr] using (hI.dRecv i h).2
    have hcol : ∀ i, (st.cols i).isSome = false := fun i => by
      cases h : (st.cols i).isSome
      · rfl
      · simpa [hdR i] using (hI.cols i h).1
    have hys : st.ysent = false := by rw [hI.ysent]; exact allCols_false_of_xo st hcol
    have hyr : st.yrecv = none := by
      cases h : st.yrecv with
      | none => rfl
      | some y => obtain ⟨_, _, _, h', _⟩ := hI.yrecv y h; simp [hr] at h'
    have hch : ch.queue ++ ch.inbox = [] := by
      have := hI.count
      simp only [hys, Bool.false_and, Bool.false_eq_true, ite_false, Nat.le_zero,
        List.length_eq_zero_iff] at this
      exact this
    refine ⟨(({ st with ro := some r, ph := .idle }, ()), (rUpd k r 0 c, ch)), ?_, ?_, ?_⟩
    · rw [realW_step_inl]
      simp only [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart, hr]
      rw [drive_rIn H φS φR ans k r (κ + 1) 0 (NeZero.pos κ) (by omega) _ rfl rfl c ch]
      simp [SPComp.map, SPComp.pure_bind, aStep, peekOut]
    · exact {
        ph := rfl
        sent := fun i => by simp [rUpd, FOTSched.sendStep, hI.sent, hr]
        chosen := fun i => by simp [rUpd, FOTSched.sendStep, hI.chosen]
        dRecv := fun i => by simp [rUpd, FOTSched.sendStep, hdR]
        inbox := fun i => by simp [rUpd, FOTSched.sendStep, hdR, hI.inbox i]
        cols := fun i h => by simp [hcol i] at h
        ysent := hI.ysent
        msgs := by simp [hch]
        count := by simp [hch]
        yrecv := by simp [hyr]
        yrecvSent := by simp [hyr] }
    · simp [absOf, aStep, hr, sviewOf, hys, rUpd, FOTSched.sendStep, rviewOf, hyr]
  · refine ⟨((st, ()), (c, ch)), ?_, hI, ?_⟩
    · rw [realW_step_inl]
      simp [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart, hr, MultiHybrid.drive,
        SPComp.map, aStep, peekOut]
    · simp [absOf, aStep, hr]

omit [NeZero κ] in
/-- The invariant depends on the base OTs only through their inputs, delivery flags and
inboxes. -/
theorem InvS.congr_c {st : PSt κ m M} {c c' : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)}
    {ch : ChanSt (Msg m M)} (hI : InvS H k st c ch)
    (h : ∀ j, (c' j).sent = (c j).sent ∧ (c' j).chosen = (c j).chosen ∧
      (c' j).dRecv = (c j).dRecv ∧ (c' j).inbox = (c j).inbox) : InvS H k st c' ch where
  ph := hI.ph
  sent j := (h j).1.trans (hI.sent j)
  chosen j := (h j).2.1.trans (hI.chosen j)
  dRecv j hd := hI.dRecv j ((h j).2.2.1 ▸ hd)
  inbox j := by rw [(h j).2.2.2, (h j).2.2.1]; exact hI.inbox j
  cols j hc := by rw [(h j).2.2.1]; exact hI.cols j hc
  ysent := hI.ysent
  msgs := hI.msgs
  count := hI.count
  yrecv := hI.yrecv
  yrecvSent := hI.yrecvSent

omit [AddCommGroup M] [NeZero κ] in
/-- Unfolding lemma of `subR`: an adversary event of the base OT `i`. -/
theorem subR_step_sched (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (i : Fin κ) (ev : SchedEv) :
    (subR κ m M).step (c, ch) (.inl (i, ev)) =
      SPComp.pure ((Function.update c i (FOTSched.schedStep baseOut (c i) ev).1, ch),
        .inl (FOTSched.schedStep baseOut (c i) ev).2) := by
  simp [subR, Sys.chanPortR, FOTSched.schedSys, SPComp.map, SPComp.pure_bind]

omit [AddCommGroup M] [NeZero κ] in
/-- Unfolding lemma of `subR`: an adversary event of the channel. -/
theorem subR_step_chan (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (d : ChanAEv (Msg m M)) :
    (subR κ m M).step (c, ch) (.inr d) =
      SPComp.pure ((c, (FChan.advStep ChannelCap.secure msgLeak ch d).1),
        .inr (FChan.advStep ChannelCap.secure msgLeak ch d).2) := by
  simp [subR, Sys.chanPortR, FChan.advSys, SPComp.map, SPComp.pure_bind]

/-- Refinement at an adversary event of a base OT. -/
theorem refines_sched (st : PSt κ m M) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (hI : InvS H k st c ch) (i : Fin κ) (ev : SchedEv) :
    Refines H φS φR ans k ((st, ()), (c, ch)) (.inr (.inl (.inl (i, ev)))) := by
  cases ev with
  | idle =>
    refine ⟨((st, ()), (c, ch)), ?_, hI, ?_⟩
    · rw [realW_step_adv, subR_step_sched]
      simp [FOTSched.schedStep, SPComp.map, SPComp.pure_bind, aStep, aSched]
    · simp [aStep, aSched]
  | poll =>
    refine ⟨((st, ()), (c, ch)), ?_, hI, ?_⟩
    · rw [realW_step_adv, subR_step_sched]
      simp [FOTSched.schedStep, SPComp.map, SPComp.pure_bind, aStep, aSched, hI.sent, hI.chosen,
        absOf]
    · simp [aStep, aSched]
  | deliverSend =>
    refine ⟨((st, ()), (Function.update c i (FOTSched.schedStep baseOut (c i) .deliverSend).1,
      ch)), ?_, ?_, ?_⟩
    · rw [realW_step_adv, subR_step_sched]
      simp only [SPComp.map, SPComp.pure_bind, aStep, aSched]
      congr 2
      simp only [FOTSched.schedStep]
      split <;> rfl
    · refine hI.congr_c H k fun j => ?_
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, FOTSched.schedStep]
        split <;> simp
      · simp [Function.update_of_ne hj]
    · have hd : ∀ j, (Function.update c i (FOTSched.schedStep baseOut (c i) .deliverSend).1
          j).dRecv = (c j).dRecv := fun j => by
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self, FOTSched.schedStep]
          split <;> rfl
        · simp [Function.update_of_ne hj]
      simp [absOf, aStep, aSched, hd]
  | deliverRecv =>
    have hs := hI.sent i
    have hc := hI.chosen i
    rcases hro : st.ro with _ | r <;> rcases hxo : st.xo with _ | x <;> cases hd : (c i).dRecv
    case some.some.false =>
      have hci : st.cols i = none := by
        cases h : st.cols i with
        | none => rfl
        | some q => have := (hI.cols i (by simp [h])).1; simp [hd] at this
      refine ⟨((st, ()), (Function.update c i
        { c i with inbox := some (qcol k r i), dRecv := true }, ch)), ?_, ?_, ?_⟩
      · rw [realW_step_adv, subR_step_sched]
        simp [FOTSched.schedStep, hs, hc, hro, hxo, hd, SPComp.map, SPComp.pure_bind, aStep,
          aSched, absOf, qcol]
      · refine {
          ph := hI.ph
          sent := fun j => ?_
          chosen := fun j => ?_
          dRecv := fun j hj => ?_
          inbox := fun j => ?_
          cols := fun j hj => ?_
          ysent := hI.ysent
          msgs := hI.msgs
          count := hI.count
          yrecv := hI.yrecv
          yrecvSent := hI.yrecvSent } <;>
        · by_cases hji : j = i
          · subst hji
            simp_all
          · (try simp only [Function.update_of_ne hji] at hj)
            simp only [Function.update_of_ne hji]
            first
            | exact hI.sent j
            | exact hI.chosen j
            | exact hI.dRecv j hj
            | exact hI.inbox j
            | exact hI.cols j hj
      · simp only [absOf, aStep, aSched, hro, hxo, hd, Option.isSome_some, Bool.not_false,
          Bool.and_self, ite_true]
        congr 1
        funext j
        by_cases hji : j = i
        · subst hji; simp
        · simp [Function.update_of_ne hji]
    all_goals
      refine ⟨((st, ()), (c, ch)), ?_, hI, ?_⟩
      · rw [realW_step_adv, subR_step_sched]
        simp [FOTSched.schedStep, hs, hc, hro, hxo, hd, SPComp.map, SPComp.pure_bind, aStep,
          aSched, absOf]
      · simp [aStep, aSched, absOf, hro, hxo, hd]

omit [AddCommGroup M] [NeZero κ] in
/-- The adversary port of the secure channel commutes with replacing every message by `y0`. -/
theorem advStep_mapC [Zero M] (ch : ChanSt (Msg m M)) (d : ChanAEv (Msg m M)) :
    FChan.advStep ChannelCap.secure msgLeak (mapC ch) d =
      (mapC (FChan.advStep ChannelCap.secure msgLeak ch d).1,
        (FChan.advStep ChannelCap.secure msgLeak ch d).2) := by
  cases d with
  | idle => rfl
  | poll =>
    have hw : (ChannelCap.secure.wireLeak msgLeak ∘ fun _ : Msg m M => (y0 : Msg m M)) =
        ChannelCap.secure.wireLeak msgLeak := funext fun _ => rfl
    simp only [FChan.advStep, FChan.pollLeak, mapC, List.map_map, hw, List.length_map]
  | deliver =>
    obtain ⟨q, cur, ib⟩ := ch
    cases q <;> simp only [FChan.advStep, FChan.popTo, mapC, List.map, List.head?, List.tail,
      Option.toList, List.map_append]
  | drop => simp [FChan.advStep, FChan.popTo, mapC, ChannelCap.secure, List.map_tail]
  | tamper v => simp [FChan.advStep, ChannelCap.secure]

omit [AddCommGroup M] [NeZero κ] in
/-- The adversary port of the secure channel keeps or removes messages. -/
theorem advStep_msgs (ch : ChanSt (Msg m M)) (d : ChanAEv (Msg m M)) :
    (∀ v ∈ (FChan.advStep ChannelCap.secure msgLeak ch d).1.queue ++
        (FChan.advStep ChannelCap.secure msgLeak ch d).1.inbox, v ∈ ch.queue ++ ch.inbox) ∧
      ((FChan.advStep ChannelCap.secure msgLeak ch d).1.queue ++
        (FChan.advStep ChannelCap.secure msgLeak ch d).1.inbox).length ≤
        (ch.queue ++ ch.inbox).length := by
  obtain ⟨q, cur, ib⟩ := ch
  cases d with
  | idle => simp [FChan.advStep]
  | poll => simp [FChan.advStep]
  | deliver =>
    cases q with
    | nil => simp [FChan.advStep, FChan.popTo]
    | cons a q => simp [FChan.advStep, FChan.popTo]; grind
  | drop =>
    cases q with
    | nil => simp [FChan.advStep, FChan.popTo, ChannelCap.secure]
    | cons a q => simp [FChan.advStep, FChan.popTo, ChannelCap.secure]; grind
  | tamper v => simp [FChan.advStep, ChannelCap.secure]

/-- Refinement at an adversary event of the channel. -/
theorem refines_chan (st : PSt κ m M) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (hI : InvS H k st c ch) (d : ChanAEv (Msg m M)) :
    Refines H φS φR ans k ((st, ()), (c, ch)) (.inr (.inl (.inr d))) := by
  refine ⟨((st, ()), (c, (FChan.advStep ChannelCap.secure msgLeak ch d).1)), ?_, ?_, ?_⟩
  · rw [realW_step_adv, subR_step_chan]
    simp [SPComp.map, SPComp.pure_bind, aStep, absOf, advStep_mapC]
  · obtain ⟨hm, hl⟩ := advStep_msgs ch d
    exact { hI with
      msgs := fun v hv => hI.msgs v (hm v hv)
      count := hl.trans hI.count }
  · simp [absOf, aStep, advStep_mapC]

/-- Refinement at a corruption event. -/
theorem refines_peek (st : PSt κ m M) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (hI : InvS H k st c ch) (p : P) :
    Refines H φS φR ans k ((st, ()), (c, ch)) (.inr (.inr p)) := by
  refine ⟨((st, ()), (c, ch)), ?_, hI, ?_⟩
  · rw [realW_step_peek]
    simp [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart, MultiHybrid.drive,
      SPComp.map, aStep, peekOut, peekAns, absOf]
  · simp [aStep]


/-- Refinement at the wake of the receiver. -/
theorem refines_wakeR (st : PSt κ m M) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (hI : InvS H k st c ch) :
    Refines H φS φR ans k ((st, ()), (c, ch)) (.inl (.inr .wakeR)) := by
  obtain ⟨xo, ro, cols, ysent, yrecv, ph⟩ := st
  obtain rfl : ph = .idle := hI.ph
  rcases hr : ro with _ | r
  · subst hr
    refine ⟨((_, ()), (c, ch)), ?_, hI, ?_⟩
    · rw [realW_step_inl]
      simp [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart, MultiHybrid.drive,
        SPComp.map, aStep, aWakeR, peekOut, absOf]
    · simp [aStep, aWakeR, absOf]
  · subst hr
    obtain ⟨q, cur, ib⟩ := ch
    cases ib with
    | nil =>
      refine ⟨((_, ()), (c, ⟨q, cur, []⟩)), ?_, hI, ?_⟩
      · rw [realW_step_inl]
        simp [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart,
          MultiHybrid.drive, subL_step_chan, FChan.honStep, pResume, SPComp.map, aStep, aWakeR,
          peekOut, absOf, mapC]
      · simp [aStep, aWakeR, absOf, mapC]
    | cons y rest =>
      obtain ⟨x, r', hx, hr', hy⟩ := hI.msgs y (by simp)
      cases hr'
      simp only at hx
      subst hx
      have hc := hI.count
      simp only [List.length_append, List.length_cons] at hc
      have hys : ysent = true := by
        cases h : ysent <;> simp_all
      have hyr : yrecv = none := by
        cases h : yrecv <;> simp_all
      subst hys hyr hy
      refine ⟨((⟨some x, some r, cols, true, some (yk H k x r), .idle⟩, ()),
        (c, ⟨q, cur, rest⟩)), ?_, ?_, ?_⟩
      · rw [realW_step_inl]
        simp [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart,
          MultiHybrid.drive, subL_step_chan, FChan.honStep, pResume, SPComp.map, aStep, aWakeR,
          peekOut, absOf, mapC, yk, iknpRecvOut_otChoose]
      · exact {
          ph := rfl
          sent := hI.sent
          chosen := hI.chosen
          dRecv := hI.dRecv
          inbox := hI.inbox
          cols := hI.cols
          ysent := hI.ysent
          msgs := fun v hv => hI.msgs v (by simp at hv ⊢; tauto)
          count := by
            simp only [List.length_append, Option.isNone_some, Bool.and_false,
              Bool.false_eq_true, ite_false]
            simp at hc
            omega
          yrecv := fun y' h => ⟨x, r, rfl, rfl, (Option.some.inj h).symm⟩
          yrecvSent := fun _ => rfl }
      · simp [absOf, aStep, aWakeR, mapC, rviewOf, sviewOf, lRv, iknpRView, yk]

omit [AddCommGroup M] [NeZero κ] in
/-- The flags of the columns after a fetch. -/
theorem allB_update (cols : Fin κ → Option (Fin m → Bool)) (i : Fin κ) (q : Fin m → Bool) :
    allB (Function.update (fun j => (cols j).isSome) i true) =
      allCols (Function.update cols i (some q)) := by
  simp only [allB, allCols]
  congr 1
  apply propext
  refine forall_congr' fun j => ?_
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

omit [AddCommGroup M] [NeZero κ] in
/-- The flags of the columns after a fetch, pointwise. -/
theorem isSome_update (cols : Fin κ → Option (Fin m → Bool)) (i : Fin κ) (q : Fin m → Bool) :
    (fun j => (Function.update cols i (some q) j).isSome) =
      Function.update (fun j => (cols j).isSome) i true := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

omit [AddCommGroup M] [NeZero κ] in
/-- The delivery flags after replacing the base OT `i` by a state with the same flag. -/
theorem dRecv_update (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool)) (i : Fin κ)
    (s : SchedSt (BPair m) Bool (Fin m → Bool)) (h : s.dRecv = (c i).dRecv) :
    (fun j => (Function.update c i s j).dRecv) = fun j => (c j).dRecv := by
  funext j
  by_cases hji : j = i
  · subst hji; simpa using h
  · simp [Function.update_of_ne hji]

/-- A later call of an activation with calls left. -/
theorem drive_pos {σ τ E O EG OG : Type} (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    {n : ℕ} (hn : 0 < n) (s : σ) (g : EG) (t : τ) :
    π.drive X n s (.inl g) t = SPComp.bind (X.step t g) fun q =>
      SPComp.bind (π.resume s q.2) fun r => π.drive X (n - 1) r.1 r.2 q.1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rfl

omit [NeZero κ] in
/-- The fetched columns, once all present, are the columns selected by `s`. -/
theorem colsVal_eq {cols : Fin κ → Option (Fin m → Bool)} {r : Fin m → Bool}
    (hc : ∀ j, (cols j).isSome → cols j = some (qcol k r j)) (hall : allCols cols = true) :
    colsVal cols = otChoose (iknpBaseIn k.1 r) k.2 := by
  funext j
  have hj : (cols j).isSome = true := by grind [allCols]
  simp only [colsVal, hc j hj, Option.getD_some]
  rfl

/-- Refinement at the wake of the sender for the base OT `i`. -/
theorem refines_wakeS (st : PSt κ m M) (c : Fin κ → SchedSt (BPair m) Bool (Fin m → Bool))
    (ch : ChanSt (Msg m M)) (hI : InvS H k st c ch) (i : Fin κ) :
    Refines H φS φR ans k ((st, ()), (c, ch)) (.inl (.inr (.wakeS i))) := by
  obtain ⟨xo, ro, cols, ysent, yrecv, ph⟩ := st
  obtain rfl : ph = .idle := hI.ph
  have hκ : 0 < κ := NeZero.pos κ
  rcases xo with _ | x
  · refine ⟨((_, ()), (c, ch)), ?_, hI, ?_⟩
    · rw [realW_step_inl]
      simp [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart, MultiHybrid.drive,
        SPComp.map, aStep, aWakeS, peekOut]
    · simp [aStep, aWakeS, absOf]
  have hch : (c i).chosen = some (k.2 i) := by simpa using hI.chosen i
  have hc1 : (FOTSched.recvStep (c i) (k.2 i)).1 = { c i with inbox := none } := by
    simp [FOTSched.recvStep, hch]
  have hc2 : (FOTSched.recvStep (c i) (k.2 i)).2 = (c i).inbox := rfl
  have hinb := hI.inbox i
  by_cases hf : (c i).dRecv = true ∧ cols i = none ∧ ro.isSome = true
  · obtain ⟨hd, hci, hro⟩ := hf
    obtain ⟨r, rfl⟩ := Option.isSome_iff_exists.mp hro
    have hq : (c i).inbox = some (qcol k r i) := by simp [hinb, hd, hci]
    have hys : ysent = false := by
      have h := hI.ysent
      simp only at h
      rw [h]
      simp only [allCols, decide_eq_false_iff_not, not_forall]
      exact ⟨i, by simp [hci]⟩
    subst hys
    have hyr : yrecv = none := by
      cases h : yrecv with
      | none => rfl
      | some y => simpa [h] using hI.yrecvSent
    subst hyr
    have hch0 : ch.queue ++ ch.inbox = [] := by
      simpa using hI.count
    have hcolj : ∀ j, j ≠ i → (cols j).isSome → cols j = some (qcol k r j) := fun j _ hj => by
      simpa using (hI.cols j hj).2
    have hdR' : (fun j => (Function.update c i { c i with inbox := none } j).dRecv) =
        fun j => (c j).dRecv := by
      funext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [Function.update_of_ne hji]
    have hInv : ∀ ys, ys = allCols (Function.update cols i (some (qcol k r i))) →
        ∀ ch' : ChanSt (Msg m M),
        (∀ v ∈ ch'.queue ++ ch'.inbox, ∃ x' r', some x = some x' ∧ some r = some r' ∧
          v = yk H k x' r') →
        (ch'.queue ++ ch'.inbox).length ≤ (if ys then 1 else 0) →
        InvS H k ⟨some x, some r, Function.update cols i (some (qcol k r i)), ys, none, .idle⟩
          (Function.update c i { c i with inbox := none }) ch' := by
      intro ys hys ch' hm hcnt
      refine {
        ph := rfl
        sent := fun j => ?_
        chosen := fun j => ?_
        dRecv := fun j hj => ?_
        inbox := fun j => ?_
        cols := fun j hj => ?_
        ysent := hys
        msgs := hm
        count := by simpa using hcnt
        yrecv := by simp
        yrecvSent := by simp } <;>
      · by_cases hji : j = i
        · subst hji
          have h₁ := hI.sent j
          have h₂ := hI.chosen j
          simp_all
        · (try simp only [Function.update_of_ne hji] at hj)
          simp only [Function.update_of_ne hji]
          first
          | exact hI.sent j
          | exact hI.chosen j
          | exact hI.dRecv j hj
          | exact hI.inbox j
          | exact hI.cols j hj
    have hab := allB_update cols i (qcol k r i)
    by_cases hall : allCols (Function.update cols i (some (qcol k r i))) = true
    · have hcv : colsVal (Function.update cols i (some (qcol k r i))) =
          otChoose (iknpBaseIn k.1 r) k.2 := by
        refine colsVal_eq k (fun j hj => ?_) hall
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji] at hj ⊢
          exact hcolj j hji hj
      refine ⟨((⟨some x, some r, Function.update cols i (some (qcol k r i)), true, none, .idle⟩,
        ()), (Function.update c i { c i with inbox := none },
          ⟨ch.queue ++ [yk H k x r], ch.cursor, ch.inbox⟩)), ?_, ?_, ?_⟩
      · rw [realW_step_inl]
        simp only [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart,
          MultiHybrid.drive, subL_step_recv, partyW_resume, hc1, hc2, hq, pResume, pFetch, hall,
          Bool.not_false, Bool.and_self, ite_true]
        rw [drive_pos _ _ hκ]
        simp [subL_step_chan, FChan.honStep, pResume, MultiHybrid.drive, SPComp.map, peekOut,
          aStep, aWakeS, absOf, hd, hci, hcv, yk, outS]
      · refine hInv true hall.symm _ (fun v hv => ⟨x, r, rfl, rfl, ?_⟩) ?_
        · simp only [List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hv
          have hq0 : ch.queue = [] := (List.append_eq_nil_iff.mp hch0).1
          have hi0 : ch.inbox = [] := (List.append_eq_nil_iff.mp hch0).2
          simp_all
        · have := congrArg List.length hch0
          simp only [List.length_append, List.length_nil] at this
          simp; omega
      · simp [absOf, aStep, aWakeS, hd, hci, hab, hall, isSome_update, mapC,
          FChan.honStep, sviewOf, hcv, lSv, iknpSView, rviewOf, dRecv_update]
    · have hall' : allCols (Function.update cols i (some (qcol k r i))) = false := by
        simpa using hall
      refine ⟨((⟨some x, some r, Function.update cols i (some (qcol k r i)), false, none,
        .idle⟩, ()), (Function.update c i { c i with inbox := none }, ch)), ?_, ?_, ?_⟩
      · rw [realW_step_inl]
        simp only [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart,
          MultiHybrid.drive, subL_step_recv, partyW_resume, hc1, hc2, hq, pResume, pFetch, hall',
          Bool.not_false]
        simp [MultiHybrid.drive, SPComp.map, peekOut, aStep, aWakeS, absOf, hd, hci, outS]
      · refine hInv false hall'.symm ch (fun v hv => ?_) ?_
        · simp [hch0] at hv
        · simp [hch0]
      · simp [absOf, aStep, aWakeS, hd, hci, hab, hall', isSome_update, sviewOf,
          rviewOf, dRecv_update]
  · have hq0 : (c i).inbox = none := by
      rw [hinb]
      rcases ro with _ | r <;> cases hd : (c i).dRecv <;> cases hcl : cols i <;> simp_all
    have hdR' : (fun j => (Function.update c i { c i with inbox := none } j).dRecv) =
        fun j => (c j).dRecv := by
      funext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [Function.update_of_ne hji]
    refine ⟨((⟨some x, ro, cols, ysent, yrecv, .idle⟩, ()),
      (Function.update c i { c i with inbox := none }, ch)), ?_, ?_, ?_⟩
    · rw [realW_step_inl]
      simp only [MultiHybrid.stepFuel, partyW_start, SPComp.pure_bind, pStart,
        MultiHybrid.drive, subL_step_recv, partyW_resume, hc1, hc2, hq0, pResume]
      rcases ro with _ | r
      · simp [SPComp.map, peekOut, aStep, aWakeS, outS]
      · have hnf : ((c i).dRecv && !(cols i).isSome) = false := by
          cases hd : (c i).dRecv <;> cases hcl : cols i <;> simp_all
        simp [SPComp.map, peekOut, aStep, aWakeS, absOf, outS]
    · refine hI.congr_c H k fun j => ?_
      by_cases hji : j = i
      · subst hji; simp [hq0]
      · simp [Function.update_of_ne hji]
    · rcases ro with _ | r
      · simp [absOf, aStep, aWakeS, hdR']
      · have hfalse : ((c i).dRecv && !(cols i).isSome) = false := by
          cases hd : (c i).dRecv <;> cases hcl : cols i <;> simp_all
        simp only [absOf, aStep, aWakeS, hdR', hfalse, Bool.false_eq_true, ite_false]

/-- Refinement at every event. -/
theorem refines (t : (PSt κ m M × Unit) × SubSt κ m M) (hI : Inv H k t)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) : Refines H φS φR ans k t e := by
  obtain ⟨⟨st, ⟨⟩⟩, c, ch⟩ := t
  rcases e with ((x | r) | (i | _)) | (⟨i, ev⟩ | d) | p
  · exact refines_x H φS φR ans k st c ch hI x
  · exact refines_r H φS φR ans k st c ch hI r
  · exact refines_wakeS H φS φR ans k st c ch hI i
  · exact refines_wakeR H φS φR ans k st c ch hI
  · exact refines_sched H φS φR ans k st c ch hI i ev
  · exact refines_chan H φS φR ans k st c ch hI d
  · exact refines_peek H φS φR ans k st c ch hI p

/-- Unfolding lemma of `realW`: the initial state. -/
theorem realW_init : (realW H φS φR ans k).init =
    ((PSt.init, ()), (fun _ => FOTSched.initSt, FChan.initSt)) := rfl

/-- The invariant holds initially. -/
theorem inv_init : Inv H k (realW H φS φR ans k).init := by
  rw [realW_init]
  exact {
    ph := rfl
    sent := fun _ => rfl
    chosen := fun _ => rfl
    dRecv := fun _ h => by simp [FOTSched.initSt] at h
    inbox := fun _ => by simp [FOTSched.initSt]
    cols := fun _ h => by simp [PSt.init] at h
    ysent := (allCols_false_of_xo PSt.init fun _ => rfl).symm
    msgs := by simp [FChan.initSt]
    count := by simp [FChan.initSt]
    yrecv := fun _ h => by simp [PSt.init] at h
    yrecvSent := fun h => by simp [PSt.init] at h }

/-- **The parties refine the abstract system**: with randomness `k`, the parties over the base
OTs beside the channel and the abstract system with the key `k` have equal views. -/
theorem view_realW_eq {ζ : Type} (uS uR : Bool) (Z : Strat ζ _ _) :
    view (realW H φS φR ans k) Z =
      view ((aKeyed ans (lSv φS) (lRv H φR) uS uR).withKey k) Z := by
  refine view_eq_of_stepMap_on _ _ (Inv H k) (absOf H φS φR k) (inv_init H φS φR ans k) ?_
    (fun t e hI => ?_) (fun t e hI => ?_) Z
  · rw [realW_init]
    simp [aKeyed, KeyedSys.withKey, absOf, PSt.init, ASt.init, FOTSched.initSt, FChan.initSt,
      mapC, sviewOf, rviewOf]
  · obtain ⟨t', h, ht', -⟩ := refines H φS φR ans k t hI e
    exact ⟨Unit, SPComp.pure (), fun _ => (t', _), by rw [h, SPComp.pure_bind], fun _ => ht'⟩
  · obtain ⟨t', h, -, ha⟩ := refines H φS φR ans k t hI e
    rw [h]
    simp [SPComp.map, SPComp.pure_bind, aKeyed, KeyedSys.withKey, ha]

/-- Whether an event is an input of a party. -/
def isInput : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P) → Bool
  | .inl (.inl _) => true
  | _ => false

/-- Whether an event is an adversary event of the base OTs or of the channel. -/
def isAdv : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- The parties with their randomness `k = (T, s)` as a key: the key is read once a party has its
input, and never by an adversary event of the base OTs or of the channel. -/
noncomputable def realKeyed : KeyedSys (IKNPKey κ m) ((PSt κ m M × Unit) × SubSt κ m M)
    ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) (InOut m M ⊕ (AOut m M ⊕ L)) where
  init := ((PSt.init, ()), (fun _ => FOTSched.initSt, FChan.initSt))
  step k := (realW H φS φR ans k).step
  step₀ := (realW H φS φR ans default).step
  uses t e := !isAdv e && (t.1.1.xo.isSome || t.1.1.ro.isSome || isInput e)

/-- **The IKNP protocol over the base OTs beside the channel**: the parties with their
randomness `(T, s)` drawn uniformly at the first input of a party. -/
noncomputable def iknpW : Sys (Option (IKNPKey κ m) × ((PSt κ m M × Unit) × SubSt κ m M))
    ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) (InOut m M ⊕ (AOut m M ⊕ L)) :=
  (realKeyed H φS φR ans).lazy (PMF.uniformFintype _)

/-- An activation before any input does not read the randomness. -/
theorem realKeyed_hind (k : IKNPKey κ m) (t : (PSt κ m M × Unit) × SubSt κ m M)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
    (hu : (realKeyed H φS φR ans).uses t e = false) :
    (realKeyed H φS φR ans).step k t e = (realKeyed H φS φR ans).step₀ t e := by
  obtain ⟨⟨st, ⟨⟩⟩, s⟩ := t
  simp only [realKeyed] at hu ⊢
  rcases e with ((x | r) | (i | _)) | (a | p)
  · simp [isInput, isAdv] at hu
  · simp [isInput, isAdv] at hu
  · simp only [isAdv, isInput, Bool.not_false, Bool.true_and, Bool.or_false,
      Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hu
    rw [realW_step_inl, realW_step_inl]
    simp [MultiHybrid.stepFuel, pStart, hu.1, MultiHybrid.drive]
  · simp only [isAdv, isInput, Bool.not_false, Bool.true_and, Bool.or_false,
      Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hu
    rw [realW_step_inl, realW_step_inl]
    simp [MultiHybrid.stepFuel, pStart, hu.2, MultiHybrid.drive]
  · rw [realW_step_adv, realW_step_adv]
  · simp only [isAdv, isInput, Bool.not_false, Bool.true_and, Bool.or_false,
      Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hu
    rw [realW_step_peek, realW_step_peek]
    simp [MultiHybrid.stepFuel, pStart, MultiHybrid.drive, peekAns, sviewOf, rviewOf, hu.1,
      hu.2]

/-- **The protocol has the view of the abstract system**, whose key is drawn where `uS` and `uR`
say, when the leaks it does not draw the key for do not depend on it. -/
theorem view_iknpW_eq {ζ : Type} (uS uR : Bool)
    (hS : uS = false → ∀ k', lSv (M := M) φS k' = lSv φS (default : IKNPKey κ m))
    (hR : uR = false → ∀ k', lRv H φR k' = lRv H φR (default : IKNPKey κ m))
    (Z : Strat ζ ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) (InOut m M ⊕ (AOut m M ⊕ L))) :
    view (iknpW H φS φR ans) Z =
      view ((aKeyed ans (lSv φS) (lRv H φR) uS uR).lazy (PMF.uniformFintype _)) Z := by
  rw [iknpW, KeyedSys.view_lazy _ _ (realKeyed_hind H φS φR ans),
    KeyedSys.view_lazy _ _ (aKeyed_hind ans _ _ uS uR hS hR)]
  congr 1
  funext k
  exact view_realW_eq H φS φR ans k uS uR Z

end Bridge

/-! ## The simulator -/

/-- The phase of an activation of the simulator: which answer of the ideal functionality is
awaited. -/
inductive SPh (κ : ℕ) where
  /-- No call is pending. -/
  | idle
  /-- The answer to a forwarded input. -/
  | fwd
  /-- The input status, for a poll of the base OT `i`. -/
  | cpoll (i : Fin κ)
  /-- The input status, for a delivery of the base OT `i`. -/
  | cdel (i : Fin κ)
  /-- The corrupt party's view, at the sender's completing wake. -/
  | revS
  /-- The acknowledgement of the receiver's delivery. -/
  | wR1
  /-- The corrupt party's view, at the receiver's wake. -/
  | wR2
  /-- The receiver's output. -/
  | wR3

/-- Whether the phase awaits an answer on the honest port. -/
def SPh.isHon : SPh κ → Bool
  | .fwd => true
  | .wR3 => true
  | _ => false

/-- The state of the simulator: the delivery flags of the base OTs, the fetched columns, the
simulated channel, the simulated views and the phase. -/
structure SSt (κ m : ℕ) (M LS LR : Type) where
  /-- The base OTs whose output has been delivered. -/
  dR : Fin κ → Bool
  /-- The columns the sender has fetched. -/
  col : Fin κ → Bool
  /-- Whether the sender has sent its message. -/
  ysent : Bool
  /-- The simulated channel, each message replaced by `y0`. -/
  ch : ChanSt (Msg m M)
  /-- The simulated view of the sender. -/
  lvS : Option LS
  /-- The simulated view of the receiver. -/
  lvR : Option LR
  /-- The phase of the activation. -/
  ph : SPh κ

/-- The initial state of the simulator. -/
def SSt.init {LS LR : Type} : SSt κ m M LS LR :=
  ⟨fun _ => false, fun _ => false, false, FChan.initSt, none, none, .idle⟩

/-- The choice the simulator gives the ideal functionality for the receiver, which has already
chosen. -/
def dummyC : Fin m → Bool := fun _ => false

/-- The view of the interface of the protocol: inputs and outputs of the parties hidden, wakes
and adversary events and outputs public. -/
abbrev outerV (κ m : ℕ) (M P L : Type) :
    PubView ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) (InOut m M ⊕ (AOut m M ⊕ L)) :=
  ((hidView : PubView (InEv m M) (InOut m M)).wake (WakeEv κ)).sum PubView.eqView

/-- The view of the interface of the ideal functionality: honest values hidden, adversary
events and outputs public. -/
abbrev innerV (m : ℕ) (M EGA OGA : Type) : PubView (InEv m M ⊕ EGA) (InOut m M ⊕ OGA) :=
  (hidView : PubView (InEv m M) (InOut m M)).sum PubView.eqView

section Simulator

variable [Zero M] {LS LR P L EGA OGA : Type} (ans : Option LS → Option LR → P → L)
  (sch : SchedEv → EGA) (stat : OGA → Bool × Bool) (pkEv : EGA)
  (simS : OGA → SPComp LS) (simR : OGA → SPComp LR)

/-- The simulator's first step. -/
def simStart (s : SSt κ m M LS LR) :
    (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P) →
      SSt κ m M LS LR × ((InEv m M ⊕ EGA) ⊕ (InOut m M ⊕ (AOut m M ⊕ L)))
  | .inl (.inl e) => ({ s with ph := .fwd }, .inl (.inl e))
  | .inl (.inr (.wakeS i)) =>
    if s.dR i && !s.col i then
      if allB (Function.update s.col i true) && !s.ysent then
        ({ s with col := Function.update s.col i true, ysent := true,
                  ch := (FChan.honStep s.ch (.send y0)).1, ph := .revS }, .inl (.inr pkEv))
      else ({ s with col := Function.update s.col i true }, .inr outS)
    else (s, .inr outS)
  | .inl (.inr .wakeR) => match s.ch.inbox with
    | [] => (s, .inr (.inl (.inr none)))
    | _ :: rest => ({ s with ch := ⟨s.ch.queue, s.ch.cursor, rest⟩, ph := .wR1 },
        .inl (.inr (sch .deliverRecv)))
  | .inr (.inl (.inl (i, ev))) => match ev with
    | .idle => (s, .inr (outA .ack))
    | .poll => ({ s with ph := .cpoll i }, .inl (.inr (sch .poll)))
    | .deliverRecv => ({ s with ph := .cdel i }, .inl (.inr (sch .poll)))
    | .deliverSend => (s, .inr (outA .ack))
  | .inr (.inl (.inr d)) =>
    ({ s with ch := (FChan.advStep ChannelCap.secure msgLeak s.ch d).1 },
      .inr (.inr (.inl (.inr (FChan.advStep ChannelCap.secure msgLeak s.ch d).2))))
  | .inr (.inr p) => (s, .inr (.inr (.inr (ans s.lvS s.lvR p))))

/-- The simulator's step on an adversary answer `oa` of the ideal functionality (`none` for an
answer on the honest port where none is expected). -/
noncomputable def simResA (s : SSt κ m M LS LR) (oa : Option OGA) :
    SPComp (SSt κ m M LS LR × ((InEv m M ⊕ EGA) ⊕ (InOut m M ⊕ (AOut m M ⊕ L)))) :=
  match s.ph, oa with
  | .cpoll _, some a =>
    SPComp.pure ({ s with ph := .idle }, .inr (outA (.status (stat a).2 (stat a).1)))
  | .cdel i, some a =>
    if (stat a).1 && (stat a).2 && !s.dR i then
      SPComp.pure ({ s with dR := Function.update s.dR i true, ph := .idle }, .inr (outA .ack))
    else SPComp.pure ({ s with ph := .idle }, .inr (outA .ack))
  | .revS, some a =>
    SPComp.map (fun v => ({ s with lvS := some v, ph := .idle }, .inr outS)) (simS a)
  | .wR1, _ =>
    if s.lvR.isNone then SPComp.pure ({ s with ph := .wR2 }, .inl (.inr pkEv))
    else SPComp.pure ({ s with ph := .wR3 }, .inl (.inl (.inr dummyC)))
  | .wR2, some a =>
    SPComp.map (fun v => ({ s with lvR := some v, ph := .wR3 }, .inl (.inl (.inr dummyC))))
      (simR a)
  | .wR2, none => SPComp.pure ({ s with ph := .wR3 }, .inl (.inl (.inr dummyC)))
  | .cpoll _, none => SPComp.pure ({ s with ph := .idle }, .inr (outA .ack))
  | .cdel _, none => SPComp.pure ({ s with ph := .idle }, .inr (outA .ack))
  | _, _ => SPComp.pure ({ s with ph := .idle }, .inr outS)

/-- The simulator's step on an answer of the ideal functionality. -/
noncomputable def simResume (s : SSt κ m M LS LR) :
    InOut m M ⊕ OGA →
      SPComp (SSt κ m M LS LR × ((InEv m M ⊕ EGA) ⊕ (InOut m M ⊕ (AOut m M ⊕ L))))
  | .inl o =>
    if s.ph.isHon then SPComp.pure ({ s with ph := .idle }, .inr (.inl o))
    else simResA (L := L) stat pkEv simS simR s none
  | .inr a => simResA (L := L) stat pkEv simS simR s (some a)

/-- **The simulator** over an ideal functionality with the inputs of IKNP on its honest port
and the adversary port `EGA`: `sch` names the scheduler's events, `stat` reads an input status,
`pkEv` asks for the corrupt party's view, and `simS`, `simR` complete that view. It forwards the
inputs to the honest port. It simulates the base OTs from the input status of the ideal
functionality and the channel with every message replaced by `y0`; the wake of the sender that
completes its columns sends the simulated message and completes the sender's view by `simS`, and
the wake of the receiver that reads the message delivers the output, completes the receiver's
view by `simR` and passes the output on. -/
noncomputable def simW (hS : ∀ a, SPComp.NoFail (simS a)) (hR : ∀ a, SPComp.NoFail (simR a)) :
    MultiHybrid (SSt κ m M LS LR) ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
      (InOut m M ⊕ (AOut m M ⊕ L)) (InEv m M ⊕ EGA) (InOut m M ⊕ OGA) where
  init := SSt.init
  fuel := 3
  start s e := SPComp.pure (simStart ans sch pkEv s e)
  resume s o := simResume stat pkEv simS simR s o
  finish s _ := SPComp.pure ({ s with ph := .idle }, outS)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail s o := by
    have hA : ∀ oa, SPComp.NoFail (simResA (L := L) stat pkEv simS simR s oa) := by
      intro oa
      unfold simResA
      split <;> (try split) <;>
        first
        | exact SPComp.pure_noFail _
        | exact Assumptions.SPComp.bind_noFail (hS _) fun _ => SPComp.pure_noFail _
        | exact Assumptions.SPComp.bind_noFail (hR _) fun _ => SPComp.pure_noFail _
    rcases o with o | a
    · simp only [simResume]
      split
      · exact SPComp.pure_noFail _
      · exact hA _
    · exact hA _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- Unfolding lemma of `simW`: the step of the simulator over a subroutine. -/
theorem simW_withSub_step (hS : ∀ a, SPComp.NoFail (simS a)) (hR : ∀ a, SPComp.NoFail (simR a))
    {τ : Type} (X : Sys τ (InEv m M ⊕ EGA) (InOut m M ⊕ OGA)) (s : SSt κ m M LS LR) (u : τ)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) :
    ((simW ans sch stat pkEv simS simR hS hR).withSub X).step (s, u) e =
      SPComp.bind ((simW ans sch stat pkEv simS simR hS hR).drive X 3
          (simStart ans sch pkEv s e).1 (simStart ans sch pkEv s e).2 u)
        fun p => SPComp.pure ((p.1, p.2.1), p.2.2) := by
  simp [MultiHybrid.withSub, simW, SPComp.pure_bind]

/-- Unfolding lemma of `simW`: the step on an answer. -/
@[simp] theorem simW_resume (hS : ∀ a, SPComp.NoFail (simS a))
    (hR : ∀ a, SPComp.NoFail (simR a)) (s : SSt κ m M LS LR) (o : InOut m M ⊕ OGA) :
    (simW ans sch stat pkEv simS simR hS hR).resume s o = simResume stat pkEv simS simR s o :=
  rfl

/-- **Opacity of the simulator**: inputs related by `hidView`, wakes and adversary events public.
The simulator reads no input value: it forwards the inputs, and its other decisions depend on
the adversary port of the ideal functionality and on its own state only. -/
theorem simW_opaque (hS : ∀ a, SPComp.NoFail (simS a)) (hR : ∀ a, SPComp.NoFail (simR a)) :
    (simW ans sch stat pkEv simS simR hS hR (κ := κ) (m := m) (M := M)).Opaque
      (outerV κ m M P L) (innerV m M EGA OGA) := by
  have hrefl : ∀ d : (InEv m M ⊕ EGA) ⊕ (InOut m M ⊕ (AOut m M ⊕ L)),
      PubView.StepRel (outerV κ m M P L) (innerV m M EGA OGA) d d := by
    rintro ((g | g) | (o | o))
    · exact Sum.LiftRel.inl trivial
    · exact Sum.LiftRel.inr rfl
    · exact Sum.LiftRel.inl trivial
    · exact Sum.LiftRel.inr rfl
  have hc : ∀ c : SPComp (SSt κ m M LS LR × ((InEv m M ⊕ EGA) ⊕ (InOut m M ⊕ (AOut m M ⊕ L)))),
      rHoare eqPre c c (fun r h r' h' => h = h' ∧ r.1 = r'.1 ∧
        PubView.StepRel (outerV κ m M P L) (innerV m M EGA OGA) r.2 r'.2) := fun c =>
    rHoare_conseq (fun _ _ h => h) (fun _ _ _ _ hp => by
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨rfl, rfl, hrefl _⟩) (rHoare_refl c)
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    cases he with
    | inl h =>
      cases h with
      | inl _ =>
        exact rHoare_ret fun _ _ h => ⟨h, rfl, Sum.LiftRel.inl trivial⟩
      | inr h => subst h; exact hc _
    | inr h => subst h; exact hc _
  · rintro s _ o o' rfl ho
    cases ho with
    | inl _ =>
      simp only [simW, simResume]
      split
      · exact rHoare_ret fun _ _ h => ⟨h, rfl, Sum.LiftRel.inl trivial⟩
      · exact hc _
    | inr h => subst h; exact hc _
  · rintro s _ o o' rfl _
    exact rHoare_ret fun _ _ h => ⟨h, rfl, Sum.LiftRel.inl trivial⟩

end Simulator

/-! ## The abstract system realizes the simulated ideal functionality -/

/-- The state of the ideal functionality: scheduled oblivious transfer of `m` message pairs. -/
abbrev FSt (m : ℕ) (M : Type) := SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M)

/-- The ideal functionality with the inputs of IKNP on its honest port and the adversary port
`FA`. -/
noncomputable def idealF {EGA OGA : Type} (FA : Sys (FSt m M) EGA OGA) :
    Sys (FSt m M) (InEv m M ⊕ EGA) (InOut m M ⊕ OGA) :=
  Sys.ofPorts (Sys.ofPorts FOTSched.sendSys FOTSched.recvSys) FA

/-- The invariant of the abstract system on the flags and the channel. -/
structure InvA {LS LR : Type} (a : ASt κ m M LS LR) : Prop where
  /-- A base OT is delivered only with both inputs. -/
  dR : ∀ i, a.dR i = true → a.xo.isSome ∧ a.ro.isSome
  /-- A column is fetched only after delivery. -/
  col : ∀ i, a.col i = true → a.dR i = true
  /-- The sender has sent once it holds every column. -/
  ysent : a.ysent = allB a.col
  /-- The sender sends only with both inputs. -/
  sentIn : a.ysent = true → a.xo.isSome ∧ a.ro.isSome
  /-- The channel carries at most the one message. -/
  count : (a.ch.queue ++ a.ch.inbox).length ≤ if a.ysent && !a.yrecv then 1 else 0
  /-- The receiver receives only a sent message. -/
  yrecv : a.yrecv = true → a.ysent = true

section Ideal

variable [Zero M] {LS LR P L : Type} (ans : Option LS → Option LR → P → L)

/-- The abstract step preserves the invariant, whatever the leaks. -/
theorem InvA.step {a : ASt κ m M LS LR} (hI : InvA a)
    (vS : (Fin m → M × M) → (Fin m → Bool) → LS) (vR : (Fin m → M × M) → (Fin m → Bool) → LR)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) : InvA (aStep (L := L) ans vS vR a e).1 := by
  have hor : ∀ {α : Type} (o : Option α) (v : α), (o.or (some v)).isSome = true := by
    intro α o v; cases o <;> rfl
  rcases e with ((x | r) | (i | _)) | (⟨i, ev⟩ | d) | p
  · exact ⟨fun j h => ⟨hor _ _, (hI.dR j h).2⟩, hI.col, hI.ysent,
      fun h => ⟨hor _ _, (hI.sentIn h).2⟩, hI.count, hI.yrecv⟩
  · exact ⟨fun j h => ⟨(hI.dR j h).1, hor _ _⟩, hI.col, hI.ysent,
      fun h => ⟨(hI.sentIn h).1, hor _ _⟩, hI.count, hI.yrecv⟩
  · simp only [aStep, aWakeS]
    rcases hx : a.xo with _ | x <;> rcases hr : a.ro with _ | r
    · exact hI
    · exact hI
    · exact hI
    · simp only
      have hcolU : ∀ j, Function.update a.col i true j = true → a.dR j = true ∨ j = i := by
        intro j h
        by_cases hji : j = i
        · exact Or.inr hji
        · rw [Function.update_of_ne hji] at h; exact Or.inl (hI.col j h)
      split_ifs with h1 h2
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1 h2
        have hys : a.ysent = false := h2.2
        have hyr : a.yrecv = false := by
          cases h : a.yrecv
          · rfl
          · simpa [hys] using hI.yrecv h
        have hc := hI.count
        simp only [hys, hyr, Bool.false_and, Bool.false_eq_true, ite_false, Nat.le_zero,
          List.length_eq_zero_iff, List.append_eq_nil_iff] at hc
        refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun j h => ?_, h2.1.symm, fun _ => ⟨rfl, rfl⟩, ?_,
          fun _ => rfl⟩
        · rcases hcolU j h with h' | rfl
          · exact h'
          · exact h1.1
        · simp [FChan.honStep, hc.1, hc.2, hyr]
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
        refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun j h => ?_, ?_, fun _ => ⟨rfl, rfl⟩, hI.count,
          hI.yrecv⟩
        · rcases hcolU j h with h' | rfl
          · exact h'
          · exact h1.1
        · cases hys : a.ysent
          · simp only [hys, Bool.not_false, Bool.and_true, Bool.not_eq_true] at h2
            exact h2.symm
          · have hall := hI.ysent
            rw [hys] at hall
            have := of_decide_eq_true hall.symm i
            simp [h1.2] at this
      · exact hI
  · simp only [aStep, aWakeR]
    rcases hr : a.ro with _ | r
    · exact hI
    · simp only
      rcases hi : a.ch.inbox with _ | ⟨y, rest⟩
      · exact hI
      · have hc := hI.count
        rw [hi] at hc
        have hys : a.ysent = true := by
          cases h : a.ysent <;> simp_all
        have hyr : a.yrecv = false := by
          cases h : a.yrecv <;> simp_all
        simp only [hys, hyr, Bool.not_false, Bool.and_self, ite_true, List.length_append,
          List.length_cons] at hc
        have hq : a.ch.queue = [] := List.length_eq_zero_iff.mp (by omega)
        have hrest : rest = [] := List.length_eq_zero_iff.mp (by omega)
        rcases hx : a.xo with _ | x
        · dsimp only
          exact ⟨fun j h => by simpa [hx, hr] using hI.dR j h, hI.col, hI.ysent,
            fun h => by simpa [hx, hr] using hI.sentIn h, by simp [hq, hrest], fun _ => hys⟩
        · dsimp only
          exact ⟨fun _ _ => ⟨rfl, rfl⟩, hI.col, hI.ysent, fun _ => ⟨rfl, rfl⟩,
            by simp [hq, hrest], fun _ => hys⟩
  · cases ev with
    | idle => exact hI
    | poll => exact hI
    | deliverSend => exact hI
    | deliverRecv =>
      simp only [aStep, aSched]
      split_ifs with h1
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
        refine ⟨fun j h => ?_, fun j h => ?_, hI.ysent, hI.sentIn, hI.count, hI.yrecv⟩ <;>
          dsimp only at h ⊢
        · by_cases hji : j = i
          · exact ⟨h1.1.2, h1.1.1⟩
          · rw [Function.update_of_ne hji] at h; exact hI.dR j h
        · by_cases hji : j = i
          · subst hji; simp
          · rw [Function.update_of_ne hji]; exact hI.col j h
      · exact hI
  · exact ⟨hI.dR, hI.col, hI.ysent, hI.sentIn, (advStep_msgs a.ch d).2.trans hI.count,
      hI.yrecv⟩
  · exact hI

/-- The abstract step never unsets the sender's or the receiver's flag. -/
theorem aStep_mono (a : ASt κ m M LS LR)
    (vS : (Fin m → M × M) → (Fin m → Bool) → LS) (vR : (Fin m → M × M) → (Fin m → Bool) → LR)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) :
    (a.ysent = true → (aStep (L := L) ans vS vR a e).1.ysent = true) ∧
      (a.yrecv = true → (aStep (L := L) ans vS vR a e).1.yrecv = true) := by
  rcases e with ((x | r) | (i | _)) | (⟨i, ev⟩ | d) | p
  · exact ⟨id, id⟩
  · exact ⟨id, id⟩
  · simp only [aStep, aWakeS]
    split
    · split_ifs <;> simp
    · exact ⟨id, id⟩
  · simp only [aStep, aWakeR]
    split
    · exact ⟨id, id⟩
    · split
      · exact ⟨id, id⟩
      · split <;> simp
  · cases ev <;> simp only [aStep, aSched] <;> (try split_ifs) <;> exact ⟨id, id⟩
  · exact ⟨id, id⟩
  · exact ⟨id, id⟩

/-- The sender's completing wake sets its flag. -/
theorem aWakeS_reveal {a : ASt κ m M LS LR} {i : Fin κ} (h : revealS a i = true)
    (vS : (Fin m → M × M) → (Fin m → Bool) → LS) : (aWakeS vS a i).ysent = true := by
  simp only [revealS, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hx, hr⟩, hd⟩, hc⟩, hall⟩, hys⟩ := h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
  simp [aWakeS, hx, hr, hd, hc, hall, hys]

omit [Zero M] in
/-- The receiver's wake that reads the message sets its flag. -/
theorem aWakeR_reveal {a : ASt κ m M LS LR} (h : revealR a = true)
    (vR : (Fin m → M × M) → (Fin m → Bool) → LR) :
    (aWakeR vR a (L := L)).1.yrecv = true := by
  simp only [revealR, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hr, hx⟩, hi⟩, -⟩ := h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
  unfold aWakeR
  rcases hc : a.ch.inbox with _ | ⟨y, rest⟩
  · simp [hc] at hi
  · simp [hr, hx]

/-- The abstract state after the sender's completing wake for the base OT `i`, with the leak
`v`. -/
def revSt (a : ASt κ m M LS LR) (i : Fin κ) (v : LS) : ASt κ m M LS LR :=
  { a with col := Function.update a.col i true, ysent := true,
           ch := (FChan.honStep a.ch (.send y0)).1, lvS := some v }

/-- The abstract state after the receiver reads the message, leaving `rest` in the inbox, with
the stored view `lv`. -/
def rcvSt (a : ASt κ m M LS LR) (rest : List (Msg m M)) (lv : Option LR) : ASt κ m M LS LR :=
  { a with ch := ⟨a.ch.queue, a.ch.cursor, rest⟩, yrecv := true, lvR := lv }

/-- The state of the simulated ideal functionality that a state of the abstract system maps
to. -/
def projA {K : Type} (t : Option K × ASt κ m M LS LR) : SSt κ m M LS LR × FSt m M :=
  (⟨t.2.dR, t.2.col, t.2.ysent, t.2.ch, t.2.lvS, t.2.lvR, .idle⟩,
    ⟨t.2.xo, t.2.ro, none, t.2.yrecv, false⟩)

/-- An activation of the lazily keyed abstract system that does not depend on the key, up to
the key. -/
theorem lazy_map_det {K : Type} [Inhabited K] (μ : PMF K)
    (lS : K → (Fin m → M × M) → (Fin m → Bool) → LS)
    (lR : K → (Fin m → M × M) → (Fin m → Bool) → LR) (uS uR : Bool) (ko : Option K)
    (a : ASt κ m M LS LR) (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
    (h : ∀ k, aStep (L := L) ans (lS k) (lR k) a e = aStep ans (lS default) (lR default) a e) :
    SPComp.map (fun p => (projA p.1, p.2)) (((aKeyed ans lS lR uS uR).lazy μ).step (ko, a) e) =
      SPComp.pure (projA (ko, (aStep ans (lS default) (lR default) a e).1),
        (aStep ans (lS default) (lR default) a e).2) := by
  rcases ko with _ | k
  · by_cases hu : (aKeyed ans lS lR uS uR).uses a e = true
    · rw [KeyedSys.lazy_step_none_of_uses _ _ hu]
      simp only [aKeyed, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, h, projA]
      exact dead_sampleFrom (mass_ofPMF μ) _
    · rw [KeyedSys.lazy_step_none_of_not_uses _ _ (by simpa using hu)]
      simp [aKeyed, SPComp.map, SPComp.pure_bind, projA]
  · simp [KeyedSys.lazy, KeyedSys.lazyStep, aKeyed, SPComp.map, SPComp.pure_bind, h k, projA]

omit [Zero M] in
/-- Unfolding lemma of `idealF`: the sender's input. -/
theorem idealF_send {EGA OGA : Type} (FA : Sys (FSt m M) EGA OGA) (u : FSt m M)
    (x : Fin m → M × M) :
    (idealF FA).step u (.inl (.inl x)) =
      SPComp.pure ((FOTSched.sendStep u x).1, .inl (.inl (FOTSched.sendStep u x).2)) := by
  simp [idealF, FOTSched.sendSys, SPComp.map, SPComp.pure_bind]

omit [Zero M] in
/-- Unfolding lemma of `idealF`: the receiver's input. -/
theorem idealF_recv {EGA OGA : Type} (FA : Sys (FSt m M) EGA OGA) (u : FSt m M)
    (r : Fin m → Bool) :
    (idealF FA).step u (.inl (.inr r)) =
      SPComp.pure ((FOTSched.recvStep u r).1, .inl (.inr (FOTSched.recvStep u r).2)) := by
  simp [idealF, FOTSched.recvSys, SPComp.map, SPComp.pure_bind]

omit [Zero M] in
/-- Unfolding lemma of `idealF`: the adversary port. -/
theorem idealF_adv {EGA OGA : Type} (FA : Sys (FSt m M) EGA OGA) (u : FSt m M) (g : EGA) :
    (idealF FA).step u (.inr g) = SPComp.map (fun q => (q.1, .inr q.2)) (FA.step u g) := rfl

end Ideal

section Realize

variable [Zero M] {LS LR P L EGA OGA K : Type} [Inhabited K] (ans : Option LS → Option LR → P → L)
  (sch : SchedEv → EGA) (stat : OGA → Bool × Bool) (pkEv : EGA)
  (simS : OGA → SPComp LS) (simR : OGA → SPComp LR)
  (hSf : ∀ a, SPComp.NoFail (simS a)) (hRf : ∀ a, SPComp.NoFail (simR a))
  (FA : Sys (FSt m M) EGA OGA) (schO : SchedOut → OGA) (pkO : FSt m M → OGA)
  (μ : PMF K) (lS : K → (Fin m → M × M) → (Fin m → Bool) → LS)
  (lR : K → (Fin m → M × M) → (Fin m → Bool) → LR) (uS uR : Bool)

/-- The invariant of the lazily keyed abstract system: `InvA`, and a key is drawn only at a
completed view that the key is read for. -/
def KInv (t : Option K × ASt κ m M LS LR) : Prop :=
  InvA t.2 ∧ (t.1.isSome = true → (uS && t.2.ysent || uR && t.2.yrecv) = true)

/-- The abstract system and the simulated ideal functionality agree at an input. -/
theorem absSim_input (t : Option K × ASt κ m M LS LR) (e : InEv m M) :
    SPComp.map (fun p => (projA p.1, p.2))
        (((aKeyed ans lS lR uS uR).lazy μ).step t (.inl (.inl e))) =
      ((simW ans sch stat pkEv simS simR hSf hRf).withSub (idealF FA)).step (projA t)
        (.inl (.inl e)) := by
  obtain ⟨ko, a⟩ := t
  rcases e with x | r <;> rw [lazy_map_det ans μ lS lR uS uR ko a _ (fun _ => rfl)]
  · simp [projA, MultiHybrid.withSub, simW, simStart, MultiHybrid.drive, idealF_send,
      simResume, SPh.isHon, aStep, FOTSched.sendStep, outS, SPComp.pure_bind]
  · simp [projA, MultiHybrid.withSub, simW, simStart, MultiHybrid.drive, idealF_recv,
      simResume, SPh.isHon, aStep, FOTSched.recvStep, SPComp.pure_bind]

/-- The abstract system and the simulated ideal functionality agree at an adversary event or a
corruption event. -/
theorem absSim_adv (hFpoll : ∀ u, FA.step u (sch .poll) =
      SPComp.pure (u, schO (.status u.sent.isSome u.chosen.isSome)))
    (hstat : ∀ b₁ b₂, stat (schO (.status b₁ b₂)) = (b₁, b₂))
    (t : Option K × ASt κ m M LS LR) (e : AEv κ m M ⊕ P) :
    SPComp.map (fun p => (projA p.1, p.2))
        (((aKeyed ans lS lR uS uR).lazy μ).step t (.inr e)) =
      ((simW ans sch stat pkEv simS simR hSf hRf).withSub (idealF FA)).step (projA t)
        (.inr e) := by
  obtain ⟨ko, a⟩ := t
  rcases e with (⟨i, ev⟩ | d) | p <;> rw [lazy_map_det ans μ lS lR uS uR ko a _ (fun _ => rfl)]
  · cases ev with
    | idle => simp [projA, MultiHybrid.withSub, simW, simStart, MultiHybrid.drive, aStep, aSched]
    | poll =>
      simp [projA, MultiHybrid.withSub, simW, simStart, MultiHybrid.drive, aStep, aSched,
        idealF_adv, hFpoll, hstat, simResume, simResA, SPComp.map, SPComp.pure_bind]
    | deliverRecv =>
      simp only [projA]
      rw [simW_withSub_step]
      cases hx : a.xo.isSome <;> cases hr : a.ro.isSome <;> cases hd : a.dR i <;>
        simp [simStart, MultiHybrid.drive, aStep, aSched, idealF_adv, hFpoll, hstat,
          simResume, simResA, SPh.isHon, SPComp.map, SPComp.pure_bind, hx, hr, hd]
    | deliverSend =>
      simp [projA, MultiHybrid.withSub, simW, simStart, MultiHybrid.drive, aStep, aSched]
  · simp [projA, MultiHybrid.withSub, simW, simStart, MultiHybrid.drive, aStep]
  · simp [projA, MultiHybrid.withSub, simW, simStart, MultiHybrid.drive, aStep]

/-- The abstract system and the simulated ideal functionality agree at the wake of the sender
for the base OT `i`. -/
theorem absSim_wakeS (hFpk : ∀ u, FA.step u pkEv = SPComp.pure (u, pkO u))
    (hSS : ∀ (x : Fin m → M × M) (r : Fin m → Bool) {γ : Type} (G : LS → γ),
      (if uS then SPComp.bind (sampleFrom (ofPMF μ)) (fun k => SPComp.pure (G (lS k x r)))
        else SPComp.pure (G (lS default x r))) =
      SPComp.bind (simS (pkO ⟨some x, some r, none, false, false⟩)) fun v => SPComp.pure (G v))
    (t : Option K × ASt κ m M LS LR) (hK : KInv uS uR t) (i : Fin κ) :
    SPComp.map (fun p => (projA p.1, p.2))
        (((aKeyed ans lS lR uS uR).lazy μ).step t (.inl (.inr (.wakeS i)))) =
      ((simW ans sch stat pkEv simS simR hSf hRf).withSub (idealF FA)).step (projA t)
        (.inl (.inr (.wakeS i))) := by
  obtain ⟨ko, a⟩ := t
  obtain ⟨hI, hk⟩ := hK
  by_cases hrev : revealS a i = true
  · have hrev' := hrev
    simp only [revealS, Bool.and_eq_true, Bool.not_eq_true'] at hrev'
    obtain ⟨⟨⟨⟨⟨hx, hr⟩, hd⟩, hc⟩, hall⟩, hys⟩ := hrev'
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
    have hyr : a.yrecv = false := by
      cases h : a.yrecv
      · rfl
      · simpa [hys] using hI.yrecv h
    have hko : ko = none := by
      cases ko with
      | none => rfl
      | some k => simpa [hys, hyr] using hk rfl
    subst hko
    have haw : ∀ vS : (Fin m → M × M) → (Fin m → Bool) → LS,
        aWakeS vS a i = revSt a i (vS x r) := by
      intro vS
      simp [aWakeS, revSt, hx, hr, hd, hc, hall, hys]
    have hlhs : SPComp.map (fun p => (projA p.1, p.2))
        (((aKeyed ans lS lR uS uR).lazy μ).step (none, a) (.inl (.inr (.wakeS i)))) =
        (if uS then SPComp.bind (sampleFrom (ofPMF μ)) (fun k => SPComp.pure
          ((fun v => (projA ((none : Option K), revSt a i v),
            (outS : InOut m M ⊕ (AOut m M ⊕ L)))) (lS k x r)))
        else SPComp.pure ((fun v => (projA ((none : Option K), revSt a i v),
            (outS : InOut m M ⊕ (AOut m M ⊕ L)))) (lS default x r))) := by
      cases huS : uS
      · rw [KeyedSys.lazy_step_none_of_not_uses _ _ (by simp [aKeyed])]
        simp [aKeyed, aStep, haw, SPComp.map, SPComp.pure_bind, projA]
      · rw [KeyedSys.lazy_step_none_of_uses _ _ (by simp [aKeyed, hrev])]
        simp [aKeyed, aStep, haw, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, projA]
    rw [hlhs]
    refine (hSS x r (fun v => (projA ((none : Option K), revSt a i v),
      (outS : InOut m M ⊕ (AOut m M ⊕ L))))).trans ?_
    rw [simW_withSub_step]
    simp [projA, simStart, hd, hc, hall, hys, MultiHybrid.drive, idealF_adv, hFpk, hx, hr, hyr,
      simResume, simResA, SPh.isHon, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, revSt]
  · have hrevf : revealS a i = false := by simpa using hrev
    rw [lazy_map_det ans μ lS lR uS uR ko a _ (fun k => by
      simp only [aStep]; rw [aWakeS_congr hrevf])]
    rw [simW_withSub_step]
    dsimp only at hI
    by_cases h1 : (a.dR i && !a.col i) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      obtain ⟨hx, hr⟩ := hI.dR i h1.1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hx
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
      have hn : (allB (Function.update a.col i true) && !a.ysent) = false := by
        cases hy : a.ysent <;> cases hb : allB (Function.update a.col i true) <;>
          simp_all [revealS]
      have haw : aWakeS (lS default) a i = { a with col := Function.update a.col i true } := by
        simp [aWakeS, hx, hr, h1.1, h1.2, hn]
      have hn' : ¬(allB (Function.update a.col i true) = true ∧ a.ysent = false) := by
        cases hy : a.ysent <;> cases hb : allB (Function.update a.col i true) <;> simp_all
      simp [projA, simStart, h1.1, h1.2, aStep, haw, MultiHybrid.drive, hn']
    · have haw : aWakeS (lS default) a i = a := by
        unfold aWakeS
        split
        · simp [h1]
        · rfl
      have h1' : ¬(a.dR i = true ∧ a.col i = false) := by
        intro hd; simp_all
      simp [projA, simStart, aStep, haw, MultiHybrid.drive, h1']

/-- The abstract system and the simulated ideal functionality agree at the wake of the
receiver. -/
theorem absSim_wakeR
    (hFdel : ∀ u, FA.step u (sch .deliverRecv) =
      SPComp.pure ((FOTSched.schedStep otChoose u .deliverRecv).1, schO .ack))
    (hFpk : ∀ u, FA.step u pkEv = SPComp.pure (u, pkO u))
    (hRind : uR = false → ∀ k, lR k = lR default) (huSR : (uS && uR) = false)
    (hRR : ∀ (x : Fin m → M × M) (r : Fin m → Bool) {γ : Type} (G : LR → γ),
      (if uR then SPComp.bind (sampleFrom (ofPMF μ)) (fun k => SPComp.pure (G (lR k x r)))
        else SPComp.pure (G (lR default x r))) =
      SPComp.bind (simR (pkO ⟨some x, some r, some (otChoose x r), true, false⟩))
        fun v => SPComp.pure (G v))
    (t : Option K × ASt κ m M LS LR) (hK : KInv uS uR t) :
    SPComp.map (fun p => (projA p.1, p.2))
        (((aKeyed ans lS lR uS uR).lazy μ).step t (.inl (.inr .wakeR))) =
      ((simW ans sch stat pkEv simS simR hSf hRf).withSub (idealF FA)).step (projA t)
        (.inl (.inr .wakeR)) := by
  obtain ⟨ko, a⟩ := t
  obtain ⟨hI, hk⟩ := hK
  dsimp only at hI hk
  rcases hi : a.ch.inbox with _ | ⟨y, rest⟩
  · have hrevf : revealR a = false := by simp [revealR, hi]
    rw [lazy_map_det ans μ lS lR uS uR ko a _ (fun k => by
      simp only [aStep]; rw [aWakeR_congr hrevf])]
    rw [simW_withSub_step]
    have haw : aWakeR (lR default) a (L := L) = (a, .inl (.inr none)) := by
      unfold aWakeR; split <;> simp [hi]
    simp [projA, simStart, hi, aStep, haw, MultiHybrid.drive]
  · have hc := hI.count
    rw [hi] at hc
    have hys : a.ysent = true := by cases h : a.ysent <;> simp_all
    have hyr : a.yrecv = false := by cases h : a.yrecv <;> simp_all
    obtain ⟨hx, hr⟩ := hI.sentIn hys
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
    have haw : ∀ vR : (Fin m → M × M) → (Fin m → Bool) → LR, aWakeR vR a (L := L) =
        ({ a with ch := ⟨a.ch.queue, a.ch.cursor, rest⟩, yrecv := true,
                  lvR := a.lvR.or (some (vR x r)) }, .inl (.inr (some (otChoose x r)))) := by
      intro vR
      simp [aWakeR, hr, hi, hx]
    rw [simW_withSub_step]
    rcases hl : a.lvR with _ | l
    · have hlhs : SPComp.map (fun p => (projA p.1, p.2))
          (((aKeyed ans lS lR uS uR).lazy μ).step (ko, a) (.inl (.inr .wakeR))) =
          (if uR then SPComp.bind (sampleFrom (ofPMF μ)) (fun k => SPComp.pure
            ((fun v => (projA ((none : Option K), rcvSt a rest (some v)),
              (.inl (.inr (some (otChoose x r))) : InOut m M ⊕ (AOut m M ⊕ L)))) (lR k x r)))
          else SPComp.pure ((fun v => (projA ((none : Option K), rcvSt a rest (some v)),
              (.inl (.inr (some (otChoose x r))) : InOut m M ⊕ (AOut m M ⊕ L)))) (lR default x r)))
          := by
        rcases ko with _ | k
        · cases huR : uR
          · rw [KeyedSys.lazy_step_none_of_not_uses _ _ (by simp [aKeyed])]
            simp [aKeyed, aStep, haw, hl, SPComp.map, SPComp.pure_bind, projA, rcvSt]
          · rw [KeyedSys.lazy_step_none_of_uses _ _ (by simp [aKeyed, revealR, hr, hx, hi,
              hl])]
            simp [aKeyed, aStep, haw, hl, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, projA,
              rcvSt]
        · have huS : uS = true := by simpa [hys, hyr] using hk rfl
          have huR : uR = false := by simpa [huS] using huSR
          simp [KeyedSys.lazy, KeyedSys.lazyStep, aKeyed, aStep, haw, hl, huR, hRind huR k,
            SPComp.map, SPComp.pure_bind, projA, rcvSt]
      rw [hlhs]
      refine (hRR x r (fun v => (projA ((none : Option K), rcvSt a rest (some v)),
        (.inl (.inr (some (otChoose x r))) : InOut m M ⊕ (AOut m M ⊕ L))))).trans ?_
      simp [projA, simStart, hi, hl, MultiHybrid.drive, idealF_adv, idealF_recv, hFdel, hFpk,
        hx, hr, hyr, simResume, simResA, SPh.isHon, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, rcvSt, FOTSched.schedStep, FOTSched.recvStep]
    · have hrevf : revealR a = false := by simp [revealR, hl]
      rw [lazy_map_det ans μ lS lR uS uR ko a _ (fun k => by
        simp only [aStep]; rw [aWakeR_congr hrevf])]
      simp [projA, simStart, hi, hl, aStep, haw, MultiHybrid.drive, idealF_adv, idealF_recv,
        hFdel, hx, hr, hyr, simResume, simResA, SPh.isHon, SPComp.map, SPComp.pure_bind,
        FOTSched.schedStep, FOTSched.recvStep]

omit [Inhabited K] in
/-- An activation that reads the key completes the view it reads the key for. -/
theorem uses_reveal [Inhabited K] (a : ASt κ m M LS LR)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
    (hu : (aKeyed (L := L) ans lS lR uS uR).uses a e = true)
    (vS : (Fin m → M × M) → (Fin m → Bool) → LS) (vR : (Fin m → M × M) → (Fin m → Bool) → LR) :
    (uS && (aStep (L := L) ans vS vR a e).1.ysent ||
      uR && (aStep (L := L) ans vS vR a e).1.yrecv) = true := by
  rcases e with ((x | r) | (i | _)) | (⟨i, ev⟩ | d) | p <;> simp [aKeyed] at hu
  · simp [aStep, hu.1, aWakeS_reveal hu.2]
  · simp [aStep, hu.1, aWakeR_reveal hu.2]

/-- The invariant holds initially. -/
theorem kinv_init [NeZero κ] :
    KInv uS uR ((aKeyed (κ := κ) (L := L) ans lS lR uS uR).lazy μ).init where
  left := {
    dR := fun _ h => by simp [KeyedSys.lazy, aKeyed, ASt.init] at h
    col := fun _ h => by simp [KeyedSys.lazy, aKeyed, ASt.init] at h
    ysent := by
      simp only [KeyedSys.lazy, aKeyed, ASt.init, allB]
      symm
      simp
    sentIn := fun h => by simp [KeyedSys.lazy, aKeyed, ASt.init] at h
    count := by simp [KeyedSys.lazy, aKeyed, ASt.init, FChan.initSt]
    yrecv := fun h => by simp [KeyedSys.lazy, aKeyed, ASt.init] at h }
  right h := by simp [KeyedSys.lazy] at h

/-- **The abstract system realizes the simulated ideal functionality at distance `0`**, when the
simulator's completions of the views couple with the leaks of the abstract system (`hSS`,
`hRR`) and the ideal functionality's adversary port answers as the scheduler. -/
theorem lazyA_realizes [NeZero κ]
    (hFpoll : ∀ u, FA.step u (sch .poll) =
      SPComp.pure (u, schO (.status u.sent.isSome u.chosen.isSome)))
    (hFdel : ∀ u, FA.step u (sch .deliverRecv) =
      SPComp.pure ((FOTSched.schedStep otChoose u .deliverRecv).1, schO .ack))
    (hFpk : ∀ u, FA.step u pkEv = SPComp.pure (u, pkO u))
    (hstat : ∀ b₁ b₂, stat (schO (.status b₁ b₂)) = (b₁, b₂))
    (hRind : uR = false → ∀ k, lR k = lR default) (huSR : (uS && uR) = false)
    (hSS : ∀ (x : Fin m → M × M) (r : Fin m → Bool) {γ : Type} (G : LS → γ),
      (if uS then SPComp.bind (sampleFrom (ofPMF μ)) (fun k => SPComp.pure (G (lS k x r)))
        else SPComp.pure (G (lS default x r))) =
      SPComp.bind (simS (pkO ⟨some x, some r, none, false, false⟩)) fun v => SPComp.pure (G v))
    (hRR : ∀ (x : Fin m → M × M) (r : Fin m → Bool) {γ : Type} (G : LR → γ),
      (if uR then SPComp.bind (sampleFrom (ofPMF μ)) (fun k => SPComp.pure (G (lR k x r)))
        else SPComp.pure (G (lR default x r))) =
      SPComp.bind (simR (pkO ⟨some x, some r, some (otChoose x r), true, false⟩))
        fun v => SPComp.pure (G v)) :
    Realizes ((aKeyed (κ := κ) ans lS lR uS uR).lazy μ)
      ((simW ans sch stat pkEv simS simR hSf hRf).withSub (idealF FA)) (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap_on _ _ (KInv uS uR) projA (kinv_init ans μ lS lR uS uR) rfl
    (fun t e hK => ?_) (fun t e hK => ?_)
  · obtain ⟨ko, a⟩ := t
    obtain ⟨hI, hk⟩ := hK
    rcases ko with _ | k
    · by_cases hu : (aKeyed ans lS lR uS uR).uses a e = true
      · refine ⟨K, sampleFrom (ofPMF μ), fun k => ((some k, (aStep ans (lS k) (lR k) a e).1),
          (aStep ans (lS k) (lR k) a e).2), ?_, fun k => ⟨hI.step ans _ _ e, fun _ => ?_⟩⟩
        · rw [KeyedSys.lazy_step_none_of_uses _ _ hu]
          simp [aKeyed, SPComp.pure_bind]
        · exact uses_reveal ans lS lR uS uR a e hu _ _
      · refine ⟨Unit, SPComp.pure (), fun _ => ((none, (aStep ans (lS default) (lR default) a
          e).1), (aStep ans (lS default) (lR default) a e).2), ?_,
          fun _ => ⟨hI.step ans _ _ e, by simp⟩⟩
        rw [KeyedSys.lazy_step_none_of_not_uses _ _ (by simpa using hu)]
        simp [aKeyed, SPComp.pure_bind]
    · refine ⟨Unit, SPComp.pure (), fun _ => ((some k, (aStep ans (lS k) (lR k) a e).1),
        (aStep ans (lS k) (lR k) a e).2), ?_, fun _ => ⟨hI.step ans _ _ e, fun _ => ?_⟩⟩
      · simp [KeyedSys.lazy, KeyedSys.lazyStep, aKeyed, SPComp.pure_bind]
      · have h := hk rfl
        have hm := aStep_mono ans a (lS k) (lR k) e
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, hm.1 h2⟩
        · exact Or.inr ⟨h1, hm.2 h2⟩
  · rcases e with ((x | r) | (i | _)) | e
    · exact absSim_input ans sch stat pkEv simS simR hSf hRf FA μ lS lR uS uR t (.inl x)
    · exact absSim_input ans sch stat pkEv simS simR hSf hRf FA μ lS lR uS uR t (.inr r)
    · exact absSim_wakeS ans sch stat pkEv simS simR hSf hRf FA pkO μ lS lR uS uR hFpk
        hSS t hK i
    · exact absSim_wakeR ans sch stat pkEv simS simR hSf hRf FA schO pkO μ lS lR uS uR hFdel
        hFpk hRind huSR hRR t hK
    · exact absSim_adv ans sch stat pkEv simS simR hSf hRf FA schO μ lS lR uS uR hFpoll hstat t e

end Realize

/-! ## The wake closure -/

/-- The deliveries: the delivery of the base OT `i` wakes the sender for it, the delivery of the
channel wakes the receiver. -/
def dlvW {P : Type} : AEv κ m M ⊕ P → Option (WakeEv κ)
  | .inl (.inl (i, .deliverRecv)) => some (.wakeS i)
  | .inl (.inr .deliver) => some .wakeR
  | _ => none

/-- The answer to a wake that would need a second pass. -/
def cutW {L : Type} (_ : WakeEv κ) : InOut m M ⊕ (AOut m M ⊕ L) := .inl (.inl false)

/-- The idle event: the channel's `idle`. -/
def idleW {P : Type} : (InEv m M ⊕ AEv κ m M ⊕ P) ⊕ WakeEv κ := .inl (.inr (.inl (.inr .idle)))

/-- Realization from equal views. -/
theorem realizes_of_view_eq {τ τ' υ E O : Type} {R : Sys τ E O} {A : Sys τ' E O}
    {I : Sys υ E O} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hv : ∀ (ζ : Type) (Z : Strat ζ E O), view R Z = view A Z) (h : Realizes A I b) :
    Realizes R I b := fun ζ => by
  have : (view R : Strat ζ E O → SPComp ζ) = view A := funext (hv ζ)
  rw [this]
  exact h ζ

section Close

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR EGA OGA : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L) [NeZero κ]
  (sch : SchedEv → EGA) (stat : OGA → Bool × Bool) (pkEv : EGA)
  (simS : OGA → SPComp LS) (simR : OGA → SPComp LR)
  (hSf : ∀ a, SPComp.NoFail (simS a)) (hRf : ∀ a, SPComp.NoFail (simR a))

/-- The protocol is idle at the channel's `idle`. -/
theorem iknpW_idleAt :
    MultiHybrid.IdleAt (iknpW H φS φR ans) (wakeEv dlvW idleW).2 (.inr (.inl (.inr .ack))) := by
  rintro ⟨ko, ⟨st, ⟨⟩⟩, c, ch⟩
  have hs : ∀ k, (realW H φS φR ans k).step ((st, ()), c, ch) (.inr (.inl (.inr .idle))) =
      SPComp.pure (((st, ()), c, ch), .inr (.inl (.inr .ack))) := by
    intro k
    rw [realW_step_adv, subR_step_chan]
    simp [FChan.advStep, SPComp.map, SPComp.pure_bind]
  rcases ko with _ | k
  · rw [iknpW, KeyedSys.lazy_step_none_of_not_uses _ _
      (by simp [realKeyed, isAdv, wakeEv, dlvW, idleW])]
    simp [wakeEv, dlvW, idleW, realKeyed, hs, SPComp.pure_bind]
  · simp [wakeEv, dlvW, idleW, iknpW, KeyedSys.lazy, KeyedSys.lazyStep, realKeyed, hs,
      SPComp.pure_bind]

omit [AddCommGroup M] [NeZero κ] in
/-- The simulator over any subroutine is idle at the channel's `idle`. -/
theorem simW_idleAt [Zero M] {υ : Type} (X : Sys υ (InEv m M ⊕ EGA) (InOut m M ⊕ OGA)) :
    MultiHybrid.IdleAt ((simW ans sch stat pkEv simS simR hSf hRf (κ := κ)).withSub X)
      (wakeEv dlvW idleW).2 (.inr (.inl (.inr .ack))) := by
  rintro ⟨s, u⟩
  rw [simW_withSub_step]
  simp [wakeEv, dlvW, idleW, simStart, FChan.advStep, MultiHybrid.drive, SPComp.pure_bind]

/-- **Realization under the wake closure** (composition plumbing) for the IKNP protocol: a
realization of `I` by the protocol behind the simulator `simW` gives a realization of `I` by
the wake closure of the protocol behind the wake closure of `simW`. -/
theorem iknpW_wakeClose {υ : Type} {I : Sys υ (InEv m M ⊕ EGA) (InOut m M ⊕ OGA)}
    {b : (ζ : Type) → Env (Strat ζ ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
      (InOut m M ⊕ (AOut m M ⊕ L))) ζ → ℝ≥0∞}
    (h : RealizesSim (iknpW H φS φR ans) I
      (Simulator.ofMultiHybrid (simW ans sch stat pkEv simS simR hSf hRf)
        (simW_opaque ans sch stat pkEv simS simR hSf hRf)) b) :
    RealizesSim ((iknpW H φS φR ans).wakeClose dlvW cutW) I
      ((Simulator.ofMultiHybrid (simW ans sch stat pkEv simS simR hSf hRf)
        (simW_opaque ans sch stat pkEv simS simR hSf hRf)).wakeClose dlvW
        (fun _ _ h => congrArg dlvW h) cutW (fun _ => Sum.LiftRel.inl trivial))
      (fun ζ Z => b (MultiHybrid.RState Unit ζ ((InEv m M ⊕ AEv κ m M ⊕ P) ⊕ WakeEv κ)
          (InOut m M ⊕ AOut m M ⊕ L) × Option (WakeEv κ))
        ((Open.relabel none (wakeEv dlvW) wakeOut).reduceEnv
          ((MultiHybrid.fbHybrid 1 cutW).reduceEnv idleW Z))) :=
  RealizesSim.wakeClose dlvW _ cutW _ idleW _ _ (iknpW_idleAt H φS φR ans)
    (simW_idleAt ans sch stat pkEv simS simR hSf hRf I) h

end Close

/-! ## Both parties honest -/

/-- The input status in an answer of the scheduler. -/
def statSched : SchedOut → Bool × Bool
  | .status a b => (a, b)
  | .ack => (false, false)

/-- No corruption event. -/
def ansH (_ : Option Unit) (_ : Option Unit) (p : Empty) : Empty := p.elim

section Honest

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) [NeZero κ]

/-- **IKNP with both parties honest**: the parties over the base OTs beside the secure channel,
with no corruption event. -/
noncomputable abbrev iknpRealH :=
  iknpW H (fun _ : IKNPSenderView κ m Unit => ())
    (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansH

/-- **The simulator with both parties honest.** It forwards the inputs to `FOTSched otChoose`,
simulates the base OTs from its input status and the channel with every message replaced by
`y0`, delivers the receiver's output when the simulated channel delivers the message, and reads
no input value. -/
noncomputable abbrev iknpSimH :
    Simulator ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ Empty)) (InOut m M ⊕ (AOut m M ⊕ Empty))
      (InEv m M ⊕ SchedEv) (InOut m M ⊕ SchedOut) (outerV κ m M Empty Empty)
      (innerV m M SchedEv SchedOut) :=
  Simulator.ofMultiHybrid
    (simW ansH id statSched .poll (fun _ => SPComp.pure ()) (fun _ => SPComp.pure ())
      (fun _ => SPComp.pure_noFail _) (fun _ => SPComp.pure_noFail _))
    (simW_opaque _ _ _ _ _ _ _ _)

/-- **IKNP with both parties honest, before the wake closure.** Ideal functionality:
`FOTSched otChoose`, the scheduled transfer of `m` message pairs. Real protocol: the IKNP
parties over `κ` scheduled base OTs beside the secure channel, inputs and wakes on the honest
port. Simulator: `iknpSimH`. Distance `0`. -/
theorem iknpH_realizesSim :
    RealizesSim (iknpRealH (κ := κ) H) (FOTSched otChoose) iknpSimH (fun _ _ => 0) := by
  refine realizes_of_view_eq (fun ζ Z => view_iknpW_eq H _ _ ansH false false
    (fun _ _ => rfl) (fun _ _ => rfl) Z) ?_
  exact lazyA_realizes ansH id statSched .poll (fun _ => SPComp.pure ())
    (fun _ => SPComp.pure ()) (fun _ => SPComp.pure_noFail _) (fun _ => SPComp.pure_noFail _)
    (FOTSched.schedSys otChoose) id (fun u => .status u.sent.isSome u.chosen.isSome)
    (PMF.uniformFintype _) _ _ false false (fun _ => rfl)
    (fun u => by simp [FOTSched.schedSys, FOTSched.schedStep]; split <;> rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    (fun _ _ _ _ => by simp [SPComp.pure_bind])
    (fun _ _ _ _ => by simp [SPComp.pure_bind])

/-- **IKNP with both parties honest, with activation on delivery.** Ideal functionality:
`FOTSched otChoose`, the scheduled transfer of `m` message pairs. Real protocol: the wake
closure of the IKNP parties over `κ` scheduled base OTs beside the secure channel, in which the
delivery of base OT `i` activates the sender and the delivery of the channel activates the
receiver. Simulator: the wake closure of `iknpSimH`; inputs hidden, wakes public. Distance `0`.
-/
theorem iknpH_wake_realizesSim :
    RealizesSim ((iknpRealH (κ := κ) H).wakeClose dlvW cutW) (FOTSched otChoose)
      ((iknpSimH (κ := κ) (m := m) (M := M)).wakeClose dlvW (fun _ _ h => congrArg dlvW h) cutW
        (fun _ => Sum.LiftRel.inl trivial)) (fun _ _ => 0) := by
  have h0 := iknpH_realizesSim (κ := κ) H
  have h := iknpW_wakeClose (P := Empty) (L := Empty) (EGA := SchedEv) (OGA := SchedOut)
    (I := FOTSched otChoose) (b := fun _ _ => 0) H (fun _ : IKNPSenderView κ m Unit => ())
    (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansH id statSched .poll
    (fun _ => SPComp.pure ()) (fun _ => SPComp.pure ()) (fun _ => SPComp.pure_noFail _)
    (fun _ => SPComp.pure_noFail _) h0
  exact h

end Honest

/-! ## A semi-honest corrupt party -/

/-- The input status in an answer of the scheduler beside a leak port. -/
def statSH {L' : Type} : SchedOut ⊕ L' → Bool × Bool
  | .inl o => statSched o
  | .inr _ => (false, false)

/-- The adversary port of `FOTSchedSH otChoose leak`: the scheduler beside the port that shows
the corrupt party's view. -/
noncomputable abbrev shFA {L' : Type} (leak : FSt m M → L') :
    Sys (FSt m M) (SchedEv ⊕ Unit) (SchedOut ⊕ L') :=
  Sys.ofPorts (FOTSched.schedSys otChoose) (peekSys leak)

/-- Unfolding lemma of `idealF` at `shFA`: the scheduled transfer with a semi-honest corrupt
party. -/
theorem idealF_shFA {L' : Type} (leak : FSt m M → L') :
    idealF (shFA leak) = FOTSchedSH otChoose leak := rfl

/-- The scheduler beside a leak port answers a poll with the input status. -/
theorem shFA_poll {L' : Type} (leak : FSt m M → L') (u : FSt m M) :
    (shFA leak).step u (.inl .poll) =
      SPComp.pure (u, .inl (.status u.sent.isSome u.chosen.isSome)) := by
  simp [FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]

/-- The scheduler beside a leak port delivers the receiver's output. -/
theorem shFA_del {L' : Type} (leak : FSt m M → L') (u : FSt m M) :
    (shFA leak).step u (.inl .deliverRecv) =
      SPComp.pure ((FOTSched.schedStep otChoose u .deliverRecv).1, .inl .ack) := by
  simp only [Sys.ofPorts_step_inl, FOTSched.schedSys, SPComp.map, SPComp.pure_bind]
  congr 2
  simp only [FOTSched.schedStep]
  split <;> rfl

/-- The leak port shows the corrupt party's view. -/
theorem shFA_peek {L' : Type} (leak : FSt m M → L') (u : FSt m M) :
    (shFA leak).step u (.inr ()) = SPComp.pure (u, .inr (leak u)) := by
  simp [peekSys, SPComp.map, SPComp.pure_bind]

/-- The sender's view simulator never fails. -/
theorem iknpSimS_noFail (x : Fin m → M × M) :
    SPComp.NoFail (iknpSimS (κ := κ) (fun _ _ => SPComp.pure ()) x) := by
  unfold iknpSimS
  aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })

section CorruptSender

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) [NeZero κ]

/-- The corruption event of a semi-honest corrupt sender shows its completed view. -/
def ansS (ls : Option (IKNPSenderView κ m Unit)) (_ : Option Unit) (_ : Unit) :
    Option (IKNPSenderView κ m Unit) := ls

/-- **IKNP against a semi-honest corrupt sender**: the parties over the base OTs beside the
secure channel; the corruption event shows the sender's secret and columns once it has sent. -/
noncomputable abbrev iknpRealS :=
  iknpW H (fun v : IKNPSenderView κ m Unit => v)
    (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansS

/-- **The simulator against a semi-honest corrupt sender.** As `iknpSimH` over
`FOTSchedSH otChoose leakSend`; at the wake that completes the sender's columns it draws the
sender's view by `iknpSimS`, and the corruption event shows that view. It reads no input value.
-/
noncomputable abbrev iknpSimSW :
    Simulator ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ Unit))
      (InOut m M ⊕ (AOut m M ⊕ Option (IKNPSenderView κ m Unit)))
      (InEv m M ⊕ (SchedEv ⊕ Unit)) (InOut m M ⊕ (SchedOut ⊕ (Option (Fin m → M × M) × Bool)))
      (outerV κ m M Unit (Option (IKNPSenderView κ m Unit)))
      (innerV m M (SchedEv ⊕ Unit) (SchedOut ⊕ (Option (Fin m → M × M) × Bool))) :=
  Simulator.ofMultiHybrid
    (simW ansS .inl statSH (.inr ())
      (fun _ => iknpSimS (fun _ _ => SPComp.pure ()) (fun _ => ((0 : M), (0 : M))))
      (fun _ => SPComp.pure ()) (fun _ => iknpSimS_noFail _) (fun _ => SPComp.pure_noFail _))
    (simW_opaque _ _ _ _ _ _ _ _)

/-- **IKNP against a semi-honest corrupt sender, before the wake closure.** Ideal
functionality: `FOTSchedSH otChoose leakSend`, the scheduled transfer with the sender's view
(its input and completion notice) on the adversary port. Real protocol: the IKNP parties over
`κ` scheduled base OTs beside the secure channel, the corruption event showing the sender's
secret and columns. Simulator: `iknpSimSW`. Distance `0`: the columns are uniform
(`iknpSView_sample`). -/
theorem iknpS_realizesSim :
    RealizesSim (iknpRealS (κ := κ) H) (FOTSchedSH otChoose leakSend) iknpSimSW
      (fun _ _ => 0) := by
  have hSS : ∀ (x : Fin m → M × M) (r : Fin m → Bool) {γ : Type}
      (G : IKNPSenderView κ m Unit → γ),
      (if true = true then SPComp.bind (sampleFrom (ofPMF (PMF.uniformFintype _)))
          (fun k => SPComp.pure (G (lSv (M := M) (fun v => v) k x r)))
        else SPComp.pure (G (lSv (fun v => v) default x r))) =
      SPComp.bind (iknpSimS (fun _ _ => SPComp.pure ()) (fun _ => ((0 : M), (0 : M))))
        fun v => SPComp.pure (G v) := by
    intro x r γ G
    simp only [↓reduceIte]
    rw [ofPMF_uniformFintype, sampleFrom_uniform]
    exact iknpSView_sample _ r G
  have hA := lazyA_realizes (κ := κ) ansS (Sum.inl : SchedEv → SchedEv ⊕ Unit) statSH (.inr ())
    (fun _ => iknpSimS (fun _ _ => SPComp.pure ()) (fun _ => ((0 : M), (0 : M))))
    (fun _ => SPComp.pure ()) (fun _ => iknpSimS_noFail _) (fun _ => SPComp.pure_noFail _)
    (shFA leakSend) Sum.inl (fun u => .inr (leakSend u))
    (PMF.uniformFintype _) (lSv (M := M) fun v => v)
    (lRv H fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) true false
    (shFA_poll leakSend) (shFA_del leakSend) (shFA_peek leakSend) (fun _ _ => rfl)
    (fun _ _ => rfl) rfl (fun x r γ G => hSS x r G)
    (fun _ _ _ _ => by simp [SPComp.pure_bind])
  rw [← idealF_shFA]
  exact realizes_of_view_eq (fun ζ Z => view_iknpW_eq H _ _ ansS true false
    (fun h => absurd h (by decide)) (fun _ _ => rfl) Z) hA

/-- **IKNP against a semi-honest corrupt sender, with activation on delivery.** Ideal
functionality: `FOTSchedSH otChoose leakSend`. Real protocol: the wake closure of the IKNP
parties over `κ` scheduled base OTs beside the secure channel, the corruption event showing the
sender's secret and columns once it has sent. Simulator: the wake closure of `iknpSimSW`, which
draws the sender's view at the wake that completes its columns. Distance `0`. -/
theorem iknpS_wake_realizesSim :
    RealizesSim ((iknpRealS (κ := κ) H).wakeClose dlvW cutW) (FOTSchedSH otChoose leakSend)
      ((iknpSimSW (κ := κ) (m := m) (M := M)).wakeClose dlvW (fun _ _ h => congrArg dlvW h)
        cutW (fun _ => Sum.LiftRel.inl trivial)) (fun _ _ => 0) := by
  have h0 := iknpS_realizesSim (κ := κ) H
  have h := iknpW_wakeClose (P := Unit) (L := Option (IKNPSenderView κ m Unit))
    (EGA := SchedEv ⊕ Unit) (OGA := SchedOut ⊕ (Option (Fin m → M × M) × Bool))
    (I := FOTSchedSH otChoose leakSend) (b := fun _ _ => 0) H
    (fun v : IKNPSenderView κ m Unit => v)
    (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansS .inl statSH (.inr ())
    (fun _ => iknpSimS (fun _ _ => SPComp.pure ()) (fun _ => ((0 : M), (0 : M))))
    (fun _ => SPComp.pure ()) (fun _ => iknpSimS_noFail _) (fun _ => SPComp.pure_noFail _) h0
  exact h

end CorruptSender

section CorruptReceiver

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) [NeZero κ]

/-- The completed view of the receiver: its matrix, the masked message pairs and its output. -/
abbrev RView (κ m : ℕ) (M : Type) := IKNPReceiverView κ m M Unit × (Fin m → M)

/-- The corruption event of a semi-honest corrupt receiver shows its completed view. -/
def ansR (_ : Option Unit) (lr : Option (RView κ m M)) (_ : Unit) : Option (RView κ m M) := lr

/-- **IKNP against a semi-honest corrupt receiver**: the parties over the base OTs beside the
secure channel; the corruption event shows the receiver's matrix, the masked message pairs and
its output once it has received them. -/
noncomputable abbrev iknpRealR :=
  iknpW H (fun _ : IKNPSenderView κ m Unit => ()) (fun v : RView κ m M => v) ansR

/-- The receiver's choices and output in the view of a corrupt receiver in
`FOTSchedSH otChoose (leakRecv otChoose)`. -/
def decR : SchedOut ⊕ (Option (Fin m → Bool) × Option (Fin m → M)) →
    (Fin m → Bool) × (Fin m → M)
  | .inr (r, z) => (r.getD fun _ => false, z.getD 0)
  | .inl _ => (fun _ => false, 0)

variable [Fintype M] [Nonempty M]

/-- The simulator's completion of the receiver's view: `iknpSimR` on the receiver's choices and
output. -/
noncomputable def simRR (o : SchedOut ⊕ (Option (Fin m → Bool) × Option (Fin m → M))) :
    SPComp (RView κ m M) :=
  SPComp.map (fun v => (v, (decR o).2)) (iknpSimR (fun _ => SPComp.pure ()) H (decR o).1 (decR o).2)

omit [NeZero κ] in
/-- The completion of the receiver's view never fails. -/
theorem simRR_noFail (o : SchedOut ⊕ (Option (Fin m → Bool) × Option (Fin m → M))) :
    SPComp.NoFail (simRR (κ := κ) H o) := by
  unfold simRR iknpSimR SPComp.map
  aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })

/-- **The simulator against a semi-honest corrupt receiver.** As `iknpSimH` over
`FOTSchedSH otChoose (leakRecv otChoose)`; at the wake that gives the receiver its message it
takes the receiver's choices and output from the leak port and completes the view by
`iknpSimR`, and the corruption event shows that view. It reads no input value. -/
noncomputable abbrev iknpSimRW :
    Simulator ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ Unit))
      (InOut m M ⊕ (AOut m M ⊕ Option (RView κ m M)))
      (InEv m M ⊕ (SchedEv ⊕ Unit))
      (InOut m M ⊕ (SchedOut ⊕ (Option (Fin m → Bool) × Option (Fin m → M))))
      (outerV κ m M Unit (Option (RView κ m M)))
      (innerV m M (SchedEv ⊕ Unit) (SchedOut ⊕ (Option (Fin m → Bool) × Option (Fin m → M)))) :=
  Simulator.ofMultiHybrid
    (simW ansR .inl statSH (.inr ()) (fun _ => SPComp.pure ()) (simRR H)
      (fun _ => SPComp.pure_noFail _) (simRR_noFail H))
    (simW_opaque _ _ _ _ _ _ _ _)

/-- The key of the correlation-robust hash game: the matrix `T` and the values at the unchosen
positions. -/
abbrev CRKey (κ m : ℕ) (M : Type) := (Fin m → Fin κ → Bool) × (Fin m → M)

/-- A default key of the correlation-robust hash game. -/
local instance instInhabitedCRKey : Inhabited (CRKey κ m M) := ⟨(fun _ _ => false, 0)⟩

/-- The abstract system against a corrupt receiver, keyed by the challenge of the
correlation-robust hash game: the receiver's view is `crRView H th`. -/
noncomputable abbrev crA :=
  aKeyed (κ := κ) (P := Unit) (L := Option (RView κ m M)) ansR (K := CRKey κ m M)
    (fun _ _ _ => ()) (fun th x r => crRView H th x r) false true

/-- **Reduction to correlation-robust hashing.** On a challenge `th`, run the environment `Z`,
from its initial heap, against the abstract system keyed by `th`, and output the bit of its
distinguisher. -/
noncomputable def iknpWakeCRRed {ζ : Type}
    (Z : Env (Strat ζ ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ Unit))
      (InOut m M ⊕ (AOut m M ⊕ Option (RView κ m M)))) ζ) :
    (Fin m → Fin κ → Bool) × (Fin m → M) → SPComp Bool :=
  fixHeap Z.heap fun th => SPComp.bind (view ((crA H).withKey th) Z.input) Z.dist

omit [NeZero κ] in
/-- The hop to uniform pads: the abstract system with the IKNP randomness realizes the one
keyed by the uniform challenge, with bound the correlation-robust hash advantage of
`iknpWakeCRRed H Z`. -/
theorem lazyR_realizes_cr :
    Realizes ((aKeyed (κ := κ) ansR (lSv (M := M) fun _ => ()) (lRv H fun v : RView κ m M => v)
        false true).lazy (PMF.uniformFintype _))
      ((crA H).lazy (PMF.uniformFintype _))
      (fun _ Z => CRHash_Advantage H (iknpWakeCRRed H Z)) := by
  intro ζ Z
  have hk : ∀ T s, (aKeyed (κ := κ) ansR (lSv (M := M) fun _ => ())
      (lRv H fun v : RView κ m M => v) false true).withKey (T, s) =
      (crA H).withKey (T, fun j => H j (T j + s)) := by
    intro T s
    simp only [KeyedSys.withKey, aKeyed]
    congr
    funext a e
    congr 2
    funext x r
    exact iknpRView_eq H T s x r
  have hr : ∀ Zs : Strat ζ _ _, view ((aKeyed (κ := κ) ansR (lSv (M := M) fun _ => ())
      (lRv H fun v : RView κ m M => v) false true).lazy (PMF.uniformFintype _)) Zs =
      SPComp.bind (crHashReal H) fun th => view ((crA H).withKey th) Zs := by
    intro Zs
    rw [KeyedSys.view_lazy _ _ (aKeyed_hind _ _ _ false true (fun _ _ => rfl)
      (fun h => absurd h (by decide))) Zs, ofPMF_uniformFintype, sampleFrom_uniform,
      SPComp.sample_prod_eq]
    simp only [crHashReal, SPComp.bind_assoc, SPComp.pure_bind, hk]
  have hi : ∀ Zs : Strat ζ _ _, view ((crA H).lazy (PMF.uniformFintype _)) Zs =
      SPComp.bind crHashIdeal fun th => view ((crA H).withKey th) Zs := by
    intro Zs
    rw [KeyedSys.view_lazy _ _ (aKeyed_hind _ _ _ false true (fun _ _ => rfl)
      (fun h => absurd h (by decide))) Zs, ofPMF_uniformFintype, sampleFrom_uniform,
      SPComp.sample_prod_eq]
    simp only [crHashIdeal, SPComp.bind_assoc, SPComp.pure_bind]
  change absDiff _ _ ≤ _
  rw [hr, hi, SPComp.bind_assoc, SPComp.bind_assoc,
    prTrue_bind_fixHeap (G := crHashReal H) (by
      unfold crHashReal; aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))
      _ Z.heap,
    prTrue_bind_fixHeap (G := crHashIdeal) (by
      unfold crHashIdeal; aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))
      _ Z.heap]
  exact le_rfl

/-- **IKNP against a semi-honest corrupt receiver, before the wake closure.** Ideal
functionality: `FOTSchedSH otChoose (leakRecv otChoose)`, the scheduled transfer with the
receiver's view (its choices and its delivered output) on the adversary port. Real protocol: the
IKNP parties over `κ` scheduled base OTs beside the secure channel, the corruption event showing
the receiver's matrix, the masked message pairs and its output. Simulator: `iknpSimRW`. Bound:
the correlation-robust hash advantage of the explicit reduction `iknpWakeCRRed H Z`. -/
theorem iknpR_realizesSim :
    RealizesSim (iknpRealR (κ := κ) H) (FOTSchedSH otChoose (leakRecv otChoose)) (iknpSimRW H)
      (fun _ Z => CRHash_Advantage H (iknpWakeCRRed H Z)) := by
  have hRR : ∀ (x : Fin m → M × M) (r : Fin m → Bool) {γ : Type} (G : RView κ m M → γ),
      (if true = true then SPComp.bind (sampleFrom (ofPMF (PMF.uniformFintype (CRKey κ m M))))
          (fun th => SPComp.pure (G (crRView H th x r)))
        else SPComp.pure (G (crRView H default x r))) =
      SPComp.bind (simRR H (.inr (leakRecv otChoose
          (⟨some x, some r, some (otChoose x r), true, false⟩ : FSt m M))))
        fun v => SPComp.pure (G v) := by
    intro x r γ G
    simp only [↓reduceIte]
    rw [ofPMF_uniformFintype, sampleFrom_uniform]
    simp only [simRR, decR, leakRecv, Option.getD_some, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
    exact crRView_sample H x r G
  have hA := lazyA_realizes (κ := κ) ansR (Sum.inl : SchedEv → SchedEv ⊕ Unit) statSH (.inr ())
    (fun _ => SPComp.pure ()) (simRR H) (fun _ => SPComp.pure_noFail _) (simRR_noFail H)
    (shFA (leakRecv otChoose)) Sum.inl (fun u => .inr (leakRecv otChoose u))
    (PMF.uniformFintype (CRKey κ m M)) (fun _ _ _ => ()) (fun th x r => crRView H th x r)
    false true
    (shFA_poll _) (shFA_del _) (shFA_peek _) (fun _ _ => rfl)
    (fun h => absurd h (by decide)) rfl (fun _ _ _ _ => by simp [SPComp.pure_bind])
    (fun x r γ G => hRR x r G)
  rw [← idealF_shFA]
  refine realizes_of_view_eq (fun ζ Z => view_iknpW_eq H _ _ ansR false true
    (fun _ _ => rfl) (fun h => absurd h (by decide)) Z) ?_
  exact fun ζ Z => le_of_le_of_eq ((Realizes.trans (lazyR_realizes_cr H) hA) ζ Z) (add_zero _)

/-- **IKNP against a semi-honest corrupt receiver, with activation on delivery.** Ideal
functionality: `FOTSchedSH otChoose (leakRecv otChoose)`. Real protocol: the wake closure of the
IKNP parties over `κ` scheduled base OTs beside the secure channel, the corruption event showing
the receiver's view once it has received the message. Simulator: the wake closure of
`iknpSimRW`, which takes the receiver's leak at the wake that gives it the message and
completes the view by `iknpSimR`. Bound: the correlation-robust hash advantage of
`iknpWakeCRRed H` at the environment reduced through the wake closure. -/
theorem iknpR_wake_realizesSim :
    RealizesSim ((iknpRealR (κ := κ) H).wakeClose dlvW cutW)
      (FOTSchedSH otChoose (leakRecv otChoose))
      ((iknpSimRW (κ := κ) H).wakeClose dlvW (fun _ _ h => congrArg dlvW h) cutW
        (fun _ => Sum.LiftRel.inl trivial))
      (fun _ Z => CRHash_Advantage H (iknpWakeCRRed H
        ((Open.relabel none (wakeEv dlvW) wakeOut).reduceEnv
          ((MultiHybrid.fbHybrid 1 cutW).reduceEnv idleW Z)))) := by
  have h0 := iknpR_realizesSim (κ := κ) H
  have h := iknpW_wakeClose (P := Unit) (L := Option (RView κ m M))
    (EGA := SchedEv ⊕ Unit) (OGA := SchedOut ⊕ (Option (Fin m → Bool) × Option (Fin m → M)))
    (I := FOTSchedSH otChoose (leakRecv otChoose)) H
    (fun _ : IKNPSenderView κ m Unit => ()) (fun v : RView κ m M => v) ansR .inl statSH
    (.inr ()) (fun _ => SPComp.pure ()) (simRR H) (fun _ => SPComp.pure_noFail _)
    (simRR_noFail H) h0
  exact h

end CorruptReceiver

end CatCrypt.Crypto.OT.IKNPWake

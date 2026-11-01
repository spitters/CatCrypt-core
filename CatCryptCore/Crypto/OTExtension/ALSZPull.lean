/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNPPVW
public import CatCryptCore.Crypto.Assumptions.OWF

/-!
# The ALSZ base OT: a seed OT and the correction string, in pull form

**Ideal functionality.** `FOTSched (alszOut G)` (`OT/FOTSched.lean`): the scheduled transfer
whose sender input is `x = ((k₀, k₁), r)`, a seed pair and the choices `r : Fin m → Bool` of the
IKNP receiver, and whose receiver with the bit `b` obtains the column
`alszOut G x b = G k_b + b · (G k₀ + G k₁ + r)`, which is `G k₀ + b · r`: the column of the IKNP
column pair `(G k₀, G k₀ + r)` (`alszOut_eq`). The sender and the receiver are on the honest port,
the scheduler on the adversary port.

**Real protocol.** `alszOne G`, one base OT of ALSZ (Asharov, Lindell, Schneider and Zohner,
CCS 2013): the parties `alszParty1 G` over the scheduled OT of the seed pair
`FOTSched seedOut` beside the secure channel `FChan ChannelCap.secure` for the correction string.
The receiver of IKNP gives the seed pair to the seed OT and, on its first input, sends the
correction string `u = G k₀ + G k₁ + r` on the channel; it outputs the seed OT's completion bit.
The sender of IKNP with the bit `b` reads its seed `k_b` from the seed OT and `u` from the channel
and outputs its column `G k_b + b · u` once it holds both (pull form). Only the seeds pass through
the OT; the `m`-bit column travels as one correction string.

**Simulator.** `(idSim OEv OOut).tensor simA`: the honest port is forwarded to the ideal
functionality, and `simA` keeps whether the seed is delivered, the stage of the correction string
and the channel's cursor. It obtains the presence of the inputs by a poll of the scheduler,
answers the seed OT's and the channel's adversary events from these, forwards `deliverSend`, and
issues `deliverRecv` at the delivery of the second of the seed and the correction string.

**Bound.** `0` (`alszOne_realizesSim`, by a coupling of the deterministic steps: the channel
shows only the presence of the correction string). The `κ` copies realize the `κ` scheduled base
OTs `FOTSchedPar (Fin κ) (alszOut G)` at distance `0` (`alszBase_realizesSim`, by
`RealizesSim.indexedSplit` and `RealizesSim.mapHon`).

## Main definitions

* `alszU`, `alszCol`, `alszOut`, `colPair`: the correction string, the sender's column, the
  output map and the IKNP column pair of an input.
* `alszParty1`, `alszOne`: the parties of one base OT and the protocol.
* `simA`: the simulator on the adversary port of one base OT.
* `alszBase`, `simKeepA`: the `κ` base OTs and their simulator.

## Main results

* `alszOut_eq`: correctness of the correction string.
* `alszOne_realizesSim`: one base OT realizes `FOTSched (alszOut G)` at distance `0`.
* `alszBase_realizesSim`: the `κ` base OTs realize `FOTSchedPar (Fin κ) (alszOut G)` at
  distance `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.ALSZ

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.Assumptions CatCrypt.Crypto.UCTransparent CatCrypt.Relational
open CatCrypt.Crypto.OT.IKNPWake
open CatCrypt.Crypto.OT.PVWHonest (couple_eq)
open CatCrypt.Crypto.Choreography (ChannelCap)
open CatCrypt.Crypto.UCCoupling (stepPost realizes_zero_of_coupling)
open scoped ENNReal

/-! ## The output of a base OT of ALSZ -/

section Out

variable {m : ℕ} {Seed : Type}

/-- The input of a base OT of ALSZ: the receiver's seed pair and its choices `r`. -/
abbrev AIn (Seed : Type) (m : ℕ) := (Seed × Seed) × (Fin m → Bool)

/-- The correction string of ALSZ for the input `x = ((k₀, k₁), r)`: `G k₀ + G k₁ + r`. -/
def alszU (G : PRGDef Seed (Fin m → Bool)) (x : AIn Seed m) : Fin m → Bool :=
  G.stretch x.1.1 + G.stretch x.1.2 + x.2

/-- The sender's column from the seed `k` it obtained for the bit `b` and the correction `u`:
`G k`, plus `u` when `b` is set. -/
def alszCol (G : PRGDef Seed (Fin m → Bool)) (k : Seed) (b : Bool) (u : Fin m → Bool) :
    Fin m → Bool :=
  G.stretch k + cond b u 0

/-- The output of a base OT of ALSZ: the sender's column from the seed of its bit and the
correction string. -/
def alszOut (G : PRGDef Seed (Fin m → Bool)) (x : AIn Seed m) (b : Bool) : Fin m → Bool :=
  alszCol G (cond b x.1.2 x.1.1) b (alszU G x)

/-- The column pair of IKNP that an input of ALSZ stands for: `T = G k₀` and `T + r`. -/
def colPair (G : PRGDef Seed (Fin m → Bool)) (x : AIn Seed m) : BPair m :=
  (G.stretch x.1.1, G.stretch x.1.1 + x.2)

/-- **Correctness of the correction string.** The sender's column is the IKNP column of the
column pair `(G k₀, G k₀ + r)` at its bit. -/
theorem alszOut_eq (G : PRGDef Seed (Fin m → Bool)) (x : AIn Seed m) (b : Bool) :
    alszOut G x b = baseOut (colPair G x) b := by
  funext j
  cases b <;>
    simp only [alszOut, alszCol, alszU, baseOut, colPair, Bool.cond_true, Bool.cond_false,
      Pi.add_apply, Pi.zero_apply, Bool.false_eq_true, ite_true, ite_false] <;>
    cases G.stretch x.1.1 j <;> cases G.stretch x.1.2 j <;> cases x.2 j <;> decide

end Out

/-! ## The protocol of one base OT -/

section Proto

variable {Seed : Type} {m : ℕ}

/-- The output of the seed OT: the second seed on the bit `true`. -/
def seedOut (p : Seed × Seed) (b : Bool) : Seed := cond b p.2 p.1

/-- The leakage of a correction string on the secure channel: nothing beyond its presence. -/
def uLeak (_ : Fin m → Bool) : Unit := ()

variable (m) in
/-- The secure channel for the correction string. -/
noncomputable abbrev uChan :=
  FChan ChannelCap.secure (uLeak (m := m))

variable (Seed m) in
/-- The seed OT beside the secure channel for the correction string. -/
noncomputable abbrev seedSub :=
  (FOTSched (seedOut (Seed := Seed))).withChan (uChan m)

variable (Seed m) in
/-- The honest events of one base OT of ALSZ: the receiver's input, or the sender's bit. -/
abbrev OEv := AIn Seed m ⊕ Bool

variable (m) in
/-- The honest outputs of one base OT of ALSZ. -/
abbrev OOut := Bool ⊕ Option (Fin m → Bool)

variable (Seed m) in
/-- The calls of the parties of one base OT: the seed OT beside the channel. -/
abbrev SCall := ((Seed × Seed) ⊕ Bool) ⊕ ChanHEv (Fin m → Bool)

variable (Seed m) in
/-- The answers to the calls of the parties of one base OT. -/
abbrev SAns := (Bool ⊕ Option Seed) ⊕ ChanHOut (Fin m → Bool)

variable (m) in
/-- The adversary events of one base OT: the seed OT's scheduler and the channel. -/
abbrev OAEv := SchedEv ⊕ ChanAEv (Fin m → Bool)

variable (m) in
/-- The adversary outputs of one base OT. -/
abbrev OAOut := SchedOut ⊕ ChanAOut (Fin m → Bool) Unit

/-- The phase of an activation of the parties of one base OT: which answer is awaited. -/
inductive APh (m : ℕ) where
  /-- No call is pending. -/
  | idle
  /-- The seed OT's answer to the receiver's seed pair, with the correction to send if any. -/
  | sSeed (u : Option (Fin m → Bool))
  /-- The channel's answer to the correction, with the completion bit to output. -/
  | sU (d : Bool)
  /-- The seed OT's answer to the sender's bit. -/
  | rSeed
  /-- The channel's answer to the sender's receive. -/
  | rU

/-- The state of the parties of one base OT. -/
structure ASt (Seed : Type) (m : ℕ) where
  /-- The receiver's first input. -/
  xo : Option (AIn Seed m)
  /-- The sender's first bit. -/
  bo : Option Bool
  /-- The seed the sender has obtained. -/
  ko : Option Seed
  /-- The correction string the sender has obtained. -/
  uo : Option (Fin m → Bool)
  /-- Whether the sender has output its column. -/
  done : Bool
  /-- The phase of the activation. -/
  ph : APh m

/-- The initial state of the parties of one base OT. -/
def ASt.init : ASt Seed m := ⟨none, none, none, none, false, .idle⟩

/-- The sender's output once it holds its seed and the correction string: its column, once. -/
def rDec (G : PRGDef Seed (Fin m → Bool)) (st : ASt Seed m) : ASt Seed m × OOut m :=
  match st.ko, st.uo, st.done with
  | some k, some u, false =>
    ({ st with done := true, ph := .idle }, .inr (some (alszCol G k (st.bo.getD false) u)))
  | _, _, _ => ({ st with ph := .idle }, .inr none)

/-- The first step of an activation: the receiver gives its seed pair to the seed OT (and sends
the correction string on its first input); the sender gives its bit to the seed OT. -/
def aStart (G : PRGDef Seed (Fin m → Bool)) (st : ASt Seed m) :
    OEv Seed m → ASt Seed m × (SCall Seed m ⊕ OOut m)
  | .inl x =>
    let u : Option (Fin m → Bool) := if st.xo.isNone then some (alszU G x) else none
    ({ st with xo := st.xo.or (some x), ph := .sSeed u }, .inl (.inl (.inl x.1)))
  | .inr b => ({ st with bo := st.bo.or (some b), ph := .rSeed }, .inl (.inl (.inr b)))

/-- The step of the parties of one base OT on the answer `o` of a call. -/
def aResume (G : PRGDef Seed (Fin m → Bool)) (st : ASt Seed m) (o : SAns Seed m) :
    ASt Seed m × (SCall Seed m ⊕ OOut m) :=
  match st.ph, o with
  | .sSeed (some u), .inl (.inl d) => ({ st with ph := .sU d }, .inl (.inr (.send u)))
  | .sSeed none, .inl (.inl d) => ({ st with ph := .idle }, .inr (.inl d))
  | .sU d, _ => ({ st with ph := .idle }, .inr (.inl d))
  | .rSeed, .inl (.inr ko) =>
    match st.uo with
    | none => ({ st with ko := st.ko.or ko, ph := .rU }, .inl (.inr .recv))
    | some _ =>
      ((rDec G { st with ko := st.ko.or ko }).1, .inr (rDec G { st with ko := st.ko.or ko }).2)
  | .rU, .inr (.got uo) =>
    ((rDec G { st with uo := st.uo.or uo }).1, .inr (rDec G { st with uo := st.uo.or uo }).2)
  | _, _ => ({ st with ph := .idle }, .inr (.inl false))

/-- **The parties of one base OT of ALSZ.** The receiver of IKNP (the sender of the seed OT)
with the input `((k₀, k₁), r)` gives the seed pair to the seed OT and, on its first input, sends
the correction string `G k₀ + G k₁ + r` on the secure channel; it outputs the seed OT's
completion bit. The sender of IKNP (the receiver of the seed OT) with the bit `b` reads its seed
from the seed OT and the correction string from the channel, and outputs its column
`G k_b + b · u` once it holds both (pull form). -/
noncomputable def alszParty1 (G : PRGDef Seed (Fin m → Bool)) :
    MultiHybrid (ASt Seed m) (OEv Seed m) (OOut m) (SCall Seed m) (SAns Seed m) where
  init := ASt.init
  fuel := 1
  start st e := SPComp.pure (aStart G st e)
  resume st o := SPComp.pure (aResume G st o)
  finish st o := SPComp.pure (match aResume G st o with
    | (st', .inr out) => (st', out)
    | (st', .inl _) => ({ st' with ph := .idle }, .inl false))
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- **One base OT of ALSZ**: the parties over the seed OT beside the channel, the adversary ports
forwarded. -/
noncomputable def alszOne (G : PRGDef Seed (Fin m → Bool)) :=
  ((alszParty1 G).tensor (MultiHybrid.idSim (OAEv m) (OAOut m))).withSub (seedSub Seed m)

end Proto

/-! ## The simulator of one base OT -/

section Sim

variable {m : ℕ}

/-- The stage of the correction string. -/
inductive UStage where
  /-- In transit once the receiver has its input. -/
  | wait
  /-- Dropped. -/
  | lost
  /-- Delivered. -/
  | dlv
  deriving DecidableEq

/-- The awaited answer of the simulator's activation. -/
inductive SPh where
  /-- No call is pending. -/
  | idle
  /-- The input status, for a poll of the seed OT. -/
  | sPoll
  /-- The input status, for a delivery of the seed. -/
  | sDel
  /-- The input status, for a poll of the channel. -/
  | cPoll
  /-- The input status, for a delivery (`false`) or a drop (`true`) of the channel. -/
  | cDel (drop : Bool)
  /-- The acknowledgement of a forwarded call, answered on the seed OT's port (`false`) or the
  channel's port (`true`). -/
  | fwd (side : Bool)

/-- The state of the simulator of one base OT. -/
structure SSt where
  /-- Whether the seed is delivered. -/
  kd : Bool
  /-- The stage of the correction string. -/
  ug : UStage
  /-- The number of messages of the channel shown to the adversary. -/
  cur : ℕ
  /-- The phase of the activation. -/
  ph : SPh

variable (m) in
/-- The decisions of the simulator: a call to the scheduler of `FOTSched alszOut`, or an output. -/
abbrev SDec := SchedEv ⊕ OAOut m

/-- The simulator's first step. -/
def sStart (s : SSt) : OAEv m → SSt × SDec m
  | .inl .idle => (s, .inr (.inl .ack))
  | .inl .poll => ({ s with ph := .sPoll }, .inl .poll)
  | .inl .deliverRecv => ({ s with ph := .sDel }, .inl .poll)
  | .inl .deliverSend => ({ s with ph := .fwd false }, .inl .deliverSend)
  | .inr .idle => (s, .inr (.inr .ack))
  | .inr .poll => ({ s with ph := .cPoll }, .inl .poll)
  | .inr .deliver => ({ s with ph := .cDel false }, .inl .poll)
  | .inr .drop => ({ s with ph := .cDel true }, .inl .poll)
  | .inr (.tamper _) => (s, .inr (.inr .ack))

/-- The number of messages of the channel in transit, given whether the receiver has its input. -/
def uLen (g : UStage) (a : Bool) : ℕ := if a && decide (g = .wait) then 1 else 0

/-- The simulator's step on an answer of the scheduler: the delivery of the second of the seed
and the correction string issues `deliverRecv`. -/
def sResume (s : SSt) : SchedOut → SSt × SDec m
  | .status a b => match s.ph with
    | .sPoll => ({ s with ph := .idle }, .inr (.inl (.status a b)))
    | .sDel =>
      if a && b && !s.kd then
        if s.ug = .dlv then ({ s with kd := true, ph := .fwd false }, .inl .deliverRecv)
        else ({ s with kd := true, ph := .idle }, .inr (.inl .ack))
      else ({ s with ph := .idle }, .inr (.inl .ack))
    | .cPoll =>
      ({ s with cur := min (s.cur + 1) (uLen s.ug a), ph := .idle },
        .inr (.inr (.leak (if s.cur < uLen s.ug a then some (.inr ()) else none))))
    | .cDel d =>
      if a && decide (s.ug = .wait) then
        if d then ({ s with ug := .lost, cur := s.cur - 1, ph := .idle }, .inr (.inr .ack))
        else if s.kd then
          ({ s with ug := .dlv, cur := s.cur - 1, ph := .fwd true }, .inl .deliverRecv)
        else ({ s with ug := .dlv, cur := s.cur - 1, ph := .idle }, .inr (.inr .ack))
      else ({ s with cur := s.cur - 1, ph := .idle }, .inr (.inr .ack))
    | _ => ({ s with ph := .idle }, .inr (.inl .ack))
  | .ack => match s.ph with
    | .fwd side => ({ s with ph := .idle }, .inr (if side then .inr .ack else .inl .ack))
    | _ => ({ s with ph := .idle }, .inr (.inl .ack))

variable (m) in
/-- **The simulator of one base OT** over the scheduler of `FOTSched alszOut`: it keeps whether
the seed is delivered, the stage of the correction string and the channel's cursor; it obtains
the presence of the inputs by a poll of the scheduler, answers the seed OT's and the channel's
adversary events from these, forwards `deliverSend`, and issues `deliverRecv` at the delivery
of the second of the seed and the correction string. -/
noncomputable def simA : MultiHybrid SSt (OAEv m) (OAOut m) SchedEv SchedOut where
  init := ⟨false, .wait, 0, .idle⟩
  fuel := 1
  start s e := SPComp.pure (sStart s e)
  resume s o := SPComp.pure (sResume s o)
  finish s o := SPComp.pure (match sResume (m := m) s o with
    | (s', .inr d) => (s', d)
    | (s', .inl _) => ({ s' with ph := .idle }, .inl .ack))
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

end Sim

/-! ## The coupling -/

section Coupling

variable {Seed : Type} {m : ℕ} (G : PRGDef Seed (Fin m → Bool))

/-- The seed of the sender: the seed of its bit. -/
def kOf (xo : Option (AIn Seed m)) (bo : Option Bool) : Option Seed :=
  match xo, bo with
  | some x, some b => some (seedOut x.1 b)
  | _, _ => none

/-- The sender's column. -/
def outOf (xo : Option (AIn Seed m)) (bo : Option Bool) : Option (Fin m → Bool) :=
  match xo, bo with
  | some x, some b => some (alszOut G x b)
  | _, _ => none

/-- The state of the protocol at the parameters: the inputs `xo` and `bo`, whether the seed is
delivered (`kd`) and read (`kr`), the stage of the correction string (`ug`) and whether it is
read (`ur`), the channel's cursor, whether the column is output, and the completion bit. -/
def realOf (xo : Option (AIn Seed m)) (bo : Option Bool) (kd kr : Bool) (ug : UStage)
    (ur : Bool) (cur : ℕ) (done dS : Bool) :
    (ASt Seed m × Unit) × (SchedSt (Seed × Seed) Bool Seed × ChanSt (Fin m → Bool)) :=
  ((⟨xo, bo, if kr then kOf xo bo else none, if ur then xo.map (alszU G) else none, done,
      .idle⟩, ()),
    (⟨xo.map (·.1), bo, if kd && !kr then kOf xo bo else none, kd, dS⟩,
      ⟨if ug = .wait then (xo.map (alszU G)).toList else [], cur,
        if ug = .dlv && !ur then (xo.map (alszU G)).toList else []⟩))

/-- The state of the simulator over `FOTSched alszOut` at the parameters. -/
def idealOf (xo : Option (AIn Seed m)) (bo : Option Bool) (kd : Bool) (ug : UStage) (cur : ℕ)
    (done dS : Bool) : (Unit × SSt) × SchedSt (AIn Seed m) Bool (Fin m → Bool) :=
  (((), ⟨kd, ug, cur, .idle⟩),
    ⟨xo, bo, if kd && decide (ug = .dlv) && !done then outOf G xo bo else none,
      kd && decide (ug = .dlv), dS⟩)

/-- The reachable parameters. -/
def WF (xo : Option (AIn Seed m)) (bo : Option Bool) (kd kr : Bool) (ug : UStage) (ur : Bool)
    (cur : ℕ) (done : Bool) : Prop :=
  (kd → xo.isSome ∧ bo.isSome) ∧ (kr → kd) ∧ (ug ≠ .wait → xo.isSome) ∧ (ur → ug = .dlv) ∧
    (done → kr ∧ ur) ∧ cur ≤ uLen ug xo.isSome

/-- The relation of the protocol's states and the simulator's states. -/
def ARel (t : (ASt Seed m × Unit) × (SchedSt (Seed × Seed) Bool Seed × ChanSt (Fin m → Bool)))
    (u : (Unit × SSt) × SchedSt (AIn Seed m) Bool (Fin m → Bool)) : Prop :=
  ∃ xo bo kd kr ug ur cur done dS, t = realOf G xo bo kd kr ug ur cur done dS ∧
    u = idealOf G xo bo kd ug cur done dS ∧ WF xo bo kd kr ug ur cur done

variable (Seed m) in
/-- The honest port of the seed OT beside the channel. -/
noncomputable abbrev subL1 :=
  Sys.chanPortL (Sys.ofPorts (FOTSched.sendSys (X := Seed × Seed) (C := Bool) (Y := Seed))
    FOTSched.recvSys) (FChan.honSys (V := Fin m → Bool)) (FOTSched (seedOut (Seed := Seed))).init
    (uChan m).init

variable (Seed m) in
/-- The adversary port of the seed OT beside the channel. -/
noncomputable abbrev subR1 :=
  Sys.chanPortR (FOTSched.schedSys (seedOut (Seed := Seed)))
    (FChan.advSys ChannelCap.secure (uLeak (m := m))) (FOTSched (seedOut (Seed := Seed))).init
    (uChan m).init

/-- Unfolding lemma of `alszOne`: a step on an honest event. -/
theorem alszOne_step_inl (st : ASt Seed m) (u : Unit)
    (t : SchedSt (Seed × Seed) Bool Seed × ChanSt (Fin m → Bool)) (e : OEv Seed m) :
    (alszOne G).step ((st, u), t) (.inl e) =
      SPComp.map (fun p => (((p.1.1, u), p.1.2), Sum.inl p.2))
        ((alszParty1 G).stepFuel (subL1 Seed m) 1 (st, t) e) := by
  rw [alszOne, MultiHybrid.tensor_withSub_step_inl _ _ (seedSub Seed m) (subL1 Seed m)
    (Sys.withChan_step_inl (fun _ _ => rfl) (fun _ _ => rfl))]
  rfl

/-- Unfolding lemma of `alszOne`: a step on an adversary event. -/
theorem alszOne_step_inr (st : ASt Seed m) (u : Unit)
    (t : SchedSt (Seed × Seed) Bool Seed × ChanSt (Fin m → Bool)) (a : OAEv m) :
    (alszOne G).step ((st, u), t) (.inr a) =
      SPComp.map (fun q => (((st, u), q.1), .inr q.2)) ((subR1 Seed m).step t a) := by
  rw [alszOne, MultiHybrid.tensor_withSub_step_inr _ _ (seedSub Seed m) (subR1 Seed m)
    (Sys.withChan_step_inr (fun _ _ => rfl) (fun _ _ => rfl)), MultiHybrid.idSim_stepFuel]
  simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

variable (Seed m) in
/-- The simulated ideal system: `(idSim OEv OOut).tensor simA` over `FOTSched alszOut`. -/
noncomputable abbrev idealA :=
  ((MultiHybrid.idSim (OEv Seed m) (OOut m)).tensor (simA m)).withSub (FOTSched (alszOut G))

/-- Unfolding lemma of the simulated ideal system: a step on an honest event. -/
theorem idealA_step_inl (s : SSt) (t : SchedSt (AIn Seed m) Bool (Fin m → Bool))
    (e : OEv Seed m) :
    (idealA Seed m G).step (((), s), t) (.inl e) =
      SPComp.map (fun q => ((((), s), q.1), Sum.inl q.2))
        ((Sys.ofPorts FOTSched.sendSys FOTSched.recvSys).step t e) := by
  rw [idealA, MultiHybrid.tensor_withSub_step_inl _ _ _
    (Sys.ofPorts FOTSched.sendSys FOTSched.recvSys) (fun _ _ => rfl), MultiHybrid.idSim_stepFuel]
  simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- Unfolding lemma of the simulated ideal system: a step on an adversary event. -/
theorem idealA_step_inr (s : SSt) (t : SchedSt (AIn Seed m) Bool (Fin m → Bool))
    (a : OAEv m) :
    (idealA Seed m G).step (((), s), t) (.inr a) =
      SPComp.map (fun p => ((((), p.1.1), p.1.2), Sum.inr p.2))
        ((simA m).stepFuel (FOTSched.schedSys (alszOut G)) 1 (s, t) a) := by
  rw [idealA, MultiHybrid.tensor_withSub_step_inr _ _ _ (FOTSched.schedSys (alszOut G))
    (fun _ _ => rfl)]
  rfl

/-- Unfolding lemma of `subL1`: the receiver's seed pair to the seed OT. -/
@[simp] theorem subL1_send (t : SchedSt (Seed × Seed) Bool Seed) (c : ChanSt (Fin m → Bool))
    (p : Seed × Seed) :
    (subL1 Seed m).step (t, c) (.inl (.inl p)) =
      SPComp.pure (((FOTSched.sendStep t p).1, c), .inl (.inl (FOTSched.sendStep t p).2)) := by
  simp [subL1, Sys.chanPortL, FOTSched.sendSys, SPComp.map, SPComp.pure_bind]

/-- Unfolding lemma of `subL1`: the sender's bit to the seed OT. -/
@[simp] theorem subL1_recv (t : SchedSt (Seed × Seed) Bool Seed) (c : ChanSt (Fin m → Bool))
    (b : Bool) :
    (subL1 Seed m).step (t, c) (.inl (.inr b)) =
      SPComp.pure (((FOTSched.recvStep t b).1, c), .inl (.inr (FOTSched.recvStep t b).2)) := by
  simp [subL1, Sys.chanPortL, FOTSched.recvSys, SPComp.map, SPComp.pure_bind]

/-- Unfolding lemma of `subL1`: an honest event of the channel. -/
@[simp] theorem subL1_chan (t : SchedSt (Seed × Seed) Bool Seed) (c : ChanSt (Fin m → Bool))
    (e : ChanHEv (Fin m → Bool)) :
    (subL1 Seed m).step (t, c) (.inr e) =
      SPComp.pure ((t, (FChan.honStep c e).1), .inr (FChan.honStep c e).2) := by
  simp [subL1, Sys.chanPortL, FChan.honSys, SPComp.map, SPComp.pure_bind]

/-- Unfolding lemma of `subR1`: an adversary event of the seed OT. -/
@[simp] theorem subR1_sched (t : SchedSt (Seed × Seed) Bool Seed) (c : ChanSt (Fin m → Bool))
    (a : SchedEv) :
    (subR1 Seed m).step (t, c) (.inl a) =
      SPComp.pure (((FOTSched.schedStep seedOut t a).1, c),
        .inl (FOTSched.schedStep seedOut t a).2) := by
  simp [subR1, Sys.chanPortR, FOTSched.schedSys, SPComp.map, SPComp.pure_bind]

/-- Unfolding lemma of `subR1`: an adversary event of the channel. -/
@[simp] theorem subR1_chan (t : SchedSt (Seed × Seed) Bool Seed) (c : ChanSt (Fin m → Bool))
    (d : ChanAEv (Fin m → Bool)) :
    (subR1 Seed m).step (t, c) (.inr d) =
      SPComp.pure ((t, (FChan.advStep ChannelCap.secure uLeak c d).1),
        .inr (FChan.advStep ChannelCap.secure uLeak c d).2) := by
  simp [subR1, Sys.chanPortR, FChan.advSys, SPComp.map, SPComp.pure_bind]

omit G in
/-- Unfolding lemma of `alszParty1`: the first step. -/
@[simp] theorem alszParty1_start (G : PRGDef Seed (Fin m → Bool)) (st : ASt Seed m)
    (e : OEv Seed m) : (alszParty1 G).start st e = SPComp.pure (aStart G st e) := rfl

omit G in
/-- Unfolding lemma of `alszParty1`: the step on an answer. -/
@[simp] theorem alszParty1_resume (G : PRGDef Seed (Fin m → Bool)) (st : ASt Seed m)
    (o : SAns Seed m) : (alszParty1 G).resume st o = SPComp.pure (aResume G st o) := rfl

omit G in
/-- Unfolding lemma of `alszParty1`: the step on the answer to the last call. -/
@[simp] theorem alszParty1_finish (G : PRGDef Seed (Fin m → Bool)) (st : ASt Seed m)
    (o : SAns Seed m) : (alszParty1 G).finish st o = SPComp.pure (match aResume G st o with
      | (st', .inr out) => (st', out)
      | (st', .inl _) => ({ st' with ph := .idle }, .inl false)) := rfl

/-- Unfolding lemma of `simA`: the first step. -/
@[simp] theorem simA_start (s : SSt) (e : OAEv m) :
    (simA m).start s e = SPComp.pure (sStart s e) := rfl

/-- Unfolding lemma of `simA`: the step on an answer. -/
@[simp] theorem simA_resume (s : SSt) (o : SchedOut) :
    (simA m).resume s o = SPComp.pure (sResume s o) := rfl

/-- Unfolding lemma of `simA`: the step on the answer to the last call. -/
@[simp] theorem simA_finish (s : SSt) (o : SchedOut) :
    (simA m).finish s o = SPComp.pure (match sResume (m := m) s o with
      | (s', .inr d) => (s', d)
      | (s', .inl _) => ({ s' with ph := .idle }, .inl .ack)) := rfl

/-- The next message not yet shown, on the secure channel, is a bare presence notice exactly
when the cursor is below the number of messages in transit. -/
theorem pollLeak_uChan (l : List (Fin m → Bool)) (k : ℕ) (inb : List (Fin m → Bool)) :
    FChan.pollLeak ChannelCap.secure (uLeak (m := m)) ⟨l, k, inb⟩ =
      if k < l.length then some (.inr ()) else none := by
  simp [FChan.pollLeak, ChannelCap.secure, List.head?_drop, List.getElem?_map]
  split_ifs <;> simp_all
  rfl

/-- The length of the queue of the channel at the parameters. -/
theorem queue_length (xo : Option (AIn Seed m)) (ug : UStage) :
    (if ug = .wait then (xo.map (alszU G)).toList else []).length = uLen ug xo.isSome := by
  rcases xo with _ | x <;> cases ug <;> simp [uLen]

/-- The step on the receiver's input. -/
theorem stepA_send (xo : Option (AIn Seed m)) (bo : Option Bool) (kd kr : Bool) (ug : UStage)
    (ur : Bool) (cur : ℕ) (done dS : Bool) (hwf : WF xo bo kd kr ug ur cur done)
    (x : AIn Seed m) :
    rHoare eqPre ((alszOne G).step (realOf G xo bo kd kr ug ur cur done dS) (.inl (.inl x)))
      ((idealA Seed m G).step (idealOf G xo bo kd ug cur done dS) (.inl (.inl x)))
      (stepPost (ARel G)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hwf
  rcases xo with _ | x₀
  · obtain rfl : ug = .wait := by
      by_contra hg
      simpa using h3 hg
    obtain rfl : kd = false := by cases kd <;> simp_all
    obtain rfl : kr = false := by cases kr <;> simp_all
    obtain rfl : ur = false := by cases ur <;> simp_all
    obtain rfl : done = false := by cases done <;> simp_all
    obtain rfl : cur = 0 := by simpa [uLen] using h6
    refine couple_eq (realOf G (some x) bo false false .wait false 0 false dS)
      (idealOf G (some x) bo false .wait 0 false dS) (.inl (.inl dS)) ?_ ?_
      ⟨some x, bo, false, false, .wait, false, 0, false, dS, rfl, rfl, by simp [WF, uLen]⟩
    · simp [realOf, alszOne_step_inl, MultiHybrid.stepFuel, aStart, aResume,
        MultiHybrid.drive, FOTSched.sendStep, FChan.honStep, SPComp.map, SPComp.pure_bind]
    · simp [idealOf, idealA_step_inl, FOTSched.sendSys, FOTSched.sendStep, SPComp.map,
        SPComp.pure_bind]
  · refine couple_eq (realOf G (some x₀) bo kd kr ug ur cur done dS)
      (idealOf G (some x₀) bo kd ug cur done dS) (.inl (.inl dS)) ?_ ?_
      ⟨some x₀, bo, kd, kr, ug, ur, cur, done, dS, rfl, rfl, h1, h2, h3, h4, h5, h6⟩
    · simp [realOf, alszOne_step_inl, MultiHybrid.stepFuel, aStart, aResume,
        MultiHybrid.drive, FOTSched.sendStep, SPComp.map, SPComp.pure_bind]
    · simp [idealOf, idealA_step_inl, FOTSched.sendSys, FOTSched.sendStep, SPComp.map,
        SPComp.pure_bind]

/-- The step on the sender's bit: it reads the delivered seed and correction string and outputs
its column once it holds both. -/
theorem stepA_recv (xo : Option (AIn Seed m)) (bo : Option Bool) (kd kr : Bool) (ug : UStage)
    (ur : Bool) (cur : ℕ) (done dS : Bool) (hwf : WF xo bo kd kr ug ur cur done) (b : Bool) :
    rHoare eqPre ((alszOne G).step (realOf G xo bo kd kr ug ur cur done dS) (.inl (.inr b)))
      ((idealA Seed m G).step (idealOf G xo bo kd ug cur done dS) (.inl (.inr b)))
      (stepPost (ARel G)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hwf
  refine couple_eq (realOf G xo (bo.or (some b)) kd kd ug (decide (ug = .dlv)) cur
      (done || (kd && decide (ug = .dlv))) dS)
    (idealOf G xo (bo.or (some b)) kd ug cur (done || (kd && decide (ug = .dlv))) dS)
    (.inl (.inr (if kd && decide (ug = .dlv) && !done then outOf G xo bo else none))) ?_ ?_
    ⟨xo, bo.or (some b), kd, kd, ug, decide (ug = .dlv), cur, _, dS, rfl, rfl, ?_⟩
  · rcases xo with _ | x <;> rcases bo with _ | b₀ <;> cases kd <;> cases kr <;> cases ug <;>
      cases ur <;> cases done <;>
      simp_all [realOf, alszOne_step_inl, MultiHybrid.stepFuel, aStart, aResume,
        rDec, MultiHybrid.drive, FOTSched.recvStep, FChan.honStep, SPComp.map, SPComp.pure_bind,
        kOf, outOf, alszOut, seedOut]
  · simp [idealOf, idealA_step_inl, FOTSched.recvSys, FOTSched.recvStep, SPComp.map,
      SPComp.pure_bind]
    rcases xo with _ | x <;> rcases bo with _ | b₀ <;> cases kd <;> cases ug <;> cases done <;>
      simp_all [outOf]
  · refine ⟨fun h => ⟨(h1 h).1, by simp⟩, id, h3, fun h => by simpa using h, ?_, h6⟩
    cases kd <;> cases ug <;> cases done <;> simp_all

/-- The step on an adversary event of the seed OT. -/
theorem stepA_sched (xo : Option (AIn Seed m)) (bo : Option Bool) (kd kr : Bool) (ug : UStage)
    (ur : Bool) (cur : ℕ) (done dS : Bool) (hwf : WF xo bo kd kr ug ur cur done) (a : SchedEv) :
    rHoare eqPre ((alszOne G).step (realOf G xo bo kd kr ug ur cur done dS) (.inr (.inl a)))
      ((idealA Seed m G).step (idealOf G xo bo kd ug cur done dS) (.inr (.inl a)))
      (stepPost (ARel G)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hwf
  cases a with
  | idle =>
    refine couple_eq (realOf G xo bo kd kr ug ur cur done dS) (idealOf G xo bo kd ug cur done dS)
      (.inr (.inl .ack)) ?_ ?_ ⟨xo, bo, kd, kr, ug, ur, cur, done, dS, rfl, rfl, h1, h2, h3, h4,
        h5, h6⟩
    · simp [realOf, alszOne_step_inr, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
    · simp [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, MultiHybrid.drive,
        SPComp.map, SPComp.pure_bind]
  | poll =>
    refine couple_eq (realOf G xo bo kd kr ug ur cur done dS) (idealOf G xo bo kd ug cur done dS)
      (.inr (.inl (.status xo.isSome bo.isSome))) ?_ ?_ ⟨xo, bo, kd, kr, ug, ur, cur, done, dS,
        rfl, rfl, h1, h2, h3, h4, h5, h6⟩
    · simp [realOf, alszOne_step_inr, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
    · simp [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, sResume, MultiHybrid.drive,
        FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
  | deliverRecv =>
    refine couple_eq (realOf G xo bo (kd || (xo.isSome && bo.isSome)) kr ug ur cur done dS)
      (idealOf G xo bo (kd || (xo.isSome && bo.isSome)) ug cur done dS)
      (.inr (.inl .ack)) ?_ ?_ ⟨xo, bo, _, kr, ug, ur, cur, done, dS, rfl, rfl, ?_⟩
    · rcases xo with _ | x <;> rcases bo with _ | b₀ <;> cases kd <;> cases kr <;>
        simp_all [realOf, alszOne_step_inr, FOTSched.schedStep, SPComp.map, SPComp.pure_bind,
          kOf]
    · rcases xo with _ | x <;> rcases bo with _ | b₀ <;> cases kd <;> cases ug <;>
        cases done <;>
        simp_all [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, sResume,
          MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind,
          outOf]
    · refine ⟨fun h => ?_, fun h => by simp [h2 h], h3, h4, h5, h6⟩
      rcases xo with _ | x <;> rcases bo with _ | b₀ <;> cases kd <;> simp_all
  | deliverSend =>
    refine couple_eq (realOf G xo bo kd kr ug ur cur done (dS || (xo.isSome && bo.isSome)))
      (idealOf G xo bo kd ug cur done (dS || (xo.isSome && bo.isSome)))
      (.inr (.inl .ack)) ?_ ?_ ⟨xo, bo, kd, kr, ug, ur, cur, done, _, rfl, rfl, h1, h2, h3, h4,
        h5, h6⟩
    · rcases xo with _ | x <;> rcases bo with _ | b₀ <;>
        simp [realOf, alszOne_step_inr, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
    · rcases xo with _ | x <;> rcases bo with _ | b₀ <;>
        simp [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, sResume,
          MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]

/-- The step on an adversary event of the channel. -/
theorem stepA_chan (xo : Option (AIn Seed m)) (bo : Option Bool) (kd kr : Bool) (ug : UStage)
    (ur : Bool) (cur : ℕ) (done dS : Bool) (hwf : WF xo bo kd kr ug ur cur done)
    (d : ChanAEv (Fin m → Bool)) :
    rHoare eqPre ((alszOne G).step (realOf G xo bo kd kr ug ur cur done dS) (.inr (.inr d)))
      ((idealA Seed m G).step (idealOf G xo bo kd ug cur done dS) (.inr (.inr d)))
      (stepPost (ARel G)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hwf
  cases d with
  | idle =>
    refine couple_eq (realOf G xo bo kd kr ug ur cur done dS) (idealOf G xo bo kd ug cur done dS)
      (.inr (.inr .ack)) ?_ ?_ ⟨xo, bo, kd, kr, ug, ur, cur, done, dS, rfl, rfl, h1, h2, h3, h4,
        h5, h6⟩
    · simp [realOf, alszOne_step_inr, FChan.advStep, SPComp.map, SPComp.pure_bind]
    · simp [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, MultiHybrid.drive,
        SPComp.map, SPComp.pure_bind]
  | tamper v =>
    refine couple_eq (realOf G xo bo kd kr ug ur cur done dS) (idealOf G xo bo kd ug cur done dS)
      (.inr (.inr .ack)) ?_ ?_ ⟨xo, bo, kd, kr, ug, ur, cur, done, dS, rfl, rfl, h1, h2, h3, h4,
        h5, h6⟩
    · simp [realOf, alszOne_step_inr, FChan.advStep, ChannelCap.secure, SPComp.map,
        SPComp.pure_bind]
    · simp [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, MultiHybrid.drive,
        SPComp.map, SPComp.pure_bind]
  | poll =>
    refine couple_eq
      (realOf G xo bo kd kr ug ur (min (cur + 1) (uLen ug xo.isSome)) done dS)
      (idealOf G xo bo kd ug (min (cur + 1) (uLen ug xo.isSome)) done dS)
      (.inr (.inr (.leak (if cur < uLen ug xo.isSome then some (.inr ()) else none)))) ?_ ?_
      ⟨xo, bo, kd, kr, ug, ur, _, done, dS, rfl, rfl, h1, h2, h3, h4, h5, min_le_right _ _⟩
    · simp only [realOf, alszOne_step_inr, subR1_chan, FChan.advStep, pollLeak_uChan,
        queue_length, SPComp.map, SPComp.pure_bind]
    · simp [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, sResume, MultiHybrid.drive,
        FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
  | deliver =>
    refine couple_eq
      (realOf G xo bo kd kr (if xo.isSome && decide (ug = .wait) then .dlv else ug) ur (cur - 1)
        done dS)
      (idealOf G xo bo kd (if xo.isSome && decide (ug = .wait) then .dlv else ug) (cur - 1)
        done dS)
      (.inr (.inr .ack)) ?_ ?_ ⟨xo, bo, kd, kr, _, ur, cur - 1, done, dS, rfl, rfl, ?_⟩
    · rcases xo with _ | x <;> cases ug <;> cases ur <;>
        simp_all [realOf, alszOne_step_inr, FChan.advStep, FChan.popTo, SPComp.map,
          SPComp.pure_bind]
    · rcases xo with _ | x <;> rcases bo with _ | b₀ <;> cases kd <;> cases ug <;>
        cases done <;>
        simp_all [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, sResume,
          MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind,
          outOf]
    · rcases xo with _ | x <;> cases ug <;> cases ur <;> cases kr <;> cases done <;>
        simp_all [WF, uLen]
  | drop =>
    refine couple_eq
      (realOf G xo bo kd kr (if xo.isSome && decide (ug = .wait) then .lost else ug) ur (cur - 1)
        done dS)
      (idealOf G xo bo kd (if xo.isSome && decide (ug = .wait) then .lost else ug) (cur - 1)
        done dS)
      (.inr (.inr .ack)) ?_ ?_ ⟨xo, bo, kd, kr, _, ur, cur - 1, done, dS, rfl, rfl, ?_⟩
    · rcases xo with _ | x <;> cases ug <;> cases ur <;>
        simp_all [realOf, alszOne_step_inr, FChan.advStep, FChan.popTo, ChannelCap.secure,
          SPComp.map, SPComp.pure_bind]
    · rcases xo with _ | x <;> cases ug <;>
        simp_all [idealOf, idealA_step_inr, MultiHybrid.stepFuel, sStart, sResume,
          MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
    · rcases xo with _ | x <;> cases ug <;> cases ur <;> cases kr <;> cases done <;>
        simp_all [WF, uLen]

/-- **One base OT of ALSZ realizes `FOTSched alszOut`** (genuine UC). Ideal functionality:
`FOTSched (alszOut G)`, the scheduled transfer whose receiver obtains the column `G k_b + b · u`
of the input `((k₀, k₁), r)`. Real protocol: `alszOne G`, the seed OT of the seed pair beside the
secure channel carrying the correction string, the sender reading both in pull form. Simulator:
the forwarding of the honest port beside `simA`, which answers the seed OT's and the channel's
adversary events from the input status and issues `deliverRecv` at the second of the two
deliveries. Distance `0`, for every view `VH` of the honest port. -/
theorem alszOne_realizesSim {VH : PubView (OEv Seed m) (OOut m)} :
    RealizesSim (alszOne G) (FOTSched (alszOut G))
      (Simulator.tensor (MultiHybrid.idSim (OEv Seed m) (OOut m)) (simA m)
        (MultiHybrid.idSim_opaque VH) (MultiHybrid.opaque_eqView _)) (fun _ _ => 0) := by
  refine (realizes_zero_of_coupling (R := alszOne G) (I := idealA Seed m G) (rel := ARel G)
    ⟨?_, ?_⟩).1
  · exact ⟨none, none, false, false, .wait, false, 0, false, false, rfl, rfl, by
      simp [WF, uLen]⟩
  · rintro t u e ⟨xo, bo, kd, kr, ug, ur, cur, done, dS, rfl, rfl, hwf⟩
    rcases e with (x | b) | (a | d)
    · exact stepA_send G xo bo kd kr ug ur cur done dS hwf x
    · exact stepA_recv G xo bo kd kr ug ur cur done dS hwf b
    · exact stepA_sched G xo bo kd kr ug ur cur done dS hwf a
    · exact stepA_chan G xo bo kd kr ug ur cur done dS hwf d

/-- The seed OT beside the channel never fails. -/
theorem seedSub_noFail : ∀ t g, SPComp.NoFail ((seedSub Seed m).step t g) := by
  have hL := Sys.withChan_step_inl (X := FOTSched (seedOut (Seed := Seed))) (C := uChan m)
    (XL := Sys.ofPorts FOTSched.sendSys FOTSched.recvSys) (CL := FChan.honSys)
    (fun _ _ => rfl) (fun _ _ => rfl)
  have hR := Sys.withChan_step_inr (X := FOTSched (seedOut (Seed := Seed))) (C := uChan m)
    (XR := FOTSched.schedSys seedOut) (CR := FChan.advSys ChannelCap.secure uLeak)
    (fun _ _ => rfl) (fun _ _ => rfl)
  rintro ⟨t, c⟩ ((g | g) | (g | g))
  · rw [hL]
    rcases g with p | b <;>
      simp [Sys.chanPortL, FOTSched.sendSys, FOTSched.recvSys, SPComp.map, SPComp.pure_bind] <;>
      exact SPComp.pure_noFail _
  · rw [hL]
    simp only [Sys.chanPortL, Sys.ofPorts_step_inr, Sys.onSnd_step, FChan.honSys, SPComp.map,
      SPComp.pure_bind]
    exact SPComp.pure_noFail _
  · rw [hR]
    simp only [Sys.chanPortR, Sys.ofPorts_step_inl, Sys.onFst_step, FOTSched.schedSys,
      SPComp.map, SPComp.pure_bind]
    exact SPComp.pure_noFail _
  · rw [hR]
    simp only [Sys.chanPortR, Sys.ofPorts_step_inr, Sys.onSnd_step, FChan.advSys, SPComp.map,
      SPComp.pure_bind]
    exact SPComp.pure_noFail _

/-- One base OT of ALSZ never fails. -/
theorem alszOne_noFail : ∀ t e, SPComp.NoFail ((alszOne G).step t e) :=
  MultiHybrid.withSub_noFail _ _ seedSub_noFail

/-- One base OT of ALSZ is idle at the seed OT's `idle`. -/
theorem alszOne_idleAt :
    MultiHybrid.IdleAt (alszOne G) (.inr (.inl .idle)) (.inr (.inl .ack)) := by
  rintro ⟨⟨st, u⟩, t, c⟩
  simp [alszOne_step_inr, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]

/-- The simulated base OT is idle at the seed OT's `idle`. -/
theorem idealA_idleAt :
    MultiHybrid.IdleAt (idealA Seed m G) (.inr (.inl .idle)) (.inr (.inl .ack)) := by
  rintro ⟨⟨⟨⟩, s⟩, t⟩
  simp [idealA_step_inr, MultiHybrid.stepFuel, sStart, MultiHybrid.drive, SPComp.map,
    SPComp.pure_bind]

end Coupling

/-! ## The `κ` base OTs of ALSZ -/

section Base

open CatCrypt.Crypto.OT.IKNPPVW

variable {Seed : Type} {κ m : ℕ} (G : PRGDef Seed (Fin m → Bool))

/-- The honest events of the `κ` ALSZ base OTs: an input to the base OT `i`, or a bit. -/
abbrev AHEv (κ : ℕ) (Seed : Type) (m : ℕ) := (Fin κ × AIn Seed m) ⊕ (Fin κ × Bool)

variable (κ) in
/-- **The `κ` base OTs of ALSZ**: `κ` copies of `alszOne G`, with the indexed events split by
port on the honest port of `FOTSchedPar` and on the indexed adversary events. -/
noncomputable def alszBase :=
  (((alszOne G).indexed (ι := Fin κ)).mapPorts splitIdx id).mapPorts (Sum.map splitIdx id) id

/-- The simulator of the `κ` ALSZ base OTs: the indexed copies of `simA` keeping the active
copy. -/
noncomputable abbrev simKeepA (κ m : ℕ) [NeZero κ] := (simA m).indexedKeep (ι := Fin κ)

/-- The view of the honest port of the ALSZ base OTs: equal events, all outputs related. -/
def aBaseHV (κ : ℕ) (Seed : Type) (m : ℕ) : PubView (AHEv κ Seed m) (OOut m) where
  ev := Eq
  out _ _ := True

/-- **The `κ` base OTs of ALSZ realize `FOTSchedPar (Fin κ) (alszOut G)`** behind the forwarding
of the honest port beside `simKeepA`, at distance `0`: the bound of `RealizesSim.indexedSplit` is
the sum over the `κ` copies of the bound `0` of one copy. -/
theorem alszBase_realizesSim [NeZero κ] :
    RealizesSim (alszBase κ G) (FOTSchedPar (Fin κ) (alszOut G))
      (Simulator.tensor (MultiHybrid.idSim (AHEv κ Seed m) (OOut m)) (simKeepA κ m)
        (MultiHybrid.idSim_opaque (aBaseHV κ Seed m)) (MultiHybrid.opaque_eqView _).indexedKeep)
      (fun _ _ => 0) := by
  have h₁ := RealizesSim.indexedSplit (κ := κ) (FOTSched_portTyped _) (alszOne_noFail G)
    (fotSched_noFail _) (.inr (.inl .idle)) (alszOne_idleAt G) (idealA_idleAt G)
    (alszOne_realizesSim G (VH := IKNPSquare.hidView))
  have h₂ := RealizesSim.mapHon (VH' := aBaseHV κ Seed m)
    (Sys.PortTyped.indexedSplit (FOTSched_portTyped _)) splitIdx id
    (fun e e' he => by subst he; exact ⟨rfl, trivial⟩) (fun _ _ _ => trivial) h₁
  simp only [Sum.map_id_id] at h₂
  have h₃ := RealizesSim.subst_stepMap (Y := FOTSchedPar (Fin κ) (alszOut G))
    (X := (((FOTSched (alszOut G)).indexed (ι := Fin κ)).mapPorts splitIdx id).mapPorts
      (Sum.map splitIdx id) id)
    (π := (MultiHybrid.idSim (AHEv κ Seed m) (OOut m)).tensor (simKeepA κ m))
    (hπ := (MultiHybrid.idSim_opaque (aBaseHV κ Seed m)).tensor
      (MultiHybrid.opaque_eqView _).indexedKeep) id rfl (fun t e => ?_) h₂
  · exact fun ζ Z => le_of_le_of_eq (h₃ ζ Z) Finset.sum_const_zero
  · rcases e with (⟨i, p⟩ | ⟨i, b⟩) | ⟨i, a⟩ <;>
      simp [FOTSchedPar, FOTSched, Sys.mapPorts, Sys.relabel, splitIdx, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]

/-- The `κ` ALSZ base OTs are idle at the seed OT's `idle` of the first copy. -/
theorem alszBase_idleAt [NeZero κ] :
    MultiHybrid.IdleAt (alszBase κ G) (.inr (default, .inl .idle)) (.inr (.inl .ack)) := by
  intro t
  simp only [alszBase, Sys.mapPorts, Sys.relabel, Sum.map_inr, splitIdx, id, SPComp.map,
    Sys.indexed_step, SPComp.bind_assoc, SPComp.pure_bind]
  rw [alszOne_idleAt G (t default)]
  simp [SPComp.pure_bind]

/-- The simulated `κ` ALSZ base OTs are idle at the seed OT's `idle` of the first copy. -/
theorem simKeepA_idleAt [NeZero κ] :
    MultiHybrid.IdleAt (((MultiHybrid.idSim (AHEv κ Seed m) (OOut m)).tensor
      (simKeepA κ m)).withSub (FOTSchedPar (Fin κ) (alszOut G))) (.inr (default, .inl .idle))
      (.inr (.inl .ack)) := by
  rintro ⟨⟨⟨⟩, ss, j⟩, u⟩
  rw [MultiHybrid.tensor_withSub_step_inr _ _ _
    ((FOTSched.schedSys (alszOut G)).indexed (ι := Fin κ)) (fun _ _ => rfl)]
  simp [MultiHybrid.stepFuel, MultiHybrid.indexedKeep_start, sStart, MultiHybrid.drive,
    SPComp.map, SPComp.pure_bind]

end Base

end CatCrypt.Crypto.OT.ALSZ

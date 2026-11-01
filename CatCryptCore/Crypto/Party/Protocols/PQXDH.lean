/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.UnwindingTransfer
public import CatCryptCore.Crypto.Party.Timed
public import CatCryptCore.Crypto.AKE.PQXDHSquare

/-!
# PQXDH in the party language

**Ideal functionality.** `F_AKE (SPComp.sample K) true` of `CatCryptCore.Crypto.AKE.FAKESys`, the
authenticated key exchange with adversarial key delivery, the unlinked delivery
`newKeyUnlinked`, corruption of parties and uniform keys in `K`, as for X3DH.

**Real protocol.** `PQXDHSquare.pqxdhReal P G`, PQXDH (Kret and Schmidt, 2023) over the group
`G : DHGroup S W` and the key encapsulation mechanism `P`, for every session
(`CatCryptCore.Crypto.AKE.PQXDHSquare`): X3DH with a post-quantum prekey, whose shared secret
enters the key derivation.

**Simulator.** The PQXDH simulator over the operations `O : KemOps PK SK SS C` of a KEM, written
as a program of the party language: `PQXDH.simBody O G`, one iteration per activation, as the
multi-call hybrid `PQXDH.simLoop O G` over `F_AKE`. It keeps a copy of the real state, draws every
secret and KEM key pair itself, encapsulates on `complete`, forwards honest events to `F_AKE` and
delivers keys by `newKey` or `newKeyUnlinked`. The start of an activation samples exactly the
start `simStart O G` of the hand-written simulator `simProtK O G` (`PQXDH.simStartP_samples`), so
the program running with any subroutine is step-equivalent to `simProtK O G`
(`PQXDH.simProtK_stepEq_simLoop`). Its structure is derived from the program by the generic
theorems of the party language: information flow `ProgE.ViewRel` of the loop is an unwinding
relation (`Prog.loopSys_unwinding`, `MultiHybrid.unwinding_ofSys`), so the simulator is opaque
(`PQXDH.simLoop_opaque`); its time certificate is the graded bound of the costed program
`PQXDH.simBodyT O G`, which charges the length of the key-derivation table per iteration and one
unit per sample, key generation and encapsulation (`PQXDH.simLoop_time`). At `kemOps P` the
program simulator is `PQXDH.pqxdhSimP P G`.

**Results.** `PQXDH.pqxdh_realizesSim_prog`: `pqxdhReal P G` realizes `F_AKE` behind the program
simulator `pqxdhSimP P G` with the oracle-game bound of
`PQXDHSquare.pqxdh_realizesSim_oracleGame`, the advantage of `OProt.oracle.reduction Z` between
`realGame P G` and `simGame P G`. Sampling a KEM key pair, an encapsulation and the shared secret
in a program goes through the codes of countable types, so the program statements carry the
hypotheses `[Countable PK] [Countable SK] [Countable SS] [Countable C]`, which the statements of
the hand-written simulator do not.

Search words: party language, PQXDH, UC, simulator, F_AKE, KEM, opacity, unwinding, time
certificate.

## Main definitions

* `PQXDH.ltP`, `PQXDH.roP`: the long-term secrets and the key derivation as programs.
* `PQXDH.simStartP`, `PQXDH.simBody`, `PQXDH.simLoop`: the PQXDH simulator as a program.
* `PQXDH.simBodyT`: its costed form.
* `PQXDH.pqxdhSimKP`, `PQXDH.pqxdhSimP`: the bundled program simulator.

## Main results

* `PQXDH.simStartP_samples`: the start of an activation samples `simStart`.
* `PQXDH.simProtK_stepEq_simLoop`: the program form of `simProtK`.
* `PQXDH.simLoop_unwinding`, `PQXDH.simLoop_opaque`: unwinding and opacity of the program.
* `PQXDH.simBodyT_loopBoundGraded`, `PQXDH.simLoop_time`: the time certificate.
* `PQXDH.pqxdh_realizesSim_prog`: PQXDH realizes `F_AKE` behind the program simulator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party.Protocols.PQXDH

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent.FAKE CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.AKE.X3DHSquare (RSt ltStep roStep aliceInp bobInp opkOf ephPubOf Named FEv
  FOut subView)
open CatCrypt.Crypto.PAKE.DHExtract Prog

/-- Programs of the PQXDH simulator: outer interface `(OEv W SS C, OOut S W K PK C)`, calls to
`F_AKE`. -/
abbrev P (S W K PK SS C : Type) (α : Type) :=
  Prog (OEv W SS C ⊕ FOut K) (FEv K ⊕ OOut S W K PK C) α

/-- The default outer output of the simulator. -/
instance {S W K PK C : Type} : Inhabited (OOut S W K PK C) := ⟨.inr (.inl .ack)⟩

/-- Programs that neither receive nor send. -/
abbrev NoIO {E O α : Type} (p : Prog E O α) : Prop :=
  ProgE.Ports (fun _ => False) (fun _ => False) p

/-- Sampling from a countable type keeps a program free of receives and sends. -/
theorem noIO_sample {E O α β : Type} [Countable β] {μ : SPComp β} {k : β → Prog E O α}
    (hk : ∀ b, NoIO (k b)) : NoIO (Prog.sample μ k) := by
  unfold Prog.sample
  refine ProgE.Ports.opN _ _ fun n => ?_
  split
  · exact hk _
  · exact ProgE.Ports.fail

section Prog

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS]
  [Countable C] (O : KemOps PK SK SS C) (G : DHGroup S W)

/-- `ltStep` as a program. -/
noncomputable def ltP {E O : Type} (s : RSt S W K) (pid : PartyId) :
    Prog E O ((S × S) × RSt S W K) :=
  match s.lt pid with
  | some l => .ret (l, s)
  | none => Prog.sample (SPComp.sample (S × S)) fun l =>
      .ret (l, { s with lt := Function.update s.lt pid (some l) })

/-- `roStep` as a program. -/
noncomputable def roP {E O D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    Prog E O (K × List (D × K)) :=
  match tb.lookup x with
  | some v => .ret (v, tb)
  | none => Prog.sample (SPComp.sample K) fun v => .ret (v, (x, v) :: tb)

/-- `deliver` as a program. -/
noncomputable def deliverP (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS))
    (x : Inst) (r : Rec K) (ip : PInp W SS) :
    P S W K PK SS C (SimSt S W K PK SK SS C × Dec S W K PK C) :=
  if Exposed s.x.st x r then
    ProgE.bind (roP s.ro ip) fun p =>
      .ret ((pKeyed s x r p.1 p.2, Function.update inp x (some ip), .out (.inl .ack)),
        .inl (.inr (.newKey x.1 x.2 p.1)))
  else
    .ret ((pKeyed s x r default s.ro, Function.update inp x (some ip), .out (.inl .ack)),
      .inl (.inr (if (inp (x.1, r.peer)).all (· = ip) then .newKey x.1 x.2 default
        else .newKeyUnlinked x.1 x.2 default)))

/-- `simComplete` as a program. -/
noncomputable def simCompleteP (s : SimSt S W K PK SK SS C) (x : Inst) :
    P S W K PK SS C (SimSt S W K PK SK SS C × Dec S W K PK C) :=
  match s.1.x.st.recs x, s.1.x.eph x with
  | some r, some ek =>
    match opkOf s.1.x x.1 r.peer, pkOf s.1 x.1 r.peer with
    | some opk, some pk =>
      if r.role = .initiator ∧ r.key.isNone then
        ProgE.bind (ltP s.1.x x.2) fun la => ProgE.bind (ltP la.2 r.peer) fun lb =>
          Prog.sample (O.encaps pk) fun kc =>
            deliverP { s.1 with x := lb.2, ct := Function.update s.1.ct x (some kc.2) } s.2.1 x r
              (aliceInp G x.1 x.2 r.peer la.1.1 ek (G.pub lb.1.1) (G.pub lb.1.2) (G.pub opk),
                kc.1)
      else .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
    | _, _ => .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | _, _ => .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))

/-- `simSend` as a program. -/
noncomputable def simSendP (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    P S W K PK SS C (SimSt S W K PK SK SS C × Dec S W K PK C) :=
  match s.1.x.st.recs x, s.1.x.eph x, s.1.kem x with
  | some r, some opk, some kp =>
    match O.decaps kp.2 c with
    | some ss =>
      if r.role = .responder ∧ r.key.isNone then
        ProgE.bind (ltP s.1.x x.2) fun lb => ProgE.bind (ltP lb.2 r.peer) fun la =>
          deliverP { s.1 with x := la.2 } s.2.1 x r
            (bobInp G x.1 r.peer x.2 (G.pub la.1.1) e lb.1.1 lb.1.2 opk, ss)
      else .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
    | none => .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | _, _, _ => .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))

/-- `simCorrupt` as a program. -/
noncomputable def simCorruptP (s : SimSt S W K PK SK SS C) (pid : PartyId) :
    P S W K PK SS C (SimSt S W K PK SK SS C × Dec S W K PK C) :=
  if Named s.1.x.st pid then .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.secret none))))
  else
    ProgE.bind (ltP s.1.x pid) fun l =>
      .ret (({ s.1 with x := { l.2 with st := corruptStep l.2.st pid } }, s.2.1,
        .out (.inl (.secret (some l.1)))), .inl (.inr (.corrupt pid)))

/-- `simStart` as a program. -/
noncomputable def simStartP (s : SimSt S W K PK SK SS C) :
    OEv W SS C → P S W K PK SS C (SimSt S W K PK SK SS C × Dec S W K PK C)
  | .inl (.newSession sid pid peer role) =>
    if (s.1.x.st.recs (sid, pid)).isNone then
      Prog.sample (SPComp.sample S) fun y =>
        if role = .responder then
          Prog.sample O.keygen fun kp =>
            .ret (({ s.1 with
                x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                                  eph := Function.update s.1.x.eph (sid, pid) (some y) },
                kem := Function.update s.1.kem (sid, pid) (some kp) }, s.2.1, .fwd),
              .inl (.inl (.newSession sid pid peer role)))
        else
          .ret (({ s.1 with
                x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                                  eph := Function.update s.1.x.eph (sid, pid) (some y) } },
                s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
    else .ret ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => .ret ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | .inr .poll =>
    .ret (({ s.1 with x := { s.1.x with st := (pollStep s.1.x.st).1 } }, s.2.1, .fwd),
      .inr (.inr (.inl (.notice (pollStep s.1.x.st).2))))
  | .inr (.pub pid) => ProgE.bind (ltP s.1.x pid) fun l =>
      .ret (({ s.1 with x := l.2 }, s.2.1, .fwd),
        .inr (.inr (.inl (.pub (G.pub l.1.1) (G.pub l.1.2)))))
  | .inr (.ephPub sid pid) =>
    .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.eph (ephPubOf G s.1.x (sid, pid))))))
  | .inr (.pqPub sid pid) =>
    .ret ((s.1, s.2.1, .fwd), .inr (.inr (.inr (pkOf s.1 sid pid, s.1.ct (sid, pid)))))
  | .inr (.corrupt pid) => simCorruptP s pid
  | .inr (.complete sid pid) => simCompleteP O G s (sid, pid)
  | .inr (.send sid pid e c) => simSendP O G s (sid, pid) e c
  | .inr (.kdf x) => ProgE.bind (roP s.1.ro x) fun p =>
      .ret (({ s.1 with ro := p.2 }, s.2.1, .fwd), .inr (.inr (.inl (.hash p.1))))

/-- The continuation of the call pending at `s`: output the answer of `F_AKE` as `simOut` does in
the phase of `s`, and return. -/
def simK (s : SimSt S W K PK SK SS C) (a : FOut K) : P S W K PK SS C (SimSt S W K PK SK SS C) :=
  ProgE.bind (outE (simOut s.2.2 a)) fun _ => .ret (s.1, s.2.1, .fwd)

/-- The end of an activation after the decision of `simStartP`: a call to `F_AKE` with the
continuation `simK`, or the outer output. -/
def simDecide (q : SimSt S W K PK SK SS C × Dec S W K PK C) :
    P S W K PK SS C (SimSt S W K PK SK SS C) :=
  match q.2 with
  | .inl f => call f (simK q.1)
  | .inr o => ProgE.bind (outE o) fun _ => .ret q.1

/-- **The PQXDH simulator over the KEM operations `O` as a program**: one iteration per
activation. -/
noncomputable def simBody (s : SimSt S W K PK SK SS C) :
    P S W K PK SS C (SimSt S W K PK SK SS C) :=
  ProgE.bind recvO fun e => ProgE.bind (simStartP O G s e) simDecide

/-- The loop of `simBody` as a multi-call hybrid over `F_AKE`, with fuel `0`. -/
noncomputable def simLoop :
    MultiHybrid (P S W K PK SS C (SimSt S W K PK SK SS C)) (OEv W SS C) (OOut S W K PK C)
      (FEv K) (FOut K) :=
  loopMulti (simBody O G) (pInit, fun _ => none, .fwd) 0

/-! ## The program samples the hand-written simulator -/

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltP` samples `ltStep`. -/
theorem ltP_samples {E O : Type} (s : RSt S W K) (pid : PartyId) :
    Samples (ltP s pid : Prog E O _) (ltStep s pid) := by
  unfold ltP ltStep
  cases s.lt pid with
  | some l => exact Samples.ret _
  | none => exact Samples.sample_map _ _

omit [Inhabited K] in
/-- `roP` samples `roStep`. -/
theorem roP_samples {E O D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    Samples (roP tb x : Prog E O _) (roStep tb x) := by
  unfold roP roStep
  cases tb.lookup x with
  | some v => exact Samples.ret _
  | none => exact Samples.sample_map _ _

omit [Field S] [Fintype S] [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- `deliverP` samples `deliver`. -/
theorem deliverP_samples (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS))
    (x : Inst) (r : Rec K) (ip : PInp W SS) :
    Samples (deliverP s inp x r ip) (deliver s inp x r ip) := by
  unfold deliverP deliver
  exact Samples.ite ((roP_samples _ _).map _) (Samples.ret _)

omit [Countable PK] [Countable SK] in
/-- `simCompleteP` samples `simComplete`. -/
theorem simCompleteP_samples (s : SimSt S W K PK SK SS C) (x : Inst) :
    Samples (simCompleteP O G s x) (simComplete O G s x) := by
  unfold simCompleteP simComplete
  cases s.1.x.st.recs x with
  | none => exact Samples.ret _
  | some r =>
    cases s.1.x.eph x with
    | none => exact Samples.ret _
    | some ek =>
      dsimp only
      cases opkOf s.1.x x.1 r.peer with
      | none => exact Samples.ret _
      | some opk =>
        cases pkOf s.1 x.1 r.peer with
        | none => exact Samples.ret _
        | some pk =>
          exact Samples.ite ((ltP_samples _ _).bind fun _ => (ltP_samples _ _).bind fun _ =>
            Samples.sample fun _ => deliverP_samples _ _ _ _ _) (Samples.ret _)

omit [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- `simSendP` samples `simSend`. -/
theorem simSendP_samples (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    Samples (simSendP O G s x e c) (simSend O G s x e c) := by
  unfold simSendP simSend
  cases s.1.x.st.recs x with
  | none => exact Samples.ret _
  | some r =>
    cases s.1.x.eph x with
    | none => exact Samples.ret _
    | some opk =>
      cases s.1.kem x with
      | none => exact Samples.ret _
      | some kp =>
        dsimp only
        cases O.decaps kp.2 c with
        | none => exact Samples.ret _
        | some ss =>
          exact Samples.ite ((ltP_samples _ _).bind fun _ => (ltP_samples _ _).bind fun _ =>
            deliverP_samples _ _ _ _ _) (Samples.ret _)

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] [Countable PK]
  [Countable SK] [Countable SS] [Countable C] in
/-- `simCorruptP` samples `simCorrupt`. -/
theorem simCorruptP_samples (s : SimSt S W K PK SK SS C) (pid : PartyId) :
    Samples (simCorruptP s pid : P S W K PK SS C _) (simCorrupt s pid) := by
  unfold simCorruptP simCorrupt
  exact Samples.ite (Samples.ret _) ((ltP_samples _ _).map _)

/-- **`simStartP` samples `simStart`.** -/
theorem simStartP_samples (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    Samples (simStartP O G s e) (simStart O G s e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · exact Samples.ite (Samples.sample fun _ =>
      Samples.ite (Samples.sample_map _ _) (Samples.ret _)) (Samples.ret _)
  · exact Samples.ret _
  · exact Samples.ret _
  · exact Samples.ret _
  · exact (ltP_samples _ _).map _
  · exact Samples.ret _
  · exact Samples.ret _
  · exact simCorruptP_samples _ _
  · exact simCompleteP_samples O G _ _
  · exact simSendP_samples O G _ _ _ _
  · exact (roP_samples _ _).map _

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- The end of an activation in the emit phase is the embedded decision. -/
theorem emitK_simDecide (q : SimSt S W K PK SK SS C × Dec S W K PK C) :
    emitK (fun o p => SPComp.pure (p, o)) (fun _ => SPComp.fail) (simDecide q) =
      SPComp.pure (MultiHybrid.liftDec (fun s => .ret s) (fun s => callK (simK s)) q) := by
  rcases q with ⟨s, f | o⟩ <;> rfl

/-- **The PQXDH simulator and its program form are step-equivalent** over every subroutine, in
particular over `F_AKE`. -/
theorem simProtK_stepEq_simLoop {τ : Type} (X : Sys τ (FEv K) (FOut K)) :
    Sys.StepEq ⟨SimSt S W K PK SK SS C × τ, (simProtK O G).withSub X⟩
      ⟨P S W K PK SS C (SimSt S W K PK SK SS C) × τ, (simLoop O G).withSub X⟩ := by
  refine loopMulti_stepEq (simProtK O G) (simBody O G) id simK (fun s e => ?_)
    (fun s a => ?_) (fun s a => ?_) X
  · change emitK (fun o p => SPComp.pure (p, o)) (fun _ => SPComp.fail)
      (ProgE.bind (simStartP O G s e) simDecide) = _
    rw [(simStartP_samples O G s e).emitK_bind]
    simp only [emitK_simDecide, SPComp.map]
    rfl
  · simp only [simProtK, SPComp.map_pure]
    rfl
  · simp only [simProtK, SPComp.map_pure]
    rfl

/-! ## Opacity from information flow -/

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltP` neither receives nor sends. -/
theorem ltP_noIO {E O : Type} (s : RSt S W K) (pid : PartyId) :
    NoIO (ltP s pid : Prog E O _) := by
  unfold ltP
  split
  · exact ProgE.Ports.ret _
  · exact noIO_sample fun _ => ProgE.Ports.ret _

omit [Inhabited K] in
/-- `roP` neither receives nor sends. -/
theorem roP_noIO {E O D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    NoIO (roP tb x : Prog E O _) := by
  unfold roP
  split
  · exact ProgE.Ports.ret _
  · exact noIO_sample fun _ => ProgE.Ports.ret _

omit [Field S] [Fintype S] [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- `deliverP` neither receives nor sends. -/
theorem deliverP_noIO (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst)
    (r : Rec K) (ip : PInp W SS) : NoIO (deliverP s inp x r ip) := by
  unfold deliverP
  split
  · exact ProgE.Ports.bind (roP_noIO _ _) fun _ => ProgE.Ports.ret _
  · exact ProgE.Ports.ret _

omit [Countable PK] [Countable SK] in
/-- `simCompleteP` neither receives nor sends. -/
theorem simCompleteP_noIO (s : SimSt S W K PK SK SS C) (x : Inst) :
    NoIO (simCompleteP O G s x) := by
  unfold simCompleteP
  cases s.1.x.st.recs x with
  | none => exact ProgE.Ports.ret _
  | some r =>
    cases s.1.x.eph x with
    | none => exact ProgE.Ports.ret _
    | some ek =>
      dsimp only
      cases opkOf s.1.x x.1 r.peer with
      | none => exact ProgE.Ports.ret _
      | some opk =>
        cases pkOf s.1 x.1 r.peer with
        | none => exact ProgE.Ports.ret _
        | some pk =>
          dsimp only
          split
          · exact ProgE.Ports.bind (ltP_noIO _ _) fun _ => ProgE.Ports.bind (ltP_noIO _ _)
              fun _ => noIO_sample fun _ => deliverP_noIO _ _ _ _ _
          · exact ProgE.Ports.ret _

omit [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- `simSendP` neither receives nor sends. -/
theorem simSendP_noIO (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    NoIO (simSendP O G s x e c) := by
  unfold simSendP
  cases s.1.x.st.recs x with
  | none => exact ProgE.Ports.ret _
  | some r =>
    cases s.1.x.eph x with
    | none => exact ProgE.Ports.ret _
    | some opk =>
      cases s.1.kem x with
      | none => exact ProgE.Ports.ret _
      | some kp =>
        dsimp only
        cases O.decaps kp.2 c with
        | none => exact ProgE.Ports.ret _
        | some ss =>
          dsimp only
          split
          · exact ProgE.Ports.bind (ltP_noIO _ _) fun _ => ProgE.Ports.bind (ltP_noIO _ _)
              fun _ => deliverP_noIO _ _ _ _ _
          · exact ProgE.Ports.ret _

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] [Countable PK]
  [Countable SK] [Countable SS] [Countable C] in
/-- `simCorruptP` neither receives nor sends. -/
theorem simCorruptP_noIO (s : SimSt S W K PK SK SS C) (pid : PartyId) :
    NoIO (simCorruptP s pid : P S W K PK SS C _) := by
  unfold simCorruptP
  split
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.bind (ltP_noIO _ _) fun _ => ProgE.Ports.ret _

/-- `simStartP` neither receives nor sends. -/
theorem simStartP_noIO (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    NoIO (simStartP O G s e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · simp only [simStartP]
    split
    · refine noIO_sample fun _ => ?_
      split
      · exact noIO_sample fun _ => ProgE.Ports.ret _
      · exact ProgE.Ports.ret _
    · exact ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.bind (ltP_noIO _ _) fun _ => ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact ProgE.Ports.ret _
  · exact simCorruptP_noIO _ _
  · exact simCompleteP_noIO O G _ _
  · exact simSendP_noIO O G _ _ _ _
  · exact ProgE.Ports.bind (roP_noIO _ _) fun _ => ProgE.Ports.ret _

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- The end of an activation is related to itself: answers of `F_AKE` related by the view of
`F_AKE` give related outputs (`simOut_rel`). -/
theorem simDecide_viewRel (q : SimSt S W K PK SK SS C × Dec S W K PK C) :
    ProgE.ViewRel (PubView.callView (outerView (SS := SS)) subView) Eq (simDecide q)
      (simDecide q) := by
  rcases q with ⟨s, f | o⟩
  · refine ProgE.ViewRel.send (stepRel_refl (SS := SS) (.inl f : Dec S W K PK C))
      (ProgE.ViewRel.recv fun x x' hx => ?_)
    cases hx with
    | inl _ => exact ProgE.ViewRel.fail
    | inr ha => exact ProgE.ViewRel.send (simOut_rel s.2.2 ha) (ProgE.ViewRel.ret rfl)
  · exact ProgE.ViewRel.send (stepRel_refl (SS := SS) (.inr o)) (ProgE.ViewRel.ret rfl)

/-- The PQXDH simulator program is related to itself for the view of its sum interface. -/
theorem simBody_viewRel (s : SimSt S W K PK SK SS C) :
    ProgE.ViewRel (PubView.callView outerView subView) Eq (simBody O G s) (simBody O G s) := by
  unfold simBody
  refine ProgE.ViewRel.bind (RA := Eq) ?_ fun e e' he => ?_
  · refine ProgE.ViewRel.recv fun x x' hx => ?_
    cases hx with
    | @inl a b h =>
      have h' : a = b := by
        cases h with
        | inl h => exact congrArg Sum.inl h
        | inr h => exact congrArg Sum.inr h
      subst h'
      exact ProgE.ViewRel.ret rfl
    | inr _ => exact ProgE.ViewRel.fail
  · subst he
    refine ProgE.ViewRel.bind
      (ProgE.ViewRel.refl_of_ports (fun _ => rfl) (simStartP_noIO O G s e)) fun q q' hq => ?_
    subst hq
    exact simDecide_viewRel q

/-- **The unwinding condition of the PQXDH simulator program**: information flow of the loop of
`simBody` for the view of the sum interface is an unwinding relation of `simLoop`. -/
theorem simLoop_unwinding :
    (simLoop (K := K) O G).Unwinding outerView subView
      (ProgE.ViewRel (PubView.callView outerView subView) Eq) :=
  MultiHybrid.unwinding_ofSys
    (loopSys_unwinding (simBody O G) _ rfl fun s _ hs => hs ▸ simBody_viewRel O G s)
    (stepRel_refl (SS := SS) (.inr default : Dec S W K PK C)) 0

/-- **Opacity of the PQXDH simulator program**: it reads no key of `F_AKE`. -/
theorem simLoop_opaque : (simLoop (K := K) O G).Opaque outerView subView :=
  ⟨_, simLoop_unwinding O G⟩

/-- **The PQXDH simulator program over the KEM operations `O`** as a bundled opaque
simulator. -/
noncomputable def pqxdhSimKP :
    Simulator (OEv W SS C) (OOut S W K PK C) (FEv K) (FOut K) outerView subView :=
  Simulator.ofMultiHybrid (simLoop O G) (simLoop_opaque O G)

/-! ## Time certificate -/

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltP` takes one unit. -/
theorem ltP_bound {E O : Type} (s : RSt S W K) (pid : PartyId) :
    ProgE.Bound (fun _ => 1) (ltP s pid : Prog E O _) 1 (fun _ => True) := by
  unfold ltP
  split
  · trivial
  · exact X3DHProg.bound_sample le_rfl fun _ => trivial

omit [Inhabited K] in
/-- `roP` takes one unit and grows the table by at most one entry. -/
theorem roP_bound {E O D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    ProgE.Bound (fun _ => 1) (roP tb x : Prog E O _) 1
      (fun r => r.2.length ≤ tb.length + 1) := by
  unfold roP
  split
  · simp [ProgE.Bound]
  · exact X3DHProg.bound_sample le_rfl fun _ => by simp [ProgE.Bound]

omit [Field S] [Fintype S] [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- `deliverP` takes one unit and grows the table by at most one entry. -/
theorem deliverP_bound (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst)
    (r : Rec K) (ip : PInp W SS) :
    ProgE.Bound (fun _ => 1) (deliverP s inp x r ip) 1
      (fun q => q.1.1.ro.length ≤ s.ro.length + 1) := by
  unfold deliverP
  split
  · refine ProgE.Bound.bind (t := 1) (u := 0) ((roP_bound s.ro ip).mono le_rfl fun p hp => ?_)
    simpa [ProgE.Bound, pKeyed] using hp
  · simp [ProgE.Bound, pKeyed]

omit [Countable PK] [Countable SK] in
/-- `simCompleteP` takes at most four units and grows the table by at most one entry. -/
theorem simCompleteP_bound (s : SimSt S W K PK SK SS C) (x : Inst) :
    ProgE.Bound (fun _ => 1) (simCompleteP O G s x) 4
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  unfold simCompleteP
  cases s.1.x.st.recs x with
  | none => simp [ProgE.Bound]
  | some r =>
    cases s.1.x.eph x with
    | none => simp [ProgE.Bound]
    | some ek =>
      dsimp only
      cases opkOf s.1.x x.1 r.peer with
      | none => simp [ProgE.Bound]
      | some opk =>
        cases pkOf s.1 x.1 r.peer with
        | none => simp [ProgE.Bound]
        | some pk =>
          dsimp only
          split
          · refine ProgE.Bound.bind (t := 1) (u := 3) ((ltP_bound _ _).mono le_rfl fun _ _ => ?_)
            refine ProgE.Bound.bind (t := 1) (u := 2) ((ltP_bound _ _).mono le_rfl fun _ _ => ?_)
            exact X3DHProg.bound_sample (by omega) fun _ =>
              (deliverP_bound _ _ _ _ _).mono le_rfl fun _ hq => hq
          · simp [ProgE.Bound]

omit [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- `simSendP` takes at most three units and grows the table by at most one entry. -/
theorem simSendP_bound (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    ProgE.Bound (fun _ => 1) (simSendP O G s x e c) 3
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  unfold simSendP
  cases s.1.x.st.recs x with
  | none => simp [ProgE.Bound]
  | some r =>
    cases s.1.x.eph x with
    | none => simp [ProgE.Bound]
    | some opk =>
      cases s.1.kem x with
      | none => simp [ProgE.Bound]
      | some kp =>
        dsimp only
        cases O.decaps kp.2 c with
        | none => simp [ProgE.Bound]
        | some ss =>
          dsimp only
          split
          · refine ProgE.Bound.bind (t := 1) (u := 2) ((ltP_bound _ _).mono le_rfl fun _ _ => ?_)
            refine ProgE.Bound.bind (t := 1) (u := 1) ((ltP_bound _ _).mono le_rfl fun _ _ => ?_)
            exact (deliverP_bound _ _ _ _ _).mono le_rfl fun _ hq => hq
          · simp [ProgE.Bound]

/-- `simStartP` takes at most four units and grows the table by at most one entry. -/
theorem simStartP_bound (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    ProgE.Bound (fun _ => 1) (simStartP O G s e) 4
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · simp only [simStartP]
    split
    · refine X3DHProg.bound_sample (by omega) fun _ => ?_
      split
      · exact X3DHProg.bound_sample (by omega) fun _ => by simp [ProgE.Bound]
      · simp [ProgE.Bound]
    · simp [ProgE.Bound]
  · simp [simStartP, ProgE.Bound]
  · simp [simStartP, ProgE.Bound]
  · simp [simStartP, ProgE.Bound]
  · simp only [simStartP]
    refine ProgE.Bound.bind (t := 1) (u := 3) ((ltP_bound _ _).mono le_rfl fun _ _ => ?_)
    simp [ProgE.Bound]
  · simp [simStartP, ProgE.Bound]
  · simp [simStartP, ProgE.Bound]
  · simp only [simStartP, simCorruptP]
    split
    · simp [ProgE.Bound]
    · refine ProgE.Bound.bind (t := 1) (u := 3) ((ltP_bound _ _).mono le_rfl fun _ _ => ?_)
      simp [ProgE.Bound]
  · exact simCompleteP_bound O G s (sid, pid)
  · exact (simSendP_bound O G s (sid, pid) e c).mono (by omega) fun _ h => h
  · simp only [simStartP]
    refine ProgE.Bound.bind (t := 1) (u := 3) ((roP_bound _ _).mono le_rfl fun p hp => ?_)
    simpa [ProgE.Bound] using hp

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS] [Countable C] in
/-- `simDecide` takes at most three units and keeps the table. -/
theorem simDecide_bound (q : SimSt S W K PK SK SS C × Dec S W K PK C) :
    ProgE.Bound (fun _ => 1) (simDecide q) 3 (fun s => s.1.ro = q.1.1.ro) := by
  unfold simDecide
  split
  · simp [call, callK, simK, outE, ProgE.Bound, ProgE.bind]
  · simp [outE, ProgE.Bound, ProgE.bind]

/-- An iteration of the PQXDH simulator program takes at most eight units and grows the
key-derivation table by at most one entry. -/
theorem simBody_bound (s : SimSt S W K PK SK SS C) :
    ProgE.Bound (fun _ => 1) (simBody O G s) 8
      (fun s' => s'.1.ro.length ≤ s.1.ro.length + 1) := by
  unfold simBody
  refine ProgE.Bound.bind (t := 1) (u := 7) (X3DHProg.bound_recvO fun e => ?_)
  refine ProgE.Bound.bind (t := 4) (u := 3)
    ((simStartP_bound O G s e).mono le_rfl fun q hq => ?_)
  exact (simDecide_bound q).mono le_rfl fun s' hs' => by rw [hs']; exact hq

/-- **The costed form of the PQXDH simulator program**: an iteration from `s` charges the length
of the key-derivation table, the cost of a lookup in it, before the unit-cost form of
`simBody`. -/
noncomputable def simBodyT : SimSt S W K PK SK SS C → ProgE (Costed (SPComp ℕ))
    (OEv W SS C ⊕ FOut K) (FEv K ⊕ OOut S W K PK C) (SimSt S W K PK SK SS C) :=
  ProgE.priced (fun s => s.1.ro.length) (simBody O G)

/-- The costed form of the PQXDH simulator program erases to `simBody`. -/
theorem simBodyT_erase (s : SimSt S W K PK SK SS C) :
    ProgE.erase (simBodyT O G s) = simBody O G s :=
  ProgE.erase_priced _ _ s

/-- **Time certificate of the PQXDH simulator program.** After `i` iterations the key-derivation
table holds at most `i` entries, and the `i`-th iteration costs at most `8 + i`. -/
theorem simBodyT_loopBoundGraded :
    ProgE.LoopBoundGraded Costed.weight (simBodyT O G)
      ((pInit, fun _ => none, .fwd) : SimSt S W K PK SK SS C) (fun i s => s.1.ro.length ≤ i)
      8 1 :=
  ProgE.priced_loopBoundGraded (fun s : SimSt S W K PK SK SS C => s.1.ro.length) (simBody O G)
    _ (fun i s => s.1.ro.length ≤ i) 8 1 0 (by simp [pInit]) (fun i s hs => by omega)
    (fun i s hs => (simBody_bound O G s).mono le_rfl fun s' hs' => by omega)

/-- **Time of the PQXDH simulator program**: the first `q` iterations of its costed form cost at
most `8 q + q (q - 1) / 2`, and the key-derivation table then holds at most `q` entries. -/
theorem simLoop_time (q : ℕ) :
    ProgE.Bound Costed.weight
      (ProgE.iterate (simBodyT O G) q ((pInit, fun _ => none, .fwd) : SimSt S W K PK SK SS C))
      (q * 8 + 1 * (q * (q - 1) / 2)) (fun s => s.1.ro.length ≤ q) :=
  (simBodyT_loopBoundGraded O G).iterate_time_le q

end Prog

/-! ## The square through the program simulator -/

section SimWorld

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS]
  [Countable C] (Pk : KEM.Games.Scheme PK SK SS C) (G : DHGroup S W)

/-- **The PQXDH simulator program** for the KEM `Pk`: `pqxdhSimKP` at the operations
`kemOps Pk`. -/
noncomputable def pqxdhSimP :
    Simulator (OEv W SS C) (OOut S W K PK C) (FEv K) (FOut K) outerView subView :=
  pqxdhSimKP (kemOps Pk) G

/-- **PQXDH realizes `F_AKE` behind the program simulator.** For every environment `Z`, the
distance between the real PQXDH protocol and the simulator program running with `F_AKE` is at
most the advantage of `OProt.oracle.reduction Z` between `realGame Pk G` and `simGame Pk G`. -/
theorem pqxdh_realizesSim_prog :
    RealizesSim (pqxdhReal (K := K) Pk G) (F_AKE (SPComp.sample K) true) (pqxdhSimP Pk G)
      (fun _ Z => KeyedGame.advantage (realGame Pk G) (simGame Pk G)
        (OProt.oracle.reduction Z)) :=
  fun ζ Z => le_of_le_of_eq (((pqxdh_realizesSim_oracleGame Pk G).trans
    (Sys.StepEq.realizes
      (simProtK_stepEq_simLoop (kemOps Pk) G (F_AKE (SPComp.sample K) true))).1) ζ Z)
    (add_zero _)

end SimWorld

end CatCrypt.Crypto.Party.Protocols.PQXDH

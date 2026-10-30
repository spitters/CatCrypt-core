/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.FAKESys
public import CatCryptCore.Crypto.PAKE.CPaceSquare

/-!
# X3DH against the authenticated key-exchange functionality

**Ideal functionality.** `F_AKE (SPComp.sample K)` of `CatCryptCore.Crypto.AKE.FAKESys`: the
multi-session authenticated key exchange of Canetti and Krawczyk with adversarial key delivery
and corruption of parties, with uniform keys in `K`. Its adversary port has the unlinked
delivery `newKeyUnlinked`, which gives a session a key independent of its partner's: an attacker
that replaces the initiator's ephemeral key on its way to the responder causes the two to derive
different keys. Corruption in `F_AKE` is adaptive; the real protocol and the simulator use it
statically.

**Real protocol.** `x3dhReal G` runs X3DH (Marlinspike and Perrin, *The X3DH Key Agreement
Protocol*, 2016) for every session, over the group `G : DHGroup S W` and with the key-derivation
function a lazily sampled random function into `K`. The variant:
* every party `p` has an identity key `ik` and a signed prekey `spk`, sampled at their first
  use; their public parts are read on the adversary port (`pub p`) and are authentic: a party
  uses the public keys of its peer as registered, so the signature on the prekey is not
  modelled;
* a session of the responder `b` in `sid` draws a one-time prekey `opk` at its start, and a
  session of the initiator `a` an ephemeral key `ek`; their public parts are read with
  `ephPub sid p`;
* the initiator completes on `complete sid a`, once its peer `b` has a responder session in
  `sid`, with the key `KDF(sid, a, b, DH1, DH2, DH3, DH4)` where `DH1 = SPK_b^{ik_a}`,
  `DH2 = IK_b^{ek}`, `DH3 = SPK_b^{ek}`, `DH4 = OPK_b^{ek}` (`aliceInp`);
* the responder completes on `send sid b E`, the delivery of the ephemeral public key `E`, with
  the key `KDF(sid, a, b, IK_a^{spk_b}, E^{ik_b}, E^{spk_b}, E^{opk_b})` (`bobInp`);
* corruption is static: `corrupt p` reveals the long-term secrets of `p` and marks it corrupt
  when no session names `p`, and is refused otherwise;
* `kdf x` queries the key-derivation function.

The initiator's and the responder's inputs agree when the responder receives the initiator's
ephemeral key (`aliceInp_eq_bobInp`), so partners derive the same key.

**Simulator.** `x3dhSim G` keeps a copy of the real state: the honest events carry no secret, so
it draws every long-term and session secret itself, forwards the honest events to `F_AKE`, and
answers `poll`, `pub`, `ephPub` and `kdf` as the real protocol does on its copy. On `corrupt p`
it corrupts `p` in `F_AKE` under the same static rule. When a session completes it computes the
session's key-derivation input `ip` (`deliver`):
* for an exposed session (its party or its peer corrupt), it samples the key derivation at `ip`
  and passes the value to `newKey`, which `F_AKE` delivers;
* otherwise it leaves the key-derivation table unchanged and calls `newKey` when the partner has
  not completed or completed with the input `ip`, and `newKeyUnlinked` otherwise; `F_AKE`
  delivers a uniform key or the partner's.
The simulator reads no key of `F_AKE` (`simProt_opaque`).

**Results.** The simulator running with `F_AKE` is a system whose steps do not read the heap; it
is at distance `0` from the oracle system of the game `simGame G` (`simWorld_realizes`). The
square is the oracle-game bound `x3dh_realizesSim_oracleGame`: `x3dhReal G` realizes `F_AKE`
behind `x3dhSim G` with bound, at the environment `Z`, the advantage of the oracle adversary
`OProt.oracle.reduction Z` between `realGame G` and `simGame G`.

## Main definitions

* `Inp`, `aliceInp`, `bobInp`: the inputs of the key derivation.
* `RSt`, `RAEv`, `ROut`: the state and the adversary port of the real protocol.
* `realGame`, `x3dhReal`: the real protocol as an oracle game and as a system.
* `simStart`: the start of an activation of the simulator, a computation over uniform draws of
  the secrets and of the key-derivation values (`ltStep`, `roStep`, `deliver`).
* `simProt`, `x3dhSim`: the simulator.
* `simGame`: the oracle game of the simulated world.

## Main results

* `aliceInp_eq_bobInp`: the two sides of an unmodified exchange derive from the same input.
* `simProt_opaque`: opacity of the simulator.
* `F_AKE_pureNF`, `simWorld_realizes`.
* `x3dh_realizesSim_oracleGame`: X3DH realizes `F_AKE` behind `x3dhSim` with the oracle-game
  bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt PureNF pureNF_pure pureNF_sample PureNF.map PureNF.bind
  withSub_pureNF pureGame pureGame_realizes)
open PubView (eqView)
open scoped ENNReal

/-! ## Inputs of the key derivation -/

/-- An input of the key derivation: the session, the initiator, the responder, and the four
Diffie–Hellman values. -/
structure Inp (W : Type) where
  /-- The session. -/
  sid : SessionId
  /-- The initiator. -/
  ini : PartyId
  /-- The responder. -/
  res : PartyId
  /-- `DH1`, between the initiator's identity key and the responder's signed prekey. -/
  dh1 : W
  /-- `DH2`, between the initiator's ephemeral key and the responder's identity key. -/
  dh2 : W
  /-- `DH3`, between the initiator's ephemeral key and the responder's signed prekey. -/
  dh3 : W
  /-- `DH4`, between the initiator's ephemeral key and the responder's one-time prekey. -/
  dh4 : W
  deriving DecidableEq

section Inputs

variable {S W : Type} [Field S] (G : DHGroup S W)

/-- The input of the initiator `a` with identity secret `ik` and ephemeral secret `ek`, for the
responder `b` with public identity key `IKB`, signed prekey `SPKB` and one-time prekey
`OPKB`. -/
def aliceInp (sid : SessionId) (a b : PartyId) (ik ek : S) (IKB SPKB OPKB : W) : Inp W :=
  ⟨sid, a, b, G.exp SPKB ik, G.exp IKB ek, G.exp SPKB ek, G.exp OPKB ek⟩

/-- The input of the responder `b` with identity secret `ik`, signed-prekey secret `spk` and
one-time-prekey secret `opk`, for the initiator `a` with public identity key `IKA`, on the
ephemeral public key `E`. -/
def bobInp (sid : SessionId) (a b : PartyId) (IKA E : W) (ik spk opk : S) : Inp W :=
  ⟨sid, a, b, G.exp IKA spk, G.exp E ik, G.exp E spk, G.exp E opk⟩

/-- **Agreement of an unmodified exchange.** The responder that receives the initiator's
ephemeral public key derives from the initiator's input. -/
theorem aliceInp_eq_bobInp (sid : SessionId) (a b : PartyId) (ikA ek ikB spkB opkB : S) :
    aliceInp G sid a b ikA ek (G.pub ikB) (G.pub spkB) (G.pub opkB) =
      bobInp G sid a b (G.pub ikA) (G.pub ek) ikB spkB opkB := by
  simp only [aliceInp, bobInp, G.exp_pub, mul_comm]

end Inputs

/-! ## The real protocol -/

/-- The state of the real protocol: the session records, corrupt parties and notices as in
`F_AKE`, the long-term secrets `(ik, spk)` of the parties, the session secrets (`ek` of an
initiator, `opk` of a responder), and the table of the key derivation. -/
structure RSt (S W K : Type) where
  /-- Session records, corrupt parties and notices. -/
  st : St K
  /-- The long-term secrets of a party, once sampled. -/
  lt : PartyId → Option (S × S)
  /-- The secret of a session. -/
  eph : Inst → Option S
  /-- The table of the key derivation. -/
  ro : List (Inp W × K)

/-- Events of the adversary port of the real protocol. -/
inductive RAEv (W : Type) where
  /-- No action. -/
  | idle
  /-- Read the next notice of a new session. -/
  | poll
  /-- Read the public identity key and signed prekey of a party. -/
  | pub (pid : PartyId)
  /-- Read the public session key of the party `pid` in `sid`. -/
  | ephPub (sid : SessionId) (pid : PartyId)
  /-- Corrupt the party `pid`. -/
  | corrupt (pid : PartyId)
  /-- Let the initiator `pid` of `sid` complete. -/
  | complete (sid : SessionId) (pid : PartyId)
  /-- Deliver the ephemeral public key `e` to the responder `pid` of `sid`. -/
  | send (sid : SessionId) (pid : PartyId) (e : W)
  /-- Query the key derivation at `x`. -/
  | kdf (x : Inp W)

/-- Outputs of the adversary port of the real protocol. -/
inductive ROut (S W K : Type) where
  /-- Acknowledgement. -/
  | ack
  /-- The next notice, if any. -/
  | notice (o : Option Notice)
  /-- The public identity key and signed prekey of a party. -/
  | pub (ik spk : W)
  /-- The public session key of a session, if any. -/
  | eph (o : Option W)
  /-- The long-term secrets of a corrupted party, or `none` when the corruption is refused. -/
  | secret (o : Option (S × S))
  /-- An answer of the key derivation. -/
  | hash (k : K)

section Real

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K]

/-- The long-term secrets of the party `pid`, sampled at their first use. -/
noncomputable def ltAt (s : RSt S W K) (pid : PartyId) : PMF ((S × S) × RSt S W K) :=
  match s.lt pid with
  | some l => PMF.pure (l, s)
  | none => (PMF.uniformFintype (S × S)).map fun l =>
      (l, { s with lt := Function.update s.lt pid (some l) })

/-- Whether a session names the party `pid`, as party or as peer. -/
def Named (t : St K) (pid : PartyId) : Bool :=
  t.notices.any fun n => n.pid == pid || n.peer == pid

/-- The state with the key `k` and the table `ro` at the session `x` with record `r`. -/
def keyed (s : RSt S W K) (x : Inst) (r : Rec K) (k : K) (ro : List (Inp W × K)) :
    RSt S W K :=
  { s with st := setRec s.st x { r with key := some k }, ro := ro }

/-- A step of the honest port of the real protocol: a new session draws its secret. -/
noncomputable def realHon (s : RSt S W K) : HEv → PMF (HOut K × RSt S W K)
  | .newSession sid pid peer role =>
    if (s.st.recs (sid, pid)).isNone then
      (PMF.uniformFintype S).map fun y =>
        (.ok, { s with st := addSession s.st (sid, pid) peer role,
                       eph := Function.update s.eph (sid, pid) (some y) })
    else PMF.pure (.ok, s)
  | .getKey sid pid => PMF.pure (.key (keyOf s.st (sid, pid)), s)

variable (G : DHGroup S W)

/-- The public session key of the session `x`. -/
def ephPubOf (s : RSt S W K) (x : Inst) : Option W := (s.eph x).map G.pub

/-- The one-time prekey of the responder `b` in `sid`, if `b` has a responder session there. -/
def opkOf (s : RSt S W K) (sid : SessionId) (b : PartyId) : Option S :=
  match s.st.recs (sid, b) with
  | some p => if p.role = .responder then s.eph (sid, b) else none
  | none => none

/-- The completion of the initiator session `x = (sid, a)`: its key is the key derivation at
`aliceInp`. -/
noncomputable def completeStep (s : RSt S W K) (x : Inst) : PMF (ROut S W K × RSt S W K) :=
  match s.st.recs x, s.eph x with
  | some r, some ek =>
    match opkOf s x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        (ltAt s x.2).bind fun la => (ltAt la.2 r.peer).bind fun lb =>
          (roAt lb.2.ro (aliceInp G x.1 x.2 r.peer la.1.1 ek (G.pub lb.1.1) (G.pub lb.1.2)
            (G.pub opk))).map fun p => (.ack, keyed lb.2 x r p.1 p.2)
      else PMF.pure (.ack, s)
    | none => PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- The completion of the responder session `x = (sid, b)` on the ephemeral public key `e`: its
key is the key derivation at `bobInp`. -/
noncomputable def sendStep (s : RSt S W K) (x : Inst) (e : W) : PMF (ROut S W K × RSt S W K) :=
  match s.st.recs x, s.eph x with
  | some r, some opk =>
    if r.role = .responder ∧ r.key.isNone then
      (ltAt s x.2).bind fun lb => (ltAt lb.2 r.peer).bind fun la =>
        (roAt la.2.ro (bobInp G x.1 r.peer x.2 (G.pub la.1.1) e lb.1.1 lb.1.2 opk)).map fun p =>
          (.ack, keyed la.2 x r p.1 p.2)
    else PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- `corrupt pid`: the long-term secrets of `pid` and the mark, when no session names `pid`. -/
noncomputable def corruptRStep (s : RSt S W K) (pid : PartyId) :
    PMF (ROut S W K × RSt S W K) :=
  if Named s.st pid then PMF.pure (.secret none, s) else
    (ltAt s pid).map fun l => (.secret (some l.1), { l.2 with st := corruptStep l.2.st pid })

/-- A step of the adversary port of the real protocol. -/
noncomputable def realAdv (s : RSt S W K) : RAEv W → PMF (ROut S W K × RSt S W K)
  | .idle => PMF.pure (.ack, s)
  | .poll => PMF.pure (.notice (pollStep s.st).2, { s with st := (pollStep s.st).1 })
  | .pub pid => (ltAt s pid).map fun l => (.pub (G.pub l.1.1) (G.pub l.1.2), l.2)
  | .ephPub sid pid => PMF.pure (.eph (ephPubOf G s (sid, pid)), s)
  | .corrupt pid => corruptRStep s pid
  | .complete sid pid => completeStep G s (sid, pid)
  | .send sid pid e => sendStep G s (sid, pid) e
  | .kdf x => (roAt s.ro x).map fun p => (.hash p.1, { s with ro := p.2 })

/-- The initial state of the real protocol. -/
def rInit : RSt S W K := ⟨initSt, fun _ => none, fun _ => none, []⟩

/-- **The real X3DH game**: a trivial key, and the oracle is the step of the real protocol. -/
noncomputable def realGame : KeyedGame (HEv ⊕ RAEv W) (HOut K ⊕ ROut S W K) where
  Key := Unit
  State := RSt S W K
  keyDist := PMF.pure ()
  oracle _ s
    | .inl h => (realHon s h).map fun p => (.inl p.1, p.2)
    | .inr a => (realAdv G s a).map fun p => (.inr p.1, p.2)
  init := rInit

/-- **The real X3DH protocol** as a system: each event is a query to the oracle of
`realGame G`. -/
noncomputable def x3dhReal :=
  (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys (realGame G)

end Real

/-! ## The simulator -/

/-- The phase of the simulator within an activation. -/
inductive Phase (S W K : Type) where
  /-- Forward the answer of `F_AKE` on its honest port. -/
  | fwd
  /-- Output `o` after the call to `F_AKE`. -/
  | out (o : ROut S W K)

/-- The state of the simulator: its copy of the real state, the key-derivation input of each
session it completed, and the phase. -/
abbrev SimSt (S W K : Type) := RSt S W K × (Inst → Option (Inp W)) × Phase S W K

/-- The outer events of the simulator: the interface of the real protocol. -/
abbrev OEv (W : Type) := HEv ⊕ RAEv W

/-- The outer outputs of the simulator. -/
abbrev OOut (S W K : Type) := HOut K ⊕ ROut S W K

/-- The events of `F_AKE`. -/
abbrev FEv (K : Type) := HEv ⊕ AEv K

/-- The outputs of `F_AKE`. -/
abbrev FOut (K : Type) := HOut K ⊕ AOut

/-- A decision of the simulator. -/
abbrev Dec (S W K : Type) := FEv K ⊕ OOut S W K

/-- The simulator's answer to an answer of `F_AKE`: in the phase `fwd`, the answer on the
honest port, and an acknowledgement for an answer on the adversary port; otherwise the
stored output otherwise. -/
def simOut {S W K : Type} : Phase S W K → FOut K → OOut S W K
  | .fwd, .inl o => .inl o
  | .fwd, .inr _ => .inr .ack
  | .out r, _ => .inr r

section Sim

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The long-term secrets of the party `pid` on the simulator's copy, as in `ltAt`: the
recorded pair, or a uniform pair that is recorded. -/
noncomputable def ltStep (s : RSt S W K) (pid : PartyId) : SPComp ((S × S) × RSt S W K) :=
  match s.lt pid with
  | some l => SPComp.pure (l, s)
  | none => SPComp.map (fun l => (l, { s with lt := Function.update s.lt pid (some l) }))
      (SPComp.sample (S × S))

/-- The key derivation on the simulator's copy of the table `tb` at `x`, as in `roAt`: the
recorded value, or a uniform value that is recorded. -/
noncomputable def roStep (tb : List (Inp W × K)) (x : Inp W) : SPComp (K × List (Inp W × K)) :=
  match tb.lookup x with
  | some v => SPComp.pure (v, tb)
  | none => SPComp.map (fun v => (v, (x, v) :: tb)) (SPComp.sample K)

/-- The delivery of the key of the session `x` with record `r` and input `ip`. An exposed session
receives the key-derivation value at `ip`, which the simulator samples and passes to `newKey`.
Any other session receives the key of `F_AKE`: `newKey` when its partner has not completed or
completed with the same input, `newKeyUnlinked` otherwise; the key-derivation table is
unchanged. -/
noncomputable def deliver (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) : SPComp (SimSt S W K × Dec S W K) :=
  if Exposed rs.st x r then
    SPComp.map (fun p => ((keyed rs x r p.1 p.2, Function.update inp x (some ip), .out .ack),
        .inl (.inr (.newKey x.1 x.2 p.1)))) (roStep rs.ro ip)
  else
    SPComp.pure ((keyed rs x r default rs.ro, Function.update inp x (some ip), .out .ack),
      .inl (.inr (if (inp (x.1, r.peer)).all (· = ip) then .newKey x.1 x.2 default
        else .newKeyUnlinked x.1 x.2 default)))

/-- The simulator on `complete sid pid`: the computation of `completeStep` on its copy, and the
delivery by `deliver`. -/
noncomputable def simComplete (s : SimSt S W K) (x : Inst) :
    SPComp (SimSt S W K × Dec S W K) :=
  match s.1.st.recs x, s.1.eph x with
  | some r, some ek =>
    match opkOf s.1 x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        SPComp.bind (ltStep s.1 x.2) fun la => SPComp.bind (ltStep la.2 r.peer) fun lb =>
          deliver lb.2 s.2.1 x r
            (aliceInp G x.1 x.2 r.peer la.1.1 ek (G.pub lb.1.1) (G.pub lb.1.2) (G.pub opk))
      else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
    | none => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- The simulator on `send sid pid e`: the computation of `sendStep` on its copy, and the
delivery by `deliver`. -/
noncomputable def simSend (s : SimSt S W K) (x : Inst) (e : W) :
    SPComp (SimSt S W K × Dec S W K) :=
  match s.1.st.recs x, s.1.eph x with
  | some r, some opk =>
    if r.role = .responder ∧ r.key.isNone then
      SPComp.bind (ltStep s.1 x.2) fun lb => SPComp.bind (ltStep lb.2 r.peer) fun la =>
        deliver la.2 s.2.1 x r (bobInp G x.1 r.peer x.2 (G.pub la.1.1) e lb.1.1 lb.1.2 opk)
    else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- The simulator on `corrupt pid`: refused as in the real protocol when a session names `pid`;
otherwise the secrets of its copy are output and `pid` is corrupted in `F_AKE`. -/
noncomputable def simCorrupt (s : SimSt S W K) (pid : PartyId) :
    SPComp (SimSt S W K × Dec S W K) :=
  if Named s.1.st pid then SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.secret none))) else
    SPComp.map (fun l =>
      (({ l.2 with st := corruptStep l.2.st pid }, s.2.1, .out (.secret (some l.1))),
        .inl (.inr (.corrupt pid)))) (ltStep s.1 pid)

/-- The start of an activation of the simulator. Honest events go to `F_AKE` and update the
copy as `realHon` does (a new session draws its secret); `complete`, `send` and `corrupt` are
handled as above; every other adversary event is answered as `realAdv` does on the copy. -/
noncomputable def simStart (s : SimSt S W K) : OEv W → SPComp (SimSt S W K × Dec S W K)
  | .inl (.newSession sid pid peer role) =>
    if (s.1.st.recs (sid, pid)).isNone then
      SPComp.map (fun y =>
        (({ s.1 with st := addSession s.1.st (sid, pid) peer role,
                     eph := Function.update s.1.eph (sid, pid) (some y) }, s.2.1, .fwd),
          .inl (.inl (.newSession sid pid peer role)))) (SPComp.sample S)
    else SPComp.pure ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => SPComp.pure ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | .inr .poll => SPComp.pure (({ s.1 with st := (pollStep s.1.st).1 }, s.2.1, .fwd),
      .inr (.inr (.notice (pollStep s.1.st).2)))
  | .inr (.pub pid) => SPComp.map (fun l =>
      ((l.2, s.2.1, .fwd), .inr (.inr (.pub (G.pub l.1.1) (G.pub l.1.2))))) (ltStep s.1 pid)
  | .inr (.ephPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.eph (ephPubOf G s.1 (sid, pid)))))
  | .inr (.corrupt pid) => simCorrupt s pid
  | .inr (.complete sid pid) => simComplete G s (sid, pid)
  | .inr (.send sid pid e) => simSend G s (sid, pid) e
  | .inr (.kdf x) => SPComp.map (fun p =>
      (({ s.1 with ro := p.2 }, s.2.1, .fwd), .inr (.inr (.hash p.1)))) (roStep s.1.ro x)

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltStep` neither touches the heap nor fails. -/
theorem ltStep_pureNF (s : RSt S W K) (pid : PartyId) : PureNF (ltStep s pid) := by
  unfold ltStep
  split
  · exact pureNF_pure _
  · exact (pureNF_sample _).map _

omit [Inhabited K] in
/-- `roStep` neither touches the heap nor fails. -/
theorem roStep_pureNF (tb : List (Inp W × K)) (x : Inp W) : PureNF (roStep tb x) := by
  unfold roStep
  split
  · exact pureNF_pure _
  · exact (pureNF_sample _).map _

omit [Field S] [Fintype S] in
/-- `deliver` neither touches the heap nor fails. -/
theorem deliver_pureNF (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) : PureNF (deliver rs inp x r ip) := by
  unfold deliver
  split
  · exact (roStep_pureNF _ _).map _
  · exact pureNF_pure _

/-- The start of the simulator neither touches the heap nor fails. -/
theorem simStart_pureNF (s : SimSt S W K) (e : OEv W) : PureNF (simStart G s e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · simp only [simStart]
    split
    · exact (pureNF_sample _).map _
    · exact pureNF_pure _
  · exact pureNF_pure _
  · exact pureNF_pure _
  · exact pureNF_pure _
  · exact (ltStep_pureNF _ _).map _
  · exact pureNF_pure _
  · simp only [simStart, simCorrupt]
    split
    · exact pureNF_pure _
    · exact (ltStep_pureNF _ _).map _
  · simp only [simStart, simComplete]
    repeat' split
    all_goals first
      | exact pureNF_pure _
      | exact (ltStep_pureNF _ _).bind fun _ => (ltStep_pureNF _ _).bind fun _ =>
          deliver_pureNF _ _ _ _ _
  · simp only [simStart, simSend]
    repeat' split
    all_goals first
      | exact pureNF_pure _
      | exact (ltStep_pureNF _ _).bind fun _ => (ltStep_pureNF _ _).bind fun _ =>
          deliver_pureNF _ _ _ _ _
  · exact (roStep_pureNF _ _).map _

/-- **The X3DH simulator** as a multi-call simulator over `F_AKE`, one call per activation. -/
noncomputable def simProt :
    MultiHybrid (SimSt S W K) (OEv W) (OOut S W K) (FEv K) (FOut K) where
  init := (rInit, fun _ => none, .fwd)
  fuel := 0
  start := simStart G
  resume s o := SPComp.pure ((s.1, s.2.1, .fwd), .inr (simOut s.2.2 o))
  finish s o := SPComp.pure ((s.1, s.2.1, .fwd), simOut s.2.2 o)
  start_noFail s e := (simStart_pureNF G s e).2
  resume_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  finish_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _

end Sim

/-! ## Opacity of the simulator -/

/-- The view of the real interface: equal events, any two honest outputs, equal adversary
outputs. -/
abbrev outerView {S W K : Type} : PubView (OEv W) (OOut S W K) := keHonView.sum eqView

/-- The view of `F_AKE`, for which `F_AKE_opaque` holds. -/
abbrev subView {K : Type} : PubView (FEv K) (FOut K) := keHonView.sum eqView

/-- Every decision is related to itself. -/
theorem stepRel_refl {S W K : Type} (d : Dec S W K) :
    PubView.StepRel (outerView (W := W)) subView d d := by
  rcases d with (h | a) | (o | o)
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl

/-- The answers of the simulator to related answers of `F_AKE` are related. -/
theorem simOut_rel {S W K : Type} (ph : Phase S W K) {o o' : FOut K}
    (h : (subView (K := K)).out o o') :
    (outerView (W := W)).out (simOut ph o) (simOut ph o') := by
  cases ph with
  | fwd =>
    cases h with
    | inl _ => exact Sum.LiftRel.inl trivial
    | inr _ => exact Sum.LiftRel.inr rfl
  | out r => exact Sum.LiftRel.inr rfl

section SimOpaque

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- **The unwinding condition of the simulator** for the equality of states: its state and its
decisions depend on its events and not on the answers of `F_AKE` on its honest port. -/
theorem simProt_unwinding : (simProt (K := K) G).Unwinding outerView subView Eq := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    have he' : e = e' := by
      cases he with
      | inl h => exact congrArg Sum.inl h
      | inr h => exact congrArg Sum.inr h
    subst he'
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, stepRel_refl _⟩)
      (rHoare_refl _)
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, simOut_rel _ ho⟩
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, simOut_rel _ ho⟩

/-- **Opacity of the simulator**: it reads no key of `F_AKE`. -/
theorem simProt_opaque : (simProt (K := K) G).Opaque outerView subView :=
  ⟨Eq, simProt_unwinding G⟩

/-- **The X3DH simulator** as a bundled opaque simulator. -/
noncomputable def x3dhSim :
    Simulator (OEv W) (OOut S W K) (FEv K) (FOut K) outerView subView :=
  Simulator.ofMultiHybrid (simProt G) (simProt_opaque G)

end SimOpaque

/-! ## The square in oracle-game form -/

/-- The steps of `F_AKE` with uniform keys do not touch the heap. -/
theorem F_AKE_pureNF {K : Type} [Fintype K] [Nonempty K] (t : St K) (e : FEv K) :
    PureNF ((F_AKE (SPComp.sample K)).step t e) := by
  rcases e with h | a
  · simp only [F_AKE, Sys.ofPorts_step_inl, honSys]
    exact (pureNF_pure _).map _
  · simp only [F_AKE, Sys.ofPorts_step_inr, advSys]
    refine PureNF.map _ ?_
    cases a <;> first | exact pureNF_pure _ | exact (pureNF_sample K).map _

section SimWorld

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The steps of the simulated world, the simulator running with `F_AKE`, do not touch the
heap. -/
theorem simWorld_pureNF :
    ∀ t e, PureNF (((simProt (K := K) G).withSub (F_AKE (SPComp.sample K))).step t e) :=
  withSub_pureNF _ _ F_AKE_pureNF (simStart_pureNF G)
    (fun _ _ => pureNF_pure _) (fun _ _ => pureNF_pure _)

/-- **The simulated X3DH game**: the oracle game of the simulator running with `F_AKE`. -/
noncomputable def simGame : KeyedGame (OEv W) (OOut S W K) :=
  pureGame ((simProt (K := K) G).withSub (F_AKE (SPComp.sample K))) (simWorld_pureNF G)

/-- **The simulated world as an oracle game**: the oracle system of `simGame G` realizes the
simulator running with `F_AKE` at distance `0`. -/
theorem simWorld_realizes :
    Realizes ((OProt.oracle (Q := OEv W) (A := OOut S W K)).sys (simGame G))
      ((simProt (K := K) G).withSub (F_AKE (SPComp.sample K))) (fun _ _ => 0) :=
  pureGame_realizes _ _

/-- **X3DH realizes `F_AKE` behind `x3dhSim`, in oracle-game form.** For every environment `Z`,
the distance between the real X3DH protocol and the simulator running with `F_AKE` is at most
the advantage of the oracle adversary `OProt.oracle.reduction Z` between the real game
`realGame G` and the simulated game `simGame G`. -/
theorem x3dh_realizesSim_oracleGame :
    RealizesSim (x3dhReal (K := K) G) (F_AKE (SPComp.sample K)) (x3dhSim G)
      (fun _ Z => KeyedGame.advantage (realGame G) (simGame G) (OProt.oracle.reduction Z)) :=
  fun ζ Z => le_of_le_of_eq
    ((Realizes.trans (Realizes.ofOracleGame OProt.oracle (realGame G) (simGame G))
      (simWorld_realizes G)) ζ Z) (add_zero _)

end SimWorld

end CatCrypt.Crypto.AKE.X3DHSquare

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.FAKESys
public import CatCryptCore.Crypto.PAKE.CPaceSquare

/-!
# X3DH as a real protocol over the key-exchange interface

**Ideal functionality.** `F_AKE (SPComp.sample K)` of `CatCryptCore.Crypto.AKE.FAKESys`: the
multi-session authenticated key exchange of Canetti and Krawczyk with adversarial key delivery
and corruption of parties.

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

## Main definitions

* `Inp`, `aliceInp`, `bobInp`: the inputs of the key derivation.
* `RSt`, `RAEv`, `ROut`: the state and the adversary port of the real protocol.
* `realGame`, `x3dhReal`: the real protocol as an oracle game and as a system.

## Main results

* `aliceInp_eq_bobInp`: the two sides of an unmodified exchange derive from the same input.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt)
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

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype K]
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

end CatCrypt.Crypto.AKE.X3DHSquare

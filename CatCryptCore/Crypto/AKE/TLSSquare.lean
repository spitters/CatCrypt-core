/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackUC
public import CatCryptCore.Crypto.Signatures.EUFCMAPMF

/-!
# The TLS 1.3 handshake against the key-exchange functionality with impersonation

**Ideal functionality.** `F_AKEImp (SPComp.sample (TKey Sec)) srvImp true` of
`CatCryptCore.Crypto.AKE.FAKESys`: the multi-session key exchange of Canetti and Krawczyk with
adversarial key delivery, adaptive corruption of parties and uniform keys in `TKey Sec` (the
four external stage secrets CATS, SATS, EMS, RMS of the full 1-RTT handshake, Dowling, Fischlin,
Günther and Stebila, J. Cryptology 34(4), 2021, Section 5), in its variant `unlinked`, with the
impersonation predicate `srvImp`: the adversary may take the place of the peer of every server
(responder) session. This is unilateral authentication: the client authenticates the server,
the server does not authenticate the client.

**Algorithms.** `TLSAlg S W Tr VK SK Sig Sec` is the record of the algorithms: the key share
`pub` and the shared value `dh` of (EC)DHE over secrets `S` and shares `W`, the transcript
operations `TrOps` (ClientHello...ServerHello, Certificate, CertificateVerify, the two Finished
messages), and a signature scheme on transcripts. The key derivation is a `KDFOp` on the inputs
`TInp`: a label of the composed key schedule, a transcript and the (EC)DHE value. TLS 1.3 over a
group `G` is `tlsDHAlg G Sg trs`.

**Real protocol.** `tlsRealOfK κ A` (and `tlsRealOf A` at the lazily sampled key derivation)
runs the full handshake (RFC 8446, Section 2) for every session:
* each party's signing key pair is drawn by the key generation of the scheme at its first use;
  `pub p` reads the verification key, `corrupt p` marks `p` corrupt and reveals its signing key,
  and is refused with `ack` while a session with a key names `p` as party or peer and the
  session of its peer in the same protocol session has no key (`Pending`);
* `hello sid c` draws the ephemeral secret `x` of the client session and reads `X = pub x`;
* `srvRecv sid s X` lets the server session draw `y`, sign the transcript up to its
  Certificate, and answer `(Y, vk_s, σ, sfin)` with `sfin` the key derivation at `sfin`;
* `cliRecv sid c Y σ sfin` lets the client verify `σ` under the registered key of its peer and
  `sfin` at its own transcript; on success it completes with the key of its transcript and
  answers its Finished `cfin`;
* `srvFin sid s cfin` completes the server session when `cfin` is the value it expects;
* `kdf x` queries the key derivation.
The filtered protocol `tlsFiltOfK κ A` differs in one rule: the client accepts only when its peer
is corrupt or signed the transcript (`filtGameK`).

**Simulator.** `tlsSim A` keeps a copy of the filtered state and draws every signing key,
ephemeral secret and the Finished values itself. It forwards the honest events, answers `poll`,
`pub`, `hello` and `kdf` on its copy, refuses `corrupt` as the protocol does on its copy, and
otherwise corrupts in the functionality. On `srvRecv` it calls
`impersonate` when the delivered share is not the share of the client session named by the
server's record. On a completion it computes the session's transcript and (EC)DHE value: an
exposed session receives the key of the key derivation, passed to `newKey`; any other session
receives the key of the functionality (`newKey` when the partner has not completed or completed
on the same input, `newKeyUnlinked` otherwise). The simulator reads no key of the functionality
(`tlsSimProt_opaque`) and is a forwarding simulator (`tlsSimProt_isFwd`).

**Results.** The square in oracle-game form, `tls_filt_realizesSim_oracleGame`: the filtered
protocol realizes `F_AKEImp … srvImp true` behind `tlsSim A`, with bound at the environment `Z`
the advantage of `OProt.oracle.reduction Z` between `filtGameK lazyKDF A` and `simGame A`.

## Main definitions

* `TLabel`, `TInp`: the labels and inputs of the composed key schedule.
* `TrOps`, `TLSAlg`, `tlsDHAlg`, `TKey`: the algorithms and the session key.
* `srvImp`: the impersonation predicate of unilateral authentication.
* `TEv`, `TOut`: the adversary port of the real protocol.
* `Pending`: the states in which `corrupt` is refused.
* `realGameK`, `filtGameK`, `tlsRealOfK`, `tlsRealOf`, `tlsFiltOfK`: the real and the filtered
  protocol as oracle games and as systems.
* `tlsSimProt`, `tlsSim`, `tlsFwd`: the simulator and its forwarding data.
* `simGame`: the oracle game of the simulated world.

## Main results

* `tlsSimProt_opaque`, `tlsSimProt_isFwd`.
* `F_AKEImp_pureNF`, `simWorld_pureNF`, `simWorld_realizes`.
* `tls_filt_realizesSim_oracleGame`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.TLSSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.Signatures (PSigScheme)
open CatCrypt.Crypto.AKE.X3DHSquare (KDFOp lazyKDF FEv FOut subView)
open CatCrypt.Crypto.Messaging.SignalStackUC (FwdData IsFwd fwdOut)
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_pure PureNF.map withSub_pureNF pureGame
  pureGame_realizes)
open PubView (eqView)
open scoped ENNReal

/-! ## Inputs of the key derivation -/

/-- The labels of the composed key schedule. `chs` and `shs` are the handshake traffic secrets
(no event of the model derives them); `sfin` and `cfin` are the Finished values; `cap`, `sap`,
`exp`, `res` are CATS, SATS, EMS and RMS. -/
inductive TLabel where
  /-- The client handshake traffic secret. -/
  | chs
  /-- The server handshake traffic secret. -/
  | shs
  /-- The server Finished value. -/
  | sfin
  /-- The client Finished value. -/
  | cfin
  /-- The client application traffic secret. -/
  | cap
  /-- The server application traffic secret. -/
  | sap
  /-- The exporter master secret. -/
  | exp
  /-- The resumption master secret. -/
  | res
  deriving DecidableEq

/-- An input of the key derivation: the label, the transcript at the stage, and the (EC)DHE
value. The transcripts are ClientHello...ServerHello for `chs`, `shs`; ...server
CertificateVerify for `sfin`; ...server Finished for `cfin`, `cap`, `sap`, `exp`; ...client
Finished for `res`. -/
structure TInp (Tr W : Type) where
  /-- The label. -/
  lbl : TLabel
  /-- The transcript. -/
  tr : Tr
  /-- The (EC)DHE value. -/
  dhe : W
  deriving DecidableEq

/-! ## The algorithms -/

/-- The transcript operations: the transcript of ClientHello (session `sid`, client `c`, share
`X`) and ServerHello (server `s`, share `Y`), and the appending of the server Certificate, the
server CertificateVerify, the server Finished and the client Finished. -/
structure TrOps (Tr W VK Sig Sec : Type) where
  /-- ClientHello...ServerHello. -/
  tr1 : SessionId → PartyId → PartyId → W → W → Tr
  /-- ...server Certificate (the verification key). -/
  trCert : Tr → VK → Tr
  /-- ...server CertificateVerify. -/
  trCV : Tr → Sig → Tr
  /-- ...server Finished. -/
  trSF : Tr → Sec → Tr
  /-- ...client Finished. -/
  trCF : Tr → Sec → Tr

/-- The algorithms of a signed ephemeral Diffie–Hellman handshake with key confirmation:
secrets `S`, shares `W`, transcripts `Tr`, a signature scheme on transcripts, stage values
`Sec`. -/
structure TLSAlg (S W Tr VK SK Sig Sec : Type) extends TrOps Tr W VK Sig Sec where
  /-- The key share of a secret. -/
  pub : S → W
  /-- The shared value of a secret and a share. -/
  dh : S → W → W
  /-- The signature scheme of CertificateVerify. -/
  sig : PSigScheme Tr VK SK Sig

/-- **TLS 1.3 over the group `G`** with the signature scheme `Sg` and the transcript operations
`trs`: the key share `g^x` and the shared value `Y^x`. -/
abbrev tlsDHAlg {S W Tr VK SK Sig Sec : Type} [Field S] (G : DHGroup S W)
    (Sg : PSigScheme Tr VK SK Sig) (trs : TrOps Tr W VK Sig Sec) :
    TLSAlg S W Tr VK SK Sig Sec :=
  { toTrOps := trs, pub := G.pub, dh := fun x Y => G.exp Y x, sig := Sg }

/-- The key of a session: CATS, SATS, EMS, RMS. -/
abbrev TKey (Sec : Type) := Sec × Sec × Sec × Sec

/-- **The impersonation predicate of unilateral authentication**: the adversary may take the
place of the peer of a responder (server) session; the client is unauthenticated. -/
def srvImp {K : Type} (r : Rec K) : Bool := decide (r.role = .responder)

/-! ## The adversary port of the real protocol -/

/-- The events of the adversary port of the real protocol. -/
inductive TEv (W Tr Sig Sec : Type) where
  /-- No action. -/
  | idle
  /-- Read the next notice of a new session. -/
  | poll
  /-- Read the verification key of the party `pid` (its Certificate). -/
  | pub (pid : PartyId)
  /-- Corrupt the party `pid`: reveal its signing key. -/
  | corrupt (pid : PartyId)
  /-- Read the ClientHello key share of the client session of `pid` in `sid`. -/
  | hello (sid : SessionId) (pid : PartyId)
  /-- Deliver the client share `X` to the server session of `pid` in `sid`. -/
  | srvRecv (sid : SessionId) (pid : PartyId) (X : W)
  /-- Deliver ServerHello share `Y`, CertificateVerify `σ` and server Finished `sfin` to the
  client session of `pid` in `sid`. -/
  | cliRecv (sid : SessionId) (pid : PartyId) (Y : W) (σ : Sig) (sfin : Sec)
  /-- Deliver the client Finished `cfin` to the server session of `pid` in `sid`. -/
  | srvFin (sid : SessionId) (pid : PartyId) (cfin : Sec)
  /-- Query the key derivation at `x`. -/
  | kdf (x : TInp Tr W)

/-- The outputs of the adversary port of the real protocol. -/
inductive TOut (W VK SK Sig Sec : Type) where
  /-- Acknowledgement. -/
  | ack
  /-- The next notice, if any. -/
  | notice (o : Option Notice)
  /-- A verification key. -/
  | pub (vk : VK)
  /-- The ClientHello share of a client session, if the session exists. -/
  | share (o : Option W)
  /-- The server flight (share, Certificate, CertificateVerify, Finished), or `none` when the
  server session does not exist or already answered. -/
  | srvMsg (o : Option (W × VK × Sig × Sec))
  /-- The client Finished, or `none` when the client aborts. -/
  | cliFin (o : Option Sec)
  /-- The signing key of a corrupted party. -/
  | secret (sk : SK)
  /-- An answer of the key derivation. -/
  | hash (k : Sec)

/-- The events of the real protocol: the honest port and the adversary port. -/
abbrev TOEv (W Tr Sig Sec : Type) := HEv ⊕ TEv W Tr Sig Sec

/-- The outputs of the real protocol. -/
abbrev TOOut (W VK SK Sig Sec : Type) := HOut (TKey Sec) ⊕ TOut W VK SK Sig Sec

/-- The view of the real interface: equal events, any two honest outputs, equal adversary
outputs. -/
abbrev tOuterView {W Tr VK SK Sig Sec : Type} :
    PubView (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) := keHonView.sum eqView

/-! ## The real protocol -/

/-- The state of the real protocol with key-derivation state `T`: the session records, corrupt
parties and notices as in `F_AKE`, the signing key pairs of the parties, the ephemeral secret of
each client session, the transcript, (EC)DHE value and expected client Finished of each server
session that answered, the transcripts each party signed, and the state of the key
derivation. -/
structure TRStT (S W Tr VK SK Sec T : Type) where
  /-- Session records, corrupt parties and notices. -/
  st : St (TKey Sec)
  /-- The signing key pair of a party, once drawn. -/
  lt : PartyId → Option (VK × SK)
  /-- The ephemeral secret of a client session. -/
  eph : Inst → Option S
  /-- The transcript up to server Finished, the (EC)DHE value and the expected client Finished
  of a server session that answered. -/
  srv : Inst → Option (Tr × W × Sec)
  /-- The transcripts signed by a party. -/
  log : PartyId → List Tr
  /-- The state of the key derivation. -/
  ro : T

/-- The state of the real protocol with the lazily sampled key derivation. -/
abbrev TRSt (S W Tr VK SK Sec : Type) := TRStT S W Tr VK SK Sec (List (TInp Tr W × Sec))

section Real

variable {S W Tr VK SK Sig Sec T : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec]

/-- The state with the key `k` at the session `x` and the key-derivation state `ro`. -/
def setKey (s : TRStT S W Tr VK SK Sec T) (x : Inst) (k : TKey Sec) (ro : T) :
    TRStT S W Tr VK SK Sec T :=
  { s with
    st := match s.st.recs x with
      | some r => setRec s.st x { r with key := some k }
      | none => s.st
    ro := ro }

variable (κ : KDFOp T (TInp Tr W) Sec)

/-- A step of the honest port of the real protocol with the key derivation `κ`: a new session
starts in `κ`. -/
noncomputable def realHonK (s : TRStT S W Tr VK SK Sec T) :
    HEv → PMF (HOut (TKey Sec) × TRStT S W Tr VK SK Sec T)
  | .newSession sid pid peer role =>
    if (s.st.recs (sid, pid)).isNone then
      (κ.start s.ro (sid, pid)).map fun t =>
        (.ok, { s with st := addSession s.st (sid, pid) peer role, ro := t })
    else PMF.pure (.ok, s)
  | .getKey sid pid => PMF.pure (.key (keyOf s.st (sid, pid)), s)

variable (A : TLSAlg S W Tr VK SK Sig Sec)

/-- The signing key pair of the party `pid`, drawn by the key generation at its first use. -/
noncomputable def ltAt (s : TRStT S W Tr VK SK Sec T) (pid : PartyId) :
    PMF ((VK × SK) × TRStT S W Tr VK SK Sec T) :=
  match s.lt pid with
  | some l => PMF.pure (l, s)
  | none => A.sig.keyDist.map fun l => (l, { s with lt := Function.update s.lt pid (some l) })

/-- The key of the session `x` with the key derivation `κ` at the transcript `tSF` up to server
Finished, the (EC)DHE value `Z` and the client Finished `cf`: CATS, SATS and EMS at `tSF`, RMS
at the transcript up to client Finished. -/
noncomputable def keysK (ro : T) (x : Inst) (tSF : Tr) (Z : W) (cf : Sec) :
    PMF (TKey Sec × T) :=
  (κ.derive ro x ⟨.cap, tSF, Z⟩).bind fun a => (κ.derive a.2 x ⟨.sap, tSF, Z⟩).bind fun b =>
    (κ.derive b.2 x ⟨.exp, tSF, Z⟩).bind fun c =>
      (κ.derive c.2 x ⟨.res, A.trCF tSF cf, Z⟩).map fun d => ((a.1, b.1, c.1, d.1), d.2)

/-- Whether `corrupt pid` is refused in the state `s`: a session of the notices has a key, has
`pid` as its party or its peer, and the session of its peer in the same protocol session has no
key (no record, or a record without key). -/
def Pending (s : TRStT S W Tr VK SK Sec T) (pid : PartyId) : Bool :=
  s.st.notices.any fun n =>
    match s.st.recs (n.sid, n.pid) with
    | some r => r.key.isSome && (n.pid == pid || r.peer == pid) &&
        (keyOf s.st (n.sid, r.peer)).isNone
    | none => false

/-- The ClientHello share of the session `x`, if drawn. -/
def shareOf (s : TRStT S W Tr VK SK Sec T) (x : Inst) : Option W := (s.eph x).map A.pub

/-- `hello` at the client session `x`: its share, drawn at the first `hello`. -/
noncomputable def helloStep (s : TRStT S W Tr VK SK Sec T) (x : Inst) :
    PMF (TOut W VK SK Sig Sec × TRStT S W Tr VK SK Sec T) :=
  match s.st.recs x with
  | some r =>
    if r.role = .initiator then
      match s.eph x with
      | some xs => PMF.pure (.share (some (A.pub xs)), s)
      | none => (PMF.uniformFintype S).map fun xs =>
          (.share (some (A.pub xs)), { s with eph := Function.update s.eph x (some xs) })
    else PMF.pure (.share none, s)
  | none => PMF.pure (.share none, s)

/-- `srvRecv` at the server session `x` on the client share `X`: the server draws `y`, signs the
transcript up to its Certificate, derives the server and the client Finished values, records
its transcript and answers its flight. -/
noncomputable def srvRecvK (s : TRStT S W Tr VK SK Sec T) (x : Inst) (X : W) :
    PMF (TOut W VK SK Sig Sec × TRStT S W Tr VK SK Sec T) :=
  match s.st.recs x with
  | some r =>
    if r.role = .responder ∧ r.key.isNone ∧ (s.srv x).isNone then
      (ltAt A s x.2).bind fun l => (PMF.uniformFintype S).bind fun y =>
        (A.sig.sign l.1.2 (A.trCert (A.tr1 x.1 r.peer x.2 X (A.pub y)) l.1.1)).bind fun σ =>
          (κ.derive l.2.ro x
            ⟨.sfin, A.trCV (A.trCert (A.tr1 x.1 r.peer x.2 X (A.pub y)) l.1.1) σ, A.dh y X⟩).bind
            fun sf =>
              (κ.derive sf.2 x ⟨.cfin, A.trSF (A.trCV (A.trCert (A.tr1 x.1 r.peer x.2 X (A.pub y))
                l.1.1) σ) sf.1, A.dh y X⟩).map fun cf =>
                (.srvMsg (some (A.pub y, l.1.1, σ, sf.1)),
                  { l.2 with
                    srv := Function.update l.2.srv x (some (A.trSF (A.trCV (A.trCert
                      (A.tr1 x.1 r.peer x.2 X (A.pub y)) l.1.1) σ) sf.1, A.dh y X, cf.1))
                    log := Function.update l.2.log x.2
                      (A.trCert (A.tr1 x.1 r.peer x.2 X (A.pub y)) l.1.1 :: l.2.log x.2)
                    ro := cf.2 })
    else PMF.pure (.srvMsg none, s)
  | none => PMF.pure (.srvMsg none, s)

/-- The check of `cliRecv` at the client session `x` on the server share `Y`, the signature `σ`
and the server Finished `sf`: the client verifies `σ` under the registered key of its peer and
`sf` at its transcript, and, when `filt`, that its peer is corrupt or signed the transcript. On
success the result is the transcript up to server Finished, the (EC)DHE value and the client
Finished. -/
noncomputable def cliCheckK (filt : Bool) (s : TRStT S W Tr VK SK Sec T) (x : Inst) (Y : W)
    (σ : Sig) (sf : Sec) : PMF (Option (Tr × W × Sec) × TRStT S W Tr VK SK Sec T) :=
  match s.st.recs x, s.eph x with
  | some r, some xs =>
    if r.role = .initiator ∧ r.key.isNone then
      (ltAt A s r.peer).bind fun l =>
        (κ.derive l.2.ro x
          ⟨.sfin, A.trCV (A.trCert (A.tr1 x.1 x.2 r.peer (A.pub xs) Y) l.1.1) σ, A.dh xs Y⟩).bind
          fun sv =>
            if A.sig.verify l.1.1 (A.trCert (A.tr1 x.1 x.2 r.peer (A.pub xs) Y) l.1.1) σ ∧
                sf = sv.1 ∧
                (!filt || l.2.st.corrupt r.peer ||
                  decide (A.trCert (A.tr1 x.1 x.2 r.peer (A.pub xs) Y) l.1.1 ∈ l.2.log r.peer))
            then
              (κ.derive sv.2 x ⟨.cfin, A.trSF (A.trCV (A.trCert (A.tr1 x.1 x.2 r.peer (A.pub xs) Y)
                l.1.1) σ) sf, A.dh xs Y⟩).map fun cf =>
                (some (A.trSF (A.trCV (A.trCert (A.tr1 x.1 x.2 r.peer (A.pub xs) Y) l.1.1) σ) sf,
                  A.dh xs Y, cf.1), { l.2 with ro := cf.2 })
            else PMF.pure (none, { l.2 with ro := sv.2 })
    else PMF.pure (none, s)
  | _, _ => PMF.pure (none, s)

/-- The check of `srvFin` at the server session `x` on the client Finished `cfin`: the recorded
transcript, (EC)DHE value and client Finished when `cfin` is the expected value. -/
def srvFinCheck (s : TRStT S W Tr VK SK Sec T) (x : Inst) (cfin : Sec) :
    Option (Tr × W × Sec) :=
  match s.st.recs x, s.srv x with
  | some r, some p => if r.role = .responder ∧ r.key.isNone ∧ cfin = p.2.2 then some p else none
  | _, _ => none

/-- `corrupt pid`: `ack` and no change when `Pending s pid`; otherwise the signing key of `pid`
and the mark. -/
noncomputable def corruptK (s : TRStT S W Tr VK SK Sec T) (pid : PartyId) :
    PMF (TOut W VK SK Sig Sec × TRStT S W Tr VK SK Sec T) :=
  if Pending s pid then PMF.pure (.ack, s) else
    (ltAt A s pid).map fun l => (.secret l.1.2, { l.2 with st := corruptStep l.2.st pid })

/-- A step of the adversary port of the real protocol with the key derivation `κ`; `filt` is
the filter of `cliCheckK`. -/
noncomputable def realAdvK (filt : Bool) (s : TRStT S W Tr VK SK Sec T) :
    TEv W Tr Sig Sec → PMF (TOut W VK SK Sig Sec × TRStT S W Tr VK SK Sec T)
  | .idle => PMF.pure (.ack, s)
  | .poll => PMF.pure (.notice (pollStep s.st).2, { s with st := (pollStep s.st).1 })
  | .pub pid => (ltAt A s pid).map fun l => (.pub l.1.1, l.2)
  | .corrupt pid => corruptK A s pid
  | .hello sid pid => helloStep A s (sid, pid)
  | .srvRecv sid pid X => srvRecvK κ A s (sid, pid) X
  | .cliRecv sid pid Y σ sf => (cliCheckK κ A filt s (sid, pid) Y σ sf).bind fun c =>
      match c.1 with
      | some p => (keysK κ A c.2.ro (sid, pid) p.1 p.2.1 p.2.2).map fun k =>
          (.cliFin (some p.2.2), setKey c.2 (sid, pid) k.1 k.2)
      | none => PMF.pure (.cliFin none, c.2)
  | .srvFin sid pid cfin =>
      match srvFinCheck s (sid, pid) cfin with
      | some p => (keysK κ A s.ro (sid, pid) p.1 p.2.1 p.2.2).map fun k =>
          (.ack, setKey s (sid, pid) k.1 k.2)
      | none => PMF.pure (.ack, s)
  | .kdf x => (κ.query s.ro x).map fun p => (.hash p.1, { s with ro := p.2 })

/-- The initial state of the real protocol with the key derivation `κ`. -/
def tInitK : TRStT S W Tr VK SK Sec T :=
  ⟨initSt, fun _ => none, fun _ => none, fun _ => none, fun _ => [], κ.init⟩

/-- The protocol of the algorithms `A` with the key derivation `κ` and the filter `filt` as an
oracle game: a trivial key, and the oracle is the step of the protocol. -/
noncomputable def gameK (filt : Bool) :
    KeyedGame (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) where
  Key := Unit
  State := TRStT S W Tr VK SK Sec T
  keyDist := PMF.pure ()
  oracle _ s
    | .inl h => (realHonK κ s h).map fun p => (.inl p.1, p.2)
    | .inr a => (realAdvK κ A filt s a).map fun p => (.inr p.1, p.2)
  init := tInitK κ

/-- **The real game of the algorithms `A` with the key derivation `κ`.** -/
noncomputable def realGameK : KeyedGame (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) :=
  gameK κ A false

/-- **The filtered game of the algorithms `A` with the key derivation `κ`**: a client accepts
only when its peer is corrupt or signed the transcript. -/
noncomputable def filtGameK : KeyedGame (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) :=
  gameK κ A true

/-- **The real protocol of the algorithms `A` with the key derivation `κ`** as a system: each
event is a query to the oracle of `realGameK κ A`. -/
noncomputable def tlsRealOfK :=
  (OProt.oracle (Q := TOEv W Tr Sig Sec) (A := TOOut W VK SK Sig Sec)).sys (realGameK κ A)

/-- **The filtered protocol of the algorithms `A` with the key derivation `κ`** as a system. -/
noncomputable def tlsFiltOfK :=
  (OProt.oracle (Q := TOEv W Tr Sig Sec) (A := TOOut W VK SK Sig Sec)).sys (filtGameK κ A)

/-- **The real protocol of the algorithms `A`** as a system, with the key derivation a lazily
sampled random function. -/
noncomputable def tlsRealOf := tlsRealOfK (lazyKDF (D := TInp Tr W) (K := Sec)) A

end Real

/-! ## The simulator -/

/-- The state of the simulator: its copy of the filtered state, the key-derivation input of
each session it completed, and the adversary output stored for the answer of the functionality
(`none` forwards the answer). -/
abbrev TSimSt (S W Tr VK SK Sig Sec : Type) :=
  TRSt S W Tr VK SK Sec × (Inst → Option (TInp Tr W)) × Option (TOut W VK SK Sig Sec)

/-- A decision of the simulator. -/
abbrev TDec (W VK SK Sig Sec : Type) :=
  FEv (TKey Sec) ⊕ TOOut W VK SK Sig Sec

/-- A call of the functionality or an adversary output as a decision. -/
def liftDec {W VK SK Sig Sec : Type} :
    FEv (TKey Sec) ⊕ TOut W VK SK Sig Sec → TDec W VK SK Sig Sec
  | .inl e => .inl e
  | .inr o => .inr (.inr o)

section Sim

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]
  (A : TLSAlg S W Tr VK SK Sig Sec)

/-- The delivery of the key of the session `x` completing at the transcript `tSF`, the (EC)DHE
value `Z` and the client Finished `cf`, with the adversary output `o`. An exposed session
receives the key derivation of its key on the simulator's copy, passed to `newKey`. Any other
session receives the key of the functionality: `newKey` when its partner has not completed or
completed on the same input, `newKeyUnlinked` otherwise; the key-derivation table is
unchanged. -/
noncomputable def deliver (rs : TRSt S W Tr VK SK Sec) (inp : Inst → Option (TInp Tr W))
    (x : Inst) (tSF : Tr) (Z : W) (cf : Sec) (o : TOut W VK SK Sig Sec) :
    PMF (TSimSt S W Tr VK SK Sig Sec × (FEv (TKey Sec) ⊕ TOut W VK SK Sig Sec)) :=
  match rs.st.recs x with
  | some r =>
    if Exposed rs.st x r then
      (keysK lazyKDF A rs.ro x tSF Z cf).map fun k =>
        ((setKey rs x k.1 k.2, Function.update inp x (some ⟨.cap, tSF, Z⟩), some o),
          .inl (.inr (.newKey x.1 x.2 k.1)))
    else
      PMF.pure ((setKey rs x default rs.ro, Function.update inp x (some ⟨.cap, tSF, Z⟩), some o),
        .inl (.inr (if (inp (x.1, r.peer)).all (· = ⟨.cap, tSF, Z⟩) then .newKey x.1 x.2 default
          else .newKeyUnlinked x.1 x.2 default)))
  | none => PMF.pure ((rs, inp, none), .inr o)

/-- Whether the server session `x` receives a share that is not the share of the client
session named by its record. -/
def Impersonated (s : TRSt S W Tr VK SK Sec) (x : Inst) (X : W) : Bool :=
  match s.st.recs x with
  | some r => decide (r.role = .responder ∧ r.key.isNone ∧ (s.srv x).isNone ∧
      shareOf A s (x.1, r.peer) ≠ some X)
  | none => false

/-- The simulator on `srvRecv` at `x`: the server step on its copy, preceded in the
functionality by `impersonate` when the share is not the client's. -/
noncomputable def simSrvRecv (s : TSimSt S W Tr VK SK Sig Sec) (x : Inst) (X : W) :
    PMF (TSimSt S W Tr VK SK Sig Sec × (FEv (TKey Sec) ⊕ TOut W VK SK Sig Sec)) :=
  (srvRecvK lazyKDF A s.1 x X).map fun p =>
    if Impersonated A s.1 x X then
      (({ p.2 with st := impStepOf srvImp p.2.st x }, s.2.1, some p.1),
        .inl (.inr (.impersonate x.1 x.2)))
    else ((p.2, s.2.1, none), .inr p.1)

/-- The start of an activation of the simulator, as a distribution over the next state and a
call of the functionality or an adversary output. Honest events update the copy as the real
protocol does and go to the functionality; `corrupt pid` is answered `ack` without a call when
`Pending` holds on the copy, and otherwise corrupts in the functionality; `srvRecv`
is `simSrvRecv`; a completion by `cliRecv` or `srvFin` is `deliver`; every other event is
answered as the filtered protocol does on the copy. -/
noncomputable def simCore (s : TSimSt S W Tr VK SK Sig Sec) :
    TOEv W Tr Sig Sec →
      PMF (TSimSt S W Tr VK SK Sig Sec × (FEv (TKey Sec) ⊕ TOut W VK SK Sig Sec))
  | .inl h => (realHonK lazyKDF s.1 h).map fun p => ((p.2, s.2.1, none), .inl (.inl h))
  | .inr (.corrupt pid) =>
      if Pending s.1 pid then PMF.pure ((s.1, s.2.1, none), .inr .ack) else
        (corruptK A s.1 pid).map fun p => ((p.2, s.2.1, some p.1), .inl (.inr (.corrupt pid)))
  | .inr (.srvRecv sid pid X) => simSrvRecv A s (sid, pid) X
  | .inr (.cliRecv sid pid Y σ sf) =>
      (cliCheckK lazyKDF A true s.1 (sid, pid) Y σ sf).bind fun c =>
        match c.1 with
        | some p => deliver A c.2 s.2.1 (sid, pid) p.1 p.2.1 p.2.2 (.cliFin (some p.2.2))
        | none => PMF.pure ((c.2, s.2.1, none), .inr (.cliFin none))
  | .inr (.srvFin sid pid cfin) =>
      match srvFinCheck s.1 (sid, pid) cfin with
      | some p => deliver A s.1 s.2.1 (sid, pid) p.1 p.2.1 p.2.2 .ack
      | none => PMF.pure ((s.1, s.2.1, none), .inr .ack)
  | .inr e => (realAdvK lazyKDF A true s.1 e).map fun p => ((p.2, s.2.1, none), .inr p.1)

/-- The start of an activation of the simulator: `simCore` lifted to a computation. -/
noncomputable def simStart (s : TSimSt S W Tr VK SK Sig Sec) (e : TOEv W Tr Sig Sec) :
    SPComp (TSimSt S W Tr VK SK Sig Sec × TDec W VK SK Sig Sec) :=
  SPComp.map (fun q => (q.1, liftDec q.2)) (liftPMF (simCore A s e))

/-- The start of the simulator neither touches the heap nor fails. -/
theorem simStart_pureNF (s : TSimSt S W Tr VK SK Sig Sec) (e : TOEv W Tr Sig Sec) :
    PureNF (simStart A s e) :=
  PureNF.map _ ⟨liftPMF_isPure _, liftPMF_noFail _⟩

/-- The state of the simulator after an answer of the functionality. -/
def simReset (s : TSimSt S W Tr VK SK Sig Sec) : TSimSt S W Tr VK SK Sig Sec :=
  (s.1, s.2.1, none)

/-- **The TLS simulator** as a multi-call simulator over `F_AKEImp`, one call per
activation. -/
noncomputable def tlsSimProt :
    MultiHybrid (TSimSt S W Tr VK SK Sig Sec) (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec)
      (FEv (TKey Sec)) (FOut (TKey Sec)) where
  init := (tInitK lazyKDF, fun _ => none, none)
  fuel := 0
  start := simStart A
  resume s o := SPComp.pure (simReset s, .inr (fwdOut .ack s.2.2 o))
  finish s o := SPComp.pure (simReset s, fwdOut .ack s.2.2 o)
  start_noFail s e := (simStart_pureNF A s e).2
  resume_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  finish_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _

/-- **The forwarding data of the TLS simulator**: no stored output after an answer of the
functionality, the stored output of the state, and the acknowledgement `ack`. -/
def tlsFwd : FwdData (TSimSt S W Tr VK SK Sig Sec) (TOut W VK SK Sig Sec) where
  reset := simReset
  phase s := s.2.2
  ack := .ack

/-- **The TLS simulator is a forwarding simulator** for the data `tlsFwd`. -/
theorem tlsSimProt_isFwd : IsFwd (tlsSimProt A) tlsFwd where
  fuel_eq := rfl
  finish_eq _ _ := rfl
  start_noHon s e q hq h := by
    change IsOutcome (simStart A s e) q at hq
    obtain ⟨a, _, rfl⟩ := isOutcome_map_iff.mp hq
    rcases a with ⟨_, d | d⟩ <;> simp [liftDec]

end Sim

/-! ## Opacity of the simulator -/

/-- Every decision of the simulator is related to itself. -/
theorem tStepRel_refl {W Tr VK SK Sig Sec : Type} (d : TDec W VK SK Sig Sec) :
    PubView.StepRel (tOuterView (Tr := Tr)) subView d d := by
  rcases d with (h | a) | (o | o)
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl

/-- The answers of the simulator to related answers of the functionality are related. -/
theorem fwdOut_rel {W Tr VK SK Sig Sec : Type} (ph : Option (TOut W VK SK Sig Sec))
    {o o' : FOut (TKey Sec)} (h : (subView (K := TKey Sec)).out o o') :
    (tOuterView (Tr := Tr)).out (fwdOut .ack ph o) (fwdOut .ack ph o') := by
  cases ph with
  | none =>
    cases h with
    | inl _ => exact Sum.LiftRel.inl trivial
    | inr _ => exact Sum.LiftRel.inr rfl
  | some r => exact Sum.LiftRel.inr rfl

section SimOpaque

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]
  (A : TLSAlg S W Tr VK SK Sig Sec)

/-- **The unwinding condition of the simulator** for the equality of states: its state and its
decisions depend on its events and not on the answers of the functionality on its honest
port. -/
theorem tlsSimProt_unwinding : (tlsSimProt A).Unwinding tOuterView subView Eq := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    have he' : e = e' := by
      cases he with
      | inl h => exact congrArg Sum.inl h
      | inr h => exact congrArg Sum.inr h
    subst he'
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, tStepRel_refl _⟩)
      (rHoare_refl _)
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, fwdOut_rel _ ho⟩
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, fwdOut_rel _ ho⟩

/-- **Opacity of the simulator**: it reads no key of the functionality. -/
theorem tlsSimProt_opaque : (tlsSimProt A).Opaque tOuterView subView :=
  ⟨Eq, tlsSimProt_unwinding A⟩

/-- **The TLS simulator** as a bundled opaque simulator. -/
noncomputable def tlsSim :
    Simulator (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) (FEv (TKey Sec)) (FOut (TKey Sec))
      tOuterView subView :=
  Simulator.ofMultiHybrid (tlsSimProt A) (tlsSimProt_opaque A)

end SimOpaque

/-! ## The square in oracle-game form -/

/-- The steps of the functionality with an impersonation predicate and uniform keys do not
touch the heap. -/
theorem F_AKEImp_pureNF {K : Type} [Fintype K] [Nonempty K] (imp : Rec K → Bool)
    {unlinked : Bool} (t : St K) (e : FEv K) :
    PureNF ((F_AKEImp (SPComp.sample K) imp unlinked).step t e) := by
  rcases e with h | a
  · simp only [F_AKEImp, F_AKEImpK, Sys.ofPorts_step_inl, honSys]
    exact (pureNF_pure _).map _
  · simp only [F_AKEImp, F_AKEImpK, Sys.ofPorts_step_inr, advSysImp]
    refine PureNF.map _ ?_
    cases a <;> first | exact pureNF_pure _ |
      exact (CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K).map _

section SimWorld

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]
  (A : TLSAlg S W Tr VK SK Sig Sec)

/-- The steps of the simulated world, the simulator running with the functionality, do not
touch the heap. -/
theorem simWorld_pureNF :
    ∀ t e, PureNF (((tlsSimProt A).withSub
      (F_AKEImp (SPComp.sample (TKey Sec)) srvImp true)).step t e) :=
  withSub_pureNF _ _ (F_AKEImp_pureNF srvImp) (simStart_pureNF A)
    (fun _ _ => pureNF_pure _) (fun _ _ => pureNF_pure _)

/-- **The simulated TLS game**: the oracle game of the simulator running with the
functionality. -/
noncomputable def simGame : KeyedGame (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) :=
  pureGame ((tlsSimProt A).withSub (F_AKEImp (SPComp.sample (TKey Sec)) srvImp true))
    (simWorld_pureNF A)

/-- **The simulated world as an oracle game**: the oracle system of `simGame A` realizes the
simulator running with the functionality at distance `0`. -/
theorem simWorld_realizes :
    Realizes ((OProt.oracle (Q := TOEv W Tr Sig Sec) (A := TOOut W VK SK Sig Sec)).sys
        (simGame A))
      ((tlsSimProt A).withSub (F_AKEImp (SPComp.sample (TKey Sec)) srvImp true))
      (fun _ _ => 0) :=
  pureGame_realizes _ _

/-- **The filtered TLS protocol realizes `F_AKEImp … srvImp` behind `tlsSim`, in oracle-game
form.** Ideal functionality: `F_AKEImp (SPComp.sample (TKey Sec)) srvImp true`, unilaterally
authenticated key exchange with uniform four-component keys. Real world: the filtered protocol
`tlsFiltOfK lazyKDF A`. Simulator: `tlsSim A`. For every environment `Z`, the distance is at
most the advantage of the oracle adversary `OProt.oracle.reduction Z` between the filtered game
`filtGameK lazyKDF A` and the simulated game `simGame A`. -/
theorem tls_filt_realizesSim_oracleGame :
    RealizesSim (tlsFiltOfK (lazyKDF (D := TInp Tr W) (K := Sec)) A)
      (F_AKEImp (SPComp.sample (TKey Sec)) srvImp true) (tlsSim A)
      (fun _ Z => KeyedGame.advantage (filtGameK lazyKDF A) (simGame A)
        (OProt.oracle.reduction Z)) :=
  fun ζ Z => le_of_le_of_eq
    ((Realizes.trans
      (Realizes.ofOracleGame OProt.oracle (filtGameK (lazyKDF (D := TInp Tr W) (K := Sec)) A)
        (simGame A))
      (simWorld_realizes A)) ζ Z) (add_zero _)

end SimWorld

end CatCrypt.Crypto.AKE.TLSSquare

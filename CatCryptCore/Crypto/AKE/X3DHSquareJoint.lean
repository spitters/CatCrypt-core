/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareSigned
public import CatCryptCore.Crypto.FiatShamirROM.DHGroupParam

/-!
# X3DH with a joint identity and signing key

In the joint-key model of X3DH the identity key `ik` is both the Diffie–Hellman key and the
signing key: the public identity key `pub ik` is the verification key of a Fiat–Shamir
signature over a Σ-protocol `P` for the key relation, with witness `ik`. `JointSigAKEAlg P`
is an `AKEAlg P.Wit P.Stmt` whose identity secret `s` is a witness of `P` for `pub s`.
`x3dhJointAlg G` is X3DH over the Diffie–Hellman group `G` with `P` the Schnorr Σ-protocol at
`GroupParam.ofDHGroup G`. XEdDSA is a later concrete instance of the same record.

**Signatures.** The signature of the party `q` is the Fiat–Shamir signature `fsOf P` over `P`
on the statements of `P`, with a random oracle of its own per party (`JSt.tabs q`, the tables
of the Fiat–Shamir game): the hash is domain-separated by the signer, as the key prefix of
XEdDSA separates it. A party signs its signed prekey once, at the first `sigPub q`, and the
signature is kept (`JSt.sigs`).

**Real protocol.** `x3dhJointRealOf A` runs the real protocol of `A.toAKEAlg` (`realGame`)
with the events of `JSigEv P`:
* `sigPub q` answers the identity key `IK_q`, the signed prekey `SPK_q` and the signature of
  `SPK_q` by the signing attempt of the Fiat–Shamir game (`FiatShamirROM.realStep`) at the
  pair `(IK_q, ik_q)`;
* `sigHash q k` is a query of the random oracle of `q` at `k`;
* `inject sid a spk σ` queries the random oracle of the peer `q` of the session at the point
  `(σ.1, spk)` of the verifier and, when `σ` verifies under `IK_q`, completes the initiator
  `a` with `spk` in place of the signed prekey of `q` (`completeSig`).
Corruption reveals `ik_p`, which is also the signing key. `jointOWith O A` is the real
protocol with the oracle family `O` of the Fiat–Shamir game in place of `realStep`; at
`O = simStep` the signatures are simulated (`simSignO`).

**Simulator.** `x3dhJointSim G` is the layer `sigLayerJ` over `x3dhSimC G`. The layer reads
`IK_q` and `SPK_q` through `pub q`, answers `sigPub q` with the signature of the simulated
signing oracle `FiatShamirROM.simStep IK_q`, which programs the table of `q`, and records the
identity key `IK_q` of a party `q` whose corruption revealed its secrets. It passes an injection
for the peer `q` on as the completion of the initiator with the delivered prekey (the event
`.inr (x, spk)` of `CEv`) when `q` is recorded corrupted and the signature verifies under
`IK_q`, as the real protocol does; when `q` is not recorded corrupted, as `complete sid a` when
the signature verifies and the prekey is the one it signed. It passes `pub q` otherwise.
`x3dhSimC G` is the X3DH simulator `x3dhSim G` with that completion (`simCompleteSig`): a
session whose peer is corrupt is exposed in `F_AKE`, and the simulator gives it the value of
its key-derivation table at the initiator's input with the delivered prekey. The layer over the
real X3DH state machine with that completion (`X3DHSquareSigned.sigSub`) is the filtered world
`filtJO A`.

## Main definitions

* `JointSigAKEAlg P` — the algorithms of an AKE with a Σ-protocol for the key relation
* `x3dhJointAlg G` — X3DH over `G` with Schnorr as the key Σ-protocol
* `JSigEv`, `JSigOut`, `JEv`, `JOut`, `jView` — the events and outputs of the joint interface
* `JSt`, `signAt`, `hashAt`, `jPre`, `jPost` — the layer of the signatures
* `jointOWith`, `jointO`, `simSignO`, `filtJO` — the real protocol, with simulated signatures,
  and the filtered world
* `jointGame`, `x3dhJointRealOf` — the real protocol as a system
* `CEv`, `cView`, `injEvJ` — the interface below the layer and the event of a delivery
* `simCompleteSig`, `simProtC`, `x3dhSimC` — the X3DH simulator with the completion at a
  delivered prekey
* `sigLayerJH`, `sigLayerJ`, `x3dhJointSim` — the layer as a hybrid, and the simulator

## Main results

* `sigLayerJ_opaque` — the layer reads no answer of the honest port of its subroutine
* `simProtC_opaque` — the X3DH simulator with the completion reads no key of `F_AKE`
* `joint_plug_realizes`, `jointLayer_plug_realizes` — the real protocol and the layer over the
  real X3DH protocol as forwarding protocols against oracles, at distance `0`
* `adv_joint_plug` — the advantage against a forwarding protocol as an oracle-run difference
* `x3dhJointSim_withSub` — the simulator over a subroutine is the layer over `x3dhSimC`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.OracleForking
open CatCrypt.Examples
open CatCrypt.Crypto.AKE.X3DHSquareSigned (completeSig layO plug_realizes layer_plug_realizes)
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_pure PureNF.bind)
open PubView (eqView)
open scoped ENNReal

/-! ## The algorithms -/

/-- **The algorithms of an AKE whose identity key is its signing key.** An `AKEAlg` with
secrets the witnesses and public keys the statements of the Fiat–Shamir Σ-protocol `P`; the
identity secret `s` is a witness for its public key `pub s`. -/
structure JointSigAKEAlg (P : FiatShamirROM.Sigma) extends AKEAlg P.Wit P.Stmt where
  /-- The identity key is the signing key. -/
  rel_pub : ∀ s : P.Wit, P.rel (pub s) s

section Schnorr

variable {S W : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]

/-- The statements of Schnorr at `ofDHGroup G` are the elements of `W`. -/
instance (G : DHGroup S W) : DecidableEq (schnorrSigma (GroupParam.ofDHGroup G)).Stmt :=
  inferInstanceAs (DecidableEq W)

/-- The witnesses of Schnorr at `ofDHGroup G` are the scalars `S`. -/
instance (G : DHGroup S W) : Fintype (schnorrSigma (GroupParam.ofDHGroup G)).Wit :=
  inferInstanceAs (Fintype S)

/-- The witnesses of Schnorr at `ofDHGroup G` are the scalars `S`. -/
instance (G : DHGroup S W) : Nonempty (schnorrSigma (GroupParam.ofDHGroup G)).Wit :=
  inferInstanceAs (Nonempty S)

/-- X3DH over the Diffie–Hellman group `G` with the Schnorr Σ-protocol at
`GroupParam.ofDHGroup G` as the signature scheme of the identity key. -/
noncomputable def x3dhJointAlg (G : DHGroup S W) :
    JointSigAKEAlg (schnorrSigma (GroupParam.ofDHGroup G)) where
  toAKEAlg := x3dhAlg (S := S) (W := W) G
  rel_pub _ := rfl

end Schnorr

/-! ## The joint interface -/

section Interface

variable (P : FiatShamirROM.Sigma)

/-- The events of the signatures on the adversary port. -/
inductive JSigEv where
  /-- Read the identity key, the signed prekey and its signature of the party `pid`. -/
  | sigPub (pid : PartyId)
  /-- Query the random oracle of the signatures of `pid` at `k`. -/
  | sigHash (pid : PartyId) (k : P.Com × P.Stmt)
  /-- Deliver the prekey `spk` with the signature `σ` to the initiator `pid` of `sid`. -/
  | inject (sid : SessionId) (pid : PartyId) (spk : P.Stmt) (σ : P.Com × P.Resp)

/-- The outputs of the signatures on the adversary port. -/
inductive JSigOut where
  /-- Acknowledgement. -/
  | ack
  /-- A value of the random oracle. -/
  | hash (e : P.Ch)
  /-- The identity key, the signed prekey and its signature, if the attempt gave one. -/
  | sigPub (ik spk : P.Stmt) (σ : Option (P.Com × P.Resp))

/-- The events of the joint interface. -/
abbrev JEv := HEv ⊕ (RAEv P.Stmt ⊕ JSigEv P)

/-- The outputs of the joint interface. -/
abbrev JOut (K : Type) := HOut K ⊕ (ROut P.Wit P.Stmt K ⊕ JSigOut P)

/-- The view of the joint interface: equal events, any two honest outputs, equal adversary
outputs. -/
abbrev jView {K : Type} : PubView (JEv P) (JOut P K) :=
  keHonView.sum eqView

/-- What the layer does with the answer of the state machine. -/
inductive JPh where
  /-- Forward an answer of the honest port. -/
  | hon
  /-- Forward an adversary answer. -/
  | adv
  /-- Sign the prekey of the party `q` in the answer to `pub q`. -/
  | sign (q : PartyId)
  /-- Query the random oracle of `q` at `k`, with the identity key of the answer to `pub q`. -/
  | hash (q : PartyId) (k : P.Com × P.Stmt)
  /-- Acknowledge a delivery. -/
  | inj
  /-- Forward the answer to `corrupt q`, and record `q` as corrupted when it reveals secrets. -/
  | corr (q : PartyId)

/-- The events of the X3DH state machine below the layer: its events, and the completion
`(x, spk)` of the initiator `x` with the delivered prekey `spk` (`completeSig`). -/
abbrev CEv (W : Type) := OEv W ⊕ (Inst × W)

/-- The view of the interface below the layer: equal events, and outputs related as by
`outerView`. -/
abbrev cView {S W K : Type} : PubView (CEv W) (OOut S W K) where
  ev := Eq
  out := outerView.out

variable [DecidableEq P.Stmt]

/-- The Fiat–Shamir signature scheme over `P` on the statements of `P`. -/
abbrev fsOf : FiatShamirROM.Protocol := P.toProtocol P.Stmt

/-- The state of the Fiat–Shamir game over `P`: its tables and its flag. -/
abbrev FSt := (fsOf P).Tables × Bool

/-- A family of oracles of the Fiat–Shamir game over `P`, indexed by the statement–witness
pair, as `FiatShamirROM.realStep` and `fun xw => FiatShamirROM.simStep xw.1`. -/
abbrev SigOracles :=
  P.Stmt × P.Wit → FSt P → (fsOf P).Query → Step (fsOf P).Answer (FSt P) P.Ch

/-- The state of the layer: the Fiat–Shamir state of each party, the identity key, signed
prekey and signature of each party that signed, the peer of each session, the identity key of
each party seen corrupted, and the phase. -/
structure JSt where
  /-- The tables of the random oracle of each party, with the flag of the game. -/
  tabs : PartyId → FSt P
  /-- The identity key, the signed prekey and the signature of a party, once signed. -/
  sigs : PartyId → Option (P.Stmt × P.Stmt × Option (P.Com × P.Resp))
  /-- The peer of a session. -/
  peers : Inst → Option PartyId
  /-- The identity key of a party whose corruption revealed its secrets. -/
  corr : PartyId → Option P.Stmt
  /-- The phase. -/
  ph : JPh P

/-- The initial state of the layer. -/
def JSt.init : JSt P :=
  ⟨fun _ => (Protocol.Tables.empty, false), fun _ => none, fun _ => none, fun _ => none, .hon⟩

end Interface

/-! ## The layer of the signatures -/

section Layer

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] {K : Type}

/-- The signature of an answer of the Fiat–Shamir game. -/
def sigOf : (fsOf P).Answer → Option (P.Com × P.Resp)
  | .inl _ => none
  | .inr o => o

/-- The output of a hash answer of the Fiat–Shamir game. -/
def hashOut : (fsOf P).Answer → JSigOut P
  | .inl e => .hash e
  | .inr _ => .ack

/-- The verifier of `σ` under `x` on the hash answer at its point `(σ.1, m)`. -/
def verAns (x : P.Stmt) (σ : P.Com × P.Resp) : (fsOf P).Answer → Bool
  | .inl e => P.verify x σ.1 e σ.2
  | .inr _ => false

/-- The layer state with the peer `peer` of the session `x`, when `x` has none. -/
def notePeerJ (l : JSt P) (x : Inst) (peer : PartyId) : JSt P :=
  if (l.peers x).isSome then l else { l with peers := Function.update l.peers x (some peer) }

/-- The layer accepts the delivery of `spk` with `σ` for `q`, on the hash answer `a` at the
point of the verifier, when it signed `spk` for `q` and `σ` verifies under the identity key
of `q`. -/
def accJ (l : JSt P) (q : PartyId) (spk : P.Stmt) (σ : P.Com × P.Resp)
    (a : (fsOf P).Answer) : Bool :=
  match l.sigs q with
  | some c => c.2.1 == spk && verAns P c.1 σ a
  | none => false

/-- **The signature of the party `q`** on its signed prekey `spk` with identity key `ik`, by the
signing query of the Fiat–Shamir oracle `O₁` on the table of `q`: the kept signature when `q`
signed, and otherwise the answer of the oracle, kept. -/
noncomputable def signAt (O₁ : FSt P → (fsOf P).Query → Step (fsOf P).Answer (FSt P) P.Ch)
    (l : JSt P) (q : PartyId) (ik spk : P.Stmt) : PMF (JSt P × JSigOut P) :=
  match l.sigs q with
  | some c => PMF.pure (l, .sigPub ik spk c.2.2)
  | none => (toOracle O₁ (l.tabs q) (.inr spk)).map fun r =>
    ({ l with tabs := Function.update l.tabs q r.2,
              sigs := Function.update l.sigs q (some (ik, spk, sigOf P r.1)) },
      .sigPub ik spk (sigOf P r.1))

/-- **A query of the random oracle of the party `q`** at `k`, by the hash oracle `H` on the
table of `q`. -/
noncomputable def hashAt (H : FSt P → (fsOf P).Key → Step (fsOf P).Answer (FSt P) P.Ch)
    (l : JSt P) (q : PartyId) (k : (fsOf P).Key) : PMF ((fsOf P).Answer × JSt P) :=
  (toOracle H (l.tabs q) k).map fun r => (r.1, { l with tabs := Function.update l.tabs q r.2 })

/-- **The event of the state machine for a delivery** of `spk` with `σ` at the initiator `x`
whose peer is `q`, on the hash answer `a` at the point of the verifier. When `q` was seen
corrupted with identity key `ik`, the completion of `x` with `spk` if `σ` verifies under `ik`;
otherwise `complete` when the layer accepts the delivery (`accJ`). It is `pub q` in the other
cases. -/
def injEvJ (l : JSt P) (x : Inst) (q : PartyId) (spk : P.Stmt) (σ : P.Com × P.Resp)
    (a : (fsOf P).Answer) : CEv P.Stmt :=
  match l.corr q with
  | some ik => if verAns P ik σ a then .inr (x, spk) else .inl (.inr (.pub q))
  | none => if accJ P l q spk σ a then .inl (.inr (.complete x.1 x.2)) else .inl (.inr (.pub q))

/-- **The event of the state machine** for an event of the joint interface. `sigPub q` and
`sigHash q k` read the keys of `q` by `pub q`; `corrupt q` is forwarded in the phase `corr q`;
an injection queries the random oracle of the peer at the point of the verifier and becomes the
event `injEvJ`. -/
noncomputable def jPre (l : JSt P) : JEv P → PMF (JSt P × CEv P.Stmt)
  | .inl (.newSession sid pid peer role) =>
    PMF.pure ({ notePeerJ P l (sid, pid) peer with ph := .hon },
      .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => PMF.pure ({ l with ph := .hon }, .inl (.inl (.getKey sid pid)))
  | .inr (.inl (.corrupt q)) => PMF.pure ({ l with ph := .corr q }, .inl (.inr (.corrupt q)))
  | .inr (.inl a) => PMF.pure ({ l with ph := .adv }, .inl (.inr a))
  | .inr (.inr (.sigPub q)) => PMF.pure ({ l with ph := .sign q }, .inl (.inr (.pub q)))
  | .inr (.inr (.sigHash q k)) => PMF.pure ({ l with ph := .hash q k }, .inl (.inr (.pub q)))
  | .inr (.inr (.inject sid pid spk σ)) =>
    match l.peers (sid, pid) with
    | none => PMF.pure ({ l with ph := .inj }, .inl (.inr .idle))
    | some q => (hashAt P (fun s k => hashStep s.1 s.2 k) l q (σ.1, spk)).map fun r =>
      ({ r.2 with ph := .inj }, injEvJ P l (sid, pid) q spk σ r.1)

/-- **The answer of the layer** to an answer of the state machine, with `pub` the public key of
an identity secret: forward it, record the identity key `pub ik` of `q` when the answer to
`corrupt q` reveals the secrets `(ik, _)`, sign the prekey of the answer to `pub q` with the
simulated signing oracle `FiatShamirROM.simStep` at the identity key of the answer, answer a
hash query with it, or acknowledge. -/
noncomputable def jPost (pub : P.Wit → P.Stmt) (l : JSt P) (o : OOut P.Wit P.Stmt K) :
    PMF (JSt P × JOut P K) :=
  match l.ph, o with
  | .hon, .inl h => PMF.pure (l, .inl h)
  | .adv, .inr a => PMF.pure (l, .inr (.inl a))
  | .corr q, .inr (.secret (some lt)) =>
    PMF.pure ({ l with corr := Function.update l.corr q (some (pub lt.1)) },
      .inr (.inl (.secret (some lt))))
  | .corr _, .inr a => PMF.pure (l, .inr (.inl a))
  | .sign q, .inr (.pub ik spk) =>
    (signAt P (FiatShamirROM.simStep ik) l q ik spk).map fun r => (r.1, .inr (.inr r.2))
  | .hash q k, .inr (.pub ik _) =>
    (hashAt P (fun s k => FiatShamirROM.simStep ik s (.inl k)) l q k).map fun r =>
      (r.2, .inr (.inr (hashOut P r.1)))
  | _, _ => PMF.pure (l, .inr (.inr .ack))

end Layer

/-! ## The real protocol and the filtered world -/

section Real

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] [Fintype P.Wit] [Nonempty P.Wit]
  {K : Type} [Fintype K] [Nonempty K]

/-- **The filtered world**: the layer of the signatures over the real X3DH state machine with
the completion at a delivered prekey (`sigSub`). -/
noncomputable def filtJO (A : AKEAlg P.Wit P.Stmt) :
    JSt P × RSt P.Wit P.Stmt K → JEv P → PMF (JOut P K × (JSt P × RSt P.Wit P.Stmt K)) :=
  layO (jPre P) (X3DHSquareSigned.sigSub A) (jPost P A.pub)

/-- **A step of the real protocol with the signature oracles `O`.** `sigPub q` signs the
signed prekey of `q` by the signing query of `O (IK_q, ik_q)`, `sigHash q k` is the hash query
of `O (IK_q, ik_q)` at `k`, and an injection for the peer `q` completes with the delivered
prekey when its signature verifies under `IK_q` on the hash answer of `O (IK_q, ik_q)`; the
keys of `q` are read by `ltAt`. The other events are those of the filtered world. -/
noncomputable def jointOWith (O : SigOracles P) (A : AKEAlg P.Wit P.Stmt)
    (t : JSt P × RSt P.Wit P.Stmt K) : JEv P → PMF (JOut P K × (JSt P × RSt P.Wit P.Stmt K))
  | .inr (.inr (.sigPub q)) => (ltAt t.2 q).bind fun lt =>
    (signAt P (O (A.pub lt.1.1, lt.1.1)) { t.1 with ph := .sign q } q (A.pub lt.1.1)
      (A.pub lt.1.2)).map fun r => (.inr (.inr r.2), (r.1, lt.2))
  | .inr (.inr (.sigHash q k)) => (ltAt t.2 q).bind fun lt =>
    (hashAt P (fun s k => O (A.pub lt.1.1, lt.1.1) s (.inl k)) { t.1 with ph := .hash q k } q
      k).map fun r => (.inr (.inr (hashOut P r.1)), (r.2, lt.2))
  | .inr (.inr (.inject sid pid spk σ)) =>
    match t.1.peers (sid, pid) with
    | none => PMF.pure (.inr (.inr .ack), ({ t.1 with ph := .inj }, t.2))
    | some q => (ltAt t.2 q).bind fun lt =>
      (hashAt P (fun s k => O (A.pub lt.1.1, lt.1.1) s (.inl k)) { t.1 with ph := .inj } q
        (σ.1, spk)).bind fun r =>
        if verAns P (A.pub lt.1.1) σ r.1 then
          (completeSig A lt.2 (sid, pid) spk).map fun c => (.inr (.inr .ack), (r.2, c.2))
        else PMF.pure (.inr (.inr .ack), (r.2, lt.2))
  | e => filtJO P A t e

/-- **A step of the real protocol**: the signatures of the Fiat–Shamir signing attempt. -/
noncomputable def jointO (A : AKEAlg P.Wit P.Stmt) :
    JSt P × RSt P.Wit P.Stmt K → JEv P → PMF (JOut P K × (JSt P × RSt P.Wit P.Stmt K)) :=
  jointOWith P (fun xw => FiatShamirROM.realStep xw) A

/-- **A step of the real protocol with simulated signatures**: the signatures of the simulated
signing oracle of the Fiat–Shamir game. -/
noncomputable def simSignO (A : AKEAlg P.Wit P.Stmt) :
    JSt P × RSt P.Wit P.Stmt K → JEv P → PMF (JOut P K × (JSt P × RSt P.Wit P.Stmt K)) :=
  jointOWith P (fun xw => FiatShamirROM.simStep xw.1) A

/-- The initial state of the real protocol. -/
def jInit : JSt P × RSt P.Wit P.Stmt K := (JSt.init P, rInit)

/-- **The joint real game**: a trivial key, and the oracle is the step of the real protocol. -/
noncomputable def jointGame (A : JointSigAKEAlg P) : KeyedGame (JEv P) (JOut P K) where
  Key := Unit
  State := JSt P × RSt P.Wit P.Stmt K
  keyDist := PMF.pure ()
  oracle _ := jointO P A.toAKEAlg
  init := jInit P

/-- **The real protocol of X3DH with a joint identity and signing key** as a system: each event
is a query to the oracle of `jointGame A`. -/
noncomputable def x3dhJointRealOf (A : JointSigAKEAlg P) :=
  (OProt.oracle (Q := JEv P) (A := JOut P K)).sys (jointGame P A)

/-- An honest event of the real protocol is the step of the filtered world. -/
theorem jointOWith_inl (O : SigOracles P) (A : AKEAlg P.Wit P.Stmt)
    (t : JSt P × RSt P.Wit P.Stmt K) (h : HEv) :
    jointOWith P O A t (.inl h) = filtJO P A t (.inl h) := by
  cases h <;> rfl

/-- An adversary event of the X3DH state machine in the real protocol is the step of the
filtered world. -/
theorem jointOWith_inr_inl (O : SigOracles P) (A : AKEAlg P.Wit P.Stmt)
    (t : JSt P × RSt P.Wit P.Stmt K) (a : RAEv P.Stmt) :
    jointOWith P O A t (.inr (.inl a)) = filtJO P A t (.inr (.inl a)) := by
  cases a <;> rfl

end Real

/-! ## The layer as a simulator -/

section Sim

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] {K : Type}

/-- **The layer of the signatures as a one-call hybrid** over the X3DH interface with the
completion at a delivered prekey, with `pub` the public key of an identity secret. -/
noncomputable def sigLayerJH (pub : P.Wit → P.Stmt) :
    Hybrid (JSt P) (JEv P) (JOut P K) (CEv P.Stmt) (OOut P.Wit P.Stmt K) where
  init := JSt.init P
  pre l e := liftPMF (jPre P l e)
  post l o := liftPMF (jPost P pub l o)
  pre_noFail _ _ := liftPMF_noFail _
  post_noFail _ _ := liftPMF_noFail _

/-- **The layer of the signatures as a multi-call simulator**, one call per activation. -/
noncomputable def sigLayerJ (pub : P.Wit → P.Stmt) :
    MultiHybrid (JSt P) (JEv P) (JOut P K) (CEv P.Stmt) (OOut P.Wit P.Stmt K) :=
  MultiHybrid.ofHybrid (sigLayerJH P pub)

/-- **The unwinding condition of the layer** for the equality of states: it reads no honest
answer of its subroutine. -/
theorem sigLayerJ_opaque (pub : P.Wit → P.Stmt) :
    (sigLayerJ P pub (K := K)).Opaque (jView P) cView := by
  have houtRefl : ∀ o : JOut P K, (jView P).out o o := by
    rintro (h | a)
    · exact Sum.LiftRel.inl trivial
    · exact Sum.LiftRel.inr rfl
  have hdecRefl : ∀ d : CEv P.Stmt ⊕ JOut P K,
      (jView P).StepRel (cView (S := P.Wit) (K := K)) d d := by
    rintro (g | o)
    · exact rfl
    · exact houtRefl o
  have hpost : ∀ (l : JSt P) (o o' : OOut P.Wit P.Stmt K), outerView.out o o' →
      rHoare eqPre (liftPMF (jPost P pub l o)) (liftPMF (jPost P pub l o'))
        (fun r h r' h' => h = h' ∧ r.1 = r'.1 ∧ (jView P).out r.2 r'.2) := by
    intro l o o' ho
    cases ho with
    | inl _ =>
      rcases l with ⟨tb, sg, pe, cr, ph⟩
      cases ph <;> simp only [jPost, ← liftPMF_pure] <;>
        exact rHoare_ret fun _ _ hh => ⟨hh, rfl, by first
          | exact Sum.LiftRel.inl trivial | exact Sum.LiftRel.inr rfl⟩
    | inr h =>
      cases h
      exact rHoare_conseq (fun _ _ h => h)
        (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, houtRefl _⟩)
        (rHoare_refl _)
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    have he' : e = e' := by
      cases he with
      | inl h => exact congrArg Sum.inl h
      | inr h => exact congrArg Sum.inr h
    subst he'
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨rfl, rfl, hdecRefl _⟩)
      (rHoare_refl _)
  · rintro s _ o o' rfl ho
    simp only [sigLayerJ, MultiHybrid.ofHybrid, sigLayerJH, SPComp.map]
    refine rHoare_bind (hpost s o o' ho) fun r r' => ?_
    intro h₁ h₂ hp
    exact rHoare_ret (Φ := fun h h' => h = h' ∧ r.1 = r'.1 ∧ (jView P).out r.2 r'.2)
      (a := (r.1, (Sum.inr r.2 : CEv P.Stmt ⊕ JOut P K)))
      (b := (r'.1, (Sum.inr r'.2 : CEv P.Stmt ⊕ JOut P K)))
      (Ψ := fun r h r' h' => h = h' ∧ r.1 = r'.1 ∧
        (jView P).StepRel (cView (S := P.Wit) (K := K)) r.2 r'.2)
      (fun _ _ hh => ⟨hh.1, hh.2.1, hh.2.2⟩) h₁ h₂ hp
  · rintro s _ o o' rfl ho
    exact hpost s o o' ho

end Sim

/-! ## The X3DH simulator with the completion at a delivered prekey -/

section SimC

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

/-- **The simulator on the completion of `x` with the delivered prekey `spk`**: the computation
of `completeSig` on its copy, with `spk` in place of the signed prekey of the peer, and the
delivery by `deliver`. At a corrupted peer the session is exposed in `F_AKE`, and `deliver`
gives it the key-derivation value of its copy. -/
noncomputable def simCompleteSig (s : SimSt S W K) (x : Inst) (spk : W) :
    SPComp (SimSt S W K × Dec S W K) :=
  match s.1.st.recs x, s.1.eph x with
  | some r, some ek =>
    match opkOf s.1 x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        SPComp.bind (ltStep s.1 x.2) fun la => SPComp.bind (ltStep la.2 r.peer) fun lb =>
          deliver lb.2 s.2.1 x r
            (aliceInp G x.1 x.2 r.peer la.1.1 ek (G.pub lb.1.1) spk (G.pub opk))
      else SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
    | none => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- The start of an activation of the simulator with the completion at a delivered prekey: an
event of the X3DH interface as `simStart`, a completion by `simCompleteSig`. -/
noncomputable def simStartC (s : SimSt S W K) : CEv W → SPComp (SimSt S W K × Dec S W K)
  | .inl e => simStart G s e
  | .inr p => simCompleteSig G s p.1 p.2

/-- `simCompleteSig` neither touches the heap nor fails. -/
theorem simCompleteSig_pureNF (s : SimSt S W K) (x : Inst) (spk : W) :
    PureNF (simCompleteSig G s x spk) := by
  unfold simCompleteSig
  repeat' split
  all_goals first
    | exact pureNF_pure _
    | exact (ltStep_pureNF _ _).bind fun _ => (ltStep_pureNF _ _).bind fun _ =>
        deliver_pureNF _ _ _ _ _

/-- The start of the simulator with the completion at a delivered prekey neither touches the
heap nor fails. -/
theorem simStartC_pureNF (s : SimSt S W K) (e : CEv W) : PureNF (simStartC G s e) := by
  rcases e with e | p
  · exact simStart_pureNF G s e
  · exact simCompleteSig_pureNF G s p.1 p.2

/-- **The X3DH simulator with the completion at a delivered prekey** as a multi-call simulator
over `F_AKE`, one call per activation. -/
noncomputable def simProtC :
    MultiHybrid (SimSt S W K) (CEv W) (OOut S W K) (FEv K) (FOut K) where
  init := (rInit, fun _ => none, .fwd)
  fuel := 0
  start := simStartC G
  resume s o := SPComp.pure ((s.1, s.2.1, .fwd), .inr (simOut s.2.2 o))
  finish s o := SPComp.pure ((s.1, s.2.1, .fwd), simOut s.2.2 o)
  start_noFail s e := (simStartC_pureNF G s e).2
  resume_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  finish_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _

/-- **Opacity of the simulator with the completion at a delivered prekey**: its state and its
decisions depend on its events and not on the answers of `F_AKE` on its honest port. -/
theorem simProtC_opaque : (simProtC (K := K) G).Opaque cView subView := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e _ rfl rfl
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, stepRel_refl _⟩)
      (rHoare_refl _)
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, simOut_rel _ ho⟩
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, simOut_rel _ ho⟩

/-- **The X3DH simulator with the completion at a delivered prekey** as a bundled opaque
simulator. -/
noncomputable def x3dhSimC :
    Simulator (CEv W) (OOut S W K) (FEv K) (FOut K) cView subView :=
  Simulator.ofMultiHybrid (simProtC G) (simProtC_opaque G)

end SimC

/-! ## The simulator -/

section JointSim

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K]

/-- **The simulator of X3DH with a joint identity and signing key**: the layer of the
signatures, with the Schnorr Σ-protocol at `ofDHGroup G` and the public keys of
`x3dhJointAlg G`, running over the X3DH simulator with the completion at a delivered prekey. -/
noncomputable def x3dhJointSim (G : DHGroup S W) :
    Simulator (JEv (schnorrSigma (GroupParam.ofDHGroup G)))
      (JOut (schnorrSigma (GroupParam.ofDHGroup G)) K) (FEv K) (FOut K) (jView _) subView :=
  (Simulator.ofMultiHybrid (sigLayerJ _ (x3dhJointAlg G).pub)
    (sigLayerJ_opaque _ (x3dhJointAlg G).pub)).comp (x3dhSimC (S := S) (W := W) G)

/-- The simulator over a subroutine system is the layer over `x3dhSimC G` over it. -/
theorem x3dhJointSim_withSub (G : DHGroup S W) {τ : Type} (X : Sys τ (FEv K) (FOut K)) :
    (x3dhJointSim (K := K) G).withSub X =
      (sigLayerJH (schnorrSigma (GroupParam.ofDHGroup G)) (x3dhJointAlg G).pub).withSub
        ((x3dhSimC (S := S) (W := W) G).withSub X) :=
  MultiHybrid.ofHybrid_withSub _ _

end JointSim

/-! ## Forwarding -/

section Plug

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] [Fintype P.Wit] [Nonempty P.Wit]
  {K : Type} [Fintype K] [Nonempty K]

/-- **The joint real protocol is the forwarding protocol against its oracle**, at distance
`0`. -/
theorem joint_plug_realizes (A : JointSigAKEAlg P) :
    Realizes (x3dhJointRealOf (K := K) P A)
      ((OProt.oracle (Q := JEv P) (A := JOut P K)).plug (jointO P A.toAKEAlg) (jInit P))
      (fun _ _ => 0) :=
  plug_realizes (jointGame P A) () (fun _ => rfl) rfl

/-- **The layer over the real X3DH protocol with the completion at a delivered prekey is the
forwarding protocol against the filtered world**, at distance `0`. -/
theorem jointLayer_plug_realizes (A : AKEAlg P.Wit P.Stmt) :
    Realizes ((sigLayerJH P A.pub).withSub ((OProt.oracle (Q := CEv P.Stmt)
        (A := OOut P.Wit P.Stmt K)).plug (X3DHSquareSigned.sigSub A) (realGame A).init))
      ((OProt.oracle (Q := JEv P) (A := JOut P K)).plug (filtJO P A) (jInit P))
      (fun _ _ => 0) :=
  layer_plug_realizes (sigLayerJH P A.pub) _ _ (fun _ _ => rfl) (fun _ _ => rfl) _ _

/-- The advantage of an environment between the joint real protocol and the forwarding protocol
against an oracle `O'` from the initial state is the difference of the probabilities of `true`
of its oracle reduction against `jointO` and `O'`. -/
theorem adv_joint_plug (A : JointSigAKEAlg P)
    (O' : JSt P × RSt P.Wit P.Stmt K → JEv P → PMF (JOut P K × (JSt P × RSt P.Wit P.Stmt K)))
    {ζ : Type} (Z : Env (Strat ζ (JEv P) (JOut P K)) ζ) :
    adv (x3dhJointRealOf P A) ((OProt.oracle (Q := JEv P) (A := JOut P K)).plug O' (jInit P))
        Z =
      absDiff ((OracleAdv.run (jointO P A.toAKEAlg) (OProt.oracle.reduction Z) (jInit P)).map
          Prod.fst true)
        ((OracleAdv.run O' (OProt.oracle.reduction Z) (jInit P)).map Prod.fst true) := by
  rw [adv_eq, x3dhJointRealOf, OProt.prTrue_view_sys, OProt.prTrue_view_plug]
  simp only [KeyedGame.accept, jointGame, PMF.pure_bind]

end Plug

end CatCrypt.Crypto.AKE.X3DHSquare

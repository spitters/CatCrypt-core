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

**Simulator.** `x3dhJointSim G` is the layer `sigLayerJ` over `x3dhSim G`. The layer reads
`IK_q` and `SPK_q` through `pub q`, answers `sigPub q` with the signature of the simulated
signing oracle `FiatShamirROM.simStep IK_q`, which programs the table of `q`, and passes an
injection on as `complete sid a` when the signature verifies and the prekey is the one it
signed; it passes `pub q` otherwise. It holds no secret key. The layer over the real X3DH state
machine is the filtered world `filtJO A`.

## Main definitions

* `JointSigAKEAlg P` — the algorithms of an AKE with a Σ-protocol for the key relation
* `x3dhJointAlg G` — X3DH over `G` with Schnorr as the key Σ-protocol
* `JSigEv`, `JSigOut`, `JEv`, `JOut`, `jView` — the events and outputs of the joint interface
* `JSt`, `signAt`, `hashAt`, `jPre`, `jPost` — the layer of the signatures
* `jointOWith`, `jointO`, `simSignO`, `filtJO` — the real protocol, with simulated signatures,
  and the filtered world
* `jointGame`, `x3dhJointRealOf` — the real protocol as a system
* `sigLayerJH`, `sigLayerJ`, `x3dhJointSim` — the layer as a hybrid, and the simulator

## Main results

* `sigLayerJ_opaque` — the layer reads no answer of the honest port of its subroutine
* `joint_plug_realizes`, `jointLayer_plug_realizes` — the real protocol and the layer over the
  real X3DH protocol as forwarding protocols against oracles, at distance `0`
* `adv_joint_plug` — the advantage against a forwarding protocol as an oracle-run difference
* `x3dhJointSim_withSub` — the simulator over a subroutine is the layer over `x3dhSim`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.OracleForking
open CatCrypt.Examples
open CatCrypt.Crypto.AKE.X3DHSquareSigned (completeSig layO plug_realizes layer_plug_realizes)
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
prekey and signature of each party that signed, the peer of each session, and the phase. -/
structure JSt where
  /-- The tables of the random oracle of each party, with the flag of the game. -/
  tabs : PartyId → FSt P
  /-- The identity key, the signed prekey and the signature of a party, once signed. -/
  sigs : PartyId → Option (P.Stmt × P.Stmt × Option (P.Com × P.Resp))
  /-- The peer of a session. -/
  peers : Inst → Option PartyId
  /-- The phase. -/
  ph : JPh P

/-- The initial state of the layer. -/
def JSt.init : JSt P :=
  ⟨fun _ => (Protocol.Tables.empty, false), fun _ => none, fun _ => none, .hon⟩

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

/-- **The event of the state machine** for an event of the joint interface. `sigPub q` and
`sigHash q k` read the keys of `q` by `pub q`; an injection queries the random oracle of the
peer at the point of the verifier and becomes `complete` when the layer accepts it (`accJ`),
and `pub q` otherwise. -/
noncomputable def jPre (l : JSt P) : JEv P → PMF (JSt P × OEv P.Stmt)
  | .inl (.newSession sid pid peer role) =>
    PMF.pure ({ notePeerJ P l (sid, pid) peer with ph := .hon },
      .inl (.newSession sid pid peer role))
  | .inl (.getKey sid pid) => PMF.pure ({ l with ph := .hon }, .inl (.getKey sid pid))
  | .inr (.inl a) => PMF.pure ({ l with ph := .adv }, .inr a)
  | .inr (.inr (.sigPub q)) => PMF.pure ({ l with ph := .sign q }, .inr (.pub q))
  | .inr (.inr (.sigHash q k)) => PMF.pure ({ l with ph := .hash q k }, .inr (.pub q))
  | .inr (.inr (.inject sid pid spk σ)) =>
    match l.peers (sid, pid) with
    | none => PMF.pure ({ l with ph := .inj }, .inr .idle)
    | some q => (hashAt P (fun s k => hashStep s.1 s.2 k) l q (σ.1, spk)).map fun r =>
      ({ r.2 with ph := .inj },
        if accJ P l q spk σ r.1 then .inr (.complete sid pid) else .inr (.pub q))

/-- **The answer of the layer** to an answer of the state machine: forward it, sign the prekey
of the answer to `pub q` with the simulated signing oracle `FiatShamirROM.simStep` at the
identity key of the answer, answer a hash query with it, or acknowledge. -/
noncomputable def jPost (l : JSt P) (o : OOut P.Wit P.Stmt K) : PMF (JSt P × JOut P K) :=
  match l.ph, o with
  | .hon, .inl h => PMF.pure (l, .inl h)
  | .adv, .inr a => PMF.pure (l, .inr (.inl a))
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

/-- **The filtered world**: the layer of the signatures over the real X3DH state machine. -/
noncomputable def filtJO (A : AKEAlg P.Wit P.Stmt) :
    JSt P × RSt P.Wit P.Stmt K → JEv P → PMF (JOut P K × (JSt P × RSt P.Wit P.Stmt K)) :=
  layO (jPre P) (X3DHSquareSigned.realStep A) (jPost P)

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

/-- **The layer of the signatures as a one-call hybrid** over the X3DH interface. -/
noncomputable def sigLayerJH :
    Hybrid (JSt P) (JEv P) (JOut P K) (OEv P.Stmt) (OOut P.Wit P.Stmt K) where
  init := JSt.init P
  pre l e := liftPMF (jPre P l e)
  post l o := liftPMF (jPost P l o)
  pre_noFail _ _ := liftPMF_noFail _
  post_noFail _ _ := liftPMF_noFail _

/-- **The layer of the signatures as a multi-call simulator**, one call per activation. -/
noncomputable def sigLayerJ :
    MultiHybrid (JSt P) (JEv P) (JOut P K) (OEv P.Stmt) (OOut P.Wit P.Stmt K) :=
  MultiHybrid.ofHybrid (sigLayerJH P)

/-- **The unwinding condition of the layer** for the equality of states: it reads no honest
answer of its subroutine. -/
theorem sigLayerJ_opaque : (sigLayerJ P (K := K)).Opaque (jView P) outerView := by
  have hrefl : ∀ g : OEv P.Stmt, (outerView (S := P.Wit) (K := K)).ev g g := by
    rintro (h | a)
    · exact Sum.LiftRel.inl rfl
    · exact Sum.LiftRel.inr rfl
  have houtRefl : ∀ o : JOut P K, (jView P).out o o := by
    rintro (h | a)
    · exact Sum.LiftRel.inl trivial
    · exact Sum.LiftRel.inr rfl
  have hdecRefl : ∀ d : OEv P.Stmt ⊕ JOut P K,
      (jView P).StepRel (outerView (S := P.Wit) (K := K)) d d := by
    rintro (g | o)
    · exact hrefl g
    · exact houtRefl o
  have hpost : ∀ (l : JSt P) (o o' : OOut P.Wit P.Stmt K), outerView.out o o' →
      rHoare eqPre (liftPMF (jPost P l o)) (liftPMF (jPost P l o'))
        (fun r h r' h' => h = h' ∧ r.1 = r'.1 ∧ (jView P).out r.2 r'.2) := by
    intro l o o' ho
    cases ho with
    | inl _ =>
      rcases l with ⟨tb, sg, pe, ph⟩
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
      (a := (r.1, (Sum.inr r.2 : OEv P.Stmt ⊕ JOut P K)))
      (b := (r'.1, (Sum.inr r'.2 : OEv P.Stmt ⊕ JOut P K)))
      (Ψ := fun r h r' h' => h = h' ∧ r.1 = r'.1 ∧
        (jView P).StepRel (outerView (S := P.Wit) (K := K)) r.2 r'.2)
      (fun _ _ hh => ⟨hh.1, hh.2.1, hh.2.2⟩) h₁ h₂ hp
  · rintro s _ o o' rfl ho
    exact hpost s o o' ho

variable {S W : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K]

/-- **The simulator of X3DH with a joint identity and signing key**: the layer of the
signatures, with the Schnorr Σ-protocol at `ofDHGroup G`, running over the X3DH simulator. -/
noncomputable def x3dhJointSim (G : DHGroup S W) :
    Simulator (JEv (schnorrSigma (GroupParam.ofDHGroup G)))
      (JOut (schnorrSigma (GroupParam.ofDHGroup G)) K) (FEv K) (FOut K) (jView _) subView :=
  (Simulator.ofMultiHybrid (sigLayerJ _) (sigLayerJ_opaque _)).comp (x3dhSim (S := S) (W := W) G)

/-- The simulator over a subroutine system is the layer over `x3dhSim G` over it. -/
theorem x3dhJointSim_withSub (G : DHGroup S W) {τ : Type} (X : Sys τ (FEv K) (FOut K)) :
    (x3dhJointSim (K := K) G).withSub X =
      (sigLayerJH (schnorrSigma (GroupParam.ofDHGroup G))).withSub
        ((x3dhSim (S := S) (W := W) G).withSub X) :=
  MultiHybrid.ofHybrid_withSub _ _

end Sim

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

/-- **The layer over the real X3DH protocol is the forwarding protocol against the filtered
world**, at distance `0`. -/
theorem jointLayer_plug_realizes (A : AKEAlg P.Wit P.Stmt) :
    Realizes ((sigLayerJH P).withSub ((OProt.oracle (Q := OEv P.Stmt)
        (A := OOut P.Wit P.Stmt K)).plug ((realGame A).oracle ()) (realGame A).init))
      ((OProt.oracle (Q := JEv P) (A := JOut P K)).plug (filtJO P A) (jInit P))
      (fun _ _ => 0) :=
  layer_plug_realizes (sigLayerJH P) _ _ (fun _ _ => rfl) (fun _ _ => rfl) _ _

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

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareGDH
public import CatCryptCore.Crypto.Signatures.EUFCMAPMF
public import CatCryptCore.Crypto.UCTransparentHybrid
public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.OracleSimulation

/-!
# X3DH with signed prekeys against the authenticated key-exchange functionality

The square of `CatCryptCore.Crypto.AKE.X3DHSquare` takes the public keys of a party as
authentic. Here the adversary delivers the signed prekey of the responder to the initiator, and
the initiator accepts a delivered prekey only when its signature verifies under the verification
key of the responder.

**Algorithms.** `SigAKEAlg S W VK SK Sig` extends the record `AKEAlg S W` by a signature scheme
`sig : PSigScheme W VK SK Sig` on public keys. X3DH over a group `G` with the signature scheme
`Sg` is `x3dhSigAlg G Sg`.

**Real protocol.** `x3dhSigRealOf A` runs the real protocol of `A.toAKEAlg` (`realGame`) with,
in addition:
* every party `q` has a signing key pair drawn from the key distribution of `A.sig` at its first
  use; `sigPub q` answers the verification key of `q` and a signature under it on the signed
  prekey of `q`;
* `inject sid a spk σ` delivers the prekey `spk` with the signature `σ` to the initiator `a` of
  `sid`: when `σ` verifies on `spk` under the verification key of the peer of the session, the
  initiator completes with `spk` in place of the signed prekey of its peer (`completeSig`), and
  the injection is otherwise refused.
The identity keys and the one-time prekeys stay authentic, and corruption reveals the
Diffie–Hellman secrets of a party and not its signing key.

The protocol is a one-call layer `layO` over a step of the X3DH state machine: `layPre` records
the peer of a new session, draws signing keys and checks a delivered signature, the state
machine runs one event, and `layPost` signs the prekey answered by `pub q`.

**Simulator.** `x3dhSigSim G Sg` is the layer `sigLayer Sg` running over `x3dhSim G`. The layer
draws the signing keys itself, answers `sigPub q` with a signature on the prekey that the X3DH
simulator answers on `pub q`, and passes a delivered prekey on as `complete sid a` when its
signature verifies and the prekey is the one it signed for the peer; it passes `idle` otherwise.

**Results.**
1. *Filtered world.* `filtO` is the layer over the real X3DH state machine; the layer over the
   real protocol realizes it at distance `0` (`layer_plug_realizes`).
2. *Up to forgery.* The signed real world and the filtered world agree on every transition but an
   injection whose signature verifies on a prekey that the layer did not sign for the peer
   (`realBad`), when the layer state matches the real state (`Inv`). The advantage of an oracle
   adversary between them is at most the probability of that transition.
3. *Forgery.* For each party `p` of a finite set `P` that names every session of the adversary,
   the forger `forgeRed A p B` runs `B` against the filtered world with the challenge
   verification key in place of the key of `p` and the signing oracle in place of its signing
   key, and outputs the first forbidden injection at `p`; the transition has at most the EUF-CMA
   advantage of `forgeRed A p B` as probability (`flag_le_eufcma`).
4. *Square.* With `x3dh_realizesSim_gapDH` under the layer (`Hybrid.adv_withSub`), the signed
   X3DH protocol realizes `F_AKE` behind `x3dhSigSim` with bound the sum of the EUF-CMA advantages
   of the forgers and the gap Diffie–Hellman bound at the environment reduced through the layer
   (`x3dh_signed_realizesSim`).

## Main definitions

* `SigAKEAlg`, `x3dhSigAlg`: the algorithms with a signature scheme on the signed prekeys.
* `SigEv`, `SigOut`, `SEv`, `SOut`: the events and outputs of the signed interface.
* `LSt`, `layPre`, `layPost`, `layO`: the layer of the signatures.
* `completeSig`, `sigO`, `sigGame`, `x3dhSigRealOf`: the signed real protocol.
* `filtO`: the filtered world.
* `sigLayerH`, `sigLayer`, `x3dhSigSim`: the layer as a hybrid, and the simulator.
* `forgeRed`: the forger of a party.
* `sigBound`: the bound of the signatures.

## Main results

* `layer_plug_realizes`, `plug_realizes`: one-call layers over oracle systems.
* `x3dh_signed_realizesSim`: X3DH with signed prekeys realizes `F_AKE` behind `x3dhSigSim`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquareSigned

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.Assumptions CatCrypt.Crypto.Signatures
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt sampleFrom_ofPMF_eq_liftPMF PureNF PureNF.map)
open CatCrypt.Crypto.UCCoupling (realizes_symm)
open PubView (eqView)
open scoped ENNReal

/-! ## The algorithms -/

/-- **The algorithms of X3DH with signed prekeys**: the algorithms of the key exchange and a
signature scheme `sig` on public keys, under which every party signs its signed prekey. -/
structure SigAKEAlg (S W VK SK Sig : Type) extends AKEAlg S W where
  /-- The signature scheme of the signed prekeys. -/
  sig : PSigScheme W VK SK Sig

/-- **X3DH over the group `G` with the signature scheme `Sg`** on the signed prekeys. -/
abbrev x3dhSigAlg {S W VK SK Sig : Type} [Field S] (G : DHGroup S W)
    (Sg : PSigScheme W VK SK Sig) : SigAKEAlg S W VK SK Sig :=
  { toAKEAlg := x3dhAlg G, sig := Sg }

/-! ## The signed interface -/

/-- The events of the signatures on the adversary port. -/
inductive SigEv (W Sig : Type) where
  /-- Read the verification key of the party `pid` and a signature on its signed prekey. -/
  | sigPub (pid : PartyId)
  /-- Deliver the prekey `spk` with the signature `σ` to the initiator `pid` of `sid`. -/
  | inject (sid : SessionId) (pid : PartyId) (spk : W) (σ : Sig)

/-- The outputs of the signatures on the adversary port. -/
inductive SigOut (VK Sig : Type) where
  /-- Acknowledgement. -/
  | ack
  /-- A verification key and a signature. -/
  | sigPub (vk : VK) (σ : Sig)

/-- The events of the signed interface. -/
abbrev SEv (W Sig : Type) := HEv ⊕ (RAEv W ⊕ SigEv W Sig)

/-- The outputs of the signed interface. -/
abbrev SOut (S W K VK Sig : Type) := HOut K ⊕ (ROut S W K ⊕ SigOut VK Sig)

/-- The view of the signed interface: equal events, any two honest outputs, equal adversary
outputs. -/
abbrev sigView {S W K VK Sig : Type} : PubView (SEv W Sig) (SOut S W K VK Sig) :=
  keHonView.sum eqView

/-! ## The layer of the signatures -/

/-- What the layer does with the answer of the state machine. -/
inductive LPh where
  /-- Forward an answer of the honest port. -/
  | hon
  /-- Forward an adversary answer. -/
  | adv
  /-- Sign the prekey of the party `q` in the answer to `pub q`. -/
  | sign (q : PartyId)
  /-- Acknowledge a delivery. -/
  | inj

/-- The state of the layer: the signing key pairs of the parties, once drawn, the prekey signed
for each party, the peer of each session, and the phase. -/
structure LSt (W VK SK : Type) where
  /-- The signing key pair of a party, once drawn. -/
  keys : PartyId → Option (VK × SK)
  /-- The prekey signed for a party. -/
  signed : PartyId → Option W
  /-- The peer of a session. -/
  peers : Inst → Option PartyId
  /-- The phase. -/
  ph : LPh

section Layer

variable {S W K VK SK Sig : Type}

/-- The initial state of the layer. -/
def LSt.init : LSt W VK SK := ⟨fun _ => none, fun _ => none, fun _ => none, .hon⟩

/-- The signing key pair of the party `q`, drawn from `D q` at its first use. -/
noncomputable def keyAt (D : PartyId → PMF (VK × SK)) (l : LSt W VK SK) (q : PartyId) :
    PMF ((VK × SK) × LSt W VK SK) :=
  match l.keys q with
  | some kp => PMF.pure (kp, l)
  | none => (D q).map fun kp => (kp, { l with keys := Function.update l.keys q (some kp) })

/-- The layer state with the peer `peer` of the session `x`, when `x` has none. -/
def notePeer (l : LSt W VK SK) (x : Inst) (peer : PartyId) : LSt W VK SK :=
  if (l.peers x).isSome then l else { l with peers := Function.update l.peers x (some peer) }

/-- **The event of the state machine** for an event of the signed interface, with the signing
keys drawn from `D` and the signatures of `Sg`. An injection whose signature verifies under the
key of the peer and that `acc` accepts becomes `inj x spk`, and `idle` otherwise; the other
events become their events of the state machine through `ι`. -/
noncomputable def layPre {EG : Type} (D : PartyId → PMF (VK × SK))
    (Sg : PSigScheme W VK SK Sig) (ι : OEv W → EG) (acc : LSt W VK SK → PartyId → W → Bool)
    (inj : Inst → W → EG) (l : LSt W VK SK) : SEv W Sig → PMF (LSt W VK SK × EG)
  | .inl (.newSession sid pid peer role) =>
    PMF.pure ({ notePeer l (sid, pid) peer with ph := .hon },
      ι (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => PMF.pure ({ l with ph := .hon }, ι (.inl (.getKey sid pid)))
  | .inr (.inl a) => PMF.pure ({ l with ph := .adv }, ι (.inr a))
  | .inr (.inr (.sigPub q)) => PMF.pure ({ l with ph := .sign q }, ι (.inr (.pub q)))
  | .inr (.inr (.inject sid pid spk σ)) =>
    match l.peers (sid, pid) with
    | none => PMF.pure ({ l with ph := .inj }, ι (.inr .idle))
    | some q => (keyAt D l q).map fun p =>
      ({ p.2 with ph := .inj },
        if Sg.verify p.1.1 spk σ && acc l q spk then inj (sid, pid) spk else ι (.inr .idle))

/-- **The answer of the layer** to an answer of the state machine: forward it, sign the prekey
of `pub q` with the key of `q` and record it as signed for `q`, or acknowledge. -/
noncomputable def layPost (D : PartyId → PMF (VK × SK)) (Sg : PSigScheme W VK SK Sig)
    (l : LSt W VK SK) (o : OOut S W K) : PMF (LSt W VK SK × SOut S W K VK Sig) :=
  match l.ph, o with
  | .hon, .inl h => PMF.pure (l, .inl h)
  | .adv, .inr a => PMF.pure (l, .inr (.inl a))
  | .sign q, .inr (.pub _ spk) => (keyAt D l q).bind fun p => (Sg.sign p.1.2 spk).map fun σ =>
      ({ p.2 with signed := Function.update p.2.signed q (some spk) },
        .inr (.inr (.sigPub p.1.1 σ)))
  | _, _ => PMF.pure (l, .inr (.inr .ack))

/-- **A one-call layer over an oracle**: `pre` chooses the event of the oracle, the oracle steps,
and `post` gives the answer. -/
noncomputable def layO {L T E O EG OG : Type} (pre : L → E → PMF (L × EG))
    (sub : T → EG → PMF (OG × T)) (post : L → OG → PMF (L × O)) (t : L × T) (e : E) :
    PMF (O × (L × T)) :=
  (pre t.1 e).bind fun a => (sub t.2 a.2).bind fun q => (post a.1 q.1).map fun r =>
    (r.2, (r.1, q.2))

/-- The layer accepts a prekey for `q` when it signed it for `q`. -/
def accSigned [DecidableEq W] (l : LSt W VK SK) (q : PartyId) (spk : W) : Bool :=
  l.signed q == some spk

/-- The event of the state machine for an accepted delivery at `x`: the completion of `x`. -/
def injComplete (x : Inst) (_ : W) : OEv W := .inr (.complete x.1 x.2)

end Layer

/-! ## The signed real protocol and the filtered world -/

section Real

variable {S W K VK SK Sig : Type} [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K]
  [Nonempty K]

/-- **The completion of the initiator `x` with the delivered prekey `spk`**: the completion of
`completeStep` with `spk` in place of the signed prekey of the peer. -/
noncomputable def completeSig (A : AKEAlg S W) (s : RSt S W K) (x : Inst) (spk : W) :
    PMF (ROut S W K × RSt S W K) :=
  match s.st.recs x, s.eph x with
  | some r, some ek =>
    match opkOf s x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        (ltAt s x.2).bind fun la => (ltAt la.2 r.peer).bind fun lb =>
          (roAt lb.2.ro (A.initInp x.1 x.2 r.peer la.1.1 ek (A.pub lb.1.1) spk
            (A.pub opk))).map fun p => (.ack, keyed lb.2 x r p.1 p.2)
      else PMF.pure (.ack, s)
    | none => PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- A step of the real X3DH state machine: the oracle of `realGame A`. -/
noncomputable def realStep (A : AKEAlg S W) (s : RSt S W K) (g : OEv W) :
    PMF (OOut S W K × RSt S W K) :=
  (realGame A).oracle () s g

/-- The state machine of the signed real protocol: the events of `realGame`, and the completion
with a delivered prekey. -/
noncomputable def sigSub (A : AKEAlg S W) (s : RSt S W K) :
    OEv W ⊕ (Inst × W) → PMF (OOut S W K × RSt S W K)
  | .inl e => realStep A s e
  | .inr p => (completeSig A s p.1 p.2).map fun q => (.inr q.1, q.2)

/-- The signing keys of the protocol: the key distribution of the signature scheme. -/
noncomputable def keyD (A : SigAKEAlg S W VK SK Sig) : PartyId → PMF (VK × SK) :=
  fun _ => A.sig.keyDist

/-- **A step of the signed real protocol**: an injection completes with the delivered prekey when
its signature verifies under the key of the peer. -/
noncomputable def sigO (A : SigAKEAlg S W VK SK Sig) :
    LSt W VK SK × RSt S W K → SEv W Sig → PMF (SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) :=
  layO (layPre (keyD A) A.sig .inl (fun _ _ _ => true) fun x spk => .inr (x, spk))
    (sigSub A.toAKEAlg) (layPost (keyD A) A.sig)

/-- **The signed real game**: a trivial key, and the oracle is the step of the signed real
protocol. -/
noncomputable def sigGame (A : SigAKEAlg S W VK SK Sig) :
    KeyedGame (SEv W Sig) (SOut S W K VK Sig) where
  Key := Unit
  State := LSt W VK SK × RSt S W K
  keyDist := PMF.pure ()
  oracle _ := sigO A
  init := (LSt.init, rInit)

/-- **The real protocol of X3DH with signed prekeys** as a system: each event is a query to the
oracle of `sigGame A`. -/
noncomputable def x3dhSigRealOf (A : SigAKEAlg S W VK SK Sig) :=
  (OProt.oracle (Q := SEv W Sig) (A := SOut S W K VK Sig)).sys (sigGame A)

/-- **The filtered world** with the signing keys drawn from `D`: the layer over the real X3DH
state machine, which passes an injection on as `complete` only when the layer signed the prekey
for the peer. -/
noncomputable def filtO (A : SigAKEAlg S W VK SK Sig) (D : PartyId → PMF (VK × SK)) :
    LSt W VK SK × RSt S W K → SEv W Sig → PMF (SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) :=
  layO (layPre D A.sig id accSigned injComplete) (realStep A.toAKEAlg)
    (layPost D A.sig)

end Real

/-! ## The layer as a simulator -/

section Sim

variable {S W K VK SK Sig : Type} [DecidableEq W]

/-- **The layer of the signatures as a one-call hybrid** over the X3DH interface. -/
noncomputable def sigLayerH (Sg : PSigScheme W VK SK Sig) :
    Hybrid (LSt W VK SK) (SEv W Sig) (SOut S W K VK Sig) (OEv W) (OOut S W K) where
  init := LSt.init
  pre l e := liftPMF (layPre (fun _ => Sg.keyDist) Sg id accSigned injComplete l e)
  post l o := liftPMF (layPost (fun _ => Sg.keyDist) Sg l o)
  pre_noFail _ _ := liftPMF_noFail _
  post_noFail _ _ := liftPMF_noFail _

/-- **The layer of the signatures as a multi-call simulator**, one call per activation. -/
noncomputable def sigLayer (Sg : PSigScheme W VK SK Sig) :
    MultiHybrid (LSt W VK SK) (SEv W Sig) (SOut S W K VK Sig) (OEv W) (OOut S W K) :=
  MultiHybrid.ofHybrid (sigLayerH Sg)

/-- **The unwinding condition of the layer** for the equality of states: it reads no honest
answer of its subroutine. -/
theorem sigLayer_opaque (Sg : PSigScheme W VK SK Sig) :
    (sigLayer (S := S) (K := K) Sg).Opaque sigView outerView := by
  have hrefl : ∀ g : OEv W, (outerView (S := S) (K := K)).ev g g := by
    rintro (h | a)
    · exact Sum.LiftRel.inl rfl
    · exact Sum.LiftRel.inr rfl
  have houtRefl : ∀ o : SOut S W K VK Sig, (sigView (S := S) (W := W) (K := K)).out o o := by
    rintro (h | a)
    · exact Sum.LiftRel.inl trivial
    · exact Sum.LiftRel.inr rfl
  have hdecRefl : ∀ d : OEv W ⊕ SOut S W K VK Sig,
      (sigView (S := S) (W := W) (K := K)).StepRel (outerView (S := S) (K := K)) d d := by
    rintro (g | o)
    · exact hrefl g
    · exact houtRefl o
  have hpost : ∀ (l : LSt W VK SK) (o o' : OOut S W K), outerView.out o o' →
      rHoare eqPre (liftPMF (layPost (fun _ => Sg.keyDist) Sg l o))
        (liftPMF (layPost (fun _ => Sg.keyDist) Sg l o'))
        (fun r h r' h' => h = h' ∧ r.1 = r'.1 ∧ sigView.out r.2 r'.2) := by
    intro l o o' ho
    cases ho with
    | inl _ =>
      rcases l with ⟨k, sg, pe, ph⟩
      cases ph <;> simp only [layPost, ← liftPMF_pure] <;>
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
    simp only [sigLayer, MultiHybrid.ofHybrid, sigLayerH, SPComp.map]
    refine rHoare_bind (hpost s o o' ho) fun r r' => ?_
    intro h₁ h₂ hp
    exact rHoare_ret (Φ := fun h h' => h = h' ∧ r.1 = r'.1 ∧ sigView.out r.2 r'.2)
      (a := (r.1, (Sum.inr r.2 : OEv W ⊕ SOut S W K VK Sig)))
      (b := (r'.1, (Sum.inr r'.2 : OEv W ⊕ SOut S W K VK Sig)))
      (Ψ := fun r h r' h' => h = h' ∧ r.1 = r'.1 ∧ sigView.StepRel outerView r.2 r'.2)
      (fun _ _ hh => ⟨hh.1, hh.2.1, hh.2.2⟩) h₁ h₂ hp
  · rintro s _ o o' rfl ho
    exact hpost s o o' ho

variable [Field S] [Fintype S] [Fintype K] [Nonempty K] [Inhabited K]

/-- **The simulator of X3DH with signed prekeys**: the layer of the signatures running over the
X3DH simulator. -/
noncomputable def x3dhSigSim (G : DHGroup S W) (Sg : PSigScheme W VK SK Sig) :
    Simulator (SEv W Sig) (SOut S W K VK Sig) (FEv K) (FOut K) sigView subView :=
  (Simulator.ofMultiHybrid (sigLayer Sg) (sigLayer_opaque Sg)).comp (x3dhSim G)

end Sim

/-! ## One-call layers over oracle systems -/

section Plug

variable {L T E O EG OG : Type}

/-- A step of the forwarding protocol against a stateful oracle is the lift of a step of the
oracle. -/
theorem plugStep_oracle (orc : T → EG → PMF (OG × T)) (t : T) (g : EG) :
    (OProt.oracle (Q := EG) (A := OG)).plugStep orc ((), t) g =
      liftPMF ((orc t g).map fun y => (((), y.2), y.1)) := by
  simp only [OProt.plugStep, OProt.oracle, OracleAdv.run_query, OracleAdv.run_ret,
    sampleFrom_ofPMF_eq_liftPMF, liftPMF_bind_pure, PMF.map_bind]
  congr 1
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- **The oracle system of a game with a trivial key is the forwarding protocol against its
oracle**, at distance `0`. -/
theorem plug_realizes (G : KeyedGame EG OG) (k₀ : G.Key) (hk : ∀ k, k = k₀)
    (hμ : G.keyDist = PMF.pure k₀) :
    Realizes ((OProt.oracle (Q := EG) (A := OG)).sys G)
      ((OProt.oracle (Q := EG) (A := OG)).plug (G.oracle k₀) G.init) (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ _ (fun u => u.2) rfl ?_
  rintro ⟨o, ⟨⟩, t⟩ e
  rcases o with _ | k
  · simp only [OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed, ↓reduceIte, hμ,
      sampleFrom_ofPMF_eq_liftPMF, ← liftPMF_pure, OProt.plug, plugStep_oracle,
      liftPMF_bind_pure, SPComp.map]
    rw [SPComp.pure_bind, liftPMF_bind_pure, PMF.map_comp, PMF.map_comp]
    rfl
  · obtain rfl := hk k
    simp only [OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed, OProt.plug,
      plugStep_oracle, liftPMF_bind_pure, SPComp.map, PMF.map_comp]
    rfl

/-- **A one-call layer over the forwarding protocol against an oracle** is the forwarding
protocol against the layered oracle `layO`, at distance `0`. -/
theorem layer_plug_realizes (H : Hybrid L E O EG OG) (pre : L → E → PMF (L × EG))
    (post : L → OG → PMF (L × O)) (hpre : ∀ l e, H.pre l e = liftPMF (pre l e))
    (hpost : ∀ l o, H.post l o = liftPMF (post l o)) (orc : T → EG → PMF (OG × T)) (s₀ : T) :
    Realizes (H.withSub ((OProt.oracle (Q := EG) (A := OG)).plug orc s₀))
      ((OProt.oracle (Q := E) (A := O)).plug (layO pre orc post) (H.init, s₀))
      (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ _ (fun u => ((), (u.1, u.2.2))) rfl ?_
  rintro ⟨l, ⟨⟩, t⟩ e
  simp only [Hybrid.withSub, OProt.plug, plugStep_oracle, hpre, hpost, liftPMF_bind_liftPMF,
    liftPMF_bind_pure, SPComp.map]
  congr 1
  simp [layO, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

end Plug

/-! ## The forger -/

section Forger

variable {S W K VK SK Sig : Type} [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K]
  [Nonempty K]

/-- The event of the state machine chosen by the forger of `p` with the challenge key `pk`: an
injection at a session whose peer is `p` is checked under `pk`; every other event is chosen as
`layPre` chooses it. -/
noncomputable def preF (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (l : LSt W VK SK) (e : SEv W Sig) : PMF (LSt W VK SK × OEv W) :=
  match e with
  | .inr (.inr (.inject sid pid spk σ)) =>
    if l.peers (sid, pid) = some p then
      PMF.pure ({ l with ph := .inj },
        if A.sig.verify pk spk σ && accSigned l p spk then injComplete (sid, pid) spk
        else .inr .idle)
    else layPre (keyD A) A.sig id accSigned injComplete l e
  | _ => layPre (keyD A) A.sig id accSigned injComplete l e

/-- The answer of the forger of `p` with the challenge key `pk`: the prekey of `pub p` is signed
by a query to the signing oracle; every other answer is given as `layPost` gives it. -/
noncomputable def postF (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (l : LSt W VK SK) (o : OOut S W K) : OracleAdv W Sig (LSt W VK SK × SOut S W K VK Sig) :=
  match l.ph, o with
  | .sign q, .inr (.pub _ spk) =>
    if q = p then
      .query spk fun σ => .ret ({ l with signed := Function.update l.signed p (some spk) },
        .inr (.inr (.sigPub pk σ)))
    else .rand (layPost (keyD A) A.sig l o) .ret
  | _, _ => .rand (layPost (keyD A) A.sig l o) .ret

/-- A step of the filtered world simulated by the forger of `p` with the challenge key `pk`. -/
noncomputable def forgeStep (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) :
    OracleAdv W Sig (SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) :=
  .rand (preF A p pk t.1 e) fun a =>
    .rand (realStep A.toAKEAlg t.2 a.2) fun q =>
      (postF A p pk a.1 q.1).bind fun r => .ret (r.2, (r.1, q.2))

/-- The forgery found at a step: an injection at a session whose peer is `p` with a signature
that verifies under `pk` on a prekey not signed for `p`. -/
noncomputable def forgeryAt (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (l : LSt W VK SK) : SEv W Sig → Option (W × Sig)
  | .inr (.inr (.inject sid pid spk σ)) =>
    if l.peers (sid, pid) = some p ∧ A.sig.verify pk spk σ = true ∧ l.signed p ≠ some spk then
      some (spk, σ)
    else none
  | _ => none

/-- **A simulation that stops at the first output.** The reduction runs the oracle adversary `B`
from the state `t`, answering a query `e` by the oracle tree `step t e`, which returns the answer
and the next state; when `stop t e` is an output `f`, it stops with `f` after the answer is
computed, and when `B` returns, it runs `fin`. The state is a parameter of the reduction, so that
its costed form is derived for every state type. -/
noncomputable def stopRed {σ E A D R Out : Type} (step : σ → E → OracleAdv D R (A × σ))
    (stop : σ → E → Option Out) (fin : OracleAdv D R Out) :
    OracleAdv E A Bool → σ → OracleAdv D R Out
  | .ret _, _ => fin
  | .rand μ k, t => .rand μ fun b => stopRed step stop fin (k b) t
  | .query e k, t => (step t e).bind fun x =>
      match stop t e with
      | some f => .ret f
      | none => stopRed step stop fin (k x.1) x.2

/-- **The loop of the forger** of `p` with the challenge key `pk`: it runs the oracle adversary
`B` against the simulated filtered world and stops at the first forgery; without a forgery it
asks the signing oracle at `m₀` and outputs the answer. It is `stopRed` at the step `forgeStep`,
the forgery `forgeryAt` and the final signing query at `m₀`. -/
noncomputable def forgeLoop (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK) (m₀ : W) :
    OracleAdv (SEv W Sig) (SOut S W K VK Sig) Bool → LSt W VK SK × RSt S W K →
      OracleAdv W Sig (W × Sig) :=
  stopRed (forgeStep A p pk) (fun t e => forgeryAt A p pk t.1 e)
    (.query m₀ fun σ => .ret (m₀, σ))

/-- The initial state of the simulated filtered world. -/
def fInit : LSt W VK SK × RSt S W K := (LSt.init, rInit)

/-- **The forger of the party `p`** against the signature scheme of `A`, for the oracle adversary
`B` of the signed interface: on the verification key `pk` it runs `forgeLoop`. -/
noncomputable def forgeRed (A : SigAKEAlg S W VK SK Sig) (p : PartyId)
    (B : OracleAdv (SEv W Sig) (SOut S W K VK Sig) Bool) (pk : VK) : OracleAdv W Sig (W × Sig) :=
  forgeLoop A p pk (A.pub (Classical.arbitrary S)) B fInit

/-- The events that start sessions only between parties of `P`. -/
def EvInSig (P : Finset PartyId) : SEv W Sig → Prop
  | .inl (.newSession _ pid peer _) => pid ∈ P ∧ peer ∈ P
  | _ => True

/-- `SigNamesIn P B`: on every path, the oracle adversary `B` starts sessions only between
parties of `P`. -/
def SigNamesIn {α : Type} (P : Finset PartyId)
    (B : OracleAdv (SEv W Sig) (SOut S W K VK Sig) α) : Prop :=
  AllQ (EvInSig P) B

open Classical in
/-- **The bound of the signatures** at the oracle adversary `B` and the finite set of parties
`P`: the sum over the parties of `P` of the EUF-CMA advantages of the forgers, when `B` starts
sessions only between parties of `P`, and `⊤` otherwise. -/
noncomputable def sigBound (A : SigAKEAlg S W VK SK Sig) (P : Finset PartyId)
    (B : OracleAdv (SEv W Sig) (SOut S W K VK Sig) Bool) : ℝ≥0∞ :=
  if SigNamesIn P B then
    ∑ p ∈ P, eufcmaAdvantage A.sig.toSigScheme (toEUFAdversary (forgeRed A p B))
  else ⊤

/-! ## Up to forgery -/

/-- The layer state matches the real state: the peer of each session is the peer of its record,
and a prekey signed for a party is the public part of its signed prekey. -/
def Inv (A : SigAKEAlg S W VK SK Sig) (t : LSt W VK SK × RSt S W K) : Prop :=
  (∀ x, t.1.peers x = (t.2.st.recs x).map Rec.peer) ∧
    ∀ q w, t.1.signed q = some w → ∃ v, t.2.lt q = some v ∧ A.pub v.2 = w

/-- The peers of the sessions of the layer state are parties of `P`. -/
def PInv (P : Finset PartyId) (t : LSt W VK SK × RSt S W K) : Prop :=
  ∀ x q, t.1.peers x = some q → q ∈ P

/-- **A forbidden injection at the party `q`**: an injection at a session whose peer is `q`, with
a signature that verifies under the key of `q` after the step, on a prekey that the layer did not
sign for `q`. -/
def BadAt (A : SigAKEAlg S W VK SK Sig) (q : PartyId) (t : LSt W VK SK × RSt S W K)
    (e : SEv W Sig) (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) : Prop :=
  ∃ sid pid spk σ kp, e = .inr (.inr (.inject sid pid spk σ)) ∧ t.1.peers (sid, pid) = some q ∧
    x.2.1.keys q = some kp ∧ A.sig.verify kp.1 spk σ = true ∧ t.1.signed q ≠ some spk

/-- A forbidden injection at some party. -/
def RealBad (A : SigAKEAlg S W VK SK Sig) (t : LSt W VK SK × RSt S W K) (e : SEv W Sig)
    (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) : Prop :=
  ∃ q, BadAt A q t e x

/-- The transitions of the comparison: from a state that violates `Inv`, or forbidden. -/
def Bad₁ (A : SigAKEAlg S W VK SK Sig) (t : LSt W VK SK × RSt S W K) (e : SEv W Sig)
    (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) : Prop :=
  ¬ Inv A t ∨ RealBad A t e x

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `keyed` keeps the peers of the records and the long-term secrets. -/
theorem keyed_recs_peer {T : Type} (s : RStT S K T) (x : Inst) (r : Rec K) (k : K) (ro : T)
    (hr : s.st.recs x = some r) (y : Inst) :
    ((keyed s x r k ro).st.recs y).map Rec.peer = (s.st.recs y).map Rec.peer := by
  simp only [keyed, setRec]
  by_cases hy : y = x
  · subst hy; simp [hr]
  · simp [Function.update_of_ne hy]

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `ltAt` keeps the session records and extends the long-term secrets. -/
theorem ltAt_support {T : Type} (s : RStT S K T) (pid : PartyId) :
    ∀ l ∈ (ltAt s pid).support, l.2.st = s.st ∧ l.2.eph = s.eph ∧ l.2.ro = s.ro ∧
      l.2.lt pid = some l.1 ∧ ∀ q v, s.lt q = some v → l.2.lt q = some v := by
  intro l hl
  unfold ltAt at hl
  split at hl
  · rename_i v hv
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hl
    subst hl
    exact ⟨rfl, rfl, rfl, hv, fun _ _ h => h⟩
  · rename_i hv
    simp only [PMF.support_map, Set.mem_image] at hl
    obtain ⟨v, -, rfl⟩ := hl
    refine ⟨rfl, rfl, rfl, by simp, fun q w h => ?_⟩
    by_cases hq : q = pid
    · subst hq; simp [hv] at h
    · simp [Function.update_of_ne hq, h]

/-- A step of the real X3DH state machine keeps the peers of the records, but for a new session,
and extends the long-term secrets. -/
theorem realO_support (A : AKEAlg S W) (s : RSt S W K) (g : OEv W) :
    ∀ q ∈ (realStep A s g).support,
      (∀ y, (q.2.st.recs y).map Rec.peer =
        match g with
        | .inl (.newSession sid pid peer _) =>
          if y = (sid, pid) ∧ (s.st.recs y).isNone then some peer
          else (s.st.recs y).map Rec.peer
        | _ => (s.st.recs y).map Rec.peer) ∧
      ∀ p v, s.lt p = some v → q.2.lt p = some v := by
  intro q hq
  rcases g with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)) <;>
    simp only [realStep, realGame, realGameK, realHonK, realAdvK, lazyKDF, PMF.support_map,
      Set.mem_image] at hq <;> obtain ⟨p, hp, rfl⟩ := hq
  · split_ifs at hp with hn
    · simp only [PMF.support_bind, PMF.support_map, PMF.support_pure, Set.mem_iUnion,
        Set.mem_image, Set.mem_singleton_iff] at hp
      obtain ⟨y, -, t, rfl, rfl⟩ := hp
      refine ⟨fun z => ?_, fun _ _ h => h⟩
      have hn' : (s.st.recs (sid, pid)).isSome = false := by simpa using hn
      by_cases hz : z = (sid, pid)
      · subst hz; simp [addSession, hn', hn]
      · simp [addSession, hn', hz]
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨fun z => ?_, fun _ _ h => h⟩
      by_cases hz : z = (sid, pid)
      · subst hz; simp [hn]
      · simp [hz]
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨fun _ => rfl, fun _ _ h => h⟩
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨fun _ => rfl, fun _ _ h => h⟩
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨fun _ => ?_, fun _ _ h => h⟩
    simp only [pollStep]
    split <;> rfl
  · obtain ⟨l, hl, rfl⟩ := hp
    obtain ⟨h1, -, -, -, h5⟩ := ltAt_support s pid l hl
    exact ⟨fun _ => by simp [h1], h5⟩
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨fun _ => rfl, fun _ _ h => h⟩
  · unfold corruptRStep at hp
    split_ifs at hp
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨fun _ => rfl, fun _ _ h => h⟩
    · simp only [PMF.support_map, Set.mem_image] at hp
      obtain ⟨l, hl, rfl⟩ := hp
      obtain ⟨h1, -, -, -, h5⟩ := ltAt_support s pid l hl
      exact ⟨fun _ => by simp [corruptStep, h1], h5⟩
  all_goals try unfold completeStepK at hp
  all_goals try unfold sendStepK at hp
  all_goals try (repeat' split at hp)
  all_goals dsimp only
  all_goals first
    | (obtain ⟨_, -, rfl⟩ := hp; exact ⟨fun _ => rfl, fun _ _ h => h⟩)
    | (simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hp
       obtain ⟨la, hla, lb, hlb, k', -, rfl⟩ := hp
       obtain ⟨a1, -, -, -, a5⟩ := ltAt_support _ _ la hla
       obtain ⟨b1, -, -, -, b5⟩ := ltAt_support _ _ lb hlb
       refine ⟨fun y => ?_, fun q v h => b5 _ _ (a5 _ _ h)⟩
       rw [keyed_recs_peer _ _ _ _ _ (by rwa [b1, a1])]
       simp only [b1, a1])
    | grind only [PMF.mem_support_pure_iff]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `keyAt` changes only the keys. -/
theorem keyAt_support (D : PartyId → PMF (VK × SK)) (l : LSt W VK SK) (q : PartyId) :
    ∀ p ∈ (keyAt D l q).support, p.2.signed = l.signed ∧ p.2.peers = l.peers ∧
      p.2.ph = l.ph ∧ p.2.keys q = some p.1 := by
  intro p hp
  unfold keyAt at hp
  split at hp
  · rename_i kp hk
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨rfl, rfl, rfl, hk⟩
  · simp only [PMF.support_map, Set.mem_image] at hp
    obtain ⟨kp, -, rfl⟩ := hp
    exact ⟨rfl, rfl, rfl, by simp⟩

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The answer of the layer keeps the peers, and keeps the signed prekeys but for the prekey of
`pub q` in the phase `sign q`. -/
theorem layPost_support (D : PartyId → PMF (VK × SK)) (Sg : PSigScheme W VK SK Sig)
    (l : LSt W VK SK) (o : OOut S W K) :
    ∀ r ∈ (layPost D Sg l o).support, r.1.peers = l.peers ∧
      (r.1.signed = l.signed ∨ ∃ q ik spk, l.ph = .sign q ∧ o = .inr (.pub ik spk) ∧
        r.1.signed = Function.update l.signed q (some spk)) := by
  intro r hr
  unfold layPost at hr
  split at hr
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr; subst hr; exact ⟨rfl, Or.inl rfl⟩
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr; subst hr; exact ⟨rfl, Or.inl rfl⟩
  · rename_i _ _ q ik spk hph
    simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hr
    obtain ⟨p, hp, σ, -, rfl⟩ := hr
    obtain ⟨h1, h2, -, -⟩ := keyAt_support D l q p hp
    exact ⟨h2, Or.inr ⟨q, ik, spk, hph, rfl, by simp only [h1]⟩⟩
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr; subst hr; exact ⟨rfl, Or.inl rfl⟩

/-- The filtered world keeps `Inv`. -/
theorem inv_filtO (A : SigAKEAlg S W VK SK Sig) (D : PartyId → PMF (VK × SK))
    (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) (ht : Inv A t) :
    ∀ x ∈ (filtO A D t e).support, Inv A x.2 := by
  intro x hx
  obtain ⟨hpe, hsg⟩ := ht
  unfold filtO layO at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨a, ha, hx⟩ := hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨q, hq, hx⟩ := hx
  rw [PMF.support_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨hq1, hq2⟩ := realO_support A.toAKEAlg t.2 a.2 q hq
  obtain ⟨hr1, hr2⟩ := layPost_support D A.sig a.1 q.1 r hr
  -- the signed prekeys when the answer keeps them
  have hkeep : a.1.signed = t.1.signed → r.1.signed = a.1.signed →
      ∀ p w, r.1.signed p = some w → ∃ v, q.2.lt p = some v ∧ A.pub v.2 = w := by
    intro h₁ h₂ p w hw
    rw [h₂, h₁] at hw
    obtain ⟨v, hv, hvw⟩ := hsg p w hw
    exact ⟨v, hq2 p v hv, hvw⟩
  rcases e with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (a' | (q0 | ⟨sid, pid, spk, σ⟩)))
  · simp only [layPre, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    have hs : r.1.signed = (notePeer t.1 (sid, pid) peer).signed := by
      rcases hr2 with h | ⟨_, _, _, h, -⟩
      · exact h
      · exact absurd h (by simp)
    refine ⟨fun y => ?_, hkeep (by unfold notePeer; split <;> rfl) hs⟩
    rw [hr1, hq1 y]
    simp only [notePeer, hpe]
    by_cases hy : y = (sid, pid)
    · subst hy
      cases h : t.2.st.recs (sid, pid) <;> simp [h, hpe]
    · split <;> simp [hy, hpe]
  rotate_left 2
  · -- `sigPub q0`
    simp only [layPre, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    refine ⟨fun y => ?_, ?_⟩
    · rw [hr1, hq1 y]; exact hpe y
    rcases hr2 with h | ⟨q1, ik, spk, hph, ho, h⟩
    · exact hkeep rfl h
    · simp only [LPh.sign.injEq] at hph
      subst hph
      simp only [realStep, realGame, realGameK, realAdvK, id_eq] at hq
      rw [PMF.support_map] at hq
      obtain ⟨_, hq', rfl⟩ := hq
      rw [PMF.support_map] at hq'
      obtain ⟨l, hl, rfl⟩ := hq'
      obtain ⟨-, -, -, hl4, hl5⟩ := ltAt_support t.2 q0 l hl
      simp only [Sum.inr.injEq, ROut.pub.injEq] at ho
      intro p w hw
      rw [h] at hw
      by_cases hp : p = q0
      · subst hp
        simp only [Function.update_self, Option.some.injEq] at hw
        exact ⟨l.1, hl4, by rw [ho.2]; exact hw⟩
      · rw [Function.update_of_ne hp] at hw
        obtain ⟨v, hv, hvw⟩ := hsg p w hw
        exact ⟨v, hl5 p v hv, hvw⟩
  · -- `inject`
    simp only [layPre] at ha
    have ha' : a.1.signed = t.1.signed ∧ a.1.peers = t.1.peers ∧ a.1.ph = .inj ∧
        (a.2 = .inr .idle ∨ a.2 = .inr (.complete sid pid)) := by
      split at ha
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at ha
        subst ha; exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
      · simp only [PMF.support_map, Set.mem_image] at ha
        obtain ⟨p, hp, rfl⟩ := ha
        obtain ⟨h1, h2, -, -⟩ := keyAt_support D t.1 _ p hp
        refine ⟨h1, h2, rfl, ?_⟩
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
    obtain ⟨h1, h2, h3, h4⟩ := ha'
    have hs : r.1.signed = a.1.signed := by
      rcases hr2 with h | ⟨_, _, _, h, -⟩
      · exact h
      · rw [h3] at h; exact absurd h (by simp)
    refine ⟨fun y => ?_, hkeep h1 hs⟩
    rw [hr1, hq1 y, h2]
    rcases h4 with h | h <;> rw [h] <;> exact hpe y
  all_goals
    simp only [layPre, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    have hs : r.1.signed = t.1.signed := by
      rcases hr2 with h | ⟨_, _, _, h, -⟩
      · exact h
      · exact absurd h (by simp)
    refine ⟨fun y => ?_, hkeep rfl hs⟩
    rw [hr1, hq1 y]
    exact hpe y

/-- The filtered world keeps `PInv P` on the events of `EvInSig P`. -/
theorem pinv_filtO (A : SigAKEAlg S W VK SK Sig) (D : PartyId → PMF (VK × SK))
    (P : Finset PartyId) (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) (ht : PInv P t)
    (he : EvInSig P e) : ∀ x ∈ (filtO A D t e).support, PInv P x.2 := by
  intro x hx
  unfold filtO layO at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨a, ha, hx⟩ := hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨q, -, hx⟩ := hx
  rw [PMF.support_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨hr1, -⟩ := layPost_support D A.sig a.1 q.1 r hr
  intro y q0 hy
  change r.1.peers y = some q0 at hy
  rw [hr1] at hy
  rcases e with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (a' | (q1 | ⟨sid, pid, spk, σ⟩)))
  · simp only [layPre, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    simp only [notePeer] at hy
    split at hy
    · exact ht y q0 hy
    · by_cases hyx : y = (sid, pid)
      · subst hyx
        simp only [Function.update_self, Option.some.injEq] at hy
        exact hy ▸ he.2
      · change Function.update t.1.peers (sid, pid) (some peer) y = some q0 at hy
        rw [Function.update_of_ne hyx] at hy
        exact ht y q0 hy
  rotate_left 3
  · simp only [layPre] at ha
    split at ha
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at ha
      subst ha; exact ht y q0 hy
    · simp only [PMF.support_map, Set.mem_image] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨-, h2, -, -⟩ := keyAt_support D t.1 _ p hp
      rw [h2] at hy
      exact ht y q0 hy
  all_goals
    simp only [layPre, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact ht y q0 hy

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `ltAt` at a party whose secrets are drawn is a point mass. -/
theorem ltAt_of_some {T : Type} (s : RStT S K T) (pid : PartyId) (v : S × S)
    (h : s.lt pid = some v) : ltAt s pid = PMF.pure (v, s) := by
  simp [ltAt, h]

/-- **The completion with the prekey of the peer** is the completion of the real protocol. -/
theorem completeSig_eq (A : AKEAlg S W) (s : RSt S W K) (x : Inst) (spk : W)
    (h : ∀ r, s.st.recs x = some r → ∃ v, s.lt r.peer = some v ∧ A.pub v.2 = spk) :
    completeSig A s x spk = completeStepK lazyKDF A s x := by
  unfold completeSig completeStepK
  rcases hr : s.st.recs x with _ | r
  · rfl
  obtain ⟨v, hv, hvs⟩ := h r hr
  rcases s.eph x with _ | ek
  · rfl
  simp only
  rcases opkOf s x.1 r.peer with _ | opk
  · rfl
  simp only
  split_ifs
  · refine PMF.bind_congr_support _ _ _ fun la hla => ?_
    obtain ⟨-, -, -, -, h5⟩ := ltAt_support s x.2 la hla
    rw [ltAt_of_some _ _ v (h5 _ _ hv), PMF.pure_bind, PMF.pure_bind, hvs]
    rfl
  · rfl

/-- **The two worlds agree off the bad transitions.** -/
theorem sigO_eq_filtO (A : SigAKEAlg S W VK SK Sig) (t : LSt W VK SK × RSt S W K)
    (e : SEv W Sig) (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) (hx : ¬ Bad₁ A t e x) :
    sigO A t e x = filtO A (keyD A) t e x := by
  have hI : Inv A t := by
    by_contra h
    exact hx (Or.inl h)
  have hnb : ¬ RealBad A t e x := fun h => hx (Or.inr h)
  obtain ⟨hpe, hsg⟩ := hI
  rcases e with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (a' | (q0 | ⟨sid, pid, spk, σ⟩)))
  rotate_left 4
  · simp only [sigO, filtO, layO, layPre]
    rcases hq : t.1.peers (sid, pid) with _ | q
    · simp only [PMF.pure_bind, sigSub, id]
    simp only [PMF.bind_map]
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun p => ?_
    by_cases hp : p ∈ (keyAt (keyD A) t.1 q).support
    swap
    · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hp, zero_mul, zero_mul]
    congr 1
    obtain ⟨-, -, -, hk4⟩ := keyAt_support _ t.1 q p hp
    have hpost : ∀ o : OOut S W K, layPost (keyD A) A.sig { p.2 with ph := .inj } o =
        PMF.pure ({ p.2 with ph := .inj }, .inr (.inr .ack)) := by
      intro o; rcases o with _ | _ <;> rfl
    simp only [Function.comp_apply, hpost, PMF.pure_map]
    by_cases hv : A.sig.verify p.1.1 spk σ = true
    · by_cases ha : accSigned t.1 q spk = true
      · simp only [hv, ha, Bool.and_self, ↓reduceIte, sigSub, injComplete]
        rw [completeSig_eq]
        · rfl
        intro r hr
        have hrq : r.peer = q := by
          have := hpe (sid, pid)
          rw [hq, hr] at this
          exact (Option.some.inj this).symm
        subst hrq
        exact hsg _ _ (by simpa [accSigned] using ha)
      · have hne : x.2.1 ≠ { p.2 with ph := .inj } := by
          intro h
          refine hnb ⟨q, sid, pid, spk, σ, p.1, rfl, hq, by rw [h]; exact hk4, hv, ?_⟩
          simpa [accSigned] using ha
        rw [PMF.bind_apply, PMF.bind_apply]
        simp only [hv, Bool.and_true, Bool.true_and, ha, ↓reduceIte, Bool.false_eq_true]
        refine (ENNReal.tsum_eq_zero.mpr fun y => ?_).trans
          (ENNReal.tsum_eq_zero.mpr fun y => ?_).symm
        all_goals
          rw [PMF.pure_apply_of_ne _ _ fun h => hne (congrArg (·.2.1) h), mul_zero]
    · simp [hv, sigSub, id]
  all_goals simp only [sigO, filtO, layO, layPre, PMF.pure_bind, sigSub, id]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The initial state satisfies `Inv`. -/
theorem inv_init (A : SigAKEAlg S W VK SK Sig) : Inv (K := K) A fInit :=
  ⟨fun _ => rfl, fun _ _ h => by simp [fInit, LSt.init] at h⟩

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The initial state satisfies `PInv P`. -/
theorem pinv_init (P : Finset PartyId) : PInv (S := S) (W := W) (K := K) (VK := VK) (SK := SK)
    P fInit :=
  fun _ _ h => by simp [fInit, LSt.init] at h

open Classical in
/-- **A bad flag implied by another along an invariant of the queries of a class**, for
transitions. -/
theorem run_flagWhen_le_of_inv_on {σ D R α : Type} (O : σ → D → PMF (R × σ)) (Q : D → Prop)
    (I : σ → Prop) (bad₁ bad₂ : σ → D → R × σ → Prop)
    (hstep : ∀ s d, I s → Q d → ∀ x ∈ (O s d).support, bad₂ s d x ∨ (¬ bad₁ s d x ∧ I x.2))
    (B : OracleAdv D R α) (hB : AllQ Q B) (s : σ) (hs : I s) :
    (OracleAdv.run (OracleAdv.flagWhen bad₁ O) B (s, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen bad₂ O) B (s, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  induction B generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    rw [OracleAdv.run_rand, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun b => ?_
    exact mul_le_mul_right (ih b (hB b) s hs) _
  | query d k ih =>
    rw [OracleAdv.run_query, OracleAdv.run_query]
    simp only [OracleAdv.flagWhen, PMF.bind_map, PMF.toOuterMeasure_bind_apply,
      Function.comp_apply, Bool.false_or]
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ (O s d).support
    · refine mul_le_mul_right ?_ _
      rcases hstep s d hs hB.1 x hx with h | ⟨h₁, h₂⟩
      · rw [decide_eq_true h, run_flag_true_one]
        exact toOuterMeasure_le_one _ _
      · rw [decide_eq_false h₁]
        by_cases h₃ : bad₂ s d x
        · rw [decide_eq_true h₃, run_flag_true_one]
          exact toOuterMeasure_le_one _ _
        · rw [decide_eq_false h₃]
          exact ih x.1 (hB.2 x.1) x.2 h₂
    · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hx, zero_mul, zero_mul]

/-- A flag that no transition sets is never set. -/
theorem run_flagWhen_false {σ D R α : Type} (O : σ → D → PMF (R × σ)) (B : OracleAdv D R α)
    (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ _ => False) O) B (s, false)).toOuterMeasure
        {y | y.2.2 = true} = 0 := by
  induction B generalizing s with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    simp [ih]
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    by_cases hx : x ∈ (OracleAdv.flagWhen (fun _ _ _ => False) O (s, false) d).support
    · simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
      obtain ⟨z, -, rfl⟩ := hx
      simp [ih]
    · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hx, zero_mul]

open Classical in
/-- **The union bound over a finite family of bad transitions.** -/
theorem run_flagWhen_union_le {σ D R α ι : Type} (O : σ → D → PMF (R × σ))
    (bad : ι → σ → D → R × σ → Prop) (T : Finset ι) (B : OracleAdv D R α) (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen (fun s d x => ∃ i ∈ T, bad i s d x) O) B
        (s, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ i ∈ T, (OracleAdv.run (OracleAdv.flagWhen (bad i) O) B
        (s, false)).toOuterMeasure {y | y.2.2 = true} := by
  induction T using Finset.induction_on with
  | empty =>
    refine (OracleAdv.run_flagWhen_mono O _ (fun _ _ _ => False)
      (fun _ _ _ h => by simp at h) B s).trans ?_
    rw [run_flagWhen_false]
    exact zero_le
  | insert j T hj ih =>
    rw [Finset.sum_insert hj]
    refine (OracleAdv.run_flagWhen_mono O _ (fun s d x => bad j s d x ∨ ∃ i ∈ T, bad i s d x)
      (fun _ _ _ h => by simpa using h) B s).trans ?_
    refine (OracleAdv.run_flagWhen_or_le O _ _ B s).trans ?_
    gcongr

/-- **A key drawn at its first triggering call, placed in the state, for an observable of the
state.** The form of `OracleAdv.run_map_fst_eq_bind_run_set_of_trigger` for the output together
with an observable `g` of the final state that `set k` keeps. -/
theorem run_map_obs_eq_bind_run_set_of_trigger {κ σ D R α β : Type} (μ : PMF κ)
    (O : σ → D → PMF (R × σ)) (set : κ → σ → σ) (g : σ → β) (hg : ∀ k s, g (set k s) = g s)
    (P : σ → Prop) (c : σ → D → Prop)
    (hc : ∀ s d, P s → c s d → O s d = μ.bind fun k => O (set k s) d)
    (hnc : ∀ k s d, P s → ¬ c s d → O (set k s) d = (O s d).map (Prod.map id (set k)))
    (hP : ∀ s d, P s → ¬ c s d → ∀ x ∈ (O s d).support, P x.2) (A : OracleAdv D R α) (s : σ)
    (hs : P s) :
    (OracleAdv.run O A s).map (fun y => (y.1, g y.2)) =
      μ.bind fun k => (OracleAdv.run O A (set k s)).map fun y => (y.1, g y.2) := by
  induction A generalizing s with
  | ret a => simp only [OracleAdv.run_ret, PMF.pure_map, hg, PMF.bind_const]
  | rand p f ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind, fun b => ih b s hs]
    exact PMF.bind_comm _ _ _
  | query d f ih =>
    simp only [OracleAdv.run_query, PMF.map_bind]
    by_cases hcs : c s d
    · rw [hc s d hs hcs, PMF.bind_bind]
    · simp only [hnc _ s d hs hcs, PMF.bind_map, Function.comp_def, Prod.map_fst, Prod.map_snd,
        id_eq]
      rw [PMF.bind_comm]
      exact PMF.bind_congr_support _ _ _ fun x hx => ih x.1 x.2 (hP s d hs hcs x hx)

/-! ## The forger simulates the filtered world -/

/-- The layer state with the key pair of the party `p` replaced by `v`. -/
def LSt.modKey (p : PartyId) (v : Option (VK × SK)) (l : LSt W VK SK) : LSt W VK SK :=
  { l with keys := Function.update l.keys p v }

/-- The events at which the filtered world uses the signing key of `p`: the verification key of
`p`, and an injection at a session whose peer is `p`. -/
def TrigAt (p : PartyId) (l : LSt W VK SK) : SEv W Sig → Prop
  | .inr (.inr (.sigPub q)) => q = p
  | .inr (.inr (.inject sid pid _ _)) => l.peers (sid, pid) = some p
  | _ => False

/-- The signing queries of the forger of `p` after a step with the event `e` and the transition
`x`: an answer to `sigPub p` with a signature `σ`, on the prekey `spk` signed for `p`, appends
`(spk, σ)` to `L`. -/
def logNext (p : PartyId) (L : List (W × Sig)) (e : SEv W Sig)
    (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) : List (W × Sig) :=
  match e, x.1, x.2.1.signed p with
  | .inr (.inr (.sigPub q)), .inr (.inr (.sigPub _ σ)), some spk =>
    if q = p then L ++ [(spk, σ)] else L
  | _, _, _ => L

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `keyAt` at a party with a key pair is a point mass. -/
theorem keyAt_of_some (D : PartyId → PMF (VK × SK)) (l : LSt W VK SK) (q : PartyId)
    (kp : VK × SK) (h : l.keys q = some kp) : keyAt D l q = PMF.pure (kp, l) := by
  simp [keyAt, h]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `keyAt` at a party `q` commutes with replacing the key pair of another party `p`. -/
theorem keyAt_modKey (D : PartyId → PMF (VK × SK)) (l : LSt W VK SK) {p q : PartyId}
    (hq : q ≠ p) (v : Option (VK × SK)) :
    keyAt D (l.modKey p v) q = (keyAt D l q).map (Prod.map id (LSt.modKey p v)) := by
  have hk : (l.modKey p v).keys q = l.keys q := Function.update_of_ne hq _ _
  unfold keyAt
  rw [hk]
  cases l.keys q with
  | some kp => simp [PMF.pure_map, Prod.map]
  | none =>
    dsimp only
    rw [PMF.map_comp]
    congr 1
    funext kp
    simp [LSt.modKey, Function.update_comm hq]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `keyAt` keeps the key pairs in place. -/
theorem keyAt_keys (D : PartyId → PMF (VK × SK)) (l : LSt W VK SK) (q : PartyId) :
    ∀ r ∈ (keyAt D l q).support, ∀ p kp, l.keys p = some kp → r.2.keys p = some kp := by
  intro r hr p kp hp
  unfold keyAt at hr
  split at hr
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hp
  · rename_i hq
    simp only [PMF.support_map, Set.mem_image] at hr
    obtain ⟨kp', -, rfl⟩ := hr
    by_cases hpq : p = q
    · subst hpq; simp [hq] at hp
    · simp [Function.update_of_ne hpq, hp]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `layPre` keeps the signed prekeys and the key pairs in place, and enters the phase `sign q`
only at `sigPub q`. -/
theorem layPre_support {EG : Type} (D : PartyId → PMF (VK × SK)) (Sg : PSigScheme W VK SK Sig)
    (ι : OEv W → EG) (acc : LSt W VK SK → PartyId → W → Bool) (inj : Inst → W → EG)
    (l : LSt W VK SK) (e : SEv W Sig) :
    ∀ a ∈ (layPre D Sg ι acc inj l e).support, a.1.signed = l.signed ∧
      (∀ q, a.1.ph = .sign q → e = .inr (.inr (.sigPub q))) ∧
      ∀ p kp, l.keys p = some kp → a.1.keys p = some kp := by
  intro a ha
  rcases e with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (a' | (q' | ⟨sid, pid, spk, σ⟩))) <;>
    simp only [layPre] at ha
  rotate_left 4
  · split at ha
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨rfl, fun _ h => by simp at h, fun _ _ h => h⟩
    · simp only [PMF.support_map, Set.mem_image] at ha
      obtain ⟨r, hr, rfl⟩ := ha
      obtain ⟨h1, -, -, -⟩ := keyAt_support D l _ r hr
      exact ⟨h1, fun _ h => by simp at h, keyAt_keys D l _ r hr⟩
  all_goals
    simp only [PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
  all_goals refine ⟨?_, ?_, ?_⟩ <;> simp only [notePeer] <;> grind

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `layPost` keeps the key pairs in place. -/
theorem layPost_keys (D : PartyId → PMF (VK × SK)) (Sg : PSigScheme W VK SK Sig)
    (l : LSt W VK SK) (o : OOut S W K) :
    ∀ r ∈ (layPost D Sg l o).support, ∀ p kp, l.keys p = some kp → r.1.keys p = some kp := by
  intro r hr p kp hp
  unfold layPost at hr
  split at hr
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hp
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hp
  · simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hr
    obtain ⟨r', hr', σ, -, rfl⟩ := hr
    exact keyAt_keys D l _ r' hr' p kp hp
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hp

omit [Fintype S] [Nonempty S] [Fintype K] [Nonempty K] in
/-- `layPre` commutes with replacing the key pair of `p`, off the injections at peer `p`. -/
theorem layPre_modKey {EG : Type} (D : PartyId → PMF (VK × SK)) (Sg : PSigScheme W VK SK Sig)
    (ι : OEv W → EG) (inj : Inst → W → EG) (l : LSt W VK SK) (p : PartyId)
    (v : Option (VK × SK)) (e : SEv W Sig)
    (he : ∀ sid pid spk σ, e = .inr (.inr (.inject sid pid spk σ)) →
      l.peers (sid, pid) ≠ some p) :
    layPre D Sg ι accSigned inj (l.modKey p v) e =
      (layPre D Sg ι accSigned inj l e).map (Prod.map (LSt.modKey p v) id) := by
  rcases e with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (a | (q | ⟨sid, pid, spk, σ⟩)))
  · simp only [layPre, PMF.pure_map, Prod.map, id, notePeer, LSt.modKey]
    by_cases h : (l.peers (sid, pid)).isSome = true <;> simp [h]
  rotate_left 3
  · have hpe : (l.modKey p v).peers (sid, pid) = l.peers (sid, pid) := rfl
    have hne := he sid pid spk σ rfl
    simp only [layPre, hpe]
    cases hq : l.peers (sid, pid) with
    | none => simp [PMF.pure_map, Prod.map, LSt.modKey]
    | some q =>
      have hqp : q ≠ p := fun h => hne (h ▸ hq)
      dsimp only
      rw [keyAt_modKey D l hqp, PMF.map_comp, PMF.map_comp]
      rfl
  all_goals simp [layPre, PMF.pure_map, Prod.map, LSt.modKey]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `layPost` commutes with replacing the key pair of `p`, off the phase `sign p`. -/
theorem layPost_modKey (D : PartyId → PMF (VK × SK)) (Sg : PSigScheme W VK SK Sig)
    (l : LSt W VK SK) (o : OOut S W K) (p : PartyId) (v : Option (VK × SK))
    (hph : ∀ q, l.ph = .sign q → q ≠ p) :
    layPost D Sg (l.modKey p v) o = (layPost D Sg l o).map (Prod.map (LSt.modKey p v) id) := by
  rcases l with ⟨k, sg, pe, ph⟩
  cases ph with
  | sign q =>
    have hq := hph q rfl
    rcases o with h | a
    · simp [layPost, LSt.modKey, PMF.pure_map, Prod.map]
    · cases a
      case pub ik spk =>
        simp only [layPost, LSt.modKey]
        rw [show ({ keys := Function.update k p v, signed := sg, peers := pe, ph := LPh.sign q } :
            LSt W VK SK) = LSt.modKey p v ⟨k, sg, pe, .sign q⟩ from rfl, keyAt_modKey D _ hq,
          PMF.bind_map, PMF.map_bind]
        refine congrArg _ (funext fun r => ?_)
        simp [PMF.map_comp, LSt.modKey, Function.comp_def, Prod.map]
      all_goals simp [layPost, LSt.modKey, PMF.pure_map, Prod.map]
  | _ => cases o <;> simp [layPost, LSt.modKey, PMF.pure_map, Prod.map]

/-- The filtered world commutes with replacing the key pair of `p`, off the events that use it. -/
theorem filtO_modKey (A : SigAKEAlg S W VK SK Sig) (D : PartyId → PMF (VK × SK))
    (t : LSt W VK SK × RSt S W K) (p : PartyId) (v : Option (VK × SK)) (e : SEv W Sig)
    (he : ¬ TrigAt p t.1 e) :
    filtO A D (t.1.modKey p v, t.2) e =
      (filtO A D t e).map fun x => (x.1, (x.2.1.modKey p v, x.2.2)) := by
  have hpre := layPre_modKey D A.sig id injComplete t.1 p v e (by
    rintro sid pid spk σ rfl h; exact he h)
  unfold filtO layO
  rw [hpre, PMF.bind_map, PMF.map_bind]
  refine PMF.bind_congr_support _ _ _ fun a ha => ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, PMF.map_bind]
  refine congrArg _ (funext fun q => ?_)
  have hph : ∀ q', a.1.ph = .sign q' → q' ≠ p := fun q' h => by
    have := (layPre_support D A.sig id accSigned injComplete t.1 e a ha).2.1 q' h
    subst this; exact he
  rw [layPost_modKey D A.sig a.1 q.1 p v hph, PMF.map_comp, PMF.map_comp]
  rfl

/-- The filtered world keeps the key pairs in place. -/
theorem filtO_keys (A : SigAKEAlg S W VK SK Sig) (D : PartyId → PMF (VK × SK))
    (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) :
    ∀ x ∈ (filtO A D t e).support, ∀ p kp, t.1.keys p = some kp → x.2.1.keys p = some kp := by
  intro x hx p kp hp
  unfold filtO layO at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨a, ha, hx⟩ := hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨q, -, hx⟩ := hx
  rw [PMF.support_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  exact layPost_keys D A.sig a.1 q.1 r hr p kp
    ((layPre_support D A.sig id accSigned injComplete t.1 e a ha).2.2 p kp hp)

/-- Off the events that use it, the filtered world keeps the key pair of `p`. -/
theorem filtO_keys_of_not_trig (A : SigAKEAlg S W VK SK Sig) (D : PartyId → PMF (VK × SK))
    (t : LSt W VK SK × RSt S W K) (p : PartyId) (e : SEv W Sig) (he : ¬ TrigAt p t.1 e) :
    ∀ x ∈ (filtO A D t e).support, x.2.1.keys p = t.1.keys p := by
  intro x hx
  have ht : (t.1.modKey p (t.1.keys p), t.2) = t := by
    rcases t with ⟨⟨k, sg, pe, ph⟩, r⟩
    simp [LSt.modKey]
  have h := filtO_modKey A D t p (t.1.keys p) e he
  rw [ht] at h
  rw [h, PMF.support_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp [LSt.modKey]

/-- **A signed prekey stays signed.** In the filtered world, from a state of `Inv`, a prekey
signed for `p` stays the prekey signed for `p`. -/
theorem filtO_signed (A : SigAKEAlg S W VK SK Sig) (D : PartyId → PMF (VK × SK))
    (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) (hI : Inv A t) (p : PartyId) (m : W)
    (hm : t.1.signed p = some m) :
    ∀ x ∈ (filtO A D t e).support, x.2.1.signed p = some m := by
  intro x hx
  have hIx := inv_filtO A D t e hI x hx
  unfold filtO layO at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨a, ha, hx⟩ := hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨q, hq, hx⟩ := hx
  rw [PMF.support_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨-, hq2⟩ := realO_support A.toAKEAlg t.2 a.2 q hq
  have ha1 := (layPre_support D A.sig id accSigned injComplete t.1 e a ha).1
  obtain ⟨v, hv, hvm⟩ := hI.2 p m hm
  have hw : ∃ w, r.1.signed p = some w := by
    rcases (layPost_support D A.sig a.1 q.1 r hr).2 with h | ⟨q', ik, spk, -, -, h⟩
    · exact ⟨m, by rw [h, ha1, hm]⟩
    · by_cases hqp : p = q'
      · subst hqp; exact ⟨spk, by rw [h]; simp⟩
      · exact ⟨m, by rw [h, Function.update_of_ne hqp, ha1, hm]⟩
  obtain ⟨w, hw⟩ := hw
  obtain ⟨v', hv', hvw⟩ := hIx.2 p w hw
  have h2 := hq2 p v hv
  rw [hv'] at h2
  obtain rfl := Option.some.inj h2
  change r.1.signed p = some m
  rw [hw, ← hvw, hvm]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- A forbidden injection at `p` is an event that uses the key of `p`. -/
theorem trigAt_of_badAt (A : SigAKEAlg S W VK SK Sig) (p : PartyId)
    (t : LSt W VK SK × RSt S W K) (e : SEv W Sig)
    (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) (h : BadAt A p t e x) :
    TrigAt p t.1 e := by
  obtain ⟨sid, pid, spk, σ, kp, rfl, hpe, -⟩ := h
  exact hpe

omit [Fintype S] [Nonempty S] [Fintype K] [Nonempty K] in
/-- A forgery found at a step is an injection at peer `p` with a signature that verifies under
`pk` on a prekey not signed for `p`. -/
theorem forgeryAt_some (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK) (l : LSt W VK SK)
    (e : SEv W Sig) (f : W × Sig) (hf : forgeryAt A p pk l e = some f) :
    ∃ sid pid spk σ, e = .inr (.inr (.inject sid pid spk σ)) ∧ f = (spk, σ) ∧
      l.peers (sid, pid) = some p ∧ A.sig.verify pk spk σ = true ∧ l.signed p ≠ some spk := by
  rcases e with ((_ | _) | (_ | (_ | ⟨sid, pid, spk, σ⟩))) <;>
    simp only [forgeryAt, reduceCtorEq] at hf
  split_ifs at hf with h
  · exact ⟨sid, pid, spk, σ, rfl, (Option.some.inj hf).symm, h.1, h.2.1, h.2.2⟩

omit [Fintype S] [Nonempty S] [Fintype K] [Nonempty K] in
/-- The forgery found at a step does not read the key pairs. -/
theorem forgeryAt_modKey (A : SigAKEAlg S W VK SK Sig) (p q : PartyId) (pk : VK)
    (l : LSt W VK SK) (v : Option (VK × SK)) (e : SEv W Sig) :
    forgeryAt A p pk (l.modKey q v) e = forgeryAt A p pk l e := by
  rcases e with ((_ | _) | (_ | (_ | ⟨sid, pid, spk, σ⟩))) <;> rfl

/-- With the key pair `(pk, sk)` of `p` in place, a forbidden injection at `p` is a forgery
found at the step. -/
theorem forgeryAt_ne_none_of_badAt (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (sk : SK) (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) (hk : t.1.keys p = some (pk, sk))
    (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) (hx : x ∈ (filtO A (keyD A) t e).support)
    (h : BadAt A p t e x) : forgeryAt A p pk t.1 e ≠ none := by
  obtain ⟨sid, pid, spk, σ, kp, rfl, hpe, hkx, hv, hs⟩ := h
  have hk' := filtO_keys A _ t _ x hx p _ hk
  rw [hkx] at hk'
  obtain rfl := Option.some.inj hk'
  simp [forgeryAt, hpe, hv, hs]

/-- With the key pair `(pk, sk)` of `p` in place, a forgery found at the step is a forbidden
injection at `p` on every transition. -/
theorem badAt_of_forgeryAt (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (sk : SK) (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) (hk : t.1.keys p = some (pk, sk))
    (f : W × Sig) (hf : forgeryAt A p pk t.1 e = some f) :
    ∀ x ∈ (filtO A (keyD A) t e).support, BadAt A p t e x := by
  intro x hx
  obtain ⟨sid, pid, spk, σ, rfl, -, hpe, hv, hs⟩ := forgeryAt_some A p pk t.1 e f hf
  exact ⟨sid, pid, spk, σ, (pk, sk), rfl, hpe, filtO_keys A _ t _ x hx p _ hk, hv, hs⟩

/-- The answer of the real state machine to `pub q`. -/
theorem realStep_pub (A : AKEAlg S W) (s : RSt S W K) (q : PartyId) :
    realStep A s (.inr (.pub q)) =
      (ltAt s q).map fun l => (.inr (.pub (A.pub l.1.1) (A.pub l.1.2)), l.2) := by
  simp only [realStep, realGame, realGameK, realAdvK, PMF.map_comp]
  rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- Replacing the key pair of `p` twice keeps the second replacement. -/
theorem LSt.modKey_modKey (p : PartyId) (v w : Option (VK × SK)) (l : LSt W VK SK) :
    (l.modKey p v).modKey p w = l.modKey p w := by
  simp [LSt.modKey]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- Replacing the key pair of `p` by the key pair it has keeps the layer state. -/
theorem LSt.modKey_self (p : PartyId) (l : LSt W VK SK) : l.modKey p (l.keys p) = l := by
  rcases l with ⟨k, sg, pe, ph⟩
  simp [LSt.modKey]

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- An entry of `logNext p L e x` is an entry of `L` or the prekey signed for `p` after `x`. -/
theorem mem_logNext (p : PartyId) (L : List (W × Sig)) (e : SEv W Sig)
    (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) :
    ∀ y ∈ logNext p L e x, y ∈ L ∨ x.2.1.signed p = some y.1 := by
  intro y hy
  unfold logNext at hy
  split at hy
  · rename_i q σ spk hs
    split_ifs at hy
    · rcases List.mem_append.mp hy with h | h
      · exact Or.inl h
      · simp only [List.mem_singleton] at h
        subst h
        exact Or.inr hs
    · exact Or.inl hy
  · exact Or.inl hy

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `logNext p` adds nothing at an event other than `sigPub p`. -/
theorem logNext_of_ne (p : PartyId) (L : List (W × Sig)) (e : SEv W Sig)
    (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K))
    (he : ∀ q, e = .inr (.inr (.sigPub q)) → q ≠ p) : logNext p L e x = L := by
  unfold logNext
  split
  · simp_all
  · rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- `logNext` adds nothing at an injection. -/
theorem logNext_inject (p : PartyId) (L : List (W × Sig)) (sid : SessionId) (pid : PartyId)
    (spk : W) (σ : Sig) (x : SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) :
    logNext p L (.inr (.inr (.inject sid pid spk σ))) x = L := by
  simp [logNext]

/-- **The forger step against the signing oracle.** Run against the signing oracle of `sk`, from
a state without a key pair for `p`, a step of the forger of `p` with the challenge key `pk` is the
step of the filtered world with the key pair `(pk, sk)` of `p` in place, with the key pair of `p`
removed after the step and the signing queries logged by `logNext`. -/
theorem run_forgeStep (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK) (sk : SK)
    (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) (L : List (W × Sig))
    (hk : t.1.keys p = none) :
    OracleAdv.run (signOracle A.sig sk) (forgeStep A p pk t e) L =
      (filtO A (keyD A) (t.1.modKey p (some (pk, sk)), t.2) e).map fun x =>
        ((x.1, (x.2.1.modKey p none, x.2.2)), logNext p L e x) := by
  by_cases he : TrigAt p t.1 e
  · rcases e with ((_ | _) | (_ | (q | ⟨sid, pid, spk, σ⟩))) <;> simp only [TrigAt] at he
    · subst he
      simp only [forgeStep, preF, layPre, id, OracleAdv.run_rand, PMF.pure_bind, realStep_pub,
        filtO, layO, PMF.bind_map, PMF.map_bind]
      refine PMF.bind_congr_support _ _ _ fun l _ => ?_
      have hkk : Function.update t.1.keys q none = t.1.keys :=
        Function.update_eq_self_iff.mpr hk.symm
      simp only [postF, layPost, keyAt, OracleAdv.run_bind, OracleAdv.run_ret,
        Function.comp_apply, ↓reduceIte, OracleAdv.run_query, signOracle, PMF.bind_map,
        Function.comp_def, PMF.bind_bind, PMF.pure_bind, LSt.modKey, logNext,
        Function.update_self, PMF.map_comp, Function.update_idem]
      rw [hkk, ← PMF.bind_pure_comp]
      rfl
    · have hkk : Function.update t.1.keys p none = t.1.keys :=
        Function.update_eq_self_iff.mpr hk.symm
      have hpe : (t.1.modKey p (some (pk, sk))).peers (sid, pid) = some p := he
      simp only [forgeStep, preF, he, ite_true, filtO, layO, layPre, hpe]
      simp only [accSigned, Bool.and_eq_true, beq_iff_eq, postF, layPost, keyAt,
        OracleAdv.run_rand, OracleAdv.run_bind, OracleAdv.run_ret, PMF.pure_bind, LSt.modKey,
        logNext, id_eq, Function.update_self, PMF.pure_map, PMF.map_bind, Function.update_idem, hkk]
  · have hpre : preF A p pk t.1 e = layPre (keyD A) A.sig id accSigned injComplete t.1 e := by
      rcases e with ((_ | _) | (_ | (_ | ⟨sid, pid, spk, σ⟩))) <;> simp_all [preF, TrigAt]
    have hpost : ∀ a ∈ (layPre (keyD A) A.sig id accSigned injComplete t.1 e).support,
        ∀ o : OOut S W K, postF A p pk a.1 o = .rand (layPost (keyD A) A.sig a.1 o) .ret := by
      intro a ha o
      have h2 := (layPre_support (keyD A) A.sig id accSigned injComplete t.1 e a ha).2.1
      unfold postF
      split
      · rename_i q _ _ hph
        rw [ite_eq_right_iff]
        rintro rfl
        exact absurd (by rw [h2 _ hph]; rfl) he
      · rfl
    have hoff : OracleAdv.run (signOracle A.sig sk) (forgeStep A p pk t e) L =
        (filtO A (keyD A) t e).map fun x => (x, L) := by
      unfold forgeStep filtO layO
      rw [hpre, OracleAdv.run_rand, PMF.map_bind]
      refine PMF.bind_congr_support _ _ _ fun a ha => ?_
      rw [OracleAdv.run_rand, PMF.map_bind]
      refine congrArg _ (funext fun q => ?_)
      rw [hpost a ha, OracleAdv.run_bind, OracleAdv.run_rand, PMF.bind_bind]
      simp only [OracleAdv.run_ret, PMF.pure_bind, PMF.map_comp]
      rw [← PMF.bind_pure_comp]
      rfl
    rw [hoff, filtO_modKey A (keyD A) t p _ e he, PMF.map_comp, ← PMF.bind_pure_comp,
      ← PMF.bind_pure_comp]
    refine PMF.bind_congr_support _ _ _ fun x hx => ?_
    have hx' := (filtO_keys_of_not_trig A (keyD A) t p e he x hx).trans hk
    have hl : logNext p L e (x.1, (x.2.1.modKey p (some (pk, sk)), x.2.2)) = L :=
      logNext_of_ne p L e _ fun q hq hqp => he (by subst hq; exact hqp)
    simp only [Function.comp_apply, LSt.modKey_modKey, hl]
    rw [← hx', LSt.modKey_self]

/-- **The key pair of `p` drawn at its first use.** At an event that uses the key pair of `p`,
from a state without one, the filtered world is the draw of the key coins followed by the step
from the state with the key pair of the coins in place. -/
theorem filtO_trigger (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (t : LSt W VK SK × RSt S W K)
    (e : SEv W Sig) (hk : t.1.keys p = none) (he : TrigAt p t.1 e) :
    filtO A (keyD A) t e = (PMF.uniformFintype A.sig.KR).bind fun kr =>
      filtO A (keyD A) (t.1.modKey p (some (A.sig.keygen kr)), t.2) e := by
  rcases e with ((_ | _) | (_ | (q | ⟨sid, pid, spk, σ⟩))) <;> simp only [TrigAt] at he
  · subst he
    simp only [filtO, layO, layPre, id, PMF.pure_bind, realStep_pub, PMF.bind_map]
    conv_rhs => rw [PMF.bind_comm]
    refine PMF.bind_congr_support _ _ _ fun l _ => ?_
    simp [layPost, keyAt, hk, LSt.modKey, keyD, PSigScheme.keyDist, PMF.bind_map, PMF.map_bind,
      Function.comp_def]
  · simp [filtO, layO, layPre, he, keyAt, hk, keyD, PSigScheme.keyDist, PMF.map_comp,
      PMF.bind_map, LSt.modKey, PMF.pure_map, Function.comp_def, accSigned]

open Classical in
/-- **The key pair of `p` drawn at the start.** The probability that the filtered world makes a
forbidden injection at `p` is the average over the key coins of that probability from the state
with the key pair of the coins in place for `p`. -/
theorem flag_lazy (A : SigAKEAlg S W VK SK Sig) (p : PartyId)
    (B : OracleAdv (SEv W Sig) (SOut S W K VK Sig) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A))) B
        (fInit, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' kr, PMF.uniformFintype A.sig.KR kr *
        (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A))) B
          (((fInit : LSt W VK SK × RSt S W K).1.modKey p (some (A.sig.keygen kr)),
            (fInit : LSt W VK SK × RSt S W K).2), false)).toOuterMeasure
          {y | y.2.2 = true} := by
  have h := run_map_obs_eq_bind_run_set_of_trigger (PMF.uniformFintype A.sig.KR)
    (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A)))
    (fun kr (s : (LSt W VK SK × RSt S W K) × Bool) =>
      ((s.1.1.modKey p (some (A.sig.keygen kr)), s.1.2), s.2))
    Prod.snd (fun _ _ => rfl) (fun s => s.1.1.keys p = none) (fun s d => TrigAt p s.1.1 d)
    (fun s d hs hcs => by
      simp only [OracleAdv.flagWhen]
      rw [filtO_trigger A p s.1 d hs hcs, PMF.map_bind]
      rfl)
    (fun k s d hs hcs => by
      simp only [OracleAdv.flagWhen]
      rw [filtO_modKey A (keyD A) s.1 p _ d hcs, PMF.map_comp, PMF.map_comp]
      congr 1
      funext x
      have h1 : ¬ BadAt A p s.1 d x := fun h => hcs (trigAt_of_badAt A p _ _ _ h)
      have h2 : ¬ BadAt A p (s.1.1.modKey p (some (A.sig.keygen k)), s.1.2) d
          (x.1, (x.2.1.modKey p (some (A.sig.keygen k)), x.2.2)) := fun h =>
        hcs (trigAt_of_badAt A p _ _ _ h)
      simp [h1, h2])
    (fun s d hs hcs x hx => by
      simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (filtO_keys_of_not_trig A (keyD A) s.1 p d hcs y hy).trans hs)
    B (fInit, false) rfl
  have hm : ∀ s, (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A))) B
      s).toOuterMeasure {y | y.2.2 = true} =
      ((OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A))) B s).map
        fun y => (y.1, y.2.2)).toOuterMeasure {z | z.2 = true} := fun s => by
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  rw [hm, h, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun kr => ?_
  rw [hm]

open Classical in
/-- **The forger simulates the filtered world.** From a state without a key pair for `p`, with
the signing log `L` of prekeys all signed for `p`, the probability that the filtered world with
the key pair `(pk, sk)` in place for `p` makes a forbidden injection at `p` is at most the
probability that the loop of the forger, run against the signing oracle of `sk` from `L`, outputs
a fresh message with a signature that verifies under `pk`. -/
theorem flag_le_forge (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK) (sk : SK) (m₀ : W)
    (B : OracleAdv (SEv W Sig) (SOut S W K VK Sig) Bool) (t : LSt W VK SK × RSt S W K)
    (L : List (W × Sig)) (hk : t.1.keys p = none) (hI : Inv A t)
    (hL : ∀ y ∈ L, t.1.signed p = some y.1) :
    (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A))) B
        ((t.1.modKey p (some (pk, sk)), t.2), false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (signOracle A.sig sk) (forgeLoop A p pk m₀ B t) L).toOuterMeasure
        {x | (A.sig.verify pk x.1.1 x.1.2 && !(x.2.map Prod.fst).contains x.1.1) = true} := by
  induction B generalizing t L with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand μ k ih =>
    rw [OracleAdv.run_rand, forgeLoop, stopRed, ← forgeLoop, OracleAdv.run_rand,
      PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b t L hk hI hL) _
  | query e k ih =>
    have hI' : Inv A (t.1.modKey p (some (pk, sk)), t.2) := hI
    have hk' : (t.1.modKey p (some (pk, sk))).keys p = some (pk, sk) := by simp [LSt.modKey]
    rw [OracleAdv.run_query, forgeLoop, stopRed, ← forgeLoop, OracleAdv.run_bind,
      run_forgeStep A p pk sk t e L hk,
      PMF.bind_map]
    rcases hf : forgeryAt A p pk t.1 e with _ | f
    · simp only [OracleAdv.flagWhen, PMF.bind_map]
      rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ (filtO A (keyD A) (t.1.modKey p (some (pk, sk)), t.2) e).support
      · refine mul_le_mul_right ?_ _
        have hb : ¬ BadAt A p (t.1.modKey p (some (pk, sk)), t.2) e x := fun h =>
          forgeryAt_ne_none_of_badAt A p pk sk _ e hk' x hx h (by rw [forgeryAt_modKey]; exact hf)
        have hxk := filtO_keys A (keyD A) _ e x hx p _ hk'
        have hx2 : ((x.2.1.modKey p none).modKey p (some (pk, sk)), x.2.2) = x.2 := by
          rw [LSt.modKey_modKey, ← hxk, LSt.modKey_self]
        have hlog : ∀ y ∈ logNext p L e x, (x.2.1.modKey p none).signed p = some y.1 := by
          intro y hy
          rcases mem_logNext p L e x y hy with h | h
          · exact filtO_signed A (keyD A) _ e hI' p y.1 (hL y h) x hx
          · exact h
        have := ih x.1 (x.2.1.modKey p none, x.2.2) (logNext p L e x) (by simp [LSt.modKey])
          (inv_filtO A (keyD A) _ e hI' x hx) hlog
        rw [hx2] at this
        simpa [decide_eq_false hb] using this
      · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hx, zero_mul, zero_mul]
    · obtain ⟨sid, pid, spk, σ, rfl, rfl, hpe, hv, hs⟩ := forgeryAt_some A p pk t.1 e f hf
      have hnot : ∀ σ', (spk, σ') ∉ L := fun σ' h => hs (hL _ h)
      refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
      rw [eq_comm, PMF.toOuterMeasure_apply_eq_one_iff]
      intro y hy
      simp only [PMF.mem_support_bind_iff, Function.comp_apply, OracleAdv.run_ret,
        PMF.support_pure, Set.mem_singleton_iff] at hy
      obtain ⟨x, -, rfl⟩ := hy
      simp [logNext_inject, hv, hnot]

open Classical in
/-- **A forbidden injection at `p` is a forgery.** The probability that the filtered world makes a
forbidden injection at `p` is at most the EUF-CMA advantage of the forger of `p`. -/
theorem flag_le_eufcma (A : SigAKEAlg S W VK SK Sig) (p : PartyId)
    (B : OracleAdv (SEv W Sig) (SOut S W K VK Sig) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A))) B
        (fInit, false)).toOuterMeasure {y | y.2.2 = true} ≤
      eufcmaAdvantage A.sig.toSigScheme (toEUFAdversary (forgeRed A p B)) := by
  rw [flag_lazy, eufcmaAdvantage_toEUFAdversary, eufDist, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun kr => mul_le_mul_right ?_ _
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  exact flag_le_forge A p _ _ _ B fInit [] rfl (inv_init A) (by simp)

/-- **The signed real world and the filtered world, up to forgery.** For every oracle adversary
`B`, the difference of the probabilities that `B` outputs `true` against the signed real protocol
and against the filtered world is at most the bound of the signatures. -/
theorem sig_filt_le (A : SigAKEAlg S W VK SK Sig) (P : Finset PartyId)
    (B : OracleAdv (SEv W Sig) (SOut S W K VK Sig) Bool) :
    absDiff ((OracleAdv.run (sigO A) B fInit).map Prod.fst true)
        ((OracleAdv.run (filtO A (keyD A)) B fInit).map Prod.fst true) ≤ sigBound A P B := by
  classical
  unfold sigBound
  split_ifs with hN
  swap
  · exact le_top
  have hgap := OracleAdv.run_gap_le_flagWhen (Bad₁ A) (sigO A) (filtO A (keyD A))
    (fun s d x hx => sigO_eq_filtO A s d x hx) B fInit {true}
  rw [OracleGameUpToBad.map_fst_apply_true, OracleGameUpToBad.map_fst_apply_true]
  refine hgap.trans ?_
  have h₁ := OracleAdv.run_flagWhen_le_of_inv (filtO A (keyD A)) (Bad₁ A) (RealBad A) (Inv A)
    (fun s d hs x hx => by
      by_cases hb : RealBad A s d x
      · exact Or.inl hb
      · exact Or.inr ⟨fun h => h.elim (· hs) hb, inv_filtO A _ s d hs x hx⟩) B fInit
    (inv_init A)
  have h₂ := run_flagWhen_le_of_inv_on (filtO A (keyD A)) (EvInSig P)
    (fun t => Inv A t ∧ PInv P t) (RealBad A) (fun s d x => ∃ q ∈ P, BadAt A q s d x)
    (fun s d hs hd x hx => by
      by_cases hb : ∃ q ∈ P, BadAt A q s d x
      · exact Or.inl hb
      · refine Or.inr ⟨fun ⟨q, hq⟩ => hb ⟨q, ?_, hq⟩,
          inv_filtO A _ s d hs.1 x hx, pinv_filtO A _ P s d hs.2 hd x hx⟩
        obtain ⟨sid, pid, spk, σ, kp, -, hpe, -⟩ := hq
        exact hs.2 _ _ hpe) B hN fInit ⟨inv_init A, pinv_init P⟩
  refine h₁.trans (h₂.trans ?_)
  have h₃ := (run_flagWhen_union_le (filtO A (keyD A)) (fun q => BadAt A q) P B fInit).trans
    (Finset.sum_le_sum fun p _ => flag_le_eufcma A p B)
  convert h₃ using 5

/-- The advantage of an environment between the signed real protocol and the forwarding protocol
against the filtered world is the difference of the probabilities of `true` of its oracle
reduction. -/
theorem adv_sig_filt (A : SigAKEAlg S W VK SK Sig) {ζ : Type}
    (Z : Env (Strat ζ (SEv W Sig) (SOut S W K VK Sig)) ζ) :
    adv (x3dhSigRealOf A) ((OProt.oracle (Q := SEv W Sig) (A := SOut S W K VK Sig)).plug
        (filtO A (keyD A)) fInit) Z =
      absDiff ((OracleAdv.run (sigO A) (OProt.oracle.reduction Z) fInit).map Prod.fst true)
        ((OracleAdv.run (filtO A (keyD A)) (OProt.oracle.reduction Z) fInit).map Prod.fst
          true) := by
  rw [adv_eq, x3dhSigRealOf, OProt.prTrue_view_sys, OProt.prTrue_view_plug]
  simp only [KeyedGame.accept, sigGame, PMF.pure_bind]
  rfl

end Forger

/-! ## The square -/

section Main

variable {S W K VK SK Sig : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W) (Sg : PSigScheme W VK SK Sig)

/-- **X3DH with signed prekeys realizes `F_AKE` behind `x3dhSigSim`.** For every finite set of
parties `P` and every environment `Z`, the distance between the real protocol of X3DH with signed
prekeys `x3dhSigRealOf (x3dhSigAlg G Sg)` and the simulator `x3dhSigSim G Sg` running with
`F_AKE` is at most the sum over the parties `p` of `P` of the EUF-CMA advantages of the forgers
`forgeRed (x3dhSigAlg G Sg) p (OProt.oracle.reduction Z)` against `Sg`, when the oracle reduction
of `Z` starts sessions only between parties of `P`, plus the gap Diffie–Hellman bound `gdhBound`
at the environment reduced through the layer of the signatures. -/
theorem x3dh_signed_realizesSim (P : Finset PartyId) :
    RealizesSim (x3dhSigRealOf (K := K) (x3dhSigAlg G Sg)) (F_AKE (SPComp.sample K) true)
      (x3dhSigSim G Sg)
      (fun _ Z => sigBound (x3dhSigAlg G Sg) P (OProt.oracle.reduction Z) +
        gdhBound G P (OProt.oracle.reduction ((sigLayerH (S := S) (K := K) Sg).reduceEnv Z))) := by
  have hJ := plug_realizes (realGame (K := K) (x3dhAlg G)) () (fun _ => rfl) rfl
  have hL := layer_plug_realizes (sigLayerH (S := S) (K := K) Sg) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) ((realGame (K := K) (x3dhAlg G)).oracle ()) (realGame (x3dhAlg G)).init
  have h₁ : Realizes (x3dhSigRealOf (K := K) (x3dhSigAlg G Sg))
      ((sigLayerH Sg).withSub ((OProt.oracle (Q := OEv W) (A := OOut S W K)).plug
        ((realGame (K := K) (x3dhAlg G)).oracle ()) (realGame (x3dhAlg G)).init))
      (fun _ Z => sigBound (x3dhSigAlg G Sg) P (OProt.oracle.reduction Z) + 0) :=
    Realizes.trans (fun _ Z => (adv_sig_filt (x3dhSigAlg G Sg) Z).le.trans
      (sig_filt_le (x3dhSigAlg G Sg) P _)) (realizes_symm hL)
  have h₂ := Realizes.trans (realizes_symm hJ) (x3dh_realizesSim_gapDH G P)
  intro ζ Z
  change adv (x3dhSigRealOf (x3dhSigAlg G Sg))
    ((sigLayer Sg).withSub ((x3dhSim G).withSub (F_AKE (SPComp.sample K) true))) Z ≤ _
  rw [sigLayer, MultiHybrid.ofHybrid_withSub]
  have h₃ : Realizes
      ((sigLayerH Sg).withSub ((OProt.oracle (Q := OEv W) (A := OOut S W K)).plug
        ((realGame (K := K) (x3dhAlg G)).oracle ()) (realGame (x3dhAlg G)).init))
      ((sigLayerH Sg).withSub ((x3dhSim G).withSub (F_AKE (SPComp.sample K) true)))
      (fun ζ Z => 0 + gdhBound G P (OProt.oracle.reduction ((sigLayerH (S := S) (K := K)
        Sg).reduceEnv Z))) := fun ζ' Z' =>
    (Hybrid.adv_withSub _ _ _ Z').le.trans (h₂ _ _)
  refine ((Realizes.trans h₁ h₃) ζ Z).trans_eq ?_
  simp only [add_zero, zero_add]

end Main

end CatCrypt.Crypto.AKE.X3DHSquareSigned

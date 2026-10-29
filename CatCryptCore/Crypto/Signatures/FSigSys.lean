/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.UCChannel
public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.Signatures.Scheme
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The signature functionality as a reactive system

The ideal functionality `fsig` is the unstoppable signature functionality `F_SIG` of Cohen,
Lindell, Osborn and Shany (ePrint 2024/1807), in the form of Canetti (CSFW 2004) for an honest
signer, as a port-typed system (`Sys.ofPorts`).

* Adversary port: `register a` installs the algorithm `a` (`SigAlg`): a verification key, a
  lossless signing procedure and a verification predicate. Only the first registration counts.
* Honest port: `keyGen` returns the registered verification key; `sign m` runs the registered
  signing procedure on `m`, records the pair `(m, σ)` and returns `σ`; `verify m σ vk` returns
  `true` on a recorded pair under the registered key (completeness), `false` on a message never
  signed under the registered key (unforgeability), and otherwise the registered predicate.
  Before a registration every honest event is answered by `err`.

Signing is unstoppable: the functionality runs the registered procedure itself, so the
adversary learns neither the messages signed nor the verification queries, only the kind of
each honest event.

The real protocol `realSig S` is the scheme `S` run by the signer: `keyGen` samples a key pair on
first use and returns its public key, `sign m` signs with the secret key, `verify m σ vk` runs
`S.verify`. Its adversary port carries no messages. Its state carries a flag `forged`, set by a
verification that accepts, under the signer's key, a message never signed (a forgery).

The simulator `fsigSim S` forwards every honest event to `fsig` and every answer back to the
honest port. On the first `keyGen` it samples a key pair with `S.keygen` and registers the
algorithm of the key pair (`algOf`) before forwarding `keyGen`. It reads the kind of each honest
event and nothing else: it is opaque from `fsigView` to `outerView`, the views that keep the kind
of honest events and forget honest outputs (`fsigSimπ_opaque`).

## Main definitions

* `SigEv`, `SigOut`, `SigAlg`, `FSigSt`: the ports and the state of `F_SIG`.
* `fsig`: the functionality `F_SIG`.
* `realSig S`: the real signing system of the scheme `S`.
* `fsigSim S`: the simulator, a bundled opaque simulator (`Simulator.ofMultiHybrid`).
* `SigScheme.ConsistentOn`: consistency of `S` in relational form, for an invariant of key pairs.

## Main results

* `fsig_portTyped`, `realSig_portTyped`: both systems answer on the port of the event.
* `fsigSimπ_opaque`: the simulator is opaque.
* `realSig_realizesSim_fsig`: for a lossless scheme consistent in relational form, `realSig S`
  realizes `fsig` behind `fsigSim S` with bound the probability that the run of the environment
  against `realSig S` contains a forgery.

The time certificate of the simulator `fsigSim` is not part of this file.

## References

* [Cohen, Lindell, Osborn, Shany — ePrint 2024/1807]
* [Canetti — Universally Composable Signature, Certification, and Authentication, CSFW 2004]
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signatures.FSigSys

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCCoupling (realizes_upto_bad_rel stepPost)
open scoped ENNReal

/-! ## Ports and state -/

/-- Honest events of the signature functionality: key generation, signing of a message, and
verification of a signature on a message under a verification key. -/
inductive SigEv (Msg PK Sig : Type) where
  /-- Key generation. -/
  | keyGen
  /-- Signing of the message `m`. -/
  | sign (m : Msg)
  /-- Verification of `σ` on `m` under `vk`. -/
  | verify (m : Msg) (σ : Sig) (vk : PK)

/-- Honest outputs of the signature functionality. -/
inductive SigOut (PK Sig : Type) where
  /-- A verification key. -/
  | vk (pk : PK)
  /-- A signature. -/
  | sig (σ : Sig)
  /-- A verification result. -/
  | result (b : Bool)
  /-- No key has been generated. -/
  | err

/-- The kind of an honest event, the part of it that the adversary learns. -/
def SigEv.kind {Msg PK Sig : Type} : SigEv Msg PK Sig → Fin 3
  | .keyGen => 0
  | .sign _ => 1
  | .verify _ _ _ => 2

/-- A signing algorithm registered by the adversary: a verification key, a lossless signing
procedure and a verification predicate. -/
structure SigAlg (Msg PK Sig : Type) where
  /-- The verification key. -/
  vk : PK
  /-- The signing procedure. -/
  sign : Msg → SPComp Sig
  /-- The verification predicate. -/
  verify : PK → Msg → Sig → Bool
  /-- The signing procedure never fails. -/
  sign_noFail : ∀ m, SPComp.NoFail (sign m)

/-- The state of `F_SIG`: the registered algorithm and the recorded signed pairs. -/
structure FSigSt (Msg PK Sig : Type) where
  /-- The registered algorithm. -/
  alg : Option (SigAlg Msg PK Sig)
  /-- The recorded pairs of messages and signatures. -/
  signed : List (Msg × Sig)

variable {Msg PK SK Sig : Type}

/-! ## The functionality -/

section Functionality

variable [DecidableEq Msg] [DecidableEq PK] [DecidableEq Sig]

/-- The verification rule of `F_SIG` with the registered algorithm `a` and the recorded pairs
`signed`: under the registered key, `true` on a recorded pair and `false` on a message never
signed; otherwise the registered predicate. -/
def verifyRule (a : SigAlg Msg PK Sig) (signed : List (Msg × Sig)) (m : Msg) (σ : Sig)
    (vk : PK) : Bool :=
  if vk = a.vk then
    if (m, σ) ∈ signed then true
    else if signed.any (fun p => decide (p.1 = m)) then a.verify vk m σ else false
  else a.verify vk m σ

/-- One activation of `F_SIG` on the honest port. -/
noncomputable def honStep (t : FSigSt Msg PK Sig) (e : SigEv Msg PK Sig) :
    SPComp (FSigSt Msg PK Sig × SigOut PK Sig) :=
  match t.alg, e with
  | none, _ => SPComp.pure (t, .err)
  | some a, .keyGen => SPComp.pure (t, .vk a.vk)
  | some a, .sign m =>
    SPComp.map (fun σ => ({ t with signed := (m, σ) :: t.signed }, .sig σ)) (a.sign m)
  | some a, .verify m σ vk => SPComp.pure (t, .result (verifyRule a t.signed m σ vk))

/-- One activation of `F_SIG` on the adversary port: the first registration installs the
algorithm. -/
noncomputable def advStep (t : FSigSt Msg PK Sig) (a : SigAlg Msg PK Sig) :
    SPComp (FSigSt Msg PK Sig × Unit) :=
  SPComp.pure ({ t with alg := some (t.alg.getD a) }, ())

/-- **The signature functionality `F_SIG`** (unstoppable, honest signer), as a system with one
state and two ports: the honest port of `SigEv` and the adversary port of registrations. -/
noncomputable def fsig :
    Sys (FSigSt Msg PK Sig) (SigEv Msg PK Sig ⊕ SigAlg Msg PK Sig) (SigOut PK Sig ⊕ Unit) :=
  Sys.ofPorts ⟨⟨none, []⟩, honStep⟩ ⟨⟨none, []⟩, advStep⟩

/-- `F_SIG` answers every event on the port of the event. -/
theorem fsig_portTyped : (fsig : Sys (FSigSt Msg PK Sig) _ _).PortTyped :=
  Sys.ofPorts_portTyped _ _

end Functionality

/-! ## The real protocol -/

section Real

variable [DecidableEq Msg] [DecidableEq PK]

/-- The state of the real signer: the key pair once generated, the signed pairs, and the flag
of a forgery. -/
structure RealSt (Msg PK SK Sig : Type) where
  /-- The key pair, once generated. -/
  keys : Option (PK × SK)
  /-- The signed pairs. -/
  signed : List (Msg × Sig)
  /-- A verification accepted a forgery. -/
  forged : Bool

/-- A forgery: a signature `σ` on a message `m` never signed, accepted under the signer's
key `pk`. -/
def isForgery (S : SigScheme Msg PK SK Sig) (pk : PK) (signed : List (Msg × Sig)) (m : Msg)
    (σ : Sig) (vk : PK) : Bool :=
  decide (vk = pk) && !(signed.any fun p => decide (p.1 = m)) && S.verify pk m σ

/-- One activation of the real signer on the honest port. -/
noncomputable def realHonStep (S : SigScheme Msg PK SK Sig) (t : RealSt Msg PK SK Sig)
    (e : SigEv Msg PK Sig) : SPComp (RealSt Msg PK SK Sig × SigOut PK Sig) :=
  match t.keys, e with
  | none, .keyGen => SPComp.map (fun ks => ({ t with keys := some ks }, .vk ks.1)) S.keygen
  | none, _ => SPComp.pure (t, .err)
  | some ks, .keyGen => SPComp.pure (t, .vk ks.1)
  | some ks, .sign m =>
    SPComp.map (fun σ => ({ t with signed := (m, σ) :: t.signed }, .sig σ)) (S.sign ks.2 m)
  | some ks, .verify m σ vk =>
    SPComp.pure ({ t with forged := t.forged || isForgery S ks.1 t.signed m σ vk },
      .result (S.verify vk m σ))

/-- **The real signing system of the scheme `S`**: the signer runs `S` on the honest port; the
adversary port carries no messages. -/
noncomputable def realSig (S : SigScheme Msg PK SK Sig) :
    Sys (RealSt Msg PK SK Sig) (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit) :=
  Sys.ofPorts ⟨⟨none, [], false⟩, realHonStep S⟩
    ⟨⟨none, [], false⟩, fun t _ => SPComp.pure (t, ())⟩

/-- The real signing system answers every event on the port of the event. -/
theorem realSig_portTyped (S : SigScheme Msg PK SK Sig) : (realSig S).PortTyped :=
  Sys.ofPorts_portTyped _ _

end Real

/-! ## The simulator -/

/-- The algorithm of the key pair `ks` of the scheme `S`. -/
def algOf (S : SigScheme Msg PK SK Sig) (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m))
    (ks : PK × SK) : SigAlg Msg PK Sig :=
  ⟨ks.1, S.sign ks.2, S.verify, hsg ks.2⟩

/-- The simulator for `F_SIG` as a multi-call simulator with at most two calls per activation;
its state records whether it has registered an algorithm. On the first `keyGen` it samples a key
pair, registers its algorithm and then forwards `keyGen`; it forwards every other honest event,
and every output of `F_SIG` on the honest port. -/
noncomputable def fsigSimπ (S : SigScheme Msg PK SK Sig) (hkg : SPComp.NoFail S.keygen)
    (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m)) :
    MultiHybrid Bool (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit)
      (SigEv Msg PK Sig ⊕ SigAlg Msg PK Sig) (SigOut PK Sig ⊕ Unit) where
  init := false
  fuel := 1
  start s e := match s, e with
    | false, .inl .keyGen => SPComp.map (fun ks => (true, .inl (.inr (algOf S hsg ks)))) S.keygen
    | s, .inl h => SPComp.pure (s, .inl (.inl h))
    | s, .inr _ => SPComp.pure (s, .inr (.inr ()))
  resume s o := match o with
    | .inl h => SPComp.pure (s, .inr (.inl h))
    | .inr _ => SPComp.pure (s, .inl (.inl .keyGen))
  finish s o := match o with
    | .inl h => SPComp.pure (s, .inl h)
    | .inr _ => SPComp.pure (s, .inl .err)
  start_noFail s e := by
    rcases s with _ | _ <;> rcases e with ((_ | _ | _) | _) <;>
      first
      | exact SPComp.pure_noFail _
      | exact Assumptions.SPComp.bind_noFail hkg fun _ => SPComp.pure_noFail _
  resume_noFail s o := by rcases o with _ | _ <;> exact SPComp.pure_noFail _
  finish_noFail s o := by rcases o with _ | _ <;> exact SPComp.pure_noFail _

/-- The view of the honest port: the kind of each event; honest outputs are not seen. -/
def honView : PubView (SigEv Msg PK Sig) (SigOut PK Sig) :=
  PubView.ofProj SigEv.kind fun _ => ()

/-- The view of the outer interface of the simulator: the honest view on the honest port and
equality on the adversary port. -/
def outerView : PubView (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit) :=
  honView.sum PubView.eqView

/-- The view of the interface of `F_SIG`: the honest view on the honest port and equality on the
adversary port. -/
def fsigView : PubView (SigEv Msg PK Sig ⊕ SigAlg Msg PK Sig) (SigOut PK Sig ⊕ Unit) :=
  honView.sum PubView.eqView

/-- Equal decisions of the simulator are related for `outerView` and `fsigView`. -/
theorem stepRel_refl
    (d : (SigEv Msg PK Sig ⊕ SigAlg Msg PK Sig) ⊕ (SigOut PK Sig ⊕ Unit)) :
    (outerView : PubView (SigEv Msg PK Sig ⊕ Unit) _).StepRel fsigView d d := by
  rcases d with (g | g) | (o | o)
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl

/-- **The simulator is opaque** from `fsigView` to `outerView`, with equality of simulator states
as the unwinding relation: its decisions depend on the kind of honest events only, and it passes
the outputs of `F_SIG` on the honest port to the honest port. -/
theorem fsigSimπ_opaque (S : SigScheme Msg PK SK Sig) (hkg : SPComp.NoFail S.keygen)
    (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m)) :
    (fsigSimπ S hkg hsg).Opaque outerView fsigView := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    cases he with
    | inl hk =>
      rename_i h h'
      cases s <;> cases h <;> cases h' <;> simp [honView, PubView.ofProj, SigEv.kind] at hk <;>
        first
        | exact rHoare_ret fun _ _ hh => ⟨hh, rfl, by
            simp [PubView.StepRel, fsigView, honView, PubView.sum, PubView.ofProj, SigEv.kind]⟩
        | exact rHoare_conseq (fun _ _ hh => hh)
            (fun _ _ _ _ hp => by
              obtain ⟨rfl, rfl⟩ := hp
              exact ⟨rfl, rfl, stepRel_refl _⟩)
            (rHoare_refl _)
    | inr hk =>
      cases s <;> exact rHoare_ret fun _ _ hh => ⟨hh, rfl, stepRel_refl _⟩
  · rintro s _ o o' rfl ho
    cases ho with
    | inl hk => exact rHoare_ret fun _ _ hh => ⟨hh, rfl, by
        simp [PubView.StepRel, outerView, honView, PubView.sum, PubView.ofProj]⟩
    | inr hk => exact rHoare_ret fun _ _ hh => ⟨hh, rfl, by
        simp [PubView.StepRel, fsigView, honView, PubView.sum, PubView.ofProj, SigEv.kind]⟩
  · rintro s _ o o' rfl ho
    cases ho with
    | inl hk => exact rHoare_ret fun _ _ hh => ⟨hh, rfl, by
        simp [outerView, honView, PubView.sum, PubView.ofProj]⟩
    | inr hk => exact rHoare_ret fun _ _ hh => ⟨hh, rfl, by
        simp [outerView, honView, PubView.sum, PubView.ofProj, PubView.eqView]⟩

/-- **The simulator for `F_SIG`** as a bundled opaque simulator from `fsigView` to `outerView`.
-/
noncomputable def fsigSim (S : SigScheme Msg PK SK Sig) (hkg : SPComp.NoFail S.keygen)
    (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m)) :
    Simulator (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit)
      (SigEv Msg PK Sig ⊕ SigAlg Msg PK Sig) (SigOut PK Sig ⊕ Unit) outerView fsigView :=
  Simulator.ofMultiHybrid (fsigSimπ S hkg hsg) (fsigSimπ_opaque S hkg hsg)

/-! ## Losslessness -/

/-- The rest of an activation of a multi-call simulator over a lossless subroutine never
fails. -/
theorem drive_noFail {σ τ E O EG OG : Type} (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (hX : ∀ t g, SPComp.NoFail (X.step t g)) :
    ∀ n s d t, SPComp.NoFail (π.drive X n s d t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t
    · exact Assumptions.SPComp.bind_noFail (hX _ _) fun _ =>
        Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact SPComp.pure_noFail _
  | succ n ih =>
    rintro s (g | o) t
    · exact Assumptions.SPComp.bind_noFail (hX _ _) fun _ =>
        Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => ih _ _ _
    · exact SPComp.pure_noFail _

/-- Single steps of a multi-call simulator over a lossless subroutine never fail. -/
theorem withSub_noFail {σ τ E O EG OG : Type} (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (hX : ∀ t g, SPComp.NoFail (X.step t g)) :
    ∀ t e, SPComp.NoFail ((π.withSub X).step t e) := by
  intro t e
  simp only [MultiHybrid.withSub]
  exact Assumptions.SPComp.bind_noFail (π.start_noFail _ _) fun _ =>
    Assumptions.SPComp.bind_noFail (drive_noFail π X hX _ _ _ _) fun _ => SPComp.pure_noFail _

section Realization

variable [DecidableEq Msg] [DecidableEq PK] [DecidableEq Sig]

/-- The honest steps of `F_SIG` never fail. -/
theorem honStep_noFail (t : FSigSt Msg PK Sig) (e : SigEv Msg PK Sig) :
    SPComp.NoFail (honStep t e) := by
  rcases t with ⟨_ | a, signed⟩ <;> rcases e with _ | m | ⟨m, σ, vk⟩ <;>
    simp only [honStep] <;>
    first
    | exact SPComp.pure_noFail _
    | exact Assumptions.SPComp.bind_noFail (a.sign_noFail m) fun _ => SPComp.pure_noFail _

/-- The steps of `F_SIG` never fail. -/
theorem fsig_noFail :
    ∀ t e, SPComp.NoFail ((fsig : Sys (FSigSt Msg PK Sig) _ _).step t e) := by
  rintro t (h | a)
  · simp only [fsig, Sys.ofPorts_step_inl]
    exact Assumptions.SPComp.bind_noFail (honStep_noFail _ _) fun _ => SPComp.pure_noFail _
  · simp only [fsig, Sys.ofPorts_step_inr]
    exact Assumptions.SPComp.bind_noFail (SPComp.pure_noFail _) fun _ => SPComp.pure_noFail _

omit [DecidableEq Sig] in
/-- The honest steps of the real signer of a lossless scheme never fail. -/
theorem realHonStep_noFail (S : SigScheme Msg PK SK Sig) (hkg : SPComp.NoFail S.keygen)
    (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m)) (t : RealSt Msg PK SK Sig)
    (e : SigEv Msg PK Sig) : SPComp.NoFail (realHonStep S t e) := by
  rcases t with ⟨_ | ks, signed, forged⟩ <;> rcases e with _ | m | ⟨m, σ, vk⟩ <;>
    simp only [realHonStep] <;>
    first
    | exact SPComp.pure_noFail _
    | exact Assumptions.SPComp.bind_noFail hkg fun _ => SPComp.pure_noFail _
    | exact Assumptions.SPComp.bind_noFail (hsg _ _) fun _ => SPComp.pure_noFail _

omit [DecidableEq Sig] in
/-- The steps of the real signing system of a lossless scheme never fail. -/
theorem realSig_noFail (S : SigScheme Msg PK SK Sig) (hkg : SPComp.NoFail S.keygen)
    (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m)) :
    ∀ t e, SPComp.NoFail ((realSig S).step t e) := by
  rintro t (h | u)
  · simp only [realSig, Sys.ofPorts_step_inl]
    exact Assumptions.SPComp.bind_noFail (realHonStep_noFail S hkg hsg _ _) fun _ =>
      SPComp.pure_noFail _
  · simp only [realSig, Sys.ofPorts_step_inr]
    exact Assumptions.SPComp.bind_noFail (SPComp.pure_noFail _) fun _ => SPComp.pure_noFail _

/-- Consistency of the scheme `S` in relational form, for the invariant `ok` of key pairs: key
generation, run twice from equal heaps, is coupled into equal key pairs satisfying `ok` and
equal heaps; for a key pair satisfying `ok`, signing, run twice from equal heaps, is coupled into
equal signatures that verify under its public key and equal heaps. -/
structure ConsistentOn (S : SigScheme Msg PK SK Sig) (ok : PK × SK → Prop) : Prop where
  /-- Key generation produces key pairs satisfying `ok`. -/
  keygen : rHoare eqPre S.keygen S.keygen fun ks h ks' h' => ks = ks' ∧ h = h' ∧ ok ks
  /-- Signing under a key pair satisfying `ok` produces verifying signatures. -/
  sign : ∀ ks, ok ks → ∀ m, rHoare eqPre (S.sign ks.2 m) (S.sign ks.2 m)
    fun σ h σ' h' => σ = σ' ∧ h = h' ∧ S.verify ks.1 m σ = true

/-- The relation of the real state and the state of the simulator over `F_SIG`: equal signed
pairs; before key generation no algorithm is registered and nothing is signed; afterwards the
registered algorithm is that of the real key pair, which satisfies `ok`, and every signed pair
verifies under its public key. -/
def simRel (S : SigScheme Msg PK SK Sig) (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m))
    (ok : PK × SK → Prop) (t : RealSt Msg PK SK Sig) (u : Bool × FSigSt Msg PK Sig) : Prop :=
  u.2.signed = t.signed ∧
    match t.keys with
    | none => u.1 = false ∧ u.2.alg = none ∧ t.signed = []
    | some ks => u.1 = true ∧ u.2.alg = some (algOf S hsg ks) ∧ ok ks ∧
        ∀ p ∈ t.signed, S.verify ks.1 p.1 p.2 = true

/-- Without a forgery, the verification rule of `F_SIG` with the algorithm of the key pair `ks`
returns the verification of `S`, when every signed pair verifies. -/
theorem verifyRule_algOf (S : SigScheme Msg PK SK Sig) (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m))
    (ks : PK × SK) (signed : List (Msg × Sig)) (m : Msg) (σ : Sig) (vk : PK)
    (hsigned : ∀ p ∈ signed, S.verify ks.1 p.1 p.2 = true)
    (hf : isForgery S ks.1 signed m σ vk = false) :
    verifyRule (algOf S hsg ks) signed m σ vk = S.verify vk m σ := by
  unfold verifyRule isForgery at *
  by_cases hvk : vk = ks.1
  · subst hvk
    by_cases hmem : (m, σ) ∈ signed
    · simp [algOf, hmem, hsigned _ hmem]
    · simp [algOf, hmem] at hf ⊢; grind
  · simp [algOf, hvk]

/-- **The real signing system realizes `F_SIG` behind the simulator, up to forgery.** For a
lossless scheme `S` consistent in relational form (`ConsistentOn`), the signer running `S`
realizes the unstoppable signature functionality `fsig` behind the opaque simulator `fsigSim`,
for every environment `Z`, with bound the probability that the run of `Z` against `realSig S`
contains a verification that accepts, under the signer's key, a message never signed. -/
theorem realSig_realizesSim_fsig (S : SigScheme Msg PK SK Sig) (hkg : SPComp.NoFail S.keygen)
    (hsg : ∀ sk m, SPComp.NoFail (S.sign sk m)) (ok : PK × SK → Prop)
    (hcons : ConsistentOn S ok) :
    RealizesSim (realSig S) fsig (fsigSim S hkg hsg)
      (fun _ Z => prBad (realSig S) (fun t => t.forged) Z) := by
  refine realizes_upto_bad_rel (realSig S) ((fsigSimπ S hkg hsg).withSub fsig) (simRel S hsg ok)
    (fun t => t.forged) ⟨rfl, rfl, rfl, rfl⟩ (realSig_noFail S hkg hsg)
    (withSub_noFail _ _ fsig_noFail) ?_
  rintro ⟨keys, signed, forged⟩ ⟨s, alg, signed'⟩ e hrel hf
  obtain ⟨hsig, hrel⟩ := hrel
  simp only at hsig hf
  subst hsig hf
  rcases e with h | u
  · rcases keys with _ | ks
    · obtain ⟨rfl, rfl, rfl⟩ := hrel
      rcases h with _ | m | ⟨m, σ, vk⟩ <;>
        simp only [realSig, fsig, Sys.ofPorts_step_inl, Sys.ofPorts_step_inr, MultiHybrid.withSub,
          MultiHybrid.drive, fsigSimπ, honStep, advStep, realHonStep, SPComp.map,
          SPComp.bind_assoc, SPComp.pure_bind]
      · exact rHoare_bind hcons.keygen fun ks ks' => rHoare_ret fun _ _ hh => by
          obtain ⟨rfl, rfl, hok⟩ := hh
          exact Or.inr ⟨rfl, ⟨rfl, rfl, rfl, hok, by simp⟩, rfl⟩
      · exact rHoare_ret fun _ _ hh => Or.inr ⟨hh, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
      · exact rHoare_ret fun _ _ hh => Or.inr ⟨hh, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    · obtain ⟨rfl, rfl, hok, hver⟩ := hrel
      rcases h with _ | m | ⟨m, σ, vk⟩ <;>
        simp only [realSig, fsig, Sys.ofPorts_step_inl, MultiHybrid.withSub,
          MultiHybrid.drive, fsigSimπ, honStep, realHonStep, algOf, SPComp.map,
          SPComp.bind_assoc, SPComp.pure_bind]
      · exact rHoare_ret fun _ _ hh => Or.inr ⟨hh, ⟨rfl, rfl, rfl, hok, hver⟩, rfl⟩
      · exact rHoare_bind (hcons.sign ks hok m) fun σ σ' => rHoare_ret fun _ _ hh => by
          obtain ⟨rfl, rfl, hv⟩ := hh
          refine Or.inr ⟨rfl, ⟨rfl, rfl, rfl, hok, ?_⟩, rfl⟩
          simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨hv, hver⟩
      · refine rHoare_ret fun _ _ hh => ?_
        cases hfg : isForgery S ks.1 signed' m σ vk
        · refine Or.inr ⟨hh, ⟨rfl, rfl, rfl, hok, hver⟩, ?_⟩
          have := verifyRule_algOf S hsg ks signed' m σ vk hver hfg
          simp only [algOf] at this
          simp [this]
        · exact Or.inl (by simp)
  · cases s <;>
      simp only [realSig, fsig, Sys.ofPorts_step_inr, MultiHybrid.withSub, MultiHybrid.drive,
        fsigSimπ, SPComp.map, SPComp.pure_bind] <;>
      exact rHoare_ret fun _ _ hh => Or.inr ⟨hh, ⟨rfl, hrel⟩, rfl⟩

end Realization

end CatCrypt.Crypto.Signatures.FSigSys

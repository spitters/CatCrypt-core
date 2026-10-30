/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCChannel
public import CatCryptCore.Crypto.UCWake

/-!
# The key-exchange ideal functionalities as port-split systems

Two multi-session ideal functionalities for key exchange, each a system `Sys.ofPorts hon adv`
with an honest port and an adversary port over one shared state, and each also in a form whose
key delivery activates the recipient (`Sys.wakeClose` of `CatCryptCore.Crypto.UCWake`).

`F_AKE keySample` is the authenticated key-exchange functionality of Canetti and Krawczyk
(Eurocrypt 2002, there named `F_KE`), after Canetti (FOCS 2001), with adversarially scheduled
key delivery and corruption of parties. A session is the record of the party `pid` in the
protocol session `sid`, with its intended peer and its role (`initiator` or `responder`).
* Honest port: `newSession sid pid peer role` records the session, marked fresh, unless a
  record of `pid` in `sid` exists; `getKey sid pid` returns the key of the session, if any.
* Adversary port: `poll` returns the next notice `(sid, pid, peer, role)` of a new session;
  `corrupt pid` marks the party `pid` corrupt; `newKey sid pid k` applies to a session without
  a key and delivers to it
  - the adversary key `k` when the party or its peer is corrupt or the session is compromised
    (the session is then marked compromised);
  - otherwise the key of the session of `peer` in `sid` when that session has `pid` as peer,
    the other role, and received a key chosen by the functionality (it is marked completed);
  - otherwise a fresh sample of `keySample`.
  `newKeyUnlinked sid pid k` is `newKey` without the second clause: the adversary may give a
  session a key independent of its partner's, as an active attacker does who changes a message
  between them; the key is still the adversary key only for an exposed session.
  `impersonate sid pid` changes nothing, and `idle` changes nothing.
  Corruption is adaptive and affects the sessions that receive their key after it; the
  functionality has no event that reveals a delivered key or the state of a party.

`F_KE keySample` is the unauthenticated variant: `impersonate sid pid` marks a fresh session
without a key compromised, so that `newKey` delivers the adversary key to it. This models an
adversary that runs the exchange with the party in place of its peer.

**What the adversary port shows.** The outputs of the adversary port are acknowledgements and
notices; they carry no key (`AOut` has no key type). The honest events carry no secret, and
both functionalities are opaque for the view that relates equal events, any two honest outputs
and equal adversary outputs (`F_AKE_opaque`, `F_KE_opaque`, and the wake forms).

**Keys.** A session without a key whose party and peer are honest, which is not compromised and
whose partner has not completed, receives the fresh sample, whatever key the adversary proposes
(`F_AKE_step_newKey_fresh`); a session whose party or peer is corrupt receives the adversary key
(`newKeyStep_key_exposed`); a session whose partner completed receives the key of the partner
(`newKeyStep_key_partner`).

**Correctness.** Two honest partner sessions of different roles receive the same fresh key when
the adversary delivers keys to both and corrupts neither party (`F_AKE_correct`).

## Main definitions

* `FAKE.St`: the shared state (session records, corrupt parties, notices, cursor).
* `F_AKE`, `F_KE`: the two functionalities.
* `F_AKEWake`, `F_KEWake`: the forms in which `newKey` activates the recipient, which outputs
  its key on the honest port.
* `keHonView`: the view of the honest port.

## Main results

* `F_AKE_portTyped`, `F_KE_portTyped`, `F_AKE_idleAt`, `F_KE_idleAt`.
* `F_AKE_opaque`, `F_KE_opaque`, `F_AKEWake_opaque`, `F_KEWake_opaque`.
* `newKeyStep_key_exposed`, `newKeyStep_key_partner`, `newKeyStep_key_fresh`,
  `newKeyFreshStep_key`, `F_AKE_step_newKey_fresh`, `F_AKE_step_impersonate`.
* `F_AKE_correct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open PubView (eqView)

namespace FAKE

/-! ## Identifiers, records and the state -/

/-- Party identifier. -/
abbrev PartyId := ℕ

/-- Protocol session identifier, shared by the two partners of a session. -/
abbrev SessionId := ℕ

/-- A session: the protocol session identifier and the party. -/
abbrev Inst := SessionId × PartyId

/-- Role of a party in a session. -/
inductive Role where
  /-- The party that sends the first message. -/
  | initiator
  /-- The party that answers. -/
  | responder
  deriving DecidableEq

/-- Status of a session. -/
inductive Status where
  /-- No key and not compromised. -/
  | fresh
  /-- The session receives, or received, the key of the adversary. -/
  | compromised
  /-- The session received a key chosen by the functionality. -/
  | completed
  deriving DecidableEq

/-- The public part of a new session: what the adversary learns of it. -/
structure Notice where
  /-- The protocol session. -/
  sid : SessionId
  /-- The party. -/
  pid : PartyId
  /-- The intended peer. -/
  peer : PartyId
  /-- The role of the party. -/
  role : Role

/-- The record of a session. -/
structure Rec (K : Type) where
  /-- The intended peer. -/
  peer : PartyId
  /-- The role of the party. -/
  role : Role
  /-- The status. -/
  status : Status
  /-- The key delivered to the session, if any. -/
  key : Option K

/-- The state of both functionalities. -/
structure St (K : Type) where
  /-- The session records. -/
  recs : Inst → Option (Rec K)
  /-- The corrupt parties. -/
  corrupt : PartyId → Bool
  /-- The notices of the new sessions, oldest first. -/
  notices : List Notice
  /-- The number of notices already shown to the adversary. -/
  cursor : ℕ

/-- Outputs of the honest port. -/
inductive HOut (K : Type) where
  /-- Acknowledgement. -/
  | ok
  /-- The key of a session, if delivered. -/
  | key (o : Option K)

/-- Outputs of the adversary port. -/
inductive AOut where
  /-- Acknowledgement. -/
  | ack
  /-- The next notice not yet shown, if any. -/
  | notice (o : Option Notice)

variable {K : Type}

/-- The initial state: no session, no corrupt party, no notice. -/
def initSt : St K := ⟨fun _ => none, fun _ => false, [], 0⟩

/-- The state with the record `r` at `x`. -/
def setRec (t : St K) (x : Inst) (r : Rec K) : St K :=
  { t with recs := Function.update t.recs x (some r) }

/-- A new fresh session at `x` with its notice, when `x` has no record. -/
def addSession (t : St K) (x : Inst) (peer : PartyId) (role : Role) : St K :=
  if (t.recs x).isSome then t else
    { t with recs := Function.update t.recs x (some ⟨peer, role, .fresh, none⟩),
             notices := t.notices ++ [⟨x.1, x.2, peer, role⟩] }

/-- The key of the session `x`, if delivered. -/
def keyOf (t : St K) (x : Inst) : Option K := (t.recs x).bind Rec.key

/-- The step of `poll`: the next notice not yet shown, and the advanced cursor. -/
def pollStep (t : St K) : St K × Option Notice :=
  match t.notices[t.cursor]? with
  | some n => ({ t with cursor := t.cursor + 1 }, some n)
  | none => (t, none)

/-- The state after `corrupt pid`. -/
def corruptStep (t : St K) (pid : PartyId) : St K :=
  { t with corrupt := Function.update t.corrupt pid true }

/-- The state after `impersonate` at `x` in the unauthenticated functionality: a fresh session
without a key is marked compromised. -/
def impStep (t : St K) (x : Inst) : St K :=
  match t.recs x with
  | some r =>
    if r.status = .fresh ∧ r.key.isNone then setRec t x { r with status := .compromised } else t
  | none => t

/-- The session `x` with record `r` receives the adversary key: its party or its peer is
corrupt, or it is compromised. -/
def Exposed (t : St K) (x : Inst) (r : Rec K) : Prop :=
  t.corrupt x.2 = true ∨ t.corrupt r.peer = true ∨ r.status = .compromised

instance (t : St K) (x : Inst) (r : Rec K) : Decidable (Exposed t x r) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The record `p` is the partner of the session `x` with record `r`: it has the party of `x`
as peer, the other role, and received a key chosen by the functionality. -/
def Partner (x : Inst) (r p : Rec K) : Prop :=
  p.peer = x.2 ∧ p.role ≠ r.role ∧ p.status = .completed

instance (x : Inst) (r p : Rec K) : Decidable (Partner x r p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The key that `newKey` gives to the session `x` with record `r`, for the adversary key `k`
and the fresh sample `kf`: `k` to an exposed session; the key of the partner, if there is one;
`kf` otherwise. -/
def newKeyVal (t : St K) (x : Inst) (r : Rec K) (k kf : K) : K :=
  if Exposed t x r then k else
    match t.recs (x.1, r.peer) with
    | some p => if Partner x r p then p.key.getD kf else kf
    | none => kf

/-- The state after `newKey` at `x` with the adversary key `k` and the fresh sample `kf`. -/
def newKeyStep (t : St K) (x : Inst) (k kf : K) : St K :=
  match t.recs x with
  | some r =>
    if r.key.isNone then
      setRec t x { r with key := some (newKeyVal t x r k kf),
                          status := if Exposed t x r then .compromised else .completed }
    else t
  | none => t

/-- The state after `newKeyUnlinked` at `x` with the adversary key `k` and the fresh sample
`kf`: `k` to an exposed session, `kf` otherwise, whatever the partner received. -/
def newKeyFreshStep (t : St K) (x : Inst) (k kf : K) : St K :=
  match t.recs x with
  | some r =>
    if r.key.isNone then
      setRec t x { r with key := some (if Exposed t x r then k else kf),
                          status := if Exposed t x r then .compromised else .completed }
    else t
  | none => t

/-! ## Events and the ports -/

/-- Events of the honest port. -/
inductive HEv where
  /-- The party `pid` starts the session `sid` with `peer` in the role `role`. -/
  | newSession (sid : SessionId) (pid peer : PartyId) (role : Role)
  /-- The party `pid` asks for the key of the session `sid`. -/
  | getKey (sid : SessionId) (pid : PartyId)

/-- Events of the adversary port. -/
inductive AEv (K : Type) where
  /-- No action. -/
  | idle
  /-- Read the next notice not yet shown. -/
  | poll
  /-- Corrupt the party `pid`. -/
  | corrupt (pid : PartyId)
  /-- Take the place of the peer of the session of `pid` in `sid` (unauthenticated
  functionality only). -/
  | impersonate (sid : SessionId) (pid : PartyId)
  /-- Deliver a key to the session of `pid` in `sid`; `k` is used if the session is exposed. -/
  | newKey (sid : SessionId) (pid : PartyId) (k : K)
  /-- Deliver a key to the session of `pid` in `sid` that is not the key of its partner; `k` is
  used if the session is exposed. -/
  | newKeyUnlinked (sid : SessionId) (pid : PartyId) (k : K)

/-- A step of the honest port. -/
def honStep (t : St K) : HEv → St K × HOut K
  | .newSession sid pid peer role => (addSession t (sid, pid) peer role, .ok)
  | .getKey sid pid => (t, .key (keyOf t (sid, pid)))

/-- The honest port as a system. -/
noncomputable def honSys : Sys (St K) HEv (HOut K) where
  init := initSt
  step t e := SPComp.pure (honStep t e)

/-- The honest port with wakes: the wake `x` outputs the key of the session `x`. -/
noncomputable def honSysW : Sys (St K) (HEv ⊕ Inst) (HOut K) where
  init := initSt
  step t
    | .inl e => SPComp.pure (honStep t e)
    | .inr x => SPComp.pure (t, .key (keyOf t x))

/-- The adversary port as a system: `newKey` draws a fresh sample of `keySample`; every other
event is deterministic; `auth` disables `impersonate`. -/
noncomputable def advSys (auth : Bool) (keySample : SPComp K) : Sys (St K) (AEv K) AOut where
  init := initSt
  step t e := match e with
    | .idle => SPComp.pure (t, .ack)
    | .poll => SPComp.pure ((pollStep t).1, .notice (pollStep t).2)
    | .corrupt pid => SPComp.pure (corruptStep t pid, .ack)
    | .impersonate sid pid => SPComp.pure (if auth then t else impStep t (sid, pid), .ack)
    | .newKey sid pid k => SPComp.map (fun kf => (newKeyStep t (sid, pid) k kf, .ack)) keySample
    | .newKeyUnlinked sid pid k =>
      SPComp.map (fun kf => (newKeyFreshStep t (sid, pid) k kf, .ack)) keySample

/-- The recipient woken by an adversary event: the session of `newKey`. -/
def keyDlv : AEv K → Option Inst
  | .newKey sid pid _ => some (sid, pid)
  | .newKeyUnlinked sid pid _ => some (sid, pid)
  | _ => none

/-- The cut-off answer of the wake closure. -/
def keyCut (_ : Inst) : HOut K ⊕ AOut := .inr .ack

end FAKE

open FAKE

/-! ## Views -/

/-- The view of the honest port: equal events, any two outputs. -/
def keHonView {K : Type} : PubView HEv (HOut K) where
  ev := Eq
  out _ _ := True

/-! ## The functionalities -/

/-- **The ideal authenticated key exchange** with the key distribution `keySample`: the honest
port on the left, the adversary port on the right, one shared state. -/
noncomputable def F_AKE {K : Type} (keySample : SPComp K) :
    Sys (St K) (HEv ⊕ AEv K) (HOut K ⊕ AOut) :=
  Sys.ofPorts honSys (advSys true keySample)

/-- **The ideal unauthenticated key exchange** with the key distribution `keySample`: as
`F_AKE`, with `impersonate` enabled. -/
noncomputable def F_KE {K : Type} (keySample : SPComp K) :
    Sys (St K) (HEv ⊕ AEv K) (HOut K ⊕ AOut) :=
  Sys.ofPorts honSys (advSys false keySample)

/-- **`F_AKE` with activation on delivery**: `newKey sid pid k` activates the party `pid`, which
outputs the key of its session `sid` on the honest port. -/
noncomputable def F_AKEWake {K : Type} (keySample : SPComp K) :
    Sys (Unit × St K) (HEv ⊕ AEv K) (HOut K ⊕ AOut) :=
  (Sys.ofPorts honSysW (advSys true keySample)).wakeClose keyDlv keyCut

/-- **`F_KE` with activation on delivery**. -/
noncomputable def F_KEWake {K : Type} (keySample : SPComp K) :
    Sys (Unit × St K) (HEv ⊕ AEv K) (HOut K ⊕ AOut) :=
  (Sys.ofPorts honSysW (advSys false keySample)).wakeClose keyDlv keyCut

section Functionalities

variable {K : Type}

/-! ## Ports, idling and opacity -/

/-- `F_AKE` answers every event on the port of the event. -/
theorem F_AKE_portTyped (keySample : SPComp K) : (F_AKE keySample).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `F_KE` answers every event on the port of the event. -/
theorem F_KE_portTyped (keySample : SPComp K) : (F_KE keySample).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `F_AKE` is idle at the adversary event `idle`. -/
theorem F_AKE_idleAt (keySample : SPComp K) :
    MultiHybrid.IdleAt (F_AKE keySample) (.inr .idle) (.inr .ack) := fun t => by
  simp [F_AKE, advSys]

/-- `F_KE` is idle at the adversary event `idle`. -/
theorem F_KE_idleAt (keySample : SPComp K) :
    MultiHybrid.IdleAt (F_KE keySample) (.inr .idle) (.inr .ack) := fun t => by
  simp [F_KE, advSys]

/-- A system on the key-exchange interface is opaque for `keHonView.sum eqView`: the view is
the equality on events and relates more outputs than the equality. -/
theorem opaque_keView {τ : Type} (X : Sys τ (HEv ⊕ AEv K) (HOut K ⊕ AOut)) :
    X.Opaque (keHonView.sum eqView) :=
  (Sys.opaque_eqView X).mono
    (fun e e' h => by
      cases h with
      | inl h => exact congrArg Sum.inl h
      | inr h => exact congrArg Sum.inr h)
    (fun o o' h => by
      subst h
      cases o
      · exact Sum.LiftRel.inl trivial
      · exact Sum.LiftRel.inr rfl)

/-- **Opacity of `F_AKE`**: equal events give equal adversary outputs; the keys reach only the
honest port. -/
theorem F_AKE_opaque (keySample : SPComp K) : (F_AKE keySample).Opaque (keHonView.sum eqView) :=
  opaque_keView _

/-- **Opacity of `F_KE`**. -/
theorem F_KE_opaque (keySample : SPComp K) : (F_KE keySample).Opaque (keHonView.sum eqView) :=
  opaque_keView _

/-- **Opacity of `F_AKEWake`**. -/
theorem F_AKEWake_opaque (keySample : SPComp K) :
    (F_AKEWake keySample).Opaque (keHonView.sum eqView) :=
  opaque_keView _

/-- **Opacity of `F_KEWake`**. -/
theorem F_KEWake_opaque (keySample : SPComp K) :
    (F_KEWake keySample).Opaque (keHonView.sum eqView) :=
  opaque_keView _

/-! ## Keys -/

/-- An exposed session without a key receives the adversary key. -/
theorem newKeyStep_key_exposed {t : St K} {x : Inst} {r : Rec K} (k kf : K)
    (hr : t.recs x = some r) (hk : r.key = none) (he : Exposed t x r) :
    keyOf (newKeyStep t x k kf) x = some k := by
  simp [newKeyStep, hr, hk, setRec, keyOf, newKeyVal, he]

/-- A session without a key that is not exposed and whose partner completed receives the key
of the partner. -/
theorem newKeyStep_key_partner {t : St K} {x : Inst} {r p : Rec K} (k kf : K)
    (hr : t.recs x = some r) (hk : r.key = none) (he : ¬ Exposed t x r)
    (hp : t.recs (x.1, r.peer) = some p) (hpp : Partner x r p) :
    keyOf (newKeyStep t x k kf) x = some (p.key.getD kf) := by
  simp [newKeyStep, hr, hk, setRec, keyOf, newKeyVal, he, hp, hpp]

/-- A session without a key that is not exposed and has no completed partner receives the
fresh sample. -/
theorem newKeyStep_key_fresh {t : St K} {x : Inst} {r : Rec K} (k kf : K)
    (hr : t.recs x = some r) (hk : r.key = none) (he : ¬ Exposed t x r)
    (hp : ∀ p, t.recs (x.1, r.peer) = some p → ¬ Partner x r p) :
    keyOf (newKeyStep t x k kf) x = some kf := by
  have hv : newKeyVal t x r k kf = kf := by
    unfold newKeyVal
    simp only [he, ↓reduceIte]
    split
    · next p hp' => simp only [hp p hp', ↓reduceIte]
    · rfl
  simp [newKeyStep, hr, hk, setRec, keyOf, hv]

/-- **The fresh key of `F_AKE`.** At a session without a key that is not exposed and has no
completed partner, the step of `newKey` stores a fresh sample of `keySample` and marks the
session completed, whatever key `k` the adversary proposes. -/
theorem F_AKE_step_newKey_fresh (keySample : SPComp K) {t : St K} {sid : SessionId}
    {pid : PartyId} {r : Rec K} (k : K) (hr : t.recs (sid, pid) = some r) (hk : r.key = none)
    (he : ¬ Exposed t (sid, pid) r)
    (hp : ∀ p, t.recs (sid, r.peer) = some p → ¬ Partner (sid, pid) r p) :
    (F_AKE keySample).step t (.inr (.newKey sid pid k)) =
      SPComp.map (fun kf => (setRec t (sid, pid) { r with key := some kf, status := .completed },
        .inr .ack)) keySample := by
  have hv : ∀ kf, newKeyVal t (sid, pid) r k kf = kf := by
    intro kf
    unfold newKeyVal
    simp only [he, ↓reduceIte]
    split
    · next p hp' => simp only [hp p hp', ↓reduceIte]
    · rfl
  simp [F_AKE, advSys, newKeyStep, hr, hk, hv, he, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]

/-- A session without a key that `newKeyUnlinked` reaches receives the adversary key when it is
exposed and the fresh sample otherwise. -/
theorem newKeyFreshStep_key {t : St K} {x : Inst} {r : Rec K} (k kf : K)
    (hr : t.recs x = some r) (hk : r.key = none) :
    keyOf (newKeyFreshStep t x k kf) x = some (if Exposed t x r then k else kf) := by
  simp [newKeyFreshStep, hr, hk, setRec, keyOf]

/-- `impersonate` changes nothing in `F_AKE`. -/
theorem F_AKE_step_impersonate (keySample : SPComp K) (t : St K) (sid : SessionId)
    (pid : PartyId) :
    (F_AKE keySample).step t (.inr (.impersonate sid pid)) = SPComp.pure (t, .inr .ack) := by
  simp [F_AKE, advSys]

/-! ## Correctness -/

/-- **Correctness of `F_AKE`**: two new partner sessions of the honest parties `a` and `b` in
`sid` with different roles, followed by `newKey` at both, give both the key sampled at the
first `newKey`, whatever keys the adversary proposes. -/
theorem F_AKE_correct (t : St K) (sid : SessionId) (a b : PartyId) (ra rb : Role)
    (k₁ k₂ kf₁ kf₂ : K) (hab : a ≠ b) (hr : ra ≠ rb) (ha : t.recs (sid, a) = none)
    (hb : t.recs (sid, b) = none) (hca : t.corrupt a = false) (hcb : t.corrupt b = false) :
    let t₂ := (honStep (honStep t (.newSession sid a b ra)).1 (.newSession sid b a rb)).1
    let t₄ := newKeyStep (newKeyStep t₂ (sid, a) k₁ kf₁) (sid, b) k₂ kf₂
    keyOf t₄ (sid, a) = some kf₁ ∧ keyOf t₄ (sid, b) = some kf₁ := by
  simp [honStep, addSession, ha, hb, newKeyStep, newKeyVal, Exposed, Partner, setRec, keyOf,
    hab, Ne.symm hab, hr, hca, hcb]

end Functionalities

end CatCrypt.Crypto.UCTransparent

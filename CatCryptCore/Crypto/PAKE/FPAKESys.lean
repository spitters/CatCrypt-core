/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCChannel

/-!
# The PAKE ideal functionalities as port-split systems

Two ideal functionalities for password-authenticated key exchange, each a system
`Sys.ofPorts hon adv` with an honest port and an adversary port over one shared state.

`F_lePAKE keySample` is the functionality `F_pwKE` of Canetti, Halevi, Katz, Lindell and
MacKenzie (Eurocrypt 2005) with the late password test of the lazy-extraction relaxation
(Abdalla, Barbosa, Bradley, Jarecki, Katz, Xu, CRYPTO 2020; Abdalla, Haase, Hesse,
Asiacrypt 2021). A session is the record of the party `pid` in the protocol session `sid`.
* Honest port: `newSession sid pid peer role pw` creates the session with the password `pw`;
  `getKey sid pid` returns the key of the session, if one was delivered.
* Adversary port: `poll` returns the next notice `(sid, pid, peer, role)` of a new session,
  without its password; `testPwd sid pid g` is the one online guess against a fresh session and
  answers whether `g` is its password, marking it compromised or interrupted;
  `newKey sid pid k` delivers a key: `k` to a compromised session, the key of the partner
  session to a fresh session whose partner completed while fresh with the same password, and a
  fresh sample of `keySample` otherwise; `lateTestPwd sid pid g` is the one guess against a
  completed session that has spent no guess, and returns the key of the session when `g` is its
  password and a fresh sample otherwise; `idle` changes nothing.

`F_aPAKE keySample` is the asymmetric functionality of Gentry, MacKenzie and Ramzan (CRYPTO
2006) in the form of Jarecki, Krawczyk and Xu (Eurocrypt 2018).
* Honest port: `storePwdFile srv cli pw` stores the password file of the server `srv` for the
  client `cli`; `usrSession sid cli srv pw` starts a client session with the password `pw`;
  `svrSession sid srv cli` starts a server session with the password of the file;
  `getKey sid pid` as above.
* Adversary port: `poll`, `testPwd`, `newKey` and `idle` as above; `stealPwdFile srv cli`
  marks the file stolen and answers whether it exists; `offlineTestPwd srv cli g` answers,
  for a stolen file, whether `g` is its password; `impersonate sid cli` answers, for a fresh
  client session whose server file is stolen, whether the client password is the password of the
  file, and marks the session compromised or interrupted. The guesses that the formulation of
  Jarecki, Krawczyk and Xu queues before the file is stolen are not kept: the adversary asks
  them again after `stealPwdFile`.

**What the adversary port shows.** Passwords and keys never appear on the adversary port
except through the test answers: the `Option Bool` answers of `testPwd`, `offlineTestPwd`
and `impersonate` (`some (pw = g)`, or `none` when the test does not apply), and the value
returned by `lateTestPwd`, which is the session key exactly when the guess is the password
(`lateReveal_eq_some`). With `answerView`, the view that relates any two answers and is the
equality on every other adversary output, both functionalities are opaque for the password-blind
honest views: `F_lePAKE_opaque`, `F_aPAKE_opaque`. Two runs whose honest events have the
same public parts (identifiers and roles, the passwords arbitrary) and whose adversary events are
equal give the adversary equal outputs at every step except the answers. Opacity with the
answers compared by equality does not hold for a password-blind view: a test answer depends on
the password.

**Correctness.** Two honest sessions that are partners and have the same password receive
the same key when the adversary delivers keys without testing a password (`F_lePAKE_correct`,
`F_aPAKE_correct`).

## Main definitions

* `FPAKE.St`: the shared state (session records, password files, notices, cursor).
* `F_lePAKE`, `F_aPAKE`: the two functionalities.
* `lePAKEHonView`, `aPAKEHonView`: the password-blind views of the honest ports.
* `answerView`: the view of the adversary port that relates any two test answers.

## Main results

* `F_lePAKE_portTyped`, `F_aPAKE_portTyped`, `F_lePAKE_idleAt`, `F_aPAKE_idleAt`.
* `F_lePAKE_opaque`, `F_aPAKE_opaque`.
* `testAns_eq_some`, `lateReveal_eq_some`: the content of the test answers.
* `F_lePAKE_correct`, `F_aPAKE_correct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational

namespace FPAKE

/-! ## Identifiers, records and the state -/

/-- Party identifier. -/
abbrev PartyId := ℕ

/-- Protocol session identifier, shared by the two partners of a session. -/
abbrev SessionId := ℕ

/-- A session: the protocol session identifier and the party. -/
abbrev Inst := SessionId × PartyId

/-- Role of a party in a session. -/
inductive Role where
  /-- The client. -/
  | client
  /-- The server. -/
  | server
  deriving DecidableEq

/-- Status of a session. -/
inductive Status where
  /-- No guess against the session and no key. -/
  | fresh
  /-- A correct guess against the session. -/
  | compromised
  /-- A wrong guess against the session. -/
  | interrupted
  /-- The session received a key while fresh. -/
  | completed
  deriving DecidableEq

/-- The public part of a new session: what the adversary learns of it. -/
structure Notice where
  /-- The protocol session. -/
  sid : SessionId
  /-- The party. -/
  pid : PartyId
  /-- The intended partner. -/
  peer : PartyId
  /-- The role of the party. -/
  role : Role

/-- The record of a session. -/
structure Rec (Pw K : Type) where
  /-- The intended partner. -/
  peer : PartyId
  /-- The role of the party. -/
  role : Role
  /-- The password of the session. -/
  pw : Pw
  /-- The status. -/
  status : Status
  /-- The key delivered to the session, if any. -/
  key : Option K
  /-- The outcome of the one guess against the session, if spent. -/
  tested : Option Bool

/-- A password file of the asymmetric functionality. -/
structure FileRec (Pw : Type) where
  /-- The password. -/
  pw : Pw
  /-- Whether the adversary stole the file. -/
  stolen : Bool

/-- The state of both functionalities. -/
structure St (Pw K : Type) where
  /-- The session records. -/
  recs : Inst → Option (Rec Pw K)
  /-- The password files, by server and client. -/
  files : PartyId × PartyId → Option (FileRec Pw)
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
inductive AOut (K : Type) where
  /-- Acknowledgement. -/
  | ack
  /-- The next notice not yet shown, if any. -/
  | notice (o : Option Notice)
  /-- The answer of a password test, `none` when the test does not apply. -/
  | answer (o : Option Bool)
  /-- The value returned by a late password test, `none` when the test does not apply. -/
  | reveal (o : Option K)
  /-- Whether the password file to be stolen exists. -/
  | stolen (b : Bool)

variable {Pw K : Type}

/-- The initial state: no session, no file, no notice. -/
def initSt : St Pw K := ⟨fun _ => none, fun _ => none, [], 0⟩

/-- The state with the record `r` at `x`. -/
def setRec (t : St Pw K) (x : Inst) (r : Rec Pw K) : St Pw K :=
  { t with recs := Function.update t.recs x (some r) }

/-- A new fresh session at `x` with its notice, when `x` has no record. -/
def addSession (t : St Pw K) (x : Inst) (peer : PartyId) (role : Role) (pw : Pw) : St Pw K :=
  if (t.recs x).isSome then t else
    { t with recs := Function.update t.recs x (some ⟨peer, role, pw, .fresh, none, none⟩),
             notices := t.notices ++ [⟨x.1, x.2, peer, role⟩] }

/-- The key of the session `x`, if delivered. -/
def keyOf (t : St Pw K) (x : Inst) : Option K := (t.recs x).bind Rec.key

/-- The step of `poll`: the next notice not yet shown, and the advanced cursor. -/
def pollStep (t : St Pw K) : St Pw K × Option Notice :=
  match t.notices[t.cursor]? with
  | some n => ({ t with cursor := t.cursor + 1 }, some n)
  | none => (t, none)

/-- Whether the online guess against `x` applies: the session is fresh and spent no guess. -/
def Testable (r : Rec Pw K) : Prop := r.status = .fresh ∧ r.tested = none

instance (r : Rec Pw K) : Decidable (Testable r) := inferInstanceAs (Decidable (_ ∧ _))

/-- The answer of the online guess `g` against `x`. -/
def testAns [DecidableEq Pw] (t : St Pw K) (x : Inst) (g : Pw) : Option Bool :=
  match t.recs x with
  | some r => if Testable r then some (decide (r.pw = g)) else none
  | none => none

/-- The record after a guess with outcome `b`: compromised on a correct guess, interrupted on a
wrong one. -/
def guessed (r : Rec Pw K) (b : Bool) : Rec Pw K :=
  { r with status := bif b then .compromised else .interrupted, tested := some b }

/-- The state after the online guess `g` against `x`. -/
def testStep [DecidableEq Pw] (t : St Pw K) (x : Inst) (g : Pw) : St Pw K :=
  match t.recs x with
  | some r => if Testable r then setRec t x (guessed r (decide (r.pw = g))) else t
  | none => t

/-- The key that `newKey` gives to the session `x` with record `r`, for the adversary key `k`
and the fresh sample `kf`. -/
def newKeyVal [DecidableEq Pw] (t : St Pw K) (x : Inst) (r : Rec Pw K) (k kf : K) : K :=
  match r.status with
  | .compromised => k
  | .fresh =>
    match t.recs (x.1, r.peer) with
    | some p => if p.peer = x.2 ∧ p.status = .completed ∧ p.pw = r.pw then p.key.getD kf else kf
    | none => kf
  | _ => kf

/-- The state after `newKey` at `x` with the adversary key `k` and the fresh sample `kf`. -/
def newKeyStep [DecidableEq Pw] (t : St Pw K) (x : Inst) (k kf : K) : St Pw K :=
  match t.recs x with
  | some r =>
    if r.key = none then
      setRec t x { r with key := some (newKeyVal t x r k kf),
                          status := if r.status = .fresh then .completed else r.status }
    else t
  | none => t

/-- Whether the late guess against a session applies: it completed while fresh and spent no
guess. -/
def LateTestable (r : Rec Pw K) : Prop := r.status = .completed ∧ r.tested = none

instance (r : Rec Pw K) : Decidable (LateTestable r) := inferInstanceAs (Decidable (_ ∧ _))

/-- The value returned by the late guess `g` against `x` with the fresh sample `kf`: the key of
the session when `g` is its password, `kf` otherwise. -/
def lateReveal [DecidableEq Pw] (t : St Pw K) (x : Inst) (g : Pw) (kf : K) : Option K :=
  match t.recs x with
  | some r => if LateTestable r then some (if r.pw = g then r.key.getD kf else kf) else none
  | none => none

/-- The state after the late guess `g` against `x`: the guess is spent. -/
def lateStep [DecidableEq Pw] (t : St Pw K) (x : Inst) (g : Pw) : St Pw K :=
  match t.recs x with
  | some r => if LateTestable r then setRec t x { r with tested := some (decide (r.pw = g)) }
    else t
  | none => t

/-! ## The relation of states with equal public parts -/

/-- Two states with the same notices, the same cursor and the same sessions and files. -/
def PubRel (t t' : St Pw K) : Prop :=
  t.notices = t'.notices ∧ t.cursor = t'.cursor ∧
    (∀ x, (t.recs x).isSome = (t'.recs x).isSome) ∧
    ∀ y, (t.files y).isSome = (t'.files y).isSome

/-- `PubRel` is reflexive. -/
theorem PubRel.refl (t : St Pw K) : PubRel t t :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- `PubRel` is symmetric. -/
theorem PubRel.symm {t t' : St Pw K} (h : PubRel t t') : PubRel t' t :=
  ⟨h.1.symm, h.2.1.symm, fun x => (h.2.2.1 x).symm, fun y => (h.2.2.2 y).symm⟩

/-- `PubRel` is transitive. -/
theorem PubRel.trans {t t' t'' : St Pw K} (h : PubRel t t') (h' : PubRel t' t'') :
    PubRel t t'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, fun x => (h.2.2.1 x).trans (h'.2.2.1 x),
    fun y => (h.2.2.2 y).trans (h'.2.2.2 y)⟩

/-- Two states each related to one of two related states are related. -/
theorem PubRel.of_left_right {t t' u u' : St Pw K} (hu : PubRel u t) (h : PubRel t t')
    (hu' : PubRel u' t') : PubRel u u' :=
  (hu.trans h).trans hu'.symm

/-- Replacing an existing record keeps the public part. -/
theorem pubRel_setRec {t : St Pw K} {x : Inst} (h : (t.recs x).isSome) (r : Rec Pw K) :
    PubRel (setRec t x r) t := by
  refine ⟨rfl, rfl, fun y => ?_, fun _ => rfl⟩
  by_cases hy : y = x
  · subst hy
    simp [setRec, h]
  · simp [setRec, Function.update_of_ne hy]

/-- The online guess keeps the public part. -/
theorem pubRel_testStep [DecidableEq Pw] (t : St Pw K) (x : Inst) (g : Pw) :
    PubRel (testStep t x g) t := by
  grind [testStep, pubRel_setRec, PubRel.refl]

/-- `newKey` keeps the public part. -/
theorem pubRel_newKeyStep [DecidableEq Pw] (t : St Pw K) (x : Inst) (k kf : K) :
    PubRel (newKeyStep t x k kf) t := by
  grind [newKeyStep, pubRel_setRec, PubRel.refl]

/-- The late guess keeps the public part. -/
theorem pubRel_lateStep [DecidableEq Pw] (t : St Pw K) (x : Inst) (g : Pw) :
    PubRel (lateStep t x g) t := by
  grind [lateStep, pubRel_setRec, PubRel.refl]

/-- New sessions with the same public part keep `PubRel`, whatever their passwords. -/
theorem PubRel.addSession {t t' : St Pw K} (h : PubRel t t') (x : Inst) (peer : PartyId)
    (role : Role) (pw pw' : Pw) :
    PubRel (addSession t x peer role pw) (addSession t' x peer role pw') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold FPAKE.addSession
  rw [← h3 x]
  split
  · exact ⟨h1, h2, h3, h4⟩
  · refine ⟨by rw [h1], h2, fun y => ?_, h4⟩
    by_cases hy : y = x
    · subst hy
      simp
    · simp [Function.update_of_ne hy, h3 y]

/-- `poll` from related states: related states and the same notice. -/
theorem PubRel.pollStep {t t' : St Pw K} (h : PubRel t t') :
    PubRel (FPAKE.pollStep t).1 (FPAKE.pollStep t').1 ∧
      (FPAKE.pollStep t).2 = (FPAKE.pollStep t').2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold FPAKE.pollStep
  rw [← h1, ← h2]
  split
  · exact ⟨⟨rfl, rfl, h3, h4⟩, rfl⟩
  · exact ⟨⟨h1, h2, h3, h4⟩, rfl⟩

/-! ## Password files -/

/-- The state after `storePwdFile` at `y` with the password `pw`, when `y` has no file. -/
def storeFile (t : St Pw K) (y : PartyId × PartyId) (pw : Pw) : St Pw K :=
  if (t.files y).isSome then t else
    { t with files := Function.update t.files y (some ⟨pw, false⟩) }

/-- The state after `svrSession sid srv cli`: a server session with the password of the file
of `srv` for `cli`, when the file exists. -/
def svrSession (t : St Pw K) (sid : SessionId) (srv cli : PartyId) : St Pw K :=
  match t.files (srv, cli) with
  | some f => addSession t (sid, srv) cli .server f.pw
  | none => t

/-- The state after `stealPwdFile` at `y`: the file, if any, is marked stolen. -/
def stealStep (t : St Pw K) (y : PartyId × PartyId) : St Pw K :=
  match t.files y with
  | some f => { t with files := Function.update t.files y (some { f with stolen := true }) }
  | none => t

/-- The answer of the offline guess `g` against the file at `y`: whether `g` is its password,
when the file is stolen. -/
def offlineAns [DecidableEq Pw] (t : St Pw K) (y : PartyId × PartyId) (g : Pw) :
    Option Bool :=
  match t.files y with
  | some f => if f.stolen then some (decide (f.pw = g)) else none
  | none => none

/-- Whether `impersonate` applies to the session `r` with the file `f`: a fresh client session
that spent no guess, whose server file is stolen. -/
def Impersonable (r : Rec Pw K) (f : FileRec Pw) : Prop :=
  r.role = .client ∧ Testable r ∧ f.stolen = true

instance (r : Rec Pw K) (f : FileRec Pw) : Decidable (Impersonable r f) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The answer of `impersonate` against the client session `x`: whether the client password is
the password of the stolen server file. -/
def impAns [DecidableEq Pw] (t : St Pw K) (x : Inst) : Option Bool :=
  match t.recs x with
  | some r =>
    match t.files (r.peer, x.2) with
    | some f => if Impersonable r f then some (decide (r.pw = f.pw)) else none
    | none => none
  | none => none

/-- The state after `impersonate` against the client session `x`. -/
def impStep [DecidableEq Pw] (t : St Pw K) (x : Inst) : St Pw K :=
  match t.recs x with
  | some r =>
    match t.files (r.peer, x.2) with
    | some f => if Impersonable r f then setRec t x (guessed r (decide (r.pw = f.pw))) else t
    | none => t
  | none => t

/-- Storing files with the same public part keeps `PubRel`, whatever their passwords. -/
theorem PubRel.storeFile {t t' : St Pw K} (h : PubRel t t') (y : PartyId × PartyId)
    (pw pw' : Pw) : PubRel (storeFile t y pw) (storeFile t' y pw') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold FPAKE.storeFile
  rw [← h4 y]
  split
  · exact ⟨h1, h2, h3, h4⟩
  · refine ⟨h1, h2, h3, fun z => ?_⟩
    by_cases hz : z = y
    · subst hz
      simp
    · simp [Function.update_of_ne hz, h4 z]

/-- Server sessions with the same public part keep `PubRel`. -/
theorem PubRel.svrSession {t t' : St Pw K} (h : PubRel t t') (sid : SessionId)
    (srv cli : PartyId) : PubRel (svrSession t sid srv cli) (svrSession t' sid srv cli) := by
  have hf := h.2.2.2 (srv, cli)
  unfold FPAKE.svrSession
  cases hs : t.files (srv, cli) <;> cases hs' : t'.files (srv, cli) <;>
    simp only [hs, hs', Option.isSome_none, Option.isSome_some] at hf ⊢
  · exact h
  · exact absurd hf (by decide)
  · exact absurd hf (by decide)
  · exact h.addSession _ _ _ _ _

/-- `stealPwdFile` keeps the public part. -/
theorem pubRel_stealStep (t : St Pw K) (y : PartyId × PartyId) : PubRel (stealStep t y) t := by
  unfold stealStep
  split
  · next f hf =>
    refine ⟨rfl, rfl, fun _ => rfl, fun z => ?_⟩
    by_cases hz : z = y
    · subst hz
      simp [hf]
    · simp [Function.update_of_ne hz]
  · exact PubRel.refl t

/-- `impersonate` keeps the public part. -/
theorem pubRel_impStep [DecidableEq Pw] (t : St Pw K) (x : Inst) : PubRel (impStep t x) t := by
  grind [impStep, pubRel_setRec, PubRel.refl]

/-! ## What the test answers carry -/

/-- An online-guess answer `some b` says whether the guess is the password of a fresh session
that spent no guess. -/
theorem testAns_eq_some [DecidableEq Pw] {t : St Pw K} {x : Inst} {g : Pw} {b : Bool}
    (h : testAns t x g = some b) :
    ∃ r, t.recs x = some r ∧ Testable r ∧ b = decide (r.pw = g) := by
  grind [testAns]

/-- A late-guess value `some k` is the key of a completed session that spent no guess when the
guess is its password, and the fresh sample otherwise. -/
theorem lateReveal_eq_some [DecidableEq Pw] {t : St Pw K} {x : Inst} {g : Pw} {kf k : K}
    (h : lateReveal t x g kf = some k) :
    ∃ r, t.recs x = some r ∧ LateTestable r ∧ (r.pw = g → k = r.key.getD kf) ∧
      (r.pw ≠ g → k = kf) := by
  grind [lateReveal]

/-- An offline-guess answer `some b` says whether the guess is the password of a stolen file. -/
theorem offlineAns_eq_some [DecidableEq Pw] {t : St Pw K} {y : PartyId × PartyId} {g : Pw}
    {b : Bool} (h : offlineAns t y g = some b) :
    ∃ f, t.files y = some f ∧ f.stolen = true ∧ b = decide (f.pw = g) := by
  grind [offlineAns]

/-- An `impersonate` answer `some b` says whether the password of a fresh client session is the
password of its stolen server file. -/
theorem impAns_eq_some [DecidableEq Pw] {t : St Pw K} {x : Inst} {b : Bool}
    (h : impAns t x = some b) :
    ∃ r f, t.recs x = some r ∧ t.files (r.peer, x.2) = some f ∧ Impersonable r f ∧
      b = decide (r.pw = f.pw) := by
  grind [impAns]

/-! ## Events -/

/-- Events of the honest port of `F_lePAKE`. -/
inductive LeHEv (Pw : Type) where
  /-- The party `pid` starts the session `sid` with `peer` in the role `role`, password `pw`. -/
  | newSession (sid : SessionId) (pid peer : PartyId) (role : Role) (pw : Pw)
  /-- The party `pid` asks for the key of the session `sid`. -/
  | getKey (sid : SessionId) (pid : PartyId)

/-- Events of the adversary port of `F_lePAKE`. -/
inductive LeAEv (Pw K : Type) where
  /-- No action. -/
  | idle
  /-- Read the next notice not yet shown. -/
  | poll
  /-- The online guess `g` against the session of `pid` in `sid`. -/
  | testPwd (sid : SessionId) (pid : PartyId) (g : Pw)
  /-- Deliver a key to the session of `pid` in `sid`; `k` is used if the session is
  compromised. -/
  | newKey (sid : SessionId) (pid : PartyId) (k : K)
  /-- The late guess `g` against the completed session of `pid` in `sid`. -/
  | lateTestPwd (sid : SessionId) (pid : PartyId) (g : Pw)

/-- Events of the honest port of `F_aPAKE`. -/
inductive AHEv (Pw : Type) where
  /-- The server `srv` stores the password file for the client `cli`. -/
  | storePwdFile (srv cli : PartyId) (pw : Pw)
  /-- The client `cli` starts the session `sid` with the server `srv`, password `pw`. -/
  | usrSession (sid : SessionId) (cli srv : PartyId) (pw : Pw)
  /-- The server `srv` starts the session `sid` with the client `cli`. -/
  | svrSession (sid : SessionId) (srv cli : PartyId)
  /-- The party `pid` asks for the key of the session `sid`. -/
  | getKey (sid : SessionId) (pid : PartyId)

/-- Events of the adversary port of `F_aPAKE`. -/
inductive AAEv (Pw K : Type) where
  /-- No action. -/
  | idle
  /-- Read the next notice not yet shown. -/
  | poll
  /-- Steal the password file of `srv` for `cli`. -/
  | stealPwdFile (srv cli : PartyId)
  /-- The offline guess `g` against the password file of `srv` for `cli`. -/
  | offlineTestPwd (srv cli : PartyId) (g : Pw)
  /-- Impersonate the server to the client session of `cli` in `sid`. -/
  | impersonate (sid : SessionId) (cli : PartyId)
  /-- The online guess `g` against the session of `pid` in `sid`. -/
  | testPwd (sid : SessionId) (pid : PartyId) (g : Pw)
  /-- Deliver a key to the session of `pid` in `sid`; `k` is used if the session is
  compromised. -/
  | newKey (sid : SessionId) (pid : PartyId) (k : K)

/-! ## The ports as systems -/

/-- A step of the honest port of `F_lePAKE`. -/
def leHonStep (t : St Pw K) : LeHEv Pw → St Pw K × HOut K
  | .newSession sid pid peer role pw => (addSession t (sid, pid) peer role pw, .ok)
  | .getKey sid pid => (t, .key (keyOf t (sid, pid)))

/-- A step of the honest port of `F_aPAKE`. -/
def aHonStep (t : St Pw K) : AHEv Pw → St Pw K × HOut K
  | .storePwdFile srv cli pw => (storeFile t (srv, cli) pw, .ok)
  | .usrSession sid cli srv pw => (addSession t (sid, cli) srv .client pw, .ok)
  | .svrSession sid srv cli => (svrSession t sid srv cli, .ok)
  | .getKey sid pid => (t, .key (keyOf t (sid, pid)))

/-- The honest port of `F_lePAKE` as a system. -/
noncomputable def leHonSys : Sys (St Pw K) (LeHEv Pw) (HOut K) where
  init := initSt
  step t e := SPComp.pure (leHonStep t e)

/-- The honest port of `F_aPAKE` as a system. -/
noncomputable def aHonSys : Sys (St Pw K) (AHEv Pw) (HOut K) where
  init := initSt
  step t e := SPComp.pure (aHonStep t e)

/-- The adversary port of `F_lePAKE` as a system; `newKey` and `lateTestPwd` draw a fresh
sample of `keySample`. -/
noncomputable def leAdvSys [DecidableEq Pw] (keySample : SPComp K) :
    Sys (St Pw K) (LeAEv Pw K) (AOut K) where
  init := initSt
  step t e := match e with
    | .idle => SPComp.pure (t, .ack)
    | .poll => SPComp.pure ((pollStep t).1, .notice (pollStep t).2)
    | .testPwd sid pid g =>
      SPComp.pure (testStep t (sid, pid) g, .answer (testAns t (sid, pid) g))
    | .newKey sid pid k =>
      SPComp.map (fun kf => (newKeyStep t (sid, pid) k kf, .ack)) keySample
    | .lateTestPwd sid pid g =>
      SPComp.map (fun kf => (lateStep t (sid, pid) g, .reveal (lateReveal t (sid, pid) g kf)))
        keySample

/-- The adversary port of `F_aPAKE` as a system; `newKey` draws a fresh sample of
`keySample`. -/
noncomputable def aAdvSys [DecidableEq Pw] (keySample : SPComp K) :
    Sys (St Pw K) (AAEv Pw K) (AOut K) where
  init := initSt
  step t e := match e with
    | .idle => SPComp.pure (t, .ack)
    | .poll => SPComp.pure ((pollStep t).1, .notice (pollStep t).2)
    | .stealPwdFile srv cli =>
      SPComp.pure (stealStep t (srv, cli), .stolen (t.files (srv, cli)).isSome)
    | .offlineTestPwd srv cli g => SPComp.pure (t, .answer (offlineAns t (srv, cli) g))
    | .impersonate sid cli => SPComp.pure (impStep t (sid, cli), .answer (impAns t (sid, cli)))
    | .testPwd sid pid g =>
      SPComp.pure (testStep t (sid, pid) g, .answer (testAns t (sid, pid) g))
    | .newKey sid pid k =>
      SPComp.map (fun kf => (newKeyStep t (sid, pid) k kf, .ack)) keySample

end FPAKE

open FPAKE

/-! ## Views -/

/-- The password-blind view of the honest port of `F_lePAKE`: two new sessions with the same
identifiers and role are related, whatever their passwords; honest outputs carry no public
part. -/
def lePAKEHonView {Pw K : Type} : PubView (LeHEv Pw) (HOut K) where
  ev
    | .newSession s p q r _, .newSession s' p' q' r' _ => s = s' ∧ p = p' ∧ q = q' ∧ r = r'
    | .getKey s p, .getKey s' p' => s = s' ∧ p = p'
    | _, _ => False
  out _ _ := True

/-- The password-blind view of the honest port of `F_aPAKE`: events with the same identifiers
are related, whatever their passwords; honest outputs carry no public part. -/
def aPAKEHonView {Pw K : Type} : PubView (AHEv Pw) (HOut K) where
  ev
    | .storePwdFile s c _, .storePwdFile s' c' _ => s = s' ∧ c = c'
    | .usrSession i c s _, .usrSession i' c' s' _ => i = i' ∧ c = c' ∧ s = s'
    | .svrSession i s c, .svrSession i' s' c' => i = i' ∧ s = s' ∧ c = c'
    | .getKey s p, .getKey s' p' => s = s' ∧ p = p'
    | _, _ => False
  out _ _ := True

/-- The view of the adversary port that relates equal events, any two test answers and any two
late-guess values, and is the equality on the other outputs. -/
def answerView {E K : Type} : PubView E (AOut K) where
  ev := Eq
  out
    | .ack, .ack => True
    | .notice o, .notice o' => o = o'
    | .answer _, .answer _ => True
    | .reveal _, .reveal _ => True
    | .stolen b, .stolen b' => b = b'
    | _, _ => False

/-! ## The functionalities -/

/-- **The ideal lePAKE functionality** with the key distribution `keySample`: the honest port
on the left, the adversary port on the right, one shared state. -/
noncomputable def F_lePAKE {Pw K : Type} [DecidableEq Pw] (keySample : SPComp K) :
    Sys (St Pw K) (LeHEv Pw ⊕ LeAEv Pw K) (HOut K ⊕ AOut K) :=
  Sys.ofPorts leHonSys (leAdvSys keySample)

/-- **The ideal aPAKE functionality** with the key distribution `keySample`: the honest port
on the left, the adversary port on the right, one shared state. -/
noncomputable def F_aPAKE {Pw K : Type} [DecidableEq Pw] (keySample : SPComp K) :
    Sys (St Pw K) (AHEv Pw ⊕ AAEv Pw K) (HOut K ⊕ AOut K) :=
  Sys.ofPorts aHonSys (aAdvSys keySample)

/-! ## Unwinding of the ports -/

namespace FPAKE

variable {Pw K : Type}

/-- The unwinding condition of the honest port of `F_lePAKE` for its password-blind view. -/
theorem leHonSys_unwinding :
    (leHonSys : Sys (St Pw K) (LeHEv Pw) (HOut K)).Unwinding lePAKEHonView PubRel := by
  refine ⟨PubRel.refl _, fun t t' e e' ht he => ?_⟩
  cases e <;> cases e' <;> simp only [lePAKEHonView] at he
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    exact rHoare_ret fun _ _ h => ⟨h, ht.addSession _ _ _ _ _, trivial⟩
  · obtain ⟨rfl, rfl⟩ := he
    exact rHoare_ret fun _ _ h => ⟨h, ht, trivial⟩

/-- The unwinding condition of the honest port of `F_aPAKE` for its password-blind view. -/
theorem aHonSys_unwinding :
    (aHonSys : Sys (St Pw K) (AHEv Pw) (HOut K)).Unwinding aPAKEHonView PubRel := by
  refine ⟨PubRel.refl _, fun t t' e e' ht he => ?_⟩
  cases e <;> cases e' <;> simp only [aPAKEHonView] at he
  · obtain ⟨rfl, rfl⟩ := he
    exact rHoare_ret fun _ _ h => ⟨h, ht.storeFile _ _ _, trivial⟩
  · obtain ⟨rfl, rfl, rfl⟩ := he
    exact rHoare_ret fun _ _ h => ⟨h, ht.addSession _ _ _ _ _, trivial⟩
  · obtain ⟨rfl, rfl, rfl⟩ := he
    exact rHoare_ret fun _ _ h => ⟨h, ht.svrSession _ _ _, trivial⟩
  · obtain ⟨rfl, rfl⟩ := he
    exact rHoare_ret fun _ _ h => ⟨h, ht, trivial⟩

/-- The unwinding condition of the adversary port of `F_lePAKE` for `answerView`. -/
theorem leAdvSys_unwinding [DecidableEq Pw] (keySample : SPComp K) :
    (leAdvSys (Pw := Pw) keySample).Unwinding answerView PubRel := by
  refine ⟨PubRel.refl _, fun t t' e e' ht he => ?_⟩
  cases he
  cases e with
  | idle => exact rHoare_ret fun _ _ h => ⟨h, ht, trivial⟩
  | poll => exact rHoare_ret fun _ _ h => ⟨h, ht.pollStep.1, ht.pollStep.2⟩
  | testPwd sid pid g =>
    exact rHoare_ret fun _ _ h =>
      ⟨h, (pubRel_testStep _ _ _).of_left_right ht (pubRel_testStep _ _ _), trivial⟩
  | newKey sid pid k =>
    simp only [leAdvSys]
    refine rHoare_bind (rHoare_refl keySample) fun _ _ => rHoare_ret fun _ _ hp => ?_
    exact ⟨hp.2, (pubRel_newKeyStep _ _ _ _).of_left_right ht (pubRel_newKeyStep _ _ _ _),
      trivial⟩
  | lateTestPwd sid pid g =>
    simp only [leAdvSys]
    refine rHoare_bind (rHoare_refl keySample) fun _ _ => rHoare_ret fun _ _ hp => ?_
    exact ⟨hp.2, (pubRel_lateStep _ _ _).of_left_right ht (pubRel_lateStep _ _ _), trivial⟩

/-- The unwinding condition of the adversary port of `F_aPAKE` for `answerView`. -/
theorem aAdvSys_unwinding [DecidableEq Pw] (keySample : SPComp K) :
    (aAdvSys (Pw := Pw) keySample).Unwinding answerView PubRel := by
  refine ⟨PubRel.refl _, fun t t' e e' ht he => ?_⟩
  cases he
  cases e with
  | idle => exact rHoare_ret fun _ _ h => ⟨h, ht, trivial⟩
  | poll => exact rHoare_ret fun _ _ h => ⟨h, ht.pollStep.1, ht.pollStep.2⟩
  | stealPwdFile srv cli =>
    exact rHoare_ret fun _ _ h =>
      ⟨h, (pubRel_stealStep _ _).of_left_right ht (pubRel_stealStep _ _), ht.2.2.2 _⟩
  | offlineTestPwd srv cli g => exact rHoare_ret fun _ _ h => ⟨h, ht, trivial⟩
  | impersonate sid cli =>
    exact rHoare_ret fun _ _ h =>
      ⟨h, (pubRel_impStep _ _).of_left_right ht (pubRel_impStep _ _), trivial⟩
  | testPwd sid pid g =>
    exact rHoare_ret fun _ _ h =>
      ⟨h, (pubRel_testStep _ _ _).of_left_right ht (pubRel_testStep _ _ _), trivial⟩
  | newKey sid pid k =>
    simp only [aAdvSys]
    refine rHoare_bind (rHoare_refl keySample) fun _ _ => rHoare_ret fun _ _ hp => ?_
    exact ⟨hp.2, (pubRel_newKeyStep _ _ _ _).of_left_right ht (pubRel_newKeyStep _ _ _ _),
      trivial⟩

end FPAKE

/-! ## Ports, idling and opacity -/

section Functionalities

variable {Pw K : Type} [DecidableEq Pw]

/-- `F_lePAKE` answers every event on the port of the event. -/
theorem F_lePAKE_portTyped (keySample : SPComp K) :
    (F_lePAKE (Pw := Pw) keySample).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `F_aPAKE` answers every event on the port of the event. -/
theorem F_aPAKE_portTyped (keySample : SPComp K) :
    (F_aPAKE (Pw := Pw) keySample).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `F_lePAKE` is idle at the adversary event `idle`. -/
theorem F_lePAKE_idleAt (keySample : SPComp K) :
    MultiHybrid.IdleAt (F_lePAKE (Pw := Pw) keySample) (.inr .idle) (.inr .ack) := fun t => by
  simp [F_lePAKE, FPAKE.leAdvSys]

/-- `F_aPAKE` is idle at the adversary event `idle`. -/
theorem F_aPAKE_idleAt (keySample : SPComp K) :
    MultiHybrid.IdleAt (F_aPAKE (Pw := Pw) keySample) (.inr .idle) (.inr .ack) := fun t => by
  simp [F_aPAKE, FPAKE.aAdvSys]

/-- **Opacity of `F_lePAKE`**: two runs whose honest events have the same identifiers and roles,
whatever the passwords, and whose adversary events are equal give the adversary equal outputs
except the test answers and the late-guess values. -/
theorem F_lePAKE_opaque (keySample : SPComp K) :
    (F_lePAKE (Pw := Pw) keySample).Opaque (lePAKEHonView.sum answerView) :=
  Sys.Opaque.ofPorts FPAKE.leHonSys_unwinding (FPAKE.leAdvSys_unwinding keySample)

/-- **Opacity of `F_aPAKE`**: two runs whose honest events have the same identifiers, whatever
the passwords, and whose adversary events are equal give the adversary equal outputs except the
test answers. -/
theorem F_aPAKE_opaque (keySample : SPComp K) :
    (F_aPAKE (Pw := Pw) keySample).Opaque (aPAKEHonView.sum answerView) :=
  Sys.Opaque.ofPorts FPAKE.aHonSys_unwinding (FPAKE.aAdvSys_unwinding keySample)

/-! ## Correctness -/

/-- **Correctness of `F_lePAKE`**: two new partner sessions of `a` and `b` in `sid` with the
same password, followed by `newKey` at both without a password test, give both the key
sampled at the first `newKey`, whatever keys the adversary proposes. -/
theorem F_lePAKE_correct (t : St Pw K) (sid : SessionId) (a b : PartyId) (ra rb : Role)
    (pw : Pw) (k₁ k₂ kf₁ kf₂ : K) (hab : a ≠ b) (ha : t.recs (sid, a) = none)
    (hb : t.recs (sid, b) = none) :
    let t₂ := (leHonStep (leHonStep t (.newSession sid a b ra pw)).1
      (.newSession sid b a rb pw)).1
    let t₄ := newKeyStep (newKeyStep t₂ (sid, a) k₁ kf₁) (sid, b) k₂ kf₂
    keyOf t₄ (sid, a) = some kf₁ ∧ keyOf t₄ (sid, b) = some kf₁ := by
  simp [leHonStep, addSession, ha, hb, newKeyStep, newKeyVal, setRec, keyOf, hab, Ne.symm hab]

/-- **Correctness of `F_aPAKE`**: a stored file of `srv` for `cli`, a client session of `cli`
with the password of the file and a server session of `srv` in `sid`, followed by `newKey` at
both without a password test, give both the key sampled at the first `newKey`. -/
theorem F_aPAKE_correct (t : St Pw K) (sid : SessionId) (cli srv : PartyId) (pw : Pw)
    (k₁ k₂ kf₁ kf₂ : K) (hcs : cli ≠ srv) (hf : t.files (srv, cli) = none)
    (hc : t.recs (sid, cli) = none) (hs : t.recs (sid, srv) = none) :
    let t₃ := (aHonStep (aHonStep (aHonStep t (.storePwdFile srv cli pw)).1
      (.usrSession sid cli srv pw)).1 (.svrSession sid srv cli)).1
    let t₅ := newKeyStep (newKeyStep t₃ (sid, cli) k₁ kf₁) (sid, srv) k₂ kf₂
    keyOf t₅ (sid, cli) = some kf₁ ∧ keyOf t₅ (sid, srv) = some kf₁ := by
  simp [aHonStep, storeFile, FPAKE.svrSession, addSession, hf, hc, hs, newKeyStep, newKeyVal,
    setRec, keyOf, hcs, Ne.symm hcs]

end Functionalities

end CatCrypt.Crypto.UCTransparent

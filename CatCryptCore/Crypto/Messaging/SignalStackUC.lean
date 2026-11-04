/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStack
public import CatCryptCore.Crypto.UCDeferred
public import CatCryptCore.Crypto.UCRoundHybrid

/-!
# The Signal stack realizes an ideal secure channel

The Signal stack runs X3DH and keys the double ratchet with the session key of X3DH
(`SignalStack`). This module proves that the stack realizes an ideal secure-channel
functionality behind a simulator, in the sense of Canetti and Krawczyk (Eurocrypt 2002, `F_SC`
from `F_KE`). The secure-messaging step uses that `F_AKE` delivers to a completed, unexposed
session a key that it samples and that no event reveals, and the adversary key to an exposed
session; the bound has no real-or-random term of the key.

**The ideal functionality.** `F_SC realV idealV` has the state and the adversary port of
`F_AKE (SPComp.sample K) true` (notices, adaptive corruption, `newKey`, `newKeyUnlinked`), except
that a session that completes without exposure stores the placeholder key `default`. Its honest
port opens sessions and answers `getKey` with the secure-messaging view of the session: the
ideal view `idealV` (for the ratchet, `sm_ideal C msgs`: the public CKA transcript and uniform
ciphertexts) for a completed session, the real view `realV k` (for the ratchet,
`smRealAt C R Gp D msgs k`) under the adversary key `k` for an exposed session, and nothing for a
session without a key.

**The real world.** `(x3dhReal G).seq (smLayer (smRealAt C R Gp D msgs))`: the real X3DH
protocol, and the ratchet keyed by the session key of every `getKey` answer.

**The simulator.** `scSim G` is the X3DH simulator `simProt G` running over `F_SC` (`simSC G`):
it keeps a copy of the real state, draws the long-term and session secrets, forwards the honest
events, answers `poll`, `pub`, `ephPub` and `kdf` on its copy, refuses or forwards `corrupt`
under the static rule of X3DH, and on `complete` and `send` passes the key-derivation value to
`newKey` for an exposed session and a placeholder key to `newKey` or `newKeyUnlinked` otherwise.
The honest answers of `F_SC` pass unchanged; the simulator never reads them (`simSC_opaque`).

**The proof.** The cascade theorem of the X3DH square (`SignalStack.signal_stack_realizes`)
replaces `x3dhReal G` by `F_AKE` behind `x3dhSim G`. Behind the simulator, this stack is
`simSC G` over `FR realV`, the functionality `F_AKE` whose honest port answers `getKey` by the
ratchet keyed by the stored key (`stack_ideal_stepMap`, distance `0`). Over the simulator, the
step from `FR realV` to `F_SC realV idealV` is a statement about the subroutine at the reduced
environment (`MultiHybrid.adv_withSub`), proved by a hybrid argument over the keys of the run
(`FR_realizes_F_SC`). The hybrid world `hyb i` keeps the keys outside the records of `F_AKE`, by
index: the key created at the non-idle activation `n` has index `n`; the keys of index below `i`
are read ideally, the others really. Then
* `hyb 0` is `FR realV` (`world_zero_stepMap`, filling the keys back into the records);
* `hyb i` and `hyb (i + 1)` differ in the key `i` (`hyb_step`): its draw moves from its creation
  to the start of the run (`run_world_create`, deferred sampling, `UCDeferred.run_deferred`),
  the first ratchet run on it moves to the start of the run (`run_world_read`), the pair is the
  real secure-messaging game `sm_real`, and the world that answers the first read of the key `i`
  by the challenge view is the reduction `hopRed i Z`; a later read of the key `i` is the bad
  event (`world_upto_reuse`);
* `hyb n` is `F_SC` on runs of at most `n` activations (`world_end`, `world_end_prBad`).

**The reuse of a key.** `smLayer` runs the ratchet afresh at every `getKey`, so a key read twice
(by the same session or by its partner) keys two ratchet runs with one root key. The
secure-messaging game `sm_real` uses a root key once, and the views of two runs on one root key
are not bounded by `SM_Advantage`: a root KDF that is a secure PRG on a uniform seed may give
correlated outputs on two seeds `(rk, I)`, `(rk, I')` that share `rk`. The bound therefore
contains, per key `i`, the probability `prBad (hyb i) (reuse i) Z` that the key `i` is read twice
in the world `hyb i`; it is `0` for environments that read each session key at most once.

## Main definitions

* `chanOut`, `chanHon`: the honest port of a channel over the state of `F_AKE`.
* `FR`: `F_AKE` followed by the ratchet layer, as one functionality.
* `F_SC`, `scView`: the ideal secure channel.
* `WSt`, `world`, `hyb`, `chalWorld`: the hybrid worlds; `WInv` their invariant.
* `hopRed`: the reduction of a step of the hybrid argument.
* `scBound`, `signalBound`: the bounds.
* `simSCOver`, `simSC`, `scSim`: the simulator.

## Main results

* `FR_realizes_F_SC`: `FR realV` realizes `F_SC realV idealV` with `scBound`.
* `hyb_step`: one step of the hybrid argument.
* `stack_ideal_stepMap`: the stack over `F_AKE` behind the X3DH simulator is `simSC G` over `FR`.
* `simSC_opaque`: opacity of the simulator.
* `signal_stack_realizes_FSC`: **the Signal stack realizes `F_SC` behind `scSim G`** with the gap
  Diffie–Hellman bound and the sum over the keys of the secure-messaging advantages of `hopRed`
  and of the reuse probabilities.
* `hopRed.tree`, `hopRed.compile_tree`, `hopRed.tree.timed`, `hopRed.timeBound_timed`: the
  tree of `hopRed`, its costed form by `derive_timed` and its time.

## References

* R. Canetti, H. Krawczyk, *Universally composable notions of key exchange and secure
  channels*, Eurocrypt 2002.
* M. Marlinspike, T. Perrin, *The X3DH key agreement protocol*, 2016; *The double ratchet
  algorithm*, 2016.
* J. Alwen, S. Coretti, Y. Dodis, *The double ratchet: security notions, proofs, and
  modularization for the Signal protocol*, Eurocrypt 2019.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStackUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.UCCoupling
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.Messaging.SignalStack CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.Assumptions
open PubView (eqView)
open scoped ENNReal

/-! ## Channel outputs of the honest port -/

section Chan

variable {K V : Type}

/-- The honest answer to `getKey` at the session `x`: the view `f r k` when the session `x` has
the record `r` and the key `k`, and no key otherwise. -/
noncomputable def chanOut (f : Rec K → K → SPComp V) (t : St K) (x : Inst) :
    SPComp (HOut V) :=
  match t.recs x with
  | some r =>
    match r.key with
    | some k => SPComp.map (fun v => HOut.key (some v)) (f r k)
    | none => SPComp.pure (.key none)
  | none => SPComp.pure (.key none)

/-- The honest port of a channel functionality over the state of `F_AKE`: `newSession` as in
`F_AKE`, and `getKey` answers by `chanOut f`. -/
noncomputable def chanHon (f : Rec K → K → SPComp V) : Sys (St K) HEv (HOut V) where
  init := initSt
  step t e := match e with
    | .newSession sid pid peer role => SPComp.pure (addSession t (sid, pid) peer role, .ok)
    | .getKey sid pid => SPComp.map (fun o => (t, o)) (chanOut f t (sid, pid))

end Chan

/-! ## The real stack over `F_AKE` and the ideal secure channel -/

section Func

variable {K V : Type} [Fintype K] [Nonempty K] [Inhabited K]

/-- **`F_AKE` followed by the ratchet layer**, as one functionality: `F_AKE` with uniform keys
and unlinked delivery, whose honest port answers `getKey` at a session with the key `k` by the
view `realV k` of the ratchet keyed by `k`. -/
noncomputable def FR (realV : K → SPComp V) : Sys (St K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  Sys.ofPorts (chanHon fun _ k => realV k) (advSys true true (SPComp.sample K))

/-- The view of the ideal channel at the session with the record `r` and the key `k`: the ideal
view `idealV` at a session that completed with a key chosen by the functionality, and the real
view `realV k` at a session that holds the adversary key `k`. -/
noncomputable def scView (realV : K → SPComp V) (idealV : SPComp V) (r : Rec K) (k : K) :
    SPComp V :=
  if r.status = .completed then idealV else realV k

/-- **The ideal secure channel `F_SC`** (Canetti–Krawczyk, `F_SC` from `F_KE`). The ports and
the state of `F_AKE`: the adversary port schedules sessions, corrupts parties and delivers keys
exactly as in `F_AKE` with unlinked delivery, except that a session that completes without
exposure stores no key (the placeholder `default`); the honest port opens sessions and, on
`getKey`, outputs the secure-messaging view of the session: the ideal view `idealV` for a
completed session, and the real view `realV k` under the adversary key `k` for an exposed
session. -/
noncomputable def F_SC (realV : K → SPComp V) (idealV : SPComp V) :
    Sys (St K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  Sys.ofPorts (chanHon (scView realV idealV)) (advSys true true (SPComp.pure default))

end Func

/-! ## The hybrid worlds -/

section World

variable {K V : Type} [Fintype K] [Nonempty K] [Inhabited K]

/-- The state of a hybrid world: the state of the functionality, the index of the key of each
completed session, the number of non-idle activations, the number of reads of each key and the
key of each index. A key created at the activation `n` has index `n`. -/
structure WSt (K : Type) where
  /-- The state of the functionality; a completed session holds the placeholder key. -/
  st : St K
  /-- The index of the key of a completed session. -/
  ix : Inst → Option ℕ
  /-- The number of non-idle activations. -/
  steps : ℕ
  /-- The number of reads of the key of each index. -/
  rd : ℕ → ℕ
  /-- The key of each index. -/
  kv : ℕ → K

/-- The initial state of a hybrid world. -/
def WSt.init : WSt K := ⟨initSt, fun _ => none, 0, fun _ => 0, fun _ => default⟩

/-- Whether an event is the idle event of the adversary. -/
def isIdle : HEv ⊕ AEv K → Bool
  | .inr .idle => true
  | _ => false

/-- Whether an event delivers a key. -/
def isNewKey : HEv ⊕ AEv K → Bool
  | .inr (.newKey _ _ _) => true
  | .inr (.newKeyUnlinked _ _ _) => true
  | _ => false

/-- The state of the functionality after an event, with the placeholder key for the sessions
that complete without exposure. -/
def stNext (t : St K) : HEv ⊕ AEv K → St K
  | .inl (.newSession sid pid peer role) => addSession t (sid, pid) peer role
  | .inl (.getKey _ _) => t
  | .inr .idle => t
  | .inr .poll => (pollStep t).1
  | .inr (.corrupt pid) => corruptStep t pid
  | .inr (.impersonate _ _) => t
  | .inr (.newKey sid pid k) => newKeyStep t (sid, pid) k default
  | .inr (.newKeyUnlinked sid pid k) => newKeyFreshStep t (sid, pid) k default

/-- The index given by `newKey` at the session `x`: the index of the completed partner, or the
new index `n`, to a session without a key that is not exposed. -/
def newKeyIx (t : St K) (ix : Inst → Option ℕ) (n : ℕ) (x : Inst) : Inst → Option ℕ :=
  match t.recs x with
  | some r =>
    if r.key.isNone ∧ ¬ Exposed t x r then
      Function.update ix x (match t.recs (x.1, r.peer) with
        | some p => if Partner x r p then ix (x.1, r.peer) else some n
        | none => some n)
    else ix
  | none => ix

/-- The index given by `newKeyUnlinked` at the session `x`: the new index `n`, to a session
without a key that is not exposed. -/
def newKeyFreshIx (t : St K) (ix : Inst → Option ℕ) (n : ℕ) (x : Inst) : Inst → Option ℕ :=
  match t.recs x with
  | some r => if r.key.isNone ∧ ¬ Exposed t x r then Function.update ix x (some n) else ix
  | none => ix

/-- The indices after an event. -/
def ixNext (w : WSt K) : HEv ⊕ AEv K → Inst → Option ℕ
  | .inr (.newKey sid pid _) => newKeyIx w.st w.ix w.steps (sid, pid)
  | .inr (.newKeyUnlinked sid pid _) => newKeyFreshIx w.st w.ix w.steps (sid, pid)
  | _ => w.ix

/-- The read counts after an event: `getKey` at a session with the index `j` reads the key
`j`. -/
def rdNext (w : WSt K) : HEv ⊕ AEv K → ℕ → ℕ
  | .inl (.getKey sid pid) =>
    match w.ix (sid, pid) with
    | some j => Function.update w.rd j (w.rd j + 1)
    | none => w.rd
  | _ => w.rd

/-- The state after an event, with the drawn key `kf` stored at the index `w.steps` when the
event delivers a key. -/
def wNext (w : WSt K) (e : HEv ⊕ AEv K) (kf : K) : WSt K where
  st := stNext w.st e
  ix := ixNext w e
  steps := w.steps + (if isIdle e then 0 else 1)
  rd := rdNext w e
  kv := if isNewKey e then Function.update w.kv w.steps kf else w.kv

variable (realV : K → SPComp V) (idealV : SPComp V)

/-- The view of the key with the index `j` in the hybrid world `i`: ideal below `i`, real
above `i`, and at `i` the first read by `rd1` and the later reads by `rd2`. -/
noncomputable def readOut (i : ℕ) (rd1 rd2 : K → SPComp V) (w : WSt K) (j : ℕ) : SPComp V :=
  if j < i then idealV else if j = i then (if w.rd i = 0 then rd1 (w.kv i) else rd2 (w.kv i))
  else realV (w.kv j)

/-- The view of the session `x` in the hybrid world `i`: the view of its key index, or the
real view of its key when it has no index. -/
noncomputable def wView (i : ℕ) (rd1 rd2 : K → SPComp V) (w : WSt K) (x : Inst) :
    Rec K → K → SPComp V :=
  fun _ k => match w.ix x with
    | some j => readOut realV idealV i rd1 rd2 w j
    | none => realV k

/-- The output of the hybrid world `i` at an event. -/
noncomputable def wOut (i : ℕ) (rd1 rd2 : K → SPComp V) (w : WSt K) :
    HEv ⊕ AEv K → SPComp (HOut V ⊕ AOut)
  | .inl (.newSession _ _ _ _) => SPComp.pure (.inl .ok)
  | .inl (.getKey sid pid) =>
    SPComp.map Sum.inl (chanOut (wView realV idealV i rd1 rd2 w (sid, pid)) w.st (sid, pid))
  | .inr .poll => SPComp.pure (.inr (.notice (pollStep w.st).2))
  | .inr _ => SPComp.pure (.inr .ack)

/-- The draw of the hybrid world `i`: at a key delivery, `cre` at the activation `i` and a
uniform key otherwise. -/
noncomputable def wDraw (i : ℕ) (cre : SPComp K) (w : WSt K) (e : HEv ⊕ AEv K) : SPComp K :=
  if isNewKey e then (if w.steps = i then cre else SPComp.sample K) else SPComp.pure default

/-- **The hybrid world `i`** with the creation `cre` of the key `i` and the reads `rd1`, `rd2`
of the key `i`: the draw, the next state and the output. -/
noncomputable def world (i : ℕ) (cre : SPComp K) (rd1 rd2 : K → SPComp V) :
    Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) where
  init := WSt.init
  step w e := SPComp.bind (wDraw i cre w e) fun kf =>
    SPComp.map (fun o => (wNext w e kf, o)) (wOut realV idealV i rd1 rd2 w e)

/-! ## The invariant of the hybrid worlds -/

/-- The invariant of a state of the functionality with the indices `ix` after `n` activations:
the indices are below `n` and belong to completed sessions, and a completed session holds the
placeholder key and has an index. -/
def WInvP (t : St K) (ix : Inst → Option ℕ) (n : ℕ) : Prop :=
  (∀ x j, ix x = some j → j < n ∧ ∃ r, t.recs x = some r ∧ r.status = .completed) ∧
  (∀ x r, t.recs x = some r → r.status = .completed → r.key = some default ∧ (ix x).isSome)

/-- The invariant of the hybrid worlds. -/
def WInv (w : WSt K) : Prop := WInvP w.st w.ix w.steps

omit [Fintype K] [Nonempty K] in
/-- The initial state satisfies the invariant. -/
theorem wInv_init : WInv (WSt.init : WSt K) := by
  refine ⟨fun x j h => ?_, fun x r h => ?_⟩ <;> simp [WSt.init, initSt] at h

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `addSession` keeps the records it does not create. -/
theorem addSession_recs (t : St K) (x : Inst) (peer : PartyId) (role : Role) (y : Inst) :
    (addSession t x peer role).recs y =
      if (t.recs x).isSome then t.recs y
      else if y = x then some ⟨peer, role, .fresh, none⟩ else t.recs y := by
  unfold addSession
  by_cases h : (t.recs x).isSome
  · simp [h]
  · by_cases hy : y = x
    · subst hy; simp [h]
    · simp [h, hy]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `pollStep` keeps the records. -/
theorem pollStep_recs (t : St K) : (pollStep t).1.recs = t.recs := by
  unfold pollStep; split <;> rfl

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `newKeyStep` changes at most the record of `x`. -/
theorem newKeyStep_recs (t : St K) (x : Inst) (r : Rec K) (hx : t.recs x = some r) (k kf : K)
    (y : Inst) :
    (newKeyStep t x k kf).recs y =
      if r.key.isNone ∧ y = x then
        some { r with key := some (newKeyVal t x r k kf),
                      status := if Exposed t x r then .compromised else .completed }
      else t.recs y := by
  unfold newKeyStep
  rw [hx]
  by_cases hk : r.key.isNone <;> by_cases hy : y = x <;> simp [hk, hy, setRec]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `newKeyFreshStep` changes at most the record of `x`. -/
theorem newKeyFreshStep_recs (t : St K) (x : Inst) (r : Rec K) (hx : t.recs x = some r)
    (k kf : K) (y : Inst) :
    (newKeyFreshStep t x k kf).recs y =
      if r.key.isNone ∧ y = x then
        some { r with key := some (if Exposed t x r then k else kf),
                      status := if Exposed t x r then .compromised else .completed }
      else t.recs y := by
  unfold newKeyFreshStep
  rw [hx]
  by_cases hk : r.key.isNone <;> by_cases hy : y = x <;> simp [hk, hy, setRec]

omit [Fintype K] [Nonempty K] in
/-- A key delivery at the session `x` with the record `r` keeps the invariant, when it stores
the placeholder key and an index below `n + 1` at a session that it completes. -/
theorem wInvP_deliver {t t' : St K} {ix ix' : Inst → Option ℕ} {n : ℕ} (h : WInvP t ix n)
    {x : Inst} {r : Rec K} (hx : t.recs x = some r) (kv : K) (jx : Option ℕ)
    (hr : ∀ y, t'.recs y = if r.key.isNone ∧ y = x then
        some { r with key := some kv,
                      status := if Exposed t x r then .compromised else .completed }
      else t.recs y)
    (hix : ∀ y, ix' y = if r.key.isNone ∧ ¬ Exposed t x r ∧ y = x then jx else ix y)
    (hkv : ¬ Exposed t x r → kv = default)
    (hjx : ¬ Exposed t x r → r.key.isNone → ∃ j, jx = some j ∧ j < n + 1) :
    WInvP t' ix' (n + 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun y j hj => ?_, fun y r' hr' hc => ?_⟩
  · rw [hix y] at hj
    by_cases hc : r.key.isNone ∧ ¬ Exposed t x r ∧ y = x
    · rw [ite_eq_left hc] at hj
      obtain ⟨j', hj', hlt⟩ := hjx hc.2.1 hc.1
      rw [hj'] at hj; cases hj
      refine ⟨hlt, _, (hr y).trans (ite_eq_left ⟨hc.1, hc.2.2⟩), by simp [hc.2.1]⟩
    · rw [ite_eq_right hc] at hj
      obtain ⟨hlt, r'', hr'', hc''⟩ := h1 y j hj
      refine ⟨by omega, ?_⟩
      by_cases hy : r.key.isNone ∧ y = x
      · exfalso
        obtain ⟨hk, rfl⟩ := hy
        rw [hx] at hr''; cases hr''
        have := (h2 _ _ hx hc'').1
        simp [this] at hk
      · exact ⟨r'', (hr y).trans (ite_eq_right hy) ▸ hr'', hc''⟩
  · rw [hr y] at hr'
    by_cases hy : r.key.isNone ∧ y = x
    · rw [ite_eq_left hy] at hr'
      cases hr'
      have he : ¬ Exposed t x r := by intro he; simp [he] at hc
      refine ⟨by simp [hkv he], ?_⟩
      rw [hix y, ite_eq_left ⟨hy.1, he, hy.2⟩]
      obtain ⟨j, hj, _⟩ := hjx he hy.1
      simp [hj]
    · rw [ite_eq_right hy] at hr'
      refine ⟨(h2 y r' hr' hc).1, ?_⟩
      rw [hix y, ite_eq_right (fun h => hy ⟨h.1, h.2.2⟩)]
      exact (h2 y r' hr' hc).2

omit [Fintype K] [Nonempty K] in
/-- **The invariant is preserved** by every event and every drawn key. -/
theorem wInv_next {w : WSt K} (hw : WInv w) (e : HEv ⊕ AEv K) (kf : K) :
    WInv (wNext w e kf) := by
  have hmono : ∀ {t : St K} {ix : Inst → Option ℕ} {n m : ℕ}, WInvP t ix n → n ≤ m →
      WInvP t ix m := fun h hnm =>
    ⟨fun y j hj => ⟨by have := (h.1 y j hj).1; omega, (h.1 y j hj).2⟩, h.2⟩
  obtain ⟨h1, h2⟩ := hw
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩)
  · refine ⟨fun y j hj => ?_, fun y r hr hc => ?_⟩
    · simp only [wNext, ixNext, stNext] at hj ⊢
      obtain ⟨hlt, r, hr, hc⟩ := h1 y j hj
      refine ⟨by simp [isIdle]; omega, r, ?_, hc⟩
      rw [addSession_recs]
      split_ifs with ha hy
      · exact hr
      · subst hy; simp [hr] at ha
      · exact hr
    · simp only [wNext, ixNext, stNext] at hr hc ⊢
      rw [addSession_recs] at hr
      split_ifs at hr with ha hy
      · exact h2 y r hr hc
      · cases hr; simp at hc
      · exact h2 y r hr hc
  · exact hmono ⟨h1, h2⟩ (by simp [wNext, isIdle])
  · exact hmono ⟨h1, h2⟩ (by simp [wNext, isIdle])
  · have h' : WInvP (pollStep w.st).1 w.ix w.steps := by
      unfold WInvP; rw [pollStep_recs]; exact ⟨h1, h2⟩
    exact hmono h' (by simp [wNext, isIdle])
  · exact hmono (t := corruptStep w.st pid) ⟨h1, h2⟩ (by simp [wNext, isIdle])
  · exact hmono ⟨h1, h2⟩ (by simp [wNext, isIdle])
  · show WInvP (newKeyStep w.st (sid, pid) k default) (newKeyIx w.st w.ix w.steps (sid, pid))
      (w.steps + 1)
    rcases hx : w.st.recs (sid, pid) with _ | r
    · have hs : newKeyStep w.st (sid, pid) k default = w.st := by simp [newKeyStep, hx]
      rw [hs]; simp only [newKeyIx, hx]
      exact hmono ⟨h1, h2⟩ (by omega)
    · refine wInvP_deliver ⟨h1, h2⟩ hx (newKeyVal w.st (sid, pid) r k default)
        (match w.st.recs (sid, r.peer) with
          | some p => if Partner (sid, pid) r p then w.ix (sid, r.peer) else some w.steps
          | none => some w.steps)
        (newKeyStep_recs _ _ r hx k default) (fun y => ?_) (fun he => ?_) (fun he _ => ?_)
      · simp only [newKeyIx, hx]
        by_cases hc : r.key.isNone ∧ ¬ Exposed w.st (sid, pid) r
        · rw [ite_eq_left hc]
          by_cases hy : y = (sid, pid)
          · subst hy; simp [hc]
          · simp [hy]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, h.2.1⟩)]
      · unfold newKeyVal
        rw [ite_eq_right he]
        split
        · next p hp =>
          split_ifs with hpp
          · rw [(h2 _ p hp hpp.2.2).1]; rfl
          · rfl
        · rfl
      · split
        · next p hp =>
          split_ifs with hpp
          · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (h2 _ p hp hpp.2.2).2
            exact ⟨j, hj, by have := (h1 _ j hj).1; omega⟩
          · exact ⟨w.steps, rfl, by omega⟩
        · exact ⟨w.steps, rfl, by omega⟩
  · show WInvP (newKeyFreshStep w.st (sid, pid) k default)
      (newKeyFreshIx w.st w.ix w.steps (sid, pid)) (w.steps + 1)
    rcases hx : w.st.recs (sid, pid) with _ | r
    · have hs : newKeyFreshStep w.st (sid, pid) k default = w.st := by
        simp [newKeyFreshStep, hx]
      rw [hs]; simp only [newKeyFreshIx, hx]
      exact hmono ⟨h1, h2⟩ (by omega)
    · refine wInvP_deliver ⟨h1, h2⟩ hx (if Exposed w.st (sid, pid) r then k else default)
        (some w.steps) (newKeyFreshStep_recs _ _ r hx k default) (fun y => ?_)
        (fun he => by simp [he]) (fun _ _ => ⟨w.steps, rfl, by omega⟩)
      simp only [newKeyFreshIx, hx]
      by_cases hc : r.key.isNone ∧ ¬ Exposed w.st (sid, pid) r
      · rw [ite_eq_left hc]
        by_cases hy : y = (sid, pid)
        · subst hy; simp [hc]
        · simp [hy]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, h.2.1⟩)]

end World

/-! ## Steps of the hybrid worlds -/

section Steps

variable {K V : Type} [Fintype K] [Nonempty K] [Inhabited K]
  (realV : K → SPComp V) (idealV : SPComp V)

/-- The outcomes of a step of a hybrid world: the next state at a possible draw. -/
theorem world_outcome {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((world realV idealV i cre rd1 rd2).step w e) q) :
    ∃ kf, IsOutcome (wDraw i cre w e) kf ∧ q.1 = wNext w e kf := by
  simp only [world] at hq
  obtain ⟨kf, hkf, hq'⟩ := isOutcome_bind hq
  obtain ⟨o, _, rfl⟩ := exists_of_isOutcome_map hq'
  exact ⟨kf, hkf, rfl⟩

/-- The steps of a hybrid world keep the invariant. -/
theorem world_inv {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)} (hw : WInv w)
    (hq : IsOutcome ((world realV idealV i cre rd1 rd2).step w e) q) : WInv q.1 := by
  obtain ⟨kf, _, h⟩ := world_outcome realV idealV hq
  rw [h]; exact wInv_next hw e kf

/-- The number of activations after a step. -/
theorem world_steps {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((world realV idealV i cre rd1 rd2).step w e) q) :
    q.1.steps = w.steps + (if isIdle e then 0 else 1) := by
  obtain ⟨kf, _, h⟩ := world_outcome realV idealV hq
  rw [h]; rfl

/-- The read counts after a step. -/
theorem world_rd {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((world realV idealV i cre rd1 rd2).step w e) q) :
    q.1.rd = rdNext w e := by
  obtain ⟨kf, _, h⟩ := world_outcome realV idealV hq
  rw [h]; rfl

/-- A hybrid world is idle at the idle event of the adversary. -/
theorem world_idleAt (i : ℕ) (cre : SPComp K) (rd1 rd2 : K → SPComp V) :
    MultiHybrid.IdleAt (world realV idealV i cre rd1 rd2) (.inr .idle) (.inr .ack) := by
  intro w
  simp only [world, wDraw, isNewKey, wOut, SPComp.pure_bind, SPComp.map, Bool.false_eq_true,
    ite_false]
  rfl

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- A map of a computation that does not fail does not fail. -/
theorem map_noFail {α β : Type} (f : α → β) {c : SPComp α} (hc : SPComp.NoFail c) :
    SPComp.NoFail (SPComp.map f c) :=
  Assumptions.SPComp.bind_noFail hc fun _ => SPComp.pure_noFail _

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The outputs of a hybrid world do not fail when its views do not fail. -/
theorem wOut_noFail {i : ℕ} {rd1 rd2 : K → SPComp V}
    (hR : ∀ k, SPComp.NoFail (realV k)) (hI : SPComp.NoFail idealV)
    (h1 : ∀ k, SPComp.NoFail (rd1 k)) (h2 : ∀ k, SPComp.NoFail (rd2 k))
    (w : WSt K) (e : HEv ⊕ AEv K) : SPComp.NoFail (wOut realV idealV i rd1 rd2 w e) := by
  rcases e with (_ | ⟨sid, pid⟩) | (_ | _ | _ | _ | _ | _)
  all_goals try exact SPComp.pure_noFail _
  refine map_noFail _ ?_
  unfold chanOut
  split
  · split
    · refine map_noFail _ ?_
      unfold wView
      split
      · unfold readOut
        split_ifs
        · exact hI
        · exact h1 _
        · exact h2 _
        · exact hR _
      · exact hR _
    · exact SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

/-- The steps of a hybrid world do not fail when its views and its creation do not fail. -/
theorem world_noFail {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V}
    (hR : ∀ k, SPComp.NoFail (realV k)) (hI : SPComp.NoFail idealV)
    (hc : SPComp.NoFail cre) (h1 : ∀ k, SPComp.NoFail (rd1 k)) (h2 : ∀ k, SPComp.NoFail (rd2 k))
    (w : WSt K) (e : HEv ⊕ AEv K) :
    SPComp.NoFail ((world realV idealV i cre rd1 rd2).step w e) := by
  simp only [world]
  refine Assumptions.SPComp.bind_noFail ?_ fun kf =>
    map_noFail _ (wOut_noFail realV idealV hR hI h1 h2 w e)
  unfold wDraw
  split_ifs
  · exact hc
  · exact (CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K).2
  · exact SPComp.pure_noFail _

/-! ## Deferred sampling at the creation of the key `i` -/

/-- **The key `i` drawn at its creation is the key `i` drawn before the run.** The hybrid world
whose key `i` is drawn from `c` at the activation `i` has the run of the worlds whose key `i` is
`k`, averaged over `k` drawn from `c` before the run. -/
theorem run_world_create (i : ℕ) {c : SPComp K} (hc : SPComp.IsPure c) (hcn : SPComp.NoFail c)
    (rd1 rd2 : K → SPComp V) {ζ : Type} (bad : WSt K → Bool) (Z : Strat ζ (HEv ⊕ AEv K) _) :
    SPComp.bind c (fun k => run (world realV idealV i (SPComp.pure k) rd1 rd2) bad Z) =
      run (world realV idealV i c rd1 rd2) bad Z := by
  refine run_deferred c hc hcn (fun k => world realV idealV i (SPComp.pure k) rd1 rd2)
    (world realV idealV i c rd1 rd2) (fun _ => True) (fun w => i < w.steps)
    (fun w e => w.steps = i ∧ isNewKey e = true) (fun _ => rfl) trivial
    (by simp [world, WSt.init]) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    ?_ ?_ ?_ ?_ ?_ bad Z
  · intro k w e _ hp
    simp only [world, wDraw, show w.steps ≠ i by omega, ite_false]
  · intro w e q _ hp hq
    have := world_steps realV idealV hq
    omega
  · intro k w e _ hp hu
    simp only [world, wDraw]
    by_cases hn : isNewKey e = true
    · simp only [hn, ite_true, show w.steps ≠ i from fun h => hu ⟨h, hn⟩, ite_false]
    · simp only [hn, Bool.false_eq_true, ite_false]
  · intro w e _ _ hu
    simp only [world, wDraw, hu.1, hu.2, ite_true, SPComp.pure_bind]
  · intro k w e q _ hp hu hq
    have := world_steps realV idealV hq
    have hi : isIdle e = false := by
      rcases e with _ | (_ | _ | _ | _ | _ | _) <;> simp_all [isNewKey, isIdle]
    rw [hi] at this
    simp only [Bool.false_eq_true, ite_false] at this
    omega



/-! ## Deferred sampling at the first read of the key `i` -/

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The read counts do not decrease. -/
theorem rdNext_ge (w : WSt K) (e : HEv ⊕ AEv K) (j : ℕ) : w.rd j ≤ rdNext w e j := by
  rcases e with (_ | ⟨sid, pid⟩) | _
  · exact le_rfl
  · rcases h : w.ix (sid, pid) with _ | j'
    · simp only [rdNext, h, le_refl]
    · simp only [rdNext, h]
      by_cases hj : j = j'
      · subst hj; simp
      · rw [Function.update_of_ne hj]
  · exact le_rfl

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- A new index is an existing index or the index of the current activation at a key
delivery. -/
theorem ixNext_some {w : WSt K} {e : HEv ⊕ AEv K} {y : Inst} {j : ℕ}
    (h : ixNext w e y = some j) :
    (∃ y', w.ix y' = some j) ∨ (j = w.steps ∧ isNewKey e = true) := by
  rcases e with _ | (_ | _ | _ | _ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩)
  all_goals try exact Or.inl ⟨y, h⟩
  · simp only [ixNext, newKeyIx] at h
    rcases hx : w.st.recs (sid, pid) with _ | r
    · rw [hx] at h; exact Or.inl ⟨y, h⟩
    · rw [hx] at h
      dsimp only at h
      split_ifs at h with hc
      · by_cases hy : y = (sid, pid)
        · subst hy
          rw [Function.update_self] at h
          rcases hp : w.st.recs (sid, r.peer) with _ | p
          · rw [hp] at h; cases h; exact Or.inr ⟨rfl, rfl⟩
          · rw [hp] at h
            dsimp only at h
            split_ifs at h
            · exact Or.inl ⟨_, h⟩
            · cases h; exact Or.inr ⟨rfl, rfl⟩
        · rw [Function.update_of_ne hy] at h; exact Or.inl ⟨y, h⟩
      · exact Or.inl ⟨y, h⟩
  · simp only [ixNext, newKeyFreshIx] at h
    rcases hx : w.st.recs (sid, pid) with _ | r
    · rw [hx] at h; exact Or.inl ⟨y, h⟩
    · rw [hx] at h
      dsimp only at h
      split_ifs at h with hc
      · by_cases hy : y = (sid, pid)
        · subst hy
          rw [Function.update_self] at h
          cases h; exact Or.inr ⟨rfl, rfl⟩
        · rw [Function.update_of_ne hy] at h; exact Or.inl ⟨y, h⟩
      · exact Or.inl ⟨y, h⟩

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The views of the indices other than `i` do not depend on the reads of `i`. -/
theorem readOut_ne {i j : ℕ} (h : j ≠ i) (rd1 rd2 rd1' rd2' : K → SPComp V) (w : WSt K) :
    readOut realV idealV i rd1 rd2 w j = readOut realV idealV i rd1' rd2' w j := by
  simp [readOut, h]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- After the first read of `i`, the views do not depend on the first read. -/
theorem readOut_post {i : ℕ} (rd1 rd1' rd2 : K → SPComp V) {w : WSt K} (h : w.rd i ≠ 0)
    (j : ℕ) : readOut realV idealV i rd1 rd2 w j = readOut realV idealV i rd1' rd2 w j := by
  simp [readOut, h]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- Two states with the same functionality state and indices, and two families of views that
agree at the index of the session that `e` reads, give the same output at `e`. -/
theorem wOut_congr₂ {i i' : ℕ} {rd1 rd2 rd1' rd2' : K → SPComp V} {w w' : WSt K}
    (hst : w.st = w'.st) (hix : w.ix = w'.ix) (e : HEv ⊕ AEv K)
    (h : ∀ sid pid j, e = .inl (.getKey sid pid) → w.ix (sid, pid) = some j →
      readOut realV idealV i rd1 rd2 w j = readOut realV idealV i' rd1' rd2' w' j) :
    wOut realV idealV i rd1 rd2 w e = wOut realV idealV i' rd1' rd2' w' e := by
  rcases e with (_ | ⟨sid, pid⟩) | (_ | _ | _ | _ | _ | _)
  all_goals try rfl
  · simp only [wOut]
    congr 1
    unfold chanOut
    rw [← hst]
    split
    · split
      · congr 1
        unfold wView
        rw [← hix]
        split
        · next j hj => exact h sid pid j rfl hj
        · rfl
      · rfl
    · rfl
  · simp only [wOut, hst]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- Two families of views that agree at the index of the session that `e` reads give the
same output at `e`. -/
theorem wOut_congr {i i' : ℕ} {rd1 rd2 rd1' rd2' : K → SPComp V} {w : WSt K}
    (e : HEv ⊕ AEv K)
    (h : ∀ sid pid j, e = .inl (.getKey sid pid) → w.ix (sid, pid) = some j →
      readOut realV idealV i rd1 rd2 w j = readOut realV idealV i' rd1' rd2' w j) :
    wOut realV idealV i rd1 rd2 w e = wOut realV idealV i' rd1' rd2' w e :=
  wOut_congr₂ realV idealV rfl rfl e h

/-- **The first read of the key `i` drawn at the read is the first read drawn before the run.**
If every key that the creation `cre` may give has the first view `rd1 kf = c`, the run of the
hybrid world with the first read `rd1` is the run of the worlds whose first read of the key `i`
returns `v`, averaged over `v` drawn from `c` before the run. -/
theorem run_world_read (i : ℕ) (cre : SPComp K) {c : SPComp V} (hc : SPComp.IsPure c)
    (hcn : SPComp.NoFail c) (rd1 rd2 : K → SPComp V)
    (hcre : ∀ kf, IsOutcome cre kf → rd1 kf = c) {ζ : Type} (bad : WSt K → Bool)
    (Z : Strat ζ (HEv ⊕ AEv K) _) :
    SPComp.bind c (fun v => run (world realV idealV i cre (fun _ => SPComp.pure v) rd2) bad Z) =
      run (world realV idealV i cre rd1 rd2) bad Z := by
  have hinv : ∀ (r1 : K → SPComp V) (w : WSt K) (e : HEv ⊕ AEv K) (q : WSt K × (HOut V ⊕ AOut)),
      (WInv w ∧ ∀ x, w.ix x = some i → rd1 (w.kv i) = c) →
      IsOutcome ((world realV idealV i cre r1 rd2).step w e) q →
      WInv q.1 ∧ ∀ x, q.1.ix x = some i → rd1 (q.1.kv i) = c := by
    intro r1 w e q ⟨hw, hr⟩ hq
    obtain ⟨kf, hkf, hq1⟩ := world_outcome realV idealV hq
    refine ⟨hq1 ▸ wInv_next hw e kf, fun x hx => ?_⟩
    rw [hq1] at hx ⊢
    rcases ixNext_some hx with ⟨y', hy'⟩ | ⟨hi, hn⟩
    · have hlt := (hw.1 y' i hy').1
      have : (wNext w e kf).kv i = w.kv i := by
        simp only [wNext]
        split_ifs
        · rw [Function.update_of_ne (by omega)]
        · rfl
      rw [this]; exact hr y' hy'
    · have hd : wDraw i cre w e = cre := by simp [wDraw, hn, ← hi]
      rw [hd] at hkf
      have : (wNext w e kf).kv i = kf := by simp [wNext, hn, hi]
      rw [this]; exact hcre kf hkf
  refine run_deferred c hc hcn (fun v => world realV idealV i cre (fun _ => SPComp.pure v) rd2)
    (world realV idealV i cre rd1 rd2)
    (fun w => WInv w ∧ ∀ x, w.ix x = some i → rd1 (w.kv i) = c) (fun w => 1 ≤ w.rd i)
    (fun w e => ∃ sid pid, e = .inl (.getKey sid pid) ∧ w.ix (sid, pid) = some i)
    (fun _ => rfl) ⟨wInv_init, fun x hx => by simp [world, WSt.init] at hx⟩
    (by simp [world, WSt.init]) (hinv rd1) (fun v => hinv _) ?_ ?_ ?_ ?_ ?_ bad Z
  · intro v w e _ hp
    simp only [world]
    rw [wOut_congr realV idealV e (fun _ _ j _ _ => readOut_post realV idealV _ rd1 rd2
      (show w.rd i ≠ 0 by omega) j)]
  · intro w e q _ hp hq
    rw [world_rd realV idealV hq]
    exact le_trans hp (rdNext_ge w e i)
  · intro v w e _ hp hu
    simp only [world]
    congr 1; funext kf; congr 1
    refine wOut_congr realV idealV e (fun sid pid j he hj => ?_)
    have hji : j ≠ i := fun h => hu ⟨sid, pid, he, h ▸ hj⟩
    exact readOut_ne realV idealV hji _ _ _ _ w
  · rintro w e ⟨_, hr⟩ hp ⟨sid, pid, rfl, hx⟩
    simp only [world, wDraw, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOut]
    unfold chanOut wView
    rw [hx]
    rcases hr' : w.st.recs (sid, pid) with _ | r
    · dsimp only; exact (bind_const_of_isPure hc hcn _).symm
    · rcases hk : r.key with _ | k
      · simp only [hk]; exact (bind_const_of_isPure hc hcn _).symm
      · simp only [hk, readOut, lt_irrefl, ite_false, ite_true, show w.rd i = 0 by omega,
          hr _ hx, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · intro v w e q _ hp hu hq
    obtain ⟨sid, pid, rfl, hx⟩ := hu
    rw [world_rd realV idealV hq]
    simp [rdNext, hx]

/-! ## A second read of the key `i` -/

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- A judgment at the equality of heaps conjoined with a fact `P` follows from the judgments
under `P`. -/
theorem rHoare_eqPre_and_of {α β : Type} {P : Prop} {c₁ : SPComp α} {c₂ : SPComp β}
    {Ψ : RPost α β} (h : P → rHoare eqPre c₁ c₂ Ψ) :
    rHoare (fun h₁ h₂ => h₁ = h₂ ∧ P) c₁ c₂ Ψ :=
  fun h₁ h₂ hp => h hp.2 h₁ h₂ hp.1

/-- The relation of two hybrid worlds that differ only in the key `i`: equal states except at
the key of the index `i`. -/
def relExcept (i : ℕ) (a b : WSt K) : Prop :=
  a.st = b.st ∧ a.ix = b.ix ∧ a.steps = b.steps ∧ a.rd = b.rd ∧ ∀ j, j ≠ i → a.kv j = b.kv j

/-- The bad event of the key `i`: it is read twice. -/
def reuse (i : ℕ) (w : WSt K) : Bool := decide (2 ≤ w.rd i)

omit [Fintype K] [Nonempty K] in
/-- The next states of related states are related, for draws that agree unless the activation
creates the key `i`. -/
theorem relExcept_next {i : ℕ} {a b : WSt K} (h : relExcept i a b) (e : HEv ⊕ AEv K)
    {kf kf' : K} (hk : a.steps ≠ i → kf = kf') :
    relExcept i (wNext a e kf) (wNext b e kf') := by
  obtain ⟨hst, hix, hs, hrd, hkv⟩ := h
  refine ⟨?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [wNext, hst]
  · rcases e with _ | (_ | _ | _ | _ | _ | _) <;> simp [wNext, ixNext, hst, hix, hs]
  · simp only [wNext, hs]
  · rcases e with (_ | ⟨sid, pid⟩) | _ <;> simp [wNext, rdNext, hix, hrd]
  · simp only [wNext]
    split_ifs
    · by_cases hjs : j = a.steps
      · subst hjs
        rw [Function.update_self, hs, Function.update_self]
        exact hk hj
      · rw [Function.update_of_ne hjs, ← hs, Function.update_of_ne hjs]; exact hkv j hj
    · exact hkv j hj

/-- **Up to a second read of the key `i`.** Two hybrid worlds whose key `i` is created as `k`
and as a uniform key, whose first read of the key `i` does not depend on the key, and whose
later reads differ, are at distance at most the probability that the key `i` is read twice in
the first world. -/
theorem world_upto_reuse (i : ℕ) (k : K) {rd1 rdA rdB : K → SPComp V}
    (hrd1 : ∀ a b, rd1 a = rd1 b) (hR : ∀ k, SPComp.NoFail (realV k))
    (hI : SPComp.NoFail idealV) (h1 : ∀ k, SPComp.NoFail (rd1 k))
    (hA : ∀ k, SPComp.NoFail (rdA k)) (hB : ∀ k, SPComp.NoFail (rdB k)) :
    Realizes (world realV idealV i (SPComp.pure k) rd1 rdA)
      (world realV idealV i (SPComp.sample K) rd1 rdB)
      (fun _ Z => prBad (world realV idealV i (SPComp.pure k) rd1 rdA) (reuse i) Z) := by
  refine realizes_upto_bad_rel _ _ (relExcept i) (reuse i)
    ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    (world_noFail realV idealV hR hI (SPComp.pure_noFail k) h1 hA)
    (world_noFail realV idealV hR hI (CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K).2 h1 hB)
    fun a b e hab hbad => ?_
  have hmap : ∀ {α β : Type} (f : α → β) (c : SPComp α),
      SPComp.map f c = SPComp.bind c fun x => SPComp.pure (f x) := fun _ _ => rfl
  simp only [world, hmap]
  -- the draws
  have hdraw : rHoare eqPre (wDraw i (SPComp.pure k) a e) (wDraw i (SPComp.sample K) b e)
      (fun kf h kf' h' => h = h' ∧ (a.steps ≠ i → kf = kf')) := by
    by_cases hc : isNewKey e = true ∧ a.steps = i
    · have hb : b.steps = i := hab.2.2.1 ▸ hc.2
      simp only [wDraw, hc.1, hc.2, hb, ite_true]
      rw [← SPComp.bind_pure (SPComp.sample K)]
      exact rHoare_sample_r fun kf' => rHoare_ret fun h h' hh => ⟨hh, fun hn => by simp_all⟩
    · have heq : wDraw i (SPComp.pure k) a e = wDraw i (SPComp.sample K) b e := by
        simp only [wDraw, ← hab.2.2.1]
        by_cases hn : isNewKey e = true
        · have : a.steps ≠ i := fun h => hc ⟨hn, h⟩
          simp [hn, this]
        · simp [hn]
      rw [heq]
      exact rHoare_conseq (fun _ _ h => h) (fun _ _ _ _ hh => ⟨hh.2, fun _ => hh.1⟩)
        (rHoare_refl _)
  refine rHoare_bind hdraw fun kf kf' => ?_
  refine rHoare_eqPre_and_of (P := a.steps ≠ i → kf = kf') fun hk => ?_
  have hnext := relExcept_next hab e hk
  by_cases hbr : ∃ sid pid, e = .inl (.getKey sid pid) ∧ a.ix (sid, pid) = some i ∧
      a.rd i ≠ 0
  · -- a second read: the run is bad
    obtain ⟨sid, pid, rfl, hx, hr⟩ := hbr
    refine rHoare_bind (rHoare_true_of_noFail (wOut_noFail realV idealV hR hI h1 hA a _)
      (wOut_noFail realV idealV hR hI h1 hB b _)) fun o o' => rHoare_ret fun _ _ _ => ?_
    left
    have hle : 1 ≤ a.rd i := Nat.one_le_iff_ne_zero.mpr hr
    simp [reuse, wNext, rdNext, hx]
    omega
  · have hout : wOut realV idealV i rd1 rdA a e = wOut realV idealV i rd1 rdB b e := by
      refine wOut_congr₂ realV idealV hab.1 hab.2.1 e fun sid pid j he hj => ?_
      unfold readOut
      by_cases hji : j = i
      · subst hji
        have hr : a.rd j = 0 := by
          by_contra hr; exact hbr ⟨sid, pid, he, hj, hr⟩
        simp [hr, ← hab.2.2.2.1, hrd1 (a.kv j) (b.kv j)]
      · simp [hji, hab.2.2.2.2 j hji]
    rw [← hout]
    refine rHoare_bind (rHoare_refl _) fun o o' => rHoare_ret fun h h' hh => ?_
    obtain ⟨rfl, rfl⟩ := hh
    exact Or.inr ⟨rfl, hnext, rfl⟩

/-! ## The last hybrid world and the ideal secure channel -/

/-- The output of `F_SC` at an event. -/
noncomputable def scOut (t : St K) : HEv ⊕ AEv K → SPComp (HOut V ⊕ AOut)
  | .inl (.newSession _ _ _ _) => SPComp.pure (.inl .ok)
  | .inl (.getKey sid pid) => SPComp.map Sum.inl (chanOut (scView realV idealV) t (sid, pid))
  | .inr .poll => SPComp.pure (.inr (.notice (pollStep t).2))
  | .inr _ => SPComp.pure (.inr .ack)

omit [Fintype K] [Nonempty K] in
/-- The steps of `F_SC`: the next state of the functionality with the placeholder key and the
output `scOut`. -/
theorem F_SC_step (t : St K) (e : HEv ⊕ AEv K) :
    (F_SC realV idealV).step t e =
      SPComp.map (fun o => (stNext t e, o)) (scOut realV idealV t e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩) <;>
    simp [F_SC, chanHon, advSys, stNext, scOut, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- Two view functions that agree at the record and the key of the session give the same
channel output. -/
theorem chanOut_congr {f g : Rec K → K → SPComp V} {t : St K} {x : Inst}
    (h : ∀ r k, t.recs x = some r → r.key = some k → f r k = g r k) :
    chanOut f t x = chanOut g t x := by
  unfold chanOut
  rcases hx : t.recs x with _ | r
  · rfl
  · rcases hk : r.key with _ | k
    · simp only [hk]
    · simp only [hk, h r k hx hk]

omit [Fintype K] [Nonempty K] in
/-- In a state of the invariant whose indices are below `n`, the hybrid world `n` with real
reads outputs as `F_SC`. -/
theorem wOut_eq_scOut {n : ℕ} {w : WSt K} (hw : WInv w) (hn : w.steps ≤ n)
    (e : HEv ⊕ AEv K) :
    wOut realV idealV n realV realV w e = scOut realV idealV w.st e := by
  rcases e with (_ | ⟨sid, pid⟩) | (_ | _ | _ | _ | _ | _)
  all_goals try rfl
  simp only [wOut, scOut]
  congr 1
  refine chanOut_congr fun r k hr _ => ?_
  unfold wView scView
  rcases hj : w.ix (sid, pid) with _ | j
  · have hc : r.status ≠ .completed := fun hc => by
      have := (hw.2 _ r hr hc).2
      rw [hj] at this; simp at this
    simp [hc]
  · obtain ⟨hlt, r', hr', hc'⟩ := hw.1 _ j hj
    rw [hr] at hr'; cases hr'
    simp [readOut, show j < n by omega, hc']

omit [Inhabited K] in
/-- The draws of a hybrid world neither touch the heap nor fail, for a creation that does
not. -/
theorem wDraw_pureNF {i : ℕ} {cre : SPComp K} (hc : SPComp.IsPure cre ∧ SPComp.NoFail cre)
    [Inhabited K] (w : WSt K) (e : HEv ⊕ AEv K) :
    SPComp.IsPure (wDraw i cre w e) ∧ SPComp.NoFail (wDraw i cre w e) := by
  unfold wDraw
  split_ifs
  · exact hc
  · exact CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K
  · exact CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _

/-- **The last hybrid world is the ideal secure channel up to `n` activations.** The hybrid
world `n` with real reads realizes `F_SC` with bound the probability that the run exceeds `n`
non-idle activations. -/
theorem world_end (n : ℕ) (hR : ∀ k, SPComp.NoFail (realV k)) (hI : SPComp.NoFail idealV) :
    Realizes (world realV idealV n (SPComp.sample K) realV realV) (F_SC realV idealV)
      (fun _ Z => prBad (world realV idealV n (SPComp.sample K) realV realV)
        (fun w => decide (n < w.steps)) Z) := by
  have hs := CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K
  refine realizes_upto_bad_rel _ _ (fun w t => w.st = t ∧ WInv w)
    (fun w => decide (n < w.steps)) ⟨rfl, wInv_init⟩
    (world_noFail realV idealV hR hI hs.2 hR hR) (fun t e => by
      rw [F_SC_step]
      refine map_noFail _ ?_
      rcases e with (_ | ⟨sid, pid⟩) | (_ | _ | _ | _ | _ | _)
      all_goals try exact SPComp.pure_noFail _
      refine map_noFail _ ?_
      unfold chanOut
      split
      · split
        · refine map_noFail _ ?_
          unfold scView; split_ifs
          · exact hI
          · exact hR _
        · exact SPComp.pure_noFail _
      · exact SPComp.pure_noFail _) fun w t e hwt hbad => ?_
  obtain ⟨rfl, hw⟩ := hwt
  have hn : w.steps ≤ n := by simpa using hbad
  have hd := wDraw_pureNF hs (i := n) w e
  rw [F_SC_step, ← wOut_eq_scOut realV idealV hw hn e,
    ← bind_const_of_isPure hd.1 hd.2 (SPComp.map _ _)]
  simp only [world]
  refine rHoare_bind (rHoare_refl _) fun kf kf' =>
    rHoare_conseq (Φ := eqPre) (fun _ _ hh => hh.2) (fun _ _ _ _ h => h) ?_
  simp only [SPComp.map]
  refine rHoare_bind (rHoare_refl _) fun o o' => rHoare_ret fun _ _ hh => ?_
  obtain ⟨rfl, rfl⟩ := hh
  exact Or.inr ⟨rfl, ⟨rfl, wInv_next hw e kf⟩, rfl⟩

/-- **The counter of the last hybrid world.** In a run of at most `n` activations, the hybrid
world never exceeds `n` non-idle activations. -/
theorem world_end_prBad (n : ℕ) {cre : SPComp K} {rd1 rd2 : K → SPComp V} {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) (hZ : Z.input.rounds ≤ n) :
    prBad (world realV idealV n cre rd1 rd2) (fun w => decide (n < w.steps)) Z = 0 :=
  prBad_counter_eq_zero _ WSt.steps n (fun w e q hq => by
    rw [world_steps realV idealV hq]; split_ifs <;> omega) Z (by simpa [world, WSt.init] using hZ)

/-! ## The first hybrid world and the real stack over `F_AKE` -/

/-- The record of the session `x` with the key of its index. -/
def fillRec (w : WSt K) (x : Inst) (r : Rec K) : Rec K :=
  match w.ix x with
  | some j => { r with key := some (w.kv j) }
  | none => r

/-- The state of `F_AKE` of a hybrid state: each completed session holds the key of its
index. -/
def fill (w : WSt K) : St K := { w.st with recs := fun x => (w.st.recs x).map (fillRec w x) }

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- Extensionality of the state of `F_AKE`. -/
theorem St.ext' {t t' : St K} (h1 : t.recs = t'.recs) (h2 : t.corrupt = t'.corrupt)
    (h3 : t.notices = t'.notices) (h4 : t.cursor = t'.cursor) : t = t' := by
  cases t; cases t'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `newKeyStep` changes only the records. -/
theorem newKeyStep_fields (t : St K) (x : Inst) (k kf : K) :
    (newKeyStep t x k kf).corrupt = t.corrupt ∧ (newKeyStep t x k kf).notices = t.notices ∧
      (newKeyStep t x k kf).cursor = t.cursor := by
  unfold newKeyStep
  split
  · split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `newKeyFreshStep` changes only the records. -/
theorem newKeyFreshStep_fields (t : St K) (x : Inst) (k kf : K) :
    (newKeyFreshStep t x k kf).corrupt = t.corrupt ∧
      (newKeyFreshStep t x k kf).notices = t.notices ∧
      (newKeyFreshStep t x k kf).cursor = t.cursor := by
  unfold newKeyFreshStep
  split
  · split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

omit [Fintype K] [Nonempty K] in
/-- A session without a key has no index. -/
theorem ix_none_of_key_none {w : WSt K} (hw : WInv w) {x : Inst} {r : Rec K}
    (hx : w.st.recs x = some r) (hk : r.key = none) : w.ix x = none := by
  rcases hj : w.ix x with _ | j
  · rfl
  · obtain ⟨_, r', hr', hc⟩ := hw.1 x j hj
    rw [hx] at hr'; cases hr'
    have := (hw.2 x r hx hc).1
    rw [hk] at this; cases this

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- Filling with keys that agree at the indices below `n` gives the same record. -/
theorem fillRec_congr {w w' : WSt K} {x : Inst} (hix : w'.ix x = w.ix x)
    (hkv : ∀ j, w.ix x = some j → w'.kv j = w.kv j) (r : Rec K) :
    fillRec w' x r = fillRec w x r := by
  unfold fillRec
  rw [hix]
  rcases hj : w.ix x with _ | j
  · rfl
  · simp only [hkv j hj]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The record filled at an index. -/
theorem fillRec_some {w : WSt K} {x : Inst} {j : ℕ} (h : w.ix x = some j) (r : Rec K) :
    fillRec w x r = { r with key := some (w.kv j) } := by
  simp [fillRec, h]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The record of a session without index is not filled. -/
theorem fillRec_none {w : WSt K} {x : Inst} (h : w.ix x = none) (r : Rec K) :
    fillRec w x r = r := by
  simp [fillRec, h]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- Filling keeps the peer, the role and the status. -/
theorem fillRec_partner (w : WSt K) (x y : Inst) (r p : Rec K) :
    Partner x r (fillRec w y p) ↔ Partner x r p := by
  unfold fillRec; split <;> rfl

omit [Fintype K] [Nonempty K] in
/-- **Filling commutes with `newKey`.** -/
theorem fill_newKey {w : WSt K} (hw : WInv w) (sid : SessionId) (pid : PartyId) (k kf : K) :
    fill (wNext w (.inr (.newKey sid pid k)) kf) = newKeyStep (fill w) (sid, pid) k kf := by
  have hkv : ∀ y j, w.ix y = some j →
      (wNext w (.inr (.newKey sid pid k)) kf).kv j = w.kv j := fun y j hj => by
    have := (hw.1 y j hj).1
    simp only [wNext, isNewKey, ite_true]
    rw [Function.update_of_ne (by omega)]
  have hixw : (wNext w (.inr (.newKey sid pid k)) kf).ix =
      newKeyIx w.st w.ix w.steps (sid, pid) := rfl
  obtain ⟨hc1, hn1, hu1⟩ := newKeyStep_fields (fill w) (sid, pid) k kf
  obtain ⟨hc2, hn2, hu2⟩ := newKeyStep_fields w.st (sid, pid) k default
  refine St.ext' ?_ (by rw [hc1]; exact hc2) (by rw [hn1]; exact hn2) (by rw [hu1]; exact hu2)
  funext y
  show Option.map (fillRec (wNext w (.inr (.newKey sid pid k)) kf) y)
      ((newKeyStep w.st (sid, pid) k default).recs y) =
    (newKeyStep (fill w) (sid, pid) k kf).recs y
  rcases hx : w.st.recs (sid, pid) with _ | r
  · have hs : newKeyStep w.st (sid, pid) k default = w.st := by simp [newKeyStep, hx]
    have hf : (fill w).recs (sid, pid) = none := by simp [fill, hx]
    have hs' : newKeyStep (fill w) (sid, pid) k kf = fill w := by simp [newKeyStep, hf]
    rw [hs, hs']
    show _ = Option.map (fillRec w y) (w.st.recs y)
    congr 1; funext r'
    exact fillRec_congr (by rw [hixw]; simp [newKeyIx, hx]) (hkv y) r'
  · have hf : (fill w).recs (sid, pid) = some (fillRec w (sid, pid) r) := by simp [fill, hx]
    by_cases hk : r.key.isNone
    · have hk' : r.key = none := Option.isNone_iff_eq_none.mp hk
      have hix : w.ix (sid, pid) = none := ix_none_of_key_none hw hx hk'
      rw [fillRec_none hix] at hf
      rw [newKeyStep_recs (fill w) _ r hf k kf y, newKeyStep_recs w.st _ r hx k default y]
      by_cases hy : y = (sid, pid)
      · subst hy
        simp only [hk, true_and, ite_true, Option.map_some]
        congr 1
        by_cases hex : Exposed w.st (sid, pid) r
        · have hex' : Exposed (fill w) (sid, pid) r := hex
          have hi' : (wNext w (.inr (.newKey sid pid k)) kf).ix (sid, pid) = none := by
            rw [hixw]; simp [newKeyIx, hx, hex, hix]
          rw [fillRec_none hi']
          simp [newKeyVal, hex, hex']
        · have hex' : ¬ Exposed (fill w) (sid, pid) r := hex
          simp only [hex, hex', ite_false]
          have hpf : (fill w).recs (sid, r.peer) =
              (w.st.recs (sid, r.peer)).map (fillRec w (sid, r.peer)) := rfl
          unfold newKeyVal
          rw [ite_eq_right hex, ite_eq_right hex', hpf]
          rcases hp : w.st.recs (sid, r.peer) with _ | p
          · have hi' : (wNext w (.inr (.newKey sid pid k)) kf).ix (sid, pid) = some w.steps := by
              rw [hixw]; simp [newKeyIx, hx, hk, hex, hp]
            rw [fillRec_some hi']
            simp [wNext, isNewKey]
          · simp only [Option.map_some]
            by_cases hpp : Partner (sid, pid) r p
            · have hpi := (hw.2 _ p hp hpp.2.2).2
              obtain ⟨jp, hjp⟩ := Option.isSome_iff_exists.mp hpi
              have hlt := (hw.1 _ jp hjp).1
              have hi' : (wNext w (.inr (.newKey sid pid k)) kf).ix (sid, pid) = some jp := by
                rw [hixw]; simp [newKeyIx, hx, hk, hex, hp, hpp, hjp]
              rw [fillRec_some hi', ite_eq_left hpp,
                ite_eq_left ((fillRec_partner w _ _ r p).mpr hpp),
                fillRec_some hjp, hkv _ jp hjp]
              simp
            · have hi' : (wNext w (.inr (.newKey sid pid k)) kf).ix (sid, pid) = some w.steps := by
                rw [hixw]; simp [newKeyIx, hx, hk, hex, hp, hpp]
              rw [fillRec_some hi', ite_eq_right hpp,
                ite_eq_right (fun h => hpp ((fillRec_partner w _ _ r p).mp h))]
              simp [wNext, isNewKey]
      · simp only [hy, and_false, ite_false]
        show Option.map _ (w.st.recs y) = Option.map (fillRec w y) (w.st.recs y)
        congr 1; funext r'
        refine fillRec_congr ?_ (hkv y) r'
        rw [hixw]
        simp only [newKeyIx, hx]
        split_ifs <;> simp [Function.update_of_ne hy]
    · have hfk : (fillRec w (sid, pid) r).key.isNone = false := by
        unfold fillRec
        split
        · rfl
        · rcases h : r.key with _ | kk
          · simp [h] at hk
          · simp
      rw [newKeyStep_recs (fill w) _ _ hf k kf y, newKeyStep_recs w.st _ r hx k default y]
      simp only [hfk, hk, Bool.false_eq_true, false_and, ite_false]
      show Option.map _ (w.st.recs y) = Option.map (fillRec w y) (w.st.recs y)
      congr 1; funext r'
      refine fillRec_congr ?_ (hkv y) r'
      rw [hixw]
      simp [newKeyIx, hx, hk]

omit [Fintype K] [Nonempty K] in
/-- **Filling commutes with `newKeyUnlinked`.** -/
theorem fill_newKeyFresh {w : WSt K} (hw : WInv w) (sid : SessionId) (pid : PartyId)
    (k kf : K) :
    fill (wNext w (.inr (.newKeyUnlinked sid pid k)) kf) =
      newKeyFreshStep (fill w) (sid, pid) k kf := by
  have hkv : ∀ y j, w.ix y = some j →
      (wNext w (.inr (.newKeyUnlinked sid pid k)) kf).kv j = w.kv j := fun y j hj => by
    have := (hw.1 y j hj).1
    simp only [wNext, isNewKey, ite_true]
    rw [Function.update_of_ne (by omega)]
  have hixw : (wNext w (.inr (.newKeyUnlinked sid pid k)) kf).ix =
      newKeyFreshIx w.st w.ix w.steps (sid, pid) := rfl
  obtain ⟨hc1, hn1, hu1⟩ := newKeyFreshStep_fields (fill w) (sid, pid) k kf
  obtain ⟨hc2, hn2, hu2⟩ := newKeyFreshStep_fields w.st (sid, pid) k default
  refine St.ext' ?_ (by rw [hc1]; exact hc2) (by rw [hn1]; exact hn2) (by rw [hu1]; exact hu2)
  funext y
  show Option.map (fillRec (wNext w (.inr (.newKeyUnlinked sid pid k)) kf) y)
      ((newKeyFreshStep w.st (sid, pid) k default).recs y) =
    (newKeyFreshStep (fill w) (sid, pid) k kf).recs y
  rcases hx : w.st.recs (sid, pid) with _ | r
  · have hs : newKeyFreshStep w.st (sid, pid) k default = w.st := by
      simp [newKeyFreshStep, hx]
    have hf : (fill w).recs (sid, pid) = none := by simp [fill, hx]
    have hs' : newKeyFreshStep (fill w) (sid, pid) k kf = fill w := by
      simp [newKeyFreshStep, hf]
    rw [hs, hs']
    show _ = Option.map (fillRec w y) (w.st.recs y)
    congr 1; funext r'
    exact fillRec_congr (by rw [hixw]; simp [newKeyFreshIx, hx]) (hkv y) r'
  · have hf : (fill w).recs (sid, pid) = some (fillRec w (sid, pid) r) := by simp [fill, hx]
    by_cases hk : r.key.isNone
    · have hk' : r.key = none := Option.isNone_iff_eq_none.mp hk
      have hix : w.ix (sid, pid) = none := ix_none_of_key_none hw hx hk'
      rw [fillRec_none hix] at hf
      rw [newKeyFreshStep_recs (fill w) _ r hf k kf y,
        newKeyFreshStep_recs w.st _ r hx k default y]
      by_cases hy : y = (sid, pid)
      · subst hy
        simp only [hk, true_and, ite_true, Option.map_some]
        congr 1
        by_cases hex : Exposed w.st (sid, pid) r
        · have hex' : Exposed (fill w) (sid, pid) r := hex
          have hi' : (wNext w (.inr (.newKeyUnlinked sid pid k)) kf).ix (sid, pid) = none := by
            rw [hixw]; simp [newKeyFreshIx, hx, hex, hix]
          rw [fillRec_none hi']
          simp [hex, hex']
        · have hex' : ¬ Exposed (fill w) (sid, pid) r := hex
          have hi' : (wNext w (.inr (.newKeyUnlinked sid pid k)) kf).ix (sid, pid) =
              some w.steps := by
            rw [hixw]; simp [newKeyFreshIx, hx, hk, hex]
          rw [fillRec_some hi']
          simp [hex, hex', wNext, isNewKey]
      · simp only [hy, and_false, ite_false]
        show Option.map _ (w.st.recs y) = Option.map (fillRec w y) (w.st.recs y)
        congr 1; funext r'
        refine fillRec_congr ?_ (hkv y) r'
        rw [hixw]
        simp only [newKeyFreshIx, hx]
        split_ifs <;> simp [Function.update_of_ne hy]
    · have hfk : (fillRec w (sid, pid) r).key.isNone = false := by
        unfold fillRec
        split
        · rfl
        · rcases h : r.key with _ | kk
          · simp [h] at hk
          · simp
      rw [newKeyFreshStep_recs (fill w) _ _ hf k kf y,
        newKeyFreshStep_recs w.st _ r hx k default y]
      simp only [hfk, hk, Bool.false_eq_true, false_and, ite_false]
      show Option.map _ (w.st.recs y) = Option.map (fillRec w y) (w.st.recs y)
      congr 1; funext r'
      refine fillRec_congr ?_ (hkv y) r'
      rw [hixw]
      simp [newKeyFreshIx, hx, hk]

omit [Fintype K] [Nonempty K] in
/-- Filling commutes with `addSession`. -/
theorem fill_addSession {w : WSt K} (hw : WInv w) (sid : SessionId) (pid peer : PartyId)
    (role : Role) (kf : K) :
    fill (wNext w (.inl (.newSession sid pid peer role)) kf) =
      addSession (fill w) (sid, pid) peer role := by
  have hS : ((fill w).recs (sid, pid)).isSome = (w.st.recs (sid, pid)).isSome := by
    simp [fill]
  by_cases h : (w.st.recs (sid, pid)).isSome
  · have h' : ((fill w).recs (sid, pid)).isSome := hS ▸ h
    have e1 : addSession w.st (sid, pid) peer role = w.st := by simp [addSession, h]
    have e2 : addSession (fill w) (sid, pid) peer role = fill w := by simp [addSession, h']
    rw [e2]
    refine St.ext' ?_ (by simp [fill, wNext, stNext, e1]) (by simp [fill, wNext, stNext, e1])
      (by simp [fill, wNext, stNext, e1])
    funext y
    show Option.map (fillRec (wNext w (.inl (.newSession sid pid peer role)) kf) y)
      ((addSession w.st (sid, pid) peer role).recs y) = Option.map (fillRec w y) (w.st.recs y)
    rw [e1]
    rfl
  · have h' : ¬ ((fill w).recs (sid, pid)).isSome := hS ▸ h
    have hix : w.ix (sid, pid) = none := by
      rcases hj : w.ix (sid, pid) with _ | j
      · rfl
      · obtain ⟨_, r, hr, _⟩ := hw.1 _ j hj; simp [hr] at h
    refine St.ext' ?_ (by simp [fill, wNext, stNext, addSession, h])
      (by simp [fill, wNext, stNext, addSession, h])
      (by simp [fill, wNext, stNext, addSession, h])
    funext y
    show Option.map (fillRec w y) ((addSession w.st (sid, pid) peer role).recs y) =
      (addSession (fill w) (sid, pid) peer role).recs y
    rw [addSession_recs, addSession_recs]
    simp only [h, h', Bool.false_eq_true, ite_false]
    by_cases hy : y = (sid, pid)
    · subst hy; simp [fillRec_none hix]
    · simp only [hy, ite_false]; rfl

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The step of `poll`. -/
theorem pollStep_eq (t : St K) :
    pollStep t = ({ t with cursor := if (t.notices[t.cursor]?).isSome then t.cursor + 1
        else t.cursor }, t.notices[t.cursor]?) := by
  unfold pollStep
  split <;> simp_all

omit [Fintype K] [Nonempty K] in
/-- The real views of the first hybrid world are the views of the real stack at the filled
state. -/
theorem chanOut_fill {w : WSt K} (hw : WInv w) (x : Inst) :
    chanOut (wView realV idealV 0 realV realV w x) w.st x =
      chanOut (fun _ k => realV k) (fill w) x := by
  unfold chanOut
  rw [show (fill w).recs x = (w.st.recs x).map (fillRec w x) from rfl]
  rcases hx : w.st.recs x with _ | r
  · rfl
  · simp only [Option.map_some]
    rcases hj : w.ix x with _ | j
    · rw [fillRec_none hj]
      rcases hk : r.key with _ | k
      · rfl
      · simp only [wView, hj]
    · rw [fillRec_some hj]
      obtain ⟨_, r', hr', hc⟩ := hw.1 x j hj
      rw [hx] at hr'; cases hr'
      rw [(hw.2 x r hx hc).1]
      simp only [wView, hj, readOut]
      split_ifs <;> first | omega | (subst_vars; rfl)

/-- **The first hybrid world is the real stack over `F_AKE`**: filling the keys of the indices
is a step map on the invariant. -/
theorem world_zero_stepMap :
    Sys.StepMapOn (world realV idealV 0 (SPComp.sample K) realV realV) (FR realV) WInv fill where
  init_inv := wInv_init
  init_map := by
    refine St.ext' ?_ rfl rfl rfl
    funext y; rfl
  pres w e hw q hq := world_inv realV idealV hw hq
  step w e hw := by
    rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
      (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩)
    · simp only [world, wDraw, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOut,
        SPComp.map]
      rw [fill_addSession hw]
      simp [FR, chanHon, SPComp.map]
    · simp only [world, wDraw, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOut]
      rw [chanOut_fill realV idealV hw]
      simp only [FR, Sys.ofPorts_step_inl, chanHon, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      rfl
    · simp only [world, wDraw, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOut,
        SPComp.map]
      simp only [FR, Sys.ofPorts_step_inr, advSys, SPComp.map, SPComp.pure_bind]
      rfl
    · simp only [world, wDraw, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOut,
        SPComp.map]
      simp only [FR, Sys.ofPorts_step_inr, advSys, SPComp.map, SPComp.pure_bind]
      congr 2
      · refine St.ext' ?_
          (by show (pollStep w.st).1.corrupt = _; rw [pollStep_eq, pollStep_eq]; rfl)
          (by show (pollStep w.st).1.notices = _; rw [pollStep_eq, pollStep_eq]; rfl)
          (by show (pollStep w.st).1.cursor = _; rw [pollStep_eq, pollStep_eq]; rfl)
        funext y
        show Option.map _ ((pollStep w.st).1.recs y) = (pollStep (fill w)).1.recs y
        rw [pollStep_recs, pollStep_recs]; rfl
      · rw [pollStep_eq, pollStep_eq]; rfl
    · simp only [world, wDraw, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOut,
        SPComp.map]
      simp only [FR, Sys.ofPorts_step_inr, advSys, SPComp.map, SPComp.pure_bind]
      rfl
    · simp only [world, wDraw, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOut,
        SPComp.map]
      simp only [FR, Sys.ofPorts_step_inr, advSys, SPComp.map, SPComp.pure_bind, ite_true]
      rfl
    · simp only [world, wDraw, isNewKey, ite_true, ite_self, wOut, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      simp only [FR, Sys.ofPorts_step_inr, advSys, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, fill_newKey hw]
    · simp only [world, wDraw, isNewKey, ite_true, ite_self, wOut, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      simp only [FR, Sys.ofPorts_step_inr, advSys, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, fill_newKeyFresh hw, ite_true]

/-! ## One step of the hybrid argument -/

/-- The hybrid world `i`: the keys below `i` read ideally, the keys from `i` on read really. -/
noncomputable abbrev hyb (i : ℕ) : Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  world realV idealV i (SPComp.sample K) realV realV

/-- The world of the reduction of the step `i`: the first read of the key `i` returns the
challenge `v`, its later reads are ideal. -/
noncomputable abbrev chalWorld (i : ℕ) (v : V) : Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  world realV idealV i (SPComp.sample K) (fun _ => SPComp.pure v) (fun _ => idealV)

/-- **The reduction of the step `i`**: on the challenge view `v`, it runs the environment `Z`
from its heap against the world in which the first read of the key `i` returns `v`, and
applies the distinguisher of `Z`. -/
noncomputable def hopRed (i : ℕ) {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    V → SPComp Bool :=
  fixHeap Z.heap fun v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The views of the step `i + 1` from below. -/
theorem readOut_succ (i : ℕ) (w : WSt K) (j : ℕ) :
    readOut realV idealV i (fun _ => idealV) (fun _ => idealV) w j =
      readOut realV idealV (i + 1) realV realV w j := by
  rcases lt_trichotomy j i with h | rfl | h
  · simp [readOut, h, show j < i + 1 by omega]
  · simp [readOut]
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · subst h'; simp [readOut]
    · simp [readOut, show ¬ j < i by omega, show j ≠ i by omega, show ¬ j < i + 1 by omega,
        show j ≠ i + 1 by omega]

/-- The challenge world at the ideal view is the hybrid world `i + 1`. -/
theorem chalWorld_ideal (i : ℕ) :
    world realV idealV i (SPComp.sample K) (fun _ => idealV) (fun _ => idealV) =
      hyb realV idealV (i + 1) := by
  simp only [hyb, world]
  congr 1
  funext w e
  have hd : wDraw i (SPComp.sample K) w e = wDraw (i + 1) (SPComp.sample K) w e := by
    simp [wDraw]
  rw [hd, wOut_congr realV idealV e fun _ _ j _ _ => readOut_succ realV idealV i w j]

/-- **One step of the hybrid argument.** For views `realV k` and `idealV` that neither touch
the heap nor fail, the distance between the hybrid worlds `i` and `i + 1` at the environment
`Z` is at most the advantage of the reduction `hopRed i Z` between the real game (a uniform key
`k`, then `realV k`) and the ideal game `idealV`, plus the probability that the key `i` is read
twice in the world `i`. -/
theorem hyb_step (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    Env.gap (view (hyb realV idealV i)) (view (hyb realV idealV (i + 1))) Z ≤
      AdvantageA (SPComp.bind (SPComp.sample K) realV) idealV (hopRed realV idealV i Z) +
        prBad (hyb realV idealV i) (reuse i) Z := by
  have hs := CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K
  set Y : K → V → Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) := fun k v =>
    world realV idealV i (SPComp.pure k) (fun _ => SPComp.pure v) realV
  -- the two deferrals, for any flag
  have hmix : ∀ bad : WSt K → Bool,
      SPComp.bind (SPComp.sample K) (fun k => SPComp.bind (realV k) fun v =>
        run (Y k v) bad Z.input) = run (hyb realV idealV i) bad Z.input := fun bad => by
    rw [← run_world_create realV idealV i hs.1 hs.2 realV realV bad Z.input]
    congr 1; funext k
    exact run_world_read realV idealV i (SPComp.pure k) (hR k).1 (hR k).2 realV realV
      (fun kf hkf => by rw [← isOutcome_pure hkf]) bad Z.input
  have hideal : SPComp.bind idealV (fun v => view (chalWorld realV idealV i v) Z.input) =
      view (hyb realV idealV (i + 1)) Z.input := by
    rw [← chalWorld_ideal realV idealV i]
    have h := run_world_read realV idealV i (SPComp.sample K) hI.1 hI.2 (fun _ => idealV)
      (fun _ => idealV) (fun _ _ => rfl) (fun _ => false) Z.input
    simp only [view, SPComp.map] at h ⊢
    rw [← h, SPComp.bind_assoc]
  -- the pair of the key and the view
  set c : SPComp (K × V) := SPComp.bind (SPComp.sample K) fun k =>
    SPComp.map (fun v => (k, v)) (realV k)
  have hc : ∀ {β : Type} (f : K → V → SPComp β),
      SPComp.bind c (fun p => f p.1 p.2) =
        SPComp.bind (SPComp.sample K) fun k => SPComp.bind (realV k) fun v => f k v := by
    intro β f
    simp only [c, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have h1 : prTrue (SPComp.bind (view (hyb realV idealV i) Z.input) Z.dist) Z.heap =
      prTrue (SPComp.bind c fun p => SPComp.bind (view (Y p.1 p.2) Z.input) Z.dist) Z.heap := by
    rw [hc (fun k v => SPComp.bind (view (Y k v) Z.input) Z.dist)]
    simp only [view, ← hmix, SPComp.map, SPComp.bind_assoc]
  have h2 : prBad (hyb realV idealV i) (reuse i) Z =
      prTrue (SPComp.bind c fun p => SPComp.bind (run (Y p.1 p.2) (reuse i) Z.input)
        fun q => SPComp.pure q.2.2) Z.heap := by
    rw [hc (fun k v => SPComp.bind (run (Y k v) (reuse i) Z.input) fun q => SPComp.pure q.2.2)]
    simp only [prBad, ← hmix, SPComp.bind_assoc]
  have h3 : prTrue (SPComp.bind c fun p =>
        SPComp.bind (view (chalWorld realV idealV i p.2) Z.input) Z.dist) Z.heap =
      prTrue (SPComp.bind (SPComp.bind (SPComp.sample K) realV)
        fun v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist) Z.heap := by
    rw [hc (fun _ v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist),
      SPComp.bind_assoc]
  have hreal : SPComp.IsPure (SPComp.bind (SPComp.sample K) realV) :=
    SPComp.bind_isPure hs.1 fun k => (hR k).1
  have h4 := absDiff_prTrue_bind_eq_advantageA hreal hI.1
    (fun v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist) Z.heap
  have h5 : prTrue (SPComp.bind idealV fun v =>
        SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist) Z.heap =
      prTrue (SPComp.bind (view (hyb realV idealV (i + 1)) Z.input) Z.dist) Z.heap := by
    rw [← hideal, SPComp.bind_assoc]
  have hupto := absDiff_prTrue_bind_le_bind c
    (fun p => SPComp.bind (view (Y p.1 p.2) Z.input) Z.dist)
    (fun p => SPComp.bind (view (chalWorld realV idealV i p.2) Z.input) Z.dist)
    (fun p => SPComp.bind (run (Y p.1 p.2) (reuse i) Z.input) fun q => SPComp.pure q.2.2)
    Z.heap fun p h => world_upto_reuse realV idealV i p.1 (fun _ _ => rfl)
      (fun k => (hR k).2) hI.2 (fun _ => SPComp.pure_noFail _) (fun k => (hR k).2)
      (fun _ => hI.2) ζ ⟨Z.input, h, Z.dist⟩
  unfold Env.gap
  rw [h1, h2, ← h5]
  rw [h3] at hupto
  refine le_trans (absDiff_triangle _ (prTrue (SPComp.bind (SPComp.bind (SPComp.sample K) realV)
    fun v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist) Z.heap) _) ?_
  exact (add_le_add hupto (le_of_eq h4)).trans (le_of_eq (add_comm _ _))

/-! ## The secure channel over `F_AKE` -/

/-- The bound of the hybrid argument at an environment `Z` of the functionality: over the
keys `i` below the number of activations of `Z`, the advantage of the reduction `hopRed i Z`
between the real and the ideal secure-messaging games, plus the probability that the key `i`
is read twice. -/
noncomputable def scBound {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range Z.input.rounds,
    (AdvantageA (SPComp.bind (SPComp.sample K) realV) idealV (hopRed realV idealV i Z) +
      prBad (hyb realV idealV i) (reuse i) Z)

/-- **`F_AKE` followed by the ratchet realizes the ideal secure channel.** For views `realV k`
and `idealV` that neither touch the heap nor fail, `FR realV` realizes `F_SC realV idealV`
with the bound `scBound`: a hybrid argument over the keys that the run creates (one per
activation), each step bounded by `hyb_step`. -/
theorem FR_realizes_F_SC (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) :
    Realizes (FR realV) (F_SC realV idealV) (fun _ Z => scBound realV idealV Z) := by
  have h0 : Realizes (FR realV) (hyb realV idealV 0) (fun _ _ => 0) :=
    realizes_symm (world_zero_stepMap realV idealV).realizes
  have hH := Realizes.hybrid_rounds (hyb realV idealV) (F_SC realV idealV)
    (fun i _ Z => AdvantageA (SPComp.bind (SPComp.sample K) realV) idealV
      (hopRed realV idealV i Z) + prBad (hyb realV idealV i) (reuse i) Z)
    (fun _ _ => 0) (fun i _ Z => hyb_step realV idealV hR hI i Z) fun _ Z => by
      have h := world_end realV idealV Z.input.rounds (fun k => (hR k).2) hI.2 _ Z
      dsimp only at h
      rwa [world_end_prBad realV idealV _ Z le_rfl] at h
  intro ζ Z
  have := (h0.trans hH) ζ Z
  simpa [scBound] using this

end Steps

/-! ## The simulator -/

section Sim

/-- The view of the honest port of the secure channel: equal events, any two outputs. -/
def scHonView {V : Type} : PubView HEv (HOut V) where
  ev := Eq
  out _ _ := True

/-- The outer view of the Signal stack: the view of the honest port and equal adversary
outputs. -/
abbrev scOuterView {S W K V : Type} : PubView (OEv W) (HOut V ⊕ ROut S W K) :=
  scHonView.sum eqView

/-- The view of `F_SC`. -/
abbrev scSubView {K V : Type} : PubView (FEv K) (HOut V ⊕ AOut) := scHonView.sum eqView

variable {S W K V : Type}

/-- A decision of the X3DH simulator as a decision over `F_SC`: a call passes, an adversary
output passes, and an honest output (which the X3DH simulator does not produce) is an
acknowledgement. -/
def decV : Dec S W K → FEv K ⊕ (HOut V ⊕ ROut S W K)
  | .inl ev => .inl ev
  | .inr (.inl _) => .inr (.inl .ok)
  | .inr (.inr r) => .inr (.inr r)

/-- The answer of the simulator to an answer of `F_SC`: in the phase `fwd`, the answer on the
honest port, and an acknowledgement for an answer on the adversary port; otherwise the stored
output. -/
def simOutV : Phase S W K → HOut V ⊕ AOut → HOut V ⊕ ROut S W K
  | .fwd, .inl o => .inl o
  | .fwd, .inr _ => .inr .ack
  | .out r, _ => .inr r

/-- **A multi-call simulator over `F_SC`** wrapping a multi-call simulator `π` over `F_AKE`:
its `start` step is that of `π` with the decision read over `F_SC` (`decV`), and an answer of
`F_SC` is answered by `simOutV` at the phase of the state. -/
noncomputable def simSCOver
    (π : MultiHybrid (SimSt S W K) (OEv W) (OOut S W K) (FEv K) (FOut K)) :
    MultiHybrid (SimSt S W K) (OEv W) (HOut V ⊕ ROut S W K) (FEv K) (HOut V ⊕ AOut) where
  init := π.init
  fuel := 0
  start s e := SPComp.map (fun q => (q.1, decV q.2)) (π.start s e)
  resume s o := SPComp.pure ((s.1, s.2.1, .fwd), .inr (simOutV s.2.2 o))
  finish s o := SPComp.pure ((s.1, s.2.1, .fwd), simOutV s.2.2 o)
  start_noFail s e := map_noFail _ (π.start_noFail s e)
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

variable [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  (G : DHGroup S W)

/-- **The simulator of the Signal stack**: the X3DH simulator `simProt G` over `F_SC`. It keeps
the copy of the real state of `simProt G`, draws the long-term and session secrets itself,
forwards the honest events to `F_SC`, answers `poll`, `pub`, `ephPub` and `kdf` on its copy,
corrupts in `F_SC` under the static rule of X3DH, and delivers keys as `simProt G` does: the
key-derivation value to an exposed session, `newKey` or `newKeyUnlinked` with a placeholder
key otherwise. The honest outputs of `F_SC` (the views of the channel) pass unchanged. -/
noncomputable def simSC :
    MultiHybrid (SimSt S W K) (OEv W) (HOut V ⊕ ROut S W K) (FEv K) (HOut V ⊕ AOut) :=
  simSCOver (simProt G)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- Every decision over `F_SC` is related to itself. -/
theorem decV_rel (d : FEv K ⊕ (HOut V ⊕ ROut S W K)) :
    PubView.StepRel (scOuterView (S := S) (W := W) (K := K) (V := V))
      (scSubView (K := K) (V := V)) d d := by
  rcases d with (h | a) | (o | o)
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The answers of the simulator to related answers of `F_SC` are related. -/
theorem simOutV_rel (ph : Phase S W K) {o o' : HOut V ⊕ AOut}
    (h : (scSubView (K := K)).out o o') :
    (scOuterView (S := S) (W := W) (K := K)).out (simOutV ph o) (simOutV ph o') := by
  cases ph with
  | fwd =>
    cases h with
    | inl _ => exact Sum.LiftRel.inl trivial
    | inr _ => exact Sum.LiftRel.inr rfl
  | out r => exact Sum.LiftRel.inr rfl

/-- **Opacity of the simulator**: its state and its decisions depend on its events and not on
the honest answers of `F_SC`. -/
theorem simSC_opaque :
    (simSC (V := V) G).Opaque (scOuterView (K := K)) scSubView := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    have he' : e = e' := by
      cases he with
      | inl h => exact congrArg Sum.inl h
      | inr h => exact congrArg Sum.inr h
    subst he'
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, decV_rel _⟩)
      (rHoare_refl _)
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, simOutV_rel _ ho⟩
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, simOutV_rel _ ho⟩

/-- **The simulator of the Signal stack** as a bundled opaque simulator over `F_SC`. -/
noncomputable def scSim : Simulator (OEv W) (HOut V ⊕ ROut S W K) (FEv K) (HOut V ⊕ AOut)
    scOuterView scSubView :=
  Simulator.ofMultiHybrid (simSC G) (simSC_opaque G)

/-- A decision that is not an honest output. -/
def NoHon (d : Dec S W K) : Prop := ∀ h, d ≠ .inr (.inl h)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- A point mass at a decision that is not an honest output. -/
theorem noHon_pure {a : SimSt S W K} {d : Dec S W K} (hd : NoHon d)
    {q : SimSt S W K × Dec S W K} (hq : IsOutcome (SPComp.pure (a, d)) q) : NoHon q.2 := by
  rw [← isOutcome_pure hq]; exact hd

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The outcomes of a map whose values are not honest outputs. -/
theorem noHon_map {α : Type} {c : SPComp α} {f : α → SimSt S W K × Dec S W K}
    (hf : ∀ a, NoHon (f a).2) {q : SimSt S W K × Dec S W K}
    (hq : IsOutcome (SPComp.map f c) q) : NoHon q.2 := by
  obtain ⟨a, _, rfl⟩ := exists_of_isOutcome_map hq; exact hf a

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The outcomes of a bind whose continuations give no honest output. -/
theorem noHon_bind {α : Type} {c : SPComp α} {f : α → SPComp (SimSt S W K × Dec S W K)}
    (hf : ∀ a q, IsOutcome (f a) q → NoHon q.2) {q : SimSt S W K × Dec S W K}
    (hq : IsOutcome (SPComp.bind c f) q) : NoHon q.2 := by
  obtain ⟨a, _, ha⟩ := isOutcome_bind hq; exact hf a q ha

omit [Field S] [Fintype S] in
/-- The delivery of a key calls `F_SC`. -/
theorem deliver_noHon (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) {q : SimSt S W K × Dec S W K} (hq : IsOutcome (deliver rs inp x r ip) q) :
    NoHon q.2 := by
  unfold deliver at hq
  split at hq
  · exact noHon_map (fun _ _ h => by simp at h) hq
  · exact noHon_pure (fun _ h => by simp at h) hq

/-- **The X3DH simulator outputs nothing on the honest port by itself**: every honest output of
the simulated world is an answer of the functionality. -/
theorem simStart_noHon (s : SimSt S W K) (e : OEv W) {q : SimSt S W K × Dec S W K}
    (hq : IsOutcome (simStart G s e) q) : NoHon q.2 := by
  have hp : ∀ (a : SimSt S W K) (r : ROut S W K) {q : SimSt S W K × Dec S W K},
      IsOutcome (SPComp.pure (a, (.inr (.inr r) : Dec S W K))) q → NoHon q.2 :=
    fun _ _ _ hq => noHon_pure (fun _ h => by simp at h) hq
  have hl : ∀ (a : SimSt S W K) (ev : FEv K) {q : SimSt S W K × Dec S W K},
      IsOutcome (SPComp.pure (a, (.inl ev : Dec S W K))) q → NoHon q.2 :=
    fun _ _ _ hq => noHon_pure (fun _ h => by simp at h) hq
  have hd : ∀ {α β : Type} (c : SPComp α) (c' : α → SPComp β)
      (f : α → β → SPComp (SimSt S W K × Dec S W K)),
      (∀ a b q, IsOutcome (f a b) q → NoHon q.2) → ∀ q,
      IsOutcome (SPComp.bind c fun a => SPComp.bind (c' a) (f a)) q → NoHon q.2 :=
    fun c c' f hf q hq => noHon_bind (fun a q' hq' => noHon_bind (hf a) hq') hq
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · simp only [simStart] at hq
    split at hq
    · exact noHon_map (fun _ _ h => by simp at h) hq
    · exact hl _ _ hq
  · exact hl _ _ hq
  · exact hp _ _ hq
  · exact hp _ _ hq
  · exact noHon_map (fun _ _ h => by simp at h) hq
  · exact hp _ _ hq
  · simp only [simStart, simCorrupt] at hq
    split at hq
    · exact hp _ _ hq
    · exact noHon_map (fun _ _ h => by simp at h) hq
  · simp only [simStart, simComplete] at hq
    repeat' split at hq
    all_goals first
      | exact hp _ _ hq
      | exact hd _ _ _ (fun _ _ _ h => deliver_noHon _ _ _ _ _ h) q hq
  · simp only [simStart, simSend] at hq
    repeat' split at hq
    all_goals first
      | exact hp _ _ hq
      | exact hd _ _ _ (fun _ _ _ h => deliver_noHon _ _ _ _ _ h) q hq
  · exact noHon_map (fun _ _ h => by simp at h) hq

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The ratchet layer on an answer of the X3DH simulator to an adversary answer of `F_AKE`. -/
theorem smLayer_simOut_inr (realV : K → SPComp V) (ph : Phase S W K) (a : AOut) :
    (smLayer (S := S) (W := W) realV).step () (simOut ph (.inr a)) =
      SPComp.pure ((), simOutV ph (.inr a)) := by
  cases ph <;> rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The ratchet layer on the key of a session is the channel output of the real stack. -/
theorem smLayer_key (realV : K → SPComp V) (t : St K) (x : Inst) :
    (smLayer (S := S) (W := W) realV).step () (.inl (.key (keyOf t x))) =
      SPComp.map (fun o => ((), .inl o)) (chanOut (fun _ k => realV k) t x) := by
  unfold chanOut keyOf
  rcases hx : t.recs x with _ | r
  · simp [smLayer, SPComp.map]
  · rcases hk : r.key with _ | k
    · simp [smLayer, hk, SPComp.map]
    · simp [smLayer, hk, SPComp.map, SPComp.bind_assoc]

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The channel output of views that neither touch the heap nor fail neither touches the heap
nor fails. -/
theorem chanOut_pureNF {f : Rec K → K → SPComp V}
    (hf : ∀ r k, SPComp.IsPure (f r k) ∧ SPComp.NoFail (f r k)) (t : St K) (x : Inst) :
    SPComp.IsPure (chanOut f t x) ∧ SPComp.NoFail (chanOut f t x) := by
  unfold chanOut
  split
  · split
    · exact ((CatCrypt.Crypto.PAKE.CPaceSquare.PureNF.map _ (hf _ _)))
    · exact CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _
  · exact CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _

/-- **The stack over `F_AKE` behind the X3DH simulator is the simulator `simSC` over the real
stack `FR`** (composition plumbing): the cascade of `x3dhIdeal G` and the ratchet layer and
`simSC G` running with `FR realV` have the same steps, up to the unit state of the layer. -/
theorem stack_ideal_stepMap (realV : K → SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k)) :
    Sys.StepMapOn ((simSC (V := V) G).withSub (FR realV)) ((x3dhIdeal G).seq (smLayer realV))
      (fun _ => True) (fun p => (p, ())) where
  init_inv := trivial
  init_map := rfl
  pres _ _ _ _ _ := trivial
  step p e _ := by
    rcases p with ⟨s, t⟩
    rw [Sys.seq_step]
    simp only [x3dhIdeal, x3dhSim, Simulator.ofMultiHybrid, MultiHybrid.withSub, simSC, simSCOver,
      simProt, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    refine bind_congr_isOutcome fun r hr => ?_
    have hn := simStart_noHon G s e hr
    rcases r with ⟨⟨a, b, ph⟩, (ev | (h | ro))⟩
    · simp only [MultiHybrid.drive, decV, SPComp.bind_assoc, SPComp.pure_bind]
      rcases ev with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | ev
      · cases ph <;> simp [FR, chanHon, F_AKE, honSys, honStep, smLayer, simOut, simOutV,
          SPComp.map, SPComp.pure_bind]
      · have hc := chanOut_pureNF (fun _ k => hR k) t (sid, pid)
        cases ph with
        | fwd =>
          simp only [FR, F_AKE, Sys.ofPorts_step_inl, chanHon, honSys, honStep, SPComp.map,
            SPComp.bind_assoc, SPComp.pure_bind, simOut, simOutV]
          have hk := smLayer_key (S := S) (W := W) realV t (sid, pid)
          simp only [SPComp.map] at hk
          rw [hk]
          simp only [SPComp.bind_assoc, SPComp.pure_bind]
        | out r =>
          simp only [FR, F_AKE, Sys.ofPorts_step_inl, chanHon, honSys, honStep, SPComp.map,
            SPComp.bind_assoc, SPComp.pure_bind, simOut, simOutV, smLayer]
          exact bind_const_of_isPure hc.1 hc.2 _
      · simp only [FR, F_AKE, Sys.ofPorts_step_inr, SPComp.map, SPComp.bind_assoc,
          SPComp.pure_bind]
        congr 1; funext q
        rw [smLayer_simOut_inr]
        simp only [SPComp.pure_bind]
    · exact (hn h rfl).elim
    · simp [MultiHybrid.drive, decV, smLayer, SPComp.map, SPComp.pure_bind]

end Sim

/-! ## The Signal stack realizes the ideal secure channel -/

section Stack

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

omit [Inhabited K] in
/-- `FR` is idle at the idle event of the adversary. -/
theorem FR_idleAt {V : Type} (realV : K → SPComp V) :
    MultiHybrid.IdleAt (FR realV) (.inr .idle) (.inr .ack) := fun t => by
  simp [FR, advSys, SPComp.map]

omit [Fintype K] [Nonempty K] in
/-- `F_SC` is idle at the idle event of the adversary. -/
theorem F_SC_idleAt {V : Type} (realV : K → SPComp V) (idealV : SPComp V) :
    MultiHybrid.IdleAt (F_SC realV idealV) (.inr .idle) (.inr .ack) := fun t => by
  simp [F_SC, advSys, SPComp.map]

/-- **The simulator over `F_AKE` with the ratchet realizes the simulator over `F_SC`**: for
views that neither touch the heap nor fail, `simSC G` over `FR realV` realizes `simSC G` over
`F_SC realV idealV` with `scBound` at the environment reduced through the simulator. -/
theorem simSC_realizes {V : Type} (realV : K → SPComp V) (idealV : SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) :
    Realizes ((simSC (V := V) G).withSub (FR realV)) ((simSC G).withSub (F_SC realV idealV))
      (fun _ Z => scBound realV idealV ((simSC G).reduceEnv (.inr .idle) Z)) := by
  intro ζ Z
  have h := MultiHybrid.adv_withSub (simSC (V := V) G) (.inr .idle) (.inr .ack) (.inr .ack)
    (FR realV) (F_SC realV idealV) (FR_idleAt realV) (F_SC_idleAt realV idealV) Z
  unfold adv at h
  change Env.gap _ _ Z ≤ _
  rw [h]
  exact FR_realizes_F_SC realV idealV hR hI _ _

variable {Sc Msg Key Sa M Ct : Type} [SampleableType M] [SampleableType Ct] [Fintype Key]
  [Nonempty Key] [Fintype Sa] [Nonempty Sa]

omit [SampleableType M] [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- The ideal secure-messaging game of a CKA of `CKAPureNF` neither touches the heap nor
fails. -/
theorem sm_ideal_pureNF {C : CKADef Sc Msg Key} (hC : CKAPureNF C)
    (msgs : List (List (M × M))) :
    SPComp.IsPure (sm_ideal (Ct := Ct) C msgs) ∧ SPComp.NoFail (sm_ideal (Ct := Ct) C msgs) := by
  unfold sm_ideal ckaPub
  exact (hC.1.bind fun _ => (ckaRun_pureNF hC _ _ _).bind fun _ =>
    CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _).bind fun _ =>
      (CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample _).bind fun _ =>
        CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _

/-- The bound of the Signal stack at an environment `Z` of the stack: the gap Diffie–Hellman
bound of the X3DH square at the environment reduced through the ratchet layer, and, at the
environment `Z'` reduced through the simulator, over the keys `i` below the number of
activations of `Z'`, the secure-messaging advantage of the reduction `hopRed i Z'` and the
probability that the key `i` is read twice. -/
noncomputable def signalBound (P : Finset PartyId) (C : CKADef Sc Msg Key)
    (R : PRGDef (K × Key) (K × Sa)) (Gp : PRGDef Sa (M × Sa)) (D : AEADDef M Ct)
    (msgs : List (List (M × M))) (hC : CKAPureNF C) (ζ : Type)
    (Z : Env (Strat ζ (OEv W) (HOut (SMView Msg Ct) ⊕ ROut S W K)) ζ) : ℝ≥0∞ :=
  gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
      ((Hybrid.seqCtxR (E := OEv W) (smLayer (smRealAt C R Gp D msgs))
        (smLayer_noFail fun k => (smRealAt_pureNF hC R Gp D msgs k).2)).reduceEnv Z)) +
    ∑ i ∈ Finset.range ((simSC (V := SMView Msg Ct) G).reduceEnv (.inr .idle) Z).input.rounds,
      (SM_Advantage C R Gp D msgs (hopRed (smRealAt C R Gp D msgs) (sm_ideal C msgs) i
          ((simSC G).reduceEnv (.inr .idle) Z)) +
        prBad (hyb (smRealAt C R Gp D msgs) (sm_ideal C msgs) i) (reuse i)
          ((simSC G).reduceEnv (.inr .idle) Z))

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- **The Signal stack realizes the ideal secure channel** (genuine UC).

*Ideal functionality.* `F_SC (smRealAt C R Gp D msgs) (sm_ideal C msgs)`: the multi-session
secure channel built from the authenticated key exchange `F_AKE` with unlinked delivery. Its
adversary port is the adversary port of `F_AKE` (notices, adaptive corruption, `newKey`,
`newKeyUnlinked`), except that a session that completes without exposure stores no key. Its
honest port opens sessions and, on `getKey`, outputs the secure-messaging view of the session:
for a completed session the ideal view `sm_ideal C msgs` (the public CKA transcript and uniform
ciphertexts), for a session exposed by corruption the real view `smRealAt C R Gp D msgs k` under
the adversary key `k`, and nothing for a session without a key.

*Real world.* The real X3DH protocol `x3dhReal G` followed by the double ratchet layer
`smLayer (smRealAt C R Gp D msgs)`, which keys the ratchet with the session key of every
`getKey` answer.

*Simulator.* `scSim G`, the X3DH simulator over `F_SC`: it keeps a copy of the real state,
draws all long-term and session secrets, forwards the honest events, answers `poll`, `pub`,
`ephPub` and `kdf` on its copy, refuses or forwards `corrupt` under the static rule of X3DH, and
on `complete` and `send` computes the key-derivation input of the session and calls `newKey` with
the key-derivation value for an exposed session and `newKey` or `newKeyUnlinked` with a
placeholder key otherwise. It never reads an honest answer of `F_SC`.

*Bound.* For a CKA that neither touches the heap nor fails, for every finite set of parties `P`
and every environment `Z`, the distance is at most `signalBound`: the gap Diffie–Hellman bound
of the X3DH square, and a sum over the keys of the run of the secure-messaging advantages of the
explicit reductions `hopRed` and of the probability that a key is read twice. The last term is
the reuse of one root key by two ratchet runs, which `SM_Advantage` does not cover; it is `0`
for environments that read each session key (with its partner) at most once. No real-or-random
term of the key appears. -/
theorem signal_stack_realizes_FSC (P : Finset PartyId) {C : CKADef Sc Msg Key}
    (hC : CKAPureNF C) (R : PRGDef (K × Key) (K × Sa)) (Gp : PRGDef Sa (M × Sa))
    (D : AEADDef M Ct) (msgs : List (List (M × M))) :
    RealizesSim ((x3dhReal (K := K) G).seq (smLayer (smRealAt C R Gp D msgs)))
      (F_SC (smRealAt C R Gp D msgs) (sm_ideal C msgs)) (scSim G)
      (signalBound G P C R Gp D msgs hC) := by
  have hR : ∀ k, SPComp.IsPure (smRealAt C R Gp D msgs k) ∧
      SPComp.NoFail (smRealAt C R Gp D msgs k) := fun k => smRealAt_pureNF hC R Gp D msgs k
  have hA := signal_stack_realizes G P (smRealAt C R Gp D msgs) fun k => (hR k).2
  have hB := realizes_symm (stack_ideal_stepMap G (smRealAt C R Gp D msgs) hR).realizes
  have hC' := simSC_realizes G (smRealAt C R Gp D msgs) (sm_ideal C msgs) hR
    (sm_ideal_pureNF hC msgs)
  intro ζ Z
  have h := ((hA.trans hB).trans hC') ζ Z
  refine h.trans (le_of_eq ?_)
  simp only [signalBound, scBound, add_zero, SM_Advantage, sm_real_eq_bind_smRealAt]

end Stack

/-! ## Time certificates -/

section Time

variable {K V : Type} [Fintype K] [Nonempty K] [Inhabited K]
  (realV : K → SPComp V) (idealV : SPComp V)

/-- **The tree of the reduction of the step `i`**: the environment reduction `sysEnvTree` of
`UCConcreteTimed` over the family of challenge worlds, with trees `next`, `obs`, `dist` of the
strategy and the distinguisher of `Z` and a tree `step` of the step of the challenge world. -/
noncomputable def hopRed.tree (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) (next : ζ → SPTree (ζ × (HEv ⊕ AEv K)))
    (step : V → WSt K → HEv ⊕ AEv K → SPTree (WSt K × (HOut V ⊕ AOut)))
    (obs : ζ → HOut V ⊕ AOut → SPTree ζ) (dist : ζ → SPTree Bool) (v : V) : SPTree Bool :=
  sysEnvTree (chalWorld realV idealV i) Z next step obs dist v

/-- The tree of the reduction of the step `i` compiles to `hopRed i Z`. -/
theorem hopRed.compile_tree (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ)
    {next : ζ → SPTree (ζ × (HEv ⊕ AEv K))}
    {step : V → WSt K → HEv ⊕ AEv K → SPTree (WSt K × (HOut V ⊕ AOut))}
    {obs : ζ → HOut V ⊕ AOut → SPTree ζ} {dist : ζ → SPTree Bool}
    (hn : ∀ z, (next z).compile = Z.input.next z)
    (hs : ∀ v t e, (step v t e).compile = (chalWorld realV idealV i v).step t e)
    (ho : ∀ z o, (obs z o).compile = Z.input.obs z o) (hd : ∀ z, (dist z).compile = Z.dist z)
    (v : V) :
    (hopRed.tree realV idealV i Z next step obs dist v).compile = hopRed realV idealV i Z v :=
  sysEnvTree_compile _ Z hn hs ho hd v

derive_timed hopRed.tree

/-- **Time of the reduction of the step `i`.** On the challenge `v`, for a costed strategy of
`Z` and a costed step of the challenge world over the same interface, from initial states of
their invariants, and a distinguisher of time at most `tD` on the final states, the costed form
of the tree of `hopRed i Z` takes at most the reset to the heap of `Z`, the time of the strategy
over its `q = Z.input.rounds` activations, `tD`, the time of `q` steps of the challenge world,
`9` per activation and `10`: the time of the environment plus the steps of the world. -/
theorem hopRed.timeBound_timed (realVCost : K → ℕ) (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ)
    {next : ζ → SPTree.Timed (ζ × (HEv ⊕ AEv K))} {nextCost : ζ → ℕ}
    {step : V → WSt K → HEv ⊕ AEv K → SPTree.Timed (WSt K × (HOut V ⊕ AOut))}
    {stepCost : V → WSt K → HEv ⊕ AEv K → ℕ}
    {obs : ζ → HOut V ⊕ AOut → SPTree.Timed ζ} {obsCost : ζ → HOut V ⊕ AOut → ℕ}
    {dist : ζ → SPTree.Timed Bool} {distCost : ζ → ℕ} (v : V) {InvZ MidZ : ℕ → ζ → Prop}
    {InvS : ℕ → WSt K → Prop} {Ev : ℕ → HEv ⊕ AEv K → Prop} {Out : ℕ → HOut V ⊕ AOut → Prop}
    {tN tS tO : ℕ → ℕ} {tD : ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : SysRunBound (step v) (stepCost v) InvS Ev Out tS)
    (hz : InvZ 0 Z.input.init) (ht : InvS 0 (chalWorld realV idealV i v).init)
    (hd : ∀ z, InvZ Z.input.rounds z → SPTree.Timed.stepTime (distCost z, dist z) ≤ tD) :
    SPTree.Timed.stepTime (hopRed.tree.timed realV realVCost idealV i Z next nextCost step
        stepCost obs obsCost dist distCost v) ≤
      Z.heap.data.keys.card + (∑ j ∈ Finset.range Z.input.rounds, (tN j + tO j)) + tD +
        (∑ j ∈ Finset.range Z.input.rounds, tS j) + 9 * Z.input.rounds + 10 := by
  have h := sysEnvTree.timeBound_timed (chalWorld realV idealV i) (fun _ => 3) Z v hZ hS hz ht hd
  simp only [hopRed.tree.timed, SPTree.Timed.stepTime_delay]
  omega

end Time

end CatCrypt.Crypto.Messaging.SignalStackUC

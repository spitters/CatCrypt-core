/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStack
public import CatCryptCore.Crypto.UCDeferred

/-!
# The Signal stack realizes an ideal secure channel

DOCSTRING
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStackUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.UCCoupling
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
    (F_SC realV idealV).step t e = SPComp.map (fun o => (stNext t e, o)) (scOut realV idealV t e) := by
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

end Steps

end CatCrypt.Crypto.Messaging.SignalStackUC

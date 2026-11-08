/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareJointEager
public import CatCryptCore.Crypto.AKE.X3DHSquareJointHop

/-!
# The forgery event of the joint-key model of X3DH

In the joint-key model of X3DH the world with simulated signatures `simSignO` and the filtered
world `filtJO` differ only at an injection that `simSignO` accepts and `filtJO` refuses: an
injection `inject sid pid spk σ` at a session whose peer `q` is honest, whose signature verifies
under the identity key `IK_q` on the random-oracle value at the point `(σ.1, spk)`, with a prekey
`spk` that the layer did not sign for `q` (`ForgeJ`).

The second hop of the joint-key model bounds the distance of the two worlds by the probability
of `ForgeJ` in `simSignO` (`joint_upto_forgery`). That probability equals the probability that
the flag environment `flagEnv B` outputs `true` against the filtered world
(`forgeJ_eq_flagEnv`). The flag environment runs `B`, records the peers of the sessions and the
parties whose signatures `B` requested, and before each injection at a session with a peer `q`
reads `IK_q` and `SPK_q` by `pub q` and the random-oracle value by `sigHash q (σ.1, spk)`; it
outputs `true` at the first forbidden injection and passes the others on.

## Main definitions

* `ForgeJ` — the forbidden injection, a transition of the worlds
* `InvJ` — the layer state matches the real state
* `FlSt`, `flNext`, `forgeObs`, `flagAsk`, `flagEnv` — the flag environment

## Main results

* `joint_upto_forgery` — hop 2: the world with simulated signatures and the filtered world are
  at distance at most the probability of `ForgeJ`
* `forgeJ_eq_flagEnv` — the probability of `ForgeJ` is the probability that the flag environment
  outputs `true` in the filtered world
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.OracleForking
open CatCrypt.Examples
open CatCrypt.Crypto.AKE.X3DHSquareSigned (completeSig layO completeSig_eq ltAt_support
  ltAt_of_some realO_support keyed_recs_peer realStep_pub)
open scoped ENNReal

/-! ## The forgery event and the invariant -/

section Defs

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] {K : Type}

/-- **A forbidden injection**: an injection at a session whose peer is `q`, whose signature
verifies under the identity key of `q` on the random-oracle value of `q` at the point
`(σ.1, spk)` after the step, with a prekey `spk` other than the signed prekey of `q` or before
`q` signed. -/
def ForgeJ (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P)
    (x : JOut P K × (JSt P × RSt P.Wit P.Stmt K)) : Prop :=
  ∃ sid pid spk σ q v c, e = .inr (.inr (.inject sid pid spk σ)) ∧
    t.1.peers (sid, pid) = some q ∧ x.2.2.lt q = some v ∧
    (x.2.1.tabs q).1.lookup (σ.1, spk) = some c ∧ P.verify (A.pub v.1) σ.1 c σ.2 = true ∧
    ¬ ((t.1.sigs q).isSome = true ∧ spk = A.pub v.2)

/-- **The layer state matches the real state**: the peer of each session is the peer of its
record, and a party that signed has drawn long-term secrets whose public parts are its identity
key and signed prekey. -/
def InvJ (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K) : Prop :=
  (∀ x, t.1.peers x = (t.2.st.recs x).map Rec.peer) ∧
    ∀ q c, t.1.sigs q = some c → ∃ v, t.2.lt q = some v ∧ c.1 = A.pub v.1 ∧ c.2.1 = A.pub v.2

/-- The state of the flag environment: the peer of each session and the parties whose
signatures were requested. -/
structure FlSt where
  /-- The peer of a session. -/
  peers : Inst → Option PartyId
  /-- Whether the signature of a party was requested. -/
  signed : PartyId → Bool

/-- The initial state of the flag environment. -/
def FlSt.init : FlSt := ⟨fun _ => none, fun _ => false⟩

/-- The state of the flag environment after the event `e`: a new session notes its peer, and a
signature request notes its party. -/
def flNext (f : FlSt) : JEv P → FlSt
  | .inl (.newSession sid pid peer _) =>
    if (f.peers (sid, pid)).isSome then f
    else { f with peers := Function.update f.peers (sid, pid) (some peer) }
  | .inr (.inr (.sigPub q)) => { f with signed := Function.update f.signed q true }
  | _ => f

/-- **The test of the flag environment** at an injection of `spk` with `σ` at a session whose
peer is `q`, on the answers to `pub q` and to `sigHash q (σ.1, spk)`: the signature verifies
under the identity key, and the prekey is not the signed prekey of a party that signed. -/
def forgeObs (f : FlSt) (q : PartyId) (spk : P.Stmt) (σ : P.Com × P.Resp) :
    JOut P K → JOut P K → Bool
  | .inr (.inl (.pub ik spk')), .inr (.inr (.hash c)) =>
    P.verify ik σ.1 c σ.2 && !(f.signed q && spk == spk')
  | _, _ => false

/-- **The queries of the flag environment for an event**: the event itself, answered by
`some`; at an injection at a session with a peer `q`, first `pub q` and `sigHash q (σ.1, spk)`,
and `none` when the test `forgeObs` holds. -/
noncomputable def flagAsk (f : FlSt) : JEv P → OracleAdv (JEv P) (JOut P K) (Option (JOut P K))
  | .inr (.inr (.inject sid pid spk σ)) =>
    match f.peers (sid, pid) with
    | none => .query (.inr (.inr (.inject sid pid spk σ))) fun o => .ret (some o)
    | some q => .query (.inr (.inl (.pub q))) fun o₁ =>
      .query (.inr (.inr (.sigHash q (σ.1, spk)))) fun o₂ =>
        if forgeObs P f q spk σ o₁ o₂ then .ret none
        else .query (.inr (.inr (.inject sid pid spk σ))) fun o => .ret (some o)
  | e => .query e fun o => .ret (some o)

/-- **The flag environment** of the oracle adversary `B`: it runs `B`, asks the queries of
`flagAsk` for each event of `B`, outputs `true` at the first forbidden injection, and `false`
when `B` returns. -/
noncomputable def flagEnv :
    OracleAdv (JEv P) (JOut P K) Bool → FlSt → OracleAdv (JEv P) (JOut P K) Bool
  | .ret _, _ => .ret false
  | .rand μ k, f => .rand μ fun b => flagEnv (k b) f
  | .query e k, f => (flagAsk P (K := K) f e).bind fun
      | none => .ret true
      | some o => flagEnv (k o) (flNext P f e)

/-- The flag environment and the layer state agree on the peers and the signed parties. -/
def RelF (f : FlSt) (t : JSt P × RSt P.Wit P.Stmt K) : Prop :=
  f.peers = t.1.peers ∧ ∀ q, f.signed q = (t.1.sigs q).isSome

end Defs

/-! ## The random oracle of a party at a point -/

section Hash

/-- An entry appended at a point without an entry is the entry found at that point. -/
theorem lookupIn_append_self {κ γ : Type} [DecidableEq κ] (l : List (κ × γ)) (k : κ) (e : γ)
    (h : lookupIn l k = none) : lookupIn (l ++ [(k, e)]) k = some e := by
  unfold lookupIn findKey at h ⊢
  rw [List.findIdx?_append]
  cases hf : l.findIdx? (fun p => decide (p.1 = k)) with
  | some i =>
    obtain ⟨hi, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp [hf, List.getElem?_eq_getElem hi] at h
  | none => simp [List.findIdx?_cons]

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt]

/-- **A hash query of a party by `hashStep`** answers a value `e` that the table of the party
holds at the point after the query, and changes only that table. -/
theorem hashAt_support (H : FSt P → (fsOf P).Key → Step (fsOf P).Answer (FSt P) P.Ch)
    (hH : ∀ s k, H s k = hashStep s.1 s.2 k) (l : JSt P) (q : PartyId) (k : (fsOf P).Key) :
    ∀ r ∈ (hashAt P H l q k).support, ∃ e, r.1 = .inl e ∧ (r.2.tabs q).1.lookup k = some e ∧
      r.2 = { l with tabs := Function.update l.tabs q (r.2.tabs q) } := by
  intro r hr
  simp only [hashAt, PMF.support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  simp only [toOracle, hH] at hz
  unfold hashStep at hz
  split at hz
  · rename_i e he
    simp only [Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨e, rfl, by simpa using he, by simp⟩
  · rename_i he
    simp only [Step.toPMF, PMF.support_map, Set.mem_image] at hz
    obtain ⟨e, -, rfl⟩ := hz
    refine ⟨e, rfl, ?_, by simp⟩
    simp only [Protocol.Tables.lookup, Option.or_eq_none_iff] at he
    simp [Protocol.Tables.lookup, he.1, lookupIn_append_self _ _ _ he.2]

/-- A hash query of a party by `hashStep` at a point where its table holds `e` answers `e` and
keeps the state. -/
theorem hashAt_of_lookup (H : FSt P → (fsOf P).Key → Step (fsOf P).Answer (FSt P) P.Ch)
    (hH : ∀ s k, H s k = hashStep s.1 s.2 k) (l : JSt P) (q : PartyId) (k : (fsOf P).Key)
    (e : P.Ch) (he : (l.tabs q).1.lookup k = some e) :
    hashAt P H l q k = PMF.pure (.inl e, l) := by
  simp only [hashAt, toOracle, hH]
  unfold hashStep
  rw [he]
  simp [Step.toPMF, PMF.pure_map]

/-- A hash query of a party does not read the phase of the layer. -/
theorem hashAt_ph (H : FSt P → (fsOf P).Key → Step (fsOf P).Answer (FSt P) P.Ch) (l : JSt P)
    (p : JPh P) (q : PartyId) (k : (fsOf P).Key) :
    hashAt P H { l with ph := p } q k =
      (hashAt P H l q k).map fun r => (r.1, { r.2 with ph := p }) := by
  simp only [hashAt, PMF.map_comp]
  rfl

end Hash

/-! ## The two worlds off the forbidden injections -/

section Worlds

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] [Fintype P.Wit] [Nonempty P.Wit]
  {K : Type} [Fintype K] [Nonempty K]

/-- The two worlds agree at an event other than an injection. -/
theorem simSignO_eq_filtJO (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K)
    (e : JEv P) (he : ∀ sid pid spk σ, e ≠ .inr (.inr (.inject sid pid spk σ))) :
    simSignO P A t e = filtJO P A t e := by
  rcases e with h | a | (q | ⟨q, k⟩ | ⟨sid, pid, spk, σ⟩)
  · exact jointOWith_inl P _ A t h
  · exact jointOWith_inr_inl P _ A t a
  · simp only [simSignO, jointOWith, filtJO, layO, jPre, PMF.pure_bind, realStep_pub,
      PMF.bind_map, PMF.map_comp, Function.comp_def, jPost]
  · simp only [simSignO, jointOWith, filtJO, layO, jPre, PMF.pure_bind, realStep_pub,
      PMF.bind_map, PMF.map_comp, Function.comp_def, jPost]
  · exact absurd rfl (he sid pid spk σ)

/-- The two worlds agree at an injection at a session without a peer. -/
theorem simSignO_eq_filtJO_none (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K)
    (sid : SessionId) (pid : PartyId) (spk : P.Stmt) (σ : P.Com × P.Resp)
    (h : t.1.peers (sid, pid) = none) :
    simSignO P A t (.inr (.inr (.inject sid pid spk σ))) =
      filtJO P A t (.inr (.inr (.inject sid pid spk σ))) := by
  simp [simSignO, jointOWith, filtJO, layO, jPre, h, jPost, X3DHSquareSigned.realStep, realGame,
    realGameK, realAdvK, PMF.pure_map]

/-- The completion with a delivered prekey keeps the peers of the records. -/
theorem completeSig_peer (A : AKEAlg P.Wit P.Stmt) (s : RSt P.Wit P.Stmt K) (x : Inst)
    (spk : P.Stmt) : ∀ c ∈ (completeSig A s x spk).support, ∀ y,
      (c.2.st.recs y).map Rec.peer = (s.st.recs y).map Rec.peer := by
  intro c hc y
  unfold completeSig at hc
  repeat' split at hc
  all_goals first
    | (simp only [PMF.support_pure, Set.mem_singleton_iff] at hc; rw [hc])
    | (simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hc
       obtain ⟨la, hla, lb, hlb, k', -, rfl⟩ := hc
       have ha := (X3DHSquareSigned.ltAt_support _ _ la hla).1
       have hb := (X3DHSquareSigned.ltAt_support _ _ lb hlb).1
       rw [keyed_recs_peer _ _ _ _ _ (by rwa [hb, ha]), hb, ha])

/-- A step of the filtered world at an honest or X3DH adversary event: the layer state is the
state of the event of the layer, and the X3DH state a state of the real step. -/
theorem filtJO_support_pre (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K)
    (e : JEv P) (he : FiltPre t.1 e) : ∀ x ∈ (filtJO P A t e).support,
      ∃ a ∈ (jPre P t.1 e).support, ∃ z ∈ (X3DHSquareSigned.realStep A t.2 a.2).support,
        x.2 = (a.1, z.2) := by
  intro x hx
  simp only [filtJO, X3DHSquareSigned.layO, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
    Set.mem_image] at hx
  obtain ⟨a, ha, z, hz, r, hr, rfl⟩ := hx
  exact ⟨a, ha, z, hz, by rw [jPost_keep a.1 z.1 (he a ha).2.2 r hr]⟩

/-- The world with simulated signatures keeps `InvJ`. -/
theorem invJ_simSignO (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P)
    (ht : InvJ P A t) : ∀ x ∈ (simSignO P A t e).support, InvJ P A x.2 := by
  intro x hx
  obtain ⟨hpe, hsg⟩ := ht
  have hlt := jointOWith_lt_mono P _ A t e x hx
  -- the signatures when they are kept
  have hkeep : x.2.1.sigs = t.1.sigs → ∀ q c, x.2.1.sigs q = some c →
      ∃ v, x.2.2.lt q = some v ∧ c.1 = A.pub v.1 ∧ c.2.1 = A.pub v.2 := by
    intro h q c hc
    rw [h] at hc
    obtain ⟨v, hv, h'⟩ := hsg q c hc
    exact ⟨v, hlt q v hv, h'⟩
  rcases e with h | g | (q | ⟨q, k⟩ | ⟨sid, pid, spk, σ⟩)
  · rw [simSignO, jointOWith_inl] at hx
    obtain ⟨a, ha, z, hz, hxa⟩ := filtJO_support_pre P A t _ (filtPre_inl t.1 h) x hx
    obtain ⟨hz1, -⟩ := X3DHSquareSigned.realO_support A t.2 a.2 z hz
    refine ⟨fun y => ?_, hkeep (by rw [hxa]; exact (filtPre_inl t.1 h a ha).2.1)⟩
    rw [hxa]
    rcases h with ⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩ <;>
      simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at ha <;> subst ha <;>
      rw [hz1 y]
    · unfold notePeerJ
      by_cases hy : y = (sid, pid)
      · subst hy
        cases hr : t.2.st.recs (sid, pid) <;> simp [hr, hpe]
      · split <;> simp [hy, hpe]
    · exact hpe y
  · rw [simSignO, jointOWith_inr_inl] at hx
    obtain ⟨a, ha, z, hz, hxa⟩ := filtJO_support_pre P A t _ (filtPre_inr_inl t.1 g) x hx
    obtain ⟨hz1, -⟩ := X3DHSquareSigned.realO_support A t.2 a.2 z hz
    refine ⟨fun y => ?_, hkeep (by rw [hxa]; exact (filtPre_inr_inl t.1 g a ha).2.1)⟩
    simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    rw [hxa, hz1 y]
    exact hpe y
  · simp only [simSignO, jointOWith, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hx
    obtain ⟨l, hl, r, hr, rfl⟩ := hx
    obtain ⟨hl1, -, -, hl4, hl5⟩ := X3DHSquareSigned.ltAt_support _ _ l hl
    refine ⟨fun y => ?_, ?_⟩
    · unfold signAt at hr
      split at hr
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
        subst hr
        simp only [hl1]
        exact hpe y
      · simp only [PMF.support_map, Set.mem_image] at hr
        obtain ⟨z, -, rfl⟩ := hr
        simp only [hl1]
        exact hpe y
    · unfold signAt at hr
      split at hr
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
        subst hr
        exact hkeep rfl
      · simp only [PMF.support_map, Set.mem_image] at hr
        obtain ⟨z, -, rfl⟩ := hr
        intro q' c hc
        by_cases hq : q' = q
        · subst hq
          simp only [Function.update_self, Option.some.injEq] at hc
          subst hc
          exact ⟨l.1, hl4, rfl, rfl⟩
        · simp only [Function.update_of_ne hq] at hc
          obtain ⟨v, hv, h'⟩ := hsg q' c hc
          exact ⟨v, hl5 q' v hv, h'⟩
  · simp only [simSignO, jointOWith, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hx
    obtain ⟨l, hl, r, hr, rfl⟩ := hx
    obtain ⟨hl1, -, -, -, -⟩ := X3DHSquareSigned.ltAt_support _ _ l hl
    obtain ⟨_, -, -, hr3⟩ := hashAt_support P _ (fun _ _ => rfl) _ q k r hr
    refine ⟨fun y => ?_, hkeep (by simp only; rw [hr3])⟩
    simp only [hl1]
    rw [hr3]
    exact hpe y
  · simp only [simSignO, jointOWith] at hx
    split at hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hpe, hsg⟩
    · simp only [PMF.support_bind, Set.mem_iUnion] at hx
      obtain ⟨l, hl, r, hr, hx⟩ := hx
      obtain ⟨hl1, -, -, -, -⟩ := X3DHSquareSigned.ltAt_support _ _ l hl
      obtain ⟨_, -, -, hr3⟩ := hashAt_support P _ (fun _ _ => rfl) _ _ _ r hr
      have hx1 : x.2.1 = r.2 := by
        split at hx
        · simp only [PMF.support_map, Set.mem_image] at hx
          obtain ⟨c, -, rfl⟩ := hx
          rfl
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
          rw [hx]
      have hx2 : ∀ y, (x.2.2.st.recs y).map Rec.peer = (t.2.st.recs y).map Rec.peer := by
        intro y
        split at hx
        · simp only [PMF.support_map, Set.mem_image] at hx
          obtain ⟨c, hc, rfl⟩ := hx
          rw [completeSig_peer P A _ _ spk c hc y, hl1]
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
          rw [hx, hl1]
      refine ⟨fun y => ?_, hkeep (by rw [hx1, hr3])⟩
      rw [hx2 y, hx1, hr3]
      exact hpe y

/-- The flag environment follows the layer state along a step of the world with simulated
signatures. -/
theorem relF_simSignO (A : AKEAlg P.Wit P.Stmt) (f : FlSt) (t : JSt P × RSt P.Wit P.Stmt K)
    (e : JEv P) (hf : RelF P f t) :
    ∀ x ∈ (simSignO P A t e).support, RelF P (flNext P f e) x.2 := by
  intro x hx
  rcases f with ⟨fp, fs⟩
  obtain ⟨hp, hs⟩ := hf
  simp only at hp hs
  subst hp
  rcases e with h | g | (q | ⟨q, k⟩ | ⟨sid, pid, spk, σ⟩)
  · rw [simSignO, jointOWith_inl] at hx
    obtain ⟨a, ha, z, -, hxa⟩ := filtJO_support_pre P A t _ (filtPre_inl t.1 h) x hx
    rw [hxa]
    rcases h with ⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩ <;>
      simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at ha <;> subst ha
    · simp only [flNext, notePeerJ]
      split_ifs <;> exact ⟨rfl, hs⟩
    · exact ⟨rfl, hs⟩
  · rw [simSignO, jointOWith_inr_inl] at hx
    obtain ⟨a, ha, z, -, hxa⟩ := filtJO_support_pre P A t _ (filtPre_inr_inl t.1 g) x hx
    simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    rw [hxa]
    exact ⟨rfl, hs⟩
  · simp only [simSignO, jointOWith, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hx
    obtain ⟨l, -, r, hr, rfl⟩ := hx
    unfold signAt at hr
    split at hr
    · rename_i c hc
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨rfl, fun q' => ?_⟩
      by_cases hq : q' = q
      · subst hq
        simp only at hc
        simp [flNext, hc]
      · simp [flNext, Function.update_of_ne hq, hs]
    · simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨z, -, rfl⟩ := hr
      refine ⟨rfl, fun q' => ?_⟩
      by_cases hq : q' = q
      · subst hq
        simp [flNext]
      · simp [flNext, Function.update_of_ne hq, hs]
  · simp only [simSignO, jointOWith, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hx
    obtain ⟨l, -, r, hr, rfl⟩ := hx
    obtain ⟨_, -, -, hr3⟩ := hashAt_support P _ (fun _ _ => rfl) _ q k r hr
    simp only [flNext]
    rw [hr3]
    exact ⟨rfl, hs⟩
  · simp only [simSignO, jointOWith] at hx
    simp only [flNext]
    split at hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨rfl, hs⟩
    · simp only [PMF.support_bind, Set.mem_iUnion] at hx
      obtain ⟨l, -, r, hr, hx⟩ := hx
      obtain ⟨_, -, -, hr3⟩ := hashAt_support P _ (fun _ _ => rfl) _ _ _ r hr
      have hx1 : x.2.1 = r.2 := by
        split at hx
        · simp only [PMF.support_map, Set.mem_image] at hx
          obtain ⟨c, -, rfl⟩ := hx
          rfl
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
          rw [hx]
      unfold RelF
      rw [hx1, hr3]
      exact ⟨rfl, hs⟩

/-- **The two worlds agree off the forbidden injections**, from a state with `InvJ`. -/
theorem filtJO_apply_eq (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P)
    (x : JOut P K × (JSt P × RSt P.Wit P.Stmt K)) (ht : InvJ P A t)
    (hx : ¬ ForgeJ P A t e x) : filtJO P A t e x = simSignO P A t e x := by
  obtain ⟨hpe, hsg⟩ := id ht
  by_cases he : ∃ sid pid spk σ, e = .inr (.inr (.inject sid pid spk σ))
  swap
  · push Not at he
    rw [simSignO_eq_filtJO P A t e he]
  obtain ⟨sid, pid, spk, σ, rfl⟩ := he
  rcases hq : t.1.peers (sid, pid) with _ | q
  · rw [simSignO_eq_filtJO_none P A t sid pid spk σ hq]
  simp only [filtJO, layO, jPre, hq, simSignO, jointOWith, hashAt_ph, PMF.bind_map,
    Function.comp_def, simStep, jPost]
  rw [PMF.bind_comm (ltAt t.2 q), PMF.bind_apply, PMF.bind_apply]
  refine tsum_mul_congr_support _ _ _ fun r hr => ?_
  obtain ⟨e, hr1, hre, -⟩ := hashAt_support P _ (fun _ _ => rfl) _ q _ r hr
  -- the points of a forbidden injection
  have hF : ∀ (o : JOut P K) (s : RSt P.Wit P.Stmt K) (v : P.Wit × P.Wit), s.lt q = some v →
      verAns P (A.pub v.1) σ r.1 = true → ¬ ((t.1.sigs q).isSome = true ∧ spk = A.pub v.2) →
      ForgeJ P A t (.inr (.inr (.inject sid pid spk σ))) (o, ({ r.2 with ph := .inj }, s)) := by
    intro o s v hs hv hn
    rw [hr1] at hv
    exact ⟨sid, pid, spk, σ, q, v, e, rfl, hq, hs, hre, hv, hn⟩
  by_cases hacc : accJ P t.1 q spk σ r.1 = true
  · simp only [hacc, ↓reduceIte]
    unfold accJ at hacc
    split at hacc
    · rename_i c hc
      obtain ⟨v, hv, hc1, hc2⟩ := hsg q c hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hacc
      rw [ltAt_of_some _ _ v hv, PMF.pure_bind, ← hc1]
      simp only [hacc.2, ↓reduceIte]
      have hstep : X3DHSquareSigned.realStep A t.2 (.inr (.complete sid pid)) =
          (completeSig A t.2 (sid, pid) spk).map fun c => (.inr c.1, c.2) := by
        rw [completeSig_eq A t.2 _ spk]
        · rfl
        intro rc hrc
        have hpq : rc.peer = q := by
          have := hpe (sid, pid)
          rw [hq, hrc] at this
          exact (Option.some.inj this).symm
        rw [hpq, ← hacc.1, hc2]
        exact ⟨v, hv, rfl⟩
      rw [hstep, PMF.bind_map]
      simp only [Function.comp_def, PMF.pure_map]
      rfl
    · exact absurd hacc Bool.false_ne_true
  · have hacc' : accJ P t.1 q spk σ r.1 = false := by simpa using hacc
    simp only [hacc', Bool.false_eq_true, ↓reduceIte]
    rw [X3DHSquareSigned.realStep_pub, PMF.bind_map, PMF.bind_apply, PMF.bind_apply]
    refine tsum_mul_congr_support _ _ _ fun lt hlt => ?_
    obtain ⟨-, -, -, hlt4, -⟩ := X3DHSquareSigned.ltAt_support _ _ lt hlt
    simp only [Function.comp_apply, PMF.pure_map]
    split_ifs with hv
    · have hn : ¬ ((t.1.sigs q).isSome = true ∧ spk = A.pub lt.1.2) := by
        rintro ⟨hs, hspk⟩
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨v, hv', hc1, hc2⟩ := hsg q c hc
        rw [ltAt_of_some _ _ v hv', PMF.support_pure, Set.mem_singleton_iff] at hlt
        subst hlt
        refine hacc ?_
        simp only [accJ, hc, Bool.and_eq_true, beq_iff_eq]
        exact ⟨hc2.trans hspk.symm, hc1 ▸ hv⟩
      rw [PMF.pure_apply_of_ne _ _ fun h => hx (by rw [h]; exact hF _ _ _ hlt4 hv hn)]
      symm
      refine (PMF.apply_eq_zero_iff _ _).mpr fun hx' => ?_
      rw [PMF.support_map] at hx'
      obtain ⟨c, hc, rfl⟩ := hx'
      exact hx (hF _ _ _ (completeSig_lt_mono P A lt.2 _ spk c hc q lt.1 hlt4) hv hn)
    · rfl

/-- The filtered world at `pub q` reads the long-term secrets of `q`. -/
theorem filtJO_pub (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K) (q : PartyId) :
    filtJO P A t (.inr (.inl (.pub q))) = (ltAt t.2 q).map fun lt =>
      (.inr (.inl (.pub (A.pub lt.1.1) (A.pub lt.1.2))), ({ t.1 with ph := .adv }, lt.2)) := by
  simp only [filtJO, layO, jPre, PMF.pure_bind, realStep_pub, PMF.bind_map, Function.comp_def,
    jPost, PMF.pure_map]
  rfl

/-- The filtered world at `sigHash q k`, when the long-term secrets of `q` are drawn, is the hash
query of `q` at `k`. -/
theorem filtJO_sigHash (A : AKEAlg P.Wit P.Stmt) (l : JSt P) (s : RSt P.Wit P.Stmt K)
    (q : PartyId) (k : P.Com × P.Stmt) (v : P.Wit × P.Wit) (hv : s.lt q = some v) :
    filtJO P A (l, s) (.inr (.inr (.sigHash q k))) =
      (hashAt P (fun s k => hashStep s.1 s.2 k) l q k).map fun r =>
        (.inr (.inr (hashOut P r.1)), ({ r.2 with ph := .hash q k }, s)) := by
  simp only [filtJO, layO, jPre, PMF.pure_bind, realStep_pub, ltAt_of_some _ _ v hv,
    PMF.pure_map, jPost, hashAt_ph, PMF.map_comp, simStep]
  rfl

/-- The filtered world at an injection at a session with the peer `q`, at a point where the
table of `q` holds `e`, is the completion or `pub q` of the real state machine. -/
theorem filtJO_inject_of_lookup (A : AKEAlg P.Wit P.Stmt) (l : JSt P) (s : RSt P.Wit P.Stmt K)
    (sid : SessionId) (pid q : PartyId) (spk : P.Stmt) (σ : P.Com × P.Resp) (e : P.Ch)
    (hq : l.peers (sid, pid) = some q) (he : (l.tabs q).1.lookup (σ.1, spk) = some e) :
    filtJO P A (l, s) (.inr (.inr (.inject sid pid spk σ))) =
      (X3DHSquareSigned.realStep A s (if accJ P l q spk σ (.inl e) then
        .inr (.complete sid pid) else .inr (.pub q))).map fun z =>
          (.inr (.inr .ack), ({ l with ph := .inj }, z.2)) := by
  simp only [filtJO, layO, jPre, hq, hashAt_of_lookup P _ (fun _ _ => rfl) l q _ e he,
    PMF.pure_map, PMF.pure_bind, jPost]
  rfl

/-- The completion of the real state machine at a session whose peer has drawn the long-term
secrets of the prekey `spk` is the completion with the delivered prekey `spk`. -/
theorem realStep_complete (A : AKEAlg P.Wit P.Stmt) (s : RSt P.Wit P.Stmt K) (sid : SessionId)
    (pid : PartyId) (spk : P.Stmt)
    (h : ∀ rc, s.st.recs (sid, pid) = some rc → ∃ v, s.lt rc.peer = some v ∧ A.pub v.2 = spk) :
    X3DHSquareSigned.realStep A s (.inr (.complete sid pid)) =
      (completeSig A s (sid, pid) spk).map fun c => (.inr c.1, c.2) := by
  rw [completeSig_eq A s _ spk h]
  rfl

open Classical in
/-- **The queries of the flag environment against the filtered world** are a step of the world
with simulated signatures, observed as `none` at a forbidden injection. -/
theorem flagAsk_run (A : AKEAlg P.Wit P.Stmt) (f : FlSt) (t : JSt P × RSt P.Wit P.Stmt K)
    (e : JEv P) (ht : InvJ P A t) (hf : RelF P f t) :
    (OracleAdv.run (filtJO P A) (flagAsk P f e) t).map
        (fun y => y.1.map fun o => (o, y.2)) =
      (simSignO P A t e).map fun x => if ForgeJ P A t e x then none else some x := by
  have hmap : ∀ {α β : Type} (p : PMF α) (g g' : α → β), (∀ a ∈ p.support, g a = g' a) →
      p.map g = p.map g' := fun p g g' h =>
    PMF.bind_congr_support _ _ _ fun a ha => by
      rw [Function.comp_apply, Function.comp_apply, h a ha]
  obtain ⟨hpe, hsg⟩ := id ht
  rcases f with ⟨fp, fs⟩
  obtain ⟨hp, hs⟩ := hf
  simp only at hp hs
  subst hp
  -- the events at which `flagAsk` passes the event on
  have hpass : flagAsk P (K := K) ⟨t.1.peers, fs⟩ e = .query e (fun o => .ret (some o)) →
      simSignO P A t e = filtJO P A t e → (∀ x, ¬ ForgeJ P A t e x) →
      (OracleAdv.run (filtJO P A) (flagAsk P ⟨t.1.peers, fs⟩ e) t).map
          (fun y => y.1.map fun o => (o, y.2)) =
        (simSignO P A t e).map fun x => if ForgeJ P A t e x then none else some x := by
    intro hfa hso hF
    simp only [hfa, hso, hF, OracleAdv.run_query, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map,
      Option.map_some, ↓reduceIte]
    rfl
  by_cases he : ∃ sid pid spk σ, e = .inr (.inr (.inject sid pid spk σ))
  swap
  · push Not at he
    refine hpass ?_ (simSignO_eq_filtJO P A t e he) ?_
    · rcases e with h | g | (q | ⟨q, k⟩ | ⟨sid, pid, spk, σ⟩) <;> try rfl
      exact absurd rfl (he sid pid spk σ)
    · rintro x ⟨sid, pid, spk, σ, -, -, -, h, -⟩
      exact he _ _ _ _ h
  obtain ⟨sid, pid, spk, σ, rfl⟩ := he
  rcases hq : t.1.peers (sid, pid) with _ | q
  · refine hpass (by simp only [flagAsk, hq]) (simSignO_eq_filtJO_none P A t sid pid spk σ hq) ?_
    intro x hx
    obtain ⟨sid', pid', spk', σ', q, v, c, he, h, -⟩ := hx
    simp only [Sum.inr.injEq, JSigEv.inject.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    rw [hq] at h
    exact absurd h (by simp)
  simp only [flagAsk, hq, OracleAdv.run_query, filtJO_pub, PMF.bind_map, PMF.map_bind]
  simp only [simSignO, jointOWith, hq, PMF.map_bind]
  refine PMF.bind_congr_support _ _ _ fun lt hlt => ?_
  obtain ⟨hl1, -, -, hlt4, -⟩ := X3DHSquareSigned.ltAt_support _ _ lt hlt
  simp only [Function.comp_apply]
  rw [filtJO_sigHash P A _ _ q _ lt.1 hlt4, PMF.bind_map]
  simp only [hashAt_ph, simStep, PMF.bind_map, PMF.map_bind]
  refine PMF.bind_congr_support _ _ _ fun r hr => ?_
  obtain ⟨e, hr1, hre, hr3⟩ := hashAt_support P _ (fun _ _ => rfl) _ q _ r hr
  simp only [Function.comp_apply, hr1, hashOut, forgeObs, verAns]
  -- the forbidden injections among the outcomes of this branch
  have hFj : ∀ (o : JOut P K) (s : RSt P.Wit P.Stmt K), s.lt q = some lt.1 →
      (ForgeJ P A t (.inr (.inr (.inject sid pid spk σ)))
          (o, ({ tabs := r.2.tabs, sigs := r.2.sigs, peers := r.2.peers, ph := .inj }, s)) ↔
        P.verify (A.pub lt.1.1) σ.1 e σ.2 = true ∧
          ¬ ((t.1.sigs q).isSome = true ∧ spk = A.pub lt.1.2)) := by
    intro o s hs
    constructor
    · rintro ⟨sid', pid', spk', σ', q', v, c, he, hq', hv, hc, hver, hn⟩
      simp only [Sum.inr.injEq, JSigEv.inject.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      rw [hq, Option.some.injEq] at hq'
      subst hq'
      rw [hs, Option.some.injEq] at hv
      subst hv
      simp only [hre, Option.some.injEq] at hc
      subst hc
      exact ⟨hver, hn⟩
    · rintro ⟨hver, hn⟩
      exact ⟨sid, pid, spk, σ, q, lt.1, e, rfl, hq, hs, hre, hver, hn⟩
  -- the long-term secrets of a party that signed
  have hsig : ∀ c, t.1.sigs q = some c → c.1 = A.pub lt.1.1 ∧ c.2.1 = A.pub lt.1.2 := by
    intro c hc
    obtain ⟨v, hv', hc1, hc2⟩ := hsg q c hc
    rw [ltAt_of_some _ _ v hv', PMF.support_pure, Set.mem_singleton_iff] at hlt
    subst hlt
    exact ⟨hc1, hc2⟩
  have hpeers : r.2.peers (sid, pid) = some q := by rw [hr3]; exact hq
  have hsigs : r.2.sigs = t.1.sigs := by rw [hr3]
  by_cases hv : P.verify (A.pub lt.1.1) σ.1 e σ.2 = true
  · by_cases hn : (t.1.sigs q).isSome = true ∧ spk = A.pub lt.1.2
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn.1
      have h1 : fs q = true := by rw [hs]; exact hn.1
      have h2 : (spk == A.pub lt.1.2) = true := by simp [hn.2]
      have hacc : accJ P ⟨r.2.tabs, r.2.sigs, r.2.peers, .hash q (σ.1, spk)⟩ q spk σ (.inl e) =
          true := by
        simp [accJ, hsigs, hc, verAns, (hsig c hc).1, (hsig c hc).2, hn.2, hv]
      simp only [hv, h1, h2, Bool.and_self, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte, OracleAdv.run_query, OracleAdv.run_ret]
      rw [filtJO_inject_of_lookup P A ⟨r.2.tabs, r.2.sigs, r.2.peers, .hash q (σ.1, spk)⟩ lt.2
        sid pid q spk σ e hpeers hre, hacc]
      simp only [↓reduceIte]
      rw [realStep_complete P A lt.2 sid pid spk fun rc hrc => ?_]
      · simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
        refine PMF.bind_congr_support _ _ _ fun c hc => ?_
        have hnF := fun h => ((hFj (.inr (.inr .ack)) c.2
          (completeSig_lt_mono P A lt.2 _ spk c hc q lt.1 hlt4)).mp h).2 hn
        split_ifs with hF
        · exact absurd hF hnF
        · rfl
      · grind
    · have h3 : (fs q && spk == A.pub lt.1.2) = false := by
        rw [hs, Bool.and_eq_false_iff]
        by_cases h : (t.1.sigs q).isSome = true
        · exact Or.inr (beq_eq_false_iff_ne.mpr fun h' => hn ⟨h, h'⟩)
        · exact Or.inl (by simpa using h)
      simp only [hv, h3, Bool.true_and, Bool.not_false, ↓reduceIte, OracleAdv.run_ret,
        PMF.pure_map, Option.map_none]
      rw [PMF.map_comp, hmap _ _ (fun _ => none)]
      · exact (PMF.map_const _ _).symm
      · intro c hc
        simp only [Function.comp_apply, (hFj (.inr (.inr .ack)) c.2
          (completeSig_lt_mono P A lt.2 _ spk c hc q lt.1 hlt4)).mpr ⟨hv, hn⟩, ↓reduceIte]
  · have hv' : P.verify (A.pub lt.1.1) σ.1 e σ.2 = false := by simpa using hv
    have hacc : accJ P ⟨r.2.tabs, r.2.sigs, r.2.peers, .hash q (σ.1, spk)⟩ q spk σ (.inl e) =
        false := by
      simp only [accJ, hsigs]
      split
      · rename_i c hc
        simp [verAns, (hsig c hc).1, hv]
      · rfl
    have hnF : ¬ ForgeJ P A t (.inr (.inr (.inject sid pid spk σ)))
        (.inr (.inr .ack), (⟨r.2.tabs, r.2.sigs, r.2.peers, .inj⟩, lt.2)) := fun h =>
          hv ((hFj _ _ hlt4).mp h).1
    simp only [hv', Bool.false_and, Bool.false_eq_true, ↓reduceIte, OracleAdv.run_query,
      OracleAdv.run_ret]
    rw [filtJO_inject_of_lookup P A ⟨r.2.tabs, r.2.sigs, r.2.peers, .hash q (σ.1, spk)⟩ lt.2
      sid pid q spk σ e hpeers hre, hacc]
    simp only [Bool.false_eq_true, ↓reduceIte, X3DHSquareSigned.realStep_pub,
      ltAt_of_some _ _ _ hlt4, PMF.pure_map, PMF.pure_bind, Option.map_some, hnF]

end Worlds

/-! ## Up to forgery -/

section Hop

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] [Fintype P.Wit] [Nonempty P.Wit]
  {K : Type} [Fintype K] [Nonempty K]

omit [Fintype P.Wit] [Nonempty P.Wit] [Fintype K] [Nonempty K] in
/-- The initial state satisfies `InvJ`. -/
theorem invJ_jInit (A : AKEAlg P.Wit P.Stmt) : InvJ P A (jInit P (K := K)) := by
  refine ⟨fun x => ?_, fun q c h => ?_⟩
  · rfl
  · simp [jInit, JSt.init] at h

omit [Fintype P.Wit] [Nonempty P.Wit] [Fintype K] [Nonempty K] in
/-- The initial states of the flag environment and of the worlds agree. -/
theorem relF_init : RelF P FlSt.init (jInit P (K := K)) :=
  ⟨rfl, fun _ => rfl⟩

open Classical in
/-- **Hop 2 of the joint-key model, up to forgery.** For every oracle adversary `B`, the
difference of the probabilities that `B` outputs `true` against the world with simulated
signatures and against the filtered world is at most the probability of a forbidden injection
in the world with simulated signatures. -/
theorem joint_upto_forgery (A : AKEAlg P.Wit P.Stmt)
    (B : OracleAdv (JEv P) (JOut P K) Bool) :
    absDiff ((OracleAdv.run (simSignO P A) B (jInit P)).map Prod.fst true)
        ((OracleAdv.run (filtJO P A) B (jInit P)).map Prod.fst true) ≤
      (OracleAdv.run (OracleAdv.flagWhen (ForgeJ P A) (simSignO P A)) B
        (jInit P, false)).toOuterMeasure {y | y.2.2 = true} := by
  have hgap := OracleAdv.run_gap_le_flagWhen (fun s d x => ¬ InvJ P A s ∨ ForgeJ P A s d x)
    (filtJO P A) (simSignO P A)
    (fun s d x hx => filtJO_apply_eq P A s d x (by tauto) (by tauto)) B (jInit P) {true}
  rw [OracleGameUpToBad.map_fst_apply_true, OracleGameUpToBad.map_fst_apply_true, absDiff_comm]
  refine hgap.trans ?_
  refine OracleAdv.run_flagWhen_le_of_inv (simSignO P A) _ (ForgeJ P A) (InvJ P A)
    (fun s d hs x hx => ?_) B (jInit P) (invJ_jInit P A)
  by_cases hb : ForgeJ P A s d x
  · exact Or.inl hb
  · exact Or.inr ⟨fun h => h.elim (· hs) hb, invJ_simSignO P A s d hs x hx⟩

open Classical in
/-- The flag of `ForgeJ` from a state related to the state of the flag environment is the
probability that the flag environment outputs `true` in the filtered world. -/
theorem flag_eq_flagEnv (A : AKEAlg P.Wit P.Stmt) (B : OracleAdv (JEv P) (JOut P K) Bool)
    (f : FlSt) (t : JSt P × RSt P.Wit P.Stmt K) (ht : InvJ P A t) (hf : RelF P f t) :
    (OracleAdv.run (OracleAdv.flagWhen (ForgeJ P A) (simSignO P A)) B
        (t, false)).toOuterMeasure {y | y.2.2 = true} =
      (OracleAdv.run (filtJO P A) (flagEnv P B f) t).toOuterMeasure {y | y.1 = true} := by
  induction B generalizing f t with
  | ret a =>
    simp [flagEnv, PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, flagEnv, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    exact tsum_congr fun b => by rw [ih b f t ht hf]
  | query e k ih =>
    -- the continuation of the flag environment after the queries of `flagAsk`
    let Q : Option (JOut P K × (JSt P × RSt P.Wit P.Stmt K)) →
        PMF (Bool × (JSt P × RSt P.Wit P.Stmt K)) := fun z => match z with
      | none => PMF.pure (true, t)
      | some x => OracleAdv.run (filtJO P A) (flagEnv P (k x.1) (flNext P f e)) x.2
    have hR : (OracleAdv.run (filtJO P A) (flagEnv P (.query e k) f) t).toOuterMeasure
          {y | y.1 = true} =
        (((simSignO P A t e).map fun x => if ForgeJ P A t e x then none else some x).bind
          Q).toOuterMeasure {y | y.1 = true} := by
      rw [← flagAsk_run P A f t e ht hf, PMF.bind_map]
      simp only [flagEnv, OracleAdv.run_bind, PMF.toOuterMeasure_bind_apply]
      refine tsum_congr fun y => ?_
      congr 1
      rcases y with ⟨_ | o, s⟩
      · simp [Q, PMF.toOuterMeasure_pure_apply]
      · rfl
    rw [hR, PMF.bind_map, OracleAdv.run_query]
    simp only [OracleAdv.flagWhen, Bool.false_or]
    rw [PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    simp only [Function.comp_apply]
    refine tsum_mul_congr_support _ _ _ fun x hx => ?_
    by_cases hb : ForgeJ P A t e x
    · simp only [hb, decide_true, ↓reduceIte, Q, X3DHSquareGDH.run_flag_true_one]
      simp [PMF.toOuterMeasure_pure_apply]
    · simp only [hb, decide_false, ↓reduceIte, Q]
      exact ih x.1 (flNext P f e) x.2 (invJ_simSignO P A t e ht x hx)
        (relF_simSignO P A f t e hf x hx)

open Classical in
/-- **The forgery event is the output of the flag environment in the filtered world.** For
every oracle adversary `B`, the probability of a forbidden injection in the world with simulated
signatures is the probability that the flag environment `flagEnv B` outputs `true` against the
filtered world. -/
theorem forgeJ_eq_flagEnv (A : AKEAlg P.Wit P.Stmt) (B : OracleAdv (JEv P) (JOut P K) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (ForgeJ P A) (simSignO P A)) B
        (jInit P, false)).toOuterMeasure {y | y.2.2 = true} =
      (OracleAdv.run (filtJO P A) (flagEnv P B FlSt.init) (jInit P)).map Prod.fst true := by
  rw [flag_eq_flagEnv P A B _ _ (invJ_jInit P A) (relF_init P),
    ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

end Hop

end CatCrypt.Crypto.AKE.X3DHSquare

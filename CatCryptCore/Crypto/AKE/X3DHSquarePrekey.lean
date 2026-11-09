/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackUC
public import CatCryptCore.Crypto.AKE.X3DHSquareGDH
public import CatCryptCore.Crypto.UCLoopbackTrace
public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.UCCascade
public import CatCryptCore.Crypto.Messaging.CKACorrupt

/-!
# X3DH with the signed prekey of the responder as a datum of the session key

The square of `CatCryptCore.Crypto.AKE.X3DHSquareGDH` delivers a session key `k`. Here the key of
a session is the pair `(k, spk)` of the session key and the signed-prekey secret of the responder
of the session, the datum with which the double ratchet starts.

**Real protocol.** `x3dhRealPair G` runs X3DH as `x3dhRealOf (x3dhAlg G)`; `getKey sid pid`
answers `key (some (k, spk))` with the session key `k` and the signed-prekey secret `spk` of the
responder of the session, the responder named at the start of the session (`respOf`).

**Ideal functionality.** `F_AKEK (prekeyFresh K S) true` of `CatCryptCore.Crypto.AKE.FAKESys`:
a fresh session receives a uniform key with the datum that the simulator proposes, a partner
session the key and datum of its partner, an exposed session the proposed pair.

**Simulator.** `simProtPair G` is the X3DH simulator `simProt G` whose proposals carry the
signed-prekey secret of the responder of the session on its copy of the real state (`pairDec`).
It reads no key of the functionality (`simProtPair_opaque`) and forwards its answers
(`simProtPair_isFwd`).

**The protocol `withPub`.** An oracle protocol over the interface of X3DH that answers
`getKey sid pid` by the key of the session and, when there is one, the public signed prekey
answered by `pub` at the responder of the session. Once a session has a key, the long-term
secrets of its responder are drawn, so `pub` changes no state.

**Results.** For a layer `L` of keyed views that reads the datum only through the public key,
`L (k, s) = Leff (k, G.pub s)`, the real protocol followed by the key layer of `L` realizes the
simulator over `F_AKEK` followed by the same layer (`x3dhPair_seq_realizesSim`), with bound the
gap Diffie–Hellman bound `gdhBound` at the oracle reduction through `withPub` of the environment
reduced through the key layer of `Leff`. The proof relates both sides to `withPub` over the games
of X3DH (`realPair_stepMapOn`, `simPair_stepMapOn`) and applies the bound of the X3DH square to
the oracle adversary `withPub.reduction`.

## Main definitions

* `respOf`, `SessT`, `noteSess`: the responder of a session and the table of started sessions.
* `withPub`: the oracle protocol that attaches the public signed prekey to a key.
* `pairOracle`, `realGamePair`, `x3dhRealPair`: the real protocol with the datum.
* `spkOf`, `pairEv`, `pairDec`, `simProtPair`: the simulator with the datum.

## Main results

* `simProtPair_opaque`, `simProtPair_isFwd`.
* `x3dhPair_seq_realizesSim`: the restricted square.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquarePrekey

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.Messaging.SignalStackUC
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_pure sampleFrom_ofPMF_eq_liftPMF)
open CatCrypt.Crypto.UCCoupling (realizes_symm)
open PubView (eqView)
open scoped ENNReal

/-! ## Sessions and the protocol `withPub` -/

section WithPub

variable {S W K : Type}

/-- The responder of the session `x` started with the peer `peer` in the role `role`: its party
when the role is `responder`, its peer otherwise. -/
def respOf (x : Inst) (peer : PartyId) (role : Role) : PartyId :=
  if role = .responder then x.2 else peer

/-- A table of the started sessions: the peer and the role of each session. -/
abbrev SessT := Inst → Option (PartyId × Role)

/-- The table after the start of the session `x` with the peer `peer` in the role `role`: the
entry is recorded when `x` has none. -/
def noteSess (τ : SessT) (x : Inst) (peer : PartyId) (role : Role) : SessT :=
  if (τ x).isSome then τ else Function.update τ x (some (peer, role))

/-- An honest output without its key: `ok`, or the absent key. -/
def hdrop {K D : Type} : HOut K → HOut D
  | .ok => .ok
  | .key _ => .key none

/-- Relabelling the key of an output without key changes nothing. -/
@[simp] theorem mapKey_hdrop {K D D' : Type} (g : D → D') (h : HOut K) :
    HOut.mapKey g (hdrop h : HOut D) = hdrop h := by
  cases h <;> rfl

/-- **The protocol that attaches the public signed prekey to a key**, over the interface of
X3DH: `getKey sid pid` queries the key of the session and, when there is one, `pub` at the
responder of the session, and answers the key with the public signed prekey; `newSession`
records the session in the table; every other event is forwarded. -/
def withPub : OProt SessT (OEv W) (HOut (K × W) ⊕ ROut S W K) (OEv W) (OOut S W K) where
  init := fun _ => none
  step τ
    | .inl (.newSession sid pid peer role) =>
      .query (.inl (.newSession sid pid peer role)) fun a =>
        .ret (noteSess τ (sid, pid) peer role, Sum.map hdrop id a)
    | .inl (.getKey sid pid) =>
      .query (.inl (.getKey sid pid)) fun a =>
        match a, τ (sid, pid) with
        | .inl (.key (some k)), some (peer, role) =>
          .query (.inr (.pub (respOf (sid, pid) peer role))) fun b =>
            match b with
            | .inr (.pub _ spk) => .ret (τ, .inl (.key (some (k, spk))))
            | _ => .ret (τ, .inl (.key none))
        | _, _ => .ret (τ, .inl (.key none))
    | .inr a => .query (.inr a) fun o => .ret (τ, Sum.map hdrop id o)

end WithPub

/-! ## The real protocol with the datum -/

section Real

variable {S W K : Type} [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K]

/-- **A step of the real protocol with the datum**: the step of `realGame A`, where `getKey`
answers the key of the session with the signed-prekey secret of the responder of the session,
drawn at its first use as in `ltAt`. -/
noncomputable def pairOracle (A : AKEAlg S W) (t : SessT × RSt S W K) :
    OEv W → PMF ((HOut (K × S) ⊕ ROut S W K) × (SessT × RSt S W K))
  | .inl (.newSession sid pid peer role) =>
    ((realGame A).oracle () t.2 (.inl (.newSession sid pid peer role))).map fun p =>
      (Sum.map hdrop id p.1, (noteSess t.1 (sid, pid) peer role, p.2))
  | .inl (.getKey sid pid) =>
    match keyOf t.2.st (sid, pid), t.1 (sid, pid) with
    | some k, some (peer, role) =>
      (ltAt t.2 (respOf (sid, pid) peer role)).map fun l =>
        (.inl (.key (some (k, l.1.2))), (t.1, l.2))
    | _, _ => PMF.pure (.inl (.key none), t)
  | .inr a => ((realGame A).oracle () t.2 (.inr a)).map fun p =>
      (Sum.map hdrop id p.1, (t.1, p.2))

/-- **The real game with the datum** of the algorithms `A`: a trivial key, and the oracle is
`pairOracle A`. -/
noncomputable def realGamePair (A : AKEAlg S W) :
    KeyedGame (OEv W) (HOut (K × S) ⊕ ROut S W K) where
  Key := Unit
  State := SessT × RSt S W K
  keyDist := PMF.pure ()
  oracle _ := pairOracle A
  init := (fun _ => none, rInit)

end Real

/-- **The real X3DH protocol with the datum** over the group `G`: each event is a query to the
oracle of `realGamePair (x3dhAlg G)`. -/
noncomputable def x3dhRealPair {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
    [Nonempty K] (G : DHGroup S W) :=
  (OProt.oracle (Q := OEv W) (A := HOut (K × S) ⊕ ROut S W K)).sys
    (realGamePair (K := K) (x3dhAlg G))

/-! ## The simulator with the datum -/

section Sim

variable {S W K : Type} [Field S]

/-- The signed-prekey secret of the responder of the session `x` on the copy `rs`, and `0` when
the session or the secret is absent. -/
def spkOf (rs : RSt S W K) (x : Inst) : S :=
  match rs.st.recs x with
  | some r => ((rs.lt (respOf x r.peer r.role)).map Prod.snd).getD 0
  | none => 0

/-- The adversary event of the simulator with the datum of its session on the copy `rs`: a
proposal `k` at `x` becomes `(k, spkOf rs x)`. -/
def pairEv (rs : RSt S W K) : AEv K → AEv (K × S)
  | .idle => .idle
  | .poll => .poll
  | .corrupt pid => .corrupt pid
  | .impersonate sid pid => .impersonate sid pid
  | .newKey sid pid k => .newKey sid pid (k, spkOf rs (sid, pid))
  | .newKeyUnlinked sid pid k => .newKeyUnlinked sid pid (k, spkOf rs (sid, pid))

/-- A decision of the X3DH simulator with the datum attached to its proposals, read at the state
`s` after the decision. -/
def pairDec (s : SimSt S W K) : Dec S W K → FEv (K × S) ⊕ (HOut (K × S) ⊕ ROut S W K)
  | .inl (.inl h) => .inl (.inl h)
  | .inl (.inr a) => .inl (.inr (pairEv s.1 a))
  | .inr (.inl h) => .inr (.inl (hdrop h))
  | .inr (.inr r) => .inr (.inr r)

omit [Field S] in
/-- Every decision of the simulator with the datum is related to itself. -/
theorem pairStepRel_refl (d : FEv (K × S) ⊕ (HOut (K × S) ⊕ ROut S W K)) :
    PubView.StepRel ((keHonView (K := K × S)).sum (eqView (E := RAEv W) (O := ROut S W K)))
      (subView (K := K × S)) d d := by
  rcases d with (h | a) | (o | o)
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl

variable [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  (G : DHGroup S W)

/-- **The X3DH simulator with the datum**: the start step of `simProt G` with the decision read
by `pairDec`, and the answers of the functionality forwarded as `simProt G` forwards them. -/
noncomputable def simProtPair :
    MultiHybrid (SimSt S W K) (OEv W) (HOut (K × S) ⊕ ROut S W K) (FEv (K × S))
      (FOut (K × S)) where
  init := (rInit, fun _ => none, .fwd)
  fuel := 0
  start s e := SPComp.map (fun q => (q.1, pairDec q.1 q.2)) (simStart G s e)
  resume s o := SPComp.pure (x3dhFwd.reset s, .inr (fwdOut x3dhFwd.ack (x3dhFwd.phase s) o))
  finish s o := SPComp.pure (x3dhFwd.reset s, fwdOut x3dhFwd.ack (x3dhFwd.phase s) o)
  start_noFail s e := map_noFail _ (simStart_pureNF G s e).2
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- **Opacity of the simulator with the datum**: its state and its decisions depend on its
events and not on the answers of the functionality on its honest port. -/
theorem simProtPair_opaque :
    (simProtPair (K := K) G).Opaque
      ((keHonView (K := K × S)).sum (eqView (E := RAEv W) (O := ROut S W K)))
      (subView (K := K × S)) := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    have he' : e = e' := by
      cases he with
      | inl h => exact congrArg Sum.inl h
      | inr h => exact congrArg Sum.inr h
    subst he'
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, pairStepRel_refl _⟩)
      (rHoare_refl _)
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, fwdOut_rel _ _ ho⟩
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, fwdOut_rel _ _ ho⟩

/-- **The simulator with the datum is a forwarding simulator** for the data `x3dhFwd`. -/
theorem simProtPair_isFwd : IsFwd (simProtPair (K := K) G) x3dhFwd where
  fuel_eq := rfl
  finish_eq _ _ := rfl
  start_noHon s e q hq h := by
    change IsOutcome (SPComp.map (fun q => (q.1, pairDec q.1 q.2)) (simStart G s e)) q at hq
    obtain ⟨⟨a, d⟩, hq', rfl⟩ := isOutcome_map_iff.mp hq
    have hn := simStart_noHon G s e hq'
    rcases d with (_ | _) | (h' | r)
    · simp [pairDec]
    · simp [pairDec]
    · exact absurd rfl (hn h')
    · simp [pairDec]

end Sim

/-! ## Plumbing -/

section Plumbing

/-- **The system of a protocol over a game with a trivial key is the protocol against its
oracle**, at distance `0`. -/
theorem sys_realizes_plug {τ E O Q A : Type} (P : OProt τ E O Q A) (G : KeyedGame Q A)
    (k₀ : G.Key) (hk : ∀ k, k = k₀) (hμ : G.keyDist = PMF.pure k₀) :
    Realizes (P.sys G) (P.plug (G.oracle k₀) G.init) (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ _ (fun u => u.2) rfl ?_
  rintro ⟨o, t⟩ e
  rcases o with _ | k
  · simp only [OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed, ↓reduceIte, hμ,
      sampleFrom_ofPMF_eq_liftPMF, ← liftPMF_pure, OProt.plug, SPComp.map]
    rw [SPComp.pure_bind]
    simp [SPComp.bind_assoc, SPComp.pure_bind]
  · obtain rfl := hk k
    simp only [OProt.sys, KeyedSys.lazy, KeyedSys.lazyStep, OProt.keyed, OProt.plug, SPComp.map]
    simp [SPComp.bind_assoc, SPComp.pure_bind]

variable {τ υ E R V K₁ K₂ : Type}

/-- The key layer of `L` on an honest output is the key layer of `L'` on the output with its
key relabelled by `g`, when `L` is `L'` after `g`. -/
theorem keyLayer_step_mapKey (g : K₁ → K₂) (L : K₁ → SPComp V) (L' : K₂ → SPComp V)
    (hL : ∀ k, L k = L' (g k)) (o : HOut K₁ ⊕ R) :
    (keyLayer (R := R) L).step () o = (keyLayer L').step () (Sum.map (HOut.mapKey g) id o) := by
  rcases o with (_ | (_ | k)) | r
  · rfl
  · rfl
  · simp [keyLayer, HOut.mapKey, hL]
  · rfl

/-- **A step map with relabelled keys, under the key layer.** A step map from `X` to `X'` on an
invariant that relabels the keys of the honest outputs by `g` gives a step map from `X` followed
by the key layer of `L` to `X'` followed by the key layer of `L'`, when `L` is `L'` after `g`. -/
theorem stepMapOn_seq_keyLayer {X : Sys τ E (HOut K₁ ⊕ R)} {X' : Sys υ E (HOut K₂ ⊕ R)}
    (g : K₁ → K₂) (L : K₁ → SPComp V) (L' : K₂ → SPComp V) (hL : ∀ k, L k = L' (g k))
    (Inv : τ → Prop) (f : τ → υ) (hinit : Inv X.init) (hmap : f X.init = X'.init)
    (hpres : ∀ t e, Inv t → ∀ q, IsOutcome (X.step t e) q → Inv q.1)
    (hstep : ∀ t e, Inv t →
      SPComp.map (fun p => (f p.1, Sum.map (HOut.mapKey g) id p.2)) (X.step t e) =
        X'.step (f t) e) :
    Sys.StepMapOn (X.seq (keyLayer L)) (X'.seq (keyLayer L')) (fun p => Inv p.1)
      (Prod.map f id) where
  init_inv := hinit
  init_map := by
    change (f X.init, ()) = (X'.init, ())
    rw [hmap]
  pres t e ht q hq := by
    rw [Sys.seq_step] at hq
    obtain ⟨a, ha, hqa⟩ := isOutcome_bind hq
    obtain ⟨r, -, rfl⟩ := isOutcome_map_iff.mp hqa
    exact hpres _ _ ht a ha
  step t e ht := by
    rw [Sys.seq_step, Sys.seq_step, Prod.map_fst, ← hstep _ _ ht]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1
    funext p
    rw [keyLayer_step_mapKey g L L' hL p.2]
    rfl

end Plumbing

/-! ## The square -/

section Square

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

/-- The table of the sessions of a state of the functionality: the peer and the role of each
record. -/
def sessOf {K' : Type} (t : St K') : SessT := fun x => (t.recs x).map fun r => (r.peer, r.role)

/-- The state of `withPub` over the simulated game for a state of the simulator with the datum
running with `F_AKEK`: the table of the sessions, and the keys without their data. -/
def pairMap (t : SimSt S W K × St (K × S)) : SessT × (SimSt S W K × St K) :=
  (sessOf t.2, (t.1, St.mapKey Prod.fst t.2))

/-- **The invariant of the simulated world with the datum**: the copy of the simulator and the
functionality have the same peers and roles, and the datum of a key of the functionality is the
signed-prekey secret of the responder of its session on the copy. -/
def PairInv (t : SimSt S W K × St (K × S)) : Prop :=
  (∀ x, (t.1.1.st.recs x).map (fun r => (r.peer, r.role)) = sessOf t.2 x) ∧
    ∀ x r k d, t.2.recs x = some r → r.key = some (k, d) →
      ∃ ik, t.1.1.lt (respOf x r.peer r.role) = some (ik, d)

/-- The relabelling of a key with the signed-prekey secret to the key with the public signed
prekey. -/
def pubKey (p : K × S) : K × W := (p.1, G.pub p.2)

omit [Inhabited K] in
/-- The real game on `getKey`: the key of the session, and no change of state. -/
theorem realGame_oracle_getKey (A : AKEAlg S W) (s : RSt S W K) (sid : SessionId)
    (pid : PartyId) :
    (realGame (K := K) A).oracle () s (.inl (.getKey sid pid)) =
      PMF.pure (.inl (.key (keyOf s.st (sid, pid))), s) := by
  simp [realGame, realGameK, realHonK, PMF.pure_map]

omit [Inhabited K] in
/-- The real game on `pub p`: the public keys of the long-term secrets of `p`, drawn at their
first use. -/
theorem realGame_oracle_pub (A : AKEAlg S W) (s : RSt S W K) (p : PartyId) :
    (realGame (K := K) A).oracle () s (.inr (.pub p)) =
      (ltAt s p).map fun l => (.inr (.pub (A.pub l.1.1) (A.pub l.1.2)), l.2) := by
  simp [realGame, realGameK, realAdvK, PMF.map_comp, Function.comp_def]

omit [Inhabited K] in
/-- A step of the oracle system of the real protocol with the datum, with the public signed
prekey in place of its secret, is a step of `withPub` against the real game. -/
theorem realPair_step (t : Unit × (SessT × RSt S W K)) (e : OEv W) :
    SPComp.map (fun p => (p.1.2, Sum.map (HOut.mapKey (pubKey G)) id p.2))
      (((OProt.oracle (Q := OEv W) (A := HOut (K × S) ⊕ ROut S W K)).plug
        ((realGamePair (K := K) (x3dhAlg G)).oracle ())
        (realGamePair (K := K) (x3dhAlg G)).init).step t e) =
    ((withPub (S := S) (K := K)).plug ((realGame (K := K) (x3dhAlg G)).oracle ())
        (realGame (K := K) (x3dhAlg G)).init).step t.2 e := by
  rcases t with ⟨⟨⟩, τ, s⟩
  simp only [OProt.plug_step, OProt.plugStep, sampleFrom_ofPMF_eq_liftPMF, SPComp.map,
    liftPMF_bind_pure]
  congr 1
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | a
  · simp only [OProt.oracle, withPub, realGamePair, pairOracle, OracleAdv.run_query,
      OracleAdv.run_ret, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
    erw [OracleAdv.run_query]; rw [PMF.map_bind]; congr 1; funext x; erw [OracleAdv.run_ret]
    simp [PMF.pure_map, Sum.map_map, Function.comp_def]
    rfl
  · simp only [OProt.oracle, withPub, realGamePair, pairOracle, OracleAdv.run_query,
      OracleAdv.run_ret, PMF.map_bind, PMF.map_comp, Function.comp_def]
    erw [OracleAdv.run_query, realGame_oracle_getKey, PMF.pure_bind]
    rcases hk : keyOf s.st (sid, pid) with _ | k <;> rcases hτ : τ (sid, pid) with _ | ⟨peer, role⟩
    · simp only [PMF.pure_map, PMF.pure_bind, Sum.map_inl]
      erw [OracleAdv.run_ret]
      simp [PMF.pure_map, HOut.mapKey]
      rfl
    · simp only [PMF.pure_map, PMF.pure_bind, Sum.map_inl]
      erw [OracleAdv.run_ret]
      simp [PMF.pure_map, HOut.mapKey]
      rfl
    · simp only [PMF.pure_map, PMF.pure_bind, Sum.map_inl]
      erw [OracleAdv.run_ret]
      simp [PMF.pure_map, HOut.mapKey]
      rfl
    · dsimp only
      erw [OracleAdv.run_query, realGame_oracle_pub]
      simp only [PMF.bind_map, Function.comp_def]
      erw [PMF.bind_map, PMF.map_bind]
      congr 1
      funext l
      dsimp only [Function.comp]
      erw [OracleAdv.run_ret]
      simp [PMF.pure_map, HOut.mapKey, pubKey]
      rfl
  · simp only [OProt.oracle, withPub, realGamePair, pairOracle, OracleAdv.run_query,
      OracleAdv.run_ret, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
    erw [OracleAdv.run_query]; rw [PMF.map_bind]; congr 1; funext x; erw [OracleAdv.run_ret]
    simp [PMF.pure_map, Sum.map_map, Function.comp_def]
    rfl

omit [Inhabited K] in
/-- **The real side**: the oracle system of the real protocol with the datum, followed by the
key layer of `L`, is `withPub` against the real game followed by the key layer of `Leff`. -/
theorem realPair_stepMapOn {V : Type} (L : K × S → SPComp V) (Leff : K × W → SPComp V)
    (hL : ∀ k x₀, L (k, x₀) = Leff (k, G.pub x₀)) :
    Sys.StepMapOn
      (((OProt.oracle (Q := OEv W) (A := HOut (K × S) ⊕ ROut S W K)).plug
        ((realGamePair (K := K) (x3dhAlg G)).oracle ())
        (realGamePair (K := K) (x3dhAlg G)).init).seq (keyLayer L))
      (((withPub (S := S) (K := K)).plug ((realGame (K := K) (x3dhAlg G)).oracle ())
        (realGame (K := K) (x3dhAlg G)).init).seq (keyLayer Leff))
      (fun _ => True) (Prod.map (fun u => u.2) id) := by
  have h := stepMapOn_seq_keyLayer (X := (OProt.oracle (Q := OEv W)
      (A := HOut (K × S) ⊕ ROut S W K)).plug ((realGamePair (K := K) (x3dhAlg G)).oracle ())
        (realGamePair (K := K) (x3dhAlg G)).init)
    (X' := (withPub (S := S) (K := K)).plug ((realGame (K := K) (x3dhAlg G)).oracle ())
        (realGame (K := K) (x3dhAlg G)).init)
    (pubKey G) L Leff (fun k => hL k.1 k.2) (fun _ => True) (fun u => u.2) trivial rfl
    (fun _ _ _ _ _ => trivial) (fun t e _ => realPair_step G t e)
  exact h

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- Relabelling the keys keeps the table of the sessions. -/
@[simp] theorem sessOf_mapKey {K' K'' : Type} (f : K' → K'') (t : St K') :
    sessOf (St.mapKey f t) = sessOf t := by
  funext x
  simp only [sessOf, St.mapKey]
  cases t.recs x <;> rfl

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- The table of the sessions after the start of a session. -/
theorem sessOf_addSession {K' : Type} (t : St K') (x : Inst) (peer : PartyId) (role : Role) :
    sessOf (addSession t x peer role) = noteSess (sessOf t) x peer role := by
  funext y
  unfold addSession noteSess sessOf
  by_cases h : (t.recs x).isSome = true
  · simp [h]
  · have h' : t.recs x = none := by simpa using h
    by_cases hy : y = x
    · subst hy; simp [h']
    · simp [h', Function.update_of_ne hy]

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- A record with a new key and status keeps the table of the sessions. -/
theorem sessOf_setRec_with {K' : Type} (t : St K') (x : Inst) (r : Rec K')
    (hr : t.recs x = some r) (k : Option K') (st : Status) :
    sessOf (setRec t x { r with key := k, status := st }) = sessOf t := by
  funext y
  unfold setRec sessOf
  by_cases hy : y = x
  · subst hy; simp [hr]
  · simp [Function.update_of_ne hy]

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- `newKey` keeps the table of the sessions. -/
theorem sessOf_newKeyStep {K' : Type} (t : St K') (x : Inst) (k kf : K') :
    sessOf (newKeyStep t x k kf) = sessOf t := by
  unfold newKeyStep
  split
  · split
    · exact sessOf_setRec_with _ _ _ (by assumption) _ _
    · rfl
  · rfl

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- `newKeyUnlinked` keeps the table of the sessions. -/
theorem sessOf_newKeyFreshStep {K' : Type} (t : St K') (x : Inst) (k kf : K') :
    sessOf (newKeyFreshStep t x k kf) = sessOf t := by
  unfold newKeyFreshStep
  split
  · split
    · exact sessOf_setRec_with _ _ _ (by assumption) _ _
    · rfl
  · rfl

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- **An adversary step of `F_AKEK`** keeps the table of the sessions and answers on the
adversary port. -/
theorem F_AKEK_adv_outcome {K' : Type} (fresh : K' → SPComp K') (t : St K') (a : AEv K')
    (q : St K' × (HOut K' ⊕ AOut)) (hq : IsOutcome ((F_AKEK fresh true).step t (.inr a)) q) :
    sessOf q.1 = sessOf t ∧ ∃ r, q.2 = .inr r := by
  simp only [F_AKEK, Sys.ofPorts_step_inr, advSysK] at hq
  obtain ⟨p, hp, rfl⟩ := isOutcome_map_iff.mp hq
  cases a with
  | idle => obtain rfl := isOutcome_pure hp; exact ⟨rfl, _, rfl⟩
  | poll =>
    obtain rfl := isOutcome_pure hp
    refine ⟨?_, _, rfl⟩
    unfold pollStep; split <;> rfl
  | corrupt pid => obtain rfl := isOutcome_pure hp; exact ⟨rfl, _, rfl⟩
  | impersonate sid pid => obtain rfl := isOutcome_pure hp; exact ⟨rfl, _, rfl⟩
  | newKey sid pid k =>
    obtain ⟨kf, -, rfl⟩ := isOutcome_map_iff.mp hp
    exact ⟨sessOf_newKeyStep _ _ _ _, _, rfl⟩
  | newKeyUnlinked sid pid k =>
    obtain ⟨kf, -, rfl⟩ := isOutcome_map_iff.mp hp
    exact ⟨sessOf_newKeyFreshStep _ _ _ _, _, rfl⟩

omit [Fintype K] [Nonempty K] [Inhabited K] [Fintype S] [SampleableType W] in
/-- Dropping the datum of an event of the simulator with the datum gives its event. -/
@[simp] theorem mapKey_pairEv (rs : RSt S W K) (a : AEv K) :
    AEv.mapKey Prod.fst (pairEv rs a) = a := by
  cases a <;> rfl

omit [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- The key of the kernel `prekeyFresh` is uniform. -/
theorem sample_eq_map_prekeyFresh (p : K × S) :
    SPComp.sample K = SPComp.map Prod.fst (prekeyFresh K S p) := by
  simp [prekeyFresh, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, SPComp.bind_pure]

/-- The world of the simulator with the datum running with `F_AKEK`. -/
noncomputable abbrev pairWorld :=
  (simProtPair (K := K) G).withSub (F_AKEK (prekeyFresh K S) true)

/-- The world of the X3DH simulator running with `F_AKE`. -/
noncomputable abbrev simWorld :=
  (simProt (K := K) G).withSub (F_AKE (SPComp.sample K) true)

/-- The invariant holds at the start. -/
theorem pairInv_init : PairInv (pairWorld (K := K) G).init := by
  refine ⟨fun x => ?_, fun x r k d h _ => ?_⟩
  · simp [sessOf, pairWorld, MultiHybrid.withSub, simProtPair, F_AKEK, Sys.ofPorts, honSys,
      rInit, initSt]
  · simp [pairWorld, MultiHybrid.withSub, F_AKEK, Sys.ofPorts, honSys, initSt] at h

/-- The start state is mapped to the start state of `withPub` over the simulated game. -/
theorem pairMap_init :
    pairMap (pairWorld (K := K) G).init =
      ((withPub (S := S) (K := K)).plug ((simGame (K := K) G).oracle ())
        (simGame (K := K) G).init).init := by
  change ((sessOf (initSt : St (K × S)),
      (((rInit, fun _ => none, Phase.fwd) : SimSt S W K), St.mapKey Prod.fst (initSt : St (K × S))))
      : SessT × (SimSt S W K × St K)) =
    ((fun _ => none), (((rInit, fun _ => none, Phase.fwd) : SimSt S W K), initSt))
  rw [St.mapKey_initSt]
  rfl

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- A record with the same peer and role keeps the table of the sessions. -/
theorem sessOf_setRec {K' : Type} (t : St K') (x : Inst) (r r' : Rec K')
    (hr : t.recs x = some r) (hp : r'.peer = r.peer) (hro : r'.role = r.role) :
    sessOf (setRec t x r') = sessOf t := by
  funext y
  unfold setRec sessOf
  by_cases hy : y = x
  · subst hy; simp [hr, hp, hro]
  · simp [Function.update_of_ne hy]

omit [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The outcomes of `ltStep`: the records are kept, the secrets of `pid` are recorded, and
recorded secrets are kept. -/
theorem ltStep_outcome (rs : RSt S W K) (pid : PartyId) {l : (S × S) × RSt S W K}
    (hl : IsOutcome (ltStep rs pid) l) :
    l.2.st = rs.st ∧ l.2.lt pid = some l.1 ∧ ∀ p v, rs.lt p = some v → l.2.lt p = some v := by
  unfold ltStep at hl
  split at hl
  · rename_i v hv
    obtain rfl := isOutcome_pure hl
    exact ⟨rfl, hv, fun _ _ h => h⟩
  · rename_i hv
    obtain ⟨v, -, rfl⟩ := isOutcome_map_iff.mp hl
    refine ⟨rfl, by simp, fun p w h => ?_⟩
    by_cases hp : p = pid
    · subst hp; simp [hv] at h
    · simp [Function.update_of_ne hp, h]

/-- The table of the sessions after a decision of the simulator: the start of a session records
it, and every other decision keeps it. -/
def sessDec (τ : SessT) : Dec S W K → SessT
  | .inl (.inl (.newSession sid pid peer role)) => noteSess τ (sid, pid) peer role
  | _ => τ

/-- **The facts about an outcome `(s', d)` of the start step of the simulator from `s`** used
by the invariant: the long-term secrets of the copy are kept, its table of sessions changes by
`sessDec`, and a key proposal at `x` comes with a record of `x` on the copy whose responder has
its secrets drawn, the datum being its signed-prekey secret. -/
structure StartOk (s s' : SimSt S W K) (d : Dec S W K) : Prop where
  /-- Recorded long-term secrets are kept. -/
  lt_mono : ∀ p v, s.1.lt p = some v → s'.1.lt p = some v
  /-- The table of the sessions of the copy. -/
  sess : sessOf s'.1.st = sessDec (sessOf s.1.st) d
  /-- A key proposal at `x`. -/
  prop : ∀ (x : Inst) (k : K), (d = .inl (.inr (.newKey x.1 x.2 k)) ∨
      d = .inl (.inr (.newKeyUnlinked x.1 x.2 k))) →
    ∃ r ik, s'.1.st.recs x = some r ∧
      s'.1.lt (respOf x r.peer r.role) = some (ik, spkOf s'.1 x)

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- An outcome that keeps the table of the copy, with a decision that neither starts a session
nor proposes a key. -/
theorem startOk_keep (s : SimSt S W K) (rs : RSt S W K) (inp : Inst → Option (Inp W))
    (ph : Phase S W K) (d : Dec S W K) (hst : sessOf rs.st = sessOf s.1.st)
    (hlt : ∀ p v, s.1.lt p = some v → rs.lt p = some v)
    (hd : ∀ sid pid peer role, d ≠ .inl (.inl (.newSession sid pid peer role)))
    (hk : ∀ (x : Inst) (k : K), d ≠ .inl (.inr (.newKey x.1 x.2 k)) ∧
      d ≠ .inl (.inr (.newKeyUnlinked x.1 x.2 k))) :
    StartOk s (rs, inp, ph) d := by
  refine ⟨hlt, ?_, fun x k h => ?_⟩
  · rcases d with (h | a) | o
    · cases h with
      | newSession sid pid peer role => exact absurd rfl (hd sid pid peer role)
      | getKey => exact hst
    · exact hst
    · exact hst
  · rcases h with h | h
    · exact absurd h (hk x k).1
    · exact absurd h (hk x k).2

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- `pollStep` keeps the table of the sessions. -/
theorem sessOf_pollStep {K' : Type} (t : St K') : sessOf (pollStep t).1 = sessOf t := by
  unfold pollStep; split <;> rfl

omit [Fintype S] in
/-- The outcomes of `deliver` at the record `r` of `x` on a copy where the secrets of the party
of `x` and of its peer are drawn. -/
theorem deliver_startOk (s : SimSt S W K) (rs : RSt S W K) (inp : Inst → Option (Inp W))
    (x : Inst) (r : Rec K) (ip : Inp W) (hst : rs.st = s.1.st) (hr : s.1.st.recs x = some r)
    (hlt : ∀ p v, s.1.lt p = some v → rs.lt p = some v)
    (ha : ∃ v, rs.lt x.2 = some v) (hb : ∃ v, rs.lt r.peer = some v)
    {q : SimSt S W K × Dec S W K} (hq : IsOutcome (deliver rs inp x r ip) q) :
    StartOk s q.1 q.2 := by
  have hrs : rs.st.recs x = some r := hst ▸ hr
  have key : ∀ (k : K) ro (d : Dec S W K),
      (∀ h, d ≠ .inl (.inl h)) →
      (∀ (y : Inst) (k' : K), (d = .inl (.inr (.newKey y.1 y.2 k')) ∨
        d = .inl (.inr (.newKeyUnlinked y.1 y.2 k'))) → y = x) →
      StartOk s ((keyed rs x r k ro, Function.update inp x (some ip), Phase.out .ack)) d := by
    intro k ro d hd hy
    have hrec : (keyed rs x r k ro).st.recs x = some { r with key := some k } := by
      simp [keyed, setRec]
    refine ⟨hlt, ?_, fun y k' h => ?_⟩
    · rw [show (keyed rs x r k ro).st = setRec rs.st x { r with key := some k } from rfl,
        sessOf_setRec rs.st x r { r with key := some k } hrs rfl rfl, hst]
      rcases d with (h | a) | o
      · exact absurd rfl (hd h)
      · rfl
      · rfl
    · obtain rfl := hy y k' h
      have hd' : ∃ v, rs.lt (respOf y r.peer r.role) = some v := by
        unfold respOf; split
        · exact ha
        · exact hb
      obtain ⟨v, hv⟩ := hd'
      refine ⟨{ r with key := some k }, v.1, hrec, ?_⟩
      simp [spkOf, keyed, setRec, hv]
  unfold deliver at hq
  split at hq
  · obtain ⟨p, -, rfl⟩ := isOutcome_map_iff.mp hq
    exact key _ _ _ (fun _ h => by simp at h) (fun y k' h => by
      rcases h with h | h <;> grind)
  · obtain rfl := isOutcome_pure hq
    exact key _ _ _ (fun _ h => by simp at h) (fun y k' h => by
      split at h <;> rcases h with h | h <;> grind)

/-- **The start step of the simulator satisfies `StartOk`** at each of its outcomes. -/
theorem simStart_startOk (s : SimSt S W K) (e : OEv W) {q : SimSt S W K × Dec S W K}
    (hq : IsOutcome (simStart G s e) q) : StartOk s q.1 q.2 := by
  have hcd : ∀ {α β : Type} (c : SPComp α) (c' : α → SPComp β)
      (f : α → β → SPComp (SimSt S W K × Dec S W K)),
      (∀ a b q, IsOutcome c a → IsOutcome (c' a) b → IsOutcome (f a b) q →
        StartOk s q.1 q.2) → ∀ q,
      IsOutcome (SPComp.bind c fun a => SPComp.bind (c' a) (f a)) q → StartOk s q.1 q.2 := by
    intro α β c c' f hf q hq
    obtain ⟨a, ha, ha'⟩ := isOutcome_bind hq
    obtain ⟨b, hb, hb'⟩ := isOutcome_bind ha'
    exact hf a b q ha hb hb'
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · simp only [simStart] at hq
    split at hq
    · obtain ⟨y, -, rfl⟩ := isOutcome_map_iff.mp hq
      refine ⟨fun _ _ h => h, ?_, fun x k h => by simp at h⟩
      exact sessOf_addSession _ _ _ _
    · obtain rfl := isOutcome_pure hq
      refine ⟨fun _ _ h => h, ?_, fun x k h => by simp at h⟩
      rename_i hn
      have : addSession s.1.st (sid, pid) peer role = s.1.st := by
        unfold addSession; simp_all
      change sessOf s.1.st = noteSess (sessOf s.1.st) (sid, pid) peer role
      rw [← sessOf_addSession, this]
  · obtain rfl := isOutcome_pure hq
    exact startOk_keep _ _ _ _ _ rfl (fun _ _ h => h) (by simp) (by simp)
  · obtain rfl := isOutcome_pure hq
    exact startOk_keep _ _ _ _ _ rfl (fun _ _ h => h) (by simp) (by simp)
  · obtain rfl := isOutcome_pure hq
    exact startOk_keep _ _ _ _ _ (sessOf_pollStep _) (fun _ _ h => h) (by simp) (by simp)
  · obtain ⟨l, hl, rfl⟩ := isOutcome_map_iff.mp hq
    obtain ⟨h1, -, h3⟩ := ltStep_outcome s.1 pid hl
    exact startOk_keep _ _ _ _ _ (by rw [h1]) h3 (by simp) (by simp)
  · obtain rfl := isOutcome_pure hq
    exact startOk_keep _ _ _ _ _ rfl (fun _ _ h => h) (by simp) (by simp)
  · simp only [simStart, simCorrupt] at hq
    split at hq
    · obtain rfl := isOutcome_pure hq
      exact startOk_keep _ _ _ _ _ rfl (fun _ _ h => h) (by simp) (by simp)
    · obtain ⟨l, hl, rfl⟩ := isOutcome_map_iff.mp hq
      obtain ⟨h1, -, h3⟩ := ltStep_outcome s.1 pid hl
      refine startOk_keep _ _ _ _ _ ?_ h3 (by simp) (by simp)
      change sessOf (corruptStep l.2.st pid) = sessOf s.1.st
      rw [← h1]
      rfl
  · simp only [simStart, simComplete] at hq
    repeat' split at hq
    all_goals first
      | (obtain rfl := isOutcome_pure hq
         exact startOk_keep _ _ _ _ _ rfl (fun _ _ h => h) (by simp) (by simp))
      | refine hcd _ _ _ (fun la lb q' hla hlb hq' => ?_) q hq
    obtain ⟨a1, a2, a3⟩ := ltStep_outcome _ _ hla
    obtain ⟨b1, b2, b3⟩ := ltStep_outcome _ _ hlb
    exact deliver_startOk s lb.2 _ _ _ _ (by rw [b1, a1]) (by assumption)
      (fun p v h => b3 _ _ (a3 _ _ h)) ⟨_, b3 _ _ a2⟩ ⟨_, b2⟩ hq'
  · simp only [simStart, simSend] at hq
    repeat' split at hq
    all_goals first
      | (obtain rfl := isOutcome_pure hq
         exact startOk_keep _ _ _ _ _ rfl (fun _ _ h => h) (by simp) (by simp))
      | refine hcd _ _ _ (fun lb la q' hlb hla hq' => ?_) q hq
    obtain ⟨b1, b2, b3⟩ := ltStep_outcome _ _ hlb
    obtain ⟨a1, a2, a3⟩ := ltStep_outcome _ _ hla
    exact deliver_startOk s la.2 _ _ _ _ (by rw [a1, b1]) (by assumption)
      (fun p v h => a3 _ _ (b3 _ _ h)) ⟨_, a3 _ _ b2⟩ ⟨_, a2⟩ hq'
  · obtain ⟨p, -, rfl⟩ := isOutcome_map_iff.mp hq
    exact startOk_keep _ _ _ _ _ rfl (fun _ _ h => h) (by simp) (by simp)

/-- The datum of each key of `F` is the signed-prekey secret of the responder of its session
under the long-term secrets `L`. -/
def DatOk (L : PartyId → Option (S × S)) (F : St (K × S)) : Prop :=
  ∀ x r k d, F.recs x = some r → r.key = some (k, d) →
    ∃ ik, L (respOf x r.peer r.role) = some (ik, d)

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- `DatOk` under more recorded secrets. -/
theorem DatOk.mono {L L' : PartyId → Option (S × S)} {F : St (K × S)} (h : DatOk L F)
    (hL : ∀ p v, L p = some v → L' p = some v) : DatOk L' F := fun x r k d hr hk => by
  obtain ⟨ik, h'⟩ := h x r k d hr hk
  exact ⟨ik, hL _ _ h'⟩

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- `DatOk` depends only on the records. -/
theorem DatOk.of_recs {L : PartyId → Option (S × S)} {F F' : St (K × S)} (h : DatOk L F)
    (hr : F'.recs = F.recs) : DatOk L F' := fun x r k d h1 h2 => h x r k d (hr ▸ h1) h2

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- The start of a session keeps `DatOk`: the new record has no key. -/
theorem DatOk.addSession {L : PartyId → Option (S × S)} {F : St (K × S)} (h : DatOk L F)
    (x : Inst) (peer : PartyId) (role : Role) : DatOk L (addSession F x peer role) := by
  intro y r k d hr hk
  unfold FAKE.addSession at hr
  split at hr
  · exact h y r k d hr hk
  · by_cases hy : y = x
    · subst hy
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      simp at hk
    · exact h y r k d (by simpa [Function.update_of_ne hy] using hr) hk

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- The responder of a partner session is the responder of the session. -/
theorem respOf_partner {K' : Type} (x : Inst) (r p : Rec K') (hp : Partner x r p) :
    respOf (x.1, r.peer) p.peer p.role = respOf x r.peer r.role := by
  obtain ⟨h1, h2, -⟩ := hp
  unfold respOf
  cases hr : r.role <;> cases hpr : p.role <;> simp_all

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- The key that `newKey` gives to `x` has the datum of the responder of `x`. -/
theorem newKeyVal_datum {L : PartyId → Option (S × S)} {F : St (K × S)} (h : DatOk L F)
    (x : Inst) (r : Rec (K × S)) (k : K) (d₀ : S) (kf : K × S) (hkf : kf.2 = d₀)
    (hx : ∃ ik, L (respOf x r.peer r.role) = some (ik, d₀)) :
    ∃ ik, L (respOf x r.peer r.role) = some (ik, (newKeyVal F x r (k, d₀) kf).2) := by
  unfold newKeyVal
  split_ifs
  · exact hx
  · split
    · rename_i p hp
      split_ifs with hpp
      · rcases hpk : p.key with _ | ⟨k', d'⟩
        · simpa [hkf] using hx
        · obtain ⟨ik, h'⟩ := h _ p k' d' hp hpk
          rw [respOf_partner x r p hpp] at h'
          exact ⟨ik, by simpa using h'⟩
      · simpa [hkf] using hx
    · simpa [hkf] using hx

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- `newKey` with the datum of the responder keeps `DatOk`. -/
theorem DatOk.newKeyStep {L : PartyId → Option (S × S)} {F : St (K × S)} (h : DatOk L F)
    (x : Inst) (k : K) (d₀ : S) (kf : K × S) (hkf : kf.2 = d₀)
    (hx : ∀ r, F.recs x = some r → ∃ ik, L (respOf x r.peer r.role) = some (ik, d₀)) :
    DatOk L (newKeyStep F x (k, d₀) kf) := by
  intro y r' k' d' hr hk
  unfold FAKE.newKeyStep at hr
  split at hr
  · rename_i r0 hr0
    split at hr
    · by_cases hy : y = x
      · subst hy
        simp only [setRec, Function.update_self, Option.some.injEq] at hr
        subst hr
        simp only [Option.some.injEq] at hk
        obtain ⟨ik, h'⟩ := newKeyVal_datum h y r0 k d₀ kf hkf (hx r0 hr0)
        exact ⟨ik, by rw [h', hk]⟩
      · exact h y r' k' d' (by simpa [setRec, Function.update_of_ne hy] using hr) hk
    · exact h y r' k' d' hr hk
  · exact h y r' k' d' hr hk

omit [Fintype K] [Nonempty K] [Inhabited K] [Field S] [Fintype S] [SampleableType W] in
/-- `newKeyUnlinked` with the datum of the responder keeps `DatOk`. -/
theorem DatOk.newKeyFreshStep {L : PartyId → Option (S × S)} {F : St (K × S)} (h : DatOk L F)
    (x : Inst) (k : K) (d₀ : S) (kf : K × S) (hkf : kf.2 = d₀)
    (hx : ∀ r, F.recs x = some r → ∃ ik, L (respOf x r.peer r.role) = some (ik, d₀)) :
    DatOk L (newKeyFreshStep F x (k, d₀) kf) := by
  intro y r' k' d' hr hk
  unfold FAKE.newKeyFreshStep at hr
  split at hr
  · rename_i r0 hr0
    split at hr
    · by_cases hy : y = x
      · subst hy
        simp only [setRec, Function.update_self, Option.some.injEq] at hr
        subst hr
        obtain ⟨ik, h'⟩ := hx r0 hr0
        refine ⟨ik, ?_⟩
        simp only [Option.some.injEq] at hk
        split_ifs at hk <;> simp_all
      · exact h y r' k' d' (by simpa [setRec, Function.update_of_ne hy] using hr) hk
    · exact h y r' k' d' hr hk
  · exact h y r' k' d' hr hk

/-- **The invariant is preserved** by the steps of the simulated world with the datum. -/
theorem pairInv_pres (t : SimSt S W K × St (K × S)) (e : OEv W) (ht : PairInv t)
    (q : (SimSt S W K × St (K × S)) × (HOut (K × S) ⊕ ROut S W K))
    (hq : IsOutcome ((pairWorld (K := K) G).step t e) q) : PairInv q.1 := by
  rcases t with ⟨s, F⟩
  have hJ : sessOf s.1.st = sessOf F := funext ht.1
  have hD : DatOk s.1.lt F := ht.2
  rw [pairWorld, MultiHybrid.withSub_step_of_fuel_eq_zero _ _ rfl] at hq
  obtain ⟨⟨s', d'⟩, h1, h2⟩ := isOutcome_bind hq
  change IsOutcome (SPComp.map (fun q => (q.1, pairDec q.1 q.2)) (simStart G s e)) _ at h1
  obtain ⟨⟨s'', d⟩, hs, he⟩ := isOutcome_map_iff.mp h1
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hok := simStart_startOk G s e hs
  suffices hfin : ∀ F' : St (K × S), sessOf F' = sessDec (sessOf F) d → DatOk s''.1.lt F' →
      ∀ ph, PairInv ((s''.1, s''.2.1, ph), F') by
    have hD' : DatOk s''.1.lt F := hD.mono hok.lt_mono
    rcases d with (h | a) | o
    · simp only [pairDec, Sum.elim_inl, F_AKEK, Sys.ofPorts_step_inl, honSys, SPComp.map,
        SPComp.pure_bind, simProtPair] at h2
      obtain rfl := isOutcome_pure h2
      cases h with
      | newSession sid pid peer role =>
        exact hfin _ (sessOf_addSession _ _ _ _) (hD'.addSession _ _ _) _
      | getKey sid pid => exact hfin _ rfl hD' _
    · simp only [pairDec, Sum.elim_inl, simProtPair, SPComp.map, SPComp.pure_bind] at h2
      obtain ⟨q', hq', hq2⟩ := isOutcome_bind h2
      obtain rfl := isOutcome_pure hq2
      have hsF := (F_AKEK_adv_outcome _ _ _ q' hq').1
      have hx : ∀ (x : Inst) (k : K), (Sum.inl (Sum.inr a) : Dec S W K) =
          .inl (.inr (.newKey x.1 x.2 k)) ∨ (Sum.inl (Sum.inr a) : Dec S W K) =
          .inl (.inr (.newKeyUnlinked x.1 x.2 k)) →
          ∀ r, F.recs x = some r →
            ∃ ik, s''.1.lt (respOf x r.peer r.role) = some (ik, spkOf s''.1 x) := by
        intro x k hk r hr
        obtain ⟨rc, ik, hrc, hl⟩ := hok.prop x k hk
        change s''.1.st.recs x = some rc at hrc
        change s''.1.lt _ = some (ik, spkOf s''.1 x) at hl
        have hs2 := congrFun (hok.sess.trans hJ) x
        simp only [sessOf, hrc, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs2
        exact ⟨ik, by rw [← hs2.1, ← hs2.2]; exact hl⟩
      refine hfin _ hsF ?_ _
      simp only [F_AKEK, Sys.ofPorts_step_inr, advSysK] at hq'
      obtain ⟨p, hp, rfl⟩ := isOutcome_map_iff.mp hq'
      cases a with
      | idle => obtain rfl := isOutcome_pure hp; exact hD'
      | poll =>
        obtain rfl := isOutcome_pure hp
        exact hD'.of_recs (by unfold pollStep; split <;> rfl)
      | corrupt pid => obtain rfl := isOutcome_pure hp; exact hD'.of_recs rfl
      | impersonate sid pid => obtain rfl := isOutcome_pure hp; exact hD'
      | newKey sid pid k =>
        obtain ⟨kf, hkf, rfl⟩ := isOutcome_map_iff.mp hp
        obtain ⟨k₀, -, rfl⟩ := isOutcome_map_iff.mp hkf
        exact hD'.newKeyStep _ _ _ _ rfl (hx (sid, pid) k (Or.inl rfl))
      | newKeyUnlinked sid pid k =>
        obtain ⟨kf, hkf, rfl⟩ := isOutcome_map_iff.mp hp
        obtain ⟨k₀, -, rfl⟩ := isOutcome_map_iff.mp hkf
        exact hD'.newKeyFreshStep _ _ _ _ rfl (hx (sid, pid) k (Or.inr rfl))
    · simp only [pairDec] at h2
      rcases o with h | r
      · obtain rfl := isOutcome_pure h2
        exact hfin F rfl hD' _
      · obtain rfl := isOutcome_pure h2
        exact hfin F rfl hD' _
  intro F' hF' hD' ph
  refine ⟨fun x => congrFun (hok.sess.trans (hJ ▸ hF'.symm)) x, hD'⟩

/-- The oracle of the simulated game is the step of the simulated world. -/
theorem simOrc_lift (u : SimSt S W K × St K) (g : OEv W) :
    SPComp.map Prod.swap ((simWorld (K := K) G).step u g) =
      liftPMF ((simGame (K := K) G).oracle () u g) := by
  simp only [simGame, CatCrypt.Crypto.PAKE.CPaceSquare.pureGame]
  rw [← liftPMF_bind_pure, ← (simWorld_pureNF G u g).eq_liftPMF]
  rfl

/-- A step of `withPub` against the simulated game: the program of `withPub` run against the
steps of the simulated world. -/
theorem withPub_simStep (τ : SessT) (u : SimSt S W K × St K) (e : OEv W) :
    ((withPub (S := S) (K := K)).plug ((simGame (K := K) G).oracle ())
        (simGame (K := K) G).init).step (τ, u) e =
      SPComp.bind (CatCrypt.Crypto.Messaging.OracleAdv.runSP
        (fun u g => SPComp.map Prod.swap ((simWorld (K := K) G).step u g))
        ((withPub (S := S) (K := K)).step τ e) u) fun x => SPComp.pure ((x.1.1, x.2), x.1.2) := by
  rw [CatCrypt.Crypto.Messaging.OracleAdv.runSP_eq_liftPMF _ _ (simOrc_lift G)]
  simp only [OProt.plug_step, OProt.plugStep, sampleFrom_ofPMF_eq_liftPMF]
  with_unfolding_all rfl

/-- The simulated world on `getKey`: the key of the session in `F_AKE`. -/
theorem simWorld_getKey (u : SimSt S W K × St K) (sid : SessionId) (pid : PartyId) :
    (simWorld (K := K) G).step u (.inl (.getKey sid pid)) =
      SPComp.pure (((u.1.1, u.1.2.1, .fwd), u.2), .inl (.key (keyOf u.2 (sid, pid)))) := by
  rw [simWorld, MultiHybrid.withSub_step_of_fuel_eq_zero _ _ rfl]
  simp only [simProt, simStart, SPComp.pure_bind, Sum.elim_inl, F_AKE, F_AKEK,
    Sys.ofPorts_step_inl, honSys, honStep, SPComp.map, simOut]

/-- The simulated world on `pub p` when the long-term secrets of `p` are drawn: their public
keys, and no change but the phase. -/
theorem simWorld_pub (u : SimSt S W K × St K) (p : PartyId) (l : S × S)
    (hl : u.1.1.lt p = some l) :
    (simWorld (K := K) G).step u (.inr (.pub p)) =
      SPComp.pure (((u.1.1, u.1.2.1, .fwd), u.2), .inr (.pub (G.pub l.1) (G.pub l.2))) := by
  rw [simWorld, MultiHybrid.withSub_step_of_fuel_eq_zero _ _ rfl]
  simp only [simProt, simStart, ltStep, hl, SPComp.pure_bind, SPComp.map, Sum.elim_inr]

/-- The simulated world with the datum on `getKey`: the key of the session in `F_AKEK`. -/
theorem pairWorld_getKey (t : SimSt S W K × St (K × S)) (sid : SessionId) (pid : PartyId) :
    (pairWorld (K := K) G).step t (.inl (.getKey sid pid)) =
      SPComp.pure (((t.1.1, t.1.2.1, .fwd), t.2), .inl (.key (keyOf t.2 (sid, pid)))) := by
  rw [pairWorld, MultiHybrid.withSub_step_of_fuel_eq_zero _ _ rfl]
  simp only [simProtPair, simStart, SPComp.pure_bind, SPComp.map, pairDec, Sum.elim_inl,
    F_AKEK, Sys.ofPorts_step_inl, honSys, honStep, x3dhFwd, fwdOut, phaseOut]

/-- The X3DH simulator passes no honest event to the functionality on an adversary event. -/
theorem simStart_inr_noHonEv (s : SimSt S W K) (a : RAEv W) {q : SimSt S W K × Dec S W K}
    (hq : IsOutcome (simStart G s (.inr a)) q) (h : HEv) : q.2 ≠ .inl (.inl h) := by
  have hdel : ∀ (rs : RSt S W K) inp x r ip {q : SimSt S W K × Dec S W K},
      IsOutcome (deliver rs inp x r ip) q → q.2 ≠ .inl (.inl h) := by
    intro rs inp x r ip q hq
    unfold deliver at hq
    split at hq
    · obtain ⟨_, -, rfl⟩ := isOutcome_map_iff.mp hq; simp
    · rw [← isOutcome_pure hq]; simp
  have hdd : ∀ {α β : Type} (c : SPComp α) (c' : α → SPComp β)
      (f : α → β → SPComp (SimSt S W K × Dec S W K)),
      (∀ a b q, IsOutcome (f a b) q → q.2 ≠ .inl (.inl h)) → ∀ q,
      IsOutcome (SPComp.bind c fun a => SPComp.bind (c' a) (f a)) q → q.2 ≠ .inl (.inl h) := by
    intro α β c c' f hf q hq
    obtain ⟨a, -, ha⟩ := isOutcome_bind hq
    obtain ⟨b, -, hb⟩ := isOutcome_bind ha
    exact hf a b q hb
  rcases a with _ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x
  all_goals simp only [simStart, simCorrupt, simComplete, simSend] at hq
  all_goals (repeat' split at hq)
  all_goals first
    | (rw [← isOutcome_pure hq]; simp)
    | (obtain ⟨_, -, rfl⟩ := isOutcome_map_iff.mp hq; simp)
    | exact hdd _ _ _ (fun _ _ _ h' => hdel _ _ _ _ _ h') q hq

/-- **A step of the simulated world with the datum**, with the public signed prekey in place of
its secret, is a step of `withPub` against the simulated game, on the invariant. -/
theorem simPair_step (t : SimSt S W K × St (K × S)) (e : OEv W) (ht : PairInv t) :
    SPComp.map (fun p => (pairMap p.1, Sum.map (HOut.mapKey (pubKey G)) id p.2))
      ((pairWorld (K := K) G).step t e) =
    ((withPub (S := S) (K := K)).plug ((simGame (K := K) G).oracle ())
        (simGame (K := K) G).init).step (pairMap t) e := by
  rcases t with ⟨s, F⟩
  simp only [pairMap]
  erw [withPub_simStep]
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | a
  · rw [pairWorld, MultiHybrid.withSub_step_of_fuel_eq_zero _ _ rfl]
    simp only [withPub, Messaging.OracleAdv.runSP, simWorld,
      MultiHybrid.withSub_step_of_fuel_eq_zero (simProt G) _ rfl, simProtPair, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    refine bind_congr_isOutcome fun q hq => ?_
    have hd : q.2 = .inl (.inl (.newSession sid pid peer role)) := by
      simp only [simStart] at hq
      split at hq
      · obtain ⟨y, -, rfl⟩ := isOutcome_map_iff.mp hq; rfl
      · rw [← isOutcome_pure hq]
    rcases q with ⟨s', d⟩
    subst hd
    simp [pairDec, F_AKEK, F_AKE, Sys.ofPorts_step_inl, honSys, honStep, SPComp.map,
      SPComp.pure_bind, (simProt_isFwd G).finish_eq, x3dhFwd, fwdOut, sessOf_addSession,
      addSession_mapKey, phaseOut]
    rcases s'.2.2 <;> rfl
  · rw [pairWorld_getKey]
    simp only [withPub, Messaging.OracleAdv.runSP, simWorld_getKey, SPComp.map,
      SPComp.pure_bind, keyOf_mapKey]
    rcases hk : keyOf F (sid, pid) with _ | ⟨k, d⟩
    · simp [Messaging.OracleAdv.runSP, SPComp.pure_bind, HOut.mapKey]
    · obtain ⟨r, hr, hrk⟩ : ∃ r, F.recs (sid, pid) = some r ∧ r.key = some (k, d) := by
        unfold keyOf at hk
        cases h : F.recs (sid, pid) with
        | none => simp [h] at hk
        | some r => exact ⟨r, rfl, by simpa [h] using hk⟩
      obtain ⟨ik, hl⟩ := ht.2 _ r k d hr hrk
      have hs : sessOf F (sid, pid) = some (r.peer, r.role) := by simp [sessOf, hr]
      simp only [Prod.swap, Option.map_some, hs, Messaging.OracleAdv.runSP, SPComp.bind_assoc]
      rw [simWorld_pub G _ _ _ hl]
      simp only [SPComp.pure_bind]
      rw [Messaging.OracleAdv.runSP]
      simp [SPComp.pure_bind, HOut.mapKey, pubKey]
  · rw [pairWorld, MultiHybrid.withSub_step_of_fuel_eq_zero _ _ rfl]
    simp only [withPub, Messaging.OracleAdv.runSP, simWorld,
      MultiHybrid.withSub_step_of_fuel_eq_zero (simProt G) _ rfl, simProtPair, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    refine bind_congr_isOutcome fun q hq => ?_
    rcases q with ⟨s', (h | a') | o⟩
    · exact absurd rfl (simStart_inr_noHonEv G s a hq h)
    · have hF := F_AKEK_stepMap_mapKey (fresh := prekeyFresh K S)
        (fresh' := fun _ => SPComp.sample K) Prod.fst (fun p => sample_eq_map_prekeyFresh p)
        true F (.inr (pairEv s'.1 a'))
      simp only [Sum.map_inr, mapKey_pairEv] at hF
      have hF' : (F_AKE (SPComp.sample K) true).step (St.mapKey Prod.fst F) (.inr a') = _ :=
        hF.symm
      simp only [pairDec, Sum.elim_inl, hF', SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
        (simProt_isFwd G).finish_eq]
      refine bind_congr_isOutcome fun q hq' => ?_
      obtain ⟨h1, r, h2⟩ := F_AKEK_adv_outcome _ _ _ q hq'
      rcases q with ⟨F', o'⟩
      subst h2
      simp only [h1, x3dhFwd, fwdOut]
      cases phaseOut s'.2.2 <;> rfl
    · rcases o with h | r <;> simp [pairDec, SPComp.pure_bind]

/-- **The simulated side**: the simulator with the datum running with `F_AKEK`, followed by the
key layer of `L`, is `withPub` against the simulated game followed by the key layer of `Leff`,
on the invariant `PairInv`. -/
theorem simPair_stepMapOn {V : Type} (L : K × S → SPComp V) (Leff : K × W → SPComp V)
    (hL : ∀ k x₀, L (k, x₀) = Leff (k, G.pub x₀)) :
    Sys.StepMapOn
      (((simProtPair (K := K) G).withSub (F_AKEK (prekeyFresh K S) true)).seq (keyLayer L))
      (((withPub (S := S) (K := K)).plug ((simGame (K := K) G).oracle ())
        (simGame (K := K) G).init).seq (keyLayer Leff))
      (fun p => PairInv p.1) (Prod.map pairMap id) :=
  stepMapOn_seq_keyLayer (pubKey G) L Leff (fun k => hL k.1 k.2) PairInv pairMap
    (pairInv_init G) (pairMap_init G) (pairInv_pres G) (simPair_step G)

/-- The advantage of an oracle adversary between the real and the simulated X3DH games is at
most the gap Diffie–Hellman bound. -/
theorem advantage_le_gdhBound (P : Finset PartyId) (B : OracleAdv (OEv W) (OOut S W K) Bool) :
    KeyedGame.advantage (realGame (x3dhAlg G)) (simGame G) B ≤ gdhBound G P B := by
  by_cases hN : NamesIn P B
  · simp only [gdhBound, hN, ↓reduceIte]
    exact (X3DHSquareHops.x3dh_advantage_le_badGame G _).trans (badGame_le_gapDH G P _ hN)
  · simp only [gdhBound, hN, ↓reduceIte]
    exact le_top

/-- **X3DH with the prekey datum realizes `F_AKEK (prekeyFresh K S) true` behind the simulator
with the datum, under a layer that reads the datum through the public key.** For every finite
set of parties `P`, every layer of keyed views `L` with `L (k, s) = Leff (k, G.pub s)`, and every
environment `Z`, the distance between the real protocol with the datum followed by the key layer
of `L` and the simulator `simProtPair G` running with `F_AKEK` followed by the same layer is at
most the gap Diffie–Hellman bound `gdhBound G P` at the oracle reduction through `withPub` of the
environment `Z` reduced through the key layer of `Leff`. -/
theorem x3dhPair_seq_realizesSim (P : Finset PartyId) {V : Type} (L : K × S → SPComp V)
    (Leff : K × W → SPComp V) (hLeff : ∀ k, SPComp.NoFail (Leff k))
    (hL : ∀ k x₀, L (k, x₀) = Leff (k, G.pub x₀)) :
    Realizes ((x3dhRealPair (K := K) G).seq (keyLayer L))
      (((Simulator.ofMultiHybrid (simProtPair (K := K) G) (simProtPair_opaque G)).withSub
        (F_AKEK (prekeyFresh K S) true)).seq (keyLayer L))
      (fun _ Z => gdhBound G P ((withPub (S := S) (K := K)).reduction
        ((Hybrid.seqCtxR (E := OEv W) (keyLayer (R := ROut S W K) Leff)
          (keyLayer_noFail hLeff)).reduceEnv Z))) := by
  have hLnf : ∀ k, SPComp.NoFail (L k) := fun k => by rw [hL]; exact hLeff _
  have h₁ := realizes_seq_left (keyLayer (R := ROut S W K) L) (keyLayer_noFail hLnf)
    (sys_realizes_plug (OProt.oracle (Q := OEv W) (A := HOut (K × S) ⊕ ROut S W K))
      (realGamePair (K := K) (x3dhAlg G)) () (fun _ => rfl) rfl)
  have h₂ := (realPair_stepMapOn G L Leff hL).realizes
  have h₃ := realizes_seq_left (keyLayer (R := ROut S W K) Leff) (keyLayer_noFail hLeff)
    (realizes_symm (sys_realizes_plug (withPub (S := S) (K := K))
      (realGame (K := K) (x3dhAlg G)) () (fun _ => rfl) rfl))
  have h₄ := realizes_seq_left (keyLayer (R := ROut S W K) Leff) (keyLayer_noFail hLeff)
    (Realizes.ofOracleGame (withPub (S := S) (K := K)) (realGame (K := K) (x3dhAlg G))
      (simGame G))
  have h₅ := realizes_seq_left (keyLayer (R := ROut S W K) Leff) (keyLayer_noFail hLeff)
    (sys_realizes_plug (withPub (S := S) (K := K)) (simGame (K := K) G) () (fun _ => rfl) rfl)
  have h₆ := realizes_symm (simPair_stepMapOn G L Leff hL).realizes
  intro ζ Z
  refine ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆) ζ Z).trans ?_
  simp only [zero_add, add_zero]
  exact advantage_le_gdhBound G P _

end Square

end CatCrypt.Crypto.AKE.X3DHSquarePrekey

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquareGDH
public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.ForMathlib.PMFSupport
public import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The KEM route of the PQXDH square

Draft.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDHSquareKEM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp bobInp RSt ROut Named keyed ephPubOf opkOf
  rInit FEv FOut subView)
open CatCrypt.Crypto.AKE.X3DHSquareHops (drive0D Draw ltD fStepD skRec InpShape DhOk Exp
  ltD_lt_mono ltD_lt_self ltD_st ltD_eph ltD_ro pollStep_fst lookup_cons)
open CatCrypt.Crypto.AKE.X3DHSquareGDH (gapDHDef AllQ toOuterMeasure_le_one run_flag_true_one
  run_flag_le_final run_flag_union_le run_flag_le_of_inv_on stop_drive0D lookup_mem roDet_mem
  addSession_corrupt)
open CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.AKE.PQXDHSquareHops
open CatCrypt.Crypto.AKE.PQXDHSquareGDH
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.OracleGameUpToBad
open scoped ENNReal

/-! ## Eager sampling of a value used at most once -/

section Eager

variable {σ D R α X : Type}

/-- After the use, the oracle with the pre-sampled value is the lazy oracle. -/
theorem run_eager_used (O₁ : σ → D → PMF (R × σ)) (O₂ : X → σ → D → PMF (R × σ))
    (U : σ → Prop) (use : σ → D → Prop) (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (x : X) (A : OracleAdv D R α) (s : σ) (hs : ¬ U s) :
    OracleAdv.run (O₂ x) A s = OracleAdv.run O₁ A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.run_rand, fun b => ih b s hs]
  | query d k ih =>
    rw [OracleAdv.run_query, OracleAdv.run_query, hno x s d (hnu s d hs)]
    exact PMF.bind_congr_support _ _ _ fun y hy => ih y.1 y.2 (hpers s d hs y hy)

/-- **Eager sampling of a value used at most once.** The lazy oracle `O₁` draws a value of `ν`
at the step that uses it (`use`), and the oracle `O₂ x` reads the pre-sampled value `x` there
and agrees with `O₁` elsewhere. When the use happens only from states where the value is
unused (`U`), makes it used, and a used value stays used, a run of `O₁` from an unused state is
the run of `O₂ x` for `x` drawn from `ν` first. -/
theorem run_eager (ν : PMF X) (O₁ : σ → D → PMF (R × σ)) (O₂ : X → σ → D → PMF (R × σ))
    (U : σ → Prop) (use : σ → D → Prop) (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (huse : ∀ s d, U s → use s d → O₁ s d = ν.bind fun x => O₂ x s d)
    (hnext : ∀ x s d, U s → use s d → ∀ y ∈ (O₂ x s d).support, ¬ U y.2)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (A : OracleAdv D R α) (s : σ) (hs : U s) :
    OracleAdv.run O₁ A s = ν.bind fun x => OracleAdv.run (O₂ x) A s := by
  induction A generalizing s with
  | ret a => rw [OracleAdv.run_ret]; simp only [OracleAdv.run_ret, PMF.bind_const]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, fun b => ih b s hs]
    exact PMF.bind_comm _ _ _
  | query d k ih =>
    simp only [OracleAdv.run_query]
    by_cases hu : use s d
    · rw [huse s d hs hu, PMF.bind_bind]
      refine PMF.bind_congr_support _ _ _ fun x _ => ?_
      refine PMF.bind_congr_support _ _ _ fun y hy => ?_
      exact (run_eager_used O₁ O₂ U use hno hpers hnu x _ _ (hnext x s d hs hu y hy)).symm
    · simp only [hno _ s d hu]
      rw [PMF.bind_comm]
      refine PMF.bind_congr_support _ _ _ fun y _ => ?_
      by_cases hy : U y.2
      · exact ih y.1 y.2 hy
      · simp only [run_eager_used O₁ O₂ U use hno hpers hnu _ _ _ hy, PMF.bind_const]

/-- `run_eager` for flagged oracles whose bad event reads the reached state. -/
theorem run_eager_flag (ν : PMF X) (O₁ : σ → D → PMF (R × σ)) (O₂ : X → σ → D → PMF (R × σ))
    (bad : σ → Prop) [DecidablePred bad]
    (U : σ → Prop) (use : σ → D → Prop) (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (huse : ∀ s d, U s → use s d → O₁ s d = ν.bind fun x => O₂ x s d)
    (hnext : ∀ x s d, U s → use s d → ∀ y ∈ (O₂ x s d).support, ¬ U y.2)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (A : OracleAdv D R α) (s : σ) (hs : U s) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ y => bad y.2) O₁) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} =
      ∑' x, ν x * (OracleAdv.run (OracleAdv.flagWhen (fun _ _ y => bad y.2) (O₂ x)) A
        (s, false)).toOuterMeasure {y | y.2.2 = true} := by
  rw [run_eager ν _ (fun x => OracleAdv.flagWhen (fun _ _ y => bad y.2) (O₂ x))
    (fun t => U t.1) (fun t d => use t.1 d) _ _ _ _ _ A (s, false) hs,
    PMF.toOuterMeasure_bind_apply]
  · intro x t d h
    simp only [OracleAdv.flagWhen, hno x t.1 d h]
  · intro t d ht h
    simp only [OracleAdv.flagWhen, huse t.1 d ht h, PMF.map_bind]
  · intro x t d ht h y hy
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hnext x t.1 d ht h z hz
  · intro t d ht y hy
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hpers t.1 d ht z hz
  · exact fun t d ht => hnu t.1 d ht

end Eager

/-! ## Bad flags under a coupling up to a second bad event -/

section HitCoupling

variable {σ₁ σ₂ D R α Ω : Type}

/-- **A bad flag under a coupling up to the bad event of the second oracle.** Two oracles are
images of draws from distributions that agree on related states. Every step from related states
either reaches a state of the second oracle with its bad event, or gives the same answer and
reaches related states; the bad event of the first oracle on related states implies that of the
second. Then the first run sets its flag with at most the probability with which the second
does. -/
theorem flag_le_of_coupling_hit (μ₁ : σ₁ → D → PMF Ω) (μ₂ : σ₂ → D → PMF Ω)
    (f₁ : σ₁ → D → Ω → R × σ₁) (f₂ : σ₂ → D → Ω → R × σ₂)
    (Rel : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop) [DecidablePred bad₁]
    [DecidablePred bad₂] (hμ : ∀ s₁ s₂ d, Rel s₁ s₂ → μ₁ s₁ d = μ₂ s₂ d)
    (hbad : ∀ s₁ s₂, Rel s₁ s₂ → bad₁ s₁ → bad₂ s₂)
    (hstep : ∀ s₁ s₂ d r, Rel s₁ s₂ → bad₂ (f₂ s₂ d r).2 ∨
      ((f₁ s₁ d r).1 = (f₂ s₂ d r).1 ∧ Rel (f₁ s₁ d r).2 (f₂ s₂ d r).2))
    (A : OracleAdv D R α) (s₁ : σ₁) (s₂ : σ₂) (h : Rel s₁ s₂) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₁ x.2)
      (fun s d => (μ₁ s d).map (f₁ s d))) A (s₁, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₂ x.2)
      (fun s d => (μ₂ s d).map (f₂ s d))) A (s₂, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  induction A generalizing s₁ s₂ with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    rw [OracleAdv.run_rand, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun b => ?_
    gcongr
    exact ih b s₁ s₂ h
  | query d k ih =>
    rw [OracleAdv.run_query, OracleAdv.run_query, flagWhen_map, flagWhen_map,
      PMF.bind_map, PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply,
      hμ s₁ s₂ d h]
    refine ENNReal.tsum_le_tsum fun r => ?_
    gcongr
    simp only [Function.comp_apply, Bool.false_or]
    rcases hstep s₁ s₂ d r h with hb | ⟨ho, hr⟩
    · rw [decide_eq_true hb, run_flag_true_one]
      exact toOuterMeasure_le_one _ _
    · by_cases hb₂ : bad₂ (f₂ s₂ d r).2
      · rw [decide_eq_true hb₂, run_flag_true_one]
        exact toOuterMeasure_le_one _ _
      · have hb₁ : ¬ bad₁ (f₁ s₁ d r).2 := fun hb => hb₂ (hbad _ _ hr hb)
        rw [decide_eq_false hb₁, decide_eq_false hb₂, ho]
        exact ih _ _ _ hr

end HitCoupling

/-! ## Records along a step of the simulator -/

section Frame

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The records of `st'` extend those of `st`: every record keeps its peer, role and status,
and a delivered key; a new record is a fresh session without a key started by the event `e`;
and no corruption is cleared. -/
def Frame (e : OEv W SS C) (st st' : St K) : Prop :=
  (∀ z r, st.recs z = some r → ∃ r', st'.recs z = some r' ∧ r'.peer = r.peer ∧
    r'.role = r.role ∧ r'.status = r.status ∧ (r.key.isSome → r'.key = r.key)) ∧
  (∀ z r', st'.recs z = some r' → st.recs z = none →
    e = .inl (.newSession z.1 z.2 r'.peer r'.role) ∧ r'.status = .fresh ∧ r'.key = none) ∧
  (∀ p, st.corrupt p = true → st'.corrupt p = true)

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
theorem frame_refl (e : OEv W SS C) (st : St K) : Frame e st st :=
  ⟨fun _ r h => ⟨r, h, rfl, rfl, rfl, fun _ => rfl⟩, fun _ _ h h' => by simp [h] at h',
    fun _ h => h⟩

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- Setting the key of a session without a key. -/
theorem frame_setRec (e : OEv W SS C) (st : St K) (x : Inst) (r : Rec K) (k : K)
    (hx : st.recs x = some r) (hk : r.key = none) :
    Frame e st (setRec st x { r with key := some k }) := by
  refine ⟨fun z r₀ hz => ?_, fun z r' hz hn => ?_, fun _ h => h⟩
  · by_cases hzx : z = x
    · subst hzx
      rw [hx] at hz
      cases hz
      exact ⟨{ r with key := some k }, by simp [setRec], rfl, rfl, rfl, fun h => by simp [hk] at h⟩
    · exact ⟨r₀, by simp [setRec, Function.update_of_ne hzx, hz], rfl, rfl, rfl, fun _ => rfl⟩
  · by_cases hzx : z = x
    · subst hzx; rw [hx] at hn; cases hn
    · simp only [setRec, Function.update_of_ne hzx] at hz; rw [hz] at hn; cases hn

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] in
/-- The delivery of a key to a session without a key. -/
theorem deliverD_frame (e : OEv W SS C) {st : St K} (s : PSt S W K PK SK SS C)
    (inp : Inst → Option (PInp W SS)) (x : Inst) (r : Rec K) (ip : PInp W SS) (k : K)
    (hst : s.x.st = st) (hx : st.recs x = some r) (hk : r.key.isNone = true) :
    Frame e st (deliverD s inp x r ip k).1.1.x.st := by
  subst hst
  unfold deliverD
  split <;> exact frame_setRec e _ x r _ hx (Option.isNone_iff_eq_none.mp hk)

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **The frame of a step of the simulator.** -/
theorem simStartD_frame (s : SimSt S W K PK SK SS C) (e : OEv W SS C)
    (d : PDraw S K PK SK SS C) : Frame e s.1.x.st (simStartD P G s e d).1.1.x.st := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | q)
  · simp only [simStartD]
    by_cases h : (s.1.x.st.recs (sid, pid)).isNone = true
    · have hadd : Frame (.inl (.newSession sid pid peer role) : OEv W SS C) s.1.x.st
          (addSession s.1.x.st (sid, pid) peer role) := by
        have hn : s.1.x.st.recs (sid, pid) = none := Option.isNone_iff_eq_none.mp h
        refine ⟨fun z r₀ hz => ?_, fun z r' hz hz' => ?_, fun p hp => ?_⟩
        · have hzx : z ≠ (sid, pid) := fun hc => by rw [hc, hn] at hz; cases hz
          refine ⟨r₀, ?_, rfl, rfl, rfl, fun _ => rfl⟩
          simp [addSession, hn, Function.update_of_ne hzx, hz]
        · by_cases hzx : z = (sid, pid)
          · subst hzx
            simp only [addSession, hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              Function.update_self, Option.some.injEq] at hz
            subst hz
            exact ⟨rfl, rfl, rfl⟩
          · simp only [addSession, hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              Function.update_of_ne hzx] at hz
            rw [hz] at hz'; cases hz'
        · rw [addSession_corrupt]; exact hp
      simp only [h, ↓reduceIte]
      split
      · exact hadd
      · exact hadd
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact frame_refl _ _
  · exact frame_refl _ _
  · exact frame_refl _ _
  · simp only [simStartD]
    rw [show (pollStep s.1.x.st).1 = { s.1.x.st with cursor := (pollStep s.1.x.st).1.cursor }
      from by unfold pollStep; split <;> rfl]
    exact frame_refl _ _
  · simp only [simStartD, ltD_st]; exact frame_refl _ _
  · exact frame_refl _ _
  · exact frame_refl _ _
  · simp only [simStartD]
    split
    · exact frame_refl _ _
    · refine ⟨fun z r h => ⟨r, by simpa [corruptStep] using h, rfl, rfl, rfl, fun _ => rfl⟩,
        fun z r' h h' => by simp [corruptStep, h'] at h, fun p hp => ?_⟩
      simp only [corruptStep, ltD_st]
      by_cases hp' : p = pid
      · subst hp'; simp
      · rw [Function.update_of_ne hp']; exact hp
  · simp only [simStartD, simCompleteD]
    split
    · rename_i r ek hr he
      split
      · split
        · rename_i hc
          exact deliverD_frame _ _ _ _ _ _ _ (by simp only [ltD_st]) hr hc.2
        · exact frame_refl _ _
      · exact frame_refl _ _
    · exact frame_refl _ _
  · simp only [simStartD, simSendD]
    split
    · rename_i r opk kp hr he hk
      split
      · split
        · rename_i hc
          exact deliverD_frame _ _ _ _ _ _ _ (by simp only [ltD_st]) hr hc.2
        · exact frame_refl _ _
      · exact frame_refl _ _
    · exact frame_refl _ _
  · simp only [simStartD]; exact frame_refl _ _

end Frame

/-! ## The matched KEM part of the bad event -/

section Split

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The session `y` with record `r` is matched: it is an initiator, or its partner, the
session `(y.1, r.peer)`, is an initiator whose peer is `y.2`. The partner of a matched responder
encapsulates to the KEM public key of the responder. -/
def Matched (t : SimSt S W K PK SK SS C) (y : Inst) (r : Rec K) : Prop :=
  r.role = .initiator ∨
    ∃ ri, t.1.x.st.recs (y.1, r.peer) = some ri ∧ ri.role = .initiator ∧ ri.peer = y.2

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The matched KEM part of the bad event**: `PQHit` at a matched session whose encapsulation
the adversary did not create. -/
def PQHitKemM (t : SimSt S W K PK SK SS C) (dlv : Inst → Option C) : Prop :=
  ∃ y r ip v, t.1.x.st.recs y = some r ∧ t.2.1 y = some ip ∧ t.1.ro.lookup ip = some v ∧
    t.1.x.st.corrupt y.2 = false ∧ t.1.x.st.corrupt r.peer = false ∧ InpShape y r ip.1 ∧
    DhOk G t.1.x.lt ip.1 ∧ KemOk P t.1 dlv y r ip ∧ HonestEnc t dlv y r ∧ Matched t y r

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The Diffie–Hellman part of the bad event at unmatched sessions**: `PQHit` at a session
whose encapsulation the adversary created or whose partner does not encapsulate to it. -/
def PQHitDhM (t : SimSt S W K PK SK SS C) (dlv : Inst → Option C) : Prop :=
  ∃ y r ip v, t.1.x.st.recs y = some r ∧ t.2.1 y = some ip ∧ t.1.ro.lookup ip = some v ∧
    t.1.x.st.corrupt y.2 = false ∧ t.1.x.st.corrupt r.peer = false ∧ InpShape y r ip.1 ∧
    DhOk G t.1.x.lt ip.1 ∧ KemOk P t.1 dlv y r ip ∧ ¬ (HonestEnc t dlv y r ∧ Matched t y r)

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
theorem pqHit_splitM {t : SimSt S W K PK SK SS C} {dlv : Inst → Option C}
    (h : PQHit P G t dlv) : PQHitKemM P G t dlv ∨ PQHitDhM P G t dlv := by
  obtain ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
  by_cases hk : HonestEnc t dlv y r ∧ Matched t y r
  · exact Or.inl ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, hk.1, hk.2⟩
  · exact Or.inr ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, hk⟩

open Classical in
/-- **The bad event is at most its matched KEM part plus the rest.** -/
theorem badGame_le_splitM (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    badGame P G B true ≤ partBad P G (PQHitKemM P G) B + partBad P G (PQHitDhM P G) B := by
  unfold badGame partBad
  rw [map_flag_apply]
  refine (OracleAdv.run_flagWhen_mono (jointSim P G) _
    (fun _ _ x => PQHitKemM P G x.2.1.1.1 x.2.1.2.2 ∨ PQHitDhM P G x.2.1.1.1 x.2.1.2.2)
    (fun _ _ _ h => pqHit_splitM P G h) B _).trans ?_
  exact OracleAdv.run_flagWhen_or_le (jointSim P G) _ _ B _

open Classical in
/-- **Both parts under the gap Diffie–Hellman assumption.** -/
theorem partBadM_le_gapDH (N : Finset PartyId)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) (hB : NamesInP N B) :
    partBad P G (PQHitKemM P G) B ≤
        ∑ a ∈ N, ∑ b ∈ N, GapDH_Advantage (gapDHDef G) (pqGdhRed G P a b B) ∧
      partBad P G (PQHitDhM P G) B ≤
        ∑ a ∈ N, ∑ b ∈ N, GapDH_Advantage (gapDHDef G) (pqGdhRed G P a b B) := by
  refine ⟨jointFlag_le_gapDH P G (PQHitKemM P G)
    (fun _ dlv h => pqHit_dh1 P G (dlv := dlv) ?_) N B hB,
    jointFlag_le_gapDH P G (PQHitDhM P G) (fun _ dlv h => pqHit_dh1 P G (dlv := dlv) ?_) N B hB⟩
  · obtain ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, -⟩ := h
    exact ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  · obtain ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, -⟩ := h
    exact ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

end Split

/-! ## The simulated world with the record of delivered encapsulations -/

section World

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- The state of the simulated world with the record of delivered encapsulations. -/
abbrev WSt (S W K PK SK SS C : Type) :=
  (SimSt S W K PK SK SS C × St K) × (Inst → Option C)

/-- A step of the simulated world with the record of delivered encapsulations, on the draw
`r`. -/
def wStep (t : WSt S W K PK SK SS C) (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) :
    OOut S W K PK C × WSt S W K PK SK SS C :=
  ((simWorldD P G t.1 e r).2, ((simWorldD P G t.1 e r).1, dlvStep t.1.1 e t.2))

/-- The oracle of the simulated world with the record of delivered encapsulations. -/
noncomputable def wO (t : WSt S W K PK SK SS C) (e : OEv W SS C) :
    PMF (OOut S W K PK C × WSt S W K PK SK SS C) :=
  (simDist P (encPk t.1.1.1 e)).map (wStep P G t e)

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS] in
/-- The initial state. -/
def wInit : WSt S W K PK SK SS C := (((pInit, fun _ => none, .fwd), initSt), fun _ => none)

/-- The joint world, read at the simulated world and the record of delivered encapsulations,
is `wO`. -/
theorem jointSim_map_w (s : JSt S W K PK SK SS C) (e : OEv W SS C) :
    (jointSim P G s e).map (Prod.map id fun s' => (s'.1.1, s'.1.2.2)) =
      wO P G (s.1.1, s.1.2.2) e := by
  rw [jointSim, PMF.map_comp, wO,
    ← jDist_map_simOf P (encPk s.1.2.1 e) (encPk s.1.1.1.1 e), PMF.map_comp]
  rfl

open Classical in
/-- **A part of the bad event in the simulated world.** -/
theorem partBad_eq_w (E : SimSt S W K PK SK SS C → (Inst → Option C) → Prop)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    partBad P G E B = (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => E x.2.1.1 x.2.2)
      (wO P G)) B (wInit, false)).toOuterMeasure {y | y.2.2 = true} := by
  have hO : ∀ (st : JSt S W K PK SK SS C × Bool) (d : OEv W SS C),
      (OracleAdv.flagWhen (fun _ _ x => E x.2.1.1.1 x.2.1.2.2) (jointSim P G) st d).map
          (Prod.map id fun st => ((st.1.1.1, st.1.1.2.2), st.2)) =
        OracleAdv.flagWhen (fun _ _ x => E x.2.1.1 x.2.2) (wO P G)
          ((st.1.1.1, st.1.1.2.2), st.2) d := by
    intro st d
    simp only [OracleAdv.flagWhen]
    rw [← jointSim_map_w P G st.1 d, PMF.map_comp, PMF.map_comp]
    rfl
  have h := congrArg (fun p => PMF.toOuterMeasure p {y | y.2.2 = true})
    (OracleAdv.run_map_state _ _ _ hO B (jointInit, false))
  simp only [PMF.toOuterMeasure_map_apply] at h
  exact h

end World

/-! ## Guessing the session of the KEM part -/

section Guess

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- A guess of the session attacked through the KEM: the session identifier, the initiator and
the responder. -/
abbrev Guess := SessionId × PartyId × PartyId

/-- The initiator session of a guess. -/
def gI (g : Guess) : Inst := (g.1, g.2.1)

/-- The responder session of a guess. -/
def gR (g : Guess) : Inst := (g.1, g.2.2)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The session `y` with record `r` is a session of the guess `g`: its initiator session with
peer the responder, or its responder session with peer the initiator, whose initiator session
has the responder as peer. -/
def AtGuess (g : Guess) (t : SimSt S W K PK SK SS C) (y : Inst) (r : Rec K) : Prop :=
  (y = gI g ∧ r.role = .initiator ∧ r.peer = g.2.2) ∨
    (y = gR g ∧ r.role = .responder ∧ r.peer = g.2.1 ∧
      ∃ ri, t.1.x.st.recs (gI g) = some ri ∧ ri.role = .initiator ∧ ri.peer = g.2.2)

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The KEM part of the bad event at the guess `g`.** -/
def EG (g : Guess) (t : SimSt S W K PK SK SS C) (dlv : Inst → Option C) : Prop :=
  ∃ y r ip v, t.1.x.st.recs y = some r ∧ t.2.1 y = some ip ∧ t.1.ro.lookup ip = some v ∧
    t.1.x.st.corrupt y.2 = false ∧ t.1.x.st.corrupt r.peer = false ∧ InpShape y r ip.1 ∧
    DhOk G t.1.x.lt ip.1 ∧ KemOk P t.1 dlv y r ip ∧ HonestEnc t dlv y r ∧ AtGuess g t y r

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- An event names session identifiers of `I` and parties of `N` where it starts a session. -/
def EvInK (I : Finset SessionId) (N : Finset PartyId) : OEv W SS C → Prop
  | .inl (.newSession sid pid peer _) => sid ∈ I ∧ pid ∈ N ∧ peer ∈ N
  | _ => True

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- **The finite-session predicate**: on every path, the oracle adversary `B` starts sessions
only with session identifiers of `I` between parties of `N`. -/
def SessInK {α : Type} (I : Finset SessionId) (N : Finset PartyId)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) α) : Prop :=
  AllQ (EvInK I N) B

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The invariant of the sessions: every record names a session identifier of `I` and parties
of `N`. -/
def InvK (I : Finset SessionId) (N : Finset PartyId) (t : SimSt S W K PK SK SS C) : Prop :=
  ∀ z r, t.1.x.st.recs z = some r → z.1 ∈ I ∧ z.2 ∈ N ∧ r.peer ∈ N

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
theorem invK_frame {I : Finset SessionId} {N : Finset PartyId} {e : OEv W SS C}
    {t t' : SimSt S W K PK SK SS C} (h : InvK I N t) (he : EvInK I N e)
    (hf : Frame e t.1.x.st t'.1.x.st) : InvK I N t' := by
  intro z r hz
  cases hz₀ : t.1.x.st.recs z with
  | none =>
    obtain ⟨rfl, -, -⟩ := hf.2.1 z r hz hz₀
    exact he
  | some r₀ =>
    obtain ⟨r', hr', hp, -⟩ := hf.1 z r₀ hz₀
    rw [hz] at hr'
    cases hr'
    rw [hp]
    exact h z r₀ hz₀

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The simulated copy reached by a step of the simulated world is the one reached by the start
of the simulator. -/
theorem simWorldD_fst (t : SimSt S W K PK SK SS C × St K) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) :
    (simWorldD P G t e r).1.1.1 = (simStartD P G t.1 e r.1).1.1 := by
  simp only [simWorldD]
  rw [stop_drive0D _ _ (fun _ _ => rfl)]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The recorded inputs reached by a step of the simulated world are those reached by the start
of the simulator. -/
theorem simWorldD_inp (t : SimSt S W K PK SK SS C × St K) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) :
    (simWorldD P G t e r).1.1.2.1 = (simStartD P G t.1 e r.1).1.2.1 := by
  simp only [simWorldD, drive0D]
  split <;> rfl

theorem invK_wO {I : Finset SessionId} {N : Finset PartyId} (t : WSt S W K PK SK SS C)
    (e : OEv W SS C) (ht : InvK I N t.1.1) (he : EvInK I N e) :
    ∀ x ∈ (wO P G t e).support, InvK I N x.2.1.1 := by
  intro x hx
  simp only [wO, PMF.support_map, Set.mem_image] at hx
  obtain ⟨r, -, rfl⟩ := hx
  refine invK_frame ht he ?_
  simp only [wStep]
  rw [show (simWorldD P G t.1 e r).1.1.1.x.st = (simStartD P G t.1.1 e r.1).1.1.x.st by
    rw [simWorldD_fst]]
  exact simStartD_frame P G t.1.1 e r.1

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- On the invariant of the sessions, the matched KEM part of the bad event is the KEM part at a
guess of `I × N × N`. -/
theorem pqHitKemM_guess {I : Finset SessionId} {N : Finset PartyId}
    {t : SimSt S W K PK SK SS C} {dlv : Inst → Option C} (hI : InvK I N t)
    (h : PQHitKemM P G t dlv) : ∃ g ∈ I ×ˢ N ×ˢ N, EG P G g t dlv := by
  obtain ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := h
  obtain ⟨hs, hp, hq⟩ := hI y r h₁
  by_cases hi : r.role = .initiator
  · refine ⟨(y.1, y.2, r.peer), by simp [hs, hp, hq], y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      h₈, h₉, Or.inl ⟨rfl, hi, rfl⟩⟩
  · have hresp : r.role = .responder := by cases h : r.role <;> simp_all
    obtain ⟨ri, hri, hrr, hrp⟩ := h₁₀.resolve_left hi
    refine ⟨(y.1, r.peer, y.2), by simp [hs, hp, hq], y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      h₈, h₉, Or.inr ⟨rfl, hresp, rfl, ri, hri, hrr, hrp⟩⟩

open Classical in
/-- **Guessing the session.** For an adversary that starts sessions only with session
identifiers of `I` between parties of `N`, the matched KEM part of the bad event is at most the
sum over the guesses of `I × N × N` of the KEM part at the guess. -/
theorem partBad_le_sum_guess (I : Finset SessionId) (N : Finset PartyId)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) (hB : SessInK I N B) :
    partBad P G (PQHitKemM P G) B ≤ ∑ g ∈ I ×ˢ N ×ˢ N,
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => EG P G g x.2.1.1 x.2.2) (wO P G)) B
        (wInit, false)).toOuterMeasure {y | y.2.2 = true} := by
  rw [partBad_eq_w]
  have h₁ := run_flag_le_of_inv_on (wO P G) (EvInK I N) (fun t => InvK I N t.1.1)
    (fun t => PQHitKemM P G t.1.1 t.2) (fun t => ∃ g ∈ I ×ˢ N ×ˢ N, EG P G g t.1.1 t.2)
    (fun t e ht he => invK_wO P G t e ht he) (fun t ht hk => pqHitKemM_guess P G ht hk) B hB
    wInit (fun _ _ h => by cases h)
  exact h₁.trans (run_flag_union_le (wO P G) (fun g t => EG P G g t.1.1 t.2) _ B wInit)

end Guess

/-! ## Draws of the challenge -/

section DrawLemmas

variable {S K PK SK SS C : Type} [Fintype S] [Nonempty S] [Fintype K] [Nonempty K]
  (P : Scheme PK SK SS C)

/-- The KEM key pair of a draw without a public key is a draw of `P.keygen`. -/
theorem simDist_none_eager {γ : Type} (F : PDraw S K PK SK SS C × K → γ) :
    (simDist P none).map F = P.keygen.bind fun x =>
      (simDist P none).map fun r => F ((r.1.1, x, r.1.2.2), r.2) := by
  simp only [simDist, pDist, encD, PMF.map_bind, PMF.bind_bind, PMF.map_comp,
    PMF.pure_bind, PMF.pure_map, Function.comp_def]
  rw [PMF.bind_comm]
  refine PMF.bind_congr_support _ _ _ fun r _ => ?_
  simp only [PMF.bind_const]

/-- The encapsulation of a draw with the public key `pk` is a draw of `P.encaps pk`. -/
theorem simDist_some_eager {γ : Type} (pk : PK) (F : PDraw S K PK SK SS C × K → γ) :
    (simDist P (some pk)).map F = (P.encaps pk).bind fun x =>
      (simDist P (some pk)).map fun r => F ((r.1.1, r.1.2.1, some x), r.2) := by
  simp only [simDist, pDist, encD, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, PMF.bind_const]
  symm
  rw [PMF.bind_comm]
  refine PMF.bind_congr_support _ _ _ fun a _ => ?_
  rw [PMF.bind_comm]

end DrawLemmas

/-! ## The worlds with the challenge sampled eagerly -/

section EagerWorld

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)
  (g : Guess)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The event `e` starts the responder session of the guess `g`. -/
def isCreate (t : SimSt S W K PK SK SS C) : OEv W SS C → Bool
  | .inl (.newSession sid pid _ role) =>
    decide (sid = g.1 ∧ pid = g.2.2 ∧ role = .responder) && (t.1.x.st.recs (sid, pid)).isNone
  | _ => false

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
open Classical in
/-- The event `e` completes the initiator session of the guess `g`, with peer the responder of
`g`, by an encapsulation to the public key `pk`. -/
noncomputable def isEnc (pk : PK) (t : SimSt S W K PK SK SS C) : OEv W SS C → Bool
  | .inr (.complete sid pid) =>
    decide (sid = g.1 ∧ pid = g.2.1) &&
      match t.1.x.st.recs (sid, pid), t.1.x.eph (sid, pid) with
      | some r, some _ =>
        decide (r.peer = g.2.2 ∧ (opkOf t.1.x sid r.peer).isSome ∧
          pkOf t.1 sid r.peer = some pk ∧ r.role = .initiator ∧ r.key = none)
      | _, _ => false
  | _ => false

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The draw with the KEM key pair `kp` at the start of the responder session of `g`. -/
def subKP (kp : PK × SK) (t : SimSt S W K PK SK SS C) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) : PDraw S K PK SK SS C × K :=
  ((r.1.1, if isCreate g t e then kp else r.1.2.1, r.1.2.2), r.2)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The draw with the encapsulation `kc` at the completion of the initiator session of `g`. -/
noncomputable def subKC (pk : PK) (kc : SS × C) (t : SimSt S W K PK SK SS C) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) : PDraw S K PK SK SS C × K :=
  ((r.1.1, r.1.2.1, if isEnc g pk t e then some kc else r.1.2.2), r.2)

/-- The simulated world with the KEM key pair `kp` of the responder session of `g`. -/
noncomputable def gw1O (kp : PK × SK) (t : WSt S W K PK SK SS C) (e : OEv W SS C) :
    PMF (OOut S W K PK C × WSt S W K PK SK SS C) :=
  (simDist P (encPk t.1.1.1 e)).map fun r => wStep P G t e (subKP g kp t.1.1 e r)

/-- **The simulated world with the challenge sampled eagerly**: the KEM key pair `kp` of the
responder session of `g` and the encapsulation `kc` of its initiator session. -/
noncomputable def gwO (kp : PK × SK) (kc : SS × C) (t : WSt S W K PK SK SS C)
    (e : OEv W SS C) : PMF (OOut S W K PK C × WSt S W K PK SK SS C) :=
  (simDist P (encPk t.1.1.1 e)).map fun r =>
    wStep P G t e (subKC g kp.1 kc t.1.1 e (subKP g kp t.1.1 e r))

omit [Fintype S] [Fintype K] [Nonempty K] in
theorem simWorldD_frame (t : SimSt S W K PK SK SS C × St K) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) :
    Frame e t.1.1.x.st (simWorldD P G t e r).1.1.1.x.st := by
  rw [simWorldD_fst]
  exact simStartD_frame P G t.1 e r.1

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The start of the responder session of `g` gives it a record. -/
theorem isCreate_recs {t : SimSt S W K PK SK SS C × St K} {e : OEv W SS C}
    (h : isCreate g t.1 e = true) (r : PDraw S K PK SK SS C × K) :
    ((simWorldD P G t e r).1.1.1.x.st.recs (gR g)).isSome = true := by
  rw [simWorldD_fst]
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | _ <;> simp only [isCreate,
    Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, hn⟩ := h
  simp [simStartD, Option.isNone_iff_eq_none.mp hn, addSession, gR]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The completion of the initiator session of `g` by an encapsulation sets its key. -/
theorem isEnc_key {pk : PK} {t : SimSt S W K PK SK SS C × St K} {e : OEv W SS C}
    (h : isEnc g pk t.1 e = true) (r : PDraw S K PK SK SS C × K) (kc : SS × C)
    (hr : r.1.2.2 = some kc) :
    ∃ ri, (simWorldD P G t e r).1.1.1.x.st.recs (gI g) = some ri ∧ ri.key.isSome := by
  rw [simWorldD_fst]
  rcases e with _ | (_ | _ | _ | _ | _ | _ | ⟨sid, pid⟩ | _ | _) <;>
    simp only [isEnc, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  revert h
  split
  · rename_i ri ek hri hek
    intro h
    simp only [decide_eq_true_eq] at h
    obtain ⟨hp, ho, hpk, hrole, hkey⟩ := h
    obtain ⟨opk, hopk⟩ := Option.isSome_iff_exists.mp ho
    simp only [simStartD, simCompleteD, hri, hek, hopk, hpk, hr, hrole, hkey, Option.isNone_none,
      and_self, ↓reduceIte]
    unfold deliverD
    split <;> simp [pKeyed, keyed, setRec, gI]
  · simp

omit [Fintype S] [Fintype K] [Nonempty K] in
theorem wStep_frame (t : WSt S W K PK SK SS C) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) :
    Frame e t.1.1.1.x.st (wStep P G t e r).2.1.1.1.x.st :=
  simWorldD_frame P G t.1 e r

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] [SampleableType W]
  [DecidableEq SS] in
theorem isCreate_encPk {t : SimSt S W K PK SK SS C} {e : OEv W SS C}
    (h : isCreate g t e = true) : encPk t.1 e = none := by
  rcases e with _ | (_ | _ | _ | _ | _ | _ | _ | _ | _) <;> first | rfl | simp [isCreate] at h

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] [SampleableType W]
  [DecidableEq SS] in
theorem isEnc_encPk {pk : PK} {t : SimSt S W K PK SK SS C} {e : OEv W SS C}
    (h : isEnc g pk t e = true) : encPk t.1 e = some pk ∧ isCreate g t e = false := by
  rcases e with _ | (_ | _ | _ | _ | _ | _ | ⟨sid, pid⟩ | _ | _) <;>
    simp only [isEnc, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  refine ⟨?_, rfl⟩
  revert h
  simp only [encPk]
  split
  · rename_i ri ek hri hek
    intro h
    simp only [decide_eq_true_eq] at h
    simp only [hri, h.2.2.1]
  · simp

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] [SampleableType W]
  [DecidableEq SS] in
theorem isEnc_key_none {pk : PK} {t : SimSt S W K PK SK SS C} {e : OEv W SS C}
    (h : isEnc g pk t e = true) : ∃ ri, t.1.x.st.recs (gI g) = some ri ∧ ri.key = none := by
  rcases e with _ | (_ | _ | _ | _ | _ | _ | ⟨sid, pid⟩ | _ | _) <;>
    simp only [isEnc, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  revert h
  split
  · rename_i ri ek hri hek
    intro h
    simp only [decide_eq_true_eq] at h
    exact ⟨ri, hri, h.2.2.2.2⟩
  · simp

open Classical in
/-- **Eager sampling of the KEM key pair of the responder session of `g`.** -/
theorem flag_w_eq_gw1 (E : WSt S W K PK SK SS C → Prop)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => E x.2) (wO P G)) B
        (wInit, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' kp, P.keygen kp * (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => E x.2)
        (gw1O P G g kp)) B (wInit, false)).toOuterMeasure {y | y.2.2 = true} := by
  refine run_eager_flag P.keygen (wO P G) (gw1O P G g) E
    (fun t => t.1.1.1.x.st.recs (gR g) = none) (fun t e => isCreate g t.1.1 e = true)
    ?_ ?_ ?_ ?_ ?_ B wInit rfl
  · intro kp t e h
    simp only [Bool.not_eq_true] at h
    simp only [gw1O, wO, subKP, h, Bool.false_eq_true, ↓reduceIte, Prod.mk.eta]
  · intro t e _ h
    unfold wO gw1O
    rw [isCreate_encPk g h, simDist_none_eager P (wStep P G t e)]
    simp only [subKP, h, ↓reduceIte]
  · intro kp t e _ h y hy
    simp only [gw1O, PMF.support_map, Set.mem_image] at hy
    obtain ⟨r, -, rfl⟩ := hy
    have := isCreate_recs P G g h (subKP g kp t.1.1 e r)
    simp only [wStep]
    intro hc
    rw [hc] at this
    cases this
  · intro t e ht y hy
    simp only [wO, PMF.support_map, Set.mem_image] at hy
    obtain ⟨r, -, rfl⟩ := hy
    intro hc
    cases h₀ : t.1.1.1.x.st.recs (gR g) with
    | none => exact ht h₀
    | some r₀ =>
      obtain ⟨r', hr', -⟩ := (wStep_frame P G t e r).1 _ r₀ h₀
      rw [hc] at hr'
      cases hr'
  · intro t e ht h
    rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | _ <;>
      simp only [isCreate, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, hn⟩ := h
    exact ht (Option.isNone_iff_eq_none.mp hn)

open Classical in
/-- **Eager sampling of the encapsulation of the initiator session of `g`.** -/
theorem flag_gw1_eq_gw (E : WSt S W K PK SK SS C → Prop) (kp : PK × SK)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => E x.2) (gw1O P G g kp)) B
        (wInit, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' kc, P.encaps kp.1 kc * (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => E x.2)
        (gwO P G g kp kc)) B (wInit, false)).toOuterMeasure {y | y.2.2 = true} := by
  refine run_eager_flag (P.encaps kp.1) (gw1O P G g kp) (gwO P G g kp) E
    (fun t => ∀ ri, t.1.1.1.x.st.recs (gI g) = some ri → ri.key = none)
    (fun t e => isEnc g kp.1 t.1.1 e = true) ?_ ?_ ?_ ?_ ?_ B wInit (fun _ h => by cases h)
  · intro kc t e h
    simp only [Bool.not_eq_true] at h
    simp only [gwO, gw1O, subKC, h, Bool.false_eq_true, ↓reduceIte, Prod.mk.eta]
  · intro t e _ h
    obtain ⟨he, hc⟩ := isEnc_encPk g h
    unfold gw1O gwO
    rw [he]
    simp only [subKP, hc, Bool.false_eq_true, ↓reduceIte, Prod.mk.eta]
    rw [simDist_some_eager P kp.1 (wStep P G t e)]
    simp only [subKC, h, ↓reduceIte]
  · intro kc t e _ h y hy
    simp only [gwO, PMF.support_map, Set.mem_image] at hy
    obtain ⟨r, -, rfl⟩ := hy
    obtain ⟨ri, hri, hk⟩ := isEnc_key P G g h (subKC g kp.1 kc t.1.1 e (subKP g kp t.1.1 e r))
      kc (by simp only [subKC, h, ↓reduceIte])
    intro hc
    have := hc ri hri
    simp [this] at hk
  · intro t e ht y hy
    simp only [gw1O, PMF.support_map, Set.mem_image] at hy
    obtain ⟨r, -, rfl⟩ := hy
    intro hc
    apply ht
    intro ri hri
    obtain ⟨r', hr', -, -, -, hk⟩ := (wStep_frame P G t e (subKP g kp t.1.1 e r)).1 _ ri hri
    by_contra hne
    have h' := hc r' hr'
    rw [hk (by cases h : ri.key <;> simp_all)] at h'
    exact hne h'
  · intro t e ht h
    obtain ⟨ri, hri, hk⟩ := isEnc_key_none g h
    exact ht fun ri' hri' => by rw [hri] at hri'; cases hri'; exact hk

end EagerWorld

/-! ## The symbolic world

The world of the reduction runs the simulator over shared secrets `Option SS`, in which `none`
stands for the challenge key, which the reduction does not use: the initiator session of the
guess encapsulates to `(none, c*)`, and the responder session of the guess decapsulates `c*` to
`none` and every other encapsulation with the decapsulation oracle. The interpretation `iSim`
reads `none` as the challenge key `k` and the absent secret key of the responder of the guess
as `sk`. -/

section Sym

variable {S W K PK SK SS C : Type}

/-- The interpretation of a symbolic shared secret: `none` is the challenge key `k`. -/
def iInp (k : SS) (p : PInp W (Option SS)) : PInp W SS := (p.1, p.2.getD k)

/-- The interpretation of an entry of the key-derivation table. -/
def iE (k : SS) (p : PInp W (Option SS) × K) : PInp W SS × K := (iInp k p.1, p.2)

/-- The interpretation of the simulator's copy of the real state: the shared secrets of the
table, and the absent secret key `sk`. -/
def iP (k : SS) (sk : SK) (s : PSt S W K PK (Option SK) (Option SS) C) :
    PSt S W K PK SK SS C :=
  ⟨s.x, fun y => (s.kem y).map fun kp => (kp.1, kp.2.getD sk), s.ct, s.ro.map (iE k)⟩

/-- The interpretation of a state of the simulator. -/
def iSim (k : SS) (sk : SK) (s : SimSt S W K PK (Option SK) (Option SS) C) :
    SimSt S W K PK SK SS C :=
  (iP k sk s.1, fun y => (s.2.1 y).map (iInp k), s.2.2)

/-- An event of the adversary with a concrete shared secret, as an event over symbolic shared
secrets. -/
def liftE : OEv W SS C → OEv W (Option SS) C
  | .inl h => .inl h
  | .inr .idle => .inr .idle
  | .inr .poll => .inr .poll
  | .inr (.pub pid) => .inr (.pub pid)
  | .inr (.ephPub sid pid) => .inr (.ephPub sid pid)
  | .inr (.pqPub sid pid) => .inr (.pqPub sid pid)
  | .inr (.corrupt pid) => .inr (.corrupt pid)
  | .inr (.complete sid pid) => .inr (.complete sid pid)
  | .inr (.send sid pid e c) => .inr (.send sid pid e c)
  | .inr (.kdf x) => .inr (.kdf (x.1, some x.2))

theorem iInp_inj {k : SS} {a b : PInp W (Option SS)} (ha : a.2 ≠ some k) (hb : b.2 ≠ some k)
    (h : iInp k a = iInp k b) : a = b := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  simp only [iInp, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases a₂ <;> cases b₂ <;> simp_all

theorem lookup_map_iE [DecidableEq W] [DecidableEq SS] {k : SS}
    (tb : List (PInp W (Option SS) × K)) (ip : PInp W (Option SS))
    (htb : ∀ e ∈ tb, e.1.2 ≠ some k) (hip : ip.2 ≠ some k) :
    @List.lookup _ _ instBEqOfDecidableEq (iInp k ip) (tb.map (iE k)) =
      @List.lookup _ _ instBEqOfDecidableEq ip tb := by
  induction tb with
  | nil => rfl
  | cons e tb ih =>
    obtain ⟨e₁, e₂⟩ := e
    simp only [List.map_cons, iE, lookup_cons]
    rw [ih fun e he => htb e (List.mem_cons_of_mem _ he)]
    by_cases h : ip = e₁
    · subst h; simp
    · have h' : iInp k ip ≠ iInp k e₁ := fun hc =>
        h (iInp_inj hip (htb _ List.mem_cons_self) hc)
      simp only [h, h', ↓reduceIte]

theorem roDet_map_iE [DecidableEq W] [DecidableEq SS] {k : SS}
    (tb : List (PInp W (Option SS) × K)) (ip : PInp W (Option SS)) (v : K)
    (htb : ∀ e ∈ tb, e.1.2 ≠ some k) (hip : ip.2 ≠ some k) :
    roDet (tb.map (iE k)) (iInp k ip) v =
      ((roDet tb ip v).1, (roDet tb ip v).2.map (iE k)) := by
  unfold roDet
  rw [lookup_map_iE tb ip htb hip]
  split <;> simp [iE]

theorem update_map_iInp {k : SS} (inp : Inst → Option (PInp W (Option SS))) (x : Inst)
    (ip : PInp W (Option SS)) :
    (fun y => (Function.update inp x (some ip) y).map (iInp k)) =
      Function.update (fun y => (inp y).map (iInp k)) x (some (iInp k ip)) := by
  funext y
  by_cases h : y = x
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem all_map_iInp [DecidableEq W] [DecidableEq SS] {k : SS} (o : Option (PInp W (Option SS)))
    (ip : PInp W (Option SS)) (ho : ∀ a, o = some a → a.2 ≠ some k) (hip : ip.2 ≠ some k) :
    (o.map (iInp k)).all (· = iInp k ip) = o.all (· = ip) := by
  cases o with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Option.all_some, decide_eq_decide]
    exact ⟨iInp_inj (ho a rfl) hip, fun h => h ▸ rfl⟩

end Sym

/-! ## The world of the reduction -/

section SymWorld

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess)

omit [DecidableEq SS] in
/-- The KEM of the world of the reduction: shared secrets are symbolic, and the absent secret
key, that of the challenge, decapsulates the challenge encapsulation `cs` to `none` and every
other encapsulation with the decapsulation oracle `dec`. -/
noncomputable def symP (cs : C) (dec : C → Option SS) : Scheme PK (Option SK) (Option SS) C where
  keygen := P.keygen.map fun kp => (kp.1, some kp.2)
  encaps pk := (P.encaps pk).map fun kc => (some kc.1, kc.2)
  decaps osk c := match osk with
    | some sk => (P.decaps sk c).map some
    | none => if c = cs then some none else (dec c).map some

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
/-- The draw of the world of the reduction: the public key `pk` without secret key at the start
of the responder session of `g`, the encapsulation `(none, cs)` at the completion of its
initiator session, and the draws of the simulator with concrete shared secrets otherwise. -/
noncomputable def liftD (pk : PK) (cs : C) (t : SimSt S W K PK (Option SK) (Option SS) C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) :
    PDraw S K PK (Option SK) (Option SS) C × K :=
  ((r.1.1, if isCreate g t (liftE e) then (pk, none) else (r.1.2.1.1, some r.1.2.1.2),
    if isEnc g pk t (liftE e) then some (none, cs)
    else r.1.2.2.map fun kc => (some kc.1, kc.2)), r.2)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The concrete shared secret that the event `e` with the draw `r` brings into the world of
the reduction: the shared secret of a query of the key derivation, of the encapsulation of a
completion, or of a decapsulation. -/
def newVal (cs : C) (dec : C → Option SS) (t : SimSt S W K PK (Option SK) (Option SS) C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) : Option SS :=
  match e with
  | .inr (.kdf x) => some x.2
  | .inr (.complete _ _) => r.1.2.2.map Prod.fst
  | .inr (.send sid pid _ c) =>
    match t.1.kem (sid, pid) with
    | some (_, some sk) => P.decaps sk c
    | some (_, none) => if c = cs then none else dec c
    | none => none
  | _ => none

/-- The state of the world of the reduction: the symbolic simulated world and the list of the
concrete shared secrets it received. -/
abbrev YSt (S W K PK SK SS C : Type) :=
  (SimSt S W K PK (Option SK) (Option SS) C × St K) × List SS

/-- A step of the world of the reduction on the draw `r`. -/
noncomputable def yStep (pk : PK) (cs : C) (dec : C → Option SS) (t : YSt S W K PK SK SS C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) : OOut S W K PK C × YSt S W K PK SK SS C :=
  ((simWorldD (symP P cs dec) G t.1 (liftE e) (liftD g pk cs t.1.1 e r)).2,
    ((simWorldD (symP P cs dec) G t.1 (liftE e) (liftD g pk cs t.1.1 e r)).1,
      t.2 ++ (newVal P cs dec t.1.1 e r).toList))

/-- **The oracle of the world of the reduction.** -/
noncomputable def yO (pk : PK) (cs : C) (dec : C → Option SS) (t : YSt S W K PK SK SS C)
    (e : OEv W SS C) : PMF (OOut S W K PK C × YSt S W K PK SK SS C) :=
  (simDist P (encPk t.1.1.1 (liftE e))).map (yStep P G g pk cs dec t e)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
/-- The initial state of the world of the reduction. -/
def yInit : YSt S W K PK SK SS C := (((pInit, fun _ => none, .fwd), initSt), [])

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
/-- **The invariant of the world of the reduction** at the public key `pk`, the challenge
encapsulation `cs` and the challenge key `k`: no symbolic shared secret is the concrete `k`;
the symbolic entries of the table are inputs of exposed sessions; records are fresh; the
responder session of `g` has the public key `pk` without secret key; encapsulations and inputs
belong to sessions with records; and the initiator session of `g` with peer the responder of `g`
encapsulated `cs` to a symbolic shared secret. -/
structure Good (pk : PK) (cs : C) (k : SS) (s : PSt S W K PK (Option SK) (Option SS) C)
    (inp : Inst → Option (PInp W (Option SS))) : Prop where
  roV : ∀ e ∈ s.ro, e.1.2 ≠ some k
  inpV : ∀ y ip, inp y = some ip → ip.2 ≠ some k
  roN : ∀ e ∈ s.ro, e.1.2 = none →
    s.x.st.corrupt e.1.1.ini = true ∨ s.x.st.corrupt e.1.1.res = true
  fresh : ∀ y r, s.x.st.recs y = some r → r.status = .fresh
  kemR : ∀ kp, s.kem (gR g) = some kp → kp = (pk, none)
  noRec : ∀ y, s.x.st.recs y = none → s.ct y = none ∧ inp y = none
  encI : ∀ ri, s.x.st.recs (gI g) = some ri → ri.role = .initiator → ri.peer = g.2.2 →
    (∀ c, s.ct (gI g) = some c → c = cs) ∧ (∀ ip, inp (gI g) = some ip → ip.2 = none)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem good_init (pk : PK) (cs : C) (k : SS) :
    Good g pk cs k (pInit : PSt S W K PK (Option SK) (Option SS) C) (fun _ => none) :=
  ⟨(fun _ h => by cases h), (fun _ _ h => by cases h), (fun _ h => by cases h),
    (fun _ _ h => by cases h), (fun _ h => by cases h), (fun _ _ => ⟨rfl, rfl⟩),
    (fun _ h => by cases h)⟩

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
@[simp] theorem iP_x (k : SS) (sk : SK) (s : PSt S W K PK (Option SK) (Option SS) C) :
    (iP k sk s).x = s.x := rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
@[simp] theorem iP_ct (k : SS) (sk : SK) (s : PSt S W K PK (Option SK) (Option SS) C) :
    (iP k sk s).ct = s.ct := rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem pkOf_iP (k : SS) (sk : SK) (s : PSt S W K PK (Option SK) (Option SS) C)
    (sid : SessionId) (p : PartyId) : pkOf (iP k sk s) sid p = pkOf s sid p := by
  simp only [pkOf, iP, Option.map_map]
  rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem isCreate_iSim (k : SS) (sk : SK) (s : SimSt S W K PK (Option SK) (Option SS) C)
    (e : OEv W SS C) : isCreate g (iSim k sk s) e = isCreate g s (liftE e) := by
  rcases e with (_ | _) | (_ | _ | _ | _ | _ | _ | _ | _ | _) <;> rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem isEnc_iSim (k : SS) (sk : SK) (pk : PK) (s : SimSt S W K PK (Option SK) (Option SS) C)
    (e : OEv W SS C) : isEnc g pk (iSim k sk s) e = isEnc g pk s (liftE e) := by
  rcases e with _ | (_ | _ | _ | _ | _ | _ | ⟨sid, pid⟩ | _ | _) <;> try rfl
  simp only [isEnc, liftE, iSim, iP_x]
  congr 1
  cases s.1.x.st.recs (sid, pid) <;> cases s.1.x.eph (sid, pid) <;> try rfl
  exact decide_eq_decide.mpr (by rw [pkOf_iP])

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem encPk_iSim (k : SS) (sk : SK) (s : SimSt S W K PK (Option SK) (Option SS) C)
    (e : OEv W SS C) : encPk (iSim k sk s).1 e = encPk s.1 (liftE e) := by
  rcases e with _ | (_ | _ | _ | _ | _ | _ | ⟨sid, pid⟩ | _ | _) <;> try rfl
  simp only [encPk, liftE, iSim, iP_x, pkOf_iP]

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
/-- **The delivery commutes with the interpretation** when the new input and the symbolic
shared secrets of the state are not the concrete challenge key. -/
theorem deliverD_iSim {k : SS} (sk : SK)
    (s : PSt S W K PK (Option SK) (Option SS) C) (inp : Inst → Option (PInp W (Option SS)))
    (x : Inst) (r : Rec K) (ip : PInp W (Option SS)) (kf : K)
    (hro : ∀ e ∈ s.ro, e.1.2 ≠ some k) (hinp : ∀ y a, inp y = some a → a.2 ≠ some k)
    (hip : ip.2 ≠ some k) :
    deliverD (iP k sk s) (fun y => (inp y).map (iInp k)) x r (iInp k ip) kf =
      (iSim k sk (deliverD s inp x r ip kf).1, (deliverD s inp x r ip kf).2) := by
  unfold deliverD
  by_cases h : Exposed s.x.st x r
  · have h' : Exposed (iP k sk s).x.st x r := h
    simp only [h, h', ↓reduceIte]
    rw [show (iP k sk s).ro = s.ro.map (iE k) from rfl, roDet_map_iE s.ro ip kf hro hip,
      ← update_map_iInp]
    rfl
  · have h' : ¬ Exposed (iP k sk s).x.st x r := h
    simp only [h, h', ↓reduceIte]
    rw [all_map_iInp (inp (x.1, r.peer)) ip (hinp _) hip, ← update_map_iInp]
    rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem opkOf_iP (k : SS) (sk : SK) (s : PSt S W K PK (Option SK) (Option SS) C)
    (sid : SessionId) (p : PartyId) : opkOf (iP k sk s).x sid p = opkOf s.x sid p := rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem Good.congr {pk : PK} {cs : C} {k : SS} {s s' : PSt S W K PK (Option SK) (Option SS) C}
    {inp : Inst → Option (PInp W (Option SS))} (h : Good g pk cs k s inp)
    (hrecs : s'.x.st.recs = s.x.st.recs)
    (hcor : ∀ p, s.x.st.corrupt p = true → s'.x.st.corrupt p = true) (hro : s'.ro = s.ro)
    (hkem : s'.kem = s.kem) (hct : s'.ct = s.ct) : Good g pk cs k s' inp := by
  refine ⟨?_, h.inpV, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hro]; exact h.roV
  · intro e he hn
    rw [hro] at he
    rcases h.roN e he hn with h' | h'
    · exact Or.inl (hcor _ h')
    · exact Or.inr (hcor _ h')
  · rw [hrecs]; exact h.fresh
  · rw [hkem]; exact h.kemR
  · rw [hrecs, hct]; exact h.noRec
  · rw [hrecs, hct]; exact h.encI

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
/-- Recording the encapsulation `c` of the session `x`. -/
theorem Good.ct {pk : PK} {cs : C} {k : SS} {s s' : PSt S W K PK (Option SK) (Option SS) C}
    {inp : Inst → Option (PInp W (Option SS))} (h : Good g pk cs k s inp) {x : Inst}
    {r : Rec K} {c : C} (hx : s.x.st.recs x = some r)
    (hc : x = gI g → r.role = .initiator → r.peer = g.2.2 → c = cs)
    (hrecs : s'.x.st = s.x.st) (hro : s'.ro = s.ro) (hkem : s'.kem = s.kem)
    (hct : s'.ct = Function.update s.ct x (some c)) : Good g pk cs k s' inp := by
  refine ⟨?_, h.inpV, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hro]; exact h.roV
  · rw [hro, hrecs]; exact h.roN
  · rw [hrecs]; exact h.fresh
  · rw [hkem]; exact h.kemR
  · intro y hy
    rw [hrecs] at hy
    have hyx : y ≠ x := fun hc => by rw [hc, hx] at hy; cases hy
    rw [hct, Function.update_of_ne hyx]
    exact h.noRec y hy
  · intro ri hri hro' hpe
    rw [hrecs] at hri
    refine ⟨fun c' hc' => ?_, (h.encI ri hri hro' hpe).2⟩
    rw [hct] at hc'
    by_cases hgx : gI g = x
    · subst hgx
      rw [hx] at hri
      cases hri
      simp only [Function.update_self, Option.some.injEq] at hc'
      rw [← hc']
      exact hc rfl hro' hpe
    · rw [Function.update_of_ne hgx] at hc'
      exact (h.encI ri hri hro' hpe).1 c' hc'

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
/-- **The delivery keeps the invariant** for an input of the shape of the session that is not
the concrete challenge key, and is symbolic at the initiator session of `g`. -/
theorem Good.deliverD {pk : PK} {cs : C} {k : SS} {s : PSt S W K PK (Option SK) (Option SS) C}
    {inp : Inst → Option (PInp W (Option SS))} (h : Good g pk cs k s inp) (x : Inst) (r : Rec K)
    (hx : s.x.st.recs x = some r) (ip : PInp W (Option SS)) (kf : K)
    (hip : ip.2 ≠ some k)
    (hsh : (ip.1.ini = x.2 ∧ ip.1.res = r.peer) ∨ (ip.1.ini = r.peer ∧ ip.1.res = x.2))
    (hI : x = gI g → r.role = .initiator → r.peer = g.2.2 → ip.2 = none) :
    Good g pk cs k (PQXDHSquareHops.deliverD s inp x r ip kf).1.1
      (PQXDHSquareHops.deliverD s inp x r ip kf).1.2.1 := by
  have hrecs : ∀ y r', (setRec s.x.st x { r with key := some kf }).recs y = some r' →
      ∃ r'', s.x.st.recs y = some r'' ∧ r'.status = r''.status := by
    intro y r' hy
    by_cases hyx : y = x
    · subst hyx
      simp only [setRec, Function.update_self, Option.some.injEq] at hy
      exact ⟨r, hx, by rw [← hy]⟩
    · simp only [setRec, Function.update_of_ne hyx] at hy
      exact ⟨r', hy, rfl⟩
  have hfr : ∀ v : K, ∀ y r', (setRec s.x.st x { r with key := some v }).recs y = some r' →
      r'.status = .fresh := by
    intro v y r' hy
    by_cases hyx : y = x
    · subst hyx
      simp only [setRec, Function.update_self, Option.some.injEq] at hy
      rw [← hy]; exact h.fresh _ r hx
    · simp only [setRec, Function.update_of_ne hyx] at hy
      exact h.fresh y r' hy
  have hnr : ∀ v : K, ∀ y, (setRec s.x.st x { r with key := some v }).recs y = none →
      s.ct y = none ∧ Function.update inp x (some ip) y = none := by
    intro v y hy
    by_cases hyx : y = x
    · subst hyx; simp [setRec] at hy
    · simp only [setRec, Function.update_of_ne hyx] at hy
      rw [Function.update_of_ne hyx]
      exact h.noRec y hy
  have hei : ∀ v : K, ∀ ri, (setRec s.x.st x { r with key := some v }).recs (gI g) = some ri →
      ri.role = .initiator → ri.peer = g.2.2 →
      (∀ c, s.ct (gI g) = some c → c = cs) ∧
        (∀ ip', Function.update inp x (some ip) (gI g) = some ip' → ip'.2 = none) := by
    intro v ri hri hro hpe
    by_cases hgx : gI g = x
    · subst hgx
      simp only [setRec, Function.update_self, Option.some.injEq] at hri
      subst hri
      refine ⟨(h.encI r hx hro hpe).1, fun ip' hip' => ?_⟩
      simp only [Function.update_self, Option.some.injEq] at hip'
      rw [← hip']
      exact hI rfl hro hpe
    · simp only [setRec, Function.update_of_ne hgx] at hri
      rw [Function.update_of_ne hgx]
      exact h.encI ri hri hro hpe
  have hiv : ∀ y ip', Function.update inp x (some ip) y = some ip' → ip'.2 ≠ some k := by
    intro y ip' hy
    by_cases hyx : y = x
    · subst hyx
      simp only [Function.update_self, Option.some.injEq] at hy
      rw [← hy]; exact hip
    · rw [Function.update_of_ne hyx] at hy
      exact h.inpV y ip' hy
  unfold PQXDHSquareHops.deliverD
  split
  · rename_i hex
    refine ⟨fun e he => ?_, hiv, fun e he hn => ?_, hfr _, h.kemR, hnr _, hei _⟩
    · rcases roDet_mem s.ro ip kf e he with he | rfl
      · exact h.roV e he
      · exact hip
    · rcases roDet_mem s.ro ip kf e he with he | rfl
      · exact h.roN e he hn
      · have hst : r.status = .fresh := h.fresh x r hx
        have hex' : s.x.st.corrupt x.2 = true ∨ s.x.st.corrupt r.peer = true := by
          rcases hex with h' | h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
          · rw [hst] at h'; cases h'
        simp only [pKeyed, keyed, setRec]
        rcases hsh with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> tauto
  · exact ⟨h.roV, hiv, h.roN, hfr _, h.kemR, hnr _, hei _⟩

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
@[simp] theorem iSim_fst (k : SS) (sk : SK) (s : SimSt S W K PK (Option SK) (Option SS) C) :
    (iSim k sk s).1 = iP k sk s.1 := rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
@[simp] theorem iSim_snd (k : SS) (sk : SK) (s : SimSt S W K PK (Option SK) (Option SS) C) :
    (iSim k sk s).2 = ((fun y => (s.2.1 y).map (iInp k)), s.2.2) := rfl

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
/-- The delivery on a state given by its fields. -/
theorem deliver_branch {k : SS} (sk : SK) (rs : PSt S W K PK (Option SK) (Option SS) C)
    (X : RSt S W K) (ct' : Inst → Option C) (inp : Inst → Option (PInp W (Option SS)))
    (x : Inst) (r : Rec K) (A : Inp W) (o : Option SS) (kf : K)
    (hro : ∀ e ∈ rs.ro, e.1.2 ≠ some k) (hinp : ∀ y a, inp y = some a → a.2 ≠ some k)
    (ho : o ≠ some k) :
    PQXDHSquareHops.deliverD (⟨X, (iP k sk rs).kem, ct', (iP k sk rs).ro⟩ :
        PSt S W K PK SK SS C) (fun y => (inp y).map (iInp k)) x r (A, o.getD k) kf =
      (iSim k sk (PQXDHSquareHops.deliverD (⟨X, rs.kem, ct', rs.ro⟩ :
          PSt S W K PK (Option SK) (Option SS) C) inp x r (A, o) kf).1,
        (PQXDHSquareHops.deliverD (⟨X, rs.kem, ct', rs.ro⟩ :
          PSt S W K PK (Option SK) (Option SS) C) inp x r (A, o) kf).2) :=
  deliverD_iSim sk ⟨X, rs.kem, ct', rs.ro⟩ inp x r (A, o) kf hro hinp ho

omit [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
open Classical in
/-- **`complete` commutes with the interpretation.** -/
theorem complete_iSim {pk : PK} {sk : SK} {k : SS} {cs : C}
    (s : SimSt S W K PK (Option SK) (Option SS) C) (hG : Good g pk cs k s.1 s.2.1)
    (sid : SessionId) (pid : PartyId) (d : Draw S K) (kc : Option (SS × C))
    (hv : kc.map Prod.fst ≠ some k) :
    simCompleteD G (iSim k sk s) (sid, pid)  d
        (if isEnc g pk s (.inr (.complete sid pid)) then some (k, cs) else kc) =
      (iSim k sk (simCompleteD G s (sid, pid) d
        (if isEnc g pk s (.inr (.complete sid pid)) then some (none, cs)
          else kc.map fun kc => (some kc.1, kc.2))).1,
        (simCompleteD G s (sid, pid) d
        (if isEnc g pk s (.inr (.complete sid pid)) then some (none, cs)
          else kc.map fun kc => (some kc.1, kc.2))).2) ∧
      Good g pk cs k (simCompleteD G s (sid, pid) d
        (if isEnc g pk s (.inr (.complete sid pid)) then some (none, cs)
          else kc.map fun kc => (some kc.1, kc.2))).1.1
        (simCompleteD G s (sid, pid) d
        (if isEnc g pk s (.inr (.complete sid pid)) then some (none, cs)
          else kc.map fun kc => (some kc.1, kc.2))).1.2.1 := by
  obtain ⟨rs, inp, ph⟩ := s
  have hG' : Good g pk cs k rs inp := hG
  simp only [simCompleteD, iSim_fst, iSim_snd, iP_x, pkOf_iP]
  cases hr : rs.x.st.recs (sid, pid) with
  | none => exact ⟨rfl, hG'⟩
  | some rc =>
    cases he : rs.x.eph (sid, pid) with
    | none => exact ⟨rfl, hG'⟩
    | some ek =>
      by_cases hE : isEnc g pk (rs, inp, ph) (.inr (.complete sid pid)) = true
      · have hE' := hE
        simp only [isEnc, hr, he, Bool.and_eq_true, decide_eq_true_eq] at hE'
        obtain ⟨⟨rfl, rfl⟩, hpe, ho, hpk, hrole, hkey⟩ := hE'
        obtain ⟨opk, hopk⟩ := Option.isSome_iff_exists.mp ho
        simp only [hE, ↓reduceIte, hopk, hpk, hrole, hkey, Option.isNone_none, and_self]
        refine ⟨deliver_branch sk rs _ _ inp _ rc _ none _ hG'.roV hG'.inpV (by simp), ?_⟩
        refine Good.deliverD g ?_ (g.1, g.2.1) rc ?_ _ _ ?_ ?_ ?_
        · exact Good.ct g hG' hr (fun _ _ _ => rfl) (by simp only [ltD_st]) rfl rfl rfl
        · simp only [ltD_st]; exact hr
        · simp
        · exact Or.inl ⟨rfl, rfl⟩
        · exact fun _ _ _ => rfl
      · have hEnc : (sid, pid) = gI g → rc.role = .initiator → rc.peer = g.2.2 →
            (opkOf rs.x sid rc.peer).isSome = true → (pkOf rs sid rc.peer).isSome = true →
            rc.key = none → False := by
          intro hx hro hpe hop hpk hkey
          simp only [gI, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          obtain ⟨pk', hpk'⟩ := Option.isSome_iff_exists.mp hpk
          have hkem : ∃ osk, rs.kem (gR g) = some (pk', osk) := by
            simp only [pkOf, gR, ← hpe, Option.map_eq_some_iff] at hpk' ⊢
            obtain ⟨kp, hkp, rfl⟩ := hpk'
            exact ⟨kp.2, hkp⟩
          obtain ⟨osk, hosk⟩ := hkem
          have hpkpk : pk' = pk := by
            have := hG'.kemR _ hosk
            simp only [Prod.mk.injEq] at this
            exact this.1
          subst hpkpk
          apply hE
          simp only [isEnc, hr, he]
          rw [Bool.and_eq_true]
          constructor
          · apply decide_eq_true; exact ⟨trivial, trivial⟩
          · apply decide_eq_true; exact ⟨hpe, hop, hpk', hro, hkey⟩
        simp only [hE, Bool.false_eq_true, ↓reduceIte]
        cases hopk : opkOf rs.x sid rc.peer with
        | none => exact ⟨rfl, hG'⟩
        | some opk =>
          cases hpk : pkOf rs sid rc.peer with
          | none => exact ⟨rfl, hG'⟩
          | some pk' =>
            cases kc with
            | none => exact ⟨rfl, hG'⟩
            | some kc0 =>
              simp only [Option.map_some]
              by_cases hc : rc.role = .initiator ∧ rc.key.isNone = true
              · simp only [hc, and_self, ↓reduceIte]
                have hv' : some kc0.1 ≠ some k := hv
                refine ⟨deliver_branch sk rs _ _ inp _ rc _ (some kc0.1) _ hG'.roV hG'.inpV hv',
                  ?_⟩
                have hk : rc.key = none := Option.isNone_iff_eq_none.mp hc.2
                refine Good.deliverD g ?_ (sid, pid) rc ?_ _ _ hv' (Or.inl ⟨rfl, rfl⟩) ?_
                · exact Good.ct g hG' hr (fun hx hro hpe => (hEnc hx hro hpe (by simp [hopk])
                    (by simp [hpk]) hk).elim) (by simp only [ltD_st]) rfl rfl rfl
                · simp only [ltD_st]; exact hr
                · exact fun hx hro hpe => (hEnc hx hro hpe (by simp [hopk]) (by simp [hpk])
                    hk).elim
              · simp only [hc, ↓reduceIte]
                exact ⟨rfl, hG'⟩

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
@[simp] theorem iP_kem (k : SS) (sk : SK) (s : PSt S W K PK (Option SK) (Option SS) C)
    (y : Inst) : (iP k sk s).kem y = (s.kem y).map fun kp => (kp.1, kp.2.getD sk) := rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The decapsulation of the world of the reduction, interpreted, is the decapsulation under
the interpreted secret key, when the challenge decapsulates to the challenge key. -/
theorem decaps_symP {sk : SK} {k : SS} {cs : C} (hc : P.decaps sk cs = some k)
    (osk : Option SK) (c : C) :
    P.decaps (osk.getD sk) c = ((symP P cs (P.decaps sk)).decaps osk c).map (·.getD k) := by
  cases osk with
  | some sk' => simp [symP]
  | none =>
    by_cases h : c = cs
    · subst h; simp [symP, hc]
    · simp [symP, h]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **`send` commutes with the interpretation.** -/
theorem send_iSim {pk : PK} {sk : SK} {k : SS} {cs : C} (hc : P.decaps sk cs = some k)
    (s : SimSt S W K PK (Option SK) (Option SS) C) (hG : Good g pk cs k s.1 s.2.1)
    (sid : SessionId) (pid : PartyId) (e : W) (c : C) (d : Draw S K)
    (hv : ∀ kp, s.1.kem (sid, pid) = some kp →
      ((symP P cs (P.decaps sk)).decaps kp.2 c).bind id ≠ some k) :
    simSendD P G (iSim k sk s) (sid, pid) e c d =
      (iSim k sk (simSendD (symP P cs (P.decaps sk)) G s (sid, pid) e c d).1,
        (simSendD (symP P cs (P.decaps sk)) G s (sid, pid) e c d).2) ∧
      Good g pk cs k (simSendD (symP P cs (P.decaps sk)) G s (sid, pid) e c d).1.1
        (simSendD (symP P cs (P.decaps sk)) G s (sid, pid) e c d).1.2.1 := by
  obtain ⟨rs, inp, ph⟩ := s
  have hG' : Good g pk cs k rs inp := hG
  simp only [simSendD, iSim_fst, iSim_snd, iP_x, iP_kem]
  cases hr : rs.x.st.recs (sid, pid) with
  | none => exact ⟨rfl, hG'⟩
  | some rc =>
    cases he : rs.x.eph (sid, pid) with
    | none => exact ⟨rfl, hG'⟩
    | some opk =>
      cases hk : rs.kem (sid, pid) with
      | none => exact ⟨rfl, hG'⟩
      | some kp =>
        have hv := hv kp hk
        simp only [Option.map_some]
        rw [decaps_symP P hc kp.2 c]
        cases ho : (symP P cs (P.decaps sk)).decaps kp.2 c with
        | none => exact ⟨rfl, hG'⟩
        | some o =>
          simp only [Option.map_some]
          simp only [ho, Option.bind_some, id] at hv
          by_cases hcd : rc.role = .responder ∧ rc.key.isNone = true
          · simp only [hcd, and_self, ↓reduceIte]
            refine ⟨deliver_branch sk rs _ _ inp _ rc _ o _ hG'.roV hG'.inpV hv, ?_⟩
            refine Good.deliverD g ?_ (sid, pid) rc ?_ _ _ hv (Or.inr ⟨rfl, rfl⟩) ?_
            · exact hG'.congr g (by simp only [ltD_st]) (fun p h => by simpa only [ltD_st] using h)
                rfl rfl rfl
            · simp only [ltD_st]; exact hr
            · intro _ hro; rw [hro] at hcd; cases hcd.1
          · simp only [hcd, ↓reduceIte]
            exact ⟨rfl, hG'⟩

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem update_map_option {α β : Type} (f : α → β) (m : Inst → Option α) (x : Inst) (a : α) :
    (fun y => (Function.update m x (some a) y).map f) =
      Function.update (fun y => (m y).map f) x (some (f a)) := by
  funext y
  by_cases h : y = x
  · subst h; simp
  · simp [Function.update_of_ne h]

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
theorem newVal_send {cs : C} {sk : SK} (s : SimSt S W K PK (Option SK) (Option SS) C)
    (sid : SessionId) (pid : PartyId) (e : W) (c : C) (r : PDraw S K PK SK SS C × K) (kp)
    (hk : s.1.kem (sid, pid) = some kp) :
    ((symP P cs (P.decaps sk)).decaps kp.2 c).bind id =
      newVal P cs (P.decaps sk) s (.inr (.send sid pid e c)) r := by
  obtain ⟨pk', osk⟩ := kp
  simp only [newVal, hk]
  cases osk with
  | some sk' => simp only [symP]; cases P.decaps sk' c <;> rfl
  | none =>
    by_cases h : c = cs
    · simp [symP, h]
    · simp only [symP, h, ↓reduceIte]; cases P.decaps sk c <;> rfl

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
/-- A new session keeps the invariant. -/
theorem Good.addSession {pk : PK} {cs : C} {k : SS}
    {s s' : PSt S W K PK (Option SK) (Option SS) C} {inp : Inst → Option (PInp W (Option SS))}
    (h : Good g pk cs k s inp) (x : Inst) (peer : PartyId) (role : Role)
    (hn : s.x.st.recs x = none) (hst : s'.x.st = addSession s.x.st x peer role)
    (hro : s'.ro = s.ro) (hct : s'.ct = s.ct)
    (hkem : ∀ kp, s'.kem (gR g) = some kp → kp = (pk, none)) : Good g pk cs k s' inp := by
  have hrecs : ∀ y r, s'.x.st.recs y = some r →
      (y = x ∧ r = ⟨peer, role, .fresh, none⟩) ∨ (y ≠ x ∧ s.x.st.recs y = some r) := by
    intro y r hy
    rw [hst] at hy
    simp only [FAKE.addSession, hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hy
    by_cases hyx : y = x
    · subst hyx
      simp only [Function.update_self, Option.some.injEq] at hy
      exact Or.inl ⟨rfl, hy.symm⟩
    · rw [Function.update_of_ne hyx] at hy
      exact Or.inr ⟨hyx, hy⟩
  refine ⟨?_, h.inpV, ?_, ?_, hkem, ?_, ?_⟩
  · rw [hro]; exact h.roV
  · intro e he hn'
    rw [hro] at he
    rw [hst, addSession_corrupt]
    exact h.roN e he hn'
  · intro y r hy
    rcases hrecs y r hy with ⟨-, rfl⟩ | ⟨-, hy⟩
    · rfl
    · exact h.fresh y r hy
  · intro y hy
    rw [hct]
    have hyx : y ≠ x := by
      intro hc
      subst hc
      rw [hst] at hy
      simp [FAKE.addSession, hn] at hy
    have hy' : s.x.st.recs y = none := by
      rw [hst] at hy
      simpa [FAKE.addSession, hn, Function.update_of_ne hyx] using hy
    exact h.noRec y hy'
  · intro ri hri hrole hpe
    rw [hct]
    rcases hrecs _ ri hri with ⟨hgx, rfl⟩ | ⟨-, hri⟩
    · rw [hgx]
      have := h.noRec x hn
      exact ⟨(fun c hc => by rw [this.1] at hc; cases hc),
        (fun ip hip => by rw [this.2] at hip; cases hip)⟩
    · exact h.encI ri hri hrole hpe

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **A start of the simulator commutes with the interpretation**: from a state of the invariant,
on a draw that brings no concrete challenge key into the world of the reduction, the real start
with the eager challenge, from the interpreted state, is the interpretation of the start of the
world of the reduction, which keeps the invariant. -/
theorem start_iSim {pk : PK} {sk : SK} {k : SS} {cs : C} (hc : P.decaps sk cs = some k)
    (s : SimSt S W K PK (Option SK) (Option SS) C) (hG : Good g pk cs k s.1 s.2.1)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K)
    (hv : newVal P cs (P.decaps sk) s e r ≠ some k) :
    simStartD P G (iSim k sk s) e
        (subKC g pk (k, cs) (iSim k sk s) e (subKP g (pk, sk) (iSim k sk s) e r)).1 =
      (iSim k sk (simStartD (symP P cs (P.decaps sk)) G s (liftE e)
          (liftD g pk cs s e r).1).1,
        (simStartD (symP P cs (P.decaps sk)) G s (liftE e) (liftD g pk cs s e r).1).2) ∧
      Good g pk cs k (simStartD (symP P cs (P.decaps sk)) G s (liftE e)
          (liftD g pk cs s e r).1).1.1
        (simStartD (symP P cs (P.decaps sk)) G s (liftE e) (liftD g pk cs s e r).1).1.2.1 := by
  obtain ⟨rs, inp, ph⟩ := s
  have hG' : Good g pk cs k rs inp := hG
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | q)
  · simp only [simStartD, liftE, iSim_fst, iSim_snd, iP_x]
    by_cases hn : (rs.x.st.recs (sid, pid)).isNone = true
    · simp only [hn, ↓reduceIte]
      have hn' : rs.x.st.recs (sid, pid) = none := Option.isNone_iff_eq_none.mp hn
      by_cases hro : role = .responder
      · simp only [hro, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · simp only [subKC, subKP, liftD]
          rw [isCreate_iSim]
          simp only [iSim, iP, update_map_option]
          cases isCreate g (rs, inp, ph) (liftE (Sum.inl (HEv.newSession sid pid peer .responder)))
            <;> rfl
        · refine hG'.addSession g (sid, pid) peer .responder hn' rfl rfl rfl fun kp hkp => ?_
          dsimp only at hkp
          by_cases hx : (sid, pid) = gR g
          · rw [← hx, Function.update_self, Option.some.injEq] at hkp
            have hc : isCreate g (rs, inp, ph) (liftE (Sum.inl (HEv.newSession sid pid peer
                .responder))) = true := by
              simp only [gR, Prod.mk.injEq] at hx
              obtain ⟨rfl, rfl⟩ := hx
              simp [isCreate, liftE, hn']
            simp only [liftD, hc, ↓reduceIte] at hkp
            exact hkp.symm
          · rw [Function.update_of_ne (Ne.symm hx)] at hkp
            exact hG'.kemR kp hkp
      · simp only [hro, ↓reduceIte]
        exact ⟨rfl, hG'.addSession g (sid, pid) peer role hn' rfl rfl rfl hG'.kemR⟩
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, hG'⟩
  · exact ⟨rfl, hG'⟩
  · exact ⟨rfl, hG'⟩
  · simp only [simStartD, liftE]
    refine ⟨rfl, hG'.congr g ?_ ?_ rfl rfl rfl⟩
    · exact (pollStep_fst _).1
    · intro p hp; rw [(pollStep_fst _).2.1]; exact hp
  · simp only [simStartD, liftE]
    exact ⟨rfl, hG'.congr g (by simp only [ltD_st]) (fun p h => by simpa only [ltD_st] using h)
      rfl rfl rfl⟩
  · exact ⟨rfl, hG'⟩
  · refine ⟨?_, hG'⟩
    simp only [simStartD, liftE, iSim_fst, iSim_snd, pkOf_iP, iP_ct]
    rfl
  · simp only [simStartD, liftE, iSim_fst, iSim_snd, iP_x]
    by_cases hN : Named rs.x.st pid = true
    · simp only [hN, ↓reduceIte]; exact ⟨rfl, hG'⟩
    · simp only [hN, Bool.false_eq_true, ↓reduceIte]
      refine ⟨rfl, hG'.congr g (by simp [corruptStep]) (fun p hp => ?_) rfl rfl rfl⟩
      simp only [corruptStep, ltD_st]
      by_cases hp' : p = pid
      · subst hp'; simp
      · rw [Function.update_of_ne hp']; exact hp
  · have h := complete_iSim G g (sk := sk) (rs, inp, ph) hG sid pid r.1.1 r.1.2.2 hv
    simp only [simStartD, liftE, subKC, subKP, liftD]
    rw [isEnc_iSim]
    exact h
  · have h := send_iSim P G g hc (rs, inp, ph) hG sid pid e c r.1.1
      (fun kp hk => (newVal_send P (rs, inp, ph) sid pid e c r kp hk).symm ▸ hv)
    simp only [simStartD, liftE, subKC, subKP, liftD]
    exact h
  · have hq : (some q.2 : Option SS) ≠ some k := hv
    simp only [simStartD, liftE, iSim_fst, iSim_snd]
    refine ⟨?_, ⟨fun e he => ?_, hG'.inpV, fun e he hn => ?_, hG'.fresh, hG'.kemR, hG'.noRec,
      hG'.encI⟩⟩
    · rw [show (iP k sk rs).ro = rs.ro.map (iE k) from rfl,
        show q = iInp k (q.1, some q.2) from rfl,
        roDet_map_iE rs.ro (q.1, some q.2) _ hG'.roV hq]
      rfl
    · rcases roDet_mem rs.ro (q.1, some q.2) _ e he with he | rfl
      · exact hG'.roV e he
      · exact hq
    · rcases roDet_mem rs.ro (q.1, some q.2) _ e he with he | rfl
      · exact hG'.roN e he hn
      · cases hn

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **A step of the simulated world commutes with the interpretation.** -/
theorem world_iSim {pk : PK} {sk : SK} {k : SS} {cs : C} (hc : P.decaps sk cs = some k)
    (s : SimSt S W K PK (Option SK) (Option SS) C) (f : St K) (hG : Good g pk cs k s.1 s.2.1)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K)
    (hv : newVal P cs (P.decaps sk) s e r ≠ some k) :
    simWorldD P G (iSim k sk s, f) e
        (subKC g pk (k, cs) (iSim k sk s) e (subKP g (pk, sk) (iSim k sk s) e r)) =
      ((iSim k sk (simWorldD (symP P cs (P.decaps sk)) G (s, f) (liftE e)
          (liftD g pk cs s e r)).1.1,
        (simWorldD (symP P cs (P.decaps sk)) G (s, f) (liftE e) (liftD g pk cs s e r)).1.2),
        (simWorldD (symP P cs (P.decaps sk)) G (s, f) (liftE e) (liftD g pk cs s e r)).2) ∧
      Good g pk cs k (simWorldD (symP P cs (P.decaps sk)) G (s, f) (liftE e)
          (liftD g pk cs s e r)).1.1.1
        (simWorldD (symP P cs (P.decaps sk)) G (s, f) (liftE e) (liftD g pk cs s e r)).1.1.2.1 := by
  obtain ⟨h₁, h₂⟩ := start_iSim P G g hc s hG e r hv
  refine ⟨?_, ?_⟩
  · simp only [simWorldD]
    rw [h₁]
    generalize simStartD (symP P cs (P.decaps sk)) G s (liftE e) (liftD g pk cs s e r).1 = q
    obtain ⟨q₁, q₂ | q₂⟩ := q <;> rfl
  · rw [simWorldD_fst, simWorldD_inp]
    exact h₂

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq C] in
/-- On states of the invariant and with a correct challenge, the KEM part of the bad event at the
guess does not hold in the interpreted state. -/
theorem not_EG_iSim {pk : PK} {sk : SK} {k : SS} {cs : C} (hc : P.decaps sk cs = some k)
    (s : SimSt S W K PK (Option SK) (Option SS) C) (hG : Good g pk cs k s.1 s.2.1)
    (dlv : Inst → Option C) : ¬ EG P G g (iSim k sk s) dlv := by
  rintro ⟨y, r, ip, v, h₁, h₂, h₃, h₄, h₅, h₆, -, h₈, h₉, h₁₀⟩
  obtain ⟨rs, inp, ph⟩ := s
  have hG' : Good g pk cs k rs inp := hG
  simp only [iSim_fst, iSim_snd, iP_x] at h₁ h₂ h₄ h₅ h₈ h₉ h₁₀
  obtain ⟨ips, hips, rfl⟩ := Option.map_eq_some_iff.mp h₂
  have hnone : ips.2 = none := by
    rcases h₁₀ with ⟨rfl, hro, hpe⟩ | ⟨rfl, hro, hpe, ri, hri, hrir, hrip⟩
    · exact (hG'.encI r h₁ hro hpe).2 ips hips
    · have hdlv : dlv (gR g) = (iP k sk rs).ct (gI g) := by
        rcases h₉ with h | ⟨-, h⟩
        · rw [hro] at h; cases h
        · rw [h, hpe]; rfl
      rcases h₈ with ⟨h, -⟩ | ⟨-, c, pk', sk', hc', hk', -, hd⟩
      · rw [hro] at h; cases h
      · rw [hdlv, iP_ct] at hc'
        have hcs : c = cs := (hG'.encI ri hri hrir hrip).1 c hc'
        subst hcs
        rw [iP_kem] at hk'
        obtain ⟨kp, hkp, hkp'⟩ := Option.map_eq_some_iff.mp hk'
        have hkp₀ := hG'.kemR kp hkp
        subst hkp₀
        simp only [Prod.mk.injEq, Option.getD_none] at hkp'
        rw [← hkp'.2, hc, Option.some.injEq] at hd
        have hv := hG'.inpV _ _ hips
        simp only [iInp] at hd
        cases h : ips.2 with
        | none => rfl
        | some v' => rw [h] at hd hv; simp only [Option.getD_some] at hd; subst hd; exact (hv rfl).elim
  obtain ⟨e, he, hee⟩ : ∃ e ∈ rs.ro, iInp k e.1 = iInp k ips := by
    have hm := lookup_mem h₃
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hm
    exact ⟨e, he, congrArg Prod.fst hee⟩
  cases h : e.1.2 with
  | some v' =>
    have : v' = k := by
      have := congrArg Prod.snd hee
      simp only [iInp, h, hnone, Option.getD_some, Option.getD_none] at this
      exact this
    exact hG'.roV e he (by rw [h, this])
  | none =>
    have hx : e.1.1 = ips.1 := by simpa only [iInp] using congrArg Prod.fst hee
    have hsh : (ips.1.ini = y.2 ∨ ips.1.ini = r.peer) ∧ (ips.1.res = y.2 ∨ ips.1.res = r.peer) := by
      obtain ⟨-, ⟨-, hi, hr⟩ | ⟨-, hr, hi⟩⟩ := h₆ <;> simp only [iInp] at hi hr <;>
        exact ⟨by simp [hi], by simp [hr]⟩
    rcases hG'.roN e he h with hc' | hc' <;> rw [hx] at hc'
    · rcases hsh.1 with h' | h' <;> rw [h'] at hc' <;> simp_all
    · rcases hsh.2 with h' | h' <;> rw [h'] at hc' <;> simp_all

open Classical in
/-- **The eager world and the world of the reduction are coupled until the challenge key is
hit.** For a correct challenge, the KEM part of the bad event at the guess `g` in the world with
the eager challenge is at most the probability that the world of the reduction receives the
challenge key as a concrete shared secret. -/
theorem gw_le_y {pk : PK} {sk : SK} {k : SS} {cs : C} (hc : P.decaps sk cs = some k)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => EG P G g x.2.1.1 x.2.2)
        (gwO P G g (pk, sk) (k, cs))) B (wInit, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => k ∈ x.2.2)
        (yO P G g pk cs (P.decaps sk))) B (yInit, false)).toOuterMeasure
          {y | y.2.2 = true} := by
  have h := flag_le_of_coupling_hit (fun t e => simDist P (encPk t.1.1.1 e))
    (fun t e => simDist P (encPk t.1.1.1 (liftE e)))
    (fun t e r => wStep P G t e (subKC g pk (k, cs) t.1.1 e (subKP g (pk, sk) t.1.1 e r)))
    (fun t e r => yStep P G g pk cs (P.decaps sk) t e r)
    (fun t₁ t₂ => t₁.1.1 = iSim k sk t₂.1.1 ∧ t₁.1.2 = t₂.1.2 ∧
      Good g pk cs k t₂.1.1.1 t₂.1.1.2.1)
    (fun t => EG P G g t.1.1 t.2) (fun t => k ∈ t.2) ?_ ?_ ?_ B wInit yInit
    ⟨rfl, rfl, good_init g pk cs k⟩
  · exact h
  · rintro t₁ t₂ e ⟨h₁, -, -⟩
    simp only [h₁, encPk_iSim]
  · rintro t₁ t₂ ⟨h₁, -, h₃⟩ hb
    simp only [h₁] at hb
    exact (not_EG_iSim P G g hc t₂.1.1 h₃ t₁.2 hb).elim
  · rintro ⟨⟨t₁, f₁⟩, dlv⟩ ⟨⟨t₂, f₂⟩, L⟩ e r ⟨h₁, h₂, h₃⟩
    dsimp only at h₁ h₂ h₃
    subst h₁ h₂
    by_cases hv : newVal P cs (P.decaps sk) t₂ e r = some k
    · left
      simp [yStep, hv]
    · right
      obtain ⟨he, hg⟩ := world_iSim P G g hc t₂ f₁ h₃ e r hv
      simp only [wStep, yStep, he, true_and]
      exact hg

end SymWorld

/-! ## The IND-CCA reduction -/

section Reduction

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
/-- The encapsulation that the event `e` asks the decapsulation oracle for: the delivered
encapsulation of a `send`, other than the challenge `cs`. -/
def needQ (cs : C) : OEv W SS C → Option C
  | .inr (.send _ _ _ c) => if c = cs then none else some c
  | _ => none

/-- The answer of a stepped oracle program with queries to the query `e` from the state `t`: the
query to an oracle that the step needs (`need`), one draw of `μ`, and the step with the answer. -/
noncomputable def stepImplQ {σ E A V Q Ans : Type} (need : σ → E → Option Q)
    (μ : σ → E → PMF V) (step : Option Ans → σ → E → V → σ × A) (t : σ) (e : E) :
    OracleAdv Q Ans (A × σ) :=
  match need t e with
  | some c => .query c fun a => .rand (μ t e) fun r =>
      let p := step (some a) t e r; .ret (p.2, p.1)
  | none => .rand (μ t e) fun r => let p := step none t e r; .ret (p.2, p.1)

/-- **A stepped oracle program with queries**: the oracle adversary `B` runs against a world
stepped by one draw of `μ` per query, after the query to an oracle that the step needs
(`need`), whose answer the step reads; the output is the extraction `ext` of the final state.
It is `X3DHSquareGDH.stepRedD` with one oracle query per step. -/
noncomputable def stepRedQ {σ E A V Q Ans Out : Type} (need : σ → E → Option Q)
    (μ : σ → E → PMF V) (step : Option Ans → σ → E → V → σ × A) (ext : σ → Out)
    (B : OracleAdv E A Bool) (s₀ : σ) : OracleAdv Q Ans Out :=
  (OracleAdv.simulate (stepImplQ need μ step) B s₀).bind fun p => .ret (ext p.2)

/-- A step of the world of the reduction with the answer of the decapsulation oracle. -/
noncomputable def kemStep (pk : PK) (cs : C) (oa : Option (Option SS)) (t : YSt S W K PK SK SS C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) :
    YSt S W K PK SK SS C × OOut S W K PK C :=
  let p := yStep P G g pk cs (fun _ => oa.getD none) t e r; (p.2, p.1)

/-- **The program of the IND-CCA reduction at the guess `g`**: on the public key `pk`, the
challenge encapsulation `cs` and the key `k`, it runs the oracle adversary `B` against the world
of the reduction, answering each delivered encapsulation other than `cs` with the decapsulation
oracle, and outputs whether `k` is among the concrete shared secrets of the world. -/
noncomputable def kemRedRun (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) (pk : PK)
    (cs : C) (k : SS) : OracleAdv C (Option SS) Bool :=
  stepRedQ (fun _ e => needQ cs e) (fun t e => simDist P (encPk t.1.1.1 (liftE e)))
    (kemStep P G g pk cs) (fun t => decide (k ∈ t.2)) B yInit

/-- The answer of the reduction to an event of the adversary: the query to the decapsulation
oracle that the event needs, a draw of the simulated world, and a step of the world of the
reduction with the answer of the oracle. -/
noncomputable def implK (pk : PK) (cs : C) (t : YSt S W K PK SK SS C) (e : OEv W SS C) :
    OracleAdv C (Option SS) (OOut S W K PK C × YSt S W K PK SK SS C) :=
  match needQ cs e with
  | some c => .query c fun a => .rand (simDist P (encPk t.1.1.1 (liftE e))) fun r =>
      let p := kemStep P G g pk cs (some a) t e r; .ret (p.2, p.1)
  | none => .rand (simDist P (encPk t.1.1.1 (liftE e))) fun r =>
      let p := kemStep P G g pk cs none t e r; .ret (p.2, p.1)

/-- The reduction asks at most as many decapsulation queries as the adversary asks queries. -/
theorem kemRedRun_isQueryBound {B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool} {q : ℕ}
    (hB : B.IsQueryBound q) (pk : PK) (cs : C) (k : SS) :
    (kemRedRun P G g B pk cs k).IsQueryBound q := by
  have h := OracleAdv.isQueryBound_simulate_mul (c := 1) (impl := implK P G g pk cs)
    (fun t e => by
      unfold implK
      split
      · exact fun _ _ => trivial
      · exact fun _ => trivial) hB yInit
  rw [Nat.mul_one] at h
  have h' := OracleAdv.isQueryBound_bind (n := 0)
    (f := fun x => OracleAdv.ret (decide (k ∈ x.2.2))) h fun _ => trivial
  rw [Nat.add_zero] at h'
  exact h'

/-- **The IND-CCA reduction at the guess `g`**, for an oracle adversary with at most `q`
queries. -/
noncomputable def kemRed (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ}
    (hB : B.IsQueryBound q) : KEM.Games.INDCCAAdversary PK SS C q :=
  ⟨kemRedRun P G g B, kemRedRun_isQueryBound P G g hB⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- A step of the world of the reduction reads the decapsulation oracle only at the delivered
encapsulation of a `send` other than the challenge. -/
theorem yStep_congr {pk : PK} {cs : C} {d₁ d₂ : C → Option SS} (t : YSt S W K PK SK SS C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K)
    (hd : ∀ sid pid w c, e = .inr (.send sid pid w c) → c ≠ cs → d₁ c = d₂ c) :
    yStep P G g pk cs d₁ t e r = yStep P G g pk cs d₂ t e r := by
  rcases e with (_ | _) | (_ | _ | _ | _ | _ | _ | _ | ⟨sid, pid, w, c⟩ | _) <;> try rfl
  have h : ∀ osk, (symP P cs d₁).decaps osk c = (symP P cs d₂).decaps osk c := by
    intro osk
    cases osk with
    | some _ => rfl
    | none =>
      by_cases hc : c = cs
      · simp [symP, hc]
      · simp [symP, hc, hd sid pid w c rfl hc]
  have h' : newVal P cs d₁ t.1.1 (.inr (.send sid pid w c)) r =
      newVal P cs d₂ t.1.1 (.inr (.send sid pid w c)) r := by
    simp only [newVal]
    split
    · rfl
    · by_cases hc : c = cs
      · simp [hc]
      · simp [hc, hd sid pid w c rfl hc]
    · rfl
  simp only [yStep, simWorldD, simStartD, liftE, simSendD, h, h']

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
theorem needQ_some {cs : C} {e : OEv W SS C} {c : C} (h : needQ cs e = some c) :
    ∃ sid pid w, e = .inr (.send sid pid w c) ∧ c ≠ cs := by
  rcases e with (_ | _) | (_ | _ | _ | _ | _ | _ | _ | ⟨sid, pid, w, c'⟩ | _) <;>
    simp only [needQ, reduceCtorEq] at h
  by_cases hc : c' = cs
  · simp [hc] at h
  · simp only [hc, ↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨sid, pid, w, rfl, hc⟩

/-- **The reduction against the decapsulation oracle is the world of the reduction** with the
decapsulation under the challenge secret key. -/
theorem simOracle_implK (pk : PK) (cs : C) (sk : SK) (t : YSt S W K PK SK SS C)
    (e : OEv W SS C) :
    OracleAdv.simOracle (implK P G g pk cs) (KEM.Games.decapsOracle P sk cs) (t, ()) e =
      (yO P G g pk cs (P.decaps sk) t e).map fun x => (x.1, (x.2, ())) := by
  unfold OracleAdv.simOracle implK yO kemStep
  cases h : needQ cs e with
  | none =>
    simp only [OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map, PMF.map_comp]
    rw [PMF.map]
    refine PMF.bind_congr_support _ _ _ fun r _ => ?_
    rw [yStep_congr P G g t e r (d₂ := P.decaps sk) fun sid pid w c he hc => by
      subst he; simp [needQ, hc] at h]
    rfl
  | some c =>
    obtain ⟨sid, pid, w, he, hc⟩ := needQ_some h
    simp only [OracleAdv.run_query, KEM.Games.decapsOracle, hc, ↓reduceIte, PMF.pure_bind,
      OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map, PMF.map_comp]
    rw [PMF.map]
    refine PMF.bind_congr_support _ _ _ fun r _ => ?_
    rw [yStep_congr P G g t e r (d₂ := P.decaps sk) fun sid' pid' w' c' he' _ => by
      rw [he] at he'
      simp only [Sum.inr.injEq, PAEv.send.injEq] at he'
      rw [← he'.2.2.2]
      rfl]
    rfl

/-- **The output of the reduction** against the decapsulation oracle of the challenge: whether
the key is among the concrete shared secrets of the final state of the world of the reduction. -/
theorem run_kemRedRun (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) (pk : PK) (cs : C)
    (sk : SK) (k : SS) :
    (OracleAdv.run (KEM.Games.decapsOracle P sk cs) (kemRedRun P G g B pk cs k) ()).map
        Prod.fst =
      (OracleAdv.run (yO P G g pk cs (P.decaps sk)) B yInit).map fun x => decide (k ∈ x.2.2) := by
  have hm := OracleAdv.run_map_state (yO P G g pk cs (P.decaps sk))
    (OracleAdv.simOracle (implK P G g pk cs) (KEM.Games.decapsOracle P sk cs)) (fun s => (s, ()))
    (fun t e => (simOracle_implK P G g pk cs sk t e).symm) B yInit
  change (OracleAdv.run (KEM.Games.decapsOracle P sk cs)
    ((OracleAdv.simulate (implK P G g pk cs) B yInit).bind fun x =>
      .ret (decide (k ∈ x.2.2))) ()).map Prod.fst = _
  rw [OracleAdv.run_bind, OracleAdv.run_simulate, ← hm]
  simp only [PMF.map_comp, PMF.bind_map, PMF.map_bind, OracleAdv.run_ret, Function.comp_apply,
    PMF.pure_map]
  rfl

end Reduction

/-! ## The bound of the KEM route -/

section Length

variable {σ D R α : Type}

/-- A run of an adversary with at most `q` queries against an oracle whose steps grow a length
by at most one reaches lengths at most `q` above the start. -/
theorem run_support_len (O : σ → D → PMF (R × σ)) (len : σ → ℕ)
    (h : ∀ s d, ∀ x ∈ (O s d).support, len x.2 ≤ len s + 1) (A : OracleAdv D R α) (q : ℕ)
    (hA : A.IsQueryBound q) (s : σ) : ∀ x ∈ (OracleAdv.run O A s).support, len x.2 ≤ len s + q := by
  induction A generalizing q s with
  | ret a =>
    intro x hx
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact Nat.le_add_right _ _
  | rand p k ih =>
    intro x hx
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ih b q (hA b) s x hb
  | query d k ih =>
    intro x hx
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    cases q with
    | zero => exact hA.elim
    | succ q =>
      have h₁ := ih y.1 q (hA y.1) y.2 x hxy
      have h₂ := h s d y hy
      omega

end Length

section Bound

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [Fintype SS] [Nonempty SS] [DecidableEq C]
  (P : Scheme PK SK SS C) (G : DHGroup S W) (g : Guess)

omit [Fintype SS] [Nonempty SS] in
theorem yO_len (pk : PK) (cs : C) (dec : C → Option SS) (t : YSt S W K PK SK SS C)
    (e : OEv W SS C) : ∀ x ∈ (yO P G g pk cs dec t e).support, x.2.2.length ≤ t.2.length + 1 := by
  intro x hx
  simp only [yO, PMF.support_map, Set.mem_image] at hx
  obtain ⟨r, -, rfl⟩ := hx
  simp only [yStep, List.length_append]
  have : (newVal P cs dec t.1.1 e r).toList.length ≤ 1 := by
    cases newVal P cs dec t.1.1 e r <;> simp
  omega

omit [DecidableEq SS] in
/-- A uniform key lies in a list with probability at most its length over the number of keys. -/
theorem uniform_mem_le [DecidableEq SS] (L : List SS) :
    ((PMF.uniformFintype SS).map fun k => decide (k ∈ L)) true ≤
      (L.length : ℝ≥0∞) * (Fintype.card SS : ℝ≥0∞)⁻¹ := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hs : (fun k => decide (k ∈ L)) ⁻¹' {true} = {k | k ∈ L} := by
    ext k; simp
  rw [hs]
  clear hs
  induction L with
  | nil => simp
  | cons a L ih =>
    have hu : {k | k ∈ a :: L} = {a} ∪ {k | k ∈ L} := by
      ext k; simp
    rw [hu]
    refine (MeasureTheory.measure_union_le _ _).trans ?_
    rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformFintype_apply, List.length_cons,
      Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
    gcongr

omit [DecidableEq SS] in
/-- **The random case**: a uniform key independent of a distribution of lists of length at most
`q` lies in the list with probability at most `q` over the number of keys. -/
theorem uniform_bind_mem_le [DecidableEq SS] {α : Type} (Rd : PMF α) (L : α → List SS) (q : ℕ)
    (hR : ∀ y ∈ Rd.support, (L y).length ≤ q) :
    ((PMF.uniformFintype SS).bind fun k => Rd.map fun y => decide (k ∈ L y)) true ≤
      (q : ℝ≥0∞) * (Fintype.card SS : ℝ≥0∞)⁻¹ := by
  have h : ((PMF.uniformFintype SS).bind fun k => Rd.map fun y => decide (k ∈ L y)) =
      Rd.bind fun y => (PMF.uniformFintype SS).map fun k => decide (k ∈ L y) := by
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  rw [h, PMF.bind_apply]
  calc ∑' y, Rd y * ((PMF.uniformFintype SS).map fun k => decide (k ∈ L y)) true
      ≤ ∑' y, Rd y * ((q : ℝ≥0∞) * (Fintype.card SS : ℝ≥0∞)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hy : y ∈ Rd.support
        · gcongr
          refine (uniform_mem_le (L y)).trans ?_
          gcongr
          exact hR y hy
        · rw [(PMF.apply_eq_zero_iff Rd y).mpr hy, zero_mul, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [Fintype SS] [Nonempty SS] [DecidableEq C] in
/-- A bind is at most a bound of its continuations. -/
theorem bind_true_le {α : Type} (p : PMF α) (f : α → PMF Bool) (c : ℝ≥0∞)
    (h : ∀ a, f a true ≤ c) : (p.bind f) true ≤ c := by
  rw [PMF.bind_apply]
  calc ∑' a, p a * f a true ≤ ∑' a, p a * c := ENNReal.tsum_le_tsum fun a => by gcongr; exact h a
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Fintype SS] [Nonempty SS] in
/-- A run of the world of the reduction by an adversary with at most `q` queries receives at
most `q` concrete shared secrets. -/
theorem run_yO_len (pk : PK) (cs : C) (dec : C → Option SS)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ} (hB : B.IsQueryBound q) :
    ∀ x ∈ (OracleAdv.run (yO P G g pk cs dec) B yInit).support, x.2.2.length ≤ q := by
  intro x hx
  have := run_support_len (yO P G g pk cs dec) (fun t => t.2.length) (yO_len P G g pk cs dec) B q
    hB yInit x hx
  simpa [yInit] using this

/-- **The random case of the IND-CCA game of the reduction**: at most `q` over the number of
shared secrets, for an adversary with at most `q` queries. -/
theorem indccaGame_false_le (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ}
    (hB : B.IsQueryBound q) :
    (KEM.Games.indccaGame P (kemRed P G g B hB) false) true ≤
      (q : ℝ≥0∞) * (Fintype.card SS : ℝ≥0∞)⁻¹ := by
  unfold KEM.Games.indccaGame
  simp only [Bool.false_eq_true, ↓reduceIte, kemRed, run_kemRedRun]
  refine bind_true_le _ _ _ fun ks => bind_true_le _ _ _ fun x => ?_
  exact uniform_bind_mem_le (OracleAdv.run (yO P G g ks.1 x.2 (P.decaps ks.2)) B yInit)
    (fun y => y.2.2) q (run_yO_len P G g _ _ _ B hB)

/-- **The real case of the IND-CCA game of the reduction**: the probability that the world of
the reduction with the challenge receives the encapsulated key. -/
theorem indccaGame_true_eq (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ}
    (hB : B.IsQueryBound q) :
    (KEM.Games.indccaGame P (kemRed P G g B hB) true) true =
      ∑' kp, P.keygen kp * ∑' kc, P.encaps kp.1 kc *
        ((OracleAdv.run (yO P G g kp.1 kc.2 (P.decaps kp.2)) B yInit).map
          fun x => decide (kc.1 ∈ x.2.2)) true := by
  unfold KEM.Games.indccaGame
  simp only [↓reduceIte, kemRed, run_kemRedRun, PMF.bind_const]
  rw [PMF.bind_apply]
  refine tsum_congr fun kp => ?_
  rw [PMF.bind_apply]

omit [Fintype SS] [Nonempty SS] [DecidableEq C] in
/-- The correctness error as a sum over key pairs and encapsulations. -/
theorem corrErr_eq :
    P.corrErr = ∑' kp, P.keygen kp * ∑' kc, P.encaps kp.1 kc *
      (PMF.pure (decide (P.decaps kp.2 kc.2 ≠ some kc.1))) true := by
  unfold KEM.Games.Scheme.corrErr
  rw [PMF.bind_apply]
  refine tsum_congr fun kp => ?_
  rw [PMF.map, PMF.bind_apply]
  rfl

omit [Fintype SS] [Nonempty SS] in
open Classical in
/-- The flag of the challenge key in the world of the reduction is the probability that the
final state holds it. -/
theorem flag_y_le (pk : PK) (cs : C) (dec : C → Option SS) (k : SS)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => k ∈ x.2.2)
        (yO P G g pk cs dec)) B (yInit, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ((OracleAdv.run (yO P G g pk cs dec) B yInit).map fun x => decide (k ∈ x.2.2)) true := by
  refine (run_flag_le_final (yO P G g pk cs dec) (fun t => k ∈ t.2) (fun t e h x hx => ?_) B
    yInit).trans ?_
  · simp only [yO, PMF.support_map, Set.mem_image] at hx
    obtain ⟨r, -, rfl⟩ := hx
    simp only [yStep, List.mem_append]
    exact Or.inl h
  · rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    refine PMF.toOuterMeasure_mono _ fun y hy => ?_
    simpa using hy.1

open Classical in
/-- **The KEM part of the bad event at a guess, under the real case of IND-CCA**: at most the
real case of the IND-CCA game of the reduction plus the correctness error of the KEM. -/
theorem flagEG_le (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ}
    (hB : B.IsQueryBound q) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => EG P G g x.2.1.1 x.2.2) (wO P G)) B
        (wInit, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (KEM.Games.indccaGame P (kemRed P G g B hB) true) true + P.corrErr := by
  rw [flag_w_eq_gw1 P G g (fun x => EG P G g x.1.1 x.2) B, indccaGame_true_eq, corrErr_eq,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun kp => ?_
  rw [← mul_add, ← ENNReal.tsum_add, flag_gw1_eq_gw P G g (fun x => EG P G g x.1.1 x.2) kp B]
  gcongr with kc
  rw [← mul_add]
  gcongr
  by_cases hc : P.decaps kp.2 kc.2 = some kc.1
  · exact le_add_right ((gw_le_y P G g (pk := kp.1) (sk := kp.2) hc B).trans
      (flag_y_le P G g _ _ _ _ B))
  · refine le_add_left ((toOuterMeasure_le_one _ _).trans_eq ?_)
    simp [hc]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq SS]
  [Field S] [DecidableEq C] in
/-- The real case of an IND-CCA game is at most the random case plus the advantage. -/
theorem indccaGame_true_le [DecidableEq C] {q : ℕ} (A : KEM.Games.INDCCAAdversary PK SS C q) :
    (KEM.Games.indccaGame P A true) true ≤
      (KEM.Games.indccaGame P A false) true + KEM.Games.indccaAdvantage P A := by
  unfold KEM.Games.indccaAdvantage Advantage
  simp only [prTrue_liftPMF]
  rw [add_comm]
  calc (KEM.Games.indccaGame P A true) true
      ≤ ((KEM.Games.indccaGame P A true) true - (KEM.Games.indccaGame P A false) true) +
          (KEM.Games.indccaGame P A false) true := le_tsub_add
    _ ≤ _ := by gcongr; exact le_sup_left

open Classical in
/-- **The KEM part of the bad event at a guess under IND-CCA.** -/
theorem flagEG_le_indcca (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ}
    (hB : B.IsQueryBound q) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => EG P G g x.2.1.1 x.2.2) (wO P G)) B
        (wInit, false)).toOuterMeasure {y | y.2.2 = true} ≤
      KEM.Games.indccaAdvantage P (kemRed P G g B hB) + P.corrErr +
        (q : ℝ≥0∞) / (Fintype.card SS : ℝ≥0∞) := by
  refine (flagEG_le P G g B hB).trans ?_
  have h₁ := indccaGame_true_le P (kemRed P G g B hB)
  have h₂ := indccaGame_false_le P G g B hB
  rw [div_eq_mul_inv]
  calc (KEM.Games.indccaGame P (kemRed P G g B hB) true) true + P.corrErr
      ≤ (q : ℝ≥0∞) * (Fintype.card SS : ℝ≥0∞)⁻¹ +
          KEM.Games.indccaAdvantage P (kemRed P G g B hB) + P.corrErr := by
        gcongr
        exact h₁.trans (by gcongr)
    _ = _ := by ring

end Bound

/-! ## The main results -/

section Main

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [Fintype SS] [Nonempty SS] [DecidableEq C]
  (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- The bound of the KEM route: the sum over the guesses of `I × N × N` of the IND-CCA
advantage of the reduction at the guess, the correctness error of the KEM, and the number of
queries over the number of shared secrets. -/
noncomputable def kemBound (I : Finset SessionId) (N : Finset PartyId)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ} (hB : B.IsQueryBound q) :
    ℝ≥0∞ :=
  ∑ g ∈ I ×ˢ N ×ˢ N, (KEM.Games.indccaAdvantage P (kemRed P G g B hB) + P.corrErr +
    (q : ℝ≥0∞) / (Fintype.card SS : ℝ≥0∞))

open Classical in
/-- **The matched KEM part of the bad event under IND-CCA.** For an oracle adversary `B` that
starts sessions only with session identifiers of `I` between parties of `N` and asks at most `q`
queries, the probability of the KEM part of the bad event at matched sessions is at most the sum
over the guesses `g` of `I × N × N` of the IND-CCA advantage of the reduction `kemRed P G g B`,
the correctness error of the KEM, and `q` over the number of shared secrets. -/
theorem partBad_kem_le (I : Finset SessionId) (N : Finset PartyId)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) (hS : SessInK I N B) {q : ℕ}
    (hB : B.IsQueryBound q) :
    partBad P G (PQHitKemM P G) B ≤ kemBound P G I N B hB :=
  (partBad_le_sum_guess P G I N B hS).trans
    (Finset.sum_le_sum fun g _ => flagEG_le_indcca P G g B hB)

open Classical in
/-- **The bad event of the PQXDH square with the minimum over the two routes.** For an oracle
adversary `B` that names only parties of `N`, starts sessions only with session identifiers of
`I`, and asks at most `q` queries, the bad event is at most its part at unmatched sessions, which
only the route of Diffie–Hellman bounds, plus the minimum of the gap Diffie–Hellman sum and the
KEM bound for its part at matched sessions. -/
theorem badGame_le_min (I : Finset SessionId) (N : Finset PartyId)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) (hN : NamesInP N B) (hS : SessInK I N B)
    {q : ℕ} (hB : B.IsQueryBound q) :
    badGame P G B true ≤ partBad P G (PQHitDhM P G) B +
      min (∑ a ∈ N, ∑ b ∈ N, GapDH_Advantage (gapDHDef G) (pqGdhRed G P a b B))
        (kemBound P G I N B hB) := by
  refine (badGame_le_splitM P G B).trans ?_
  rw [add_comm]
  gcongr
  exact le_min (partBadM_le_gapDH P G N B hN).1 (partBad_kem_le P G I N B hS hB)

open Classical in
/-- The same bound with the Diffie–Hellman part bounded by the gap Diffie–Hellman sum. -/
theorem badGame_le_gapDH_min (I : Finset SessionId) (N : Finset PartyId)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) (hN : NamesInP N B) (hS : SessInK I N B)
    {q : ℕ} (hB : B.IsQueryBound q) :
    badGame P G B true ≤
      ∑ a ∈ N, ∑ b ∈ N, GapDH_Advantage (gapDHDef G) (pqGdhRed G P a b B) +
        min (∑ a ∈ N, ∑ b ∈ N, GapDH_Advantage (gapDHDef G) (pqGdhRed G P a b B))
          (kemBound P G I N B hB) :=
  (badGame_le_min P G I N B hN hS hB).trans (by gcongr; exact (partBadM_le_gapDH P G N B hN).2)

open Classical in
/-- The bound of the PQXDH square with the minimum over the two routes at the oracle adversary
`B`: the gap Diffie–Hellman sum plus the minimum of the gap Diffie–Hellman sum and the KEM bound,
when `B` names only parties of `N`, starts sessions only with session identifiers of `I` and
asks at most `q` queries, and `⊤` otherwise. -/
noncomputable def minBoundP (I : Finset SessionId) (N : Finset PartyId) (q : ℕ)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) : ℝ≥0∞ :=
  if h : NamesInP N B ∧ SessInK I N B ∧ B.IsQueryBound q then
    ∑ a ∈ N, ∑ b ∈ N, GapDH_Advantage (gapDHDef G) (pqGdhRed G P a b B) +
      min (∑ a ∈ N, ∑ b ∈ N, GapDH_Advantage (gapDHDef G) (pqGdhRed G P a b B))
        (kemBound P G I N B h.2.2)
  else ⊤

/-- **PQXDH realizes `F_AKE` behind `pqxdhSim` with the minimum over the two routes.** For every
finite set of session identifiers `I`, finite set of parties `N` and query bound `q`, and every
environment `Z` whose oracle reduction names only parties of `N`, starts sessions only with
session identifiers of `I` and asks at most `q` queries, the distance between the real PQXDH
protocol and the simulator running with `F_AKE` is at most the gap Diffie–Hellman sum plus the
minimum of the gap Diffie–Hellman sum and the KEM bound `kemBound`; the bound is `⊤` for the other
environments. -/
theorem pqxdh_realizesSim_min (I : Finset SessionId) (N : Finset PartyId) (q : ℕ) :
    RealizesSim (pqxdhReal (K := K) P G) (F_AKE (SPComp.sample K) true) (pqxdhSim P G)
      (fun _ Z => minBoundP P G I N q
        ((OProt.oracle (Q := OEv W SS C) (A := OOut S W K PK C)).reduction Z)) :=
  fun ζ Z => (pqxdh_realizesSim_oracleGame P G ζ Z).trans (by
    dsimp only
    unfold minBoundP
    split
    · rename_i h
      exact (pqxdh_advantage_le_badGame P G _).trans
        (badGame_le_gapDH_min P G I N _ h.1 h.2.1 h.2.2)
    · exact le_top)

end Main

end CatCrypt.Crypto.AKE.PQXDHSquareKEM

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

end CatCrypt.Crypto.AKE.PQXDHSquareKEM

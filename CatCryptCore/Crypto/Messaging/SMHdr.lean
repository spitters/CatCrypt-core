/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.FSAEADCorruptSM
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction

/-!
# The ACD construction with message headers in the associated data

The Double Ratchet specification encrypts a message with associated data
`CONCAT(ad, header)`, where the header of a message holds the public value `T` of the sender's
current sending epoch, the length `PN` of its previous sending chain and the position `N` of the
message in the current one. `acdHdrSM C R G D hdrAD` is the ACD construction whose party state
`SMHdrSt` is the state `SMPartySt` of `acdSMAD` with these header data `SMHdrData`: opening an
epoch records its public value and resets the counters, and sending encrypts with associated
data `hdrAD ad ((T, PN), N)` and advances `N`. A corruption reveals the header data with the
state; the ciphertext of a message is the AEAD ciphertext.

## The reduction to `sm_corrupt_game`

The header data are a function of the public transcript: the public value of an opening is the
answer to the opening, and `PN`, `N` count the answered sends. The wrapper adversary
`A.toHdr hdrAD` keeps the header data of both parties, asks each send and challenge of `A` with
associated data `hdrAD ad hdr` for the header `hdr` of the sending party, and completes each
corruption answer with the header data of the corrupted party. `smCorruptGame_acdHdr` proves
that the corruption game over `acdHdrSM` against `A` is `sm_corrupt_game` against
`A.toHdr hdrAD`.

## Main definitions

* `SMHdrData`, `SMHdrSt`, `acdHdrBase`, `acdHdrSM` — the header data, the party state, and the
  construction
* `smHdrImpl`, `SMSchemeAdv.toHdr` — the wrapper adversary

## Main results

* `smCorruptGame_acdHdr`, `acdHdrSM_corruptAdvantage_eq` — the corruption game over `acdHdrSM`
  is `sm_corrupt_game` at the wrapper adversary
* `acdHdrSM_corruptAdvantage_le_prim` — the bound from CKA, PRF-PRNG, PRG and AEAD security,
  every term an advantage of an explicit reduction of `A.toHdr hdrAD`
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## Header data -/

/-- The header data of a party: the public value of its sending epoch, the length of its
previous sending chain and the number of messages sent in its current sending chain. -/
structure SMHdrData (Msg : Type) where
  /-- The public value `T` of the sending epoch. -/
  pub : Msg
  /-- The length `PN` of the previous sending chain. -/
  pn : ℕ
  /-- The number `N` of messages sent in the current sending chain. -/
  ns : ℕ

namespace SMHdrData

variable {Msg : Type}

/-- The header `((T, PN), N)` of the next message. -/
def hdr (h : SMHdrData Msg) : (Msg × ℕ) × ℕ := ((h.pub, h.pn), h.ns)

/-- The header data after a query of the party with answer `a`: an opening with public value
`T` records `T` and resets the counters, a ciphertext advances `N`. -/
def step {Ct L : Type} (h : SMHdrData Msg) : SMSchemeAns Msg Ct L → SMHdrData Msg
  | .msg T => ⟨T, h.ns, 0⟩
  | .ct _ => ⟨h.pub, h.pn, h.ns + 1⟩
  | .none => h
  | .state _ => h

end SMHdrData

/-- The party state of the ACD construction with headers: the state of the ACD construction and
the header data. -/
structure SMHdrSt (Sc RK Sa Msg : Type) where
  /-- The state of the ACD construction. -/
  base : SMPartySt Sc RK Sa
  /-- The header data. -/
  hd : SMHdrData Msg

/-- The game state over the construction with headers from a game state over the ACD
construction and the header data `tr` of the parties. -/
def SMHdrSt.join {Sc RK Sa Msg : Type} (tr : CKAParty → SMHdrData Msg)
    (σ : SMSchemeSt (SMPartySt Sc RK Sa) Msg) : SMSchemeSt (SMHdrSt Sc RK Sa Msg) Msg :=
  ⟨⟨fun p => ⟨σ.ck.st p, tr p⟩, σ.ck.t, σ.ck.msg⟩, σ.done⟩

/-! ## The construction -/

section Construction

variable {Sc Msg Key Rand RK Sa W Ct AD : Type} [Fintype Rand] [Nonempty Rand]
  [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] {Kt : Type}
  [SampleableType Kt]

/-- The ACD construction at the header data `h`: `acdSMAD` with associated data
`hdrAD ad h.hdr` of the AEAD. -/
noncomputable def acdHdrBase (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → (Msg × ℕ) × ℕ → AD) (h : SMHdrData Msg) :
    SMScheme (SMPartySt Sc RK Sa) Msg Rand W Ct (SMPartySt Sc RK Sa) :=
  acdSMAD C R G D fun _ ad => hdrAD ad h.hdr

/-- **The ACD construction with message headers.** Both parties start with the state of
`acdSMAD` and the header data of the public value of the initialisation. Opening an epoch is the
opening of `acdSMAD`, records its public value as `T`, the number of messages sent as `PN`, and
sets `N` to `0`; receiving is the receiving of `acdSMAD`; sending from header data `h` is the
sending of `acdSMAD` with associated data `hdrAD ad h.hdr` of the AEAD, and advances `N`; a
corruption reveals the state with the header data. -/
noncomputable def acdHdrSM (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → (Msg × ℕ) × ℕ → AD) :
    SMScheme (SMHdrSt Sc RK Sa Msg) Msg Rand W Ct (SMHdrSt Sc RK Sa Msg) where
  init := SPComp.bind C.init fun i => SPComp.bind (SPComp.sample RK) fun rk =>
    SPComp.pure (i.1, ⟨⟨i.2.1, rk, none, none⟩, ⟨i.1, 0, 0⟩⟩,
      ⟨⟨i.2.2, rk, none, none⟩, ⟨i.1, 0, 0⟩⟩)
  ratchet x r :=
    (⟨((acdHdrBase C R G D hdrAD x.hd).ratchet x.base r).1,
        ⟨((acdHdrBase C R G D hdrAD x.hd).ratchet x.base r).2, x.hd.ns, 0⟩⟩,
      ((acdHdrBase C R G D hdrAD x.hd).ratchet x.base r).2)
  recv x T := ⟨(acdHdrBase C R G D hdrAD x.hd).recv x.base T, x.hd⟩
  send x m := ((acdHdrBase C R G D hdrAD x.hd).send x.base m).map fun y =>
    (⟨y.1, ⟨x.hd.pub, x.hd.pn, x.hd.ns + 1⟩⟩, y.2)
  expose := id
  idealCt := PMF.uniformFintype Ct

end Construction

/-! ## The wrapper adversary -/

section Wrapper

variable {Sc Msg RK Sa W Ct AD : Type}

/-- The step of the wrapper adversary from the header data `tr` of the parties: the query `d`
is asked with associated data `hdrAD ad hdr` for the header `hdr` of its party, a corruption
answer is completed with the header data of the party, and the header data of the party take
the step of the answer. -/
def smHdrImpl (hdrAD : W → (Msg × ℕ) × ℕ → AD) (tr : CKAParty → SMHdrData Msg)
    (d : SMQuery W) :
    OracleAdv (SMQuery W AD) (SMAns Sc Msg RK Sa Ct)
      (SMSchemeAns Msg Ct (SMHdrSt Sc RK Sa Msg) × (CKAParty → SMHdrData Msg)) :=
  .query (d.mapAD fun ad => hdrAD ad (tr d.party).hdr) fun a =>
    .ret (a.toScheme.map id id fun b => ⟨b, tr d.party⟩,
      Function.update tr d.party ((tr d.party).step a.toScheme))

/-- **The wrapper adversary.** An adversary of the game over `acdHdrSM C R G D hdrAD` as an
adversary of `sm_corrupt_game` with associated data in `AD`: it starts with the header data of
the public value `T` of the initialisation for both parties and answers each query of `A` by
`smHdrImpl hdrAD`. -/
def SMSchemeAdv.toHdr (hdrAD : W → (Msg × ℕ) × ℕ → AD)
    (A : SMSchemeAdv Msg W Ct (SMHdrSt Sc RK Sa Msg)) : SMCorruptAdv Sc Msg RK Sa W Ct AD where
  tStar := A.tStar
  play t T := (OracleAdv.simulate (smHdrImpl hdrAD) (A.play t T) fun _ => ⟨T, 0, 0⟩).bind
    fun x => .ret x.1

time_cert_try derive_reduction smHdrImpl

time_cert_try derive_reduction SMSchemeAdv.toHdr

/-- The wrapper adversary keeps the query bound of `A`. -/
theorem SMSchemeAdv.toHdr_play_isQueryBound (hdrAD : W → (Msg × ℕ) × ℕ → AD)
    {A : SMSchemeAdv Msg W Ct (SMHdrSt Sc RK Sa Msg)} {q : ℕ}
    (hA : ∀ t T, (A.play t T).IsQueryBound q) (t : ℕ) (T : Msg) :
    ((A.toHdr hdrAD).play t T).IsQueryBound q := by
  have himpl : ∀ tr d, (smHdrImpl (Sc := Sc) (RK := RK) (Sa := Sa) (Ct := Ct) hdrAD tr
      d).IsQueryBound 1 := by
    intro tr d
    exact fun _ => trivial
  simp only [SMSchemeAdv.toHdr]
  simpa using OracleAdv.isQueryBound_bind (n := 0) (f := fun x => OracleAdv.ret x.1)
    (OracleAdv.isQueryBound_simulate _ (fun _ => 1) himpl (hA t T).isQueryBoundBy_one _)
    (fun _ => trivial)

end Wrapper

/-! ## The game over the construction is `sm_corrupt_game` at the wrapper -/

/-- Relabelling the queries and the answers of an adversary by the identity is the
adversary. -/
theorem OracleAdv.mapQueryAnswer_id_id {D R α : Type} (A : OracleAdv D R α) :
    A.mapQueryAnswer id id = A := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.mapQueryAnswer, ih]
  | query d k ih => simp only [OracleAdv.mapQueryAnswer, id_eq, ih]

section Join

variable {Sc RK Sa Msg : Type} (tr : CKAParty → SMHdrData Msg)
  (σ : SMSchemeSt (SMPartySt Sc RK Sa) Msg)

/-- The joined state has the counters of `σ` (an unfolding lemma of `SMHdrSt.join`). -/
theorem SMHdrSt.join_ck_t : (SMHdrSt.join tr σ).ck.t = σ.ck.t := rfl

/-- The joined state has the party states of `σ` with the header data of `tr` (an unfolding
lemma of `SMHdrSt.join`). -/
theorem SMHdrSt.join_ck_st (p : CKAParty) : (SMHdrSt.join tr σ).ck.st p = ⟨σ.ck.st p, tr p⟩ :=
  rfl

/-- The joined state has the challenge flag of `σ` (an unfolding lemma of `SMHdrSt.join`). -/
theorem SMHdrSt.join_done : (SMHdrSt.join tr σ).done = σ.done := rfl

/-- An opening commutes with the join. -/
theorem SMHdrSt.join_sent (p : CKAParty) (x : SMPartySt Sc RK Sa) (h : SMHdrData Msg) (T : Msg)
    (d : Bool) :
    SMHdrSt.join (Function.update tr p h) ⟨σ.ck.sent p x T, d⟩ =
      ⟨(SMHdrSt.join tr σ).ck.sent p ⟨x, h⟩ T, d⟩ := by
  simp only [SMHdrSt.join, CKAGameSt.sent, SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

/-- A receive commutes with the join. -/
theorem SMHdrSt.join_recvd (p : CKAParty) (x : SMPartySt Sc RK Sa) (d : Bool) :
    SMHdrSt.join tr ⟨σ.ck.recvd p x, d⟩ = ⟨(SMHdrSt.join tr σ).ck.recvd p ⟨x, tr p⟩, d⟩ := by
  simp only [SMHdrSt.join, CKAGameSt.recvd, SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

/-- A send commutes with the join. -/
theorem SMHdrSt.join_upd (p : CKAParty) (x : SMPartySt Sc RK Sa) (h : SMHdrData Msg)
    (d : Bool) :
    SMHdrSt.join (Function.update tr p h) (σ.upd p x d) = (SMHdrSt.join tr σ).upd p ⟨x, h⟩ d := by
  simp only [SMHdrSt.join, SMSchemeSt.upd, SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

end Join

section Game

variable {Sc Msg Key Rand RK Sa W Ct AD : Type} [Fintype Rand] [Nonempty Rand]
  [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] {Kt : Type}
  [SampleableType Kt]

omit [SampleableType Kt] in
/-- **The oracle over the construction with headers at a joined state** is the oracle over the
ACD construction at the header data of the party of the query, with the corruption answer
completed by the header data and the header data of the party stepped by the answer. -/
theorem smSchemeOracle_acdHdrSM_join (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → (Msg × ℕ) × ℕ → AD) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (tr : CKAParty → SMHdrData Msg) (σ : SMSchemeSt (SMPartySt Sc RK Sa) Msg)
    (d : SMQuery W) :
    smSchemeOracle (acdHdrSM C R G D hdrAD) ΔFS ΔPCS t ideal (SMHdrSt.join tr σ) d =
      (smSchemeOracle (acdHdrBase C R G D hdrAD (tr d.party)) ΔFS ΔPCS t ideal σ d).map
        fun y => (y.1.map id id fun b => ⟨b, tr d.party⟩,
          SMHdrSt.join (Function.update tr d.party ((tr d.party).step y.1)) y.2) := by
  cases d with
  | ratchet p =>
    simp only [smSchemeOracle, SMQuery.party, CKAGameSt.canSend, SMHdrSt.join_ck_t,
      SMHdrSt.join_ck_st, SMHdrSt.join_done]
    split_ifs with hc <;> simp only [hc, Bool.false_eq_true, ↓reduceIte]
    · simp only [PMF.map_bind, PMF.pure_map, SMSchemeAns.map, SMHdrData.step,
        SMHdrSt.join_sent, acdHdrSM]
      rfl
    · simp only [PMF.pure_map, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self]
  | recv p =>
    simp only [smSchemeOracle, SMQuery.party, CKAGameSt.canRecv, SMHdrSt.join_ck_t,
      SMHdrSt.join_ck_st, SMHdrSt.join_done]
    split_ifs with hc <;> simp only [hc, Bool.false_eq_true, ↓reduceIte]
    · simp only [PMF.pure_map, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self,
        SMHdrSt.join_recvd, acdHdrSM]
      rfl
    · simp only [PMF.pure_map, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self]
  | send p m =>
    simp only [smSchemeOracle, SMQuery.party, SMHdrSt.join_ck_t, SMHdrSt.join_ck_st,
      SMHdrSt.join_done, acdHdrSM]
    split_ifs with hc <;> simp only [hc, Bool.false_eq_true, ↓reduceIte]
    · cases (acdHdrBase C R G D hdrAD (tr p)).send (σ.ck.st p) m with
      | none =>
        simp only [Option.map_none, PMF.pure_map, SMSchemeAns.map, SMHdrData.step,
          Function.update_eq_self]
      | some y =>
        simp only [Option.map_some, PMF.pure_map, SMSchemeAns.map, SMHdrData.step,
          SMHdrSt.join_upd, id_eq]
    · simp only [PMF.pure_map, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self]
  | chall p m =>
    simp only [smSchemeOracle, SMQuery.party, SMHdrSt.join_ck_t, SMHdrSt.join_ck_st,
      SMHdrSt.join_done, acdHdrSM]
    split_ifs with hc <;> simp only [hc, Bool.false_eq_true, ↓reduceIte]
    · cases (acdHdrBase C R G D hdrAD (tr p)).send (σ.ck.st p) m with
      | none =>
        simp only [Option.map_none, PMF.pure_map, SMSchemeAns.map, SMHdrData.step,
          Function.update_eq_self]
      | some y =>
        simp only [Option.map_some, PMF.map_bind, PMF.pure_map, SMSchemeAns.map,
          SMHdrData.step, SMHdrSt.join_upd]
        rfl
    · simp only [PMF.pure_map, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self]
  | corrupt p =>
    have he : ckaAllowCorr ΔFS ΔPCS t (SMHdrSt.join tr σ).ck p =
        ckaAllowCorr ΔFS ΔPCS t σ.ck p := rfl
    simp only [smSchemeOracle, SMQuery.party, he, SMHdrSt.join_ck_st, PMF.pure_map]
    by_cases hc : ckaAllowCorr ΔFS ΔPCS t σ.ck p = true
    · simp only [hc, ↓reduceIte, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self,
        acdHdrSM, acdHdrBase, acdSMAD, id]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, SMSchemeAns.map, SMHdrData.step,
        Function.update_eq_self]

omit [Fintype RK] [Nonempty RK] [SampleableType Kt] in
/-- The composite oracle of the wrapper against the oracle of `sm_corrupt_game` asks the query
with the associated data of the header of its party. -/
theorem simOracle_smHdrImpl (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → (Msg × ℕ) × ℕ → AD) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (tr : CKAParty → SMHdrData Msg) (s : SMSt Sc Msg RK Sa) (d : SMQuery W) :
    OracleAdv.simOracle (smHdrImpl hdrAD) (smOracleOf C R G D ΔFS ΔPCS t ideal (realRoot R))
        (tr, s) d =
      (smOracleOf C R G D ΔFS ΔPCS t ideal (realRoot R) s
          (d.mapAD fun ad => hdrAD ad (tr d.party).hdr)).map fun x =>
        (x.1.toScheme.map id id fun b => ⟨b, tr d.party⟩,
          Function.update tr d.party ((tr d.party).step x.1.toScheme), x.2) := by
  simp only [OracleAdv.simOracle, smHdrImpl, OracleAdv.run_query, OracleAdv.run_ret,
    PMF.map_bind, PMF.pure_map]
  rfl

omit [SampleableType Kt] in
/-- **The step of the reduction.** Under `ACDInv`, each call of the composite oracle of the
wrapper, with the state joined, is the call of the oracle over `acdHdrSM`. -/
theorem acdHdr_step (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt) (hdrAD : W → (Msg × ℕ) × ℕ → AD)
    (J : Sc → Sc → Prop) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (x : (CKAParty → SMHdrData Msg) × SMSt Sc Msg RK Sa) (hs : ACDInv C R J x.2)
    (d : SMQuery W) :
    (OracleAdv.simOracle (smHdrImpl hdrAD) (smOracleOf C R G D ΔFS ΔPCS t ideal (realRoot R))
        x d).map (fun y => (id y.1, SMHdrSt.join y.2.1 y.2.2.toScheme)) =
      smSchemeOracle (acdHdrSM C R G D hdrAD) ΔFS ΔPCS t ideal
        (SMHdrSt.join x.1 x.2.toScheme) d := by
  obtain ⟨tr, s⟩ := x
  rw [simOracle_smHdrImpl, smSchemeOracle_acdHdrSM_join, acdHdrBase,
    ← acdAD_step C R G D (fun ad => hdrAD ad (tr d.party).hdr) J ΔFS ΔPCS t ideal s hs d,
    PMF.map_comp, PMF.map_comp]
  rfl

omit [Fintype RK] [Nonempty RK] in
/-- The initial state of the wrapper joined with the initial state of `sm_corrupt_game` is the
initial state of the game over `acdHdrSM`. -/
theorem smHdr_join_init (i : Msg × Sc × Sc) (rk : RK) :
    SMHdrSt.join (fun _ => ⟨i.1, 0, 0⟩) (smInit (Sa := Sa) i rk).toScheme =
      SMSchemeSt.init (i.1, ⟨⟨i.2.1, rk, none, none⟩, ⟨i.1, 0, 0⟩⟩,
        ⟨⟨i.2.2, rk, none, none⟩, ⟨i.1, 0, 0⟩⟩) := by
  rw [SMSt.toScheme_smInit]
  simp only [SMHdrSt.join, SMSchemeSt.init, CKAGameSt.init, SMSchemeSt.mk.injEq,
    CKAGameSt.mk.injEq, and_true]
  funext q
  cases q <;> rfl

omit [SampleableType Kt] in
/-- **The corruption game over `acdHdrSM` is `sm_corrupt_game` at the wrapper.** For a CKA `C`
correct along `J`, with an initialisation that is the lift of `initP` and initial states related
by `J`, the corruption game over the ACD construction with headers against `A` is the game
`sm_corrupt_game C R G D` against `A.toHdr hdrAD`. -/
theorem smCorruptGame_acdHdr (C : CKADef Sc Msg Key) [CKACoins C Rand] {J : Sc → Sc → Prop}
    (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt) (hdrAD : W → (Msg × ℕ) × ℕ → AD)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : SMSchemeAdv Msg W Ct (SMHdrSt Sc RK Sa Msg)) :
    smCorruptGame (acdHdrSM C R G D hdrAD) ΔFS ΔPCS ideal A =
      sm_corrupt_game C R G D ΔFS ΔPCS ideal (A.toHdr hdrAD) := by
  rw [sm_corrupt_game, sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  simp only [smCorruptGame, acdHdrSM, hinit, sample_eq_liftPMF, SPComp.bind_assoc,
    SPComp.pure_bind, liftPMF_bind_liftPMF]
  refine congrArg _ (congrArg _ (funext fun t => ?_))
  refine PMF.bind_congr_support _ _ _ fun i hi => congrArg _ (funext fun rk => ?_)
  simp only [SMSchemeAdv.toHdr]
  rw [OracleAdv.run_simulate_fst, ← smHdr_join_init (Sa := Sa) i rk]
  have h := OracleAdv.run_map_fst_mapQueryAnswer_of_map_state_inv
    (OracleAdv.simOracle (smHdrImpl hdrAD) (smOracleOf C R G D ΔFS ΔPCS t ideal (realRoot R)))
    (smSchemeOracle (acdHdrSM C R G D hdrAD) ΔFS ΔPCS t ideal) id
    (fun x => SMHdrSt.join x.1 x.2.toScheme) (fun x => ACDInv C R J x.2)
    (fun x d hx y hy => by
      obtain ⟨tr, s⟩ := x
      rw [simOracle_smHdrImpl, PMF.support_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact acdInv_step C R G D hJ ΔFS ΔPCS t ideal s hx _ z hz)
    (fun x d hx => acdHdr_step C R G D hdrAD J ΔFS ΔPCS t ideal x hx d) (A.play t i.1)
    (fun _ => ⟨i.1, 0, 0⟩, smInit i rk) (acdInv_smInit C R i (hJi i hi) rk)
  rw [OracleAdv.mapQueryAnswer_id_id] at h
  exact h

omit [SampleableType Kt] in
/-- **The advantage of an adversary against `acdHdrSM`** is the advantage of the wrapper
adversary `A.toHdr hdrAD` in `sm_corrupt_game` with associated data in `AD`. -/
theorem acdHdrSM_corruptAdvantage_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc))
    (hinit : C.init = liftPMF initP) (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → (Msg × ℕ) × ℕ → AD) (ΔFS ΔPCS : ℕ)
    (A : SMSchemeAdv Msg W Ct (SMHdrSt Sc RK Sa Msg)) :
    (acdHdrSM C R G D hdrAD).corruptAdvantage ΔFS ΔPCS A =
      SM_Corrupt_Advantage C R G D ΔFS ΔPCS (A.toHdr hdrAD) := by
  simp only [SMScheme.corruptAdvantage, SM_Corrupt_Advantage,
    smCorruptGame_acdHdr C hJ initP hinit hJi]

end Game

section Prim

variable {Sc Msg Key Rand RK Sa W Ct AD : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key] [Fintype Sa]
  [Nonempty Sa] [DecidableEq RK] [DecidableEq Key] [DecidableEq AD] {Kt : Type} [SampleableType Kt]

/-- **The ACD construction with message headers from CKA, PRF-PRNG, PRG and AEAD security.**
For a CKA correct along `J` with a sound explicit-randomness sending algorithm, `2 ≤ ΔFS`,
`1 ≤ ΔPCS`, and an adversary `A` whose interactions ask at most `q` queries, the advantage
against `acdHdrSM C R G D hdrAD` is at most the CKA and PRF-PRNG advantages of `smcCKARed` and
`smcRootRed`, the PRG advantages of `fsCorrPRGRed G D b i` for `i < q` and both bits `b`, and
the AEAD advantage of `fsCorrAEADRed G D`, all at the wrapper adversary `A.toHdr hdrAD`. -/
theorem acdHdrSM_corruptAdvantage_le_prim (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt) (hdrAD : W → (Msg × ℕ) × ℕ → AD)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (A : SMSchemeAdv Msg W Ct (SMHdrSt Sc RK Sa Msg)) (q : ℕ)
    (hA : ∀ t T, (A.play t T).IsQueryBound q) :
    (acdHdrSM C R G D hdrAD).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G D b (A.toHdr hdrAD)) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP (A.toHdr hdrAD)) +
        (∑ i ∈ Finset.range q, PRG_Advantage G
            (fsCorrPRGRed G D false i (smcFSRed C R G D ΔFS ΔPCS initP (A.toHdr hdrAD))) +
          ∑ i ∈ Finset.range q, PRG_Advantage G
            (fsCorrPRGRed G D true i (smcFSRed C R G D ΔFS ΔPCS initP (A.toHdr hdrAD))) +
          AEAD_CCA_Advantage D
            (fsCorrAEADRed G D (smcFSRed C R G D ΔFS ΔPCS initP (A.toHdr hdrAD)))) := by
  rw [acdHdrSM_corruptAdvantage_eq C hJ initP hinit hJi]
  exact sm_corrupt_advantage_le_prim C hS initP hinit R G D hFS hPCS _ q
    (SMSchemeAdv.toHdr_play_isQueryBound hdrAD hA)

end Prim

end CatCrypt.Crypto.Messaging

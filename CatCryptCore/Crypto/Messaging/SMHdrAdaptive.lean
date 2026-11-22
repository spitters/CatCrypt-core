/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMHdr
public import CatCryptCore.Crypto.OracleQueryVecRun
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction

/-!
# The adaptive game over the construction with a header in the associated data

The construction `acdHdrSM` puts the header of a message into the associated data of the AEAD.
The game with an adaptive challenge epoch over `acdHdrSM` is `sm_adaptive_game` at the wrapper
adversary `smHdrAdaptive hdrAD A` (`smAdaptiveGame_acdHdr`): the wrapper keeps the header data of
both parties and answers each query of `A` by the query with the associated data of the header of
its party (`acdHdr_ad_step`, over the oracle step `acdAD_ad_step`). The advantage of `A` against
`acdHdrSM` is the advantage of the wrapper (`acdHdrSM_adaptiveAdvantage_eq`), and the wrapper
keeps the query bound of `A` (`smHdrAdaptive_isQueryBound`). A scheme that simulates the
Diffie-Hellman instance with the header in the associated data has the adaptive challenge bound
with DDH, PRF-PRNG and FS-AEAD terms at the wrapper under a query bound `q`, delays
`2 ≤ ΔFS`, `2 ≤ ΔPCS`, and a sampler certificate `c`, plus `(q + 1) * 8 * c.δ`
(`SMScheme.Sim.adaptiveAdvantage_le_acdHdr_dhCKAOf_of_isQueryBound`).

A passive adversary asks no corruption query, so its games read no delay: the section Passive
shows the corruption game and the adaptive game against a passive adversary independent of the
delays (`smCorruptGame_passive`, `smAdaptiveGame_passive`). The adaptive game over a scheme with
a lifted initialisation is a lifted distribution on one bit (`smAdaptiveGame_eq_liftPMF`).

## Main results

* `smHdrAdaptive`, `smAdaptiveGame_acdHdr`, `acdHdrSM_adaptiveAdvantage_eq` — the wrapper and
  the reduction of the adaptive game
* `smHdrAdaptive_isQueryBound` — the wrapper keeps the query bound
* `SMScheme.Sim.adaptiveAdvantage_le_acdHdr_dhCKAOf_of_isQueryBound` — the bound from DDH
* `smNoCorrupt`, `smCorruptGame_passive`, `smAdaptiveGame_passive` — passive adversaries
* `smAdaptiveGame_eq_liftPMF` — the adaptive game as a lifted distribution
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions

section AdaptiveHdr

variable {Sc Msg Key Rand RK Sa W Ct AD : Type} [Fintype Rand] [Nonempty Rand]
  [SampleableType W] [SampleableType Ct] {Kt : Type} [SampleableType Kt]

omit [SampleableType Kt] in
/-- **The step of the adaptive game over `acdSMAD` with associated data `f ad`.** Under
`ACDInv`, each call of `smAdOracle` on the query with the associated data mapped by `f`, with
its answer and state carried to the game over the scheme, is the call of
`smSchemeAdOracle (acdSMAD C R G D fun _ => f)`. -/
theorem acdAD_ad_step [Fintype RK] [Nonempty RK] (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (f : W → AD) (J : Sc → Sc → Prop) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (x : SMSt Sc Msg RK Sa × SMAdRec) (hx : ACDInv C R J x.1) (q : SMQuery W) :
    (smAdOracle C R G D ΔFS ΔPCS ideal x (q.mapAD f)).map
        (fun y => (SMAns.toScheme y.1, (y.2.1.toScheme, y.2.2))) =
      smSchemeAdOracle (acdSMAD C R G D fun _ => f) ΔFS ΔPCS ideal (x.1.toScheme, x.2) q := by
  have hmap : ∀ q' : SMQuery W,
      ((smOracleOf C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1 (q'.mapAD f)).map
          fun y => (y.1, (y.2, x.2))).map
        (fun y => (SMAns.toScheme y.1, (y.2.1.toScheme, y.2.2))) =
      (smSchemeOracle (acdSMAD C R G D fun _ => f) ΔFS ΔPCS 0 ideal x.1.toScheme q').map
        fun y => (y.1, (y.2, x.2)) := fun q' => by
    rw [PMF.map_comp, ← acdAD_step C R G D f J ΔFS ΔPCS 0 ideal x.1 hx q', PMF.map_comp]
    rfl
  cases q with
  | ratchet p => exact hmap (.ratchet p)
  | recv p => exact hmap (.recv p)
  | send p m => exact hmap (.send p m)
  | chall p m =>
    simp only [SMQuery.mapAD, smAdOracle, smSchemeAdOracle, SMSt.toScheme_ck_t,
      SMSt.toScheme_ck_st, acdSMAD, SMSt.toScheme_done]
    cases hsnd : x.1.loc.snd p with
    | none =>
      simp only [Option.map_none, PMF.pure_map]
      by_cases hc : x.2.cE = none ∧ x.1.loc.done = false ∧ x.2.lo ≤ x.1.ck.t p ∧
          ckaSender (x.1.ck.t p) = p <;>
        simp only [hc, and_self, ite_true, ite_false] <;> rfl
    | some sa =>
      simp only [Option.map_some]
      by_cases hc : x.2.cE = none ∧ x.1.loc.done = false ∧ x.2.lo ≤ x.1.ck.t p ∧
          ckaSender (x.1.ck.t p) = p
      · simp only [hc, and_self, ite_true, PMF.map_bind, PMF.pure_map, SMAns.toScheme, challCt,
          SMSt.toScheme_advanced_done]
      · simp only [hc, ite_false, PMF.pure_map]
        rfl
  | corrupt p =>
    simp only [SMQuery.mapAD, smAdOracle, smSchemeAdOracle, SMSt.toScheme_ck_t,
      SMSt.toScheme_ck_st, acdSMAD]
    cases x.2.cE with
    | none => simp only [PMF.pure_map, SMAns.toScheme]; rfl
    | some e =>
      simp only [PMF.pure_map]
      by_cases hc : e + ΔFS ≤ x.1.ck.t p <;> simp only [hc, ite_true, ite_false] <;> rfl

omit [SampleableType Kt] in
/-- **The invariant `ACDInv` is kept by the adaptive oracle** with associated data in `AD`. -/
theorem acdInvAD_ad_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (x : SMSt Sc Msg RK Sa × SMAdRec) (hx : ACDInv C R J x.1) (q : SMQuery W AD) :
    ∀ y ∈ (smAdOracle C R G D ΔFS ΔPCS ideal x q).support, ACDInv C R J y.2.1 := by
  have hmap : ∀ q' : SMQuery W AD, ∀ y ∈ ((smOracleOf C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1
      q').map fun y => (y.1, (y.2, x.2))).support, ACDInv C R J y.2.1 := by
    intro q' y hy
    rw [PMF.support_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact acdInv_step C R G D hJ ΔFS ΔPCS 0 ideal x.1 hx q' z hz
  intro y hy
  cases q with
  | ratchet _ | recv _ | send _ _ => exact hmap _ y hy
  | chall p m =>
    simp only [smAdOracle] at hy
    split at hy
    · split at hy
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hy
        obtain ⟨c, -, rfl⟩ := hy
        exact hx.of_eq rfl rfl rfl
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        rw [hy]; exact hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      rw [hy]; exact hx
  | corrupt p =>
    simp only [smAdOracle] at hy
    split at hy <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hy <;> rw [hy] <;>
      exact hx

omit [SampleableType W] [SampleableType Ct] in
/-- The composite oracle of the wrapper against an oracle `O` asks the query with the
associated data of the header of its party. -/
theorem simOracle_smHdrImpl_of {S : Type} (hdrAD : W → (Msg × ℕ) × ℕ → AD)
    (O : S → SMQuery W AD → PMF (SMAns Sc Msg RK Sa Ct × S)) (tr : CKAParty → SMHdrData Msg)
    (s : S) (d : SMQuery W) :
    OracleAdv.simOracle (smHdrImpl hdrAD) O (tr, s) d =
      (O s (d.mapAD fun ad => hdrAD ad (tr d.party).hdr)).map fun x =>
        (x.1.toScheme.map id id fun b => ⟨b, tr d.party⟩,
          Function.update tr d.party ((tr d.party).step x.1.toScheme), x.2) := by
  simp only [OracleAdv.simOracle, smHdrImpl, OracleAdv.run_query, OracleAdv.run_ret,
    PMF.map_bind, PMF.pure_map]
  rfl

omit [SampleableType Kt] in
/-- **The adaptive oracle over the construction with headers at a joined state** is the
adaptive oracle over the ACD construction at the header data of the party of the query, with
the corruption answer completed by the header data and the header data of the party stepped by
the answer. -/
theorem smSchemeAdOracle_acdHdrSM_join [Fintype RK] [Nonempty RK] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct AD Kt) (hdrAD : W → (Msg × ℕ) × ℕ → AD) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (tr : CKAParty → SMHdrData Msg) (σ : SMSchemeSt (SMPartySt Sc RK Sa) Msg) (ad : SMAdRec)
    (d : SMQuery W) :
    smSchemeAdOracle (acdHdrSM C R G D hdrAD) ΔFS ΔPCS ideal (SMHdrSt.join tr σ, ad) d =
      (smSchemeAdOracle (acdHdrBase C R G D hdrAD (tr d.party)) ΔFS ΔPCS ideal (σ, ad) d).map
        fun y => (y.1.map id id fun b => ⟨b, tr d.party⟩,
          (SMHdrSt.join (Function.update tr d.party ((tr d.party).step y.1)) y.2.1, y.2.2)) := by
  cases d with
  | ratchet _ | recv _ | send _ _ =>
    simp only [smSchemeAdOracle]
    rw [smSchemeOracle_acdHdrSM_join, PMF.map_comp, PMF.map_comp]
    rfl
  | chall p m =>
    simp only [smSchemeAdOracle, SMQuery.party, SMHdrSt.join_ck_t, SMHdrSt.join_ck_st,
      SMHdrSt.join_done, acdHdrSM]
    by_cases hc : ad.cE = none ∧ σ.done = false ∧ ad.lo ≤ σ.ck.t p ∧ ckaSender (σ.ck.t p) = p
    · simp only [hc, and_self, ↓reduceIte]
      cases (acdHdrBase C R G D hdrAD (tr p)).send (σ.ck.st p) m with
      | none =>
        simp only [Option.map_none, PMF.pure_map, SMSchemeAns.map, SMHdrData.step,
          Function.update_eq_self]
      | some y =>
        simp only [Option.map_some, PMF.map_bind, PMF.pure_map, SMSchemeAns.map,
          SMHdrData.step, SMHdrSt.join_upd, acdHdrBase, acdSMAD, id]
    · simp only [hc, ↓reduceIte, PMF.pure_map, SMSchemeAns.map, SMHdrData.step,
        Function.update_eq_self]
  | corrupt p =>
    simp only [smSchemeAdOracle, SMQuery.party, SMHdrSt.join_ck_st, SMHdrSt.join_ck_t]
    cases ad.cE with
    | none =>
      simp only [PMF.pure_map, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self,
        acdHdrSM, acdHdrBase, acdSMAD, id]
    | some e =>
      simp only [PMF.pure_map]
      by_cases hc : e + ΔFS ≤ σ.ck.t p
      · simp only [hc, ↓reduceIte, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self,
          acdHdrSM, acdHdrBase, acdSMAD, id]
      · simp only [hc, ↓reduceIte, SMSchemeAns.map, SMHdrData.step, Function.update_eq_self]

omit [SampleableType Kt] in
/-- **The step of the reduction of the adaptive game.** Under `ACDInv`, each call of the
composite oracle of the wrapper against `smAdOracle`, with the state joined, is the call of the
adaptive oracle over `acdHdrSM`. -/
theorem acdHdr_ad_step [Fintype RK] [Nonempty RK] (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → (Msg × ℕ) × ℕ → AD) (J : Sc → Sc → Prop) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (x : (CKAParty → SMHdrData Msg) × (SMSt Sc Msg RK Sa × SMAdRec)) (hs : ACDInv C R J x.2.1)
    (d : SMQuery W) :
    (OracleAdv.simOracle (smHdrImpl hdrAD) (smAdOracle C R G D ΔFS ΔPCS ideal) x d).map
        (fun y => (id y.1, (SMHdrSt.join y.2.1 y.2.2.1.toScheme, y.2.2.2))) =
      smSchemeAdOracle (acdHdrSM C R G D hdrAD) ΔFS ΔPCS ideal
        (SMHdrSt.join x.1 x.2.1.toScheme, x.2.2) d := by
  obtain ⟨tr, s, ad⟩ := x
  rw [simOracle_smHdrImpl_of, smSchemeAdOracle_acdHdrSM_join, acdHdrBase,
    ← acdAD_ad_step C R G D (fun ad => hdrAD ad (tr d.party).hdr) J ΔFS ΔPCS ideal (s, ad) hs d,
    PMF.map_comp, PMF.map_comp]
  rfl

/-- **The wrapper adversary of the adaptive game.** An adversary of the game over
`acdHdrSM C R G D hdrAD` with an adaptive challenge epoch as an adversary of
`sm_adaptive_game` with associated data in `AD`: from the public value `T` of the
initialisation it keeps the header data of both parties, starting at `T`, and answers each
query of `A T` by `smHdrImpl hdrAD`. -/
def smHdrAdaptive (hdrAD : W → (Msg × ℕ) × ℕ → AD)
    (A : Msg → OracleAdv (SMQuery W) (SMSchemeAns Msg Ct (SMHdrSt Sc RK Sa Msg)) Bool) (T : Msg) :
    OracleAdv (SMQuery W AD) (SMAns Sc Msg RK Sa Ct) Bool :=
  (OracleAdv.simulate (smHdrImpl hdrAD) (A T) fun _ => ⟨T, 0, 0⟩).bind fun x => .ret x.1

time_cert_try derive_reduction smHdrAdaptive

omit [SampleableType Kt] in
/-- **The adaptive game over `acdHdrSM` is `sm_adaptive_game` at the wrapper.** For a CKA `C`
correct along `J`, with an initialisation that is the lift of `initP` and initial states related
by `J`, the game with an adaptive challenge epoch over the ACD construction with headers against
`A` is `sm_adaptive_game C R G D` against `smHdrAdaptive hdrAD A`. -/
theorem smAdaptiveGame_acdHdr [Fintype RK] [Nonempty RK] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc))
    (hinit : C.init = liftPMF initP) (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → (Msg × ℕ) × ℕ → AD) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : Msg → OracleAdv (SMQuery W) (SMSchemeAns Msg Ct (SMHdrSt Sc RK Sa Msg)) Bool) :
    smAdaptiveGame (acdHdrSM C R G D hdrAD) ΔFS ΔPCS ideal A =
      sm_adaptive_game C R G D ΔFS ΔPCS ideal (smHdrAdaptive hdrAD A) := by
  simp only [smAdaptiveGame, sm_adaptive_game, acdHdrSM, hinit, sample_eq_liftPMF,
    SPComp.bind_assoc, SPComp.pure_bind, liftPMF_bind_liftPMF]
  refine congrArg _ (PMF.bind_congr_support _ _ _ fun i hi => congrArg _ (funext fun rk => ?_))
  simp only [smHdrAdaptive]
  rw [OracleAdv.run_simulate_fst]
  have he : (SMSchemeSt.init (i.1, (⟨⟨i.2.1, rk, none, none⟩, ⟨i.1, 0, 0⟩⟩ :
      SMHdrSt Sc RK Sa Msg), (⟨⟨i.2.2, rk, none, none⟩, ⟨i.1, 0, 0⟩⟩ : SMHdrSt Sc RK Sa Msg)),
      (⟨none, 0⟩ : SMAdRec)) =
      (fun x : (CKAParty → SMHdrData Msg) × (SMSt Sc Msg RK Sa × SMAdRec) =>
        (SMHdrSt.join x.1 x.2.1.toScheme, x.2.2))
        (fun _ => ⟨i.1, 0, 0⟩, smInit i rk, ⟨none, 0⟩) := by
    simp only [smHdr_join_init]
  rw [he]
  have h := OracleAdv.run_map_fst_mapQueryAnswer_of_map_state_inv
    (OracleAdv.simOracle (smHdrImpl hdrAD) (smAdOracle C R G D ΔFS ΔPCS ideal))
    (smSchemeAdOracle (acdHdrSM C R G D hdrAD) ΔFS ΔPCS ideal) id
    (fun x : (CKAParty → SMHdrData Msg) × (SMSt Sc Msg RK Sa × SMAdRec) =>
      (SMHdrSt.join x.1 x.2.1.toScheme, x.2.2)) (fun x => ACDInv C R J x.2.1)
    (fun x d hx y hy => by
      obtain ⟨tr, s⟩ := x
      rw [simOracle_smHdrImpl_of, PMF.support_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact acdInvAD_ad_step C R G D hJ ΔFS ΔPCS ideal s hx _ z hz)
    (fun x d hx => acdHdr_ad_step C R G D hdrAD J ΔFS ΔPCS ideal x hx d) (A i.1)
    (fun _ => ⟨i.1, 0, 0⟩, smInit i rk, ⟨none, 0⟩) (acdInv_smInit C R i (hJi i hi) rk)
  rw [OracleAdv.mapQueryAnswer_id_id] at h
  exact h

omit [SampleableType Kt] in
/-- **The advantage of an adversary against `acdHdrSM` with an adaptive challenge epoch** is
the advantage of the wrapper adversary `smHdrAdaptive hdrAD A` in `sm_adaptive_game` with
associated data in `AD`. -/
theorem acdHdrSM_adaptiveAdvantage_eq [Fintype RK] [Nonempty RK] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc))
    (hinit : C.init = liftPMF initP) (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → (Msg × ℕ) × ℕ → AD) (ΔFS ΔPCS : ℕ)
    (A : Msg → OracleAdv (SMQuery W) (SMSchemeAns Msg Ct (SMHdrSt Sc RK Sa Msg)) Bool) :
    (acdHdrSM C R G D hdrAD).adaptiveAdvantage ΔFS ΔPCS A =
      SM_Adaptive_Advantage C R G D ΔFS ΔPCS (smHdrAdaptive hdrAD A) := by
  simp only [SMScheme.adaptiveAdvantage, SM_Adaptive_Advantage,
    smAdaptiveGame_acdHdr C hJ initP hinit hJi]

omit [SampleableType W] [SampleableType Ct] in
/-- The wrapper adversary `smHdrAdaptive hdrAD A` keeps the query bound of `A`: its handler
asks one query for each query of `A`. -/
theorem smHdrAdaptive_isQueryBound (hdrAD : W → (Msg × ℕ) × ℕ → AD)
    {A : Msg → OracleAdv (SMQuery W) (SMSchemeAns Msg Ct (SMHdrSt Sc RK Sa Msg)) Bool} {q : ℕ}
    (hA : ∀ T, (A T).IsQueryBound q) (T : Msg) :
    (smHdrAdaptive hdrAD A T).IsQueryBound q := by
  have himpl : ∀ tr d, (smHdrImpl (Sc := Sc) (RK := RK) (Sa := Sa) (Ct := Ct) hdrAD tr
      d).IsQueryBound 1 := fun _ _ _ => trivial
  simp only [smHdrAdaptive]
  simpa using OracleAdv.isQueryBound_bind (n := 0) (f := fun x => OracleAdv.ret x.1)
    (OracleAdv.isQueryBound_simulate _ (fun _ => 1) himpl (hA T).isQueryBoundBy_one _)
    (fun _ => trivial)

end AdaptiveHdr

section AdaptiveHdrDH

open CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

variable (G : Type) [CG : CyclicGroup G] [DecidableEq G]
  {Sk RK Sa W Ct AD St' Pub' Ct' Leak' : Type}
  [Fintype Sk] [Nonempty Sk] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [DecidableEq RK] [Fintype Sa] [Nonempty Sa] {Kt : Type} [SampleableType Kt]

/-- **A scheme that simulates the Diffie–Hellman ACD construction with headers, with an adaptive
challenge epoch and a query bound, from DDH.** If `M'` simulates
`acdHdrSM (dhCKAOf G decE) R F D hdrAD`, the delays satisfy `2 ≤ ΔFS`, `2 ≤ ΔPCS`, and `c` is a
sampler certificate from the image `c.μ` of the uniform sampler on `Sk` under `decE` to the
uniform exponent sampler `c.ν`, the advantage of every adversary `A` asking at most `q` queries
in the game over `M'` with an adaptive challenge epoch is at most the sum over the epochs
`e ≤ q` of the DDH advantages of `ckaCorruptDDHRedOf`, the PRF-PRNG terms and the FS-AEAD term at
the guessing reduction of the wrapper adversary `smHdrAdaptive hdrAD` of `A` with its answers
encoded, plus `(q + 1) * 8 * c.δ`. -/
theorem SMScheme.Sim.adaptiveAdvantage_le_acdHdr_dhCKAOf_of_isQueryBound (decE : Sk → CG.Exp)
    (c : SamplerCert CG.Exp) (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) (R : PRGDef (RK × G) (RK × Sa))
    (F : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt) (hdrAD : W → (G × ℕ) × ℕ → AD)
    {M' : SMScheme St' Pub' Sk W Ct' Leak'} {ρ : St' → SMHdrSt (G × Sk) RK Sa G → Prop}
    {encP : G → Pub'} {encC : Ct → Ct'} {encL : SMHdrSt (G × Sk) RK Sa G → Leak'}
    {encI : SMHdrSt (G × Sk) RK Sa G → St'}
    (h : M'.Sim (acdHdrSM (dhCKAOf G decE) R F D hdrAD) ρ encP encC encL encI) {ΔFS ΔPCS : ℕ}
    (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) {q : ℕ}
    (A : Pub' → OracleAdv (SMQuery W) (SMSchemeAns Pub' Ct' Leak') Bool)
    (hA : ∀ T, (A T).IsQueryBound q) :
    M'.adaptiveAdvantage ΔFS ΔPCS A ≤
      ∑ e ∈ Finset.range (q + 1), (∑ b : Bool, DDH_Advantage G
            (ckaCorruptDDHRedOf (G := G) decE ΔFS ΔPCS (smcCKARed R F D b (smGuessAdv ΔFS ΔPCS
              (smHdrAdaptive hdrAD fun T => (A (encP T)).mapQueryAnswer id
                (SMSchemeAns.map encP encC encL)) e))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
          (dhInitPOf G decE) (smGuessAdv ΔFS ΔPCS
            (smHdrAdaptive hdrAD fun T => (A (encP T)).mapQueryAnswer id
              (SMSchemeAns.map encP encC encL)) e)) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
          (dhInitPOf G decE) (smGuessAdv ΔFS ΔPCS
            (smHdrAdaptive hdrAD fun T => (A (encP T)).mapQueryAnswer id
              (SMSchemeAns.map encP encC encL)) e))) +
        (q + 1) * 8 * c.δ := by
  rw [h.adaptiveAdvantage_eq, acdHdrSM_adaptiveAdvantage_eq (dhCKAOf G decE)
    (dhCKAOf_correct G decE) (dhInitPOf G decE) (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)]
  refine (sm_adaptive_corrupt_advantage_le_of_isQueryBound (dhCKAOf G decE)
    (dhCKAOfCoins_sound G decE) (dhInitPOf G decE) (dhCKAOf_init_eq G decE) R F D hFS
    (le_trans (by norm_num) hPCS) _ (smHdrAdaptive_isQueryBound hdrAD
      fun T => OracleAdv.isQueryBound_mapQueryAnswer _ _ (hA (encP T)))).trans ?_
  have hc : ((q : ℝ≥0∞) + 1) * 8 * c.δ =
      ∑ e ∈ Finset.range (q + 1), ∑ b : Bool, 4 * c.δ := by
    simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hc, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have key : ∀ a b x y d : ℝ≥0∞, a ≤ b + d → a + x + y ≤ b + x + y + d := by
    intro a b x y d h
    calc a + x + y ≤ b + d + x + y := by gcongr
      _ = b + x + y + d := by ring
  refine key _ _ _ _ _ ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => dhCKAOf_corrupt_advantage_le decE c hμ hν hFS hPCS _

end AdaptiveHdrDH

open scoped ENNReal

/-- The queries of the secure-messaging games other than the corruptions. An adversary whose
tree asks only these queries is passive. -/
def smNoCorrupt {W AD : Type} : Set (SMQuery W AD) := {d | ∀ p, d ≠ .corrupt p}

section Passive

variable {St Pub Rand W Ct Leak : Type} [Fintype Rand] [Nonempty Rand]

/-- Away from the corruptions the oracle of the corruption game does not read the delays. -/
theorem smSchemeOracle_noCorrupt (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS ΔFS' ΔPCS' t : ℕ) (ideal : Bool) (s : SMSchemeSt St Pub) (d : SMQuery W)
    (hd : d ∈ smNoCorrupt) :
    smSchemeOracle M ΔFS ΔPCS t ideal s d = smSchemeOracle M ΔFS' ΔPCS' t ideal s d := by
  cases d with
  | corrupt p => exact (hd p rfl).elim
  | _ => rfl

/-- Away from the corruptions the oracle of the adaptive game does not read the delays. -/
theorem smSchemeAdOracle_noCorrupt (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS ΔFS' ΔPCS' : ℕ) (ideal : Bool) (x : SMSchemeSt St Pub × SMAdRec)
    (d : SMQuery W) (hd : d ∈ smNoCorrupt) :
    smSchemeAdOracle M ΔFS ΔPCS ideal x d = smSchemeAdOracle M ΔFS' ΔPCS' ideal x d := by
  cases d with
  | corrupt p => exact (hd p rfl).elim
  | _ => rfl

/-- **The corruption game against a passive adversary does not depend on the delays.** -/
theorem smCorruptGame_passive (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS ΔFS' ΔPCS' : ℕ)
    (ideal : Bool) (A : SMSchemeAdv Pub W Ct Leak)
    (hA : ∀ t T, (A.play t T).MayOnlyCall smNoCorrupt) :
    smCorruptGame M ΔFS ΔPCS ideal A = smCorruptGame M ΔFS' ΔPCS' ideal A := by
  simp only [smCorruptGame]
  congr 1
  funext t
  congr 1
  funext i
  rw [OracleAdv.run_eq_of_mayOnlyCall _ (smSchemeOracle M ΔFS' ΔPCS' t ideal)
    (fun s d hd => smSchemeOracle_noCorrupt M ΔFS ΔPCS ΔFS' ΔPCS' t ideal s d hd) (hA t i.1)]

/-- **The corruption advantage of a passive adversary does not depend on the delays.** -/
theorem SMScheme.corruptAdvantage_passive (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS ΔFS' ΔPCS' : ℕ) (A : SMSchemeAdv Pub W Ct Leak)
    (hA : ∀ t T, (A.play t T).MayOnlyCall smNoCorrupt) :
    M.corruptAdvantage ΔFS ΔPCS A = M.corruptAdvantage ΔFS' ΔPCS' A := by
  rw [SMScheme.corruptAdvantage, SMScheme.corruptAdvantage,
    smCorruptGame_passive M ΔFS ΔPCS ΔFS' ΔPCS' false A hA,
    smCorruptGame_passive M ΔFS ΔPCS ΔFS' ΔPCS' true A hA]

/-- **The adaptive game against a passive adversary does not depend on the delays.** -/
theorem smAdaptiveGame_passive (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS ΔFS' ΔPCS' : ℕ)
    (ideal : Bool) (A : Pub → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool)
    (hA : ∀ T, (A T).MayOnlyCall smNoCorrupt) :
    smAdaptiveGame M ΔFS ΔPCS ideal A = smAdaptiveGame M ΔFS' ΔPCS' ideal A := by
  simp only [smAdaptiveGame]
  congr 1
  funext i
  rw [OracleAdv.run_eq_of_mayOnlyCall _ (smSchemeAdOracle M ΔFS' ΔPCS' ideal)
    (fun x d hd => smSchemeAdOracle_noCorrupt M ΔFS ΔPCS ΔFS' ΔPCS' ideal x d hd) (hA i.1)]

/-- **The adaptive advantage of a passive adversary does not depend on the delays.** -/
theorem SMScheme.adaptiveAdvantage_passive (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS ΔFS' ΔPCS' : ℕ)
    (A : Pub → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool)
    (hA : ∀ T, (A T).MayOnlyCall smNoCorrupt) :
    M.adaptiveAdvantage ΔFS ΔPCS A = M.adaptiveAdvantage ΔFS' ΔPCS' A := by
  rw [SMScheme.adaptiveAdvantage, SMScheme.adaptiveAdvantage,
    smAdaptiveGame_passive M ΔFS ΔPCS ΔFS' ΔPCS' false A hA,
    smAdaptiveGame_passive M ΔFS ΔPCS ΔFS' ΔPCS' true A hA]

end Passive

/-- The adaptive game over a scheme whose initialisation is a lifted distribution is a lifted
distribution on `Bool`. -/
theorem smAdaptiveGame_eq_liftPMF {St Pub Rand W Ct Leak : Type} [Fintype Rand]
    [Nonempty Rand] (M : SMScheme St Pub Rand W Ct Leak) {ι : PMF (Pub × St × St)}
    (hM : M.init = liftPMF ι)
    (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : Pub → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool) :
    smAdaptiveGame M ΔFS ΔPCS ideal A = liftPMF (ι.bind fun i =>
      (OracleAdv.run (smSchemeAdOracle M ΔFS ΔPCS ideal) (A i.1)
        (SMSchemeSt.init i, ⟨none, 0⟩)).map Prod.fst) := by
  rw [smAdaptiveGame, hM, liftPMF_bind_liftPMF]

end CatCrypt.Crypto.Messaging

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLWE_PKE_Scheme
public import CatCryptCore.Crypto.MLKEM.MLWE_PKE_Stateful

/-!
# IND-CCA security of FO⊥̸ over the MLWE PKE from module-LWE

The Fujisaki–Okamoto KEM `foNotBot (toScheme P)` over the base MLWE public-key
encryption scheme is IND-CCA secure in the classical random-oracle model, with a
bound in the module-LWE and extended module-LWE advantages of named reductions.
The composition has two parts: the IND-CPA adversary of `PKE.Games` is a two-stage
adversary of `MLWE_PKE_Stateful` lifted to sub-distributions, so
`indcpaAdvantage (toScheme P) A` is `CPA_Adv_st` and `main_theorem_st` bounds it by
four MLWE terms; and `KEM.FOTransform.foNotBot_indcca_of_indcpa` bounds the IND-CCA
advantage of `foNotBot (toScheme P)` by the IND-CPA advantages of the two adversaries
`owToIndcpa (tReductionC …)` and `owToIndcpa (tReductionD …)`, each of which is
replaced by its four MLWE terms.

## Main definitions

* `choose_st A`, `guess_st A` — the two stages of an `INDCPAAdversary` as
  sub-distributions
* `advC P B`, `advD P B qRO` — the IND-CPA adversaries against `toScheme P` built from
  an IND-CCA adversary `B` against `foNotBot (toScheme P)`
* `redC1`, `redC2`, `redD1`, `redD2` — the MLWE and extended MLWE reductions of
  `MLWE_PKE_Stateful` at these adversaries

## Main results

* `indcpaGame_eq_CPA_Game_st` — the IND-CPA game of `toScheme P` is `CPA_Game_st`
* `indcpaAdvantage_eq_CPA_Adv_st` — the IND-CPA advantage of `toScheme P` is
  `CPA_Adv_st`
* `indcpaAdvantage_le_mlwe` — the IND-CPA advantage of `toScheme P` is bounded by two
  MLWE and two extended MLWE advantages
* `foNotBot_indcca_mlwe` — the IND-CCA advantage of `foNotBot (toScheme P)` is bounded
  by eight MLWE terms of named reductions, the correctness error and the message-space
  terms of the Fujisaki–Okamoto bound

## The model

* The KEM of `foNotBot_indcca_mlwe` is `foNotBot (toScheme P)`, `U⊥̸[T[P, G], H]` with
  key `H(m, c)` and implicit rejection `H(s, c)`.
* The random oracles `G` and `H` are classical, and the MLWE adversaries are classical.
* The fields `sampleShort_eq` and `sampleKey_eq` of `MLWE_PKE_Scheme.Params` model
  `SamplePolyCBD` over a uniform seed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.FOFromMLWE

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.PKE.Games
open CatCrypt.Crypto.KEM.Games (ROM2INDCCAAdversary rom2INDCCAAdvantage)
open CatCrypt.Crypto.KEM.FOTransform (foNotBot uRedROM foNotBot_indcca_of_indcpa)
open CatCrypt.Crypto.PKE.FOTransformT (tReductionC tReductionD)
open MLWE_PKE_Basic (PK CT MLWE_Ext_advantage)
open MLWE_PKE_Scheme (toScheme)
open MLWE_PKE_Stateful
open scoped ENNReal

variable (P : MLWE_PKE_Scheme.Params)

/-! ## The IND-CPA adversary as a two-stage adversary -/

/-- The first stage of `A` as a sub-distribution. -/
noncomputable def choose_st (A : INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic))
    (pk : PK P.toBasic) : SDistr (P.PT × P.PT × A.St) :=
  (A.choose pk).map some

/-- The second stage of `A` as a sub-distribution. -/
noncomputable def guess_st (A : INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic))
    (st : A.St) (c : CT P.toBasic) : SDistr Bool :=
  (A.guess st c).map some

/-- The IND-CPA game of `toScheme P` against `A` is the two-stage game of
`MLWE_PKE_Stateful` against `choose_st A`, `guess_st A`. -/
theorem indcpaGame_eq_CPA_Game_st
    (A : INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic)) (b : Bool) :
    (indcpaGame (toScheme P) A b).map some =
      CPA_Game_st P.toBasic (choose_st P A) (guess_st P A) b := by
  rw [MLWE_PKE_Scheme.indcpaGame_eq]
  rfl

/-- The IND-CPA advantage of `toScheme P` against `A` is the two-stage advantage of
`MLWE_PKE_Stateful` against `choose_st A`, `guess_st A`. -/
theorem indcpaAdvantage_eq_CPA_Adv_st
    (A : INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic)) :
    indcpaAdvantage (toScheme P) A = CPA_Adv_st P.toBasic (choose_st P A) (guess_st P A) := by
  rw [MLWE_PKE_Scheme.indcpaAdvantage_eq_absDiff_prTrue, CPA_Adv_st,
    indcpaGame_eq_CPA_Game_st, indcpaGame_eq_CPA_Game_st]

/-- The IND-CPA advantage of `toScheme P` against `A` is bounded by two MLWE
advantages of `B1_st` and two extended MLWE advantages of `B2_ext_st`. -/
theorem indcpaAdvantage_le_mlwe
    (A : INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic)) :
    indcpaAdvantage (toScheme P) A ≤
      MLWE.advantage P.toBasic.toParams (B1_st P.toBasic (choose_st P A) (guess_st P A) true) +
      MLWE_Ext_advantage P.toBasic (B2_ext_st P.toBasic (choose_st P A) (guess_st P A) true) +
      MLWE_Ext_advantage P.toBasic (B2_ext_st P.toBasic (choose_st P A) (guess_st P A) false) +
      MLWE.advantage P.toBasic.toParams (B1_st P.toBasic (choose_st P A) (guess_st P A) false) := by
  rw [indcpaAdvantage_eq_CPA_Adv_st]
  exact main_theorem_st P.toBasic (choose_st P A) (guess_st P A)

/-! ## The reductions -/

variable {K : Type} [Fintype K] [Nonempty K] {qRO qD : ℕ}

/-- The IND-CPA adversary against `toScheme P` built from an IND-CCA adversary `B`
against `foNotBot (toScheme P)`: `owToIndcpa` of the OW-CPA adversary `tReductionC`. -/
noncomputable def advC
    (B : ROM2INDCCAAdversary (PK P.toBasic) K (CT P.toBasic) P.PT P.Seed (P.PT × CT P.toBasic)
      K qRO qD) :
    INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic) :=
  owToIndcpa (tReductionC (toScheme P) (uRedROM B))

/-- The IND-CPA adversary against `toScheme P` built from an IND-CCA adversary `B`
against `foNotBot (toScheme P)`: `owToIndcpa` of the OW-CPA adversary
`tReductionD` with log bound `qRO`. -/
noncomputable def advD
    (B : ROM2INDCCAAdversary (PK P.toBasic) K (CT P.toBasic) P.PT P.Seed (P.PT × CT P.toBasic)
      K qRO qD) :
    INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic) :=
  owToIndcpa (tReductionD (toScheme P) (uRedROM B) qRO)

/-- The MLWE reduction `B1_st` at bit `b` for the adversary `advC P B`. -/
noncomputable def redC1
    (B : ROM2INDCCAAdversary (PK P.toBasic) K (CT P.toBasic) P.PT P.Seed (P.PT × CT P.toBasic)
      K qRO qD) (b : Bool) : P.Mat → P.Vec → SDistr Bool :=
  B1_st P.toBasic (choose_st P (advC P B)) (guess_st P (advC P B)) b

/-- The extended MLWE reduction `B2_ext_st` at bit `b` for the adversary `advC P B`. -/
noncomputable def redC2
    (B : ROM2INDCCAAdversary (PK P.toBasic) K (CT P.toBasic) P.PT P.Seed (P.PT × CT P.toBasic)
      K qRO qD) (b : Bool) : P.Mat → P.Vec → P.Vec → P.R → SDistr Bool :=
  B2_ext_st P.toBasic (choose_st P (advC P B)) (guess_st P (advC P B)) b

/-- The MLWE reduction `B1_st` at bit `b` for the adversary `advD P B`. -/
noncomputable def redD1
    (B : ROM2INDCCAAdversary (PK P.toBasic) K (CT P.toBasic) P.PT P.Seed (P.PT × CT P.toBasic)
      K qRO qD) (b : Bool) : P.Mat → P.Vec → SDistr Bool :=
  B1_st P.toBasic (choose_st P (advD P B)) (guess_st P (advD P B)) b

/-- The extended MLWE reduction `B2_ext_st` at bit `b` for the adversary `advD P B`. -/
noncomputable def redD2
    (B : ROM2INDCCAAdversary (PK P.toBasic) K (CT P.toBasic) P.PT P.Seed (P.PT × CT P.toBasic)
      K qRO qD) (b : Bool) : P.Mat → P.Vec → P.Vec → P.R → SDistr Bool :=
  B2_ext_st P.toBasic (choose_st P (advD P B)) (guess_st P (advD P B)) b

/-! ## The theorem -/

/-- **FO⊥̸ over the MLWE PKE is IND-CCA secure from module-LWE in the classical
random-oracle model.** For every IND-CCA adversary `B` against `foNotBot (toScheme P)`
asking at most `qRO` random-oracle queries, the bound of
`KEM.FOTransform.foNotBot_indcca_of_indcpa` holds with each IND-CPA advantage replaced
by the two MLWE advantages of `B1_st` and the two extended MLWE advantages of
`B2_ext_st` at that adversary (`redC1`, `redC2` for `advC P B`; `redD1`, `redD2` for
`advD P B`). -/
theorem foNotBot_indcca_mlwe
    (B : ROM2INDCCAAdversary (PK P.toBasic) K (CT P.toBasic) P.PT P.Seed (P.PT × CT P.toBasic)
      K qRO qD) :
    rom2INDCCAAdvantage (foNotBot (toScheme P)) B ≤
      (MLWE.advantage P.toBasic.toParams (redC1 P B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P B false) +
          MLWE.advantage P.toBasic.toParams (redC1 P B false) +
          (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (toScheme P).corrErr) +
        ((qRO + 1 : ℕ) : ℝ≥0∞) * (toScheme P).corrWorst + (toScheme P).corrErr +
        ((qRO + 1 : ℕ) : ℝ≥0∞) *
          (MLWE.advantage P.toBasic.toParams (redD1 P B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P B false) +
            MLWE.advantage P.toBasic.toParams (redD1 P B false) +
            (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (toScheme P).corrErr) +
        (qRO : ℝ≥0∞) / Fintype.card P.PT + (toScheme P).corrErr := by
  refine (foNotBot_indcca_of_indcpa (toScheme P) B).trans ?_
  gcongr
  · exact indcpaAdvantage_le_mlwe P (advC P B)
  · exact indcpaAdvantage_le_mlwe P (advD P B)

end CatCrypt.Crypto.MLKEM.FOFromMLWE

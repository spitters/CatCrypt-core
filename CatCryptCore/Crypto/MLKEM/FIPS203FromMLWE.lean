/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FIPS203Security
public import CatCryptCore.Crypto.MLKEM.FOFromMLWE
public import CatCryptCore.Crypto.MLKEM.CorrectnessBounds

/-!
# IND-CCA security of the FIPS 203 KEM over the MLWE PKE from module-LWE

The key-encapsulation mechanism `fips203 (toScheme P) hpk` over the base MLWE
public-key encryption scheme is IND-CCA secure in the classical random-oracle model,
with a bound in the module-LWE and extended module-LWE advantages of named reductions
together with correctness, message-space and seed terms.

The composition has two parts. `KEM.FIPS203.fips203_indcca` bounds the IND-CCA
advantage of `fips203 P hpk` by two OW-CPA advantages of the adversaries
`tReductionC P (redROM P hpk B)` and `tReductionD P (redROM P hpk B) (2 qRO)`;
`PKE.Games.owcpa_le_indcpa` replaces each OW-CPA advantage by an IND-CPA advantage of
`owToIndcpa` at that adversary, plus `1/|PT|` and the correctness error; and
`FOFromMLWE.indcpaAdvantage_le_mlwe` replaces each IND-CPA advantage of `toScheme P`
by two module-LWE and two extended module-LWE advantages.

## Main definitions

* `advC P hpk B`, `advD P hpk B` — the IND-CPA adversaries against `toScheme P` built
  from a two-oracle IND-CCA adversary `B` against `fips203 (toScheme P) hpk`
* `redC1`, `redC2`, `redD1`, `redD2` — the module-LWE and extended module-LWE
  reductions of `MLWE_PKE_Stateful` at these adversaries

## Main results

* `owcpa_le_mlweBound` — the OW-CPA advantage of an adversary against `toScheme P` is
  bounded by the module-LWE terms of its `owToIndcpa` lift
* `fips203_indcca_mlwe` — the IND-CCA advantage of `fips203 (toScheme P) hpk` is
  bounded by eight module-LWE terms of named reductions, the correctness terms of
  `toScheme P`, the message-space terms `1/|PT|` and the seed term `qRO/|Z|`
* `fips203_indcca_of_corr` — the same bound with both correctness quantities of
  `toScheme P` replaced by an upper bound on `corrWorst`
* `fips203_indcca_at_mlkem512Noise`, `fips203_indcca_at_mlkem768Noise`, `fips203_indcca_at_mlkem1024Noise` —
  the same bound with the two correctness quantities of `toScheme P` replaced by
  `decryptionFailureProb` at the noise parameters of the corresponding ML-KEM
  parameter set

## Model and hypotheses

* **Model.** The random-oracle model is classical: the oracles `G` and `J` are
  answered by lazily sampled tables and the adversary has classical access to them.
  The quantum bound is the development under `Quantum/QROM/`.
* **Correctness.** `fips203_indcca_at_mlkem512Noise` and its siblings take the
  hypothesis `hWorst : (toScheme P).corrWorst ≤ decryptionFailureProb … δ_c`, which
  bounds the correctness error of `toScheme P` by the union bound of `CorrectnessBounds`
  at the noise parameters of the parameter set (a statement over `NoiseParams`); the
  second correctness quantity `(toScheme P).corrErr` is bounded by
  `PKE.Games.Scheme.corrErr_le_corrWorst`.
* **Scheme.** `toScheme P` is the base MLWE PKE over a parameter record
  `MLWE_PKE_Scheme.Params`, and `fips203` is the transform of FIPS 203 applied to it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.FIPS203FromMLWE

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.PKE.Games
open CatCrypt.Crypto.KEM.Games (ROM2INDCCAAdversary rom2INDCCAAdvantage)
open CatCrypt.Crypto.KEM.FIPS203 (fips203 redROM fips203_indcca)
open CatCrypt.Crypto.PKE.FOTransformT (tReductionC tReductionD)
open MLWE_PKE_Basic (PK CT MLWE_Ext_advantage)
open MLWE_PKE_Scheme (toScheme)
open MLWE_PKE_Stateful
open FOFromMLWE (choose_st guess_st indcpaAdvantage_le_mlwe)
open scoped ENNReal

variable (P : MLWE_PKE_Scheme.Params)

variable {K Hash Z : Type} [Fintype K] [Nonempty K] [Fintype Z] [Nonempty Z]
  [DecidableEq Hash] [DecidableEq Z] {qRO qD : ℕ}

/-- The two-oracle IND-CCA adversary against the FIPS 203 KEM over `toScheme P`, with
random oracle `G : PT × Hash → K × Seed`, rejection oracle `J : Z × CT → K`, at most
`qRO` random-oracle queries and at most `qD` decapsulation queries. -/
abbrev Adversary (P : MLWE_PKE_Scheme.Params) (K Hash Z : Type) (qRO qD : ℕ) : Type 1 :=
  ROM2INDCCAAdversary (PK P.toBasic) K (CT P.toBasic) (P.PT × Hash) (K × P.Seed)
    (Z × CT P.toBasic) K qRO qD

/-! ## The reductions -/

variable (hpk : PK P.toBasic → Hash)

/-- The IND-CPA adversary against `toScheme P` built from `B`: `owToIndcpa` of the
OW-CPA adversary `tReductionC` at the OW-PCA reduction `redROM`. -/
noncomputable def advC (B : Adversary P K Hash Z qRO qD) :
    INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic) :=
  owToIndcpa (tReductionC (toScheme P) (redROM (toScheme P) hpk B))

/-- The IND-CPA adversary against `toScheme P` built from `B`: `owToIndcpa` of the
OW-CPA adversary `tReductionD` at the OW-PCA reduction `redROM` with log bound
`qRO + qRO`. -/
noncomputable def advD (B : Adversary P K Hash Z qRO qD) :
    INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic) :=
  owToIndcpa (tReductionD (toScheme P) (redROM (toScheme P) hpk B) (qRO + qRO))

/-- The module-LWE reduction `B1_st` at bit `b` for the adversary `advC P hpk B`. -/
noncomputable def redC1 (B : Adversary P K Hash Z qRO qD) (b : Bool) :
    P.Mat → P.Vec → SDistr Bool :=
  B1_st P.toBasic (choose_st P (advC P hpk B)) (guess_st P (advC P hpk B)) b

/-- The extended module-LWE reduction `B2_ext_st` at bit `b` for the adversary
`advC P hpk B`. -/
noncomputable def redC2 (B : Adversary P K Hash Z qRO qD) (b : Bool) :
    P.Mat → P.Vec → P.Vec → P.R → SDistr Bool :=
  B2_ext_st P.toBasic (choose_st P (advC P hpk B)) (guess_st P (advC P hpk B)) b

/-- The module-LWE reduction `B1_st` at bit `b` for the adversary `advD P hpk B`. -/
noncomputable def redD1 (B : Adversary P K Hash Z qRO qD) (b : Bool) :
    P.Mat → P.Vec → SDistr Bool :=
  B1_st P.toBasic (choose_st P (advD P hpk B)) (guess_st P (advD P hpk B)) b

/-- The extended module-LWE reduction `B2_ext_st` at bit `b` for the adversary
`advD P hpk B`. -/
noncomputable def redD2 (B : Adversary P K Hash Z qRO qD) (b : Bool) :
    P.Mat → P.Vec → P.Vec → P.R → SDistr Bool :=
  B2_ext_st P.toBasic (choose_st P (advD P hpk B)) (guess_st P (advD P hpk B)) b

/-- The four module-LWE terms of the IND-CPA bound at a two-stage adversary, together
with the message-space term `1/|PT|` and the correctness error: the bound on the
OW-CPA advantage of an adversary whose `owToIndcpa` lift is `A`. -/
noncomputable def mlweBound
    (r1 : Bool → P.Mat → P.Vec → SDistr Bool)
    (r2 : Bool → P.Mat → P.Vec → P.Vec → P.R → SDistr Bool) : ℝ≥0∞ :=
  MLWE.advantage P.toBasic.toParams (r1 true) +
    MLWE_Ext_advantage P.toBasic (r2 true) +
    MLWE_Ext_advantage P.toBasic (r2 false) +
    MLWE.advantage P.toBasic.toParams (r1 false) +
    (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (toScheme P).corrErr

/-! ## The bound over an arbitrary MLWE PKE -/

/-- The OW-CPA advantage of an adversary against `toScheme P` is bounded by the four
module-LWE terms of its `owToIndcpa` lift, the message-space term and the correctness
error. -/
theorem owcpa_le_mlweBound (A : PK P.toBasic → CT P.toBasic → PMF P.PT) :
    owcpaAdvantage (toScheme P) A ≤
      mlweBound P (fun b => B1_st P.toBasic (choose_st P (owToIndcpa A))
          (guess_st P (owToIndcpa A)) b)
        (fun b => B2_ext_st P.toBasic (choose_st P (owToIndcpa A))
          (guess_st P (owToIndcpa A)) b) := by
  refine (owcpa_le_indcpa (toScheme P) A).trans ?_
  unfold mlweBound
  gcongr
  exact indcpaAdvantage_le_mlwe P (owToIndcpa A)

/-- **The FIPS 203 KEM over the MLWE PKE is IND-CCA secure from module-LWE in the
classical random-oracle model.** For every two-oracle IND-CCA adversary `B` against
`fips203 (toScheme P) hpk` asking at most `qRO` random-oracle queries, the bound of
`KEM.FIPS203.fips203_indcca` holds with each OW-CPA advantage replaced by the two
module-LWE advantages of `B1_st`, the two extended module-LWE advantages of
`B2_ext_st`, the message-space term `1/|PT|` and the correctness error
(`redC1`, `redC2` for `advC P hpk B`; `redD1`, `redD2` for `advD P hpk B`). -/
theorem fips203_indcca_mlwe (B : Adversary P K Hash Z qRO qD) :
    rom2INDCCAAdvantage (fips203 (toScheme P) hpk) B ≤
      mlweBound P (redC1 P hpk B) (redC2 P hpk B) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * (toScheme P).corrWorst + (toScheme P).corrErr +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * mlweBound P (redD1 P hpk B) (redD2 P hpk B) +
        (qRO : ℝ≥0∞) / Fintype.card Z + (toScheme P).corrErr := by
  refine (fips203_indcca (toScheme P) hpk B).trans ?_
  gcongr
  · exact owcpa_le_mlweBound P _
  · exact owcpa_le_mlweBound P _

/-! ## The bound at the concrete noise parameters -/

section Concrete

open CatCrypt.Crypto.MLKEM.CorrectnessBounds (decryptionFailureProb mlkem512Noise
  mlkem768Noise mlkem1024Noise)

/-- The bound of `fips203_indcca_mlwe` with the two correctness quantities of
`toScheme P` replaced by an upper bound `δ`. -/
theorem fips203_indcca_of_corr (B : Adversary P K Hash Z qRO qD) (δ : ℝ≥0∞)
    (hWorst : (toScheme P).corrWorst ≤ δ) :
    rom2INDCCAAdvantage (fips203 (toScheme P) hpk) B ≤
      (MLWE.advantage P.toBasic.toParams (redC1 P hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P hpk B false) +
          MLWE.advantage P.toBasic.toParams (redC1 P hpk B false) +
          (Fintype.card P.PT : ℝ≥0∞)⁻¹ + δ) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * δ + δ +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) *
          (MLWE.advantage P.toBasic.toParams (redD1 P hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P hpk B false) +
            MLWE.advantage P.toBasic.toParams (redD1 P hpk B false) +
            (Fintype.card P.PT : ℝ≥0∞)⁻¹ + δ) +
        (qRO : ℝ≥0∞) / Fintype.card Z + δ := by
  have hErr : (toScheme P).corrErr ≤ δ := (Scheme.corrErr_le_corrWorst (toScheme P)).trans hWorst
  refine (fips203_indcca_mlwe P hpk B).trans ?_
  unfold mlweBound
  gcongr

/-- The bound of `fips203_indcca_mlwe` with the two correctness quantities of
`toScheme P` bounded by the ML-KEM-512 decryption-failure probability at
per-coefficient failure probability `δ_c`. -/
theorem fips203_indcca_at_mlkem512Noise (B : Adversary P K Hash Z qRO qD) (δ_c : ℝ≥0∞)
    (hWorst : (toScheme P).corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c) :
    rom2INDCCAAdvantage (fips203 (toScheme P) hpk) B ≤
      (MLWE.advantage P.toBasic.toParams (redC1 P hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P hpk B false) +
          MLWE.advantage P.toBasic.toParams (redC1 P hpk B false) +
          (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (256 : ℝ≥0∞) * δ_c) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * ((256 : ℝ≥0∞) * δ_c) + (256 : ℝ≥0∞) * δ_c +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) *
          (MLWE.advantage P.toBasic.toParams (redD1 P hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P hpk B false) +
            MLWE.advantage P.toBasic.toParams (redD1 P hpk B false) +
            (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (256 : ℝ≥0∞) * δ_c) +
        (qRO : ℝ≥0∞) / Fintype.card Z + (256 : ℝ≥0∞) * δ_c := by
  have h := fips203_indcca_of_corr P hpk B _ hWorst
  rwa [CorrectnessBounds.mlkem512_failure_from_coeff] at h

/-- The bound of `fips203_indcca_mlwe` with the two correctness quantities of
`toScheme P` bounded by the ML-KEM-768 decryption-failure probability at
per-coefficient failure probability `δ_c`. The parameter record `P` is free: the
theorem holds for every MLWE PKE parameter record, and `768` names the noise
parameters `mlkem768Noise` of the correctness term only. `toScheme P` has no
ciphertext compression. -/
theorem fips203_indcca_at_mlkem768Noise (B : Adversary P K Hash Z qRO qD) (δ_c : ℝ≥0∞)
    (hWorst : (toScheme P).corrWorst ≤ decryptionFailureProb mlkem768Noise δ_c) :
    rom2INDCCAAdvantage (fips203 (toScheme P) hpk) B ≤
      (MLWE.advantage P.toBasic.toParams (redC1 P hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P hpk B false) +
          MLWE.advantage P.toBasic.toParams (redC1 P hpk B false) +
          (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (256 : ℝ≥0∞) * δ_c) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * ((256 : ℝ≥0∞) * δ_c) + (256 : ℝ≥0∞) * δ_c +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) *
          (MLWE.advantage P.toBasic.toParams (redD1 P hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P hpk B false) +
            MLWE.advantage P.toBasic.toParams (redD1 P hpk B false) +
            (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (256 : ℝ≥0∞) * δ_c) +
        (qRO : ℝ≥0∞) / Fintype.card Z + (256 : ℝ≥0∞) * δ_c := by
  have h := fips203_indcca_of_corr P hpk B _ hWorst
  rwa [CorrectnessBounds.mlkem768_failure_from_coeff] at h

/-- The bound of `fips203_indcca_mlwe` with the two correctness quantities of
`toScheme P` bounded by the ML-KEM-1024 decryption-failure probability at
per-coefficient failure probability `δ_c`. -/
theorem fips203_indcca_at_mlkem1024Noise (B : Adversary P K Hash Z qRO qD) (δ_c : ℝ≥0∞)
    (hWorst : (toScheme P).corrWorst ≤ decryptionFailureProb mlkem1024Noise δ_c) :
    rom2INDCCAAdvantage (fips203 (toScheme P) hpk) B ≤
      (MLWE.advantage P.toBasic.toParams (redC1 P hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P hpk B false) +
          MLWE.advantage P.toBasic.toParams (redC1 P hpk B false) +
          (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (256 : ℝ≥0∞) * δ_c) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * ((256 : ℝ≥0∞) * δ_c) + (256 : ℝ≥0∞) * δ_c +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) *
          (MLWE.advantage P.toBasic.toParams (redD1 P hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P hpk B false) +
            MLWE.advantage P.toBasic.toParams (redD1 P hpk B false) +
            (Fintype.card P.PT : ℝ≥0∞)⁻¹ + (256 : ℝ≥0∞) * δ_c) +
        (qRO : ℝ≥0∞) / Fintype.card Z + (256 : ℝ≥0∞) * δ_c := by
  have h := fips203_indcca_of_corr P hpk B _ hWorst
  rwa [CorrectnessBounds.mlkem1024_failure_from_coeff] at h

end Concrete

end CatCrypt.Crypto.MLKEM.FIPS203FromMLWE

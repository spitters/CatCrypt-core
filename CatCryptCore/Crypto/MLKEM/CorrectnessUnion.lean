/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.CorrectnessDecode
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# The union bound over the coefficients of the ML-KEM decryption noise

The correctness error `corrWorst` of the base MLWE public-key encryption scheme at module
rank `k` and noise parameters `η₁`, `η₂` is at most the sum over the 256 coefficients of
the probability, under uniform key-generation and encryption coins, that the coefficient
of the decryption noise `e · r + e₂ − s · e₁` has centred absolute value at least `832`.
The bound does not depend on the matrix or the message: by the decode lemma
`exists_large_noise_of_decrypt_ne`, every decryption failure has such a coefficient.

## Main definitions

* `Coins k η₁ η₂` — the seeds of one key generation and one encryption
* `coinNoise c` — the decryption noise `e · r + e₂ − s · e₁` of the coins `c`

## Main results

* `failProb_le_noise` — the failure probability at one key pair and message is at most
  the probability of a large noise coefficient under the encryption seed
* `corrWorst_le_sum_coeff` — the union bound over the 256 coefficients
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MLKEMRankInstance

open CatCrypt.Util
open MLKEM512Instance (Rq Msg PrfBlock samplePoly)
open CatCrypt.Crypto.MLKEM.Compress (centeredAbs)
open scoped ENNReal

/-- The coins of one key generation and one encryption at rank `k`: the key seed of
`(s, e)` and the encryption seed of `(r, e₁, e₂)`. -/
abbrev Coins (k η₁ η₂ : ℕ) : Type :=
  (PrfVecBlock k η₁ × PrfVecBlock k η₁) × (PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂)

/-- The decryption noise `e · r + e₂ − s · e₁` of the coins. -/
def coinNoise {k η₁ η₂ : ℕ} (c : Coins k η₁ η₂) : Rq :=
  vecDot (sampleVec k η₁ c.1.2) (sampleVec k η₁ c.2.1) + samplePoly η₂ c.2.2.2 -
    vecDot (sampleVec k η₁ c.1.1) (sampleVec k η₂ c.2.2.1)

/-- The event that some coefficient of the decryption noise of a key seed and an
encryption seed has centred absolute value at least `832`. -/
def LargeNoise {k η₁ η₂ : ℕ} (ks : PrfVecBlock k η₁ × PrfVecBlock k η₁)
    (sd : PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂) : Prop :=
  ∃ i, 832 ≤ centeredAbs (coinNoise (ks, sd) i)

/-- The failure probability at the key pair of a matrix and a key seed is at most the
probability, under a uniform encryption seed, of a large noise coefficient. -/
theorem failProb_le_noise (k η₁ η₂ : ℕ) (A : Mat k) (ks : PrfVecBlock k η₁ × PrfVecBlock k η₁)
    (m : Msg) :
    (MLWE_PKE_Scheme.toScheme (paramsOfRankEta k η₁ η₂)).failProb
        (A, vecAdd (matVecMul A (sampleVec k η₁ ks.1)) (sampleVec k η₁ ks.2))
        (sampleVec k η₁ ks.1) m ≤
      (PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂)).toOuterMeasure
        {sd | LargeNoise ks sd} := by
  apply MeasureTheory.measure_mono
  intro sd hsd
  exact exists_large_noise_of_decrypt_ne A _ _ _ _ _ m (fun h => hsd (congrArg some h))

/-- The correctness error is at most the expected probability, over the key seed, of a
large noise coefficient. -/
theorem corrWorst_le_tsum_noise (k η₁ η₂ : ℕ) :
    (MLWE_PKE_Scheme.toScheme (paramsOfRankEta k η₁ η₂)).corrWorst ≤
      ∑' ks, PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₁) ks *
        (PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂)).toOuterMeasure
          {sd | LargeNoise ks sd} := by
  unfold PKE.Games.Scheme.corrWorst
  simp only [MLWE_PKE_Scheme.toScheme]
  rw [PMF.tsum_bind_mul]
  simp only [← PMF.tsum_mul_comp_eq_map]
  calc _ ≤ ∑' A : Mat k, PMF.uniformFintype (Mat k) A *
        ∑' ks, PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₁) ks *
          (PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂)).toOuterMeasure
            {sd | LargeNoise ks sd} := by
        refine ENNReal.tsum_le_tsum fun A => mul_le_mul' le_rfl ?_
        refine ENNReal.tsum_le_tsum fun ks => mul_le_mul' le_rfl ?_
        exact iSup_le fun m => failProb_le_noise k η₁ η₂ A ks m
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The probability of a large noise coefficient under uniform coins is the expectation
over the key seed of its probability under the encryption seed. -/
theorem uniform_coins_largeNoise (k η₁ η₂ : ℕ) :
    (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure {c | LargeNoise c.1 c.2} =
      ∑' ks, PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₁) ks *
        (PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂)).toOuterMeasure
          {sd | LargeNoise ks sd} := by
  rw [PMF.uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply]
  rfl

/-- **The union bound over the coefficients.** The correctness error of the base MLWE
PKE at rank `k` is at most the sum over the 256 coefficients of the probability, under
uniform coins, that the coefficient of the decryption noise has centred absolute value at
least `832`. -/
theorem corrWorst_le_sum_coeff (k η₁ η₂ : ℕ) :
    (MLWE_PKE_Scheme.toScheme (paramsOfRankEta k η₁ η₂)).corrWorst ≤
      ∑ i : Fin 256, (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure
        {c | 832 ≤ centeredAbs (coinNoise c i)} := by
  calc _ ≤ _ := corrWorst_le_tsum_noise k η₁ η₂
    _ = (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure
          (⋃ i : Fin 256, {c | 832 ≤ centeredAbs (coinNoise c i)}) := by
        rw [← uniform_coins_largeNoise]
        congr 1
        ext c
        simp [LargeNoise]
    _ ≤ _ := MeasureTheory.measure_iUnion_fintype_le _ _

end CatCrypt.Crypto.MLKEM.MLKEMRankInstance

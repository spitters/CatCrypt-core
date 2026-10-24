/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLKEM512Hypotheses
public import CatCryptCore.Crypto.MLKEM.CorrectnessBounds

/-!
# The failure-bound hypothesis of the quantum ML-KEM-512 theorem

The failure bound `lam` of `FIPS203QROMQuantumMLWE.mlkem512_qindcca_qmlwe_coll`
is instantiated at the largest decryption-failure probability over messages of
each key pair, and the weighted failure term `Λ = ∑ i, kemSample i · lam i.1` of
that theorem is the correctness error `corrWorst` of `mlkem512CompressedScheme`.

## Main definitions

* `lamWorst ks` — the largest failure probability over messages, over a uniform
  encryption seed, under the key pair `ks`

## Main results

* `card_badVals_kemBad_div_le` — the bad values at a point of the `G`-table, as a
  fraction of all values, are at most the failure probability of its message
* `sum_kemSample_mul_fst` — the `kemSample`-expectation of a function of the key pair
  is its `keygen`-expectation
* `hlam_lamWorst` — `lamWorst` satisfies the failure-bound hypothesis `hlam`
* `sum_kemSample_lamWorst` — `Λ` at `lamWorst` equals `corrWorst`

## The correctness hypothesis

The classical theorem `CompressedPKE.mlkem512Compressed_indcca` and the quantum
theorem `MLKEM512QROM.mlkem512_qindcca_coll` take the correctness hypothesis
`corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c`; by `sum_kemSample_lamWorst`,
the failure term `Λ` at `lamWorst` is that `corrWorst`. FIPS 203 states the value
`2^-139` for the decryption-failure probability, computed by a numerical convolution
of the noise distributions.

References: Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the
Fujisaki-Okamoto transformation", TCC 2017, ePrint 2017/604 (δ-correctness as
the key-averaged worst-message failure probability); NIST, FIPS 203,
"Module-Lattice-Based Key-Encapsulation Mechanism Standard", 2024 (the quoted
decryption-failure probability `2^-139`); Hövelmanns, Hülsing, Majenz, "Failing
gracefully: decryption failures and the Fujisaki-Okamoto transform", ASIACRYPT
2022, ePrint 2022/365.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Crypto.MLKEM.MLKEM512FailureBound

open CatCrypt.Quantum CatCrypt.Quantum.QROM
open PKE.Games (Scheme)

/-! ## Generic counting -/

section Generic

variable {m₁ m₂ n : ℕ} {PK SK M C R K Hash Z : Type} [Fintype R] [Nonempty R]
  [DecidableEq Hash] [DecidableEq M]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eKR : (K × R) ≃ Fin n)

/-- The bad values at a point `x` of the `G`-table, as a fraction of all `n` values,
are at most the failure probability of the message of `x`: a bad value has a coin
part on which decryption fails, whatever its key part. -/
theorem card_badVals_kemBad_div_le [Fintype K] [Nonempty K] (pk : PK) (sk : SK)
    (x : Fin m₁) :
    ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤
      P.failProb pk sk (eG.symm x).1 := by
  classical
  set m := (eG.symm x).1
  set S := Finset.univ.filter (fun r : R => P.dec sk (P.enc pk m r) ≠ some m)
  have hsub : badVals (kemBad P hpk eG eKR pk sk) x ⊆
      (Finset.univ ×ˢ S).map eKR.toEmbedding := by
    intro y hy
    simp only [badVals, kemBad, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hy
    rw [Finset.mem_map_equiv]
    simp only [Finset.mem_product, Finset.mem_univ, true_and, S, Finset.mem_filter]
    exact hy.2
  have hcard : (badVals (kemBad P hpk eG eKR pk sk) x).card ≤ Fintype.card K * S.card := by
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_map, Finset.card_product, Finset.card_univ]
  have hn : n = Fintype.card K * Fintype.card R := by
    rw [← Fintype.card_prod, Fintype.card_congr eKR, Fintype.card_fin]
  have hfp : P.failProb pk sk m = (S.card : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
    rw [Scheme.failProb, PMF.toOuterMeasure_uniformFintype_apply]
    congr 2
    rw [Fintype.card_ofFinset]
    congr 1
  rw [hfp]
  generalize (badVals (kemBad P hpk eG eKR pk sk) x).card = b at hcard ⊢
  generalize S.card = s at hcard ⊢
  rw [hn]
  have hK : (Fintype.card K : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc (b : ℝ≥0∞) / ((Fintype.card K * Fintype.card R : ℕ) : ℝ≥0∞)
      ≤ ((Fintype.card K * s : ℕ) : ℝ≥0∞) /
          ((Fintype.card K * Fintype.card R : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hcard) _
    _ = (s : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞) := by
        push_cast
        exact ENNReal.mul_div_mul_left _ _ hK (ENNReal.natCast_ne_top _)

omit [Fintype R] [Nonempty R] [DecidableEq Hash] [DecidableEq M] in
/-- The `kemSample`-expectation of a function of the key pair is its
`keygen`-expectation: the weight of an input is its key-pair weight times a constant
over the rest of the input, and the constants sum to one. -/
theorem sum_kemSample_mul_fst [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M]
    [Fintype Z] [Nonempty Z] [Fintype K] [Nonempty K] [NeZero n] (f : PK × SK → ℝ≥0∞) :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * f i.1 = ∑ ks, P.keygen ks * f ks := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ks _ => ?_
  simp only [kemSample, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  have hc : ∀ t : ℕ, t ≠ 0 → (t : ℝ≥0∞) * (t : ℝ≥0∞)⁻¹ = 1 := fun t ht =>
    ENNReal.mul_inv_cancel (by exact_mod_cast ht) (ENNReal.natCast_ne_top t)
  have hp : ∀ e : ℕ, (n : ℝ≥0∞) ^ e * ((n : ℝ≥0∞) ^ e)⁻¹ = 1 := fun e =>
    ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast NeZero.ne n))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  have hZ := hc _ (Fintype.card_ne_zero (α := Z))
  have hM := hc _ (Fintype.card_ne_zero (α := M))
  have hK := hc _ (Fintype.card_ne_zero (α := K))
  have h₁ := hp m₁
  have h₂ := hp m₂
  generalize ((Fintype.card Z : ℕ) : ℝ≥0∞) = z at hZ ⊢
  generalize ((Fintype.card M : ℕ) : ℝ≥0∞) = u at hM ⊢
  generalize ((Fintype.card K : ℕ) : ℝ≥0∞) = v at hK ⊢
  generalize (n : ℝ≥0∞) ^ m₁ = a at h₁ ⊢
  generalize (n : ℝ≥0∞) ^ m₂ = b at h₂ ⊢
  calc z * (u * (v * (a * b))) * (P.keygen ks * z⁻¹ * u⁻¹ * v⁻¹ * a⁻¹ * b⁻¹ * f ks)
      = P.keygen ks * f ks * ((z * z⁻¹) * (u * u⁻¹) * (v * v⁻¹) * (a * a⁻¹) * (b * b⁻¹)) := by
        ac_rfl
    _ = P.keygen ks * f ks := by rw [hZ, hM, hK, h₁, h₂]; simp

end Generic

/-! ## ML-KEM-512 -/

section QINDCCA

open MLKEM512Instance
open CompressedPKE (MLKEM512CT mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)

/-- The largest failure probability over messages, over a uniform encryption seed,
of `mlkem512CompressedScheme` under the key pair `ks`.

References: Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the
Fujisaki-Okamoto transformation", TCC 2017, ePrint 2017/604 (the per-key
worst-message quantity whose key average is δ-correctness). -/
def lamWorst (ks : PK mlkem512Params.toBasic × MLWE_PKE_Basic.SK mlkem512Params.toBasic) :
    ℝ≥0∞ :=
  ⨆ m, mlkem512CompressedScheme.failProb ks.1 ks.2 m

variable {m₁ m₂ n w q k c a : ℕ} {K Hash Z : Type} [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [DecidableEq Hash]
  (hpk : PK mlkem512Params.toBasic → Hash) (eG : (mlkem512Params.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × MLKEM512CT) ≃ Fin m₂) (eKR : (K × mlkem512Params.Seed) ≃ Fin n)
  (eC : MLKEM512CT ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c] [NeZero a] [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]

omit [Fintype Z] [Nonempty Z] [DecidableEq Z] [NeZero n] [NeZero c] [NeZero a]
  [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)] in
/-- `lamWorst` satisfies the failure-bound hypothesis `hlam` of
`FIPS203QROMQuantumMLWE.mlkem512_qindcca_qmlwe_coll`. -/
theorem hlam_lamWorst (pk : PK mlkem512Params.toBasic)
    (sk : MLWE_PKE_Basic.SK mlkem512Params.toBasic) (x : Fin m₁) :
    ((badVals (kemBad mlkem512CompressedScheme hpk eG eKR pk sk) x).card : ℝ≥0∞) /
      (n : ℝ≥0∞) ≤ lamWorst (pk, sk) :=
  (card_badVals_kemBad_div_le _ hpk eG eKR pk sk x).trans (le_iSup _ _)

omit [DecidableEq Z] [NeZero (m₁ + m₂)] in
/-- The weighted failure term of `mlkem512_qindcca_qmlwe_coll` at `lamWorst` is
the correctness error of `mlkem512CompressedScheme`.

References: Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the
Fujisaki-Okamoto transformation", TCC 2017, ePrint 2017/604 (δ-correctness);
NIST, FIPS 203, "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
2024 (the quoted value `2^-139` for ML-KEM-512); Hövelmanns, Hülsing, Majenz,
"Failing gracefully: decryption failures and the Fujisaki-Okamoto transform",
ASIACRYPT 2022, ePrint 2022/365. -/
theorem sum_kemSample_lamWorst :
    ∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
        Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lamWorst i.1 =
      mlkem512CompressedScheme.corrWorst := by
  rw [sum_kemSample_mul_fst, PKE.Games.Scheme.corrWorst, tsum_fintype]
  rfl

end QINDCCA

end CatCrypt.Crypto.MLKEM.MLKEM512FailureBound

end

end

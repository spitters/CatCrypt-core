/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.PolyOracle
public import CatCryptCore.Crypto.MLKEM.MLKEM512FailureBound

/-!
# ML-KEM-512 in the quantum random-oracle model under module-LWE and extended module-LWE

The quantum IND-CCA advantage of the FIPS 203 Fujisaki–Okamoto KEM over an
idealised ML-KEM-512 K-PKE with compressed ciphertexts,
`CompressedPKE.mlkem512CompressedScheme`, against every
quantum adversary with superposition access to both random oracles and `k`
classical decapsulation rounds, is bounded by quantum module-LWE and extended
module-LWE advantages of explicit reductions without oracle access, the decryption-failure
bound `decryptionFailureProb mlkem512Noise δ_c`, a bound `ε` on the coin-collision
weight of the scheme and the query-count terms.

## Main results

* `mlkem512_qindcca_coll` — with `q' = flatQ q k q`, `q'' = flatQ (q + 4) k q`,
  `Λ = decryptionFailureProb mlkem512Noise δ_c`, `ε` a bound on
  `collWeight mlkem512CompressedScheme` and `B_b` the module-LWE term
  `qMLWEStdBound` of the normal form `nfKEM A` at challenge bit `b`,

  `Adv ≤ 4 √(4 q'² (B_true + Λ)) + (8 q' √Λ + (Λ + ε) + 8 q' √Λ)
    + 4 √(4 q'² (B_false + Λ)) + 2 (8 q' / √|Z| + 8 q'' √Λ + Λ + 8 q' √Λ)`.

  `MLKEM512QROMNumeric.mlkem512_qindcca_numeric` is this bound at the proved
  collision term `collBound`.

## The model

The K-PKE `CompressedPKE.mlkem512CompressedScheme` is idealised in three places:
the random oracle `G` returns the key together with the whole pseudorandom block
from which the encryption noise is sampled, the key-generation noise is drawn
uniformly, and the matrix `A` is drawn uniformly. The bound contains no PRF or XOF
term. The noise derived as `PRF_η` and the matrix expanded as `SampleNTT(XOF(ρ))`
are treated in `PRFOracle` and `XOFMatrix`.

The hypotheses of `mlkem512_qindcca_coll` are:

* module-LWE (`qMLWE`, the key-generation instance) and extended module-LWE
  (`qMLWEExt`, a `(k+1) × k` instance with the secret at `η₁` and the errors at
  `η₂`) at `mlkem512Params`, against quantum distinguishers without oracle
  access, as the four advantages in each `qMLWEStdBound`;
* `hWorst : corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c`, the correctness
  hypothesis of the classical theorem `CompressedPKE.mlkem512Compressed_indcca`;
* the polynomial-oracle data `PG`, `PJ`, `PH`, `PT` for the four auxiliary tables.
  `PolyData.nonempty_galois` supplies them over `GaloisField 2 N` when the range
  sizes `|K|` and `n` are powers of two and each domain has at most `2 ^ N`
  elements.

The coin hypothesis (`MLKEM512Hypotheses.mlkem512_hcoin`) is proved, and the
collision weight is bounded by `CollisionSpreadBound.collWeight_mlkem512_le`.

The reductions `qRedPoly`, `qRedEnc`, `qRedExt`, `indRed` and `owRedQuery` are
efficient: each runs the adversary's circuit up to a uniformly drawn query index
with its oracle calls kept, draws polynomial coefficient vectors of length
`auxDeg q k` in place of oracle tables, and performs at most one encryption or
compression and a constant number of classical draws. None of them draws a whole
oracle table or computes a measurement distribution.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Crypto.MLKEM.MLKEM512QROM

open CatCrypt.Quantum CatCrypt.Quantum.QROM
open MLKEM512Instance (mlkem512Params)
open CompressedPKE (MLKEM512CT mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)
open FIPS203QROMQuantumMLWE (qMLWEBound mlkem512_qindcca_qmlwe_coll)
open MLKEM512FailureBound (lamWorst hlam_lamWorst sum_kemSample_lamWorst)
open CorrectnessBounds (decryptionFailureProb mlkem512Noise)

variable {m₁ m₂ n w q k c a : ℕ} {K Hash Z : Type} [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [DecidableEq Hash]
  (hpk : PK mlkem512Params.toBasic → Hash) (eG : (mlkem512Params.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × MLKEM512CT) ≃ Fin m₂) (eKR : (K × mlkem512Params.Seed) ≃ Fin n)
  (eC : MLKEM512CT ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c] [NeZero a] [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]

open scoped Classical in
/-- **The FIPS 203 Fujisaki–Okamoto KEM over the idealised ML-KEM-512 K-PKE in the
quantum random-oracle model, under quantum module-LWE and extended module-LWE.**
The K-PKE idealisations are listed in the module docstring. For every quantum
adversary `A` with `k` decapsulation rounds and every polynomial-oracle data
`PG`, `PJ`, `PH`, `PT` for the auxiliary tables, under `hWorst`, with
`q' = flatQ q k q`, `q'' = flatQ (q + 4) k q`,
`Λ = decryptionFailureProb mlkem512Noise δ_c` and `ε` any bound on the
coin-collision weight `collWeight mlkem512CompressedScheme`
(`Quantum/QROM/CollisionWeight.lean`), the advantage is at most

`4 √(4 q'² (B_true + Λ)) + (8 q' √Λ + (Λ + ε) + 8 q' √Λ)
  + 4 √(4 q'² (B_false + Λ)) + 2 (8 q' / √|Z| + 8 q'' √Λ + Λ + 8 q' √Λ)`,

where `B_b = qMLWEStdBound … (nfKEM A) b` is two module-LWE and two extended
module-LWE advantages of the reductions `qRedPoly`, plus `|M|⁻¹` and the
decryption error of the scheme. `MLKEM512QROMNumeric.mlkem512_qindcca_numeric`
is this bound at the proved collision term `collBound`. -/
theorem mlkem512_qindcca_coll (PG : PolyData (Fin m₁) (Fin n)) (PJ : PolyData (Fin m₂) (Fin n))
    (PH : PolyData MLKEM512CT K) (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K) (δ_c : ℝ≥0∞)
    (hWorst : mlkem512CompressedScheme.corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c)
    (ε : ℝ≥0∞) (hcoll : collWeight mlkem512CompressedScheme ≤ ε) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) true +
            decryptionFailureProb mlkem512Noise δ_c))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) * decryptionFailureProb mlkem512Noise δ_c ^ (1 / 2 : ℝ) +
          (decryptionFailureProb mlkem512Noise δ_c + ε) +
          8 * (flatQ q k q : ℝ≥0∞) * decryptionFailureProb mlkem512Noise δ_c ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) false +
            decryptionFailureProb mlkem512Noise δ_c))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) * decryptionFailureProb mlkem512Noise δ_c ^ (1 / 2 : ℝ) +
          decryptionFailureProb mlkem512Noise δ_c +
          8 * (flatQ q k q : ℝ≥0∞) * decryptionFailureProb mlkem512Noise δ_c ^ (1 / 2 : ℝ))) := by
  have h := mlkem512_qindcca_qmlwe_coll hpk eG eJ eKR eC eKa A ε hcoll
    MLKEM512Hypotheses.mlkem512_hcoin lamWorst (fun pk sk _ x => hlam_lamWorst hpk eG eKR pk sk x)
  rw [sum_kemSample_lamWorst] at h
  simp only [qMLWEBound_eq_qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT] at h
  refine h.trans ?_
  gcongr

end CatCrypt.Crypto.MLKEM.MLKEM512QROM

end

end

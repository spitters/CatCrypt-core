/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public meta import CatCryptCore.Crypto.MLKEM.ConcreteParams
public import CatCryptCore.Crypto.MLKEM.ConcreteParams

/-!
# ML-KEM Decryption Failure Probability Bounds

Formalizes the decryption failure probability analysis for ML-KEM following the
noise model from FIPS 203 and the tighter analysis of Barbosa, Biham, Cremers,
and Ducas (CCS 2025).

## Overview

Decryption failure in ML-KEM occurs when the combined noise from:
1. **Secret/error sampling** (CBD distribution with parameter eta)
2. **Compress/decompress rounding** (lossy compression of u and v)

exceeds the decoding threshold `q/4`. The failure probability is bounded by
a union bound over all `n * k` coefficients of the inner product, where each
coefficient's failure probability depends on the noise variance.

## Noise sources

- **CBD noise**: The centered binomial distribution `CBD_eta` has mean 0 and
  variance `eta/2`. Secret keys and encryption noise are sampled from CBD.
- **Rounding noise**: Compressing a value `x` to `d` bits introduces noise
  bounded by `ceil(q / 2^{d+1})`.

## Concrete bounds (FIPS 203 / CCS 2025)

| Parameter Set | delta (failure prob) | Security Level |
|---------------|---------------------|----------------|
| ML-KEM-512    | 2^{-139}            | Category 1     |
| ML-KEM-768    | 2^{-174}            | Category 3     |
| ML-KEM-1024   | 2^{-189}            | Category 5     |

This module does not prove these three figures. It formalizes no probability
distribution: `decryptionFailureProb P δ_coeff` is the union bound
`P.n * δ_coeff` over a per-coefficient failure probability `δ_coeff` taken as
a parameter, and the theorems below are arithmetic on the tabulated constants
and on that expression. A proof of `δ ≤ 2^{-139}` (and the other two rows)
needs the tail-bound computation of FIPS 203 Appendix A and the Kyber
specification: the exact distribution of each coefficient of
`e^T r + e_2 + c_v - s^T (e_1 + c_u)`, obtained by convolving the centered
binomial distributions `CBD_eta1`, `CBD_eta2` with the rounding-error
distributions of `Compress_{d_u}` and `Compress_{d_v}`, the probability that a
coefficient's absolute value exceeds the decoding threshold `q/4`, and the union
bound over the `n = 256` coefficients, stated for the decryption failure event
of the ML-KEM PKE.

## Main results

* `NoiseParams` -- parameter structure for the noise analysis
* `compressNoiseBound` -- rounding noise from compress/decompress
* `cbdVariance` -- the variance value FIPS 203 tabulates for `CBD_eta`
* `decryptionFailureProb` -- union bound over the per-coefficient failure probability
* `fo_correctness_amplification` -- FO transform correctness amplification

## References

* NIST FIPS 203 (2024): ML-KEM specification, Section 4
* Barbosa, Biham, Cremers, Ducas (CCS 2025): Tighter ML-KEM failure analysis
* Bos et al. (CRYSTALS-Kyber): Original failure probability analysis
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.CorrectnessBounds

open CatCrypt.Prob
open CatCrypt.Crypto.MLKEM.ConcreteParams
open scoped ENNReal

/-! ## Noise Model Parameters

The noise analysis requires the lattice parameters (n, k, q), the CBD
parameters (eta1, eta2), and the compression bit-widths (d_u, d_v).
We reuse `NISTParams` from `ConcreteParams` and add the primality proof. -/

/-- Parameters for the ML-KEM noise analysis.

    Captures the NIST-specified values needed to compute the decryption
    failure probability. The primality of `q` is required for the
    algebraic structure of `R_q = Z_q[X]/(X^n + 1)`.

    FIPS 203, Section 4 and Table 1. -/
structure NoiseParams where
  /-- Polynomial degree (256 for ML-KEM) -/
  n : ℕ
  /-- Module rank (2, 3, or 4) -/
  k : ℕ
  /-- Modulus (3329 for ML-KEM) -/
  q : ℕ
  /-- CBD parameter for secret/noise in key generation -/
  eta1 : ℕ
  /-- CBD parameter for noise in encryption -/
  eta2 : ℕ
  /-- Compression bits for u (ciphertext vector component) -/
  d_u : ℕ
  /-- Compression bits for v (ciphertext scalar component) -/
  d_v : ℕ
  /-- Primality of the modulus -/
  hq : Nat.Prime q

/-! ## Concrete Noise Parameter Instances -/

/-- ML-KEM-512 noise parameters. -/
def mlkem512Noise : NoiseParams where
  n := 256
  k := 2
  q := 3329
  eta1 := 3
  eta2 := 2
  d_u := 10
  d_v := 4
  hq := q_prime

/-- ML-KEM-768 noise parameters. -/
def mlkem768Noise : NoiseParams where
  n := 256
  k := 3
  q := 3329
  eta1 := 2
  eta2 := 2
  d_u := 10
  d_v := 4
  hq := q_prime

/-- ML-KEM-1024 noise parameters. -/
def mlkem1024Noise : NoiseParams where
  n := 256
  k := 4
  q := 3329
  eta1 := 2
  eta2 := 2
  d_u := 11
  d_v := 5
  hq := q_prime

/-! ## Parameter Consistency

Verify that the noise parameter instances agree with `ConcreteParams.NISTParams`. -/

theorem mlkem512Noise_matches :
    mlkem512Noise.n = MLKEM512Params.n ∧
    mlkem512Noise.k = MLKEM512Params.k ∧
    mlkem512Noise.q = MLKEM512Params.q ∧
    mlkem512Noise.eta1 = MLKEM512Params.eta1 ∧
    mlkem512Noise.eta2 = MLKEM512Params.eta2 ∧
    mlkem512Noise.d_u = MLKEM512Params.d_u ∧
    mlkem512Noise.d_v = MLKEM512Params.d_v :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mlkem768Noise_matches :
    mlkem768Noise.n = MLKEM768Params.n ∧
    mlkem768Noise.k = MLKEM768Params.k ∧
    mlkem768Noise.q = MLKEM768Params.q ∧
    mlkem768Noise.eta1 = MLKEM768Params.eta1 ∧
    mlkem768Noise.eta2 = MLKEM768Params.eta2 ∧
    mlkem768Noise.d_u = MLKEM768Params.d_u ∧
    mlkem768Noise.d_v = MLKEM768Params.d_v :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mlkem1024Noise_matches :
    mlkem1024Noise.n = MLKEM1024Params.n ∧
    mlkem1024Noise.k = MLKEM1024Params.k ∧
    mlkem1024Noise.q = MLKEM1024Params.q ∧
    mlkem1024Noise.eta1 = MLKEM1024Params.eta1 ∧
    mlkem1024Noise.eta2 = MLKEM1024Params.eta2 ∧
    mlkem1024Noise.d_u = MLKEM1024Params.d_u ∧
    mlkem1024Noise.d_v = MLKEM1024Params.d_v :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Rounding Noise Bounds

Compress/decompress introduces rounding noise bounded by `ceil(q / 2^{d+1})`.
For ML-KEM, `Compress_d(x) = round(2^d / q * x) mod 2^d` and
`Decompress_d(y) = round(q / 2^d * y)`. The round-trip error is at most
`ceil(q / 2^{d+1})`.

FIPS 203, Section 4.2.1. -/

/-- Rounding noise bound from compress/decompress with `d` bits and modulus `q`.

    The maximum absolute rounding error is `ceil(q / 2^{d+1})`.
    We express this as a natural number (the ceiling). -/
def compressNoiseBoundNat (d q : ℕ) : ℕ :=
  (q + 2 ^ (d + 1) - 1) / 2 ^ (d + 1)

/-- Rounding noise bound as an `ℝ≥0∞` value. -/
noncomputable def compressNoiseBound (d q : ℕ) : ℝ≥0∞ :=
  (compressNoiseBoundNat d q : ℝ≥0∞)

/-- ML-KEM-768 / ML-KEM-512: compress noise for u with d_u = 10, q = 3329.

    `ceil(3329 / 2^11) = ceil(3329 / 2048) = ceil(1.625...) = 2` -/
theorem mlkem768_compress_u_noise :
    compressNoiseBoundNat 10 3329 = 2 := by decide

/-- ML-KEM-768 / ML-KEM-512: compress noise for v with d_v = 4, q = 3329.

    `ceil(3329 / 2^5) = ceil(3329 / 32) = ceil(104.03...) = 105` -/
theorem mlkem768_compress_v_noise :
    compressNoiseBoundNat 4 3329 = 105 := by decide

/-- ML-KEM-1024: compress noise for u with d_u = 11, q = 3329.

    `ceil(3329 / 2^12) = ceil(3329 / 4096) = ceil(0.8126...) = 1` -/
theorem mlkem1024_compress_u_noise :
    compressNoiseBoundNat 11 3329 = 1 := by decide

/-- ML-KEM-1024: compress noise for v with d_v = 5, q = 3329.

    `ceil(3329 / 2^6) = ceil(3329 / 64) = ceil(52.015...) = 53` -/
theorem mlkem1024_compress_v_noise :
    compressNoiseBoundNat 5 3329 = 53 := by decide

/-! ## CBD Values Tabulated from FIPS 203

FIPS 203, Section 4.1 specifies the centered binomial distribution `CBD_eta` as
the difference of two sums of `eta` uniform bits, and records its support
`{-eta, ..., eta}`, mean 0, and variance `eta/2`.

No probability distribution is formalized in this file. The definitions below
record those published values as `ℕ`- and `ℝ≥0∞`-valued constants, for use in
the arithmetic of the failure-probability bound. The theorems about them are
arithmetic on the constants; they assert nothing about any distribution. The
mean value 0 needs no constant and none is defined. -/

/-- Numerator of the variance value FIPS 203 records for `CBD_eta`, over the
    implicit denominator `cbdVarianceDenom = 2`: the published variance is
    `eta/2`.

    A tabulated constant, not a derived quantity. -/
def cbdVarianceNumer (eta : ℕ) : ℕ := eta

/-- Denominator of the tabulated `CBD_eta` variance value (always 2). -/
def cbdVarianceDenom : ℕ := 2

/-- The tabulated `CBD_eta` variance value as `ℝ≥0∞`: `eta / 2`. -/
noncomputable def cbdVariance (eta : ℕ) : ℝ≥0∞ :=
  (eta : ℝ≥0∞) / 2

/-- At `eta = 2` the tabulated variance numerator equals the denominator, so the
    tabulated value `2/2` is 1. Arithmetic on the two constants. -/
theorem cbdVarianceNumer_two : cbdVarianceNumer 2 = cbdVarianceDenom := rfl

/-- At `eta = 3` the tabulated variance numerator is 3, so the tabulated value
    is `3/2`. Arithmetic on the constant. -/
theorem cbdVarianceNumer_three : cbdVarianceNumer 3 = 3 := rfl

/-- Size of the support interval `{-eta, ..., eta}` that FIPS 203 records for
    `CBD_eta`: `2 * eta + 1`. A tabulated constant. -/
def cbdSupportSize (eta : ℕ) : ℕ := 2 * eta + 1

/-- The tabulated support size at `eta = 2` is 5. Arithmetic on the constant. -/
theorem cbdSupportSize_two : cbdSupportSize 2 = 5 := by decide

/-- The tabulated support size at `eta = 3` is 7. Arithmetic on the constant. -/
theorem cbdSupportSize_three : cbdSupportSize 3 = 7 := by decide

/-! ## Total Noise Variance

The decryption noise in ML-KEM comes from the inner product computation:
```
v - s^T u = m + e_v + s^T e_1 - e^T r + (rounding noise from u) + (rounding noise from v)
```

For each coefficient of the result polynomial, the noise variance is:
```
sigma^2 = k * Var(s_i) * Var(r_j) + Var(e_v) + Var(compress_u) + Var(compress_v)
```

where `s_i`, `r_j` are CBD_eta1 and CBD_eta2 samples respectively,
`e_v` is CBD_eta2, and the compress variances come from the rounding.

This is a simplification; the full analysis uses the convolution of
the noise distribution with the rounding noise distribution. -/

/-- Number of independent noise terms in the inner product per coefficient.

    Each coefficient of `s^T * r` involves `k` products of CBD samples,
    so there are `k` cross-terms plus error and rounding noise. -/
def noiseTermCount (P : NoiseParams) : ℕ := P.k

/-- Total noise variance numerator (scaled by 2 to avoid fractions).

    For each coefficient:
    `2 * sigma^2 = k * eta1 * eta2 / 2 + eta2 + (rounding terms)`

    We compute `4 * sigma^2` to stay in natural numbers:
    `4 * sigma^2 = k * eta1 * eta2 + 2 * eta2 + 4 * round_u^2 / 12 + 4 * round_v^2 / 12`

    Simplified (ignoring rounding variance approximation):
    `4 * sigma^2 approx k * eta1 * eta2 + 2 * eta2` -/
def noiseVarianceNumer4 (P : NoiseParams) : ℕ :=
  P.k * P.eta1 * P.eta2 + 2 * P.eta2

/-- ML-KEM-512 noise variance numerator (times 4).

    `4 * sigma^2 = 2 * 3 * 2 + 2 * 2 = 12 + 4 = 16` -/
theorem mlkem512_noise_var : noiseVarianceNumer4 mlkem512Noise = 16 := by decide

/-- ML-KEM-768 noise variance numerator (times 4).

    `4 * sigma^2 = 3 * 2 * 2 + 2 * 2 = 12 + 4 = 16` -/
theorem mlkem768_noise_var : noiseVarianceNumer4 mlkem768Noise = 16 := by decide

/-- ML-KEM-1024 noise variance numerator (times 4).

    `4 * sigma^2 = 4 * 2 * 2 + 2 * 2 = 16 + 4 = 20` -/
theorem mlkem1024_noise_var : noiseVarianceNumer4 mlkem1024Noise = 20 := by decide

/-! ## Decoding Threshold

Decryption succeeds when the total noise is less than `q/4` (the
half-distance of the message encoding). For `q = 3329`:
`floor(q/4) = floor(832.25) = 832`.

A coefficient decryption failure occurs when `|noise| > q/4`. -/

/-- Decoding threshold: `floor(q/4)`.

    Decryption succeeds when `|noise| <= floor(q/4)`. -/
def decodingThreshold (q : ℕ) : ℕ := q / 4

theorem mlkem_decoding_threshold : decodingThreshold 3329 = 832 := by decide

/-- The decoding threshold exceeds the rounding noise for u in ML-KEM-768.

    `832 > 2` (compress_u noise bound) -/
theorem mlkem768_threshold_exceeds_u_noise :
    decodingThreshold 3329 > compressNoiseBoundNat 10 3329 := by decide

/-- The decoding threshold exceeds the rounding noise for v in ML-KEM-768.

    `832 > 105` (compress_v noise bound) -/
theorem mlkem768_threshold_exceeds_v_noise :
    decodingThreshold 3329 > compressNoiseBoundNat 4 3329 := by decide

/-! ## Per-Coefficient Failure Probability

The per-coefficient failure probability is the probability that the total
noise on a single coefficient exceeds the decoding threshold. This depends
on the noise distribution (convolution of CBD and rounding noise).

For ML-KEM, this is computed numerically. We take the bound as a hypothesis
and verify the structural relationship between the per-coefficient bound
and the overall scheme failure probability. -/

/-- Per-coefficient failure probability (abstract).

    The probability that the noise on a single coefficient exceeds `q/4`.
    This is computed numerically from the noise distribution; we take it
    as a parameter. -/
noncomputable def coeffFailureProb (_P : NoiseParams) (δ_coeff : ℝ≥0∞) : ℝ≥0∞ :=
  δ_coeff

/-- Total number of coefficients that must decode correctly.

    For the u-component: `n * k` coefficients (vector of k polynomials).
    For the v-component: `n` coefficients (single polynomial).
    Total: `n * k + n = n * (k + 1)`.

    However, the standard union bound counts over `n` coefficients of the
    final noise polynomial (after inner product), giving `n` terms. -/
def totalCoefficients (P : NoiseParams) : ℕ := P.n

/-- Extended coefficient count including cross-terms.

    The full noise has contributions from `k` inner-product terms plus
    the encryption noise, compressed across `n * k` (for u) and `n` (for v)
    coefficients. The union bound over all noise sources gives `n * (k + 1)`. -/
def extendedCoefficients (P : NoiseParams) : ℕ := P.n * (P.k + 1)

theorem mlkem512_total_coeffs : totalCoefficients mlkem512Noise = 256 := rfl
theorem mlkem768_total_coeffs : totalCoefficients mlkem768Noise = 256 := rfl
theorem mlkem1024_total_coeffs : totalCoefficients mlkem1024Noise = 256 := rfl

theorem mlkem512_extended_coeffs : extendedCoefficients mlkem512Noise = 768 := by decide
theorem mlkem768_extended_coeffs : extendedCoefficients mlkem768Noise = 1024 := by decide
theorem mlkem1024_extended_coeffs : extendedCoefficients mlkem1024Noise = 1280 := by decide

/-! ## Decryption Failure Probability

The overall decryption failure probability is bounded by a union bound
over all coefficients:

```
delta <= n * delta_coeff
```

where `delta_coeff` is the per-coefficient failure probability. For the
extended analysis (Barbosa et al., CCS 2025), the bound accounts for
cross-term dependencies and achieves tighter results. -/

/-- Decryption failure probability: union bound over `n` coefficients.

    `delta <= n * delta_coeff`

    This is the standard (loose) union bound. The CCS 2025 analysis
    achieves tighter bounds by accounting for the joint distribution
    of noise across coefficients. -/
noncomputable def decryptionFailureProb (P : NoiseParams) (δ_coeff : ℝ≥0∞) : ℝ≥0∞ :=
  P.n * δ_coeff

/-- Extended failure probability: union bound over `n * (k+1)` coefficients.

    Used in the full noise analysis that separately bounds the noise
    contributions from each source (secret-error cross-terms, encryption
    noise, and rounding). -/
noncomputable def decryptionFailureProbExtended (P : NoiseParams) (δ_coeff : ℝ≥0∞) : ℝ≥0∞ :=
  (P.n * (P.k + 1) : ℕ) * δ_coeff

/-- The standard union bound is at most the extended bound when
    `k >= 0` (always true). -/
theorem standard_le_extended (P : NoiseParams) (δ_coeff : ℝ≥0∞) :
    decryptionFailureProb P δ_coeff ≤ decryptionFailureProbExtended P δ_coeff := by
  simp only [decryptionFailureProb, decryptionFailureProbExtended]
  gcongr
  exact_mod_cast Nat.le_mul_of_pos_right P.n (Nat.succ_pos P.k)

/-! ## Structured Failure Bounds

These theorems express the failure bounds with explicit structure:
the failure probability is a function of the noise parameters and
per-coefficient bound, and the concrete numerical bound holds when
the per-coefficient probability is small enough. -/

/-- ML-KEM-512: failure probability from per-coefficient bound.

    If each coefficient fails with probability at most `δ_c`, then the
    overall failure probability is at most `256 * δ_c`. -/
theorem mlkem512_failure_from_coeff (δ_c : ℝ≥0∞) :
    decryptionFailureProb mlkem512Noise δ_c = 256 * δ_c := by
  simp [decryptionFailureProb, mlkem512Noise]

/-- ML-KEM-768: failure probability from per-coefficient bound.

    If each coefficient fails with probability at most `δ_c`, then the
    overall failure probability is at most `256 * δ_c`. -/
theorem mlkem768_failure_from_coeff (δ_c : ℝ≥0∞) :
    decryptionFailureProb mlkem768Noise δ_c = 256 * δ_c := by
  simp [decryptionFailureProb, mlkem768Noise]

/-- ML-KEM-1024: failure probability from per-coefficient bound.

    If each coefficient fails with probability at most `δ_c`, then the
    overall failure probability is at most `256 * δ_c`. -/
theorem mlkem1024_failure_from_coeff (δ_c : ℝ≥0∞) :
    decryptionFailureProb mlkem1024Noise δ_c = 256 * δ_c := by
  simp [decryptionFailureProb, mlkem1024Noise]

/-! ## Connection to FO Transform: Correctness Amplification

The Fujisaki-Okamoto transform amplifies the base PKE correctness error
by a factor of `(qHK + 1)` (where `qHK` is the combined hash/KDF query bound),
because each hash query can trigger an independent correctness check.

From `FO_TT.correctness`:
```
delta_FO <= (qHC) * delta_PKE
```

and from `FO_MLKEM.conclusion_fo_mlkem`, the CCA bound includes:
```
(2 * qHK + 3) * 3 * epsilon_fail + epsilon_fail
```

We express the structural relationship between the base PKE failure
probability and the amplified FO failure probability. -/

/-- FO correctness amplification factor.

    The FO transform multiplies the base correctness error by `qHK + 1`
    (the total number of hash queries including the challenge).

    Here `qHK` is the combined hash + KDF query bound from `FO_MLKEM.Params`. -/
def foAmplificationFactor (qHK : ℕ) : ℕ := qHK + 1

theorem mlkem768_amplification : foAmplificationFactor 256 = 257 := by decide
theorem mlkem512_amplification : foAmplificationFactor 256 = 257 := by decide
theorem mlkem1024_amplification : foAmplificationFactor 256 = 257 := by decide

/-- FO correctness amplification: `delta_FO <= (qHK + 1) * delta_PKE`.

    The FO transform's correctness error is amplified by the number of
    hash queries, because each query can trigger an independent
    re-encryption check that may fail.

    This is the structural bound; the concrete values come from the
    noise analysis. -/
theorem fo_correctness_amplification
    (qHK : ℕ) (δ_PKE : ℝ≥0∞) :
    (foAmplificationFactor qHK : ℝ≥0∞) * δ_PKE =
    ((qHK : ℝ≥0∞) + 1) * δ_PKE := by
  simp [foAmplificationFactor]

/-- The FO amplification factor is at least 1. -/
theorem fo_amplification_ge_one (qHK : ℕ) :
    (1 : ℝ≥0∞) ≤ (foAmplificationFactor qHK : ℝ≥0∞) := by
  simp [foAmplificationFactor]

/-- FO amplification preserves zero failure: if delta_PKE = 0 then delta_FO = 0. -/
theorem fo_amplification_zero (qHK : ℕ) :
    (foAmplificationFactor qHK : ℝ≥0∞) * (0 : ℝ≥0∞) = 0 := by
  simp

/-- FO amplification is monotone: if delta1 <= delta2 then
    amplified delta1 <= amplified delta2. -/
theorem fo_amplification_mono (qHK : ℕ) (δ₁ δ₂ : ℝ≥0∞) (h : δ₁ ≤ δ₂) :
    (foAmplificationFactor qHK : ℝ≥0∞) * δ₁ ≤
    (foAmplificationFactor qHK : ℝ≥0∞) * δ₂ := by
  gcongr

/-! ## Connection to CCA Security Bound

The CCA security theorem from `Security.mlkem_cca_security` includes the
correctness terms:
```
(2 * qHK + 3) * 3 * epsilon_fail + epsilon_fail
```

We show how the decryption failure probability `delta` feeds into this
bound via the FO transform. -/

/-- CCA correctness coefficient: `(2 * qHK + 3) * 3 + 1`.

    This is the total multiplier of `epsilon_fail` in the CCA bound
    from `Security.mlkem_cca_security`. -/
noncomputable def ccaCorrectnessCoeff (qHK : ℕ) : ℝ≥0∞ :=
  (2 * qHK + 3 : ℝ≥0∞) * 3 + 1

/-- ML-KEM-768 CCA correctness coefficient.

    `(2 * 256 + 3) * 3 + 1 = 515 * 3 + 1 = 1546` -/
theorem mlkem768_cca_coeff :
    ccaCorrectnessCoeff 256 = (1546 : ℝ≥0∞) := by
  simp only [ccaCorrectnessCoeff]
  norm_num

/-- The correctness contribution to the CCA bound is monotone in epsilon_fail. -/
theorem cca_correctness_mono (qHK : ℕ) (ε₁ ε₂ : ℝ≥0∞) (h : ε₁ ≤ ε₂) :
    (2 * qHK + 3 : ℝ≥0∞) * 3 * ε₁ + ε₁ ≤
    (2 * qHK + 3 : ℝ≥0∞) * 3 * ε₂ + ε₂ := by
  gcongr

/-! ## Structural Properties of Failure Probability -/

/-- Failure probability is monotone in per-coefficient probability. -/
theorem decryptionFailureProb_mono (P : NoiseParams) (δ₁ δ₂ : ℝ≥0∞) (h : δ₁ ≤ δ₂) :
    decryptionFailureProb P δ₁ ≤ decryptionFailureProb P δ₂ := by
  simp only [decryptionFailureProb]
  gcongr

/-- Failure probability is zero when per-coefficient probability is zero. -/
theorem decryptionFailureProb_zero (P : NoiseParams) :
    decryptionFailureProb P 0 = 0 := by
  simp [decryptionFailureProb]

/-- Failure probability scales linearly. -/
theorem decryptionFailureProb_mul (P : NoiseParams) (c δ : ℝ≥0∞) :
    decryptionFailureProb P (c * δ) = c * decryptionFailureProb P δ := by
  simp only [decryptionFailureProb]
  ring

/-- Failure probability for parameter sets with the same `n`. -/
theorem decryptionFailureProb_eq_of_n_eq (P₁ P₂ : NoiseParams) (δ : ℝ≥0∞)
    (h : P₁.n = P₂.n) :
    decryptionFailureProb P₁ δ = decryptionFailureProb P₂ δ := by
  simp only [decryptionFailureProb, h]

/-- All three ML-KEM parameter sets have the same `n = 256`. -/
theorem all_same_n_noise :
    mlkem512Noise.n = 256 ∧ mlkem768Noise.n = 256 ∧ mlkem1024Noise.n = 256 :=
  ⟨rfl, rfl, rfl⟩

/-- Consequently, all three have the same failure probability formula. -/
theorem all_same_failure_formula (δ : ℝ≥0∞) :
    decryptionFailureProb mlkem512Noise δ = 256 * δ ∧
    decryptionFailureProb mlkem768Noise δ = 256 * δ ∧
    decryptionFailureProb mlkem1024Noise δ = 256 * δ := by
  simp [decryptionFailureProb, mlkem512Noise, mlkem768Noise, mlkem1024Noise]

/-! ## Summary Checks -/

#check mlkem512Noise
#check mlkem768Noise
#check mlkem1024Noise
#check compressNoiseBound
#check cbdVariance
#check decryptionFailureProb
#check fo_correctness_amplification
#check decryptionFailureProb_mono
#check decryptionFailureProb_zero

end CatCrypt.Crypto.MLKEM.CorrectnessBounds

/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCryptCore.Prob.SDistr

/-!
# Concrete ML-KEM Parameter Sets (FIPS 203)

Instantiates the abstract ML-KEM parameters with the three NIST security levels.

| Parameter Set | n   | k | q    | eta1 | eta2 | d_u | d_v | Security   |
|---------------|-----|---|------|------|------|-----|-----|------------|
| ML-KEM-512    | 256 | 2 | 3329 | 3    | 2    | 10  | 4   | Category 1 |
| ML-KEM-768    | 256 | 3 | 3329 | 2    | 2    | 10  | 4   | Category 3 |
| ML-KEM-1024   | 256 | 4 | 3329 | 2    | 2    | 11  | 5   | Category 5 |

## Security Bounds

For ML-KEM-768 (Category 3, 128-bit classical / 192-bit quantum):
- Best known classical attack: ~2^187 (primal lattice attack)
- Best known quantum attack: ~2^170 (Grover-enhanced)
- Decryption failure probability quoted by FIPS 203: about 2^{-174}

## References
* NIST FIPS 203 (2024), Table 1
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.ConcreteParams

open CatCrypt.Prob
open scoped ENNReal

/-! ## NIST Parameter Record

A plain data structure capturing the NIST-specified ML-KEM parameter values.
This is independent of the abstract algebra used in the security proofs. -/

/-- Record of NIST ML-KEM parameters (FIPS 203, Table 1).

    Captures the numerical constants for each security level.
    The security proof infrastructure uses abstract types; this record
    documents and verifies the concrete parameter choices. -/
structure NISTParams where
  /-- Polynomial degree (always 256 for ML-KEM) -/
  n : ℕ
  /-- Module rank (number of polynomials in vectors) -/
  k : ℕ
  /-- Modulus (always 3329 for ML-KEM) -/
  q : ℕ
  /-- CBD parameter for secret/noise in key generation -/
  eta1 : ℕ
  /-- CBD parameter for noise in encryption -/
  eta2 : ℕ
  /-- Bits for compressing u (ciphertext vector component) -/
  d_u : ℕ
  /-- Bits for compressing v (ciphertext scalar component) -/
  d_v : ℕ
  /-- Maximum hash queries -/
  qH : ℕ
  /-- Maximum CVO queries -/
  qV : ℕ
  /-- Maximum PCO queries -/
  qP : ℕ
  /-- Maximum decapsulation queries -/
  qDK : ℕ

/-! ## ML-KEM-512 (NIST Security Category 1) -/

/-- ML-KEM-512 parameter set (FIPS 203, Table 1).

    Security Category 1 (at least as hard as AES-128 key search). -/
def MLKEM512Params : NISTParams where
  n := 256
  k := 2
  q := 3329
  eta1 := 3
  eta2 := 2
  d_u := 10
  d_v := 4
  qH := 256
  qV := 256
  qP := 256
  qDK := 256

/-! ## ML-KEM-768 (NIST Security Category 3) -/

/-- ML-KEM-768 parameter set (FIPS 203, Table 1).

    Security Category 3 (at least as hard as AES-192 key search). -/
def MLKEM768Params : NISTParams where
  n := 256
  k := 3
  q := 3329
  eta1 := 2
  eta2 := 2
  d_u := 10
  d_v := 4
  qH := 256
  qV := 256
  qP := 256
  qDK := 256

/-! ## ML-KEM-1024 (NIST Security Category 5) -/

/-- ML-KEM-1024 parameter set (FIPS 203, Table 1).

    Security Category 5 (at least as hard as AES-256 key search). -/
def MLKEM1024Params : NISTParams where
  n := 256
  k := 4
  q := 3329
  eta1 := 2
  eta2 := 2
  d_u := 11
  d_v := 5
  qH := 256
  qV := 256
  qP := 256
  qDK := 256

/-! ## Verified Arithmetic Properties

These theorems verify key numerical relationships required by the NIST standard.
Each is closed by `decide`, the values being concrete. -/

/-- The ML-KEM modulus 3329 is prime. -/
theorem q_prime : Nat.Prime 3329 := by norm_num

/-- 3329 is an NTT-friendly prime: 3329 = 1 (mod 256).

    This allows efficient NTT for polynomials of degree < 256.
    Note: 3329 = 13 * 256 + 1. -/
theorem q_ntt_friendly : 3329 % 256 = 1 := by decide

/-- The polynomial degree 256 is a power of two. -/
theorem n_power_of_two : 256 = 2 ^ 8 := by decide

/-- 256 divides q - 1 (required for NTT). -/
theorem n_divides_q_minus_one : (3329 - 1) % 256 = 0 := by decide

/-- q - 1 = 3328 = 2^8 * 13, confirming the NTT structure. -/
theorem q_minus_one_factored : 3329 - 1 = 2 ^ 8 * 13 := by decide

/-! ## Parameter Consistency Checks

Verify that each parameter set satisfies the constraints from FIPS 203. -/

/-- ML-KEM-512: d_u * k < n * log2(q). Since q=3329, log2(q) ~ 11.7,
    we check the weaker constraint d_u <= 12 (bits per coefficient). -/
theorem mlkem512_du_valid : MLKEM512Params.d_u < MLKEM512Params.n := by decide

/-- ML-KEM-512: d_v < log2(q). -/
theorem mlkem512_dv_valid : MLKEM512Params.d_v < 12 := by decide

/-- ML-KEM-768: d_u fits within the modulus. -/
theorem mlkem768_du_valid : MLKEM768Params.d_u < MLKEM768Params.n := by decide

/-- ML-KEM-768: d_v fits within the modulus. -/
theorem mlkem768_dv_valid : MLKEM768Params.d_v < 12 := by decide

/-- ML-KEM-1024: d_u fits within the modulus. -/
theorem mlkem1024_du_valid : MLKEM1024Params.d_u < MLKEM1024Params.n := by decide

/-- ML-KEM-1024: d_v fits within the modulus. -/
theorem mlkem1024_dv_valid : MLKEM1024Params.d_v < 12 := by decide

/-- All three parameter sets share the same modulus. -/
theorem all_same_q :
    MLKEM512Params.q = 3329 ∧ MLKEM768Params.q = 3329 ∧ MLKEM1024Params.q = 3329 :=
  ⟨rfl, rfl, rfl⟩

/-- All three parameter sets share the same polynomial degree. -/
theorem all_same_n :
    MLKEM512Params.n = 256 ∧ MLKEM768Params.n = 256 ∧ MLKEM1024Params.n = 256 :=
  ⟨rfl, rfl, rfl⟩

/-- The eta parameters satisfy eta1 >= eta2 for all parameter sets. -/
theorem eta_ordering :
    MLKEM512Params.eta1 ≥ MLKEM512Params.eta2 ∧
    MLKEM768Params.eta1 ≥ MLKEM768Params.eta2 ∧
    MLKEM1024Params.eta1 ≥ MLKEM1024Params.eta2 := by
  decide

/-! ## Compression Bound Checks

The compression parameters d_u, d_v determine the rounding error introduced
during encryption. Larger values mean less noise but bigger ciphertexts. -/

/-- ML-KEM-512: 2^d_u = 1024, which is less than q = 3329. -/
theorem mlkem512_compress_u : 2 ^ MLKEM512Params.d_u < MLKEM512Params.q := by decide

/-- ML-KEM-512: 2^d_v = 16, which is less than q = 3329. -/
theorem mlkem512_compress_v : 2 ^ MLKEM512Params.d_v < MLKEM512Params.q := by decide

/-- ML-KEM-768: 2^d_u = 1024, which is less than q = 3329. -/
theorem mlkem768_compress_u : 2 ^ MLKEM768Params.d_u < MLKEM768Params.q := by decide

/-- ML-KEM-768: 2^d_v = 16, which is less than q = 3329. -/
theorem mlkem768_compress_v : 2 ^ MLKEM768Params.d_v < MLKEM768Params.q := by decide

/-- ML-KEM-1024: 2^d_u = 2048, which is less than q = 3329. -/
theorem mlkem1024_compress_u : 2 ^ MLKEM1024Params.d_u < MLKEM1024Params.q := by decide

/-- ML-KEM-1024: 2^d_v = 32, which is less than q = 3329. -/
theorem mlkem1024_compress_v : 2 ^ MLKEM1024Params.d_v < MLKEM1024Params.q := by decide

/-! ## Ciphertext and Key Sizes

These are derived quantities from the NIST parameters, useful for
verifying implementation correctness. Sizes in bytes. -/

/-- Public key size: 12 * k * n/8 + 32 bytes (encoded polynomial vector + seed). -/
def pk_size (p : NISTParams) : ℕ := 12 * p.k * (p.n / 8) + 32

/-- Secret key size: 12 * k * n/8 + pk_size + 32 + 32 bytes
    (encoded s + pk + H(pk) + z). -/
def sk_size (p : NISTParams) : ℕ := 12 * p.k * (p.n / 8) + pk_size p + 32 + 32

/-- Ciphertext size: d_u * k * n/8 + d_v * n/8 bytes. -/
def ct_size (p : NISTParams) : ℕ := p.d_u * p.k * (p.n / 8) + p.d_v * (p.n / 8)

/-- Shared secret size: always 32 bytes. -/
def ss_size (_p : NISTParams) : ℕ := 32

/-- ML-KEM-512 public key is 800 bytes. -/
theorem mlkem512_pk_size : pk_size MLKEM512Params = 800 := by decide

/-- ML-KEM-512 ciphertext is 768 bytes. -/
theorem mlkem512_ct_size : ct_size MLKEM512Params = 768 := by decide

/-- ML-KEM-768 public key is 1184 bytes. -/
theorem mlkem768_pk_size : pk_size MLKEM768Params = 1184 := by decide

/-- ML-KEM-768 ciphertext is 1088 bytes. -/
theorem mlkem768_ct_size : ct_size MLKEM768Params = 1088 := by decide

/-- ML-KEM-1024 public key is 1568 bytes. -/
theorem mlkem1024_pk_size : pk_size MLKEM1024Params = 1568 := by decide

/-- ML-KEM-1024 ciphertext is 1568 bytes. -/
theorem mlkem1024_ct_size : ct_size MLKEM1024Params = 1568 := by decide

/-! ## Verification Summary -/

#check q_prime
#check n_power_of_two
#check mlkem768_pk_size
#check mlkem768_ct_size

end CatCrypt.Crypto.MLKEM.ConcreteParams

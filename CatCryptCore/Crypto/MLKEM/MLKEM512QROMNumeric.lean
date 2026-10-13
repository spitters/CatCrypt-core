/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLKEM512QROMPrf
public import CatCryptCore.Crypto.MLKEM.CollisionSpreadBound

/-!
# ML-KEM-512 in the quantum random-oracle model: the collision term as a number

The quantum IND-CCA bounds of `MLKEM512QROM`, `MLKEM512QROMFinal` stated with the
coin-collision weight `collWeight mlkem512CompressedScheme` in place of the
spreadness term take that weight as a hypothesis `collWeight … ≤ ε`. This module
discharges the hypothesis with the bound `collWeight_mlkem512_le` of
`CollisionSpreadBound` and writes the bound as a power of two: the collision term
of ML-KEM-512 is at most `2⁻¹³⁷`.

## Main definitions

* `collBound` — the value `C(128, 40) · 20^160 · 64^352 / 64^512 + 7^256 / 3329^178`
  bounding the coin-collision weight of ML-KEM-512

## Main results

* `collWeight_le_collBound` — the coin-collision weight of ML-KEM-512 is at most
  `collBound`
* `mlkem512_qindcca_numeric`, `mlkem512_qindcca_corrWorst_numeric`,
  `mlkem512_qindcca_fips_numeric` — the three IND-CCA bounds at the collision term
  `collBound`
* `collBound_le_two_pow` — `collBound ≤ (2 ^ 137)⁻¹`, by monotone steps on the
  factors `C(128, 40) ≤ 2^128`, `5^3 ≤ 2^7`, `7 ≤ 2^3` and `2^11 ≤ 3329`
* `collWeight_le_two_pow` — the coin-collision weight of ML-KEM-512 is at most
  `(2 ^ 137)⁻¹`
* `mlkem512_qindcca_fips_two_pow` — the FIPS 203 IND-CCA bound at the collision
  term `(2 ^ 137)⁻¹`
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Crypto.MLKEM.MLKEM512QROMNumeric

open CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.MLKEM.FIPS203QROMQuantumMLWE
open MLKEM512Instance (mlkem512Params)
open CompressedPKE (MLKEM512CT mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)
open CorrectnessBounds (decryptionFailureProb mlkem512Noise)
open CollisionSpread (collWeight_mlkem512_le)
open MLKEM512QROM (mlkem512_qindcca_coll)
open MLKEM512QROMFinal (qMLWEWorstBound Bytes32 polyG polyJ polyH polyT
  mlkem512_qindcca_corrWorst_coll mlkem512_qindcca_fips_coll)

/-! ## The bound on the coin-collision weight -/

/-- The bound `C(128, 40) · 20^160 · 64^352 / 64^512 + 7^256 / 3329^178` on the
coin-collision weight of ML-KEM-512. -/
def collBound : ℝ≥0∞ :=
  (Nat.choose 128 40 * (20 ^ 160 * 64 ^ 352) : ℝ≥0∞) / 64 ^ 512 + (7 ^ 256 : ℝ≥0∞) / 3329 ^ 178

/-- The coin-collision weight of ML-KEM-512 is at most `collBound`. -/
theorem collWeight_le_collBound : collWeight mlkem512CompressedScheme ≤ collBound :=
  collWeight_mlkem512_le

/-! ## The IND-CCA bounds at the collision term `collBound` -/

section Worst

variable {m₁ m₂ n w q k c a : ℕ} {K Hash Z : Type} [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [DecidableEq Hash]
  (hpk : PK mlkem512Params.toBasic → Hash) (eG : (mlkem512Params.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × MLKEM512CT) ≃ Fin m₂) (eKR : (K × mlkem512Params.Seed) ≃ Fin n)
  (eC : MLKEM512CT ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c] [NeZero a] [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]

open scoped Classical in
/-- `MLKEM512QROM.mlkem512_qindcca_coll` at the collision term `collBound`. -/
theorem mlkem512_qindcca_numeric (PG : PolyData (Fin m₁) (Fin n))
    (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData MLKEM512CT K)
    (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K) (δ_c : ℝ≥0∞)
    (hWorst : mlkem512CompressedScheme.corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) true +
            decryptionFailureProb mlkem512Noise δ_c))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) * decryptionFailureProb mlkem512Noise δ_c ^ (1 / 2 : ℝ) +
          (decryptionFailureProb mlkem512Noise δ_c + collBound) +
          8 * (flatQ q k q : ℝ≥0∞) * decryptionFailureProb mlkem512Noise δ_c ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) false +
            decryptionFailureProb mlkem512Noise δ_c))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) * decryptionFailureProb mlkem512Noise δ_c ^ (1 / 2 : ℝ) +
          decryptionFailureProb mlkem512Noise δ_c +
          8 * (flatQ q k q : ℝ≥0∞) * decryptionFailureProb mlkem512Noise δ_c ^ (1 / 2 : ℝ))) :=
  mlkem512_qindcca_coll hpk eG eJ eKR eC eKa PG PJ PH PT A δ_c hWorst collBound
    collWeight_le_collBound

open scoped Classical in
/-- `MLKEM512QROMFinal.mlkem512_qindcca_corrWorst_coll` at the collision term
`collBound`. -/
theorem mlkem512_qindcca_corrWorst_numeric (PG : PolyData (Fin m₁) (Fin n))
    (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData MLKEM512CT K)
    (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) true +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          (mlkem512CompressedScheme.corrWorst + collBound) +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) false +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          mlkem512CompressedScheme.corrWorst +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ))) :=
  mlkem512_qindcca_corrWorst_coll hpk eG eJ eKR eC eKa PG PJ PH PT A collBound
    collWeight_le_collBound

end Worst

section FIPS

variable {m₁ m₂ n w q k c a : ℕ}

open scoped Classical in
/-- `MLKEM512QROMFinal.mlkem512_qindcca_fips_coll` at the collision term `collBound`. -/
theorem mlkem512_qindcca_fips_numeric (hpk : PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eKR : (Bytes32 × mlkem512Params.Seed) ≃ Fin n) (eC : MLKEM512CT ≃ Fin c)
    (eKa : Bytes32 ≃ Fin a) [NeZero n] [NeZero c] [NeZero a] [NeZero (flatQ q k q)]
    [NeZero (m₁ + m₂)]
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT Bytes32) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa (polyG eG eKR) (polyJ eJ eKR) polyH
              (polyT eKR) (nfKEM A) true +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          (mlkem512CompressedScheme.corrWorst + collBound) +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa (polyG eG eKR) (polyJ eJ eKR) polyH
              (polyT eKR) (nfKEM A) false +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((2 ^ 256 : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          mlkem512CompressedScheme.corrWorst +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ))) :=
  mlkem512_qindcca_fips_coll hpk eG eJ eKR eC eKa A collBound collWeight_le_collBound

end FIPS

/-! ## The bound as a power of two -/

/-- A quotient whose numerator is at most `2 ^ m` and whose denominator is at least
`2 ^ (m + k)` is at most `(2 ^ k)⁻¹`. -/
theorem div_le_inv_two_pow {x y : ℝ≥0∞} (m k : ℕ) (hx : x ≤ 2 ^ m) (hy : 2 ^ (m + k) ≤ y) :
    x / y ≤ (2 ^ k)⁻¹ := by
  have h0 : ((2 : ℝ≥0∞) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : ((2 : ℝ≥0∞) ^ m) ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc x / y ≤ 2 ^ m / 2 ^ (m + k) := ENNReal.div_le_div hx hy
    _ = (2 ^ k)⁻¹ := by
      rw [pow_add, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), mul_comm,
        ← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul]

/-- `(2 ^ (k + 1))⁻¹ + (2 ^ (k + 1))⁻¹ = (2 ^ k)⁻¹`. -/
theorem inv_two_pow_succ_add_self (k : ℕ) :
    ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ + (2 ^ (k + 1))⁻¹ = (2 ^ k)⁻¹ := by
  have h0 : ((2 : ℝ≥0∞) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : ((2 : ℝ≥0∞) ^ k) ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [← two_mul, pow_succ, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), mul_comm ((2 : ℝ≥0∞) ^ k)⁻¹,
    ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- `5 ^ 160 ≤ 2 ^ 374`, from `5 ^ 3 ≤ 2 ^ 7` and `5 ≤ 2 ^ 3`. -/
theorem five_pow_le : (5 : ℝ≥0∞) ^ 160 ≤ 2 ^ 374 := by
  have h125 : (5 : ℝ≥0∞) ^ 3 ≤ 2 ^ 7 := by norm_num
  have h5 : (5 : ℝ≥0∞) ≤ 2 ^ 3 := by norm_num
  calc (5 : ℝ≥0∞) ^ 160 = (5 ^ 3) ^ 53 * 5 := by rw [← pow_mul, ← pow_succ]
    _ ≤ (2 ^ 7) ^ 53 * 2 ^ 3 := mul_le_mul' (pow_le_pow_left₀ zero_le h125 53) h5
    _ = 2 ^ 374 := by rw [← pow_mul, ← pow_add]

/-- `20 ^ 160 ≤ 2 ^ 694`, from `20 = 2 ^ 2 · 5` and `five_pow_le`. -/
theorem twenty_pow_le : (20 : ℝ≥0∞) ^ 160 ≤ 2 ^ 694 := by
  calc (20 : ℝ≥0∞) ^ 160 = 2 ^ 320 * 5 ^ 160 := by
        rw [show (20 : ℝ≥0∞) = 2 ^ 2 * 5 by norm_num, mul_pow, ← pow_mul]
    _ ≤ 2 ^ 320 * 2 ^ 374 := mul_le_mul' le_rfl five_pow_le
    _ = 2 ^ 694 := by rw [← pow_add]

/-- `64 ^ n = 2 ^ (6 n)`. -/
theorem sixtyfour_pow (n : ℕ) : (64 : ℝ≥0∞) ^ n = 2 ^ (6 * n) := by
  rw [pow_mul]; norm_num

/-- The first summand of `collBound` is at most `(2 ^ 138)⁻¹`. -/
theorem collBound_first_le :
    (Nat.choose 128 40 * (20 ^ 160 * 64 ^ 352) : ℝ≥0∞) / 64 ^ 512 ≤ (2 ^ 138)⁻¹ := by
  have hC : ((Nat.choose 128 40 : ℕ) : ℝ≥0∞) ≤ 2 ^ 128 := by
    have h := (Nat.cast_le (α := ℝ≥0∞)).mpr (Nat.choose_le_two_pow 128 40)
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  generalize Nat.choose 128 40 = C at hC ⊢
  have h64 : (64 : ℝ≥0∞) ^ 352 ≤ 2 ^ (6 * 352) := (sixtyfour_pow 352).le
  refine div_le_inv_two_pow (128 + (694 + 6 * 352)) 138 ?_ ?_
  · rw [pow_add, pow_add]
    exact mul_le_mul' hC (mul_le_mul' twenty_pow_le h64)
  · rw [sixtyfour_pow]

/-- The second summand of `collBound` is at most `(2 ^ 138)⁻¹`. -/
theorem collBound_second_le : (7 ^ 256 : ℝ≥0∞) / 3329 ^ 178 ≤ (2 ^ 138)⁻¹ := by
  have h7 : (7 : ℝ≥0∞) ≤ 2 ^ 3 := by norm_num
  have h3329 : (2 : ℝ≥0∞) ^ 11 ≤ 3329 := by norm_num
  refine div_le_inv_two_pow (3 * 256) 138 ?_ ?_
  · rw [pow_mul]
    exact pow_le_pow_left₀ zero_le h7 256
  · calc (2 : ℝ≥0∞) ^ (3 * 256 + 138) ≤ 2 ^ (11 * 178) :=
        pow_le_pow_right₀ one_le_two (by norm_num)
      _ = (2 ^ 11) ^ 178 := pow_mul _ _ _
      _ ≤ 3329 ^ 178 := pow_le_pow_left₀ zero_le h3329 178

/-- `collBound ≤ (2 ^ 137)⁻¹`. -/
theorem collBound_le_two_pow : collBound ≤ (2 ^ 137 : ℝ≥0∞)⁻¹ := by
  unfold collBound
  exact (add_le_add collBound_first_le collBound_second_le).trans
    (inv_two_pow_succ_add_self 137).le

/-- The coin-collision weight of ML-KEM-512 is at most `(2 ^ 137)⁻¹`. -/
theorem collWeight_le_two_pow : collWeight mlkem512CompressedScheme ≤ (2 ^ 137 : ℝ≥0∞)⁻¹ :=
  collWeight_le_collBound.trans collBound_le_two_pow

section FIPSTwoPow

variable {m₁ m₂ n w q k c a : ℕ}

open scoped Classical in
/-- `mlkem512_qindcca_fips_numeric` at the collision term `(2 ^ 137)⁻¹`.

References: the bound is of the FO⊥̸ shape of Hövelmanns, Kiltz, Schäge, Unruh,
"Generic authenticated key exchange in the quantum random oracle model", PKC
2020, ePrint 2018/928, and Bindel, Hamburg, Hövelmanns, Hülsing, Persichetti,
"Tighter proofs of CCA security in the quantum random oracle model", TCC 2019,
ePrint 2019/590, derived from the semi-classical one-way-to-hiding theorem of
Ambainis, Hamburg, Unruh, "Quantum security proofs using semi-classical
oracles", CRYPTO 2019, ePrint 2018/904; the KEM is that of NIST, FIPS 203,
"Module-Lattice-Based Key-Encapsulation Mechanism Standard", 2024. -/
theorem mlkem512_qindcca_fips_two_pow (hpk : PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eKR : (Bytes32 × mlkem512Params.Seed) ≃ Fin n) (eC : MLKEM512CT ≃ Fin c)
    (eKa : Bytes32 ≃ Fin a) [NeZero n] [NeZero c] [NeZero a] [NeZero (flatQ q k q)]
    [NeZero (m₁ + m₂)]
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT Bytes32) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa (polyG eG eKR) (polyJ eJ eKR) polyH
              (polyT eKR) (nfKEM A) true +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          (mlkem512CompressedScheme.corrWorst + (2 ^ 137 : ℝ≥0∞)⁻¹) +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa (polyG eG eKR) (polyJ eJ eKR) polyH
              (polyT eKR) (nfKEM A) false +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((2 ^ 256 : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          mlkem512CompressedScheme.corrWorst +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ))) :=
  mlkem512_qindcca_fips_coll hpk eG eJ eKR eC eKa A _ collWeight_le_two_pow

end FIPSTwoPow

end CatCrypt.Crypto.MLKEM.MLKEM512QROMNumeric

end

end

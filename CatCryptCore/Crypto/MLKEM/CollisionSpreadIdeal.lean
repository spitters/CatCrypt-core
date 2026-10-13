/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLKEM512QROMNumeric

/-!
# ML-KEM-512 with `PRF_η` as a random oracle: the collision term as a number

The quantum IND-CCA bounds `mlkem512_qindcca_prf_coll` and
`mlkem512_qindcca_prf_worst_coll` of `MLKEM512QROMPrf` carry the coin-collision
weight of the scheme with uniform noise rows and the XOF matrix,
`collWeight (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK)`. That
scheme encrypts as `mlkem512CompressedScheme` does (the row `ρ` enters through the
seed `eE ρ`, which is uniform when `ρ` is), and generates keys from the matrix
`e (xofMatrix H)` in place of a uniform matrix. Its collision weight is therefore
that of `mlkem512CompressedScheme` up to the XOF hop `xofHop`, and the bound
`collBound` of `MLKEM512QROMNumeric` applies with the additive term `xofHop`.

## Main results

* `collProb_idealScheme_eq` — at every public key and message, the collision
  probability of the scheme with uniform noise rows is that of
  `mlkem512CompressedScheme`
* `collWeight_idealScheme_le_collWeight` — the coin-collision weight of the scheme
  with the XOF matrix is at most that of `mlkem512CompressedScheme` plus `xofHop`
* `collWeight_idealScheme_le`, `collWeight_idealScheme_le_two_pow` — the same weight
  is at most `collBound + xofHop` and at most `(2 ^ 137)⁻¹ + xofHop`
* `mlkem512_qindcca_prf_numeric`, `mlkem512_qindcca_prf_worst_numeric` — the two
  IND-CCA bounds at the collision term `3 / 2^256 + collBound + xofHop`
* `mlkem512_qindcca_prf_two_pow`, `mlkem512_qindcca_prf_worst_two_pow` — the same
  bounds at the collision term `3 / 2^256 + (2 ^ 137)⁻¹ + xofHop`
* `xofHop_le_two_pow` — `xofHop ≤ (2 ^ 170)⁻¹`
* `prfCollTerm_le_two_pow` — the collision term `3 / 2^256 + (2 ^ 137)⁻¹ + xofHop` is
  at most `(2 ^ 136)⁻¹`
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Crypto.MLKEM.CollisionSpreadIdeal

open CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.MLKEM.PRFOracle (avg)
open CatCrypt.Crypto.MLKEM.PRFAuxHop (prfScheme)
open CatCrypt.Crypto.MLKEM.PRFKEMChain (qINDCCAAdvantageF)
open CatCrypt.Crypto.MLKEM.PRFMLWE (owTermStd)
open CatCrypt.Quantum.QROM.PRFChain (chainBound chainBound_mono_all)
open CatCrypt.Crypto.MLKEM.PRFBadTableKeyed (idealScheme)
open CatCrypt.Crypto.MLKEM.PRFCoinWeak (collWeight_idealScheme)
open CatCrypt.Crypto.MLKEM.XOFMatrix (Family)
open MLKEM512Instance (mlkem512Params)
open CompressedPKE (MLKEM512CT mlkem512Compress mlkem512Decompress mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)
open CorrectnessBounds (decryptionFailureProb mlkem512Noise)
open CatCrypt.Crypto.MLKEM.PRFInstance512 (Row prfN prfM eD512 eKR512 eK enc512 B512 S512
  avg_enc512 sum_inv_mul_le_one)
open CatCrypt.Crypto.MLKEM.MLKEM512QROMFinal (Bytes32)
open CatCrypt.Crypto.MLKEM.MLKEM512QROMPrf (kgX xofHop kgX_close polyGp polyJp polyHp polyTp
  polyFp owTermWorst mlkem512_qindcca_prf_coll mlkem512_qindcca_prf_worst_coll)
open CatCrypt.Crypto.MLKEM.MLKEM512QROMNumeric (collBound collWeight_le_collBound
  collBound_le_two_pow div_le_inv_two_pow inv_two_pow_succ_add_self)

/-! ## The collision weight of the scheme with uniform noise rows -/

section Weight

variable (e : XOFMatrix.Mat 2 ≃ B512.Mat)

/-- The collision probability of the scheme with uniform noise rows at a public key
and a message is that of `mlkem512CompressedScheme`: the encryption-noise row
enters through the seed `eE ρ`, which is uniform when the row is. -/
theorem collProb_idealScheme_eq (pk : PK mlkem512Params.toBasic) (m : mlkem512Params.PT) :
    collProb (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK) pk m =
      collProb mlkem512CompressedScheme pk m := by
  change avg (fun w : Row => avg fun w' : Row =>
      if enc512 pk m w' = enc512 pk m w then (1 : ℝ≥0∞) else 0) =
    avg fun r : mlkem512Params.Seed => avg fun r' : mlkem512Params.Seed =>
      if S512.enc pk m r' = S512.enc pk m r then (1 : ℝ≥0∞) else 0
  rw [avg_enc512 pk m
    (fun c => avg fun w' : Row => if enc512 pk m w' = c then (1 : ℝ≥0∞) else 0)]
  refine congrArg avg (funext fun r => ?_)
  exact avg_enc512 pk m (fun c' => if c' = S512.enc pk m r then (1 : ℝ≥0∞) else 0)

/-- The collision probability of a scheme is at most one. -/
theorem collProb_le_one {PK SK M C R : Type} [Fintype M] [Nonempty M] [Fintype R] [Nonempty R]
    [DecidableEq C] (P : Scheme PK SK M C R) (pk : PK) (m : M) : collProb P pk m ≤ 1 := by
  unfold collProb
  exact sum_inv_mul_le_one fun r => sum_inv_mul_le_one fun r' => by split_ifs <;> simp

/-- The coin-collision weight of the scheme with uniform noise rows and the XOF
matrix is the average, over a uniform XOF family and a uniform key-noise row, of the
message-averaged collision probability of `mlkem512CompressedScheme` at the generated
public key. -/
theorem collWeight_idealScheme_eq :
    collWeight (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK) =
      avg fun p : Family 2 280 × Row => ∑ m : mlkem512Params.PT,
        (Fintype.card mlkem512Params.PT : ℝ≥0∞)⁻¹ *
          collProb mlkem512CompressedScheme (kgX e p.1 (eK p.2)).1 m := by
  classical
  rw [collWeight_idealScheme]
  refine congrArg avg (funext fun p => Finset.sum_congr rfl fun m _ => congrArg _ ?_)
  exact collProb_idealScheme_eq e (kgX e p.1 (eK p.2)).1 m

/-- **The XOF hop on the collision weight.** The coin-collision weight of the scheme
with uniform noise rows and the XOF matrix is at most that of
`mlkem512CompressedScheme` plus `xofHop`. -/
theorem collWeight_idealScheme_le_collWeight :
    collWeight (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK) ≤
      collWeight mlkem512CompressedScheme + xofHop := by
  rw [collWeight_idealScheme_eq]
  have hg : ∀ pk : PK mlkem512Params.toBasic, (∑ m : mlkem512Params.PT,
      (Fintype.card mlkem512Params.PT : ℝ≥0∞)⁻¹ * collProb mlkem512CompressedScheme pk m) ≤ 1 :=
    fun pk => sum_inv_mul_le_one fun m => collProb_le_one _ _ _
  refine (kgX_close e (fun pk => ∑ m : mlkem512Params.PT,
    (Fintype.card mlkem512Params.PT : ℝ≥0∞)⁻¹ * collProb mlkem512CompressedScheme pk m) hg).1.trans
    (add_le_add (le_of_eq ?_) le_rfl)
  rw [collWeight, tsum_fintype]
  rfl

/-- The coin-collision weight of the scheme with uniform noise rows and the XOF
matrix is at most `collBound + xofHop`. -/
theorem collWeight_idealScheme_le :
    collWeight (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK) ≤
      collBound + xofHop :=
  (collWeight_idealScheme_le_collWeight e).trans (add_le_add collWeight_le_collBound le_rfl)

/-- The coin-collision weight of the scheme with uniform noise rows and the XOF
matrix is at most `(2 ^ 137)⁻¹ + xofHop`. -/
theorem collWeight_idealScheme_le_two_pow :
    collWeight (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK) ≤
      (2 ^ 137 : ℝ≥0∞)⁻¹ + xofHop :=
  (collWeight_idealScheme_le e).trans (add_le_add collBound_le_two_pow le_rfl)

end Weight

/-! ## The IND-CCA bounds at the collision term `collBound + xofHop` -/

section Bounds

variable {m₁ m₂ w q k c a : ℕ}

open scoped Classical in
/-- `MLKEM512QROMPrf.mlkem512_qindcca_prf_coll` at the collision term
`3 / 2^256 + collBound + xofHop`. -/
theorem mlkem512_qindcca_prf_numeric (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (hpk : PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eC : MLKEM512CT ≃ Fin c) (eKa : Bytes32 ≃ Fin a) [NeZero c] [NeZero a]
    [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]
    (A : KEMQAdv (m₁ + m₂) prfM prfN w q k c a (PK mlkem512Params.toBasic) MLKEM512CT Bytes32) :
    (avg fun F : Fin prfM → Fin prfN =>
      qINDCCAAdvantageF (prfScheme eD512 (kgX e) enc512 mlkem512CompressedScheme.dec eK id F)
        hpk eG eJ eKR512 eC eKa F A) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (6 * (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK).corrWorst +
          514 / 2 ^ 256 + 2 ^ 256 * 2⁻¹ ^ 512)
        (3 * (2 ^ 256)⁻¹ + (collBound + xofHop))
        (2 ^ 256)⁻¹
        (owTermStd mlkem512Params mlkem512Compress mlkem512Decompress eD512 (kgX e) enc512
            mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG) (polyJp eJ)
            polyHp polyTp polyFp true A + 2 * xofHop)
        (owTermStd mlkem512Params mlkem512Compress mlkem512Decompress eD512 (kgX e) enc512
            mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG) (polyJp eJ)
            polyHp polyTp polyFp false A + 2 * xofHop) :=
  (mlkem512_qindcca_prf_coll e hpk eG eJ eC eKa A).trans
    (chainBound_mono_all _ _ _ le_rfl (add_le_add le_rfl (collWeight_idealScheme_le e))
      le_rfl le_rfl)

open scoped Classical in
/-- `MLKEM512QROMPrf.mlkem512_qindcca_prf_worst_coll` at the collision term
`3 / 2^256 + collBound + xofHop`. -/
theorem mlkem512_qindcca_prf_worst_numeric (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (hpk : PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eC : MLKEM512CT ≃ Fin c) (eKa : Bytes32 ≃ Fin a) [NeZero c] [NeZero a]
    [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]
    (A : KEMQAdv (m₁ + m₂) prfM prfN w q k c a (PK mlkem512Params.toBasic) MLKEM512CT Bytes32)
    (δ_c : ℝ≥0∞)
    (hWorst : mlkem512CompressedScheme.corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c) :
    (avg fun F : Fin prfM → Fin prfN =>
      qINDCCAAdvantageF (prfScheme eD512 (kgX e) enc512 mlkem512CompressedScheme.dec eK id F)
        hpk eG eJ eKR512 eC eKa F A) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (6 * (decryptionFailureProb mlkem512Noise δ_c + xofHop) +
          514 / 2 ^ 256 + 2 ^ 256 * 2⁻¹ ^ 512)
        (3 * (2 ^ 256)⁻¹ + (collBound + xofHop))
        (2 ^ 256)⁻¹
        (owTermWorst e hpk eG eJ eC eKa A δ_c true)
        (owTermWorst e hpk eG eJ eC eKa A δ_c false) :=
  (mlkem512_qindcca_prf_worst_coll e hpk eG eJ eC eKa A δ_c hWorst).trans
    (chainBound_mono_all _ _ _ le_rfl (add_le_add le_rfl (collWeight_idealScheme_le e))
      le_rfl le_rfl)

open scoped Classical in
/-- `mlkem512_qindcca_prf_numeric` at the collision term
`3 / 2^256 + (2 ^ 137)⁻¹ + xofHop`.

References: the bound is of the FO⊥̸ shape of Hövelmanns, Kiltz, Schäge, Unruh,
"Generic authenticated key exchange in the quantum random oracle model", PKC
2020, ePrint 2018/928, and Bindel, Hamburg, Hövelmanns, Hülsing, Persichetti,
"Tighter proofs of CCA security in the quantum random oracle model", TCC 2019,
ePrint 2019/590, derived from the semi-classical one-way-to-hiding theorem of
Ambainis, Hamburg, Unruh, "Quantum security proofs using semi-classical
oracles", CRYPTO 2019, ePrint 2018/904; the KEM is that of NIST, FIPS 203,
"Module-Lattice-Based Key-Encapsulation Mechanism Standard", 2024. The Kyber
analysis of Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler,
Stehlé, "CRYSTALS-Kyber: a CCA-secure module-lattice-based KEM", EuroS&P 2018,
makes a PRF assumption on the noise sampler; the random-oracle model of
`prfScheme` is the stronger idealisation. -/
theorem mlkem512_qindcca_prf_two_pow (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (hpk : PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eC : MLKEM512CT ≃ Fin c) (eKa : Bytes32 ≃ Fin a) [NeZero c] [NeZero a]
    [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]
    (A : KEMQAdv (m₁ + m₂) prfM prfN w q k c a (PK mlkem512Params.toBasic) MLKEM512CT Bytes32) :
    (avg fun F : Fin prfM → Fin prfN =>
      qINDCCAAdvantageF (prfScheme eD512 (kgX e) enc512 mlkem512CompressedScheme.dec eK id F)
        hpk eG eJ eKR512 eC eKa F A) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (6 * (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK).corrWorst +
          514 / 2 ^ 256 + 2 ^ 256 * 2⁻¹ ^ 512)
        (3 * (2 ^ 256)⁻¹ + ((2 ^ 137 : ℝ≥0∞)⁻¹ + xofHop))
        (2 ^ 256)⁻¹
        (owTermStd mlkem512Params mlkem512Compress mlkem512Decompress eD512 (kgX e) enc512
            mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG) (polyJp eJ)
            polyHp polyTp polyFp true A + 2 * xofHop)
        (owTermStd mlkem512Params mlkem512Compress mlkem512Decompress eD512 (kgX e) enc512
            mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG) (polyJp eJ)
            polyHp polyTp polyFp false A + 2 * xofHop) :=
  (mlkem512_qindcca_prf_numeric e hpk eG eJ eC eKa A).trans
    (chainBound_mono_all _ _ _ le_rfl
      (add_le_add le_rfl (add_le_add collBound_le_two_pow le_rfl)) le_rfl le_rfl)

open scoped Classical in
/-- `mlkem512_qindcca_prf_worst_numeric` at the collision term
`3 / 2^256 + (2 ^ 137)⁻¹ + xofHop`. -/
theorem mlkem512_qindcca_prf_worst_two_pow (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (hpk : PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eC : MLKEM512CT ≃ Fin c) (eKa : Bytes32 ≃ Fin a) [NeZero c] [NeZero a]
    [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]
    (A : KEMQAdv (m₁ + m₂) prfM prfN w q k c a (PK mlkem512Params.toBasic) MLKEM512CT Bytes32)
    (δ_c : ℝ≥0∞)
    (hWorst : mlkem512CompressedScheme.corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c) :
    (avg fun F : Fin prfM → Fin prfN =>
      qINDCCAAdvantageF (prfScheme eD512 (kgX e) enc512 mlkem512CompressedScheme.dec eK id F)
        hpk eG eJ eKR512 eC eKa F A) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (6 * (decryptionFailureProb mlkem512Noise δ_c + xofHop) +
          514 / 2 ^ 256 + 2 ^ 256 * 2⁻¹ ^ 512)
        (3 * (2 ^ 256)⁻¹ + ((2 ^ 137 : ℝ≥0∞)⁻¹ + xofHop))
        (2 ^ 256)⁻¹
        (owTermWorst e hpk eG eJ eC eKa A δ_c true)
        (owTermWorst e hpk eG eJ eC eKa A δ_c false) :=
  (mlkem512_qindcca_prf_worst_numeric e hpk eG eJ eC eKa A δ_c hWorst).trans
    (chainBound_mono_all _ _ _ le_rfl
      (add_le_add le_rfl (add_le_add collBound_le_two_pow le_rfl)) le_rfl le_rfl)

end Bounds

/-! ## The XOF hop and the collision term as powers of two -/

section TwoPow

/-- `767 ^ 305 ≤ 2 ^ 2928`, from `767 ^ 5 ≤ 2 ^ 48`. -/
theorem sevenSixtySeven_pow_le : (767 : ℝ≥0∞) ^ 305 ≤ 2 ^ 2928 := by
  have h5 : (767 : ℝ≥0∞) ^ 5 ≤ 2 ^ 48 := by norm_num
  calc (767 : ℝ≥0∞) ^ 305 = (767 ^ 5) ^ 61 := by rw [← pow_mul]
    _ ≤ (2 ^ 48) ^ 61 := pow_le_pow_left₀ zero_le h5 61
    _ = 2 ^ 2928 := by rw [← pow_mul]

/-- `xofHop ≤ (2 ^ 170)⁻¹`, from `C(560, 255) ≤ 2 ^ 560`, `767 ^ 305 ≤ 2 ^ 2928` and
`4096 ^ 305 = 2 ^ 3660`. -/
theorem xofHop_le_two_pow : xofHop ≤ (2 ^ 170 : ℝ≥0∞)⁻¹ := by
  have hC : ((Nat.choose 560 255 : ℕ) : ℝ≥0∞) ≤ 2 ^ 560 := by
    exact_mod_cast Nat.choose_le_two_pow 560 255
  unfold xofHop
  show ((4 : ℕ) : ℝ≥0∞) * ((Nat.choose 560 255 : ℕ) * (767 / 4096) ^ 305) ≤ _
  generalize Nat.choose 560 255 = C at hC ⊢
  rw [show ((4 : ℕ) : ℝ≥0∞) = 2 ^ 2 by norm_num, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow,
    ← div_eq_mul_inv, ← mul_div_assoc, ← mul_div_assoc, ← mul_assoc]
  refine div_le_inv_two_pow (2 + 560 + 2928) 170 ?_ ?_
  · rw [pow_add, pow_add]
    exact mul_le_mul' (mul_le_mul' le_rfl hC) sevenSixtySeven_pow_le
  · rw [show (4096 : ℝ≥0∞) = 2 ^ 12 by norm_num, ← pow_mul]

/-- The collision term `3 / 2^256 + (2 ^ 137)⁻¹ + xofHop` of
`mlkem512_qindcca_prf_two_pow` is at most `(2 ^ 136)⁻¹`. -/
theorem prfCollTerm_le_two_pow :
    3 * (2 ^ 256 : ℝ≥0∞)⁻¹ + ((2 ^ 137 : ℝ≥0∞)⁻¹ + xofHop) ≤ (2 ^ 136 : ℝ≥0∞)⁻¹ := by
  have h3 : 3 * (2 ^ 256 : ℝ≥0∞)⁻¹ ≤ (2 ^ 138)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact div_le_inv_two_pow 2 138 (by norm_num) (pow_le_pow_right₀ one_le_two (by norm_num))
  have hx : xofHop ≤ (2 ^ 138 : ℝ≥0∞)⁻¹ :=
    xofHop_le_two_pow.trans (ENNReal.inv_le_inv.2 (pow_le_pow_right₀ one_le_two (by norm_num)))
  calc 3 * (2 ^ 256 : ℝ≥0∞)⁻¹ + ((2 ^ 137 : ℝ≥0∞)⁻¹ + xofHop)
      ≤ (2 ^ 138)⁻¹ + ((2 ^ 137)⁻¹ + (2 ^ 138)⁻¹) := add_le_add h3 (add_le_add le_rfl hx)
    _ = (2 ^ 137)⁻¹ + ((2 ^ 138)⁻¹ + (2 ^ 138)⁻¹) := add_left_comm _ _ _
    _ = (2 ^ 136)⁻¹ := by rw [inv_two_pow_succ_add_self 137, inv_two_pow_succ_add_self 136]

end TwoPow

end CatCrypt.Crypto.MLKEM.CollisionSpreadIdeal

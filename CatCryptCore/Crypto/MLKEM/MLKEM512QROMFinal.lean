/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLKEM512QROM

/-!
# ML-KEM-512 in the quantum random-oracle model: worst-case failure term and byte types

Two forms of the bound of the quantum IND-CCA theorem
`MLKEM512QROM.mlkem512_qindcca_coll`, proved from the same hop chain rather than
from that theorem: the decryption-failure terms written as the correctness error
`corrWorst`, and the polynomial-oracle data constructed at FIPS 203's 32-byte
types.

## Main definitions

* `qMLWEWorstBound` — the module-LWE term `qMLWEStdBound` with the average
  decryption error `corrErr` replaced by the worst-case correctness error
  `corrWorst`.
* `Bytes32` — 32-byte strings, the FIPS 203 type of shared keys, of `H(ek)` and
  of the implicit-rejection seed `z`.
* `polyG`, `polyJ`, `polyH`, `polyT` — polynomial-oracle data for the four
  auxiliary tables over `GaloisField 2 6400`.

## Main results

* `corrErr_le_corrWorst` — the average decryption error over keys, messages and
  coins is at most the average over keys of the largest failure probability over
  messages.
* `mlkem512_qindcca_corrWorst_coll` — the bound of `mlkem512_qindcca_coll` with
  the decryption-failure term equal to `corrWorst` and each module-LWE term
  `qMLWEWorstBound`; the only hypothesis is a bound `ε` on the coin-collision
  weight of the scheme.
* `mlkem512_qindcca_fips_coll` — the same bound with keys, hashes and rejection
  seeds of 32 bytes and the polynomial-oracle data `polyG`, `polyJ`, `polyH`,
  `polyT`.

`MLKEM512QROMNumeric` states both at the proved collision term `collBound`.

## Scope

With 32-byte keys, hashes and seeds, every table range has `2 ^ 256` or
`2 ^ 6400` elements and every table domain at most `2 ^ 6400` elements: the
encryption seed has `2 ^ 6144` elements (768 PRF bytes), the compressed
ciphertext `2 ^ 6144` (`2 · 256 · 10 + 256 · 4` bits) and the message
`2 ^ 256`. The field `GaloisField 2 6400` therefore carries all four tables.
The K-PKE idealisations of `mlkem512_qindcca_coll` are unchanged.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Crypto.MLKEM.MLKEM512QROMFinal

open CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)

/-! ## Average and worst-case decryption error -/

section Generic

variable {PK SK M C R : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype R] [Nonempty R]
  [DecidableEq M]

omit [Fintype PK] [Fintype SK] [Fintype M] in
/-- The failure probability of `m` under `(pk, sk)` is the uniform average over
coins of the failure indicator. -/
theorem failProb_eq_sum (P : Scheme PK SK M C R) (pk : PK) (sk : SK) (m : M) :
    P.failProb pk sk m = ∑ r : R, (Fintype.card R : ℝ≥0∞)⁻¹ *
      if P.dec sk (P.enc pk m r) = some m then 0 else 1 := by
  rw [Scheme.failProb, PMF.toOuterMeasure_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : P.dec sk (P.enc pk m r) = some m <;>
    simp [Set.indicator, h, PMF.uniformOfFintype_apply]

/-- The decryption error `corrErr` (the key-weighted average over messages and coins
of the failure indicator) is at most the correctness error `corrWorst` (the
key-weighted largest failure probability over messages). -/
theorem corrErr_le_corrWorst (P : Scheme PK SK M C R) : corrErr P ≤ P.corrWorst := by
  unfold corrErr Scheme.corrWorst
  rw [tsum_fintype]
  gcongr with ks
  simp_rw [← failProb_eq_sum]
  calc ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ * P.failProb ks.1 ks.2 m
      ≤ ∑ _m : M, (Fintype.card M : ℝ≥0∞)⁻¹ * ⨆ m', P.failProb ks.1 ks.2 m' := by
        gcongr with m
        exact le_iSup (P.failProb ks.1 ks.2) m
    _ = (Fintype.card M : ℝ≥0∞) * (Fintype.card M : ℝ≥0∞)⁻¹ *
          ⨆ m', P.failProb ks.1 ks.2 m' := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ ⨆ m', P.failProb ks.1 ks.2 m' := by
        refine mul_le_of_le_one_left zero_le ?_
        exact ENNReal.mul_inv_le_one _

end Generic

/-! ## ML-KEM-512 with the worst-case failure term -/

section Worst

open CatCrypt.Crypto.MLKEM.FIPS203QROMQuantumMLWE
open MLKEM512Instance (mlkem512Params)
open CompressedPKE (MLKEM512CT mlkem512Compress mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)
open MLKEM512FailureBound (lamWorst hlam_lamWorst sum_kemSample_lamWorst)

variable {m₁ m₂ n w q k c a : ℕ} {K Hash Z : Type} [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [DecidableEq Hash]
  (hpk : PK mlkem512Params.toBasic → Hash) (eG : (mlkem512Params.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × MLKEM512CT) ≃ Fin m₂) (eKR : (K × mlkem512Params.Seed) ≃ Fin n)
  (eC : MLKEM512CT ≃ Fin c) (eKa : K ≃ Fin a) [NeZero n] [NeZero c]

open scoped Classical in
/-- `qMLWEStdBound` with the decryption error `corrErr mlkem512CompressedScheme`
replaced by the correctness error `mlkem512CompressedScheme.corrWorst`: two
module-LWE and two extended module-LWE advantages of the reductions `qRedPoly`,
`|M|⁻¹` and `corrWorst`. -/
def qMLWEWorstBound (PG : PolyData (Fin m₁) (Fin n)) (PJ : PolyData (Fin m₂) (Fin n))
    (PH : PolyData MLKEM512CT K) (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K) (b : Bool) :
    ℝ≥0∞ :=
  qMLWE mlkem512Params.toBasic (qRedPoly mlkem512Params.toBasic mlkem512CompressedScheme hpk eG
      eJ eKR eC eKa PG PJ PH PT id
      (qRedEnc mlkem512CompressedScheme (indRed eG (owRedQuery A b)) true)) +
    qMLWEExt mlkem512Params.toBasic (qRedPoly mlkem512Params.toBasic mlkem512CompressedScheme
      hpk eG eJ eKR eC eKa PG PJ PH PT (fun x => (x.1, x.2.1))
      (qRedExt mlkem512Params.toBasic mlkem512Compress (indRed eG (owRedQuery A b)) true)) +
    qMLWEExt mlkem512Params.toBasic (qRedPoly mlkem512Params.toBasic mlkem512CompressedScheme
      hpk eG eJ eKR eC eKa PG PJ PH PT (fun x => (x.1, x.2.1))
      (qRedExt mlkem512Params.toBasic mlkem512Compress (indRed eG (owRedQuery A b)) false)) +
    qMLWE mlkem512Params.toBasic (qRedPoly mlkem512Params.toBasic mlkem512CompressedScheme hpk eG
      eJ eKR eC eKa PG PJ PH PT id
      (qRedEnc mlkem512CompressedScheme (indRed eG (owRedQuery A b)) false)) +
    (Fintype.card mlkem512Params.PT : ℝ≥0∞)⁻¹ + mlkem512CompressedScheme.corrWorst

omit [Nonempty Z] in
open scoped Classical in
/-- `qMLWEStdBound` is at most `qMLWEWorstBound`. -/
theorem qMLWEStdBound_le_qMLWEWorstBound (PG : PolyData (Fin m₁) (Fin n))
    (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData MLKEM512CT K)
    (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K) (b : Bool) :
    qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT A b ≤
      qMLWEWorstBound hpk eG eJ eKR eC eKa PG PJ PH PT A b := by
  unfold qMLWEStdBound qMLWEWorstBound
  gcongr
  exact corrErr_le_corrWorst _

variable [NeZero a] [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]

open scoped Classical in
/-- **The FIPS 203 Fujisaki–Okamoto KEM over the idealised ML-KEM-512 K-PKE in the
quantum random-oracle model, under quantum module-LWE and extended module-LWE, with
the correctness error `corrWorst`.** For every quantum adversary `A` with `k`
decapsulation rounds and every polynomial-oracle data `PG`, `PJ`, `PH`, `PT`, with
`q' = flatQ q k q`, `q'' = flatQ (q + 4) k q`, `δ = corrWorst` and `ε` any bound
on the coin-collision weight `collWeight mlkem512CompressedScheme`, the advantage
is at most

`4 √(4 q'² (W_true + δ)) + (8 q' √δ + (δ + ε) + 8 q' √δ)
  + 4 √(4 q'² (W_false + δ)) + 2 (8 q' / √|Z| + 8 q'' √δ + δ + 8 q' √δ)`,

where `W_b = qMLWEWorstBound … (nfKEM A) b`. -/
theorem mlkem512_qindcca_corrWorst_coll (PG : PolyData (Fin m₁) (Fin n))
    (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData MLKEM512CT K)
    (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K)
    (ε : ℝ≥0∞) (hcoll : collWeight mlkem512CompressedScheme ≤ ε) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) true +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          (mlkem512CompressedScheme.corrWorst + ε) +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) false +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          mlkem512CompressedScheme.corrWorst +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ))) := by
  have h := mlkem512_qindcca_qmlwe_coll hpk eG eJ eKR eC eKa A ε hcoll
    MLKEM512Hypotheses.mlkem512_hcoin lamWorst (fun pk sk _ x => hlam_lamWorst hpk eG eKR pk sk x)
  rw [sum_kemSample_lamWorst] at h
  simp only [qMLWEBound_eq_qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT] at h
  refine h.trans ?_
  gcongr <;> exact qMLWEStdBound_le_qMLWEWorstBound hpk eG eJ eKR eC eKa PG PJ PH PT _ _

end Worst

/-! ## FIPS 203 byte types and polynomial oracles over `GaloisField 2 6400` -/

section FIPS

open MLKEM512Instance (mlkem512Params mlkem512_message_card)
open CompressedPKE (MLKEM512CT mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)

/-- A 32-byte string: the FIPS 203 type of the shared key `K`, of the hash
`H(ek)` and of the implicit-rejection seed `z`. -/
abbrev Bytes32 : Type := Fin 32 → UInt8

theorem card_uint8 : Fintype.card UInt8 = 2 ^ 8 := by
  rw [Fintype.card_congr (⟨UInt8.toFin, UInt8.ofFin, fun x => UInt8.ofFin_toFin x,
    fun x => UInt8.toFin_ofFin x⟩ : UInt8 ≃ Fin (2 ^ 8)), Fintype.card_fin]

/-- A string of `k` bytes has `2 ^ (8 k)` values. -/
theorem card_bytes (k : ℕ) : Fintype.card (Fin k → UInt8) = 2 ^ (8 * k) := by
  rw [Fintype.card_fun, Fintype.card_fin, card_uint8, ← pow_mul]

theorem card_bytes32 : Fintype.card Bytes32 = 2 ^ 256 := card_bytes 32

/-- The encryption seed of `mlkem512Params` is 768 PRF bytes. -/
theorem card_seed : Fintype.card mlkem512Params.Seed = 2 ^ 6144 := by
  have h : Fintype.card mlkem512Params.Seed = Fintype.card ((Fin 2 → Fin 192 → UInt8) ×
      (Fin 2 → Fin 128 → UInt8) × (Fin 128 → UInt8)) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h, Fintype.card_prod, Fintype.card_prod, Fintype.card_fun (α := Fin 2),
    Fintype.card_fun (α := Fin 2), card_bytes, card_bytes, Fintype.card_fin, ← pow_mul, ← pow_mul, ← pow_add,
    ← pow_add]

/-- The compressed ML-KEM-512 ciphertext has `2 · 256 · 10 + 256 · 4 = 6144` bits. -/
theorem card_ct : Fintype.card MLKEM512CT = 2 ^ 6144 := by
  have h : Fintype.card MLKEM512CT = Fintype.card ((Fin 2 → Fin 256 → ZMod (2 ^ 10)) ×
      (Fin 256 → ZMod (2 ^ 4))) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, ZMod.card, ZMod.card, ← pow_mul, ← pow_mul, ← pow_mul,
    ← pow_add]

theorem card_pt_bytes32 : Fintype.card (mlkem512Params.PT × Bytes32) = 2 ^ 512 := by
  rw [Fintype.card_prod, mlkem512_message_card, card_bytes32, ← pow_add]

theorem card_bytes32_seed : Fintype.card (Bytes32 × mlkem512Params.Seed) = 2 ^ 6400 := by
  rw [Fintype.card_prod, card_bytes32, card_seed, ← pow_add]

theorem card_bytes32_ct : Fintype.card (Bytes32 × MLKEM512CT) = 2 ^ 6400 := by
  rw [Fintype.card_prod, card_bytes32, card_ct, ← pow_add]

theorem card_ct_le : Fintype.card MLKEM512CT ≤ 2 ^ 6400 :=
  calc Fintype.card MLKEM512CT = 2 ^ 6144 := card_ct
    _ ≤ 2 ^ 6400 := pow_le_pow_right₀ one_le_two (by norm_num)

theorem card_pt_bytes32_le : Fintype.card (mlkem512Params.PT × Bytes32) ≤ 2 ^ 6400 :=
  calc Fintype.card (mlkem512Params.PT × Bytes32) = 2 ^ 512 := card_pt_bytes32
    _ ≤ 2 ^ 6400 := pow_le_pow_right₀ one_le_two (by norm_num)

variable {m₁ m₂ n : ℕ}

/-- Polynomial-oracle data over `GaloisField 2 6400` for the table
`G : Fin m₁ → Fin n`. -/
def polyG (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁)
    (eKR : (Bytes32 × mlkem512Params.Seed) ≃ Fin n) : PolyData (Fin m₁) (Fin n) :=
  Classical.choice <| PolyData.nonempty_galois 2 6400 6400 (by norm_num)
    ((Fintype.card_congr eG).symm.trans_le card_pt_bytes32_le)
    ((Fintype.card_congr eKR).symm.trans card_bytes32_seed) le_rfl

/-- Polynomial-oracle data over `GaloisField 2 6400` for the table
`J : Fin m₂ → Fin n`. -/
def polyJ (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eKR : (Bytes32 × mlkem512Params.Seed) ≃ Fin n) : PolyData (Fin m₂) (Fin n) :=
  Classical.choice <| PolyData.nonempty_galois 2 6400 6400 (by norm_num)
    ((Fintype.card_congr eJ).symm.trans card_bytes32_ct).le
    ((Fintype.card_congr eKR).symm.trans card_bytes32_seed) le_rfl

/-- Polynomial-oracle data over `GaloisField 2 6400` for the table
`T : MLKEM512CT → Fin n`. -/
def polyT (eKR : (Bytes32 × mlkem512Params.Seed) ≃ Fin n) : PolyData MLKEM512CT (Fin n) :=
  Classical.choice <| PolyData.nonempty_galois 2 6400 6400 (by norm_num) card_ct_le
    ((Fintype.card_congr eKR).symm.trans card_bytes32_seed) le_rfl

/-- Polynomial-oracle data over `GaloisField 2 6400` for the table
`H : MLKEM512CT → Bytes32`, at the classical decidable equality on `Bytes32` that the
statements of `PolyOracle` use for a generic key type. -/
def polyH : @PolyData MLKEM512CT Bytes32 _ (fun a b => Classical.propDecidable (a = b)) :=
  letI : DecidableEq Bytes32 := fun a b => Classical.propDecidable (a = b)
  Classical.choice <| PolyData.nonempty_galois 2 6400 256 (by norm_num) card_ct_le
    card_bytes32 (by norm_num)

variable {w q k c a : ℕ}

open scoped Classical in
/-- **The FIPS 203 Fujisaki–Okamoto KEM over the idealised ML-KEM-512 K-PKE in the
quantum random-oracle model, under quantum module-LWE and extended module-LWE, at
32-byte keys and hashes.** The bound of `mlkem512_qindcca_corrWorst_coll` with
shared keys and `H(ek)` in `Bytes32` and the auxiliary tables answered by the
polynomial oracles `polyG`, `polyJ`, `polyH`, `polyT` over `GaloisField 2 6400`.
With `q' = flatQ q k q`, `q'' = flatQ (q + 4) k q`, `δ = corrWorst` and `ε` any
bound on the coin-collision weight `collWeight mlkem512CompressedScheme`, the
advantage is at most

`4 √(4 q'² (W_true + δ)) + (8 q' √δ + (δ + ε) + 8 q' √δ)
  + 4 √(4 q'² (W_false + δ)) + 2 (8 q' / √(2 ^ 256) + 8 q'' √δ + δ + 8 q' √δ)`,

where `W_b = qMLWEWorstBound … (nfKEM A) b`. The implicit-rejection seed `z` is a
32-byte string. -/
theorem mlkem512_qindcca_fips_coll (hpk : PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eKR : (Bytes32 × mlkem512Params.Seed) ≃ Fin n) (eC : MLKEM512CT ≃ Fin c)
    (eKa : Bytes32 ≃ Fin a) [NeZero n] [NeZero c] [NeZero a] [NeZero (flatQ q k q)]
    [NeZero (m₁ + m₂)]
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT Bytes32)
    (ε : ℝ≥0∞) (hcoll : collWeight mlkem512CompressedScheme ≤ ε) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa (polyG eG eKR) (polyJ eJ eKR) polyH
              (polyT eKR) (nfKEM A) true +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          (mlkem512CompressedScheme.corrWorst + ε) +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEWorstBound hpk eG eJ eKR eC eKa (polyG eG eKR) (polyJ eJ eKR) polyH
              (polyT eKR) (nfKEM A) false +
            mlkem512CompressedScheme.corrWorst))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((2 ^ 256 : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ) +
          mlkem512CompressedScheme.corrWorst +
          8 * (flatQ q k q : ℝ≥0∞) * mlkem512CompressedScheme.corrWorst ^ (1 / 2 : ℝ))) := by
  have h := mlkem512_qindcca_corrWorst_coll hpk eG eJ eKR eC eKa (polyG eG eKR) (polyJ eJ eKR)
    polyH (polyT eKR) A ε hcoll
  rwa [card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at h

end FIPS

end CatCrypt.Crypto.MLKEM.MLKEM512QROMFinal

end

end

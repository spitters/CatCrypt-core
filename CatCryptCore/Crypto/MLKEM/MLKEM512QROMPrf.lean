/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PRFCoinWeak
public import CatCryptCore.Crypto.MLKEM.PRFMLWE
public import CatCryptCore.Crypto.MLKEM.PRFInstance512
public import CatCryptCore.Crypto.MLKEM.MLKEM512QROMFinal

/-!
# ML-KEM-512 in the quantum random-oracle model with `PRF_η` as a random oracle

The quantum IND-CCA bound of the FIPS 203 Fujisaki–Okamoto KEM over the
ML-KEM-512 K-PKE in which

* the hash functions `G`, `J`, `H` and the noise function `PRF_η` are quantum
  random oracles; the adversary queries the table `F` of `PRF_η` in
  superposition, and the bound is averaged over `F` (the Kyber analysis of Bos,
  Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé,
  "CRYSTALS-Kyber: a CCA-secure module-lattice-based KEM", EuroS&P 2018, makes
  a PRF assumption on the noise sampler; the random-oracle model of `prfScheme`
  is the stronger idealisation);
* the matrix is `e (SampleNTT(XOF(ρ, j, i)))`, with the four XOF outputs uniform
  streams of `m = 280` three-byte groups (the XOF on a uniform seed `ρ` as a
  random oracle, read to 280 groups), and `e` a relabelling of NTT-domain
  matrices as matrices of `mlkem512Params` (FIPS 203 takes the entrywise inverse
  NTT); the public key carries the matrix rather than `ρ`, the adversary does not
  query the XOF, `hpk` is any function of the public key, and the seeds `ρ` and
  `σ` are independent and uniform (the derivation `(ρ, σ) := G(d ‖ k)` is not
  modelled);
* security rests on quantum module-LWE and quantum extended module-LWE at
  `mlkem512Params` with a uniform matrix, for distinguishers without oracle
  access; the change from the uniform matrix to the XOF matrix is the
  total-variation term `4 · C(560, 255) · (767 / 4096) ^ 305`.

The collision term is `3 / 2^256` plus the coin-collision weight of the scheme
with uniform noise rows and the XOF matrix; `CollisionSpreadIdeal` bounds that
weight by the proved bound `collBound + xofHop`.

## Main definitions

* `kgX e` — key generation with the matrix `e (xofMatrix H)` from the XOF
  family `H`
* `xofHop` — the bound `2² · C(560, 255) · (767 / 4096) ^ 305` on the distance of
  the XOF matrix from a uniform matrix
* `polyGp`, `polyJp`, `polyHp`, `polyTp`, `polyFp` — polynomial-oracle data over
  `GaloisField 2 6400` for the tables `G`, `J`, `H`, `T` and `F`
* `owTermWorst` — the one-wayness term with the decryption error bounded by
  `decryptionFailureProb mlkem512Noise δ_c`

## Main results

* `qIndAuxIdealPr_close_cpaExp`, `owTerm_le_owTermStd_close` — `PRFMLWE`'s
  bound of the one-wayness term when key generation at uniform rows is only
  `δ`-close to the key distribution of the K-PKE
* `avg_qINDCCAF_le_std_coll` — `avg_qINDCCAF_le_corrWorst_coll` with each
  one-wayness term bounded by module-LWE advantages
* `avg_corrErr_prfScheme_le` — the decryption error averaged over the table is
  at most the correctness error with uniform noise rows plus `|Sd|⁻¹`
* `kgX_close`, `corrWorst_ideal_kgX_le` — key generation and the correctness
  error with the XOF matrix are within `xofHop` of those of the K-PKE
* `mlkem512_qindcca_prf_coll` — the averaged quantum IND-CCA bound at ML-KEM-512
  with the collision term `3 / 2^256 + collWeight` of the scheme with uniform
  noise rows and the XOF matrix
* `mlkem512_qindcca_prf_worst_coll` — the same bound under the correctness bound
  `hWorst`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.MLKEM.PRFOracle (avg avg_prod avg_le_one prfRow PushesUniform)
open CatCrypt.Crypto.MLKEM.PRFAuxHop (prfScheme QIndAuxPrfAdv qIndAuxIdealPr)
open CatCrypt.Crypto.MLKEM.PRFKEMChain (redAdv owTerm prfHop qINDCCAAdvantageF)
open CatCrypt.Crypto.MLKEM.PRFMLWE (viewF viewF_le_one qIndAuxIdealPr_eq_avg qMLWEPrfBound
  owTermStd prfDeg qStdAcc_qRedEncF qStdAcc_qRedExtF)
open CatCrypt.Quantum.QROM.PRFChain (chainBound)
open CatCrypt.Crypto.MLKEM.PRFBadTableKeyed (idealScheme chainBound_mono_keyed)
open CatCrypt.Crypto.MLKEM.XOFMatrix (absDiff_le_of_close)

noncomputable section

namespace CatCrypt.Crypto.MLKEM.MLKEM512QROMPrf

/-! ## The one-wayness term when key generation is only close to the K-PKE -/

section Close

variable {Sd Nc PK SK M C KS K Hash Z Φ ι : Type} {m₁ m₂ m₃ n W Q : ℕ} [Fintype Φ] [Nonempty Φ]
  [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash] [NeZero n]
  [Fintype Z] [Nonempty Z] [Fintype C] [DecidableEq C] [Fintype K] [Nonempty K] [Fintype ι]
  [Fintype Nc] [DecidableEq Nc]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n)

/-- **The ideal experiment is close to an IND-CPA expectation.** When the average
over the public coins and the key-noise row of every `[0, 1]`-valued function of
the public key is within `δ` of its expectation under the key distribution of `S`
(`hKey`) and encryption at a uniform noise row gives the ciphertext of `S`
(`hEnc`), the ideal experiment is within `δ` of `cpaExp S` of `viewF`. -/
theorem qIndAuxIdealPr_close_cpaExp {SK' R : Type} [Fintype PK] [Fintype SK'] [Fintype R]
    (S : Scheme PK SK' M C R) (δ : ℝ≥0∞)
    (hKey : ∀ g : PK → ℝ≥0∞, (∀ x, g x ≤ 1) →
      (avg fun p : Φ × (Nc → Fin n) => g (kg p.1 (eK p.2)).1) ≤
          (∑ ks : PK × SK', S.keygen ks * g ks.1) + δ ∧
        (∑ ks : PK × SK', S.keygen ks * g ks.1) ≤
          (avg fun p : Φ × (Nc → Fin n) => g (kg p.1 (eK p.2)).1) + δ)
    (hEnc : ∀ (pk : PK) (m : M) (g : C → ℝ≥0∞),
      (avg fun ρ : Nc → Fin n => g (enc pk m ρ)) = avg fun r : R => g (S.enc pk m r))
    (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q PK C K M) (b : Bool) :
    qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B b ≤
        cpaExp S B.msgs (viewF eD kg enc dec eK hpk eG eJ eKR B) b + δ ∧
      cpaExp S B.msgs (viewF eD kg enc dec eK hpk eG eJ eKR B) b ≤
        qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B b + δ := by
  set H : PK → ℝ≥0∞ := fun pk => avg fun i : ι => avg fun r : R =>
    viewF eD kg enc dec eK hpk eG eJ eKR B pk i (S.enc pk (B.msg pk i b) r) with hH
  have hH1 : ∀ pk, H pk ≤ 1 := fun pk =>
    PRFInstance512.sum_inv_mul_le_one fun _ => PRFInstance512.sum_inv_mul_le_one fun _ =>
      viewF_le_one eD kg enc dec eK hpk eG eJ eKR B _ _ _
  have hI : qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B b =
      avg fun p : Φ × (Nc → Fin n) => H (kg p.1 (eK p.2)).1 := by
    rw [qIndAuxIdealPr_eq_avg]
    have h1 : ∀ (pk : PK) (i : ι),
        (avg fun ρ : Nc → Fin n =>
          viewF eD kg enc dec eK hpk eG eJ eKR B pk i (enc pk (B.msg pk i b) ρ)) =
        avg fun r : R => viewF eD kg enc dec eK hpk eG eJ eKR B pk i (S.enc pk (B.msg pk i b) r) :=
      fun pk i => hEnc pk _ (fun cst => viewF eD kg enc dec eK hpk eG eJ eKR B pk i cst)
    simp only [h1, hH]
  have hC : cpaExp S B.msgs (viewF eD kg enc dec eK hpk eG eJ eKR B) b =
      ∑ ks : PK × SK', S.keygen ks * H ks.1 := rfl
  rw [hI, hC]
  exact hKey H hH1

end Close

section Bound

open CatCrypt.Crypto.MLKEM.CompressedPKE (mapCiphertext)

variable {Sd Nc SK C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n w q k c a : ℕ} [Fintype Φ]
  [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash]
  [NeZero n] [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Z]
  [Nonempty Z] [Fintype Nc] [DecidableEq Nc] [NeZero c] [NeZero (m₁ + m₂)] [NeZero (flatQ q k q)]
  (P : MLWE_PKE_Scheme.Params) (f : MLWE_PKE_Basic.CT P.toBasic → C)
  (g : C → MLWE_PKE_Basic.CT P.toBasic)
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → MLWE_PKE_Basic.PK P.toBasic × SK)
  (enc : MLWE_PKE_Basic.PK P.toBasic → P.PT → (Nc → Fin n) → C)
  (dec : SK → C → Option P.PT) (eK : (Nc → Fin n) → KS)
  (hpk : MLWE_PKE_Basic.PK P.toBasic → Hash) (eG : (P.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × Sd) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  (PG : PolyData (Fin m₁) (Fin n)) (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData C K)
  (PT : PolyData C (Fin n)) (PF : PolyData (Fin m₃) (Fin n))

/-- **The ideal IND-CPA advantage under quantum module-LWE, key generation
`δ`-close.** `PRFMLWE.absDiff_qIndAuxIdealPr_le_qMLWE` with the hypothesis
`hKey` weakened to `δ`-closeness on `[0, 1]`-valued functions of the public key;
the bound gains `2 δ`. -/
theorem absDiff_qIndAuxIdealPr_le_qMLWE_close (δ : ℝ≥0∞)
    (hKey : ∀ g' : MLWE_PKE_Basic.PK P.toBasic → ℝ≥0∞, (∀ x, g' x ≤ 1) →
      (avg fun p : Φ × (Nc → Fin n) => g' (kg p.1 (eK p.2)).1) ≤
          (∑ ks, (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).keygen ks * g' ks.1) + δ ∧
        (∑ ks, (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).keygen ks * g' ks.1) ≤
          (avg fun p : Φ × (Nc → Fin n) => g' (kg p.1 (eK p.2)).1) + δ)
    (hEnc : ∀ (pk : MLWE_PKE_Basic.PK P.toBasic) (m : P.PT) (g' : C → ℝ≥0∞),
      (avg fun ρ : Nc → Fin n => g' (enc pk m ρ)) =
        avg fun r : P.Seed => g' ((mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).enc pk m r))
    (b₀ : Bool) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a (MLWE_PKE_Basic.PK P.toBasic) C K) :
    absDiff (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) true)
        (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) false) ≤
      qMLWEPrfBound P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF b₀ A + 2 * δ := by
  obtain ⟨h1, h1'⟩ := qIndAuxIdealPr_close_cpaExp eD kg enc dec eK hpk eG eJ eKR _ δ hKey hEnc
    (redAdv eG eC eKa b₀ A) true
  obtain ⟨h0, h0'⟩ := qIndAuxIdealPr_close_cpaExp eD kg enc dec eK hpk eG eJ eKR _ δ hKey hEnc
    (redAdv eG eC eKa b₀ A) false
  refine (absDiff_le_of_close h1 h1' h0 h0').trans (add_le_add ?_ le_rfl)
  refine (cpaExp_absDiff_le P f g _ _
    (viewF_le_one eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A))).trans_eq ?_
  simp only [qMLWEPrfBound, qMLWE, qMLWEExt,
    qStdAcc_qRedEncF P f g eD kg enc dec eK hpk eG eJ eKR eC eKa _ _ _ _ _ (PG.kWise _)
      (PJ.kWise _) (PH.kWise _) (PT.kWise _) (PF.kWise _),
    qStdAcc_qRedExtF P f eD kg enc dec eK hpk eG eJ eKR eC eKa _ _ _ _ _ (PG.kWise _)
      (PJ.kWise _) (PH.kWise _) (PT.kWise _) (PF.kWise _)]

variable [Fintype SK]

/-- `owTerm` is at most `owTermStd + 2 δ` when key generation at uniform rows is
`δ`-close to the key distribution of the K-PKE. -/
theorem owTerm_le_owTermStd_close (δ : ℝ≥0∞)
    (hKey : ∀ g' : MLWE_PKE_Basic.PK P.toBasic → ℝ≥0∞, (∀ x, g' x ≤ 1) →
      (avg fun p : Φ × (Nc → Fin n) => g' (kg p.1 (eK p.2)).1) ≤
          (∑ ks, (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).keygen ks * g' ks.1) + δ ∧
        (∑ ks, (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).keygen ks * g' ks.1) ≤
          (avg fun p : Φ × (Nc → Fin n) => g' (kg p.1 (eK p.2)).1) + δ)
    (hEnc : ∀ (pk : MLWE_PKE_Basic.PK P.toBasic) (m : P.PT) (g' : C → ℝ≥0∞),
      (avg fun ρ : Nc → Fin n => g' (enc pk m ρ)) =
        avg fun r : P.Seed => g' ((mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).enc pk m r))
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a (MLWE_PKE_Basic.PK P.toBasic) C K) (b₀ : Bool) :
    owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A b₀ ≤
      owTermStd P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF b₀ A + 2 * δ := by
  calc owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A b₀
      ≤ (qMLWEPrfBound P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF b₀ A + 2 * δ) +
          (Fintype.card P.PT : ℝ≥0∞)⁻¹ + 2 * prfHop Sd q k +
          avg (fun F : Fin m₃ → Fin n => corrErr (prfScheme eD kg enc dec eK id F)) := by
        unfold owTerm
        gcongr
        exact absDiff_qIndAuxIdealPr_le_qMLWE_close P f g eD kg enc dec eK hpk eG eJ eKR eC eKa
          PG PJ PH PT PF δ hKey hEnc b₀ A
    _ = _ := by unfold owTermStd; ring

variable [DecidableEq Sd] [DecidableEq SK] [NeZero a]

open scoped Classical in
/-- **The averaged IND-CCA bound with the collision weight of the scheme with
uniform noise rows, under quantum module-LWE.** `avg_qINDCCAF_le_corrWorst_coll`
with each one-wayness term bounded by `owTermStd + 2 δ`, when key generation at
uniform rows is `δ`-close to the key distribution of the K-PKE; no condition on
the table remains. -/
theorem avg_qINDCCAF_le_std_coll (δ : ℝ≥0∞)
    (hKey : ∀ g' : MLWE_PKE_Basic.PK P.toBasic → ℝ≥0∞, (∀ x, g' x ≤ 1) →
      (avg fun p : Φ × (Nc → Fin n) => g' (kg p.1 (eK p.2)).1) ≤
          (∑ ks, (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).keygen ks * g' ks.1) + δ ∧
        (∑ ks, (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).keygen ks * g' ks.1) ≤
          (avg fun p : Φ × (Nc → Fin n) => g' (kg p.1 (eK p.2)).1) + δ)
    (hEnc : ∀ (pk : MLWE_PKE_Basic.PK P.toBasic) (m : P.PT) (g' : C → ℝ≥0∞),
      (avg fun ρ : Nc → Fin n => g' (enc pk m ρ)) =
        avg fun r : P.Seed => g' ((mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).enc pk m r))
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a (MLWE_PKE_Basic.PK P.toBasic) C K) (t : ℕ) :
    (avg fun F : Fin m₃ → Fin n =>
      qINDCCAAdvantageF (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR eC eKa F A) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (6 * (idealScheme kg enc dec eK).corrWorst +
          ((t + 2 : ℕ) : ℝ≥0∞) / Fintype.card Sd + (Fintype.card P.PT : ℝ≥0∞) * 2⁻¹ ^ t)
        (3 * (Fintype.card Sd : ℝ≥0∞)⁻¹ + collWeight (idealScheme kg enc dec eK))
        (Fintype.card Z : ℝ≥0∞)⁻¹
        (owTermStd P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF true A + 2 * δ)
        (owTermStd P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF false A + 2 * δ) :=
  (PRFCoinWeak.avg_qINDCCAF_le_corrWorst_coll eD kg enc dec eK hpk eG eJ eKR eC eKa A t).trans
    (chainBound_mono_keyed _ _ _ _ le_rfl
      (owTerm_le_owTermStd_close P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF δ
        hKey hEnc A true)
      (owTerm_le_owTermStd_close P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF δ
        hKey hEnc A false))

end Bound

/-! ## The decryption error of the scheme with noise from the table -/

section CorrErr

open CatCrypt.Crypto.MLKEM.PRFOracle (avg_mono avg_const avg_comm avg_add avg_fst avg_setRows
  keygenPrf)
open CatCrypt.Crypto.MLKEM.PRFBadTable (failRel)
open CatCrypt.Crypto.MLKEM.PRFBadTableKeyed (corrWorst_idealScheme)
open CatCrypt.Crypto.MLKEM.PRFKEMChain (sum_map_uniform)

variable {Sd Nc PK SK M C KS Φ : Type} {m₃ n : ℕ} [Fintype Φ] [Nonempty Φ] [Fintype Sd]
  [DecidableEq Sd] [Nonempty Sd] [Fintype Nc] [DecidableEq Nc] [Fintype PK] [DecidableEq PK]
  [Fintype SK] [DecidableEq SK] [Fintype M] [DecidableEq M] [Nonempty M] [NeZero n]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)

omit [DecidableEq SK] [Nonempty Sd] in
/-- The average over the seed `s` of the indicator of `s = σ` is `|Sd|⁻¹`. -/
theorem avg_ite_eq (σ : Sd) : (avg fun s : Sd => if s = σ then (1 : ℝ≥0∞) else 0) =
    (Fintype.card Sd : ℝ≥0∞)⁻¹ := by
  unfold avg
  simp

/-- **The averaged decryption error of the scheme with noise from the table.**
Averaged over a uniform table, the decryption error `corrErr` of `prfScheme F` is
at most the correctness error of the scheme with uniform noise rows plus the
probability `|Sd|⁻¹` that the encryption seed is the key seed. -/
theorem avg_corrErr_prfScheme_le :
    (avg fun F : Fin m₃ → Fin n => corrErr (prfScheme eD kg enc dec eK id F)) ≤
      (idealScheme kg enc dec eK).corrWorst + (Fintype.card Sd : ℝ≥0∞)⁻¹ := by
  set fl : Φ → M → (Nc → Fin n) → (Nc → Fin n) → ℝ≥0∞ := fun φ m a b =>
    if dec (kg φ (eK a)).2 (enc (kg φ (eK a)).1 m b) = some m then 0 else 1 with hfl
  have hfl1 : ∀ φ m a b, fl φ m a b ≤ 1 := fun φ m a b => by
    simp only [hfl]; split_ifs <;> simp
  have hce : ∀ F : Fin m₃ → Fin n, corrErr (prfScheme eD kg enc dec eK id F) =
      avg fun p : Φ × Sd => avg fun m : M => avg fun s : Sd =>
        fl p.1 m (prfRow eD F p.2) (prfRow eD F s) := fun F =>
    sum_map_uniform (fun p : Φ × Sd => keygenPrf eD kg eK F p.1 p.2) _
  have hswap : (avg fun F : Fin m₃ → Fin n => avg fun p : Φ × Sd => avg fun m : M =>
      avg fun s : Sd => fl p.1 m (prfRow eD F p.2) (prfRow eD F s)) =
      avg fun p : Φ × Sd => avg fun m : M => avg fun s : Sd =>
        avg fun F : Fin m₃ → Fin n => fl p.1 m (prfRow eD F p.2) (prfRow eD F s) := by
    rw [avg_comm]
    refine congrArg avg (funext fun p => ?_)
    rw [avg_comm]
    refine congrArg avg (funext fun m => ?_)
    rw [avg_comm]
  have hpt : ∀ (φ : Φ) (σ : Sd) (m : M) (s : Sd),
      (avg fun F : Fin m₃ → Fin n => fl φ m (prfRow eD F σ) (prfRow eD F s)) ≤
        (if s = σ then (1 : ℝ≥0∞) else 0) +
          avg fun a : Nc → Fin n => avg fun b : Nc → Fin n => fl φ m a b := by
    intro φ σ m s
    by_cases hs : s = σ
    · rw [if_pos hs]
      exact (avg_le_one fun F => hfl1 _ _ _ _).trans le_self_add
    · rw [if_neg hs, zero_add, ← avg_setRows eD (Ne.symm hs)
        (fun a b (_ : Fin m₃ → Fin n) => fl φ m a b)]
      simp only [avg_prod, avg_const, le_refl]
  have hmax : ∀ (φ : Φ) (a : Nc → Fin n),
      (avg fun m : M => avg fun b : Nc → Fin n => fl φ m a b) ≤
        ⨆ m : M, avg (fun w => if failRel kg enc dec eK id φ m a w then (1 : ℝ≥0∞) else 0) := by
    intro φ a
    refine (avg_mono fun m => le_of_eq_of_le ?_ (le_iSup (fun m : M =>
      avg (fun w => if failRel kg enc dec eK id φ m a w then (1 : ℝ≥0∞) else 0)) m)).trans
        (avg_const _).le
    refine congrArg avg (funext fun b => ?_)
    simp only [hfl, failRel, id]
    split_ifs with h1 h2 h2 <;> simp_all
  rw [corrWorst_idealScheme, add_comm]
  calc (avg fun F : Fin m₃ → Fin n => corrErr (prfScheme eD kg enc dec eK id F))
      = avg fun p : Φ × Sd => avg fun m : M => avg fun s : Sd =>
          avg fun F : Fin m₃ → Fin n => fl p.1 m (prfRow eD F p.2) (prfRow eD F s) := by
        simp only [hce]; exact hswap
    _ ≤ avg fun p : Φ × Sd => avg fun m : M => (Fintype.card Sd : ℝ≥0∞)⁻¹ +
          avg fun a : Nc → Fin n => avg fun b : Nc → Fin n => fl p.1 m a b :=
        avg_mono fun p => avg_mono fun m => (avg_mono fun s => hpt p.1 p.2 m s).trans
          (le_of_eq (by rw [avg_add, avg_ite_eq, avg_const]))
    _ = (Fintype.card Sd : ℝ≥0∞)⁻¹ + avg fun φ : Φ => avg fun m : M =>
          avg fun a : Nc → Fin n => avg fun b : Nc → Fin n => fl φ m a b := by
        simp only [avg_add, avg_const]
        rw [avg_fst (fun φ : Φ => avg fun m : M => avg fun a : Nc → Fin n =>
          avg fun b : Nc → Fin n => fl φ m a b)]
    _ ≤ _ := by
        refine add_le_add le_rfl (avg_mono fun φ => ?_)
        rw [avg_comm]
        exact avg_mono fun a => hmax φ a

end CorrErr

/-! ## The XOF matrix as public coins -/

section XOF

open CatCrypt.Prob
open CatCrypt.Crypto.MLKEM.XOFMatrix (Family xofMatrix xofMatrixDistVia nonFillProb
  nonFillProb_le)

/-- The expectation under a point mass is the value at the point. -/
theorem sdExp_pure {α : Type} (x : α) (G : α → ℝ≥0∞) : sdExp (SDistr.pure x) G = G x := by
  classical
  unfold sdExp
  simp only [SDistr.pure_apply_some, ite_mul, one_mul, zero_mul]
  simp

/-- The expectation under the uniform distribution is the uniform average. -/
theorem sdExp_uniform {α : Type} [Fintype α] [Nonempty α] (G : α → ℝ≥0∞) :
    sdExp (SDistr.uniform α) G = avg G := by
  unfold sdExp avg
  rw [tsum_fintype]
  simp only [SDistr.uniform_apply_some]

/-- A sum over `Option T` against `Option.elim o 0 G` is the expectation of `G`. -/
theorem tsum_elim_eq_sdExp {T : Type} [Fintype T] (d : SDistr T) (G : T → ℝ≥0∞) :
    ∑' o, d o * Option.elim o 0 G = sdExp d G := by
  unfold sdExp
  rw [tsum_fintype, tsum_fintype, Fintype.sum_option]
  simp

/-- Two expectations of a `[0, 1]`-valued function are at most `tvDist` apart. -/
theorem absDiff_sdExp_le_tvDist {T : Type} [Fintype T] (d₁ d₂ : SDistr T) (G : T → ℝ≥0∞)
    (hG : ∀ x, G x ≤ 1) : absDiff (sdExp d₁ G) (sdExp d₂ G) ≤ tvDist d₁ d₂ := by
  rw [← tsum_elim_eq_sdExp, ← tsum_elim_eq_sdExp]
  refine le_iSup₂_of_le (f := fun (f : Option T → ℝ≥0∞) (_ : ∀ x, f x ≤ 1) =>
    absDiff (∑' x, d₁ x * f x) (∑' x, d₂ x * f x)) (fun o => Option.elim o 0 G) ?_ le_rfl
  rintro (_ | a)
  · exact zero_le_one
  · exact hG a

/-- **The XOF matrix as public coins.** For every `[0, 1]`-valued `G`, its average
at `e (xofMatrix H)` over a uniform family `H` is within `k² · nonFillProb m` of
its average over a uniform matrix. -/
theorem absDiff_avg_xofMatrix_le (k m : ℕ) {T : Type} [Fintype T] [Nonempty T]
    (e : XOFMatrix.Mat k ≃ T) (G : T → ℝ≥0∞) (hG : ∀ x, G x ≤ 1) :
    absDiff (avg fun H : Family k m => G (e (xofMatrix H))) (avg G) ≤
      ((k * k : ℕ) : ℝ≥0∞) * nonFillProb m := by
  have h1 : sdExp (xofMatrixDistVia (m := m) e) G = avg fun H : Family k m => G (e (xofMatrix H)) := by
    rw [xofMatrixDistVia, ← CatCrypt.Prob.SDistr.monad_bind_eq, PRFInstance512.sdExp_bind]
    simp only [sdExp_pure]
    rw [tsum_elim_eq_sdExp]
    convert sdExp_uniform (α := Family k m) _ using 3
  rw [← h1, ← sdExp_uniform]
  exact (absDiff_sdExp_le_tvDist _ _ G hG).trans (PRFInstance512.tvDist_xofMatrixDistVia_le k m e)

end XOF

/-! ## ML-KEM-512 -/

section MLKEM512

open CatCrypt.Crypto.MLKEM.XOFMatrix (Family xofMatrix nonFillProb_le)
open MLKEM512Instance (mlkem512Params mlkem512_message_card)
open CompressedPKE (MLKEM512CT mlkem512Compress mlkem512Decompress mlkem512CompressedScheme)
open CatCrypt.Crypto.MLKEM.PRFInstance512 (Row Nonce prfN prfM eD512 eKR512 eK eE kg512 enc512
  B512 avg_kg512_eK avg_enc512 pushesUniform_eE sum_inv_mul_le_one)
open CatCrypt.Crypto.MLKEM.MLKEM512QROMFinal (Bytes32 card_bytes32 card_ct card_ct_le
  card_pt_bytes32_le card_bytes32_ct)

instance : NeZero prfN := ⟨pow_ne_zero _ two_ne_zero⟩

/-- Key generation at ML-KEM-512 with the matrix `e (SampleNTT(XOF(ρ, j, i)))`, the
XOF outputs given by the family `H`, and the key seed `ks`. -/
def kgX (e : XOFMatrix.Mat 2 ≃ B512.Mat) (H : Family 2 280) (ks : mlkem512Params.KeySeed) :
    MLWE_PKE_Basic.PK mlkem512Params.toBasic × MLWE_PKE_Basic.SK mlkem512Params.toBasic :=
  kg512 (e (xofMatrix H)) ks

/-- The bound `2² · C(560, 255) · (767 / 4096) ^ 305` on the total-variation
distance between the XOF matrix read to 280 groups and a uniform matrix.

References: NIST, FIPS 203, "Module-Lattice-Based Key-Encapsulation Mechanism
Standard", 2024, Algorithm 7 (SampleNTT: the matrix entries rejection-sampled
from three-byte groups of the XOF stream). -/
def xofHop : ℝ≥0∞ :=
  ((2 * 2 : ℕ) : ℝ≥0∞) * (((2 * 280).choose 255 : ℝ≥0∞) * (767 / 4096) ^ (2 * 280 - 255))

/-- **Key generation with the XOF matrix is `xofHop`-close to the K-PKE.** For every
`[0, 1]`-valued function of the public key, its average over a uniform XOF family
and a uniform key-noise row is within `xofHop` of its expectation under the key
distribution of `S512`.

References: NIST, FIPS 203, "Module-Lattice-Based Key-Encapsulation Mechanism
Standard", 2024, Algorithm 7 (SampleNTT, the rejection-sampled matrix that
`xofMatrix` models). -/
theorem kgX_close (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (g' : MLWE_PKE_Basic.PK mlkem512Params.toBasic → ℝ≥0∞) (hg : ∀ x, g' x ≤ 1) :
    (avg fun p : Family 2 280 × Row => g' (kgX e p.1 (eK p.2)).1) ≤
        (∑ ks, PRFInstance512.S512.keygen ks * g' ks.1) + xofHop ∧
      (∑ ks, PRFInstance512.S512.keygen ks * g' ks.1) ≤
        (avg fun p : Family 2 280 × Row => g' (kgX e p.1 (eK p.2)).1) + xofHop := by
  rw [← avg_kg512_eK, avg_prod, avg_prod]
  have hG : ∀ A, (avg fun v : Row => g' (kg512 A (eK v)).1) ≤ 1 :=
    fun A => sum_inv_mul_le_one fun _ => hg _
  exact PRFInstance512.le_add_of_absDiff_le ((absDiff_avg_xofMatrix_le 2 280 e _ hG).trans
    (show ((2 * 2 : ℕ) : ℝ≥0∞) * XOFMatrix.nonFillProb 280 ≤ xofHop by
      unfold xofHop
      gcongr
      exact nonFillProb_le 280 (by norm_num)))

/-- `Fin prfM` has at most `2 ^ 6400` elements. -/
theorem card_prfM_le : Fintype.card (Fin prfM) ≤ 2 ^ 6400 := by
  have key : ∀ a N : ℕ, a + 4 ≤ N → 2 ^ a * 15 ≤ 2 ^ N := fun a N hN =>
    (Nat.mul_le_mul_left _ (by norm_num : 15 ≤ 2 ^ 4)).trans
      ((pow_add 2 a 4).symm.trans_le (Nat.pow_le_pow_right (by norm_num) hN))
  rw [Fintype.card_fin]
  exact key (8 * 32) 6400 (by norm_num)

variable {m₁ m₂ : ℕ}

/-- Polynomial-oracle data over `GaloisField 2 6400` for `G : Fin m₁ → Fin prfN`. -/
def polyGp (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) : PolyData (Fin m₁) (Fin prfN) :=
  Classical.choice <| PolyData.nonempty_galois 2 6400 (8 * 64) (by norm_num)
    ((Fintype.card_congr eG).symm.trans_le card_pt_bytes32_le) (Fintype.card_fin _)
    (by norm_num)

/-- Polynomial-oracle data over `GaloisField 2 6400` for `J : Fin m₂ → Fin prfN`. -/
def polyJp (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂) : PolyData (Fin m₂) (Fin prfN) :=
  Classical.choice <| PolyData.nonempty_galois 2 6400 (8 * 64) (by norm_num)
    ((Fintype.card_congr eJ).symm.trans card_bytes32_ct).le (Fintype.card_fin _) (by norm_num)

/-- Polynomial-oracle data over `GaloisField 2 6400` for `H : MLKEM512CT → Bytes32`. -/
def polyHp : PolyData MLKEM512CT Bytes32 :=
  Classical.choice <| PolyData.nonempty_galois 2 6400 256 (by norm_num) card_ct_le
    card_bytes32 (by norm_num)

/-- Polynomial-oracle data over `GaloisField 2 6400` for `T : MLKEM512CT → Fin prfN`. -/
def polyTp : PolyData MLKEM512CT (Fin prfN) :=
  Classical.choice <| PolyData.nonempty_galois 2 6400 (8 * 64) (by norm_num) card_ct_le
    (Fintype.card_fin _) (by norm_num)

/-- Polynomial-oracle data over `GaloisField 2 6400` for the `PRF_η` table
`F : Fin prfM → Fin prfN`. -/
def polyFp : PolyData (Fin prfM) (Fin prfN) :=
  Classical.choice <| PolyData.nonempty_galois 2 6400 (8 * 64) (by norm_num) card_prfM_le
    (Fintype.card_fin _) (by norm_num)

/-- `absDiff_avg_xofMatrix_le` at ML-KEM-512: `k = 2`, `m = 280`. -/
theorem absDiff_avg_xof512_le (e : XOFMatrix.Mat 2 ≃ B512.Mat) (G : B512.Mat → ℝ≥0∞)
    (hG : ∀ x, G x ≤ 1) :
    absDiff (avg fun H : Family 2 280 => G (e (xofMatrix H))) (avg G) ≤ xofHop :=
  (absDiff_avg_xofMatrix_le 2 280 e G hG).trans
    (show ((2 * 2 : ℕ) : ℝ≥0∞) * XOFMatrix.nonFillProb 280 ≤ xofHop by
      unfold xofHop
      gcongr
      exact nonFillProb_le 280 (by norm_num))

/-- Key generation at a uniform matrix and the key seed read from a uniform row
has the key-pair distribution of `S512`. -/
theorem avg_kg512_eK_pair
    (g' : MLWE_PKE_Basic.PK mlkem512Params.toBasic × MLWE_PKE_Basic.SK mlkem512Params.toBasic →
      ℝ≥0∞) :
    (avg fun p : mlkem512Params.Mat × Row => g' (kg512 p.1 (eK p.2))) =
      ∑ ks, PRFInstance512.S512.keygen ks * g' ks := by
  rw [avg_prod]
  simp only [fun A => PRFInstance512.pushesUniform_eK (fun ks => g' (kg512 A ks))]
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  change _ = ∑' ks, ((PMF.uniformOfFintype mlkem512Params.Mat).bind fun A =>
    (PMF.uniformOfFintype mlkem512Params.KeySeed).map fun ks => kg512 A ks) ks * g' ks
  rw [KEM.FOTransformU.tsum_bind_mul]
  simp only [KEM.FOTransformU.tsum_map_mul, PMF.uniformOfFintype_apply]
  unfold avg
  rw [tsum_fintype (L := SummationFilter.unconditional _)]
  simp only [tsum_fintype (L := SummationFilter.unconditional _)]

open CatCrypt.Crypto.MLKEM.PRFBadTable (failRel) in
/-- The fraction of encryption-noise rows at which decryption fails is the failure
probability of `mlkem512CompressedScheme`. -/
theorem avg_failRel_kgX (e : XOFMatrix.Mat 2 ≃ B512.Mat) (φ : Family 2 280)
    (m : mlkem512Params.PT) (v : Row) :
    avg (fun w => if failRel (kgX e) enc512 mlkem512CompressedScheme.dec eK id φ m v w
      then (1 : ℝ≥0∞) else 0) =
      mlkem512CompressedScheme.failProb (kgX e φ (eK v)).1 (kgX e φ (eK v)).2 m := by
  rw [MLKEM512QROMFinal.failProb_eq_sum]
  change _ = avg fun r => if mlkem512CompressedScheme.dec (kgX e φ (eK v)).2
    (mlkem512CompressedScheme.enc (kgX e φ (eK v)).1 m r) = some m then (0 : ℝ≥0∞) else 1
  rw [← pushesUniform_eE]
  refine congrArg avg (funext fun w => ?_)
  show (if decide (mlkem512CompressedScheme.dec (kgX e φ (eK v)).2
    (mlkem512CompressedScheme.enc (kgX e φ (eK v)).1 m (eE w)) ≠ some m) = true
    then (1 : ℝ≥0∞) else 0) = _
  rw [if_congr decide_eq_true_iff rfl rfl]
  exact ite_not _ _ _

open CatCrypt.Crypto.MLKEM.PRFBadTableKeyed (corrWorst_idealScheme) in
/-- **The correctness error with the XOF matrix.** The correctness error of the
scheme with uniform noise rows and the XOF matrix is within `xofHop` of the
correctness error of `mlkem512CompressedScheme`. -/
theorem corrWorst_ideal_kgX_le (e : XOFMatrix.Mat 2 ≃ B512.Mat) :
    (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK).corrWorst ≤
      mlkem512CompressedScheme.corrWorst + xofHop := by
  classical
  set G : B512.Mat → ℝ≥0∞ := fun A => avg fun v : Row => ⨆ m,
    mlkem512CompressedScheme.failProb (kg512 A (eK v)).1 (kg512 A (eK v)).2 m with hGdef
  have hG : ∀ A, G A ≤ 1 := fun A => sum_inv_mul_le_one fun v => iSup_le fun m => by
    rw [MLKEM512QROMFinal.failProb_eq_sum]
    exact sum_inv_mul_le_one fun r => by split_ifs <;> simp
  have h1 : (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK).corrWorst =
      avg fun H : Family 2 280 => G (e (xofMatrix H)) := by
    rw [corrWorst_idealScheme]
    simp only [avg_failRel_kgX]
    rfl
  have h2 : mlkem512CompressedScheme.corrWorst = avg G := by
    rw [Scheme.corrWorst, tsum_fintype (L := SummationFilter.unconditional _)]
    rw [show (∑ ks, mlkem512CompressedScheme.keygen ks *
        ⨆ m, mlkem512CompressedScheme.failProb ks.1 ks.2 m) =
        ∑ ks, PRFInstance512.S512.keygen ks *
          ⨆ m, mlkem512CompressedScheme.failProb ks.1 ks.2 m from rfl,
      ← avg_kg512_eK_pair, avg_prod]
  rw [h1, h2]
  exact (PRFInstance512.le_add_of_absDiff_le (absDiff_avg_xof512_le e G hG)).1

variable {w q k c a : ℕ}

open CorrectnessBounds (decryptionFailureProb mlkem512Noise)

open scoped Classical in
/-- The one-wayness term of `mlkem512_qindcca_prf_coll` with the averaged
decryption error bounded through the correctness error: two module-LWE and two
extended module-LWE advantages of `qRedEncF`, `qRedExtF`, the message term
`2^-256`, twice the `PRF_η` hop,
`decryptionFailureProb mlkem512Noise δ_c + xofHop + 2^-256`, and twice the XOF
hop. -/
def owTermWorst (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (hpk : MLWE_PKE_Basic.PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eC : MLKEM512CT ≃ Fin c) (eKa : Bytes32 ≃ Fin a) [NeZero c] [NeZero (flatQ q k q)]
    [NeZero (m₁ + m₂)]
    (A : KEMQAdv (m₁ + m₂) prfM prfN w q k c a (MLWE_PKE_Basic.PK mlkem512Params.toBasic)
      MLKEM512CT Bytes32) (δ_c : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  qMLWEPrfBound mlkem512Params mlkem512Compress mlkem512Decompress eD512 (kgX e) enc512
      mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG) (polyJp eJ) polyHp
      polyTp polyFp b A +
    (2 ^ 256)⁻¹ + 2 * prfHop Bytes32 q k +
    (decryptionFailureProb mlkem512Noise δ_c + xofHop + (2 ^ 256)⁻¹) + 2 * xofHop

open scoped Classical in
/-- **The FIPS 203 Fujisaki–Okamoto KEM over ML-KEM-512 in the quantum random-oracle
model with `PRF_η` a random oracle and the matrix from `SampleNTT(XOF(ρ))`.**
For every quantum adversary `A` with superposition access to `G`, `J` and the
`PRF_η` table `F`, `k` decapsulation rounds, 32-byte keys, hashes and rejection
seeds, the IND-CCA advantage averaged over `F` is at most `chainBound` at the
failure term `6 · corrWorst + 514 / 2^256 + 2^256 · 2^-512`, `corrWorst` the
correctness error of the scheme with uniform noise rows and the XOF matrix, at
the collision term `3 / 2^256 + collWeight` of that scheme, at the seed term
`(2^256)⁻¹`, and at the one-wayness terms `owTermStd b + 2 · xofHop`: two
module-LWE and two extended module-LWE advantages at a uniform matrix of the
reductions `qRedEncF`, `qRedExtF` with polynomial oracles `polyGp`, `polyJp`,
`polyHp`, `polyTp`, `polyFp`, the message term `2^-256`, twice the `PRF_η` hop,
the averaged decryption error, and twice the XOF hop. No condition on the table
appears. -/
theorem mlkem512_qindcca_prf_coll (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (hpk : MLWE_PKE_Basic.PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eC : MLKEM512CT ≃ Fin c) (eKa : Bytes32 ≃ Fin a) [NeZero c] [NeZero a]
    [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]
    (A : KEMQAdv (m₁ + m₂) prfM prfN w q k c a (MLWE_PKE_Basic.PK mlkem512Params.toBasic)
      MLKEM512CT Bytes32) :
    (avg fun F : Fin prfM → Fin prfN =>
      qINDCCAAdvantageF (prfScheme eD512 (kgX e) enc512 mlkem512CompressedScheme.dec eK id F)
        hpk eG eJ eKR512 eC eKa F A) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (6 * (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK).corrWorst +
          514 / 2 ^ 256 + 2 ^ 256 * 2⁻¹ ^ 512)
        (3 * (2 ^ 256)⁻¹ +
          collWeight (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK))
        (2 ^ 256)⁻¹
        (owTermStd mlkem512Params mlkem512Compress mlkem512Decompress eD512 (kgX e) enc512
            mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG) (polyJp eJ)
            polyHp polyTp polyFp true A + 2 * xofHop)
        (owTermStd mlkem512Params mlkem512Compress mlkem512Decompress eD512 (kgX e) enc512
            mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG) (polyJp eJ)
            polyHp polyTp polyFp false A + 2 * xofHop) := by
  have h := avg_qINDCCAF_le_std_coll mlkem512Params mlkem512Compress mlkem512Decompress eD512
    (kgX e) enc512 mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG)
    (polyJp eJ) polyHp polyTp polyFp xofHop (kgX_close e) avg_enc512 A 512
  have h514 : (((512 + 2 : ℕ) : ℝ≥0∞)) = 514 := by norm_num
  simp only [card_bytes32, mlkem512_message_card, h514, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

open scoped Classical in
/-- **`mlkem512_qindcca_prf_coll` under the correctness bound `hWorst` (assumed
bound).** With `Λ = decryptionFailureProb mlkem512Noise δ_c` bounding the
correctness error of `mlkem512CompressedScheme`, the averaged IND-CCA advantage is
at most `chainBound` at the failure term `6 (Λ + xofHop) + 514 / 2^256 + 2^256 · 2^-512`,
the collision term `3 / 2^256 + collWeight` of the scheme with uniform noise rows
and the XOF matrix, the seed term `(2^256)⁻¹` and the one-wayness terms
`owTermWorst`. -/
theorem mlkem512_qindcca_prf_worst_coll (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (hpk : MLWE_PKE_Basic.PK mlkem512Params.toBasic → Bytes32)
    (eG : (mlkem512Params.PT × Bytes32) ≃ Fin m₁) (eJ : (Bytes32 × MLKEM512CT) ≃ Fin m₂)
    (eC : MLKEM512CT ≃ Fin c) (eKa : Bytes32 ≃ Fin a) [NeZero c] [NeZero a]
    [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]
    (A : KEMQAdv (m₁ + m₂) prfM prfN w q k c a (MLWE_PKE_Basic.PK mlkem512Params.toBasic)
      MLKEM512CT Bytes32) (δ_c : ℝ≥0∞)
    (hWorst : mlkem512CompressedScheme.corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c) :
    (avg fun F : Fin prfM → Fin prfN =>
      qINDCCAAdvantageF (prfScheme eD512 (kgX e) enc512 mlkem512CompressedScheme.dec eK id F)
        hpk eG eJ eKR512 eC eKa F A) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (6 * (decryptionFailureProb mlkem512Noise δ_c + xofHop) +
          514 / 2 ^ 256 + 2 ^ 256 * 2⁻¹ ^ 512)
        (3 * (2 ^ 256)⁻¹ +
          collWeight (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK))
        (2 ^ 256)⁻¹
        (owTermWorst e hpk eG eJ eC eKa A δ_c true)
        (owTermWorst e hpk eG eJ eC eKa A δ_c false) := by
  have hI : (idealScheme (kgX e) enc512 mlkem512CompressedScheme.dec eK).corrWorst ≤
      decryptionFailureProb mlkem512Noise δ_c + xofHop :=
    (corrWorst_ideal_kgX_le e).trans (add_le_add hWorst le_rfl)
  have hc := avg_corrErr_prfScheme_le eD512 (kgX e) enc512 mlkem512CompressedScheme.dec eK
  simp only [card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at hc
  have hT : ∀ b, owTermStd mlkem512Params mlkem512Compress mlkem512Decompress eD512 (kgX e)
      enc512 mlkem512CompressedScheme.dec eK hpk eG eJ eKR512 eC eKa (polyGp eG) (polyJp eJ)
      polyHp polyTp polyFp b A + 2 * xofHop ≤ owTermWorst e hpk eG eJ eC eKa A δ_c b := by
    intro b
    unfold owTermStd owTermWorst
    rw [mlkem512_message_card, Nat.cast_pow, Nat.cast_ofNat]
    gcongr
    exact hc.trans (add_le_add hI le_rfl)
  refine (mlkem512_qindcca_prf_coll e hpk eG eJ eC eKa A).trans
    (chainBound_mono_keyed _ _ _ _ ?_ (hT true) (hT false))
  gcongr

end MLKEM512

end CatCrypt.Crypto.MLKEM.MLKEM512QROMPrf

end

end

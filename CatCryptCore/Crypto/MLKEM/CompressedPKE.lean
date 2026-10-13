/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLKEM512Params
public import CatCryptCore.Crypto.KEM.FIPS203Security
public import CatCryptCore.Crypto.MLKEM.FOFromMLWE
public import CatCryptCore.Crypto.MLKEM.CorrectnessBounds
public import CatCryptCore.Crypto.MLKEM.Compress

/-!
# The MLWE PKE with FIPS 203 ciphertext compression

A public-key encryption scheme `S` composed with a ciphertext map `f : C → C'` and a
left map `g : C' → C` is the scheme `mapCiphertext S f g` that encrypts as `f ∘ S.enc`
and decrypts as `S.dec ∘ g`. Its IND-CPA game against an adversary `A` is the IND-CPA
game of `S` against `cpaReduction f A`, the adversary that applies `f` to the
challenge ciphertext before passing it to `A`; the two advantages are equal.

FIPS 203 K-PKE is the base MLWE PKE with `u` compressed coefficientwise by
`Compress_{d_u}` and `v` by `Compress_{d_v}`, and decryption decompressing both
components before decoding. `compressCT` and `decompressCT` are these maps on the
rank-`k` ciphertext, built from `Compress.compress_d` and `Compress.decompress_d`.

## Main definitions

* `mapCiphertext S f g` — the scheme `S` with ciphertexts post-processed by `f` and
  pre-processed by `g` before decryption
* `cpaReduction f A` — the IND-CPA adversary against `S` built from an IND-CPA
  adversary `A` against `mapCiphertext S f g`
* `compressCT k du dv`, `decompressCT k du dv` — FIPS 203 ciphertext compression and
  decompression at rank `k`
* `Adversary P C'`, `advC`, `advD`, `redC1`, `redC2`, `redD1`, `redD2` — the IND-CCA
  adversary against the FIPS 203 KEM over `mapCiphertext (toScheme P) f g` and the
  module-LWE reductions built from it
* `mlkem512CompressedScheme` — `mapCiphertext (toScheme mlkem512Params)` at the
  ML-KEM-512 compression parameters `d_u = 10`, `d_v = 4`

## Main results

* `indcpaGame_mapCiphertext`, `indcpaAdvantage_mapCiphertext` — IND-CPA of
  `mapCiphertext S f g` against `A` is IND-CPA of `S` against `cpaReduction f A`
* `indcpaAdvantage_mapCiphertext_le_mlwe` — the IND-CPA advantage against
  `mapCiphertext (toScheme P) f g` is bounded by two module-LWE and two extended
  module-LWE advantages
* `fips203_indcca_mapCiphertext_of_corr` — the IND-CCA bound of the FIPS 203 KEM over
  `mapCiphertext (toScheme P) f g`, with the correctness error bounded by `δ`
* `mlkem512_du`, `mlkem512_dv` — the compression parameters against
  `ConcreteParams.MLKEM512Params`
* `mlkem512Compressed_indcca` — the IND-CCA bound of the FIPS 203 KEM over
  `mlkem512CompressedScheme`

## The model

* `mlkem512Compressed_indcca` takes the worst-case correctness bound
  `mlkem512CompressedScheme.corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c` as
  the hypothesis `hWorst`. The decryption error of the compressed scheme consists of
  the noise `e·r − s·e₁ + e₂` and the rounding error of `Compress_{d_u}` and
  `Compress_{d_v}`, which `Compress.roundtrip_error_int` bounds per coefficient.
* The ciphertext of `mlkem512CompressedScheme` is the pair of compressed coefficient
  vectors returned by `compressCT`, without the FIPS 203 `ByteEncode` byte encoding.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.CompressedPKE

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

/-! ## Ciphertext post-processing -/

section MapCiphertext

variable {PK SK M C C' R : Type}

/-- The scheme `S` with every ciphertext mapped by `f` after encryption and by `g`
before decryption. -/
def mapCiphertext (S : Scheme PK SK M C R) (f : C → C') (g : C' → C) :
    Scheme PK SK M C' R where
  keygen := S.keygen
  enc pk m r := f (S.enc pk m r)
  dec sk c := S.dec sk (g c)

/-- The IND-CPA adversary against a scheme with ciphertexts `C` built from an IND-CPA
adversary `A` with ciphertexts `C'`: the first stage of `A`, and the second stage of
`A` on the challenge ciphertext mapped by `f`. -/
def cpaReduction (f : C → C') (A : INDCPAAdversary PK M C') : INDCPAAdversary PK M C where
  St := A.St
  choose := A.choose
  guess st c := A.guess st (f c)

variable [Fintype R] [Nonempty R]

/-- The IND-CPA game of `mapCiphertext S f g` against `A` is the IND-CPA game of `S`
against `cpaReduction f A`. -/
theorem indcpaGame_mapCiphertext (S : Scheme PK SK M C R) (f : C → C') (g : C' → C)
    (A : INDCPAAdversary PK M C') (b : Bool) :
    indcpaGame (mapCiphertext S f g) A b = indcpaGame S (cpaReduction f A) b := by
  simp only [indcpaGame, Scheme.encDist, mapCiphertext, cpaReduction, PMF.bind_map,
    Function.comp_def]

/-- The IND-CPA advantage against `mapCiphertext S f g` is the IND-CPA advantage
against `S` of `cpaReduction f A`. -/
theorem indcpaAdvantage_mapCiphertext (S : Scheme PK SK M C R) (f : C → C') (g : C' → C)
    (A : INDCPAAdversary PK M C') :
    indcpaAdvantage (mapCiphertext S f g) A = indcpaAdvantage S (cpaReduction f A) := by
  simp only [indcpaAdvantage, indcpaGame_mapCiphertext]

end MapCiphertext

/-! ## FIPS 203 compression of the ciphertext -/

/-- `Compress_d` on each of the 256 coefficients of a polynomial. -/
def compressPoly (d : ℕ) (a : Fin 256 → ZMod Compress.q) : Fin 256 → ZMod (2 ^ d) :=
  fun i => Compress.compress_d d (a i)

/-- `Decompress_d` on each of the 256 coefficients of a polynomial. -/
def decompressPoly (d : ℕ) (a : Fin 256 → ZMod (2 ^ d)) : Fin 256 → ZMod Compress.q :=
  fun i => Compress.decompress_d d (a i)

/-- The compressed ciphertext at rank `k`: `k` polynomials with `du`-bit coefficients
and one polynomial with `dv`-bit coefficients. -/
abbrev CompressedCT (k du dv : ℕ) : Type :=
  (Fin k → Fin 256 → ZMod (2 ^ du)) × (Fin 256 → ZMod (2 ^ dv))

/-- FIPS 203 ciphertext compression at rank `k`: `u` by `Compress_{du}` and `v` by
`Compress_{dv}`, coefficientwise. -/
def compressCT (k du dv : ℕ)
    (c : (Fin k → Fin 256 → ZMod Compress.q) × (Fin 256 → ZMod Compress.q)) :
    CompressedCT k du dv :=
  (fun j => compressPoly du (c.1 j), compressPoly dv c.2)

/-- FIPS 203 ciphertext decompression at rank `k`: `u` by `Decompress_{du}` and `v` by
`Decompress_{dv}`, coefficientwise. -/
def decompressCT (k du dv : ℕ) (c : CompressedCT k du dv) :
    (Fin k → Fin 256 → ZMod Compress.q) × (Fin 256 → ZMod Compress.q) :=
  (fun j => decompressPoly du (c.1 j), decompressPoly dv c.2)

/-! ## IND-CPA and IND-CCA over a post-processed MLWE PKE -/

variable (P : MLWE_PKE_Scheme.Params) {C' : Type} (f : CT P.toBasic → C')
  (g : C' → CT P.toBasic)

/-- The IND-CPA advantage against `mapCiphertext (toScheme P) f g` is bounded by two
module-LWE advantages of `B1_st` and two extended module-LWE advantages of
`B2_ext_st` at the adversary `cpaReduction f A`. -/
theorem indcpaAdvantage_mapCiphertext_le_mlwe
    (A : INDCPAAdversary (PK P.toBasic) P.PT C') :
    indcpaAdvantage (mapCiphertext (toScheme P) f g) A ≤
      MLWE.advantage P.toBasic.toParams
          (B1_st P.toBasic (choose_st P (cpaReduction f A)) (guess_st P (cpaReduction f A))
            true) +
        MLWE_Ext_advantage P.toBasic
          (B2_ext_st P.toBasic (choose_st P (cpaReduction f A))
            (guess_st P (cpaReduction f A)) true) +
        MLWE_Ext_advantage P.toBasic
          (B2_ext_st P.toBasic (choose_st P (cpaReduction f A))
            (guess_st P (cpaReduction f A)) false) +
        MLWE.advantage P.toBasic.toParams
          (B1_st P.toBasic (choose_st P (cpaReduction f A)) (guess_st P (cpaReduction f A))
            false) := by
  rw [indcpaAdvantage_mapCiphertext]
  exact indcpaAdvantage_le_mlwe P (cpaReduction f A)

variable {K Hash Z : Type} [Fintype K] [Nonempty K] [Fintype Z] [Nonempty Z]
  [DecidableEq Hash] [DecidableEq Z] [DecidableEq C'] {qRO qD : ℕ}

/-- The two-oracle IND-CCA adversary against the FIPS 203 KEM over a scheme with the
key and message spaces of `toScheme P` and ciphertexts `C'`, with random oracle
`G : PT × Hash → K × Seed`, rejection oracle `J : Z × C' → K`, at most `qRO`
random-oracle queries and at most `qD` decapsulation queries. -/
abbrev Adversary (P : MLWE_PKE_Scheme.Params) (C' K Hash Z : Type) (qRO qD : ℕ) : Type 1 :=
  ROM2INDCCAAdversary (PK P.toBasic) K C' (P.PT × Hash) (K × P.Seed) (Z × C') K qRO qD

variable (hpk : PK P.toBasic → Hash)

/-- The IND-CPA adversary against `toScheme P` built from `B`: `cpaReduction f` of
`owToIndcpa` of the OW-CPA adversary `tReductionC` at the OW-PCA reduction
`redROM`, all over `mapCiphertext (toScheme P) f g`. -/
noncomputable def advC (B : Adversary P C' K Hash Z qRO qD) :
    INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic) :=
  cpaReduction f (owToIndcpa (tReductionC (mapCiphertext (toScheme P) f g)
    (redROM (mapCiphertext (toScheme P) f g) hpk B)))

/-- The IND-CPA adversary against `toScheme P` built from `B`: `cpaReduction f` of
`owToIndcpa` of the OW-CPA adversary `tReductionD` at the OW-PCA reduction `redROM`
with log bound `qRO + qRO`, all over `mapCiphertext (toScheme P) f g`. -/
noncomputable def advD (B : Adversary P C' K Hash Z qRO qD) :
    INDCPAAdversary (PK P.toBasic) P.PT (CT P.toBasic) :=
  cpaReduction f (owToIndcpa (tReductionD (mapCiphertext (toScheme P) f g)
    (redROM (mapCiphertext (toScheme P) f g) hpk B) (qRO + qRO)))

/-- The module-LWE reduction `B1_st` at bit `b` for the adversary `advC P f g hpk B`. -/
noncomputable def redC1 (B : Adversary P C' K Hash Z qRO qD) (b : Bool) :
    P.Mat → P.Vec → SDistr Bool :=
  B1_st P.toBasic (choose_st P (advC P f g hpk B)) (guess_st P (advC P f g hpk B)) b

/-- The extended module-LWE reduction `B2_ext_st` at bit `b` for the adversary
`advC P f g hpk B`. -/
noncomputable def redC2 (B : Adversary P C' K Hash Z qRO qD) (b : Bool) :
    P.Mat → P.Vec → P.Vec → P.R → SDistr Bool :=
  B2_ext_st P.toBasic (choose_st P (advC P f g hpk B)) (guess_st P (advC P f g hpk B)) b

/-- The module-LWE reduction `B1_st` at bit `b` for the adversary `advD P f g hpk B`. -/
noncomputable def redD1 (B : Adversary P C' K Hash Z qRO qD) (b : Bool) :
    P.Mat → P.Vec → SDistr Bool :=
  B1_st P.toBasic (choose_st P (advD P f g hpk B)) (guess_st P (advD P f g hpk B)) b

/-- The extended module-LWE reduction `B2_ext_st` at bit `b` for the adversary
`advD P f g hpk B`. -/
noncomputable def redD2 (B : Adversary P C' K Hash Z qRO qD) (b : Bool) :
    P.Mat → P.Vec → P.Vec → P.R → SDistr Bool :=
  B2_ext_st P.toBasic (choose_st P (advD P f g hpk B)) (guess_st P (advD P f g hpk B)) b

omit [DecidableEq C'] in
/-- The OW-CPA advantage of an adversary `A` against `mapCiphertext (toScheme P) f g`
is bounded by the four module-LWE terms at `cpaReduction f (owToIndcpa A)`, the
message-space term `1/|PT|` and the correctness error `δ`. -/
theorem owcpa_mapCiphertext_le (A : PK P.toBasic → C' → PMF P.PT) (δ : ℝ≥0∞)
    (hErr : (mapCiphertext (toScheme P) f g).corrErr ≤ δ) :
    owcpaAdvantage (mapCiphertext (toScheme P) f g) A ≤
      MLWE.advantage P.toBasic.toParams
          (B1_st P.toBasic (choose_st P (cpaReduction f (owToIndcpa A)))
            (guess_st P (cpaReduction f (owToIndcpa A))) true) +
        MLWE_Ext_advantage P.toBasic
          (B2_ext_st P.toBasic (choose_st P (cpaReduction f (owToIndcpa A)))
            (guess_st P (cpaReduction f (owToIndcpa A))) true) +
        MLWE_Ext_advantage P.toBasic
          (B2_ext_st P.toBasic (choose_st P (cpaReduction f (owToIndcpa A)))
            (guess_st P (cpaReduction f (owToIndcpa A))) false) +
        MLWE.advantage P.toBasic.toParams
          (B1_st P.toBasic (choose_st P (cpaReduction f (owToIndcpa A)))
            (guess_st P (cpaReduction f (owToIndcpa A))) false) +
        (Fintype.card P.PT : ℝ≥0∞)⁻¹ + δ := by
  refine (owcpa_le_indcpa (mapCiphertext (toScheme P) f g) A).trans ?_
  gcongr
  exact indcpaAdvantage_mapCiphertext_le_mlwe P f g (owToIndcpa A)

/-- **The FIPS 203 KEM over the post-processed MLWE PKE is IND-CCA secure from
module-LWE in the classical random-oracle model.** For every two-oracle IND-CCA
adversary `B` against `fips203 (mapCiphertext (toScheme P) f g) hpk` asking at most
`qRO` random-oracle queries, the advantage is bounded by the module-LWE advantages of
`redC1`, `redD1`, the extended module-LWE advantages of `redC2`, `redD2`, the
message-space terms `1/|PT|`, the seed term `qRO/|Z|` and the correctness bound `δ`
of the post-processed scheme. -/
theorem fips203_indcca_mapCiphertext_of_corr (B : Adversary P C' K Hash Z qRO qD)
    (δ : ℝ≥0∞) (hWorst : (mapCiphertext (toScheme P) f g).corrWorst ≤ δ) :
    rom2INDCCAAdvantage (fips203 (mapCiphertext (toScheme P) f g) hpk) B ≤
      (MLWE.advantage P.toBasic.toParams (redC1 P f g hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P f g hpk B true) +
          MLWE_Ext_advantage P.toBasic (redC2 P f g hpk B false) +
          MLWE.advantage P.toBasic.toParams (redC1 P f g hpk B false) +
          (Fintype.card P.PT : ℝ≥0∞)⁻¹ + δ) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * δ + δ +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) *
          (MLWE.advantage P.toBasic.toParams (redD1 P f g hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P f g hpk B true) +
            MLWE_Ext_advantage P.toBasic (redD2 P f g hpk B false) +
            MLWE.advantage P.toBasic.toParams (redD1 P f g hpk B false) +
            (Fintype.card P.PT : ℝ≥0∞)⁻¹ + δ) +
        (qRO : ℝ≥0∞) / Fintype.card Z + δ := by
  have hErr : (mapCiphertext (toScheme P) f g).corrErr ≤ δ :=
    (Scheme.corrErr_le_corrWorst _).trans hWorst
  refine (fips203_indcca (mapCiphertext (toScheme P) f g) hpk B).trans ?_
  gcongr
  · exact owcpa_mapCiphertext_le P f g _ δ hErr
  · exact owcpa_mapCiphertext_le P f g _ δ hErr

/-! ## The instance at ML-KEM-512 -/

open MLKEM512Instance (mlkem512Params)
open CatCrypt.Crypto.MLKEM.CorrectnessBounds (decryptionFailureProb mlkem512Noise)

/-- The ML-KEM-512 compressed ciphertext: two polynomials with `d_u`-bit coefficients
and one polynomial with `d_v`-bit coefficients. -/
abbrev MLKEM512CT : Type :=
  CompressedCT 2 ConcreteParams.MLKEM512Params.d_u ConcreteParams.MLKEM512Params.d_v

/-- FIPS 203 ciphertext compression at the ML-KEM-512 parameters. -/
def mlkem512Compress : CT mlkem512Params.toBasic → MLKEM512CT :=
  compressCT 2 ConcreteParams.MLKEM512Params.d_u ConcreteParams.MLKEM512Params.d_v

/-- FIPS 203 ciphertext decompression at the ML-KEM-512 parameters. -/
def mlkem512Decompress : MLKEM512CT → CT mlkem512Params.toBasic :=
  decompressCT 2 ConcreteParams.MLKEM512Params.d_u ConcreteParams.MLKEM512Params.d_v

/-- The ML-KEM-512 K-PKE: the base MLWE PKE at `mlkem512Params` with the ciphertext
compressed at `d_u = 10`, `d_v = 4`, and decryption decompressing before decoding. -/
noncomputable def mlkem512CompressedScheme :
    Scheme (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
      mlkem512Params.PT MLKEM512CT mlkem512Params.Seed :=
  mapCiphertext (toScheme mlkem512Params) mlkem512Compress mlkem512Decompress

/-- The vector component is compressed at `d_u = 10`. -/
theorem mlkem512_du : ConcreteParams.MLKEM512Params.d_u = 10 := rfl

/-- The scalar component is compressed at `d_v = 4`. -/
theorem mlkem512_dv : ConcreteParams.MLKEM512Params.d_v = 4 := rfl

/-- Decryption in `mlkem512CompressedScheme` decompresses the ciphertext and decrypts
it in the base scheme. -/
theorem mlkem512Compressed_dec (sk : MLWE_PKE_Basic.SK mlkem512Params.toBasic)
    (c : MLKEM512CT) :
    mlkem512CompressedScheme.dec sk c = (toScheme mlkem512Params).dec sk (mlkem512Decompress c) :=
  rfl

/-- The IND-CCA advantage against the FIPS 203 KEM over `mlkem512CompressedScheme`,
in the classical random-oracle model, bounded by module-LWE advantages of named
reductions at the ML-KEM-512 ring and noise parameters. The decryption-failure bound
`hWorst` of the compressed scheme is a hypothesis. -/
theorem mlkem512Compressed_indcca {K Hash Z : Type} [Fintype K] [Nonempty K] [Fintype Z]
    [Nonempty Z] [DecidableEq Hash] [DecidableEq Z] {qRO qD : ℕ}
    (hpk : PK mlkem512Params.toBasic → Hash)
    (B : Adversary mlkem512Params MLKEM512CT K Hash Z qRO qD) (δ_c : ℝ≥0∞)
    (hWorst : mlkem512CompressedScheme.corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c) :
    rom2INDCCAAdvantage (fips203 mlkem512CompressedScheme hpk) B ≤
      (MLWE.advantage mlkem512Params.toBasic.toParams
            (redC1 mlkem512Params mlkem512Compress mlkem512Decompress hpk B true) +
          MLWE_Ext_advantage mlkem512Params.toBasic
            (redC2 mlkem512Params mlkem512Compress mlkem512Decompress hpk B true) +
          MLWE_Ext_advantage mlkem512Params.toBasic
            (redC2 mlkem512Params mlkem512Compress mlkem512Decompress hpk B false) +
          MLWE.advantage mlkem512Params.toBasic.toParams
            (redC1 mlkem512Params mlkem512Compress mlkem512Decompress hpk B false) +
          (Fintype.card mlkem512Params.PT : ℝ≥0∞)⁻¹ + (256 : ℝ≥0∞) * δ_c) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * ((256 : ℝ≥0∞) * δ_c) + (256 : ℝ≥0∞) * δ_c +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) *
          (MLWE.advantage mlkem512Params.toBasic.toParams
              (redD1 mlkem512Params mlkem512Compress mlkem512Decompress hpk B true) +
            MLWE_Ext_advantage mlkem512Params.toBasic
              (redD2 mlkem512Params mlkem512Compress mlkem512Decompress hpk B true) +
            MLWE_Ext_advantage mlkem512Params.toBasic
              (redD2 mlkem512Params mlkem512Compress mlkem512Decompress hpk B false) +
            MLWE.advantage mlkem512Params.toBasic.toParams
              (redD1 mlkem512Params mlkem512Compress mlkem512Decompress hpk B false) +
            (Fintype.card mlkem512Params.PT : ℝ≥0∞)⁻¹ + (256 : ℝ≥0∞) * δ_c) +
        (qRO : ℝ≥0∞) / Fintype.card Z + (256 : ℝ≥0∞) * δ_c := by
  have h := fips203_indcca_mapCiphertext_of_corr mlkem512Params mlkem512Compress
    mlkem512Decompress hpk B _ hWorst
  rwa [CorrectnessBounds.mlkem512_failure_from_coeff] at h

end CatCrypt.Crypto.MLKEM.CompressedPKE

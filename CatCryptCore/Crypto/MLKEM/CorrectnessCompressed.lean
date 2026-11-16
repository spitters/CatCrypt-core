/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.CorrectnessTail
public import CatCryptCore.Crypto.MLKEM.CompressedPKE

/-!
# The decryption-failure bound of ML-KEM-768 with ciphertext compression

`mlkem768CompressedScheme` is the base MLWE public-key encryption scheme at `mlkem768Params`
with the ciphertext compressed at `d_u = 10`, `d_v = 4`. Its correctness error is at most
`256 · 2⁻⁹⁸ = 2⁻⁹⁰`.

Decryption of the compressed ciphertext decodes `msgEncode m + N + c_v`, where `c_v` is the
rounding error of `v` and `N = e · r + e₂ − s · (e₁ + c_u)` with `c_u` the rounding error of
`u = Aᵀ r + e₁`. The rounding error `c_v` is bounded in the worst case by
`Compress.errorBound 4 = 104`, so a failure has a coefficient with `728 ≤ |N_i|`.

The rounding error `c_u` is not bounded in the worst case. Given the matrix and `r`, the
vector `w = Aᵀ r` is fixed, `c_u` at a coefficient is a function of `w + e₁` at that
coefficient, and `s` and `e₁` are independent of `w`. Coefficient `i` of `s · (e₁ + c_u)` is a
signed sum of `256 k` products `s_l · y_{i−l}` with distinct coordinates of `s` and of `e₁`,
so its moment-generating function, conditionally on `r`, is a product of `256 k` factors
`E[τ^(s · (x + c(w + x)))]`, each at most the maximum of `roundMgf` over `w`. The bound uses
no assumption on the distribution of the ciphertext and no computational step.

## Main definitions

* `mlkem768CompressedScheme` — the ML-KEM-768 K-PKE with compressed ciphertexts
* `roundErr d x` — the rounding error of `Decompress_d ∘ Compress_d` at `x`, as an integer
* `sgnDot i X Y` — coefficient `i` of the dot product of two integer vectors in the
  negacyclic ring, over `ℤ`
* `compNoise du A c` — the noise `e · r + e₂ − s · (u' − Aᵀ r)` of the coins `c` under the
  matrix `A`, where `u'` is the decompressed `u`
* `roundMgf du τ w` — the moment-generating factor of one product `s · (x + c(w + x))`

## Main results

* `exists_large_compNoise_of_failure` — the decode lemma with compression
* `sdExp_sgnDot_le` — the product bound on the moment-generating function of a signed dot
  product with independent uniform windows
* `compNoise_tail_le` — the Chernoff bound for one coefficient of the compressed noise
* `mlkem768Compressed_coeff_tail_le` — at ML-KEM-768 the bound is `2⁻⁹⁸`
* `mlkem768Compressed_corrWorst_le` — the hypothesis `hWorst` of the compressed scheme,
  `corrWorst ≤ decryptionFailureProb mlkem768Noise 2⁻⁹⁸`
* `mlkem768Compressed_corrWorst_le_two_pow` — `corrWorst ≤ 2⁻⁹⁰`
-/

@[expose] public section

set_option autoImplicit false

/-! ## The ML-KEM-768 instance of the compressed scheme -/

namespace CatCrypt.Crypto.MLKEM.CompressedPKE

open CatCrypt.Crypto.PKE.Games
open MLWE_PKE_Basic (PK CT)
open MLWE_PKE_Scheme (toScheme)
open MLKEMRankInstance (mlkem768Params)

/-- The ML-KEM-768 compressed ciphertext: three polynomials with `d_u`-bit coefficients
and one polynomial with `d_v`-bit coefficients. -/
abbrev MLKEM768CT : Type :=
  CompressedCT ConcreteParams.MLKEM768Params.k ConcreteParams.MLKEM768Params.d_u
    ConcreteParams.MLKEM768Params.d_v

/-- FIPS 203 ciphertext compression at the ML-KEM-768 parameters. -/
def mlkem768Compress : CT mlkem768Params.toBasic → MLKEM768CT :=
  compressCT ConcreteParams.MLKEM768Params.k ConcreteParams.MLKEM768Params.d_u
    ConcreteParams.MLKEM768Params.d_v

/-- FIPS 203 ciphertext decompression at the ML-KEM-768 parameters. -/
def mlkem768Decompress : MLKEM768CT → CT mlkem768Params.toBasic :=
  decompressCT ConcreteParams.MLKEM768Params.k ConcreteParams.MLKEM768Params.d_u
    ConcreteParams.MLKEM768Params.d_v

/-- The ML-KEM-768 K-PKE: the base MLWE PKE at `mlkem768Params` with the ciphertext
compressed at `d_u = 10`, `d_v = 4`, and decryption decompressing before decoding. -/
noncomputable def mlkem768CompressedScheme :
    Scheme (PK mlkem768Params.toBasic) (MLWE_PKE_Basic.SK mlkem768Params.toBasic)
      mlkem768Params.PT MLKEM768CT mlkem768Params.Seed :=
  mapCiphertext (toScheme mlkem768Params) mlkem768Compress mlkem768Decompress

end CatCrypt.Crypto.MLKEM.CompressedPKE

namespace CatCrypt.Crypto.MLKEM.MLKEMRankInstance

open CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Util
open MLKEM512Instance (Rq Msg PrfBlock samplePoly msgEncode msgDecode)
open SamplerCbd (Win windowVal windowMap samplePoly_eq uniform_windowVal)
open CatCrypt.Crypto.MLKEM.Compress (centeredAbs errorBound)
open CatCrypt.Crypto.MLKEM.CompressedPKE (compressPoly decompressPoly compressCT decompressCT
  mapCiphertext)
open CatCrypt.Crypto.MLKEM.CorrectnessBounds (decryptionFailureProb mlkem768Noise
  mlkem768_failure_from_coeff)
open scoped ENNReal NNReal

/-! ## Expectations under uniform distributions -/

/-- The expectation under a uniform distribution is invariant under an equivalence. -/
theorem sdExp_uniform_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (σ : α ≃ β) (g : β → ℝ≥0∞) :
    sdExp (SDistr.uniform α) (fun a => g (σ a)) = sdExp (SDistr.uniform β) g := by
  have h := SDistr.uniform_bind_equiv_comp σ (fun b => SDistr.pure b)
  have h2 : sdExp ((SDistr.uniform α).bind fun a => SDistr.pure (σ a)) g =
      sdExp ((SDistr.uniform β).bind fun b => SDistr.pure b) g := by rw [h]
  simpa only [sdExp_bind, sdExp_pure] using h2

/-- The expectation under the uniform distribution on a product is the iterated
expectation. -/
theorem sdExp_uniform_prod {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α × β → ℝ≥0∞) :
    sdExp (SDistr.uniform (α × β)) g =
      sdExp (SDistr.uniform α) fun a => sdExp (SDistr.uniform β) fun b => g (a, b) := by
  rw [← SDistr.uniform_nested_eq_prod]
  simp only [sdExp_bind, sdExp_pure]

/-- Two expectations commute. -/
theorem sdExp_comm {α β : Type} (d : SDistr α) (d' : SDistr β) (g : α → β → ℝ≥0∞) :
    sdExp d (fun a => sdExp d' (g a)) = sdExp d' fun b => sdExp d fun a => g a b := by
  simp only [sdExp, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  grind

/-- The expectation of a product of functions of the coordinates of a uniform function is
the product of the expectations. -/
theorem sdExp_uniform_pi_prod {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α]
    [Nonempty α] (f : ι → α → ℝ≥0∞) :
    sdExp (SDistr.uniform (ι → α)) (fun X => ∏ i, f i (X i)) =
      ∏ i, sdExp (SDistr.uniform α) (f i) := by
  simp only [sdExp_uniform, tsum_fintype, PMF.uniformFintype_apply, Fintype.card_fun,
    ← Finset.mul_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Fintype.prod_sum, Nat.cast_pow, ENNReal.inv_pow]

/-- The base of a power of a sum, as a product in `ℝ≥0∞`. -/
theorem coe_zpow_sum {ι : Type} (s : Finset ι) {t : ℝ≥0} (ht : t ≠ 0) (a : ι → ℤ) :
    ((t ^ (∑ i ∈ s, a i) : ℝ≥0) : ℝ≥0∞) = ∏ i ∈ s, ((t ^ a i : ℝ≥0) : ℝ≥0∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add₀ ht,
      ENNReal.coe_mul, ih]

/-! ## The decode lemma with compression -/

/-- The rounding error of `Decompress_d ∘ Compress_d` at `x`, as the integer of least
absolute value. -/
def roundErr (d : ℕ) (x : Zq3329) : ℤ :=
  (Compress.decompress_d d (Compress.compress_d d x) - x).valMinAbs

/-- The decompressed compressed value is `x` plus the rounding error. -/
theorem decompress_compress_eq (d : ℕ) (x : Zq3329) :
    Compress.decompress_d d (Compress.compress_d d x) = x + Zq3329.fromInt (roundErr d x) := by
  simp only [roundErr, Zq3329.fromInt, ZMod.coe_valMinAbs]
  ring

/-- The centred absolute value is subadditive. -/
theorem centeredAbs_add_le (a b : Zq3329) :
    centeredAbs (a + b) ≤ centeredAbs a + centeredAbs b := by
  simp only [centeredAbs, Compress.q, ← ZMod.valMinAbs_natAbs_eq_min]
  exact (ZMod.natAbs_valMinAbs_add_le a b).trans (Int.natAbs_add_le _ _)

/-- The noise of the compressed scheme of the coins `c` under the matrix `A`, before the
rounding of `v`: `e · r + e₂ − s · (u' − Aᵀ r)`, where `u'` is `u = Aᵀ r + e₁` after
compression and decompression at `du` bits. -/
def compNoise {k η₁ η₂ : ℕ} (du : ℕ) (A : Mat k) (c : Coins k η₁ η₂) : Rq :=
  vecDot (sampleVec k η₁ c.1.2) (sampleVec k η₁ c.2.1) + samplePoly η₂ c.2.2.2 -
    vecDot (sampleVec k η₁ c.1.1)
      ((fun j => decompressPoly du (compressPoly du
          (vecAdd (matVecMul (matTranspose A) (sampleVec k η₁ c.2.1)) (sampleVec k η₂ c.2.2.1)
            j))) - matVecMul (matTranspose A) (sampleVec k η₁ c.2.1))

/-- The compressed decryption value: `v' − s · u'` is the encoded message plus the noise
`compNoise` and the rounding error of `v`. -/
theorem compressed_dec_eq {k η₁ η₂ : ℕ} (du : ℕ) (A : Mat k) (c : Coins k η₁ η₂)
    (m : Msg) (v v' : Rq) (hv : v = MLKEM512Instance.ringAdd (MLKEM512Instance.ringAdd
      (vecDot (vecAdd (matVecMul A (sampleVec k η₁ c.1.1)) (sampleVec k η₁ c.1.2))
        (sampleVec k η₁ c.2.1)) (samplePoly η₂ c.2.2.2)) (msgEncode m)) :
    MLKEM512Instance.ringSub v' (vecDot (sampleVec k η₁ c.1.1)
      (fun j => decompressPoly du (compressPoly du
          (vecAdd (matVecMul (matTranspose A) (sampleVec k η₁ c.2.1)) (sampleVec k η₂ c.2.2.1)
            j)))) =
      msgEncode m + (compNoise du A c + (v' - v)) := by
  subst hv
  unfold compNoise
  set w := matVecMul (matTranspose A) (sampleVec k η₁ c.2.1)
  set u' : Vec k := fun j => decompressPoly du (compressPoly du
    (vecAdd w (sampleVec k η₂ c.2.2.1) j))
  have h := decrypt_noise_eq A (sampleVec k η₁ c.1.1) (sampleVec k η₁ c.1.2)
    (sampleVec k η₁ c.2.1) (u' - w) (samplePoly η₂ c.2.2.2) m
  rw [show vecAdd w (u' - w) = u' by simp [vecAdd]] at h
  simp only [MLKEM512Instance.ringSub, MLKEM512Instance.ringAdd] at h ⊢
  linear_combination h

/-- The MLWE PKE at rank `k` and noise parameters `η₁`, `η₂` with the ciphertext compressed
at `du`, `dv` bits. -/
noncomputable abbrev compScheme (k η₁ η₂ du dv : ℕ) :=
  mapCiphertext (MLWE_PKE_Scheme.toScheme (paramsOfRankEta k η₁ η₂)) (compressCT k du dv)
    (decompressCT k du dv)

/-- **The decode lemma with compression.** If decryption of a compressed honest encryption
fails, some coefficient of `compNoise` has centred absolute value at least
`832 − errorBound dv`. -/
theorem exists_large_compNoise_of_failure (k η₁ η₂ du dv : ℕ) (hdv : 1 ≤ dv) (hdv12 : dv ≤ 12)
    (A : Mat k) (c : Coins k η₁ η₂) (m : Msg)
    (h : (compScheme k η₁ η₂ du dv).dec (sampleVec k η₁ c.1.1)
      ((compScheme k η₁ η₂ du dv).enc
        (A, vecAdd (matVecMul A (sampleVec k η₁ c.1.1)) (sampleVec k η₁ c.1.2)) m c.2) ≠
        some m) :
    ∃ i, 832 - errorBound dv ≤ centeredAbs (compNoise du A c i) := by
  set v := MLKEM512Instance.ringAdd (MLKEM512Instance.ringAdd
      (vecDot (vecAdd (matVecMul A (sampleVec k η₁ c.1.1)) (sampleVec k η₁ c.1.2))
        (sampleVec k η₁ c.2.1)) (samplePoly η₂ c.2.2.2)) (msgEncode m) with hv
  have h' : msgDecode (MLKEM512Instance.ringSub (decompressPoly dv (compressPoly dv v))
      (vecDot (sampleVec k η₁ c.1.1) (fun j => decompressPoly du (compressPoly du
        (vecAdd (matVecMul (matTranspose A) (sampleVec k η₁ c.2.1))
          (sampleVec k η₂ c.2.2.1) j))))) ≠ m := fun he => h (Eq.trans rfl (congrArg some he))
  rw [compressed_dec_eq du A c m v _ hv] at h'
  obtain ⟨i, hi⟩ := exists_large_of_msgDecode_ne m _ h'
  refine ⟨i, ?_⟩
  have hc : centeredAbs ((decompressPoly dv (compressPoly dv v) - v) i) ≤ errorBound dv :=
    Compress.decompress_compress_centered dv hdv hdv12 (v i)
  have := (centeredAbs_add_le (compNoise du A c i) _).trans' (le_of_le_of_eq hi rfl)
  grind

/-! ## The noise over the integers -/

/-- Coefficient `i` of the dot product of two vectors over the negacyclic ring, computed
over `ℤ`: `Σ_j Σ_l ± X_{j,l} Y_{j,i−l}`, with sign `−1` exactly when `l > i`. -/
def sgnDot {k : ℕ} (i : Fin 256) (X Y : Fin k → Fin 256 → ℤ) : ℤ :=
  ∑ j, ∑ l, if l.val ≤ i.val then X j l * Y j (i - l) else -(X j l * Y j (i - l))

/-- The dot product of the reductions of two integer vectors is the reduction of
`sgnDot`. -/
theorem vecDot_fromInt_apply {k : ℕ} (X Y : Fin k → Fin 256 → ℤ) (i : Fin 256) :
    vecDot (fun j l => Zq3329.fromInt (X j l)) (fun j l => Zq3329.fromInt (Y j l)) i =
      Zq3329.fromInt (sgnDot i X Y) := by
  simp only [vecDot, Finset.sum_apply, MLKEM512Instance.ringMul,
    CatCrypt.Crypto.Lattice.SignedNegacyclicConv.signedNegaConv, sgnDot, Zq3329.fromInt,
    Int.cast_sum, apply_ite (Int.cast (R := ZMod 3329)), Int.cast_neg, Int.cast_mul]

/-- The window values of a vector of PRF blocks. -/
def wvals {k : ℕ} (η : ℕ) (x : PrfVecBlock k η) : Fin k → Fin 256 → ℤ :=
  fun j l => windowVal (wvec η x j l)

/-- A sampled vector is the reduction of its window values. -/
theorem sampleVec_eq_fromInt {k : ℕ} (η : ℕ) (x : PrfVecBlock k η) :
    sampleVec k η x = fun j l => Zq3329.fromInt (wvals η x j l) := by
  funext j l
  simp [sampleVec, samplePoly_eq, wvals, wvec]

/-- The integer form of coefficient `i` of `compNoise`, as a function of the window values
`S`, `E`, `R`, `X` of `s`, `e`, `r`, `e₁` and the value `z` of `e₂` at `i`. -/
def compNoiseInt {k : ℕ} (du : ℕ) (A : Mat k) (i : Fin 256) (S E R X : Fin k → Fin 256 → ℤ)
    (z : ℤ) : ℤ :=
  sgnDot i E R + z - sgnDot i S (fun j l => X j l +
    roundErr du (matVecMul (matTranspose A) (fun j l => Zq3329.fromInt (R j l)) j l +
      Zq3329.fromInt (X j l)))

/-- Coefficient `i` of `compNoise` is the reduction of `compNoiseInt`. -/
theorem compNoise_apply {k η₁ η₂ : ℕ} (du : ℕ) (A : Mat k) (c : Coins k η₁ η₂) (i : Fin 256) :
    compNoise du A c i = Zq3329.fromInt (compNoiseInt du A i (wvals η₁ c.1.1) (wvals η₁ c.1.2)
      (wvals η₁ c.2.1) (wvals η₂ c.2.2.1) (windowVal (windowMap η₂ c.2.2.2 i))) := by
  have hu : ∀ w : Vec k, ((fun j => decompressPoly du (compressPoly du
      (vecAdd w (fun j l => Zq3329.fromInt (wvals η₂ c.2.2.1 j l)) j))) - w) =
      fun j l => Zq3329.fromInt (wvals η₂ c.2.2.1 j l +
        roundErr du (w j l + Zq3329.fromInt (wvals η₂ c.2.2.1 j l))) := by
    intro w
    funext j l
    simp only [Pi.sub_apply, decompressPoly, compressPoly, vecAdd, Pi.add_apply,
      decompress_compress_eq, Zq3329.fromInt, Int.cast_add]
    ring
  rw [compNoise, sampleVec_eq_fromInt η₁ c.2.1, sampleVec_eq_fromInt η₂ c.2.2.1, hu,
    sampleVec_eq_fromInt η₁ c.1.1, sampleVec_eq_fromInt η₁ c.1.2, samplePoly_eq]
  simp only [Pi.sub_apply, Pi.add_apply, vecDot_fromInt_apply, compNoiseInt]
  simp only [Zq3329.fromInt, Int.cast_add, Int.cast_sub]

/-! ## The moment-generating function of a signed dot product -/

/-- The expectation over a uniform window of a function of its value is the expectation
under `cbd η`. -/
theorem sdExp_uniform_windowVal (η : ℕ) (g : ℤ → ℝ≥0∞) :
    sdExp (SDistr.uniform (Win η)) (fun u => g (windowVal u)) = sdExp (cbd η) g := by
  rw [← uniform_windowVal, sdExp_bind]
  simp only [sdExp_pure]

/-- The expectation of `τ ^ (± u · y)` over a uniform window `u` of width `2` is
`cbdTwoMgf (τ ^ y)`. -/
theorem sdExp_windowVal_sign (p : Prop) [Decidable p] {τ : ℝ≥0} (y : ℤ) :
    sdExp (SDistr.uniform (Win 2)) (fun u =>
      ((τ ^ (if p then windowVal u * y else -(windowVal u * y)) : ℝ≥0) : ℝ≥0∞)) =
      cbdTwoMgf (τ ^ y) := by
  have hcbd := sdExp_uniform_windowVal 2
  rw [← mgfZ_cbd_two]
  by_cases hp : p
  · simp only [hp, ite_true]
    rw [hcbd fun x => ((τ ^ (x * y) : ℝ≥0) : ℝ≥0∞)]
    simp only [mgfZ, mul_comm _ y, zpow_mul]
  · simp only [hp, ite_false]
    rw [hcbd fun x => ((τ ^ (-(x * y)) : ℝ≥0) : ℝ≥0∞), mgfZ]
    conv_rhs => rw [← cbd_symm 2, sdExp_bind]
    simp only [sdExp_pure, mul_comm _ y, zpow_mul, zpow_neg]

/-- The expectation over a uniform window vector `V` of a product of functions of the
coordinates `V_{j,i−l}` is the product of the expectations. -/
theorem sdExp_uniform_reidx {k : ℕ} (i : Fin 256) (ψ : Fin k → Fin 256 → Win 2 → ℝ≥0∞) :
    sdExp (SDistr.uniform (WinVec k 2)) (fun V => ∏ j, ∏ l, ψ j l (V j (i - l))) =
      ∏ j, ∏ l, sdExp (SDistr.uniform (Win 2)) (ψ j l) := by
  have hre : ∀ (g : Fin 256 → ℝ≥0∞), ∏ l, g (i - l) = ∏ l, g l := fun g =>
    Fintype.prod_equiv (Equiv.subLeft i) _ _ fun l => rfl
  have h1 : ∀ V : WinVec k 2, ∏ j, ∏ l, ψ j l (V j (i - l)) =
      ∏ j, ∏ l, ψ j (i - l) (V j l) := fun V => Finset.prod_congr rfl fun j _ => by
    rw [← hre fun l => ψ j l (V j (i - l))]
    simp only [sub_sub_cancel]
  simp only [h1]
  rw [sdExp_uniform_pi_prod (fun j (Y : Fin 256 → Win 2) => ∏ l, ψ j (i - l) (Y l))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [sdExp_uniform_pi_prod, hre fun l => sdExp (SDistr.uniform (Win 2)) (ψ j l)]

/-- **The product bound for a signed dot product.** For independent uniform window vectors
`U`, `V` of width `2` and integer functions `f j l` of the coordinates of `V`, the
moment-generating function of `sgnDot i (windowVal ∘ U) (f ∘ V)` at `τ` is at most `K ^ (256 k)`
when every factor `E_v[cbdTwoMgf (τ ^ f j l v)]` is at most `K`. -/
theorem sdExp_sgnDot_le {k : ℕ} (i : Fin 256) {τ : ℝ≥0} (hτ : τ ≠ 0)
    (f : Fin k → Fin 256 → Win 2 → ℤ) (K : ℝ≥0∞)
    (hK : ∀ j l, sdExp (SDistr.uniform (Win 2)) (fun v => (cbdTwoMgf (τ ^ f j l v) : ℝ≥0∞)) ≤ K) :
    sdExp (SDistr.uniform (WinVec k 2)) (fun U => sdExp (SDistr.uniform (WinVec k 2)) fun V =>
      ((τ ^ sgnDot i (fun j l => windowVal (U j l)) (fun j l => f j l (V j l)) : ℝ≥0) : ℝ≥0∞))
      ≤ K ^ (k * 256) := by
  set φ : Fin k → Fin 256 → Win 2 → Win 2 → ℝ≥0∞ := fun j l u v =>
    ((τ ^ (if l.val ≤ i.val then windowVal u * f j (i - l) v
      else -(windowVal u * f j (i - l) v)) : ℝ≥0) : ℝ≥0∞) with hφ
  have h1 : ∀ U V : WinVec k 2, ((τ ^ sgnDot i (fun j l => windowVal (U j l))
      (fun j l => f j l (V j l)) : ℝ≥0) : ℝ≥0∞) = ∏ j, ∏ l, φ j l (U j l) (V j (i - l)) := by
    intro U V
    simp only [sgnDot, coe_zpow_sum _ hτ, hφ]
  have h2 : ∀ U : WinVec k 2, sdExp (SDistr.uniform (WinVec k 2))
      (fun V => ∏ j, ∏ l, φ j l (U j l) (V j (i - l))) =
      ∏ j, ∏ l, sdExp (SDistr.uniform (Win 2)) (φ j l (U j l)) :=
    fun U => sdExp_uniform_reidx i fun j l => φ j l (U j l)
  simp only [h1, h2]
  rw [sdExp_uniform_pi_prod
    (fun j (Y : Fin 256 → Win 2) => ∏ l, sdExp (SDistr.uniform (Win 2)) (φ j l (Y l)))]
  rw [Finset.prod_congr rfl fun j _ => sdExp_uniform_pi_prod
    (fun l (u : Win 2) => sdExp (SDistr.uniform (Win 2)) (φ j l u))]
  calc _ ≤ ∏ _j : Fin k, ∏ _l : Fin 256, K := by
        gcongr with j _ l _
        rw [sdExp_comm]
        simp only [hφ, sdExp_windowVal_sign]
        exact hK j (i - l)
    _ = K ^ (k * 256) := by simp [Finset.prod_const, ← pow_mul, mul_comm]

/-- `sdExp_sgnDot_le` over uniform vectors of PRF blocks, read through their windows. -/
theorem sdExp_sgnDot_block_le {k : ℕ} (i : Fin 256) {τ : ℝ≥0} (hτ : τ ≠ 0)
    (f : Fin k → Fin 256 → Win 2 → ℤ) (K : ℝ≥0∞)
    (hK : ∀ j l, sdExp (SDistr.uniform (Win 2)) (fun v => (cbdTwoMgf (τ ^ f j l v) : ℝ≥0∞)) ≤ K) :
    sdExp (SDistr.uniform (PrfVecBlock k 2)) (fun x =>
      sdExp (SDistr.uniform (PrfVecBlock k 2)) fun y =>
        ((τ ^ sgnDot i (wvals 2 x) (fun j l => f j l (wvec 2 y j l)) : ℝ≥0) : ℝ≥0∞)) ≤
      K ^ (k * 256) := by
  calc _ = sdExp (SDistr.uniform (WinVec k 2)) (fun U =>
        sdExp (SDistr.uniform (WinVec k 2)) fun V =>
          ((τ ^ sgnDot i (fun j l => windowVal (U j l)) (fun j l => f j l (V j l)) : ℝ≥0) :
            ℝ≥0∞)) := by
        rw [← sdExp_uniform_equiv (vecEquiv k 2 two_pos)]
        refine congrArg _ (funext fun x => ?_)
        rw [← sdExp_uniform_equiv (vecEquiv k 2 two_pos)]
        rfl
    _ ≤ _ := sdExp_sgnDot_le i hτ f K hK

/-- The expectation over a uniform PRF block of a function of the value of window `i` is the
expectation under `cbd η`. -/
theorem sdExp_uniform_block_windowVal (η : ℕ) (hη : 0 < η) (i : Fin 256) (g : ℤ → ℝ≥0∞) :
    sdExp (SDistr.uniform (PrfBlock η)) (fun b => g (windowVal (windowMap η b i))) =
      sdExp (cbd η) g := by
  calc _ = sdExp (SDistr.uniform (Fin 256 → Win η)) (fun Z => g (windowVal (Z i))) :=
        sdExp_uniform_equiv (blockEquiv η hη) fun Z => g (windowVal (Z i))
    _ = _ := by
        rw [← uniform_eval_windowVal η i, sdExp_bind]
        simp only [sdExp_pure]

/-- The moment-generating factor of one product `s · (x + c(w + x))` at base `τ`, for
independent `cbd 2` draws `s`, `x` and the rounding error `c = roundErr du`. -/
noncomputable def roundMgf (du : ℕ) (τ : ℝ≥0) (w : Zq3329) : ℝ≥0 :=
  let h : ℤ → ℝ≥0 := fun x => cbdTwoMgf (τ ^ (x + roundErr du (w + Zq3329.fromInt x)))
  2⁻¹ ^ 4 * (h (-2) + 4 * h (-1) + 6 * h 0 + 4 * h 1 + h 2)

/-- `roundMgf` is the expectation over a uniform window. -/
theorem sdExp_roundMgf (du : ℕ) (τ : ℝ≥0) (w : Zq3329) :
    sdExp (SDistr.uniform (Win 2)) (fun v => (cbdTwoMgf (τ ^ (windowVal v +
      roundErr du (w + Zq3329.fromInt (windowVal v)))) : ℝ≥0∞)) = roundMgf du τ w := by
  rw [sdExp_uniform_windowVal 2 fun x =>
    ((cbdTwoMgf (τ ^ (x + roundErr du (w + Zq3329.fromInt x))) : ℝ≥0) : ℝ≥0∞),
    sdExp_cbd_two_coe]
  rfl

/-- The expectation over a uniform window of `cbdTwoMgf (τ ^ v)` is `cbdProdTwoMgf τ`. -/
theorem sdExp_cbdProdTwoMgf (τ : ℝ≥0) :
    sdExp (SDistr.uniform (Win 2)) (fun v => (cbdTwoMgf (τ ^ windowVal v) : ℝ≥0∞)) =
      cbdProdTwoMgf τ := by
  rw [sdExp_uniform_windowVal 2 fun x => ((cbdTwoMgf (τ ^ x) : ℝ≥0) : ℝ≥0∞),
    sdExp_cbd_two_coe]
  rfl

/-- **The moment-generating function of the compressed noise.** Under uniform coins and a
fixed matrix `A`, the moment-generating function at `τ` of coefficient `i` of the
compressed noise over `ℤ` is at most `cbdProdTwoMgf τ ^ (256 k) · cbdTwoMgf τ · K ^ (256 k)`,
where `K` bounds `roundMgf du τ⁻¹ w` for every `w`. -/
theorem sdExp_compNoiseInt_le {k : ℕ} (du : ℕ) (A : Mat k) (i : Fin 256) {τ : ℝ≥0}
    (hτ : τ ≠ 0) (K : ℝ≥0) (hK : ∀ w, roundMgf du τ⁻¹ w ≤ K) :
    sdExp (SDistr.uniform (Coins k 2 2)) (fun c => ((τ ^ compNoiseInt du A i (wvals 2 c.1.1)
      (wvals 2 c.1.2) (wvals 2 c.2.1) (wvals 2 c.2.2.1) (windowVal (windowMap 2 c.2.2.2 i)) :
        ℝ≥0) : ℝ≥0∞)) ≤
      (cbdProdTwoMgf τ : ℝ≥0∞) ^ (k * 256) * cbdTwoMgf τ * (K : ℝ≥0∞) ^ (k * 256) := by
  set Y : PrfVecBlock k 2 → PrfVecBlock k 2 → Fin k → Fin 256 → ℤ := fun r x j l =>
    wvals 2 x j l + roundErr du (matVecMul (matTranspose A)
      (fun j l => Zq3329.fromInt (wvals 2 r j l)) j l + Zq3329.fromInt (wvals 2 x j l)) with hY
  set a : PrfVecBlock k 2 → PrfVecBlock k 2 → ℝ≥0∞ := fun e r =>
    ((τ ^ sgnDot i (wvals 2 e) (wvals 2 r) : ℝ≥0) : ℝ≥0∞) with ha
  set b : PrfVecBlock k 2 → PrfVecBlock k 2 → PrfVecBlock k 2 → ℝ≥0∞ := fun s r x =>
    ((τ⁻¹ ^ sgnDot i (wvals 2 s) (Y r x) : ℝ≥0) : ℝ≥0∞) with hb
  have hpt : ∀ s e r x (z : PrfBlock 2), ((τ ^ compNoiseInt du A i (wvals 2 s) (wvals 2 e)
      (wvals 2 r) (wvals 2 x) (windowVal (windowMap 2 z i)) : ℝ≥0) : ℝ≥0∞) =
      a e r * b s r x * ((τ ^ windowVal (windowMap 2 z i) : ℝ≥0) : ℝ≥0∞) := by
    intro s e r x z
    rw [ha, hb, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    congr 1
    rw [compNoiseInt, zpow_sub₀ hτ, zpow_add₀ hτ, inv_zpow, div_eq_mul_inv]
    ring
  have hz : sdExp (SDistr.uniform (PrfBlock 2))
      (fun z => ((τ ^ windowVal (windowMap 2 z i) : ℝ≥0) : ℝ≥0∞)) = cbdTwoMgf τ :=
    (sdExp_uniform_block_windowVal 2 two_pos i _).trans (mgfZ_cbd_two τ)
  simp only [sdExp_uniform_prod, hpt, sdExp_mul_left, hz]
  set U := SDistr.uniform (PrfVecBlock k 2)
  have hB : ∀ r, sdExp U (fun s => sdExp U fun x => b s r x) ≤ (K : ℝ≥0∞) ^ (k * 256) := by
    intro r
    refine sdExp_sgnDot_block_le i (inv_ne_zero hτ) (fun j l v => windowVal v +
      roundErr du (matVecMul (matTranspose A) (fun j l => Zq3329.fromInt (wvals 2 r j l)) j l +
        Zq3329.fromInt (windowVal v))) _ fun j l => ?_
    rw [sdExp_roundMgf]
    exact_mod_cast hK _
  have hA : sdExp U (fun e => sdExp U (a e)) ≤ (cbdProdTwoMgf τ : ℝ≥0∞) ^ (k * 256) :=
    sdExp_sgnDot_block_le i hτ (fun _ _ v => windowVal v) _ fun _ _ =>
      (sdExp_cbdProdTwoMgf τ).le
  calc _ = sdExp U (fun e => sdExp U fun r =>
        a e r * cbdTwoMgf τ * sdExp U (fun s => sdExp U fun x => b s r x)) := by
        rw [sdExp_comm]
        refine congrArg _ (funext fun e => ?_)
        rw [sdExp_comm]
        refine congrArg _ (funext fun r => ?_)
        simp only [sdExp_mul_right, sdExp_mul_left]
        ring
    _ ≤ sdExp U (fun e => sdExp U fun r => a e r * cbdTwoMgf τ * (K : ℝ≥0∞) ^ (k * 256)) :=
        sdExp_mono _ fun e => sdExp_mono _ fun r => mul_le_mul_right (hB r) _
    _ = sdExp U (fun e => sdExp U (a e)) * (cbdTwoMgf τ * (K : ℝ≥0∞) ^ (k * 256)) := by
        simp only [mul_assoc, sdExp_mul_right]
    _ ≤ (cbdProdTwoMgf τ : ℝ≥0∞) ^ (k * 256) * (cbdTwoMgf τ * (K : ℝ≥0∞) ^ (k * 256)) :=
        mul_le_mul_left hA _
    _ = _ := by ring

/-! ## The tail bound -/

/-- `cbdTwoMgf` is invariant under inversion of the base. -/
theorem cbdTwoMgf_inv (u : ℝ≥0) : cbdTwoMgf u⁻¹ = cbdTwoMgf u := by
  simp only [cbdTwoMgf, inv_zpow', neg_neg, neg_zero]
  ring

/-- `cbdProdTwoMgf` is invariant under inversion of the base. -/
theorem cbdProdTwoMgf_inv (u : ℝ≥0) : cbdProdTwoMgf u⁻¹ = cbdProdTwoMgf u := by
  simp only [cbdProdTwoMgf, inv_zpow, cbdTwoMgf_inv]

/-- `roundMgf` is invariant under inversion of the base. -/
theorem roundMgf_inv (du : ℕ) (u : ℝ≥0) (w : Zq3329) : roundMgf du u⁻¹ w = roundMgf du u w := by
  simp only [roundMgf, inv_zpow, cbdTwoMgf_inv]

/-- The pointwise two-sided Markov inequality: for `1 ≤ t`, the indicator of `a ≤ |z|` is
at most `(t ^ z + t⁻¹ ^ z) · t⁻ᵃ`. -/
theorem indicator_le_zpow (a : ℕ) {t : ℝ≥0} (ht : 1 ≤ t) (z : ℤ) :
    (if a ≤ z.natAbs then (1 : ℝ≥0∞) else 0) ≤
      (((t ^ z : ℝ≥0) : ℝ≥0∞) + ((t⁻¹ ^ z : ℝ≥0) : ℝ≥0∞)) * ((t⁻¹ ^ a : ℝ≥0) : ℝ≥0∞) := by
  have h := sdExp_tail_le (SDistr.pure z) a ht
  simpa only [mgfZ, sdExp_pure] using h

/-- **Tail bound for one coefficient of the compressed noise.** For a fixed matrix `A`, a
threshold `T`, a base `1 ≤ t` and a bound `K` on `roundMgf du t`, the probability under
uniform coins that coefficient `i` of `compNoise du A` has centred absolute value at least `T`
is at most `2 · cbdProdTwoMgf t ^ (256 k) · cbdTwoMgf t · K ^ (256 k) · t⁻ᵀ`. -/
theorem compNoise_tail_le {k : ℕ} (du : ℕ) (A : Mat k) (i : Fin 256) (T : ℕ) {t : ℝ≥0}
    (ht : 1 ≤ t) (K : ℝ≥0) (hK : ∀ w, roundMgf du t w ≤ K) :
    (PMF.uniformFintype (Coins k 2 2)).toOuterMeasure
        {c | T ≤ centeredAbs (compNoise du A c i)} ≤
      2 * ((cbdProdTwoMgf t : ℝ≥0∞) ^ (k * 256) * cbdTwoMgf t * (K : ℝ≥0∞) ^ (k * 256)) *
        ((t⁻¹ ^ T : ℝ≥0) : ℝ≥0∞) := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
  have hK' : ∀ w, roundMgf du t⁻¹ w ≤ K := fun w => (roundMgf_inv du t w).le.trans (hK w)
  have hK'' : ∀ w, roundMgf du t⁻¹⁻¹ w ≤ K := by simpa only [inv_inv] using hK
  set Z : Coins k 2 2 → ℤ := fun c => compNoiseInt du A i (wvals 2 c.1.1) (wvals 2 c.1.2)
    (wvals 2 c.2.1) (wvals 2 c.2.2.1) (windowVal (windowMap 2 c.2.2.2 i)) with hZ
  calc _ = sdExp (SDistr.uniform (Coins k 2 2))
        (fun c => if T ≤ centeredAbs (compNoise du A c i) then 1 else 0) := by
        rw [sdExp_uniform, PMF.toOuterMeasure_apply]
        refine tsum_congr fun c => ?_
        by_cases hc : T ≤ centeredAbs (compNoise du A c i) <;>
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, hc, ite_true, ite_false, mul_one,
            mul_zero]
    _ ≤ sdExp (SDistr.uniform (Coins k 2 2)) (fun c => (((t ^ Z c : ℝ≥0) : ℝ≥0∞) +
        ((t⁻¹ ^ Z c : ℝ≥0) : ℝ≥0∞)) * ((t⁻¹ ^ T : ℝ≥0) : ℝ≥0∞)) := by
        refine sdExp_mono _ fun c => le_trans ?_ (indicator_le_zpow T ht (Z c))
        have h1 := centeredAbs_fromInt_le (Z c)
        have h2 : compNoise du A c i = Zq3329.fromInt (Z c) := compNoise_apply du A c i
        rw [h2]
        split_ifs <;> first | omega | simp
    _ = (sdExp (SDistr.uniform (Coins k 2 2)) (fun c => ((t ^ Z c : ℝ≥0) : ℝ≥0∞)) +
        sdExp (SDistr.uniform (Coins k 2 2)) (fun c => ((t⁻¹ ^ Z c : ℝ≥0) : ℝ≥0∞))) *
          ((t⁻¹ ^ T : ℝ≥0) : ℝ≥0∞) := by
        rw [sdExp_mul_right, sdExp_add]
    _ ≤ ((cbdProdTwoMgf t : ℝ≥0∞) ^ (k * 256) * cbdTwoMgf t * (K : ℝ≥0∞) ^ (k * 256) +
        (cbdProdTwoMgf t⁻¹ : ℝ≥0∞) ^ (k * 256) * cbdTwoMgf t⁻¹ * (K : ℝ≥0∞) ^ (k * 256)) *
          ((t⁻¹ ^ T : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        · exact sdExp_compNoiseInt_le du A i ht0 K hK'
        · exact sdExp_compNoiseInt_le du A i (inv_ne_zero ht0) K hK''
    _ = _ := by rw [cbdProdTwoMgf_inv, cbdTwoMgf_inv, two_mul]

/-! ## The union bound over the coefficients -/

/-- **The union bound for the compressed scheme.** If for every matrix and every
coefficient the compressed noise reaches `832 − errorBound dv` with probability at most `δ`
under uniform coins, the correctness error of the compressed scheme is at most `256 δ`. -/
theorem compScheme_corrWorst_le (k η₁ η₂ du dv : ℕ) (hdv : 1 ≤ dv) (hdv12 : dv ≤ 12)
    (δ : ℝ≥0∞) (hδ : ∀ (A : Mat k) (i : Fin 256),
      (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure
        {c | 832 - errorBound dv ≤ centeredAbs (compNoise du A c i)} ≤ δ) :
    (compScheme k η₁ η₂ du dv).corrWorst ≤ 256 * δ := by
  set T := 832 - errorBound dv
  have hkg : (compScheme k η₁ η₂ du dv).keygen = ((PMF.uniformFintype (Mat k)).bind fun A =>
      (PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₁)).map fun ks =>
        ((A, vecAdd (matVecMul A (sampleVec k η₁ ks.1)) (sampleVec k η₁ ks.2)),
          sampleVec k η₁ ks.1) : PMF (MLWE_PKE_Basic.PK (paramsOfRankEta k η₁ η₂).toBasic ×
            MLWE_PKE_Basic.SK (paramsOfRankEta k η₁ η₂).toBasic)) := rfl
  have hA : ∀ A : Mat k, ∑' ks, PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₁) ks *
      ⨆ m, (compScheme k η₁ η₂ du dv).failProb
        (A, vecAdd (matVecMul A (sampleVec k η₁ ks.1)) (sampleVec k η₁ ks.2))
        (sampleVec k η₁ ks.1) m ≤ 256 * δ := by
    intro A
    calc _ ≤ ∑' ks, PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₁) ks *
          (PMF.uniformFintype (PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂)).toOuterMeasure
            {sd | ∃ i, T ≤ centeredAbs (compNoise du A (ks, sd) i)} := by
          refine ENNReal.tsum_le_tsum fun ks => mul_le_mul_right (iSup_le fun m => ?_) _
          apply MeasureTheory.measure_mono
          intro sd hsd
          exact exists_large_compNoise_of_failure k η₁ η₂ du dv hdv hdv12 A (ks, sd) m hsd
      _ = (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure
            (⋃ i : Fin 256, {c | T ≤ centeredAbs (compNoise du A c i)}) := by
          refine Eq.symm ?_
          rw [PMF.uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply]
          simp only [PMF.toOuterMeasure_map_apply]
          congr 1
          funext ks
          congr 2
          ext sd
          simp
      _ ≤ ∑ i : Fin 256, (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure
            {c | T ≤ centeredAbs (compNoise du A c i)} :=
          MeasureTheory.measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin 256, δ := Finset.sum_le_sum fun i _ => hδ A i
      _ = 256 * δ := by simp
  unfold PKE.Games.Scheme.corrWorst
  rw [hkg, PMF.tsum_bind_mul]
  simp only [← PMF.tsum_mul_comp_eq_map]
  calc _ ≤ ∑' A : Mat k, PMF.uniformFintype (Mat k) A * (256 * δ) :=
        ENNReal.tsum_le_tsum fun A => mul_le_mul_right (hA A) _
    _ = 256 * δ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ## The numeric bound for ML-KEM-768 at `t = 6/5` -/

/-- `30 ^ 8 · (6/5) ^ m` as a natural number, for `|m| ≤ 8`, written with `Nat.pow`. -/
def powSixFifths (m : ℤ) : ℕ := Nat.pow 6 (8 + m).toNat * Nat.pow 5 (8 - m).toNat

/-- `16 · 30 ^ 8 · cbdTwoMgf ((6/5) ^ y)` as a natural number, for `|y| ≤ 4`. -/
def cbdTwoMgfNat (y : ℤ) : ℕ :=
  powSixFifths (-2 * y) + 4 * powSixFifths (-y) + 6 * powSixFifths 0 + 4 * powSixFifths y +
    powSixFifths (2 * y)

/-- `cbdTwoMgfNat y` is `16 · 30 ^ 8 · cbdTwoMgf ((6/5) ^ y)` for `|y| ≤ 4`. -/
theorem cbdTwoMgf_six_fifths (y : ℤ) (h1 : -4 ≤ y) (h2 : y ≤ 4) :
    cbdTwoMgf ((6 / 5) ^ y) = (cbdTwoMgfNat y : ℝ≥0) / (16 * 30 ^ 8) := by
  rw [← NNReal.coe_inj]
  interval_cases y <;>
    norm_num [cbdTwoMgf, cbdTwoMgfNat, powSixFifths]

/-- The rounding pattern of `Compress_10` at `w`: the five values `x + c(w + x)` for
`x ∈ [-2, 2]` lie in `[-4, 4]`, and their weighted `cbdTwoMgfNat` sum is at most
`256 · 30 ^ 8 · 13845841 / 12960000`. -/
def roundPatternOk (w : Zq3329) : Bool :=
  let p : ℤ → ℤ := fun x => x + roundErr 10 (w + Zq3329.fromInt x)
  decide (-4 ≤ p (-2) ∧ p (-2) ≤ 4 ∧ -4 ≤ p (-1) ∧ p (-1) ≤ 4 ∧ -4 ≤ p 0 ∧ p 0 ≤ 4 ∧
    -4 ≤ p 1 ∧ p 1 ≤ 4 ∧ -4 ≤ p 2 ∧ p 2 ≤ 4) &&
  decide (cbdTwoMgfNat (p (-2)) + 4 * cbdTwoMgfNat (p (-1)) + 6 * cbdTwoMgfNat (p 0) +
    4 * cbdTwoMgfNat (p 1) + cbdTwoMgfNat (p 2) ≤ 179442099360000)

/-- `roundErr 10` on the residue `y` of `ℕ`, computed with natural and integer division:
`Compress_10`, `Decompress_10` and the centred residue of their difference. -/
def roundErrNat (y : ℕ) : ℤ :=
  let c : ℕ := (1024 * y + 1664) / 3329 % 1024
  let x' : ℕ := (3329 * c + 512) / 1024 % 3329
  let r : ℕ := (((x' : ℤ) - y) % 3329).toNat
  if r ≤ 1664 then r else (r : ℤ) - 3329

/-- `roundPatternOk` on the representative `v` of `w`, over `ℕ` and `ℤ`. -/
def roundPatternOkNat (v : ℕ) : Bool :=
  let p : ℤ → ℤ := fun x => x + roundErrNat ((((v : ℤ) + x) % 3329).toNat)
  decide (-4 ≤ p (-2) ∧ p (-2) ≤ 4 ∧ -4 ≤ p (-1) ∧ p (-1) ≤ 4 ∧ -4 ≤ p 0 ∧ p 0 ≤ 4 ∧
    -4 ≤ p 1 ∧ p 1 ≤ 4 ∧ -4 ≤ p 2 ∧ p 2 ≤ 4) &&
  decide (cbdTwoMgfNat (p (-2)) + 4 * cbdTwoMgfNat (p (-1)) + 6 * cbdTwoMgfNat (p 0) +
    4 * cbdTwoMgfNat (p 1) + cbdTwoMgfNat (p 2) ≤ 179442099360000)

/-- `roundErr 10 y` is `roundErrNat` of the representative of `y`. -/
theorem roundErr_ten_eq (y : Zq3329) : roundErr 10 y = roundErrNat y.val := by
  have hc : (Compress.compress_d 10 y).val = (1024 * y.val + 1664) / 3329 % 1024 := by
    simp [Compress.compress_d, ZMod.val_natCast, Compress.q]
  have hd : (Compress.decompress_d 10 (Compress.compress_d 10 y)).val =
      (3329 * ((1024 * y.val + 1664) / 3329 % 1024) + 512) / 1024 % 3329 := by
    simp [Compress.decompress_d, ZMod.val_natCast, hc]
  have hr : (Compress.decompress_d 10 (Compress.compress_d 10 y) - y).val =
      ((((Compress.decompress_d 10 (Compress.compress_d 10 y)).val : ℤ) - y.val) %
        3329).toNat := by
    have e : Compress.decompress_d 10 (Compress.compress_d 10 y) - y =
        ((((Compress.decompress_d 10 (Compress.compress_d 10 y)).val : ℤ) - y.val : ℤ) :
          ZMod 3329) := by
      simp
    rw [e]
    have h := ZMod.val_intCast (n := 3329)
      (((Compress.decompress_d 10 (Compress.compress_d 10 y)).val : ℤ) - y.val)
    omega
  rw [roundErr, ZMod.valMinAbs_def_pos, hr, hd]
  simp only [roundErrNat, Compress.q]
  split_ifs <;> omega

/-- The representative of `w + x` is `(w.val + x) mod 3329`. -/
theorem val_add_fromInt (w : Zq3329) (x : ℤ) :
    (w + Zq3329.fromInt x).val = ((((w.val : ℤ) + x) % 3329).toNat) := by
  have e : w + Zq3329.fromInt x = (((w.val : ℤ) + x : ℤ) : ZMod 3329) := by
    simp [Zq3329.fromInt]
  rw [e]
  have h := ZMod.val_intCast (n := 3329) ((w.val : ℤ) + x)
  omega

/-- `roundPatternOk w` is `roundPatternOkNat` of the representative of `w`. -/
theorem roundPatternOk_eq (w : Zq3329) : roundPatternOk w = roundPatternOkNat w.val := by
  simp only [roundPatternOk, roundPatternOkNat, roundErr_ten_eq, val_add_fromInt]

set_option linter.style.native false in
/-- Every representative `v < 3329` has an admissible rounding pattern. -/
theorem roundPatternOkNat_all : (List.range 3329).all roundPatternOkNat = true := by
  native_decide

/-- Every `w` has an admissible rounding pattern. -/
theorem roundPatternOk_all : ∀ w : Zq3329, roundPatternOk w = true := by
  intro w
  rw [roundPatternOk_eq]
  have h := roundPatternOkNat_all
  rw [List.all_eq_true] at h
  exact h _ (List.mem_range.2 (ZMod.val_lt w))

/-- `roundMgf 10 (6/5) w` is at most `13845841 / 12960000` for every `w`. -/
theorem roundMgf_six_fifths_le (w : Zq3329) : roundMgf 10 (6 / 5) w ≤ 13845841 / 12960000 := by
  have h := roundPatternOk_all w
  simp only [roundPatternOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hN⟩ := h
  calc roundMgf 10 (6 / 5) w = ((cbdTwoMgfNat (-2 + roundErr 10 (w + Zq3329.fromInt (-2))) +
        4 * cbdTwoMgfNat (-1 + roundErr 10 (w + Zq3329.fromInt (-1))) +
        6 * cbdTwoMgfNat (0 + roundErr 10 (w + Zq3329.fromInt 0)) +
        4 * cbdTwoMgfNat (1 + roundErr 10 (w + Zq3329.fromInt 1)) +
        cbdTwoMgfNat (2 + roundErr 10 (w + Zq3329.fromInt 2)) : ℕ) : ℝ≥0) /
          (256 * 30 ^ 8) := by
        simp only [roundMgf, cbdTwoMgf_six_fifths _ h1 h2, cbdTwoMgf_six_fifths _ h3 h4,
          cbdTwoMgf_six_fifths _ h5 h6, cbdTwoMgf_six_fifths _ h7 h8,
          cbdTwoMgf_six_fifths _ h9 h10]
        push_cast
        ring
    _ ≤ ((179442099360000 : ℕ) : ℝ≥0) / (256 * 30 ^ 8) := by
        gcongr
    _ = 13845841 / 12960000 := by
        rw [← NNReal.coe_inj]
        norm_num

/-- `cbdProdTwoMgf (6/5) = 105433441 / 103680000`. -/
theorem cbdProdTwoMgf_six_fifths : cbdProdTwoMgf (6 / 5) = 105433441 / 103680000 := by
  rw [← NNReal.coe_inj]
  push_cast [cbdProdTwoMgf, cbdTwoMgf]
  norm_num

/-- `cbdTwoMgf (6/5) = 14641 / 14400`. -/
theorem cbdTwoMgf_six_fifths' : cbdTwoMgf (6 / 5) = 14641 / 14400 := by
  rw [← NNReal.coe_inj]
  push_cast [cbdTwoMgf]
  norm_num

/-- The rational inequality behind `mlkem768Compressed_chernoff_value`, with numerators and
denominators as natural-number variables. -/
theorem chernoffCompressed_of_nat {np dp nc dc nf df a b m : ℕ} (hdp : 0 < dp) (hdc : 0 < dc)
    (hdf : 0 < df) (hb : 0 < b) (hm : 0 < m)
    (h : 2 * np ^ 768 * nc * nf ^ 768 * a ^ 728 * m ≤ dp ^ 768 * dc * df ^ 768 * b ^ 728) :
    2 * (((np : ℝ) / dp) ^ 768 * (nc / dc) * ((nf : ℝ) / df) ^ 768) * ((a : ℝ) / b) ^ 728 ≤
      (m : ℝ)⁻¹ := by
  have hY : (0 : ℝ) < dp ^ 768 * dc * df ^ 768 * b ^ 728 := by positivity
  rw [show 2 * (((np : ℝ) / dp) ^ 768 * (nc / dc) * ((nf : ℝ) / df) ^ 768) * ((a : ℝ) / b) ^ 728 =
      (2 * np ^ 768 * nc * nf ^ 768 * a ^ 728 : ℝ) / (dp ^ 768 * dc * df ^ 768 * b ^ 728) by
      field_simp,
    div_le_iff₀ hY, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact_mod_cast h

set_option exponentiation.threshold 2000 in
/-- The cleared-denominator form of the compressed ML-KEM-768 Chernoff value at `t = 6/5`. -/
theorem mlkem768Compressed_chernoff_nat :
    2 * 105433441 ^ 768 * 14641 * 13845841 ^ 768 * 5 ^ 728 * 2 ^ 98 ≤
      103680000 ^ 768 * 14400 * 12960000 ^ 768 * 6 ^ 728 :=
  Nat.le_of_ble_eq_true rfl

/-- The per-coefficient Chernoff value of compressed ML-KEM-768 at `t = 6/5` is at most
`2⁻⁹⁸`. -/
theorem mlkem768Compressed_chernoff_value :
    2 * (cbdProdTwoMgf (6 / 5) ^ (3 * 256) * cbdTwoMgf (6 / 5) *
        (13845841 / 12960000 : ℝ≥0) ^ (3 * 256)) * (6 / 5 : ℝ≥0)⁻¹ ^ 728 ≤ (2 ^ 98)⁻¹ := by
  rw [cbdProdTwoMgf_six_fifths, cbdTwoMgf_six_fifths', ← NNReal.coe_le_coe]
  have key := chernoffCompressed_of_nat (np := 105433441) (dp := 103680000) (nc := 14641)
    (dc := 14400) (nf := 13845841) (df := 12960000) (a := 5) (b := 6) (m := 2 ^ 98)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
    mlkem768Compressed_chernoff_nat
  push_cast at key ⊢
  norm_num at key ⊢
  exact key

/-- **Tail bound for compressed ML-KEM-768.** For every matrix, one coefficient of the
compressed noise of ML-KEM-768 has centred absolute value at least `728` with probability at
most `2⁻⁹⁸`. -/
theorem mlkem768Compressed_coeff_tail_le (A : Mat 3) (i : Fin 256) :
    (PMF.uniformFintype (Coins 3 2 2)).toOuterMeasure
        {c | 728 ≤ centeredAbs (compNoise 10 A c i)} ≤ ((2 : ℝ≥0∞) ^ 98)⁻¹ := by
  have ht : (1 : ℝ≥0) ≤ 6 / 5 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  refine (compNoise_tail_le 10 A i 728 ht _ roundMgf_six_fifths_le).trans ?_
  have h := ENNReal.coe_le_coe.2 mlkem768Compressed_chernoff_value
  push_cast at h
  push_cast
  exact h

/-- **The decryption-failure hypothesis of compressed ML-KEM-768.** The correctness error of
`mlkem768CompressedScheme` is at most `decryptionFailureProb mlkem768Noise 2⁻⁹⁸`: this
discharges the worst-case failure hypothesis `hWorst` of the compressed scheme. The bound uses
no assumption on the distribution of the ciphertext and no computational step. -/
theorem mlkem768Compressed_corrWorst_le :
    CompressedPKE.mlkem768CompressedScheme.corrWorst ≤
      decryptionFailureProb mlkem768Noise ((2 : ℝ≥0∞) ^ 98)⁻¹ := by
  rw [mlkem768_failure_from_coeff]
  exact compScheme_corrWorst_le 3 2 2 10 4 (by norm_num) (by norm_num) _
    fun A i => mlkem768Compressed_coeff_tail_le A i

/-- The correctness error of `mlkem768CompressedScheme` is at most `2⁻⁹⁰`. -/
theorem mlkem768Compressed_corrWorst_le_two_pow :
    CompressedPKE.mlkem768CompressedScheme.corrWorst ≤ ((2 : ℝ≥0∞) ^ 90)⁻¹ := by
  refine mlkem768Compressed_corrWorst_le.trans (le_of_eq ?_)
  rw [mlkem768_failure_from_coeff, show (256 : ℝ≥0∞) = 2 ^ 8 by norm_num,
    show (2 : ℝ≥0∞) ^ 98 = 2 ^ 8 * 2 ^ 90 by rw [← pow_add],
    ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

end CatCrypt.Crypto.MLKEM.MLKEMRankInstance

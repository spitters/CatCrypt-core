/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.CorrectnessCompressed
public meta import CatCryptCore.Crypto.MLKEM.CorrectnessCompressed

/-!
# The decryption-failure bound of ML-KEM-512 with ciphertext compression

`mlkem512CompressedScheme` is the base MLWE public-key encryption scheme at the ML-KEM-512
parameters `k = 2`, `η₁ = 3`, `η₂ = 2` with the ciphertext compressed at `d_u = 10`,
`d_v = 4`. Its correctness error is at most `256 · 2⁻⁸⁸ = 2⁻⁸⁰`.

The argument is that of `CorrectnessCompressed` for ML-KEM-768, with the noise widths as
parameters. Coefficient `i` of the compressed noise `e · r + e₂ − s · (e₁ + c_u)` is a sum of
two signed dot products and one `cbd η₂` draw. The moment-generating function of the signed
dot product of a uniform window vector of width `η_U` with a function of an independent
uniform window vector of width `η_V` is a product of `256 k` factors
`E_v[mgfZ (cbd η_U) (τ ^ f v)]` (`sdExp_sgnDot_le_eta`). At ML-KEM-512, `e · r` has factors
`E_{y ∼ cbd 3}[mgfZ (cbd 3) (τ ^ y)]`, and `s · (e₁ + c_u)` has factors
`roundMgfEta 10 3 2 τ w = E_{x ∼ cbd 2}[mgfZ (cbd 3) (τ ^ (x + c(w + x)))]`.

At `τ = 6/5` and threshold `728` the per-coefficient bound is
`2 · P ^ 512 · M₂ · K ^ 512 · (5/6) ^ 728 ≤ 2⁻⁸⁸`, with
`P = 41887707090098041 / 40310784000000000`, `M₂ = 14641 / 14400` and
`K = 51520374361 / 46656000000` the maximum of `roundMgfEta 10 3 2 (6/5)` over `w`.

## Main definitions

* `roundMgfEta du η₁ η₂ τ w` — the moment-generating factor of one product
  `s · (x + c(w + x))` with `s ∼ cbd η₁` and `x ∼ cbd η₂`
* `cbdThreeMgf` — the moment-generating function of `cbd 3`

## Main results

* `sdExp_sgnDot_le_eta` — the product bound for a signed dot product of windows of two widths
* `compNoise_tail_le_eta` — the Chernoff bound for one coefficient of the compressed noise
* `mlkem512Compressed_coeff_tail_le` — at ML-KEM-512 the bound is `2⁻⁸⁸`
* `mlkem512Compressed_corrWorst_le` — the hypothesis `hWorst` of the compressed scheme,
  `corrWorst ≤ decryptionFailureProb mlkem512Noise 2⁻⁸⁸`
* `mlkem512Compressed_corrWorst_le_two_pow` — `corrWorst ≤ 2⁻⁸⁰`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MLKEMRankInstance

open CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Util
open MLKEM512Instance (Rq Msg PrfBlock samplePoly msgEncode msgDecode)
open SamplerCbd (Win windowVal windowMap samplePoly_eq uniform_windowVal)
open CatCrypt.Crypto.MLKEM.Compress (centeredAbs errorBound)
open CatCrypt.Crypto.MLKEM.CorrectnessBounds (decryptionFailureProb mlkem512Noise
  mlkem512_failure_from_coeff)
open scoped ENNReal NNReal

/-! ## Moment-generating functions of `cbd η` -/

/-- `mgfZ (cbd η)` is invariant under inversion of the base. -/
theorem mgfZ_cbd_inv (η : ℕ) (t : ℝ≥0) : mgfZ (cbd η) t⁻¹ = mgfZ (cbd η) t := by
  conv_rhs => rw [← cbd_symm η]
  simp only [mgfZ, sdExp_bind, sdExp_pure, inv_zpow']

/-- The expectation of `τ ^ (± u · y)` over a uniform window `u` of width `η` is
`mgfZ (cbd η) (τ ^ y)`. -/
theorem sdExp_windowVal_sign_eta (η : ℕ) (p : Prop) [Decidable p] {τ : ℝ≥0} (y : ℤ) :
    sdExp (SDistr.uniform (Win η)) (fun u =>
      ((τ ^ (if p then windowVal u * y else -(windowVal u * y)) : ℝ≥0) : ℝ≥0∞)) =
      mgfZ (cbd η) (τ ^ y) := by
  have hcbd := sdExp_uniform_windowVal η
  by_cases hp : p
  · simp only [hp, ite_true]
    rw [hcbd fun x => ((τ ^ (x * y) : ℝ≥0) : ℝ≥0∞)]
    simp only [mgfZ, mul_comm _ y, zpow_mul]
  · simp only [hp, ite_false]
    rw [hcbd fun x => ((τ ^ (-(x * y)) : ℝ≥0) : ℝ≥0∞), mgfZ]
    conv_rhs => rw [← cbd_symm η, sdExp_bind]
    simp only [sdExp_pure, mul_comm _ y, zpow_mul, zpow_neg]

/-! ## The moment-generating function of a signed dot product -/

/-- The expectation over a uniform window vector `V` of width `η` of a product of functions
of the coordinates `V_{j,i−l}` is the product of the expectations. -/
theorem sdExp_uniform_reidx_eta {k : ℕ} (η : ℕ) (i : Fin 256)
    (ψ : Fin k → Fin 256 → Win η → ℝ≥0∞) :
    sdExp (SDistr.uniform (WinVec k η)) (fun V => ∏ j, ∏ l, ψ j l (V j (i - l))) =
      ∏ j, ∏ l, sdExp (SDistr.uniform (Win η)) (ψ j l) := by
  have hre : ∀ (g : Fin 256 → ℝ≥0∞), ∏ l, g (i - l) = ∏ l, g l := fun g =>
    Fintype.prod_equiv (Equiv.subLeft i) _ _ fun l => rfl
  have h1 : ∀ V : WinVec k η, ∏ j, ∏ l, ψ j l (V j (i - l)) =
      ∏ j, ∏ l, ψ j (i - l) (V j l) := fun V => Finset.prod_congr rfl fun j _ => by
    rw [← hre fun l => ψ j l (V j (i - l))]
    simp only [sub_sub_cancel]
  simp only [h1]
  rw [sdExp_uniform_pi_prod (fun j (Y : Fin 256 → Win η) => ∏ l, ψ j (i - l) (Y l))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [sdExp_uniform_pi_prod, hre fun l => sdExp (SDistr.uniform (Win η)) (ψ j l)]

/-- **The product bound for a signed dot product of two widths.** For independent uniform
window vectors `U` of width `ηU` and `V` of width `ηV` and integer functions `f j l` of the
coordinates of `V`, the moment-generating function of
`sgnDot i (windowVal ∘ U) (f ∘ V)` at `τ` is at most `K ^ (256 k)` when every factor
`E_v[mgfZ (cbd ηU) (τ ^ f j l v)]` is at most `K`. -/
theorem sdExp_sgnDot_le_eta {k : ℕ} (ηU ηV : ℕ) (i : Fin 256) {τ : ℝ≥0} (hτ : τ ≠ 0)
    (f : Fin k → Fin 256 → Win ηV → ℤ) (K : ℝ≥0∞)
    (hK : ∀ j l, sdExp (SDistr.uniform (Win ηV)) (fun v => mgfZ (cbd ηU) (τ ^ f j l v)) ≤ K) :
    sdExp (SDistr.uniform (WinVec k ηU)) (fun U =>
      sdExp (SDistr.uniform (WinVec k ηV)) fun V =>
        ((τ ^ sgnDot i (fun j l => windowVal (U j l)) (fun j l => f j l (V j l)) : ℝ≥0) :
          ℝ≥0∞)) ≤ K ^ (k * 256) := by
  set φ : Fin k → Fin 256 → Win ηU → Win ηV → ℝ≥0∞ := fun j l u v =>
    ((τ ^ (if l.val ≤ i.val then windowVal u * f j (i - l) v
      else -(windowVal u * f j (i - l) v)) : ℝ≥0) : ℝ≥0∞) with hφ
  have h1 : ∀ (U : WinVec k ηU) (V : WinVec k ηV), ((τ ^ sgnDot i
      (fun j l => windowVal (U j l)) (fun j l => f j l (V j l)) : ℝ≥0) : ℝ≥0∞) =
      ∏ j, ∏ l, φ j l (U j l) (V j (i - l)) := by
    intro U V
    simp only [sgnDot, coe_zpow_sum _ hτ, hφ]
  have h2 : ∀ U : WinVec k ηU, sdExp (SDistr.uniform (WinVec k ηV))
      (fun V => ∏ j, ∏ l, φ j l (U j l) (V j (i - l))) =
      ∏ j, ∏ l, sdExp (SDistr.uniform (Win ηV)) (φ j l (U j l)) :=
    fun U => sdExp_uniform_reidx_eta ηV i fun j l => φ j l (U j l)
  simp only [h1, h2]
  rw [sdExp_uniform_pi_prod
    (fun j (Y : Fin 256 → Win ηU) => ∏ l, sdExp (SDistr.uniform (Win ηV)) (φ j l (Y l)))]
  rw [Finset.prod_congr rfl fun j _ => sdExp_uniform_pi_prod
    (fun l (u : Win ηU) => sdExp (SDistr.uniform (Win ηV)) (φ j l u))]
  calc _ ≤ ∏ _j : Fin k, ∏ _l : Fin 256, K := by
        gcongr with j _ l _
        rw [sdExp_comm]
        simp only [hφ, sdExp_windowVal_sign_eta]
        exact hK j (i - l)
    _ = K ^ (k * 256) := by simp [Finset.prod_const, ← pow_mul, mul_comm]

/-- `sdExp_sgnDot_le_eta` over uniform vectors of PRF blocks, read through their windows. -/
theorem sdExp_sgnDot_block_le_eta {k : ℕ} (ηU ηV : ℕ) (hηU : 0 < ηU) (hηV : 0 < ηV)
    (i : Fin 256) {τ : ℝ≥0} (hτ : τ ≠ 0) (f : Fin k → Fin 256 → Win ηV → ℤ) (K : ℝ≥0∞)
    (hK : ∀ j l, sdExp (SDistr.uniform (Win ηV)) (fun v => mgfZ (cbd ηU) (τ ^ f j l v)) ≤ K) :
    sdExp (SDistr.uniform (PrfVecBlock k ηU)) (fun x =>
      sdExp (SDistr.uniform (PrfVecBlock k ηV)) fun y =>
        ((τ ^ sgnDot i (wvals ηU x) (fun j l => f j l (wvec ηV y j l)) : ℝ≥0) : ℝ≥0∞)) ≤
      K ^ (k * 256) := by
  calc _ = sdExp (SDistr.uniform (WinVec k ηU)) (fun U =>
        sdExp (SDistr.uniform (WinVec k ηV)) fun V =>
          ((τ ^ sgnDot i (fun j l => windowVal (U j l)) (fun j l => f j l (V j l)) : ℝ≥0) :
            ℝ≥0∞)) := by
        rw [← sdExp_uniform_equiv (vecEquiv k ηU hηU)]
        refine congrArg _ (funext fun x => ?_)
        rw [← sdExp_uniform_equiv (vecEquiv k ηV hηV)]
        rfl
    _ ≤ _ := sdExp_sgnDot_le_eta ηU ηV i hτ f K hK

/-- The moment-generating factor of one product `s · (x + c(w + x))` at base `τ`, for
independent draws `s ∼ cbd η₁`, `x ∼ cbd η₂` and the rounding error `c = roundErr du`. -/
noncomputable def roundMgfEta (du η₁ η₂ : ℕ) (τ : ℝ≥0) (w : Zq3329) : ℝ≥0∞ :=
  sdExp (cbd η₂) fun x => mgfZ (cbd η₁) (τ ^ (x + roundErr du (w + Zq3329.fromInt x)))

/-- `roundMgfEta` is invariant under inversion of the base. -/
theorem roundMgfEta_inv (du η₁ η₂ : ℕ) (τ : ℝ≥0) (w : Zq3329) :
    roundMgfEta du η₁ η₂ τ⁻¹ w = roundMgfEta du η₁ η₂ τ w := by
  simp only [roundMgfEta, inv_zpow, mgfZ_cbd_inv]

/-- The expectation of `mgfZ (cbd η₁) (τ ^ y)` over `y ∼ cbd η₁` is invariant under inversion
of the base. -/
theorem sdExp_mgfZ_cbd_inv (η₁ : ℕ) (τ : ℝ≥0) :
    sdExp (cbd η₁) (fun y => mgfZ (cbd η₁) (τ⁻¹ ^ y)) =
      sdExp (cbd η₁) (fun y => mgfZ (cbd η₁) (τ ^ y)) := by
  simp only [inv_zpow, mgfZ_cbd_inv]

/-- **The moment-generating function of the compressed noise at two widths.** Under uniform
coins and a fixed matrix `A`, the moment-generating function at `τ` of coefficient `i` of the
compressed noise over `ℤ` is at most `P ^ (256 k) · mgfZ (cbd η₂) τ · K ^ (256 k)`, where `P`
bounds `E_{y ∼ cbd η₁}[mgfZ (cbd η₁) (τ ^ y)]` and `K` bounds `roundMgfEta du η₁ η₂ τ⁻¹ w`
for every `w`. -/
theorem sdExp_compNoiseInt_le_eta {k : ℕ} (η₁ η₂ : ℕ) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (du : ℕ) (A : Mat k) (i : Fin 256) {τ : ℝ≥0} (hτ : τ ≠ 0) (P K : ℝ≥0∞)
    (hP : sdExp (cbd η₁) (fun y => mgfZ (cbd η₁) (τ ^ y)) ≤ P)
    (hK : ∀ w, roundMgfEta du η₁ η₂ τ⁻¹ w ≤ K) :
    sdExp (SDistr.uniform (Coins k η₁ η₂)) (fun c => ((τ ^ compNoiseInt du A i
      (wvals η₁ c.1.1) (wvals η₁ c.1.2) (wvals η₁ c.2.1) (wvals η₂ c.2.2.1)
      (windowVal (windowMap η₂ c.2.2.2 i)) : ℝ≥0) : ℝ≥0∞)) ≤
      P ^ (k * 256) * mgfZ (cbd η₂) τ * K ^ (k * 256) := by
  set Y : PrfVecBlock k η₁ → PrfVecBlock k η₂ → Fin k → Fin 256 → ℤ := fun r x j l =>
    wvals η₂ x j l + roundErr du (matVecMul (matTranspose A)
      (fun j l => Zq3329.fromInt (wvals η₁ r j l)) j l + Zq3329.fromInt (wvals η₂ x j l))
    with hY
  set a : PrfVecBlock k η₁ → PrfVecBlock k η₁ → ℝ≥0∞ := fun e r =>
    ((τ ^ sgnDot i (wvals η₁ e) (wvals η₁ r) : ℝ≥0) : ℝ≥0∞) with ha
  set b : PrfVecBlock k η₁ → PrfVecBlock k η₁ → PrfVecBlock k η₂ → ℝ≥0∞ := fun s r x =>
    ((τ⁻¹ ^ sgnDot i (wvals η₁ s) (Y r x) : ℝ≥0) : ℝ≥0∞) with hb
  have hpt : ∀ s e r x (z : PrfBlock η₂), ((τ ^ compNoiseInt du A i (wvals η₁ s)
      (wvals η₁ e) (wvals η₁ r) (wvals η₂ x) (windowVal (windowMap η₂ z i)) : ℝ≥0) : ℝ≥0∞) =
      a e r * b s r x * ((τ ^ windowVal (windowMap η₂ z i) : ℝ≥0) : ℝ≥0∞) := by
    intro s e r x z
    rw [ha, hb, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    congr 1
    rw [compNoiseInt, zpow_sub₀ hτ, zpow_add₀ hτ, inv_zpow, div_eq_mul_inv]
    ring
  have hz : sdExp (SDistr.uniform (PrfBlock η₂))
      (fun z => ((τ ^ windowVal (windowMap η₂ z i) : ℝ≥0) : ℝ≥0∞)) = mgfZ (cbd η₂) τ :=
    sdExp_uniform_block_windowVal η₂ hη₂ i fun y => ((τ ^ y : ℝ≥0) : ℝ≥0∞)
  simp only [sdExp_uniform_prod, hpt, sdExp_mul_left, hz]
  set U₁ := SDistr.uniform (PrfVecBlock k η₁)
  set U₂ := SDistr.uniform (PrfVecBlock k η₂)
  have hB : ∀ r, sdExp U₁ (fun s => sdExp U₂ fun x => b s r x) ≤ K ^ (k * 256) := by
    intro r
    refine sdExp_sgnDot_block_le_eta η₁ η₂ hη₁ hη₂ i (inv_ne_zero hτ) (fun j l v =>
      windowVal v + roundErr du (matVecMul (matTranspose A)
        (fun j l => Zq3329.fromInt (wvals η₁ r j l)) j l + Zq3329.fromInt (windowVal v))) _
      fun j l => ?_
    rw [sdExp_uniform_windowVal η₂ fun x => mgfZ (cbd η₁) (τ⁻¹ ^ (x + roundErr du
      (matVecMul (matTranspose A) (fun j l => Zq3329.fromInt (wvals η₁ r j l)) j l +
        Zq3329.fromInt x)))]
    exact hK _
  have hA : sdExp U₁ (fun e => sdExp U₁ (a e)) ≤ P ^ (k * 256) := by
    refine sdExp_sgnDot_block_le_eta η₁ η₁ hη₁ hη₁ i hτ (fun _ _ v => windowVal v) _
      fun _ _ => ?_
    rw [sdExp_uniform_windowVal η₁ fun y => mgfZ (cbd η₁) (τ ^ y)]
    exact hP
  calc _ = sdExp U₁ (fun e => sdExp U₁ fun r =>
        a e r * mgfZ (cbd η₂) τ * sdExp U₁ (fun s => sdExp U₂ fun x => b s r x)) := by
        rw [sdExp_comm]
        refine congrArg _ (funext fun e => ?_)
        rw [sdExp_comm]
        refine congrArg _ (funext fun r => ?_)
        simp only [sdExp_mul_right, sdExp_mul_left]
        ring
    _ ≤ sdExp U₁ (fun e => sdExp U₁ fun r => a e r * mgfZ (cbd η₂) τ * K ^ (k * 256)) :=
        sdExp_mono _ fun e => sdExp_mono _ fun r => mul_le_mul_right (hB r) _
    _ = sdExp U₁ (fun e => sdExp U₁ (a e)) * (mgfZ (cbd η₂) τ * K ^ (k * 256)) := by
        simp only [mul_assoc, sdExp_mul_right]
    _ ≤ P ^ (k * 256) * (mgfZ (cbd η₂) τ * K ^ (k * 256)) :=
        mul_le_mul_left hA _
    _ = _ := by ring

/-! ## The tail bound -/

/-- **Tail bound for one coefficient of the compressed noise at two widths.** For a fixed
matrix `A`, a threshold `T`, a base `1 ≤ t`, a bound `P` on
`E_{y ∼ cbd η₁}[mgfZ (cbd η₁) (t ^ y)]` and a bound `K` on `roundMgfEta du η₁ η₂ t`, the
probability under uniform coins that coefficient `i` of `compNoise du A` has centred absolute
value at least `T` is at most `2 · P ^ (256 k) · mgfZ (cbd η₂) t · K ^ (256 k) · t⁻ᵀ`. -/
theorem compNoise_tail_le_eta {k : ℕ} (η₁ η₂ : ℕ) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (du : ℕ)
    (A : Mat k) (i : Fin 256) (T : ℕ) {t : ℝ≥0} (ht : 1 ≤ t) (P K : ℝ≥0∞)
    (hP : sdExp (cbd η₁) (fun y => mgfZ (cbd η₁) (t ^ y)) ≤ P)
    (hK : ∀ w, roundMgfEta du η₁ η₂ t w ≤ K) :
    (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure
        {c | T ≤ centeredAbs (compNoise du A c i)} ≤
      2 * (P ^ (k * 256) * mgfZ (cbd η₂) t * K ^ (k * 256)) * ((t⁻¹ ^ T : ℝ≥0) : ℝ≥0∞) := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
  have hK' : ∀ w, roundMgfEta du η₁ η₂ t⁻¹ w ≤ K := fun w =>
    (roundMgfEta_inv du η₁ η₂ t w).le.trans (hK w)
  have hK'' : ∀ w, roundMgfEta du η₁ η₂ t⁻¹⁻¹ w ≤ K := by simpa only [inv_inv] using hK
  have hP' : sdExp (cbd η₁) (fun y => mgfZ (cbd η₁) (t⁻¹ ^ y)) ≤ P :=
    (sdExp_mgfZ_cbd_inv η₁ t).le.trans hP
  set Z : Coins k η₁ η₂ → ℤ := fun c => compNoiseInt du A i (wvals η₁ c.1.1)
    (wvals η₁ c.1.2) (wvals η₁ c.2.1) (wvals η₂ c.2.2.1) (windowVal (windowMap η₂ c.2.2.2 i))
    with hZ
  calc _ = sdExp (SDistr.uniform (Coins k η₁ η₂))
        (fun c => if T ≤ centeredAbs (compNoise du A c i) then 1 else 0) := by
        rw [sdExp_uniform, PMF.toOuterMeasure_apply]
        refine tsum_congr fun c => ?_
        by_cases hc : T ≤ centeredAbs (compNoise du A c i) <;>
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, hc, ite_true, ite_false, mul_one,
            mul_zero]
    _ ≤ sdExp (SDistr.uniform (Coins k η₁ η₂)) (fun c => (((t ^ Z c : ℝ≥0) : ℝ≥0∞) +
        ((t⁻¹ ^ Z c : ℝ≥0) : ℝ≥0∞)) * ((t⁻¹ ^ T : ℝ≥0) : ℝ≥0∞)) := by
        refine sdExp_mono _ fun c => le_trans ?_ (indicator_le_zpow T ht (Z c))
        have h1 := centeredAbs_fromInt_le (Z c)
        have h2 : compNoise du A c i = Zq3329.fromInt (Z c) := compNoise_apply du A c i
        rw [h2]
        split_ifs <;> first | omega | simp
    _ = (sdExp (SDistr.uniform (Coins k η₁ η₂)) (fun c => ((t ^ Z c : ℝ≥0) : ℝ≥0∞)) +
        sdExp (SDistr.uniform (Coins k η₁ η₂)) (fun c => ((t⁻¹ ^ Z c : ℝ≥0) : ℝ≥0∞))) *
          ((t⁻¹ ^ T : ℝ≥0) : ℝ≥0∞) := by
        rw [sdExp_mul_right, sdExp_add]
    _ ≤ (P ^ (k * 256) * mgfZ (cbd η₂) t * K ^ (k * 256) +
        P ^ (k * 256) * mgfZ (cbd η₂) t⁻¹ * K ^ (k * 256)) * ((t⁻¹ ^ T : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        · exact sdExp_compNoiseInt_le_eta η₁ η₂ hη₁ hη₂ du A i ht0 P K hP hK'
        · exact sdExp_compNoiseInt_le_eta η₁ η₂ hη₁ hη₂ du A i (inv_ne_zero ht0) P K hP' hK''
    _ = _ := by rw [mgfZ_cbd_inv, two_mul]

/-! ## Expectations under `cbd 3` -/

/-- The expectation under `binom 3`. -/
theorem sdExp_binom_three (g : ℕ → ℝ≥0∞) :
    sdExp (binom 3) g = 2⁻¹ ^ 3 * (g 0 + 3 * g 1 + 3 * g 2 + g 3) := by
  simp only [binom, sdExp_bind, sdExp_uniform_bool, sdExp_pure]
  norm_num
  ring

/-- The expectation under `cbd 3`. -/
theorem sdExp_cbd_three (g : ℤ → ℝ≥0∞) :
    sdExp (cbd 3) g = 2⁻¹ ^ 6 * (g (-3) + 6 * g (-2) + 15 * g (-1) + 20 * g 0 + 15 * g 1 +
      6 * g 2 + g 3) := by
  simp only [cbd, sdExp_bind, sdExp_binom_three, sdExp_pure]
  norm_num
  ring

/-- The expectation under `cbd 3` of a function with values in `ℝ≥0`. -/
theorem sdExp_cbd_three_coe (h : ℤ → ℝ≥0) :
    sdExp (cbd 3) (fun z => (h z : ℝ≥0∞)) =
      ((2⁻¹ ^ 6 * (h (-3) + 6 * h (-2) + 15 * h (-1) + 20 * h 0 + 15 * h 1 + 6 * h 2 + h 3) :
        ℝ≥0) : ℝ≥0∞) := by
  rw [sdExp_cbd_three]
  push_cast
  rfl

/-- The moment-generating function of `cbd 3` at base `t`. -/
noncomputable def cbdThreeMgf (t : ℝ≥0) : ℝ≥0 :=
  2⁻¹ ^ 6 * (t ^ (-3 : ℤ) + 6 * t ^ (-2 : ℤ) + 15 * t ^ (-1 : ℤ) + 20 * t ^ (0 : ℤ) +
    15 * t ^ (1 : ℤ) + 6 * t ^ (2 : ℤ) + t ^ (3 : ℤ))

/-- `mgfZ (cbd 3) t` is `cbdThreeMgf t`. -/
theorem mgfZ_cbd_three (t : ℝ≥0) : mgfZ (cbd 3) t = cbdThreeMgf t :=
  sdExp_cbd_three_coe _

/-! ## The numeric bound for ML-KEM-512 at `t = 6/5` -/

/-- `30 ^ 12 · (6/5) ^ m` as a natural number, for `|m| ≤ 12`, written with `Nat.pow`. -/
def powSixFifths12 (m : ℤ) : ℕ := Nat.pow 6 (12 + m).toNat * Nat.pow 5 (12 - m).toNat

/-- `64 · 30 ^ 12 · cbdThreeMgf ((6/5) ^ y)` as a natural number, for `|y| ≤ 4`. -/
def cbdThreeMgfNat (y : ℤ) : ℕ :=
  powSixFifths12 (-3 * y) + 6 * powSixFifths12 (-2 * y) + 15 * powSixFifths12 (-y) +
    20 * powSixFifths12 0 + 15 * powSixFifths12 y + 6 * powSixFifths12 (2 * y) +
    powSixFifths12 (3 * y)

/-- `cbdThreeMgfNat y` is `64 · 30 ^ 12 · cbdThreeMgf ((6/5) ^ y)` for `|y| ≤ 4`. -/
theorem cbdThreeMgf_six_fifths (y : ℤ) (h1 : -4 ≤ y) (h2 : y ≤ 4) :
    cbdThreeMgf ((6 / 5) ^ y) = (cbdThreeMgfNat y : ℝ≥0) / (64 * 30 ^ 12) := by
  rw [← NNReal.coe_inj]
  interval_cases y <;>
    norm_num [cbdThreeMgf, cbdThreeMgfNat, powSixFifths12]

/-- The rounding pattern of `Compress_10` at `w` for `s ∼ cbd 3`: the five values
`x + c(w + x)` for `x ∈ [-2, 2]` lie in `[-4, 4]`, and their weighted `cbdThreeMgfNat` sum is
at most `1024 · 30 ^ 12 · 51520374361 / 46656000000`. -/
def roundPatternOk3 (w : Zq3329) : Bool :=
  let p : ℤ → ℤ := fun x => x + roundErr 10 (w + Zq3329.fromInt x)
  decide (-4 ≤ p (-2) ∧ p (-2) ≤ 4 ∧ -4 ≤ p (-1) ∧ p (-1) ≤ 4 ∧ -4 ≤ p 0 ∧ p 0 ≤ 4 ∧
    -4 ≤ p 1 ∧ p 1 ≤ 4 ∧ -4 ≤ p 2 ∧ p 2 ≤ 4) &&
  decide (cbdThreeMgfNat (p (-2)) + 4 * cbdThreeMgfNat (p (-1)) + 6 * cbdThreeMgfNat (p 0) +
    4 * cbdThreeMgfNat (p 1) + cbdThreeMgfNat (p 2) ≤ 600933646546704000000)

/-- `roundPatternOk3` on the representative `v` of `w`, over `ℕ` and `ℤ`. -/
def roundPatternOk3Nat (v : ℕ) : Bool :=
  let p : ℤ → ℤ := fun x => x + roundErrNat ((((v : ℤ) + x) % 3329).toNat)
  decide (-4 ≤ p (-2) ∧ p (-2) ≤ 4 ∧ -4 ≤ p (-1) ∧ p (-1) ≤ 4 ∧ -4 ≤ p 0 ∧ p 0 ≤ 4 ∧
    -4 ≤ p 1 ∧ p 1 ≤ 4 ∧ -4 ≤ p 2 ∧ p 2 ≤ 4) &&
  decide (cbdThreeMgfNat (p (-2)) + 4 * cbdThreeMgfNat (p (-1)) + 6 * cbdThreeMgfNat (p 0) +
    4 * cbdThreeMgfNat (p 1) + cbdThreeMgfNat (p 2) ≤ 600933646546704000000)

/-- `roundPatternOk3 w` is `roundPatternOk3Nat` of the representative of `w`. -/
theorem roundPatternOk3_eq (w : Zq3329) : roundPatternOk3 w = roundPatternOk3Nat w.val := by
  simp only [roundPatternOk3, roundPatternOk3Nat, roundErr_ten_eq, val_add_fromInt]

set_option linter.style.native false in
/-- Every representative `v < 3329` has an admissible rounding pattern for `s ∼ cbd 3`. -/
theorem roundPatternOk3Nat_all : (List.range 3329).all roundPatternOk3Nat = true := by
  native_decide

/-- Every `w` has an admissible rounding pattern for `s ∼ cbd 3`. -/
theorem roundPatternOk3_all : ∀ w : Zq3329, roundPatternOk3 w = true := by
  intro w
  rw [roundPatternOk3_eq]
  have h := roundPatternOk3Nat_all
  rw [List.all_eq_true] at h
  exact h _ (List.mem_range.2 (ZMod.val_lt w))

/-- `roundMgfEta 10 3 2 (6/5) w` is at most `51520374361 / 46656000000` for every `w`. -/
theorem roundMgfEta_six_fifths_le (w : Zq3329) :
    roundMgfEta 10 3 2 (6 / 5) w ≤ ((51520374361 / 46656000000 : ℝ≥0) : ℝ≥0∞) := by
  have h := roundPatternOk3_all w
  simp only [roundPatternOk3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hN⟩ := h
  rw [roundMgfEta]
  simp only [mgfZ_cbd_three]
  rw [sdExp_cbd_two_coe, ENNReal.coe_le_coe]
  calc _ = ((cbdThreeMgfNat (-2 + roundErr 10 (w + Zq3329.fromInt (-2))) +
        4 * cbdThreeMgfNat (-1 + roundErr 10 (w + Zq3329.fromInt (-1))) +
        6 * cbdThreeMgfNat (0 + roundErr 10 (w + Zq3329.fromInt 0)) +
        4 * cbdThreeMgfNat (1 + roundErr 10 (w + Zq3329.fromInt 1)) +
        cbdThreeMgfNat (2 + roundErr 10 (w + Zq3329.fromInt 2)) : ℕ) : ℝ≥0) /
          (1024 * 30 ^ 12) := by
        simp only [cbdThreeMgf_six_fifths _ h1 h2, cbdThreeMgf_six_fifths _ h3 h4,
          cbdThreeMgf_six_fifths _ h5 h6, cbdThreeMgf_six_fifths _ h7 h8,
          cbdThreeMgf_six_fifths _ h9 h10]
        push_cast
        ring
    _ ≤ ((600933646546704000000 : ℕ) : ℝ≥0) / (1024 * 30 ^ 12) := by
        gcongr
    _ = 51520374361 / 46656000000 := by
        rw [← NNReal.coe_inj]
        norm_num

/-- The expectation of `mgfZ (cbd 3) ((6/5) ^ y)` over `y ∼ cbd 3` is
`41887707090098041 / 40310784000000000`. -/
theorem sdExp_cbdThreeMgf_six_fifths :
    sdExp (cbd 3) (fun y => mgfZ (cbd 3) ((6 / 5) ^ y)) =
      ((41887707090098041 / 40310784000000000 : ℝ≥0) : ℝ≥0∞) := by
  simp only [mgfZ_cbd_three]
  rw [sdExp_cbd_three_coe, ENNReal.coe_inj, ← NNReal.coe_inj]
  push_cast [cbdThreeMgf]
  norm_num

/-- The rational inequality behind `mlkem512Compressed_chernoff_value`, with numerators and
denominators as natural-number variables. -/
theorem chernoffCompressed512_of_nat {np dp nc dc nf df a b m : ℕ} (hdp : 0 < dp)
    (hdc : 0 < dc) (hdf : 0 < df) (hb : 0 < b) (hm : 0 < m)
    (h : 2 * np ^ 512 * nc * nf ^ 512 * a ^ 728 * m ≤ dp ^ 512 * dc * df ^ 512 * b ^ 728) :
    2 * (((np : ℝ) / dp) ^ 512 * (nc / dc) * ((nf : ℝ) / df) ^ 512) * ((a : ℝ) / b) ^ 728 ≤
      (m : ℝ)⁻¹ := by
  have hY : (0 : ℝ) < dp ^ 512 * dc * df ^ 512 * b ^ 728 := by positivity
  rw [show 2 * (((np : ℝ) / dp) ^ 512 * (nc / dc) * ((nf : ℝ) / df) ^ 512) * ((a : ℝ) / b) ^ 728 =
      (2 * np ^ 512 * nc * nf ^ 512 * a ^ 728 : ℝ) / (dp ^ 512 * dc * df ^ 512 * b ^ 728) by
      field_simp,
    div_le_iff₀ hY, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact_mod_cast h

set_option exponentiation.threshold 2000 in
/-- The cleared-denominator form of the compressed ML-KEM-512 Chernoff value at `t = 6/5`. -/
theorem mlkem512Compressed_chernoff_nat :
    2 * 41887707090098041 ^ 512 * 14641 * 51520374361 ^ 512 * 5 ^ 728 * 2 ^ 88 ≤
      40310784000000000 ^ 512 * 14400 * 46656000000 ^ 512 * 6 ^ 728 :=
  Nat.le_of_ble_eq_true rfl

/-- The per-coefficient Chernoff value of compressed ML-KEM-512 at `t = 6/5` is at most
`2⁻⁸⁸`. -/
theorem mlkem512Compressed_chernoff_value :
    2 * ((41887707090098041 / 40310784000000000 : ℝ≥0) ^ (2 * 256) * cbdTwoMgf (6 / 5) *
        (51520374361 / 46656000000 : ℝ≥0) ^ (2 * 256)) * (6 / 5 : ℝ≥0)⁻¹ ^ 728 ≤
      (2 ^ 88)⁻¹ := by
  rw [cbdTwoMgf_six_fifths', ← NNReal.coe_le_coe]
  have key := chernoffCompressed512_of_nat (np := 41887707090098041)
    (dp := 40310784000000000) (nc := 14641) (dc := 14400) (nf := 51520374361)
    (df := 46656000000) (a := 5) (b := 6) (m := 2 ^ 88)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
    mlkem512Compressed_chernoff_nat
  push_cast at key ⊢
  norm_num at key ⊢
  exact key

/-- **Tail bound for compressed ML-KEM-512.** For every matrix, one coefficient of the
compressed noise of ML-KEM-512 has centred absolute value at least `728` with probability at
most `2⁻⁸⁸`. -/
theorem mlkem512Compressed_coeff_tail_le (A : Mat 2) (i : Fin 256) :
    (PMF.uniformFintype (Coins 2 3 2)).toOuterMeasure
        {c | 728 ≤ centeredAbs (compNoise 10 A c i)} ≤ ((2 : ℝ≥0∞) ^ 88)⁻¹ := by
  have ht : (1 : ℝ≥0) ≤ 6 / 5 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  refine (compNoise_tail_le_eta 3 2 (by norm_num) (by norm_num) 10 A i 728 ht _ _
    sdExp_cbdThreeMgf_six_fifths.le roundMgfEta_six_fifths_le).trans ?_
  have h := ENNReal.coe_le_coe.2 mlkem512Compressed_chernoff_value
  rw [mgfZ_cbd_two]
  push_cast at h
  push_cast
  exact h

/-- **The decryption-failure hypothesis of compressed ML-KEM-512.** The correctness error of
`mlkem512CompressedScheme` is at most `decryptionFailureProb mlkem512Noise 2⁻⁸⁸`: this
discharges the worst-case failure hypothesis `hWorst` of the compressed scheme. The bound uses
no assumption on the distribution of the ciphertext and no computational step. -/
theorem mlkem512Compressed_corrWorst_le :
    CompressedPKE.mlkem512CompressedScheme.corrWorst ≤
      decryptionFailureProb mlkem512Noise ((2 : ℝ≥0∞) ^ 88)⁻¹ := by
  rw [mlkem512_failure_from_coeff]
  exact compScheme_corrWorst_le 2 3 2 10 4 (by norm_num) (by norm_num) _
    fun A i => mlkem512Compressed_coeff_tail_le A i

/-- The correctness error of `mlkem512CompressedScheme` is at most `2⁻⁸⁰`. -/
theorem mlkem512Compressed_corrWorst_le_two_pow :
    CompressedPKE.mlkem512CompressedScheme.corrWorst ≤ ((2 : ℝ≥0∞) ^ 80)⁻¹ := by
  refine mlkem512Compressed_corrWorst_le.trans (le_of_eq ?_)
  rw [mlkem512_failure_from_coeff, show (256 : ℝ≥0∞) = 2 ^ 8 by norm_num,
    show (2 : ℝ≥0∞) ^ 88 = 2 ^ 8 * 2 ^ 80 by rw [← pow_add],
    ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

end CatCrypt.Crypto.MLKEM.MLKEMRankInstance

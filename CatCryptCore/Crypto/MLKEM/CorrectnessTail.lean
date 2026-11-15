/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.CorrectnessNoiseLaw
public import CatCryptCore.Crypto.MLKEM.CorrectnessBounds

/-!
# A Chernoff tail bound for the ML-KEM decryption noise, and the ML-KEM-768 failure bound

For a sub-distribution `d` over `ℤ` and a base `t : ℝ≥0`, `mgfZ d t` is the expectation of
`t ^ z` under `d`. It is multiplicative along sums of independent draws, so the
moment-generating function of `noiseCoeffLaw k η₁ η₂` at `t` is a product of powers of the
moment-generating functions of `cbdProd` and `cbd`. Markov's inequality applied to `t ^ z`
and `t⁻¹ ^ z` bounds the probability that one coefficient of the decryption noise has centred
absolute value at least `832`.

At `k = 3`, `η₁ = η₂ = 2` these moment-generating functions are explicit Laurent polynomials
in `t`. At `t = 81/50` the bound for one coefficient is at most `2⁻³⁰³`, and the union bound
over the 256 coefficients bounds the correctness error of the base MLWE public-key encryption
scheme `toScheme mlkem768Params` by `256 · 2⁻³⁰³ = 2⁻²⁹⁵`. The scheme has no ciphertext
compression, so the decryption noise has no rounding term. The only numeric computation is
one inequality between natural numbers, `mlkem768_chernoff_nat`, checked by `Nat.ble`.

## Main definitions

* `sdExp d g` — the expectation of `g : α → ℝ≥0∞` over the successful outcomes of `d`
* `mgfZ d t` — the expectation of `t ^ z` under `d : SDistr ℤ`
* `cbdTwoMgf t`, `cbdProdTwoMgf t` — the moment-generating functions of `cbd 2` and
  `cbdProd 2 2`

## Main results

* `mgfZ_sumIID` — `mgfZ (sumIID d n) t = mgfZ d t ^ n`
* `mgfZ_noiseCoeffLaw` — the moment-generating function of one noise coefficient
* `sdExp_tail_le` — the two-sided Markov bound `Pr[a ≤ |z|] ≤ (M(t) + M(t⁻¹)) · t⁻ᵃ`
* `coinNoise_tail_le` — the bound for one coefficient of the decryption noise under uniform
  coins
* `mlkem768_coeff_tail_le` — at ML-KEM-768, one coefficient is large with probability at
  most `2⁻³⁰³`
* `mlkem768_corrWorst_le` — the hypothesis `hWorst` of the ML-KEM-768 theorems,
  `corrWorst ≤ decryptionFailureProb mlkem768Noise 2⁻³⁰³`
* `mlkem768_corrWorst_le_two_pow` — `corrWorst ≤ 2⁻²⁹⁵`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MLKEMRankInstance

open CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Util
open CatCrypt.Crypto.MLKEM.Compress (centeredAbs)
open CatCrypt.Crypto.MLKEM.CorrectnessBounds (decryptionFailureProb mlkem768Noise
  mlkem768_failure_from_coeff)
open scoped ENNReal NNReal

/-! ## Expectations under a sub-distribution -/

/-- The expectation of `g` over the successful outcomes of the sub-distribution `d`. -/
noncomputable def sdExp {α : Type} (d : SDistr α) (g : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, d (some a) * g a

/-- The expectation under a point mass is the value at the point. -/
theorem sdExp_pure {α : Type} (a : α) (g : α → ℝ≥0∞) : sdExp (SDistr.pure a) g = g a := by
  classical
  simp [sdExp, SDistr.pure_apply_some]

/-- The expectation under a bind is the expectation of the inner expectations. -/
theorem sdExp_bind {α β : Type} (d : SDistr α) (f : α → SDistr β) (g : β → ℝ≥0∞) :
    sdExp (d.bind f) g = sdExp d fun a => sdExp (f a) g := by
  simp only [sdExp, SDistr.bind, PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm, SDistr.tsum_option_eq_add]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  simp [SDistr.fail_apply_some]

/-- The expectation under the uniform distribution on `Bool`. -/
theorem sdExp_uniform_bool (g : Bool → ℝ≥0∞) :
    sdExp (SDistr.uniform Bool) g = 2⁻¹ * g true + 2⁻¹ * g false := by
  simp [sdExp, SDistr.uniform_apply_some, tsum_fintype]

/-- The expectation under a uniform distribution is the `PMF.uniformFintype` average. -/
theorem sdExp_uniform {α : Type} [Fintype α] [Nonempty α] (g : α → ℝ≥0∞) :
    sdExp (SDistr.uniform α) g = ∑' a, PMF.uniformFintype α a * g a := by
  simp [sdExp, SDistr.uniform_apply_some, PMF.uniformFintype_apply]

/-- A constant factor on the left leaves the expectation. -/
theorem sdExp_mul_left {α : Type} (d : SDistr α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    sdExp d (fun a => c * g a) = c * sdExp d g := by
  simp only [sdExp, ← ENNReal.tsum_mul_left]
  grind

/-- A constant factor on the right leaves the expectation. -/
theorem sdExp_mul_right {α : Type} (d : SDistr α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    sdExp d (fun a => g a * c) = sdExp d g * c := by
  simp only [sdExp, ← ENNReal.tsum_mul_right]
  grind

/-- The expectation is additive. -/
theorem sdExp_add {α : Type} (d : SDistr α) (f g : α → ℝ≥0∞) :
    sdExp d (fun a => f a + g a) = sdExp d f + sdExp d g := by
  simp only [sdExp, mul_add]
  exact ENNReal.tsum_add

/-- The expectation is monotone in the integrand. -/
theorem sdExp_mono {α : Type} (d : SDistr α) {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) :
    sdExp d f ≤ sdExp d g :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)

/-! ## Moment-generating functions over `ℤ` -/

/-- The moment-generating function of `d : SDistr ℤ` at base `t`: the expectation of
`t ^ z`. -/
noncomputable def mgfZ (d : SDistr ℤ) (t : ℝ≥0) : ℝ≥0∞ :=
  sdExp d fun z => ((t ^ z : ℝ≥0) : ℝ≥0∞)

/-- The moment-generating function of the sum of two independent draws is the product. -/
theorem mgfZ_bind_add (d e : SDistr ℤ) {t : ℝ≥0} (ht : t ≠ 0) :
    mgfZ (d.bind fun a => e.bind fun b => SDistr.pure (a + b)) t = mgfZ d t * mgfZ e t := by
  simp only [mgfZ, sdExp_bind, sdExp_pure, zpow_add₀ ht, ENNReal.coe_mul, sdExp_mul_left,
    sdExp_mul_right]

/-- The moment-generating function of `sumIID d n` is the `n`-th power of that of `d`. -/
theorem mgfZ_sumIID (d : SDistr ℤ) {t : ℝ≥0} (ht : t ≠ 0) (n : ℕ) :
    mgfZ (sumIID d n) t = mgfZ d t ^ n := by
  induction n with
  | zero => simp [sumIID, mgfZ, sdExp_pure]
  | succ n ih => rw [sumIID, mgfZ_bind_add d _ ht, ih, pow_succ']

/-- The moment-generating function of one coefficient of the decryption noise. -/
theorem mgfZ_noiseCoeffLaw (k η₁ η₂ : ℕ) {t : ℝ≥0} (ht : t ≠ 0) :
    mgfZ (noiseCoeffLaw k η₁ η₂) t =
      mgfZ (cbdProd η₁ η₁) t ^ (k * 256) * mgfZ (cbd η₂) t *
        mgfZ (cbdProd η₁ η₂) t⁻¹ ^ (k * 256) := by
  rw [← mgfZ_sumIID _ ht, ← mgfZ_sumIID _ (inv_ne_zero ht)]
  have hz : ∀ a z b : ℤ, t ^ (a + z - b) = t ^ a * t ^ z * t⁻¹ ^ b := fun a z b => by
    rw [zpow_sub₀ ht, zpow_add₀ ht, inv_zpow', zpow_neg, div_eq_mul_inv]
  simp only [noiseCoeffLaw, mgfZ, sdExp_bind, sdExp_pure, hz, ENNReal.coe_mul, sdExp_mul_left,
    sdExp_mul_right]

/-! ## The tail bound -/

/-- The two-sided Markov bound: for `1 ≤ t`, the probability that `a ≤ |z|` is at most
`(mgfZ d t + mgfZ d t⁻¹) · t⁻ᵃ`. -/
theorem sdExp_tail_le (d : SDistr ℤ) (a : ℕ) {t : ℝ≥0} (ht : 1 ≤ t) :
    sdExp d (fun z => if a ≤ z.natAbs then 1 else 0) ≤
      (mgfZ d t + mgfZ d t⁻¹) * ((t⁻¹ ^ a : ℝ≥0) : ℝ≥0∞) := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
  have hpt : ∀ z : ℤ, (if a ≤ z.natAbs then (1 : ℝ≥0∞) else 0) ≤
      (((t ^ z : ℝ≥0) : ℝ≥0∞) + ((t⁻¹ ^ z : ℝ≥0) : ℝ≥0∞)) * ((t⁻¹ ^ a : ℝ≥0) : ℝ≥0∞) := by
    intro z
    split_ifs with h
    · rw [← ENNReal.coe_add, ← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_le_coe]
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
      · simp only [Int.natAbs_natCast] at h
        calc (1 : ℝ≥0) ≤ t ^ ((n : ℤ) - a) := one_le_zpow₀ ht (by omega)
          _ = t ^ (n : ℤ) * t⁻¹ ^ a := by
            rw [zpow_sub₀ ht0, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
          _ ≤ _ := by gcongr; exact le_self_add
      · simp only [Int.natAbs_neg, Int.natAbs_natCast] at h
        calc (1 : ℝ≥0) ≤ t ^ ((n : ℤ) - a) := one_le_zpow₀ ht (by omega)
          _ = t⁻¹ ^ (-(n : ℤ)) * t⁻¹ ^ a := by
            rw [inv_zpow', neg_neg, zpow_sub₀ ht0, zpow_natCast, zpow_natCast, inv_pow,
              div_eq_mul_inv]
          _ ≤ _ := by gcongr; exact le_add_self
    · exact bot_le
  calc _ ≤ _ := sdExp_mono d hpt
    _ = _ := by rw [sdExp_mul_right, sdExp_add]; rfl

/-- The centred absolute value of the reduction of an integer is at most its absolute
value. -/
theorem centeredAbs_fromInt_le (z : ℤ) : centeredAbs (Zq3329.fromInt z) ≤ z.natAbs := by
  have h := ZMod.natAbs_min_of_le_div_two 3329 (Zq3329.fromInt z).valMinAbs z
    (ZMod.coe_valMinAbs _) (ZMod.natAbs_valMinAbs_le _)
  rw [ZMod.valMinAbs_natAbs_eq_min] at h
  exact h

/-- **Tail bound for one noise coefficient.** For `1 ≤ t`, the probability under uniform
coins that coefficient `i` of the decryption noise has centred absolute value at least `832`
is at most `(M(t) + M(t⁻¹)) · t⁻⁸³²`, where `M` is the moment-generating function of
`noiseCoeffLaw k η₁ η₂`. -/
theorem coinNoise_tail_le (k η₁ η₂ : ℕ) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (i : Fin 256)
    {t : ℝ≥0} (ht : 1 ≤ t) :
    (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure
        {c | 832 ≤ centeredAbs (coinNoise c i)} ≤
      (mgfZ (noiseCoeffLaw k η₁ η₂) t + mgfZ (noiseCoeffLaw k η₁ η₂) t⁻¹) *
        ((t⁻¹ ^ (832 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
  have h1 : (PMF.uniformFintype (Coins k η₁ η₂)).toOuterMeasure
        {c | 832 ≤ centeredAbs (coinNoise c i)} =
      sdExp ((SDistr.uniform (Coins k η₁ η₂)).bind fun c => SDistr.pure (coinNoise c i))
        (fun x => if 832 ≤ centeredAbs x then 1 else 0) := by
    rw [sdExp_bind, sdExp_uniform, PMF.toOuterMeasure_apply]
    refine tsum_congr fun c => ?_
    by_cases hc : 832 ≤ centeredAbs (coinNoise c i) <;>
      simp only [sdExp_pure, Set.indicator_apply, Set.mem_ofPred_eq, hc, ite_true, ite_false,
        mul_one, mul_zero]
  rw [h1, coinNoise_law k η₁ η₂ hη₁ hη₂ i, sdExp_bind]
  simp only [sdExp_pure]
  refine le_trans (sdExp_mono _ fun z => ?_) (sdExp_tail_le _ 832 ht)
  have := centeredAbs_fromInt_le z
  split_ifs <;> first | omega | simp

/-! ## Expectations under `cbd 2` -/

/-- The expectation under `binom 2`. -/
theorem sdExp_binom_two (g : ℕ → ℝ≥0∞) :
    sdExp (binom 2) g = 2⁻¹ ^ 2 * (g 0 + 2 * g 1 + g 2) := by
  simp only [binom, sdExp_bind, sdExp_uniform_bool, sdExp_pure]
  norm_num
  ring

/-- The expectation under `cbd 2`. -/
theorem sdExp_cbd_two (g : ℤ → ℝ≥0∞) :
    sdExp (cbd 2) g = 2⁻¹ ^ 4 * (g (-2) + 4 * g (-1) + 6 * g 0 + 4 * g 1 + g 2) := by
  simp only [cbd, sdExp_bind, sdExp_binom_two, sdExp_pure]
  norm_num
  ring

/-- The expectation under `cbd 2` of a function with values in `ℝ≥0`. -/
theorem sdExp_cbd_two_coe (h : ℤ → ℝ≥0) :
    sdExp (cbd 2) (fun z => (h z : ℝ≥0∞)) =
      ((2⁻¹ ^ 4 * (h (-2) + 4 * h (-1) + 6 * h 0 + 4 * h 1 + h 2) : ℝ≥0) : ℝ≥0∞) := by
  rw [sdExp_cbd_two]
  push_cast
  rfl

/-! ## The moment-generating functions at `η = 2` -/

/-- The moment-generating function of `cbd 2` at base `t`. -/
noncomputable def cbdTwoMgf (t : ℝ≥0) : ℝ≥0 :=
  2⁻¹ ^ 4 * (t ^ (-2 : ℤ) + 4 * t ^ (-1 : ℤ) + 6 * t ^ (0 : ℤ) + 4 * t ^ (1 : ℤ) + t ^ (2 : ℤ))

/-- The moment-generating function of `cbdProd 2 2` at base `t`. -/
noncomputable def cbdProdTwoMgf (t : ℝ≥0) : ℝ≥0 :=
  2⁻¹ ^ 4 * (cbdTwoMgf (t ^ (-2 : ℤ)) + 4 * cbdTwoMgf (t ^ (-1 : ℤ)) +
    6 * cbdTwoMgf (t ^ (0 : ℤ)) + 4 * cbdTwoMgf (t ^ (1 : ℤ)) + cbdTwoMgf (t ^ (2 : ℤ)))

/-- `mgfZ (cbd 2) t` is `cbdTwoMgf t`. -/
theorem mgfZ_cbd_two (t : ℝ≥0) : mgfZ (cbd 2) t = cbdTwoMgf t :=
  sdExp_cbd_two_coe _

/-- `mgfZ (cbdProd 2 2) t` is `cbdProdTwoMgf t`. -/
theorem mgfZ_cbdProd_two (t : ℝ≥0) : mgfZ (cbdProd 2 2) t = cbdProdTwoMgf t := by
  simp only [mgfZ, cbdProd, sdExp_bind, sdExp_pure, zpow_mul]
  have hin : ∀ u : ℝ≥0, sdExp (cbd 2) (fun y => ((u ^ y : ℝ≥0) : ℝ≥0∞)) = cbdTwoMgf u :=
    mgfZ_cbd_two
  simp only [hin]
  exact sdExp_cbd_two_coe _

/-! ## The numeric bound for ML-KEM-768 at `t = 81/50` -/

/-- The rational inequality behind `mlkem768_chernoff_value`, with the numerators and
denominators of the moment-generating functions as natural-number variables. -/
theorem chernoff_value_of_nat {np dp nc dc a b m : ℕ} (hdp : 0 < dp) (hdc : 0 < dc)
    (hb : 0 < b) (hm : 0 < m)
    (h : 2 * np ^ 1536 * nc * a ^ 832 * m ≤ dp ^ 1536 * dc * b ^ 832) :
    ((((np : ℝ) / dp) ^ 768 * (nc / dc) * (np / dp) ^ 768 +
        ((np : ℝ) / dp) ^ 768 * (nc / dc) * (np / dp) ^ 768) * ((a : ℝ) / b) ^ 832) ≤
      (m : ℝ)⁻¹ := by
  have hY : (0 : ℝ) < dp ^ 1536 * dc * b ^ 832 := by positivity
  rw [show ((((np : ℝ) / dp) ^ 768 * (nc / dc) * (np / dp) ^ 768 +
        ((np : ℝ) / dp) ^ 768 * (nc / dc) * (np / dp) ^ 768) * ((a : ℝ) / b) ^ 832) =
        (2 * np ^ 1536 * nc * a ^ 832 : ℝ) / (dp ^ 1536 * dc * b ^ 832) by
      field_simp
      ring,
    div_le_iff₀ hY, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact_mod_cast h

set_option exponentiation.threshold 2000 in
/-- The cleared-denominator form of the ML-KEM-768 Chernoff value at `t = 81/50`:
`cbdProdTwoMgf (81/50) = 38976848707971841 / 34437376800000000` and
`cbdTwoMgf (81/50) = 294499921 / 262440000`. -/
theorem mlkem768_chernoff_nat :
    2 * 38976848707971841 ^ 1536 * 294499921 * 50 ^ 832 * 2 ^ 303 ≤
      34437376800000000 ^ 1536 * 262440000 * 81 ^ 832 :=
  Nat.le_of_ble_eq_true rfl

/-- The per-coefficient Chernoff value of ML-KEM-768 at `t = 81/50` is at most `2⁻³⁰³`. -/
theorem mlkem768_chernoff_value :
    (cbdProdTwoMgf (81 / 50) ^ 768 * cbdTwoMgf (81 / 50) * cbdProdTwoMgf (81 / 50)⁻¹ ^ 768 +
        cbdProdTwoMgf (81 / 50)⁻¹ ^ 768 * cbdTwoMgf (81 / 50)⁻¹ * cbdProdTwoMgf (81 / 50) ^ 768) *
        (81 / 50 : ℝ≥0)⁻¹ ^ 832 ≤ (2 ^ 303)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  push_cast [cbdProdTwoMgf, cbdTwoMgf]
  norm_num
  have key := chernoff_value_of_nat (np := 38976848707971841) (dp := 34437376800000000)
    (nc := 294499921) (dc := 262440000) (a := 50) (b := 81) (m := 2 ^ 303)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) mlkem768_chernoff_nat
  simp only [Nat.cast_ofNat, Nat.cast_pow] at key
  exact key

/-- **Tail bound for ML-KEM-768.** One coefficient of the decryption noise of ML-KEM-768
has centred absolute value at least `832` with probability at most `2⁻³⁰³`. -/
theorem mlkem768_coeff_tail_le (i : Fin 256) :
    (PMF.uniformFintype (Coins 3 2 2)).toOuterMeasure
        {c | 832 ≤ centeredAbs (coinNoise c i)} ≤ ((2 : ℝ≥0∞) ^ 303)⁻¹ := by
  have ht : (1 : ℝ≥0) ≤ 81 / 50 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  have ht0 : (81 / 50 : ℝ≥0) ≠ 0 := (zero_lt_one.trans_le ht).ne'
  refine (coinNoise_tail_le 3 2 2 (by norm_num) (by norm_num) i ht).trans ?_
  rw [mgfZ_noiseCoeffLaw _ _ _ ht0, mgfZ_noiseCoeffLaw _ _ _ (inv_ne_zero ht0), inv_inv]
  simp only [mgfZ_cbd_two, mgfZ_cbdProd_two]
  have h := ENNReal.coe_le_coe.2 mlkem768_chernoff_value
  push_cast at h
  push_cast
  exact h

/-- **The decryption-failure hypothesis of ML-KEM-768.** The correctness error of the base
MLWE public-key encryption scheme at `mlkem768Params` is at most
`decryptionFailureProb mlkem768Noise 2⁻³⁰³`: this discharges the hypothesis `hWorst` of the
ML-KEM-768 correctness and IND-CCA theorems. -/
theorem mlkem768_corrWorst_le :
    (MLWE_PKE_Scheme.toScheme mlkem768Params).corrWorst ≤
      decryptionFailureProb mlkem768Noise ((2 : ℝ≥0∞) ^ 303)⁻¹ := by
  rw [mlkem768_failure_from_coeff]
  refine (corrWorst_le_sum_coeff 3 2 2).trans ?_
  calc _ ≤ ∑ _i : Fin 256, ((2 : ℝ≥0∞) ^ 303)⁻¹ :=
        Finset.sum_le_sum fun i _ => mlkem768_coeff_tail_le i
    _ = _ := by simp

/-- The correctness error of `toScheme mlkem768Params` is at most `2⁻²⁹⁵`. -/
theorem mlkem768_corrWorst_le_two_pow :
    (MLWE_PKE_Scheme.toScheme mlkem768Params).corrWorst ≤ ((2 : ℝ≥0∞) ^ 295)⁻¹ := by
  refine mlkem768_corrWorst_le.trans (le_of_eq ?_)
  rw [mlkem768_failure_from_coeff, show (256 : ℝ≥0∞) = 2 ^ 8 by norm_num,
    show (2 : ℝ≥0∞) ^ 303 = 2 ^ 8 * 2 ^ 295 by rw [← pow_add],
    ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

end CatCrypt.Crypto.MLKEM.MLKEMRankInstance

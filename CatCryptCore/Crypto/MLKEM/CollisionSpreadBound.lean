/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.CollisionSpreadLemmas
public import CatCryptCore.Quantum.QROM.CollisionWeight
public import CatCryptCore.Crypto.MLKEM.PRFOracle
public import CatCryptCore.Crypto.KEM.FOTransformU

/-!
# The coin-collision weight of ML-KEM-512

The probability-level assembly of the counting lemmas of
`CollisionSpreadLemmas` into a bound on the key-averaged
coin-collision weight `collWeight` of `CompressedPKE.mlkem512CompressedScheme`.

Two seeds `sd`, `sd'` that encrypt a message to the same ciphertext under the key
`(A, t)` either have a noise difference `d = sampleVec 3 sd.1 - sampleVec 3 sd'.1`
vanishing on `40` or more NTT components, or put `uComp A d` in the compression
window set at their noise polynomials. The first event does not depend on the key
and has probability at most `C(128, 40) · 20^160 · 64^352 / 64^512` over the seed;
the second has probability at most `7^256 / 3329^178` over the uniform matrix `A`.

## Main results

* `collWeight_mapCiphertext_toScheme_eq` — `collWeight` of a ciphertext-mapped MLWE
  scheme is the iterated uniform average over the matrix, the key seed and the
  message of `collProb`
* `collProb_le_add` — the union bound at a fixed key: `collProb` is at most the sum
  of the averaged indicators of the two events
* `prob_zeroPairs_ge_le` — the first event has probability at most
  `C(128, 40) · 20^160 · 64^352 / 64^512` over a uniform seed
* `avg_uComp_mem_le` — the second event has probability at most `7^256 / 3329^178`
  over the uniform matrix
* `collWeight_mlkem512_le` — the coin-collision weight of ML-KEM-512 is at most the
  sum of the two bounds
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.CollisionSpread

open Finset
open scoped ENNReal
open CatCrypt.Quantum.QROM (collProb collWeight)
open CatCrypt.Crypto.MLKEM.PRFOracle (avg avg_mono avg_const avg_add avg_comm avg_fst)
open CatCrypt.Crypto.KEM.FOTransformU (tsum_bind_mul tsum_map_mul)
open CatCrypt.Crypto.MLKEM.Spec.Coeffs
open CatCrypt.Crypto.MLKEM.MLKEM512Instance
open CompressedPKE (MLKEM512CT mlkem512CompressedScheme mapCiphertext)
open MLWE_PKE_Scheme (toScheme)

noncomputable section

/-! ## The average of an indicator -/

/-- The uniform average of the indicator of `p` is the count of `p` over the size of
the type. -/
theorem avg_ite_eq_card {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (avg fun x : α => if p x then (1 : ℝ≥0∞) else 0) =
      ((univ.filter p).card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  unfold avg
  rw [← Finset.mul_sum, Finset.sum_boole, mul_comm]

/-! ## The marginal of key generation -/

section Marginal

variable (P : MLWE_PKE_Scheme.Params) {C' : Type} [DecidableEq C']
  (f : MLWE_PKE_Basic.CT P.toBasic → C') (g : C' → MLWE_PKE_Basic.CT P.toBasic)

/-- `collWeight` of a ciphertext-mapped MLWE scheme is the iterated uniform average over
the matrix, the key seed and the message of `collProb` at the generated public key. -/
theorem collWeight_mapCiphertext_toScheme_eq :
    collWeight (mapCiphertext (toScheme P) f g) =
      avg fun A : P.Mat => avg fun ks : P.KeySeed => avg fun m : P.PT =>
        collProb (mapCiphertext (toScheme P) f g)
          (A, P.vec_add (P.mat_vec_mul A (P.sampleKey ks).1) (P.sampleKey ks).2) m := by
  unfold collWeight
  change ∑' ks, ((PMF.uniformOfFintype P.Mat).bind fun A =>
    (PMF.uniformOfFintype P.KeySeed).map fun ks =>
      ((A, P.vec_add (P.mat_vec_mul A (P.sampleKey ks).1) (P.sampleKey ks).2),
        (P.sampleKey ks).1)) ks * _ = _
  rw [tsum_bind_mul, tsum_fintype]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [tsum_map_mul, tsum_fintype, PMF.uniformOfFintype_apply]
  refine congrArg _ (Finset.sum_congr rfl fun ks _ => ?_)
  rw [PMF.uniformOfFintype_apply]
  rfl

end Marginal

/-! ## The union bound at a fixed key -/

/-- **The union bound at a fixed key.** The collision probability of two uniform seeds
is at most the probability of the first event plus the probability of the second event
at the matrix of the key. -/
theorem collProb_le_add (pk : Mat × Vec) (m : Msg) :
    collProb mlkem512CompressedScheme pk m ≤
      (avg fun r : Seed => avg fun r' : Seed => manyZeros r' r) +
        avg fun r : Seed => avg fun r' : Seed => windowHit pk.1 r' r := by
  change avg (fun r : Seed => avg fun r' : Seed =>
    if mlkem512CompressedScheme.enc pk m r' = mlkem512CompressedScheme.enc pk m r then (1 : ℝ≥0∞)
      else 0) ≤ _
  rw [← avg_add]
  refine avg_mono fun r => ?_
  rw [← avg_add]
  exact avg_mono fun r' => collision_le_indicators pk m r' r

/-! ## The first event over a uniform seed -/

/-- `PrfBlock 3` has `2 ^ 1536` elements. -/
theorem card_prfBlock_three : Fintype.card (PrfBlock 3) = 2 ^ 1536 := by
  rw [Fintype.card_fun, SamplerCbd.card_uint8, Fintype.card_fin, show (256 : ℕ) = 2 ^ 8 from rfl,
    ← pow_mul]

/-- `PrfVecBlock 3` has `64 ^ 512` elements. -/
theorem card_prfVecBlock_three : Fintype.card (PrfVecBlock 3) = 64 ^ 512 := by
  rw [Fintype.card_fun, card_prfBlock_three, Fintype.card_fin, ← pow_mul,
    show (64 : ℕ) = 2 ^ 6 from rfl, ← pow_mul]

/-- **The first event over a uniform seed.** For a fixed seed `r`, the probability over a
uniform seed `r'` that the noise difference vanishes on `40` or more NTT components is
at most `C(128, 40) · 20^160 · 64^352 / 64^512`. -/
theorem prob_zeroPairs_ge_le (r : Seed) :
    (avg fun r' : Seed => manyZeros r' r) ≤
      (Nat.choose 128 40 * (20 ^ 160 * 64 ^ 352) : ℝ≥0∞) / 64 ^ 512 := by
  have h := card_zeroPairs_ge_le r.1
  generalize Nat.choose 128 40 = C at h ⊢
  set g : PrfVecBlock 3 → ℝ≥0∞ := fun x =>
    if 40 ≤ (zeroPairs (sampleVec 3 x - sampleVec 3 r.1)).card then (1 : ℝ≥0∞) else 0 with hg
  change avg (fun p : PrfVecBlock 3 × (PrfVecBlock 2 × PrfBlock 2) => g p.1) ≤ _
  rw [avg_fst, hg, avg_ite_eq_card, card_prfVecBlock_three, div_eq_mul_inv, Nat.cast_pow,
    Nat.cast_ofNat]
  gcongr
  exact_mod_cast h

/-! ## The second event over the uniform matrix -/

/-- `Rq` has `3329 ^ 256` elements. -/
theorem card_rq : Fintype.card Rq = 3329 ^ 256 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- `Mat` has `3329 ^ 1024` elements. -/
theorem card_mat : Fintype.card Mat = 3329 ^ 1024 := by
  rw [Fintype.card_fun, Fintype.card_fun, card_rq, Fintype.card_fin, ← pow_mul, ← pow_mul]

/-- **The second event over the uniform matrix.** When the noise difference `d` vanishes
on at most `39` NTT components, the probability over a uniform matrix `A` that
`uComp A d` lies in a set of at most `7^256` polynomials is at most `7^256 / 3329^178`. -/
theorem avg_uComp_mem_le (d : Vec) (S : Finset Rq) (hS : S.card ≤ 7 ^ 256)
    (hd : (zeroPairs d).card ≤ 39) :
    (avg fun A : Mat => if uComp A d ∈ S then (1 : ℝ≥0∞) else 0) ≤
      (7 ^ 256 : ℝ≥0∞) / 3329 ^ 178 := by
  have h1 : (univ.filter fun A : Mat => uComp A d ∈ S).card ≤
      S.card * 3329 ^ (768 + 2 * (zeroPairs d).card) := card_uComp_mem_le d S
  have hcount : (univ.filter fun A : Mat => uComp A d ∈ S).card ≤ 7 ^ 256 * 3329 ^ 846 :=
    h1.trans (Nat.mul_le_mul hS (pow_le_pow_right₀ (by norm_num) (by omega)))
  rw [avg_ite_eq_card, card_mat]
  calc ((univ.filter fun A : Mat => uComp A d ∈ S).card : ℝ≥0∞) * ((3329 ^ 1024 : ℕ) : ℝ≥0∞)⁻¹
      ≤ ((7 ^ 256 * 3329 ^ 846 : ℕ) : ℝ≥0∞) * ((3329 ^ 1024 : ℕ) : ℝ≥0∞)⁻¹ := by
        gcongr
    _ = (7 ^ 256 : ℝ≥0∞) / 3329 ^ 178 := by
        rw [← div_eq_mul_inv, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow,
          Nat.cast_ofNat, Nat.cast_ofNat, show (1024 : ℕ) = 846 + 178 from rfl, pow_add,
          mul_comm ((7 : ℝ≥0∞) ^ 256)]
        exact ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))
          (ENNReal.pow_ne_top (by norm_num))

/-! ## The assembly -/

/-- **The coin-collision weight of ML-KEM-512.** The expectation over key generation and
a uniform message of the probability that two independent uniform seeds give the same
ciphertext is at most `C(128, 40) · 20^160 · 64^352 / 64^512 + 7^256 / 3329^178`. -/
theorem collWeight_mlkem512_le :
    collWeight mlkem512CompressedScheme ≤
      (Nat.choose 128 40 * (20 ^ 160 * 64 ^ 352) : ℝ≥0∞) / 64 ^ 512 +
        (7 ^ 256 : ℝ≥0∞) / 3329 ^ 178 := by
  have h1 : (avg fun r : Seed => avg fun r' : Seed => manyZeros r' r) ≤
      (Nat.choose 128 40 * (20 ^ 160 * 64 ^ 352) : ℝ≥0∞) / 64 ^ 512 :=
    (avg_mono fun r => prob_zeroPairs_ge_le r).trans (avg_const _).le
  have h2 : (avg fun A : Mat => avg fun r : Seed => avg fun r' : Seed => windowHit A r' r) ≤
      (7 ^ 256 : ℝ≥0∞) / 3329 ^ 178 := by
    rw [avg_comm]
    refine (avg_mono fun r => ?_).trans (avg_const _).le
    rw [avg_comm]
    refine (avg_mono fun r' => ?_).trans (avg_const _).le
    by_cases h40 : 40 ≤ (zeroPairs (sampleVec 3 r'.1 - sampleVec 3 r.1)).card
    · simp only [windowHit, h40, not_true_eq_false, false_and, if_false]
      rw [avg_const]
      exact zero_le
    · simp only [windowHit, h40, not_false_eq_true, true_and]
      exact avg_uComp_mem_le _ _ (card_collWindowSet_le _ _) (by omega)
  generalize Nat.choose 128 40 = C at h1 ⊢
  rw [mlkem512CompressedScheme, collWeight_mapCiphertext_toScheme_eq]
  refine le_trans (avg_mono fun A => avg_mono fun ks => avg_mono fun m =>
    collProb_le_add (A, _) m) ?_
  simp only [avg_add, avg_const]
  exact add_le_add h1 h2

end

end CatCrypt.Crypto.MLKEM.CollisionSpread

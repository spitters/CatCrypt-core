/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.CompressedPKE
public import CatCryptCore.Crypto.MLKEM.SamplerCbd
public import CatCryptCore.Crypto.MLKEM.Spec.Ntt
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Lemmas for the coin-collision bound of ML-KEM-512

Number-theoretic and counting lemmas behind a bound on the probability that two
independent encryption seeds encrypt the same message to the same ciphertext under
`CompressedPKE.mlkem512CompressedScheme`.

## Main definitions

* `compress10Diff` — the residues `δ` with `Compress_{10} x = Compress_{10} (x + δ)`
  for some `x`
* `cbdCoeff3` — the coefficient of the `η = 3` sampler on one window
* `uComp` — the first component of `Aᵀ d`; `zeroPairs` — the NTT components on which
  both entries of a rank-2 vector vanish
* `collWindowSet` — the values of `uComp A (r - r')` compatible with a coefficientwise
  `Compress_{10}` collision at given noise polynomials

## Main results

* `card_compress10Diff_le` — `compress10Diff` has at most `7` elements
* `gammaKem_not_isSquare` — no modulus root `gammaKem j` is a square in `ZMod 3329`
* `basemulPair_left_bijective` — multiplication by a nonzero pair is a bijection of
  the quadratic component when the modulus root is not a square
* `nttKem_bijective` — the ML-KEM transform is a bijection
* `card_cbdCoeff3_eq_le` — at most `20` of the `64` windows at `η = 3` have a given
  coefficient
* `card_filter_pivot_le` — the anticoncentration count: an additive map with a set
  of `k` pivot coordinates vanishes on at most `M^k · |Ω|^(n-k)` of the
  coordinatewise images of `Fin n → Ω`
* `nttHalf_pivot_eq_zero` — the first `|T|` coordinates are pivots of `nttHalf`
  restricted to the output indices in `T`
* `card_uComp_mem_le` — at most `|S| · q^(768 + 2·|zeroPairs d|)` matrices `A` have
  `uComp A d ∈ S`
* `uComp_sub_mem_collWindowSet_of_collision` — a ciphertext collision of two seeds
  puts `uComp A (r - r')` in `collWindowSet`
* `card_zeroPairs_ge_le` — at most `C(128, 40) · 20^160 · 64^352` noise blocks have a
  difference vanishing on `40` or more NTT components
* `collision_le_indicators` — the collision indicator of two seeds at a key is at most
  `manyZeros` (the difference vanishes on `40` or more NTT components) plus `windowHit`
  (it does not, and `uComp A` of it lies in the compression window set)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.CollisionSpread

open Finset
open scoped ENNReal
open CatCrypt.Crypto.MLKEM.Spec.Coeffs
open CatCrypt.Crypto.MLKEM.Spec.Ntt

/-! ## The bucket-difference set of `Compress_{10}` -/

/-- The integer form of the bucket width of `Compress_{10}`: for `a < 3329` and a
shift `4 ≤ δ ≤ 3325`, the rounded `1024 · a / 3329` and the rounded
`1024 · ((a + δ) mod 3329) / 3329` differ modulo `1024`. -/
theorem compress10_nat_ne_shift (a δ : ℕ) (ha : a < 3329) (hδ₁ : 4 ≤ δ) (hδ₂ : δ ≤ 3325) :
    (1024 * a + 1664) / 3329 % 1024 ≠ (1024 * ((a + δ) % 3329) + 1664) / 3329 % 1024 := by
  have e1 := Nat.div_add_mod (1024 * a + 1664) 3329
  have e2 := Nat.mod_lt (1024 * a + 1664) (show 3329 > 0 by norm_num)
  have e3 := Nat.div_add_mod (1024 * ((a + δ) % 3329) + 1664) 3329
  have e4 := Nat.mod_lt (1024 * ((a + δ) % 3329) + 1664) (show 3329 > 0 by norm_num)
  have e5 := Nat.div_add_mod (a + δ) 3329
  have e6 := Nat.mod_lt (a + δ) (show 3329 > 0 by norm_num)
  have e7 : (a + δ) / 3329 ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]
    omega
  generalize (1024 * a + 1664) / 3329 = n₁ at *
  generalize (1024 * ((a + δ) % 3329) + 1664) / 3329 = n₂ at *
  generalize (1024 * a + 1664) % 3329 = r₁ at *
  generalize (1024 * ((a + δ) % 3329) + 1664) % 3329 = r₂ at *
  generalize (a + δ) % 3329 = b at *
  generalize (a + δ) / 3329 = c at *
  have hdiff : (n₁ + 1 ≤ n₂ ∧ n₂ ≤ n₁ + 1023) ∨ (n₂ + 1 ≤ n₁ ∧ n₁ ≤ n₂ + 1023) := by
    interval_cases c <;> omega
  intro heq
  have h1 := Nat.div_add_mod n₁ 1024
  have h2 := Nat.div_add_mod n₂ 1024
  rw [heq] at h1
  generalize n₁ / 1024 = u₁ at *
  generalize n₂ / 1024 = u₂ at *
  generalize n₂ % 1024 = s at *
  omega

/-- `Compress_{10}` separates every two residues whose distance on the circle `Z_q` is
between `4` and `3325`. -/
theorem compress10_ne_shift (z δ : ZMod Compress.q) (hδ₁ : 4 ≤ δ.val) (hδ₂ : δ.val ≤ 3325) :
    Compress.compress_d 10 z ≠ Compress.compress_d 10 (z + δ) := by
  have hz : z.val < 3329 := ZMod.val_lt z
  have hδ : (z + δ).val = (z.val + δ.val) % 3329 := by
    rw [ZMod.val_add]
  unfold Compress.compress_d
  rw [hδ, Ne, ZMod.natCast_eq_natCast_iff']
  norm_num
  exact compress10_nat_ne_shift _ _ hz hδ₁ hδ₂

/-- The residues `δ` for which some `x` and `x + δ` share their `Compress_{10}` value. -/
def compress10Diff : Finset (ZMod Compress.q) :=
  univ.filter fun δ => ∃ x, Compress.compress_d 10 x = Compress.compress_d 10 (x + δ)

/-- A residue in `compress10Diff` is one of `-3, …, 3`. -/
theorem mem_compress10Diff_val (δ : ZMod Compress.q) (h : δ ∈ compress10Diff) :
    δ.val ≤ 3 ∨ 3326 ≤ δ.val := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hx⟩ := (mem_filter.mp h).2
  exact compress10_ne_shift x δ (by omega) (by omega) hx

/-- `compress10Diff` has at most `7` elements. -/
theorem card_compress10Diff_le : compress10Diff.card ≤ 7 := by
  have hsub : compress10Diff ⊆ (univ : Finset (Fin 7)).image
      (fun k : Fin 7 => ((k.val : ℕ) : ZMod Compress.q) - 3) := by
    intro δ hδ
    rw [mem_image]
    rcases mem_compress10Diff_val δ hδ with h | h
    · refine ⟨⟨δ.val + 3, by omega⟩, mem_univ _, ?_⟩
      simp only [Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right, ZMod.natCast_val,
        ZMod.cast_id', id]
    · have hlt : δ.val < 3329 := ZMod.val_lt δ
      refine ⟨⟨δ.val - 3326, by omega⟩, mem_univ _, ?_⟩
      have h3329 : ((3329 : ℕ) : ZMod Compress.q) = 0 := by
        exact ZMod.natCast_self 3329
      calc ((δ.val - 3326 : ℕ) : ZMod Compress.q) - 3
          = ((δ.val - 3326 + 3329 : ℕ) : ZMod Compress.q) - 3 - ((3329 : ℕ) : ZMod Compress.q) := by
            rw [Nat.cast_add, h3329]
            ring
        _ = ((δ.val : ℕ) : ZMod Compress.q) := by
            rw [show δ.val - 3326 + 3329 = δ.val + 3 by omega, Nat.cast_add, h3329]
            norm_num
        _ = δ := ZMod.natCast_zmod_val δ
  exact (card_le_card hsub).trans ((card_image_le).trans (by simp))

/-- The residues `w` for which some `x` has `Compress_{10} (x + a) = Compress_{10} (x + w + b)`:
the coefficient differences `(Aᵀ(r - r'))_i` compatible with a coefficientwise
`Compress_{10}` collision at noise coefficients `a` and `b`. -/
def compress10CollWindow (a b : ZMod Compress.q) : Finset (ZMod Compress.q) :=
  univ.filter fun w => ∃ x, Compress.compress_d 10 (x + a) = Compress.compress_d 10 (x + w + b)

/-- `compress10CollWindow a b` is the translate of `compress10Diff` by `a - b`. -/
theorem compress10CollWindow_subset (a b : ZMod Compress.q) :
    compress10CollWindow a b ⊆ compress10Diff.image (fun δ => δ + a - b) := by
  intro w hw
  obtain ⟨x, hx⟩ := (mem_filter.mp hw).2
  rw [mem_image]
  refine ⟨w + b - a, mem_filter.mpr ⟨mem_univ _, x + a, ?_⟩, by ring⟩
  rw [hx]
  congr 1
  ring

/-- At most `7` coefficient differences are compatible with a `Compress_{10}` collision
at given noise coefficients. -/
theorem card_compress10CollWindow_le (a b : ZMod Compress.q) :
    (compress10CollWindow a b).card ≤ 7 :=
  (card_le_card (compress10CollWindow_subset a b)).trans
    (card_image_le.trans card_compress10Diff_le)

/-! ## The quadratic components are fields -/

/-- `-1 ≠ 1` in `ZMod 3329`. -/
theorem neg_one_ne_one_zq : (-1 : ZMod q_kem) ≠ 1 := by decide

/-- An odd power of `ζ = 17` is not a square in `ZMod 3329`: a square `y²` satisfies
`(y²)^1664 = y^3328 = 1`, while `ζ^(odd · 1664) = (ζ^128)^odd = -1`. -/
theorem zetaKem_pow_odd_not_isSquare (e : ℕ) (he : Odd e) : ¬ IsSquare (zetaKem ^ e) := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : zetaKem ^ e = 0 := by rw [hy]; ring
    exact pow_ne_zero e zetaKem_ne_zero this
  have hfermat : (zetaKem ^ e) ^ 1664 = 1 := by
    rw [hy, ← pow_two, ← pow_mul]
    exact ZMod.pow_card_sub_one_eq_one hy0
  have hneg : (zetaKem ^ e) ^ 1664 = -1 := by
    rw [← pow_mul, show e * 1664 = 128 * (e * 13) by ring, pow_mul, zetaKem_pow_128]
    exact Odd.neg_one_pow (he.mul (by decide))
  exact neg_one_ne_one_zq (hneg.symm.trans hfermat)

/-- No modulus root `gammaKem j = ζ^(2·BitRev7 j + 1)` is a square in `ZMod 3329`. -/
theorem gammaKem_not_isSquare (j : Fin 128) : ¬ IsSquare (gammaKem j) :=
  zetaKem_pow_odd_not_isSquare _ (odd_two_mul_add_one _)

/-- The norm `s₁² - γ s₂²` of a pair is nonzero when the pair is nonzero and `γ` is
not a square. -/
theorem pair_norm_ne_zero (γ : ZMod q_kem) (hγ : ¬ IsSquare γ) (s : ZMod q_kem × ZMod q_kem)
    (hs : s ≠ 0) : s.1 * s.1 - γ * (s.2 * s.2) ≠ 0 := by
  intro h
  by_cases h2 : s.2 = 0
  · apply hs
    rw [h2, mul_zero, mul_zero, sub_zero, mul_self_eq_zero] at h
    exact Prod.ext h h2
  · apply hγ
    refine ⟨s.1 / s.2, ?_⟩
    field_simp
    linear_combination (-1 : ZMod q_kem) * h

/-- The conjugate pair `(s₁, -s₂)` multiplied against `basemulPair γ s t` gives the norm
of `s` times `t`. -/
theorem basemulPair_conj (γ : ZMod q_kem) (s t : ZMod q_kem × ZMod q_kem) :
    basemulPair γ (s.1, -s.2) (basemulPair γ s t) =
      ((s.1 * s.1 - γ * (s.2 * s.2)) * t.1, (s.1 * s.1 - γ * (s.2 * s.2)) * t.2) := by
  simp only [basemulPair]
  ext <;> ring

/-- Base multiplication by a nonzero pair is injective when the modulus root is not a
square: the quadratic component `Z_q[X]/(X² - γ)` is a field. -/
theorem basemulPair_left_injective (γ : ZMod q_kem) (hγ : ¬ IsSquare γ)
    (s : ZMod q_kem × ZMod q_kem) (hs : s ≠ 0) : Function.Injective (basemulPair γ s) := by
  intro t t' h
  have hN := pair_norm_ne_zero γ hγ s hs
  have h1 := congrArg (basemulPair γ (s.1, -s.2)) h
  rw [basemulPair_conj, basemulPair_conj] at h1
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  simp only at e1 e2
  exact Prod.ext (mul_left_cancel₀ hN e1) (mul_left_cancel₀ hN e2)

/-- Base multiplication by a nonzero pair is a bijection of the quadratic component
when the modulus root is not a square. -/
theorem basemulPair_left_bijective (γ : ZMod q_kem) (hγ : ¬ IsSquare γ)
    (s : ZMod q_kem × ZMod q_kem) (hs : s ≠ 0) : Function.Bijective (basemulPair γ s) :=
  Finite.injective_iff_bijective.mp (basemulPair_left_injective γ hγ s hs)

/-- `basemulPair γ` is additive in its right argument. -/
theorem basemulPair_add_right (γ : ZMod q_kem) (s t t' : ZMod q_kem × ZMod q_kem) :
    basemulPair γ s (t + t') = basemulPair γ s t + basemulPair γ s t' := by
  simp only [basemulPair, Prod.fst_add, Prod.snd_add]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- `basemulPair γ` is symmetric. -/
theorem basemulPair_comm (γ : ZMod q_kem) (s t : ZMod q_kem × ZMod q_kem) :
    basemulPair γ s t = basemulPair γ t s := by
  simp only [basemulPair]
  ext <;> ring

/-! ## The transform as a Vandermonde system -/

/-- The evaluation node `ζ^(2k+1)` of output index `k` of `nttHalf`. -/
def nttNode (k : Fin 128) : ZMod q_kem := zetaKem ^ (2 * k.val + 1)

/-- The 128 evaluation nodes are distinct. -/
theorem nttNode_injective : Function.Injective nttNode := by
  intro k k' h
  have hk := k.isLt
  have hk' := k'.isLt
  have := (zetaKem_isPrimitiveRoot.pow_inj (by omega) (by omega)) h
  exact Fin.ext (by omega)

/-- `nttHalf x k` is the evaluation `Σ_j x_j · nttNode k ^ j`. -/
theorem nttHalf_eq_sum_node (x : Fin 128 → ZMod q_kem) (k : Fin 128) :
    nttHalf x k = ∑ j : Fin 128, nttNode k ^ j.val * x j := by
  rw [nttHalf_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nttNode, ← pow_mul, mul_comm, Nat.mul_comm]

/-- **Pivot coordinates of the transform.** A coefficient vector supported on the
first `T.card` indices whose transform vanishes on the output indices in `T` is
zero: the `T.card × T.card` Vandermonde matrix at the distinct nodes of `T` is
invertible. -/
theorem nttHalf_pivot_eq_zero (T : Finset (Fin 128)) (x : Fin 128 → ZMod q_kem)
    (hsupp : ∀ j : Fin 128, T.card ≤ j.val → x j = 0)
    (hvan : ∀ k ∈ T, nttHalf x k = 0) : x = 0 := by
  have hm : T.card ≤ 128 := by
    have := Finset.card_le_univ T
    simpa using this
  set m := T.card with hm_def
  let e : Fin m ≃ T := T.equivFin.symm
  let v : Fin m → ZMod q_kem := fun a => nttNode (e a).1
  have hv : Function.Injective v := fun a b h =>
    e.injective (Subtype.ext (nttNode_injective h))
  let x' : Fin m → ZMod q_kem := fun j => x (Fin.castLE hm j)
  have hsum : ∀ k : Fin 128, nttHalf x k = ∑ j : Fin m, nttNode k ^ (j : ℕ) * x' j := by
    intro k
    rw [nttHalf_eq_sum_node]
    symm
    calc ∑ j : Fin m, nttNode k ^ (j : ℕ) * x' j
        = ∑ j ∈ (univ : Finset (Fin m)).map (Fin.castLEEmb hm), nttNode k ^ j.val * x j := by
          rw [Finset.sum_map]
          rfl
      _ = ∑ j : Fin 128, nttNode k ^ j.val * x j := by
          refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
          rw [hsupp j ?_, mul_zero]
          by_contra hlt
          push Not at hlt
          exact hj (Finset.mem_map.mpr ⟨⟨j.val, hlt⟩, mem_univ _, Fin.ext rfl⟩)
  have hmul : (Matrix.vandermonde v).mulVec x' = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rw [← hsum (e a).1]
    exact hvan _ (e a).2
  have hdet : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hx' : x' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  funext j
  by_cases hj : j.val < m
  · have := congrFun hx' ⟨j.val, hj⟩
    simpa [x'] using this
  · exact hsupp j (by omega)

/-- `nttHalf` is injective. -/
theorem nttHalf_injective : Function.Injective nttHalf := by
  intro x y h
  have hsub : nttHalf (x - y) = 0 := by
    funext k
    rw [show x - y = x + (-y) from sub_eq_add_neg x y, nttHalf_add]
    have hneg : nttHalf (-y) k = -nttHalf y k := by
      simp only [nttHalf_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hneg, h, add_neg_cancel, Pi.zero_apply]
  have hzero := nttHalf_pivot_eq_zero univ (x - y)
    (fun j hj => by simp at hj; omega) (fun k _ => congrFun hsub k)
  exact sub_eq_zero.mp hzero

/-- `nttHalf` of a difference is the difference of the transforms. -/
theorem nttHalf_sub (x y : Fin 128 → ZMod q_kem) (k : Fin 128) :
    nttHalf (x - y) k = nttHalf x k - nttHalf y k := by
  simp only [nttHalf_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The ML-KEM transform is injective. -/
theorem nttKem_injective : Function.Injective nttKem := by
  intro a b h
  have he : nttHalf (evens a) = nttHalf (evens b) := by
    funext k
    have := congrArg Prod.fst (congrFun h (bitRev7 k))
    simpa [nttKem, bitRev7_bitRev7] using this
  have ho : nttHalf (odds a) = nttHalf (odds b) := by
    funext k
    have := congrArg Prod.snd (congrFun h (bitRev7 k))
    simpa [nttKem, bitRev7_bitRev7] using this
  rw [← interleave_evens_odds a, ← interleave_evens_odds b, nttHalf_injective he,
    nttHalf_injective ho]

/-- The ML-KEM transform is a bijection between the coefficient and NTT layouts. -/
theorem nttKem_bijective : Function.Bijective nttKem := by
  refine (Fintype.bijective_iff_injective_and_card nttKem).mpr ⟨nttKem_injective, ?_⟩
  simp only [Tq_kem, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  rw [← pow_two, ← pow_mul]

/-! ## The anticoncentration count -/

section Anticoncentration

variable {ι κ Ω F : Type} [DecidableEq ι]

/-- A coordinatewise image `g ∘ ω` lands in a prescribed vector `v` for at most
`M ^ |ι|` choices of `ω` when every fiber of `g` has at most `M` elements. -/
theorem card_filter_comp_eq_le [Fintype ι] [Fintype Ω] [DecidableEq F] (g : Ω → F) (M : ℕ)
    (hM : ∀ z, (univ.filter fun ω => g ω = z).card ≤ M) (v : ι → F) :
    (univ.filter fun ω : ι → Ω => g ∘ ω = v).card ≤ M ^ Fintype.card ι := by
  classical
  have hset : (univ.filter fun ω : ι → Ω => g ∘ ω = v) =
      Fintype.piFinset fun i => univ.filter fun ω => g ω = v i := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff,
      Function.comp_apply]
  rw [hset, Fintype.card_piFinset]
  calc ∏ i, (univ.filter fun ω => g ω = v i).card ≤ ∏ _i : ι, M :=
        Finset.prod_le_prod' fun i _ => hM (v i)
    _ = M ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

variable [AddCommGroup F]

/-- The extension by zero of a function on the coordinates in `P`. -/
def extendZero (P : Finset ι) (v : {i // i ∈ P} → F) : ι → F :=
  fun i => if h : i ∈ P then v ⟨i, h⟩ else 0

/-- The extension by zero of a function on the coordinates outside `P`. -/
def extendZero' (P : Finset ι) (v : {i // i ∉ P} → F) : ι → F :=
  fun i => if h : i ∉ P then v ⟨i, h⟩ else 0

/-- A function is the sum of the zero-extensions of its restrictions to `P` and to
the complement of `P`. -/
theorem extendZero_add_extendZero' (P : Finset ι) (x : ι → F) :
    extendZero P (fun i => x i.1) + extendZero' P (fun i => x i.1) = x := by
  funext i
  simp only [extendZero, extendZero', Pi.add_apply]
  by_cases h : i ∈ P <;> simp [h]

/-- `extendZero P v` vanishes outside `P`. -/
theorem extendZero_of_not_mem (P : Finset ι) (v : {i // i ∈ P} → F) (i : ι) (hi : i ∉ P) :
    extendZero P v i = 0 := by
  simp [extendZero, hi]

/-- `extendZero P` is injective. -/
theorem extendZero_injective (P : Finset ι) : Function.Injective (extendZero P : _ → ι → F) := by
  intro v w h
  funext ⟨i, hi⟩
  have := congrFun h i
  simpa [extendZero, hi] using this

/-- `extendZero P` is additive. -/
theorem extendZero_add (P : Finset ι) (v w : {i // i ∈ P} → F) :
    extendZero P (v + w) = extendZero P v + extendZero P w := by
  funext i
  simp only [extendZero, Pi.add_apply]
  by_cases h : i ∈ P <;> simp [h]

/-- `extendZero P` maps zero to zero. -/
theorem extendZero_zero (P : Finset ι) : extendZero P (0 : {i // i ∈ P} → F) = 0 := by
  funext i
  simp [extendZero]

/-- **The anticoncentration count.** For an additive map `L` on `ι → F` with a set `P`
of pivot coordinates — `L` is injective on the functions supported in `P` — and a
coordinate map `g : Ω → F` each of whose fibers has at most `M` elements, at most
`M ^ |P| · |Ω| ^ (|ι| - |P|)` of the `ω : ι → Ω` have `L (g ∘ ω) = c`. -/
theorem card_filter_pivot_le [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq F]
    (L : (ι → F) →+ (κ → F)) (P : Finset ι)
    (hinj : ∀ x : ι → F, (∀ i, i ∉ P → x i = 0) → L x = 0 → x = 0)
    (g : Ω → F) (M : ℕ) (hM : ∀ z, (univ.filter fun ω => g ω = z).card ≤ M) (c : κ → F) :
    (univ.filter fun ω : ι → Ω => L (g ∘ ω) = c).card ≤
      M ^ P.card * Fintype.card Ω ^ (Fintype.card ι - P.card) := by
  classical
  let e : (ι → Ω) ≃ ({i // i ∈ P} → Ω) × ({i // i ∉ P} → Ω) :=
    Equiv.piEquivPiSubtypeProd (fun i => i ∈ P) (fun _ => Ω)
  -- the fiber over a fixed assignment of the coordinates outside `P`
  have hfiber : ∀ ω₂ : {i // i ∉ P} → Ω,
      (univ.filter fun ω₁ : {i // i ∈ P} → Ω => L (g ∘ e.symm (ω₁, ω₂)) = c).card ≤
        M ^ P.card := by
    intro ω₂
    -- `g ∘ e.symm (ω₁, ω₂)` splits into the two zero-extensions
    have hsplit : ∀ ω₁ : {i // i ∈ P} → Ω,
        g ∘ e.symm (ω₁, ω₂) = extendZero P (g ∘ ω₁) + extendZero' P (g ∘ ω₂) := by
      intro ω₁
      funext i
      simp only [Function.comp_apply, Pi.add_apply, extendZero, extendZero', e,
        Equiv.piEquivPiSubtypeProd_symm_apply]
      by_cases h : i ∈ P <;> simp [h]
    -- `v ↦ L (extendZero P v)` is injective
    have hLinj : Function.Injective fun v : {i // i ∈ P} → F => L (extendZero P v) := by
      intro v w h
      simp only at h
      have h0 : L (extendZero P (v - w)) = 0 := by
        rw [sub_eq_add_neg, extendZero_add, map_add, h, ← map_add, ← extendZero_add,
          add_neg_cancel, extendZero_zero, map_zero]
      have h1 := hinj _ (fun i hi => extendZero_of_not_mem P _ i hi) h0
      rw [← extendZero_zero P] at h1
      exact sub_eq_zero.mp (extendZero_injective P h1)
    set S := univ.filter fun ω₁ : {i // i ∈ P} → Ω => L (g ∘ e.symm (ω₁, ω₂)) = c with hS
    rcases S.eq_empty_or_nonempty with hemp | ⟨ω₀, hω₀⟩
    · rw [hemp, card_empty]
      exact Nat.zero_le _
    · have hsub : S ⊆ univ.filter fun ω₁ : {i // i ∈ P} → Ω => g ∘ ω₁ = g ∘ ω₀ := by
        intro ω₁ hω₁
        rw [hS, mem_filter] at hω₁ hω₀
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        apply hLinj
        have h1 := hω₁.2
        have h0 := hω₀.2
        rw [hsplit, map_add] at h1 h0
        exact add_right_cancel (h1.trans h0.symm)
      exact (card_le_card hsub).trans
        ((card_filter_comp_eq_le g M hM (g ∘ ω₀)).trans_eq (by rw [Fintype.card_coe]))
  -- sum the fibers
  have hcard : (univ.filter fun ω : ι → Ω => L (g ∘ ω) = c).card =
      ∑ ω₂ : {i // i ∉ P} → Ω,
        (univ.filter fun ω₁ : {i // i ∈ P} → Ω => L (g ∘ e.symm (ω₁, ω₂)) = c).card := by
    rw [← Finset.card_map e.toEmbedding, Finset.card_eq_sum_card_fiberwise
      (f := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
    refine Finset.sum_congr rfl fun ω₂ _ => ?_
    conv_rhs => rw [← Finset.card_map ⟨fun ω₁ => (ω₁, ω₂), fun a b h => (Prod.mk.inj h).1⟩]
    refine congrArg Finset.card ?_
    ext p
    simp only [mem_filter, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨ω, hω, rfl⟩, hsnd⟩
      refine ⟨(e ω).1, ?_, ?_⟩
      · rw [show ((e ω).1, ω₂) = e ω from Prod.ext rfl hsnd.symm, Equiv.symm_apply_apply]
        exact hω
      · exact Prod.ext rfl hsnd.symm
    · rintro ⟨ω₁, hω₁, rfl⟩
      exact ⟨⟨e.symm (ω₁, ω₂), hω₁, Equiv.apply_symm_apply _ _⟩, rfl⟩
  rw [hcard]
  calc ∑ ω₂ : {i // i ∉ P} → Ω,
        (univ.filter fun ω₁ : {i // i ∈ P} → Ω => L (g ∘ e.symm (ω₁, ω₂)) = c).card
      ≤ ∑ _ω₂ : {i // i ∉ P} → Ω, M ^ P.card := Finset.sum_le_sum fun ω₂ _ => hfiber ω₂
    _ = M ^ P.card * Fintype.card Ω ^ (Fintype.card ι - P.card) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Fintype.card_fun,
          Fintype.card_subtype_compl, Fintype.card_coe]

end Anticoncentration

/-! ## The point mass of the `η = 3` centered-binomial sampler -/

/-- `countOnes` of a Boolean vector of length `n` is at most `n`. -/
theorem countOnes_le {n : ℕ} (w : Fin n → Bool) : SamplerCbd.countOnes w ≤ n := by
  unfold SamplerCbd.countOnes
  calc (∑ j, if w j then 1 else 0) ≤ ∑ _j : Fin n, 1 :=
        Finset.sum_le_sum fun j _ => by split <;> omega
    _ = n := by simp

/-- The centered-binomial value of an `η`-window lies in `[-η, η]`. -/
theorem windowVal_bounds {η : ℕ} (w : SamplerCbd.Win η) :
    -(η : ℤ) ≤ SamplerCbd.windowVal w ∧ SamplerCbd.windowVal w ≤ η := by
  have h1 := countOnes_le w.1
  have h2 := countOnes_le w.2
  unfold SamplerCbd.windowVal
  omega

/-- At most `20 = C(6,3)` of the `64` windows at `η = 3` have a given centered-binomial
value. -/
theorem card_windowVal_eq_le (j : ℤ) :
    (univ.filter fun w : SamplerCbd.Win 3 => SamplerCbd.windowVal w = j).card ≤ 20 := by
  by_cases hj : -3 ≤ j ∧ j ≤ 3
  · obtain ⟨hj₁, hj₂⟩ := hj
    interval_cases j <;> decide
  · have hemp : (univ.filter fun w : SamplerCbd.Win 3 => SamplerCbd.windowVal w = j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w _ hw
      have := windowVal_bounds w
      omega
    rw [hemp, card_empty]
    exact Nat.zero_le _

/-- The coefficient map of the `η = 3` sampler on one window. -/
def cbdCoeff3 (w : SamplerCbd.Win 3) : ZMod q_kem := Util.Zq3329.fromInt (SamplerCbd.windowVal w)

/-- At most `20` of the `64` windows at `η = 3` have a given coefficient in `ZMod 3329`:
the sampler's point mass is at most `20/64 = 5/16`. -/
theorem card_cbdCoeff3_eq_le (z : ZMod q_kem) :
    (univ.filter fun w : SamplerCbd.Win 3 => cbdCoeff3 w = z).card ≤ 20 := by
  set S := univ.filter fun w : SamplerCbd.Win 3 => cbdCoeff3 w = z with hS
  rcases S.eq_empty_or_nonempty with hemp | ⟨w₀, hw₀⟩
  · rw [hemp, card_empty]
    exact Nat.zero_le _
  · refine (card_le_card ?_).trans (card_windowVal_eq_le (SamplerCbd.windowVal w₀))
    intro w hw
    rw [hS, mem_filter] at hw hw₀
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h := hw.2.trans hw₀.2.symm
    simp only [cbdCoeff3, Util.Zq3329.fromInt] at h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have b1 := windowVal_bounds w
    have b2 := windowVal_bounds w₀
    omega

/-- The `η = 3` sampler on a block is `cbdCoeff3` on each window. -/
theorem samplePoly_three_eq (b : MLKEM512Instance.PrfBlock 3) :
    MLKEM512Instance.samplePoly 3 b = cbdCoeff3 ∘ SamplerCbd.windowMap 3 b := by
  rw [SamplerCbd.samplePoly_eq]
  rfl

/-! ## The transform and the ring operations of `MLKEM512Instance` -/

open CatCrypt.Crypto.MLKEM.MLKEM512Instance
open CatCrypt.Crypto.Lattice

/-- `evens` is additive. -/
theorem evens_add (a b : Fin 256 → ZMod q_kem) : evens (a + b) = evens a + evens b := rfl

/-- `odds` is additive. -/
theorem odds_add (a b : Fin 256 → ZMod q_kem) : odds (a + b) = odds a + odds b := rfl

/-- `evens` preserves differences. -/
theorem evens_sub (a b : Fin 256 → ZMod q_kem) : evens (a - b) = evens a - evens b := rfl

/-- `odds` preserves differences. -/
theorem odds_sub (a b : Fin 256 → ZMod q_kem) : odds (a - b) = odds a - odds b := rfl

/-- The transform is additive. -/
theorem nttKem_add (a b : Fin 256 → ZMod q_kem) : nttKem (a + b) = nttKem a + nttKem b := by
  funext j
  simp only [nttKem, evens_add, odds_add, nttHalf_add, Pi.add_apply, Prod.mk_add_mk]

/-- The transform preserves differences. -/
theorem nttKem_sub (a b : Fin 256 → ZMod q_kem) : nttKem (a - b) = nttKem a - nttKem b := by
  funext j
  simp only [nttKem, evens_sub, odds_sub, nttHalf_sub, Pi.sub_apply, Prod.mk_sub_mk]

/-- The transform of the zero polynomial is zero. -/
theorem nttKem_zero : nttKem 0 = 0 := by
  have := nttKem_sub 0 0
  rwa [sub_self, sub_self] at this

/-- `ringMul` of `MLKEM512Instance` is `polyMulKem`. -/
theorem ringMul_eq_polyMulKem (a b : Rq) : ringMul a b = polyMulKem a b := rfl

/-- The transform carries `ringMul` to `basemulKem`. -/
theorem nttKem_ringMul (a b : Rq) : nttKem (ringMul a b) = basemulKem (nttKem a) (nttKem b) := by
  rw [ringMul_eq_polyMulKem, ← negaMulKem_eq_polyMulKem, nttKem_negaMulKem]

/-- `ringMul` preserves differences in its right argument. -/
theorem ringMul_sub_right (a b c : Rq) : ringMul a (b - c) = ringMul a b - ringMul a c := by
  funext k
  simp only [ringMul, SignedNegacyclicConv.signedNegaConv, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- The first component of `Aᵀ d`. -/
def uComp (A : Mat) (d : Vec) : Rq := matVecMul (matTranspose A) d 0

/-- `uComp A d` is `ringMul (A 0 0) (d 0) + ringMul (A 1 0) (d 1)`. -/
theorem uComp_eq (A : Mat) (d : Vec) :
    uComp A d = ringMul (A 0 0) (d 0) + ringMul (A 1 0) (d 1) := by
  simp only [uComp, matVecMul, matTranspose, Fin.sum_univ_two]

/-- `uComp A` preserves differences. -/
theorem uComp_sub (A : Mat) (d d' : Vec) : uComp A (d - d') = uComp A d - uComp A d' := by
  simp only [uComp_eq, Pi.sub_apply, ringMul_sub_right]
  abel

/-- The NTT components on which both entries of a rank-2 vector vanish. -/
def zeroPairs (d : Vec) : Finset (Fin 128) :=
  univ.filter fun ℓ => nttKem (d 0) ℓ = 0 ∧ nttKem (d 1) ℓ = 0

/-! ## The count of matrices with `uComp A d` in a prescribed set -/

set_option linter.constructorNameAsVariable false in
/-- The fiber of `(p, p') ↦ p·s + p'·s'` in one quadratic component has at most `q²`
elements when `s` or `s'` is nonzero. -/
theorem card_basemul_fiber_le (γ : ZMod q_kem) (hγ : ¬ IsSquare γ)
    (s s' t : ZMod q_kem × ZMod q_kem) (hss : s ≠ 0 ∨ s' ≠ 0) :
    (univ.filter fun y : (ZMod q_kem × ZMod q_kem) × (ZMod q_kem × ZMod q_kem) =>
      basemulPair γ y.1 s + basemulPair γ y.2 s' = t).card ≤ q_kem ^ 2 := by
  have hcard : Fintype.card (ZMod q_kem × ZMod q_kem) = q_kem ^ 2 := by
    rw [Fintype.card_prod, ZMod.card, pow_two]
  rcases hss with hs | hs'
  · refine le_trans (card_le_card_of_injOn (fun y => y.2) (fun _ _ => mem_univ _) ?_)
      (by rw [card_univ, hcard])
    intro y hy y' hy' h
    rw [mem_coe, mem_filter] at hy hy'
    have h1 : basemulPair γ y.1 s = basemulPair γ y'.1 s := by
      have := hy.2.trans hy'.2.symm
      simp only at h
      rw [h] at this
      exact add_right_cancel this
    rw [basemulPair_comm γ y.1 s, basemulPair_comm γ y'.1 s] at h1
    exact Prod.ext (basemulPair_left_injective γ hγ s hs h1) h
  · refine le_trans (card_le_card_of_injOn (fun y => y.1) (fun _ _ => mem_univ _) ?_)
      (by rw [card_univ, hcard])
    intro y hy y' hy' h
    rw [mem_coe, mem_filter] at hy hy'
    have h1 : basemulPair γ y.2 s' = basemulPair γ y'.2 s' := by
      have := hy.2.trans hy'.2.symm
      simp only at h
      rw [h] at this
      exact add_left_cancel this
    rw [basemulPair_comm γ y.2 s', basemulPair_comm γ y'.2 s'] at h1
    exact Prod.ext h (basemulPair_left_injective γ hγ s' hs' h1)

/-- The transformed form of `(a₀, a₁) ↦ ringMul a₀ (d 0) + ringMul a₁ (d 1)`: base
multiplication against the transform of `d` in each component. -/
def uCompHat (d : Vec) (P : Tq_kem × Tq_kem) : Tq_kem :=
  fun ℓ => basemulPair (gammaKem ℓ) (P.1 ℓ) (nttKem (d 0) ℓ) +
    basemulPair (gammaKem ℓ) (P.2 ℓ) (nttKem (d 1) ℓ)

/-- The transform of `ringMul a₀ (d 0) + ringMul a₁ (d 1)` is `uCompHat d` at the
transforms of `a₀`, `a₁`. -/
theorem nttKem_uComp_pair (d : Vec) (a₀ a₁ : Rq) :
    nttKem (ringMul a₀ (d 0) + ringMul a₁ (d 1)) = uCompHat d (nttKem a₀, nttKem a₁) := by
  rw [nttKem_add, nttKem_ringMul, nttKem_ringMul]
  rfl

/-- The fiber of `uCompHat d` over any target has at most `q^(256 + 2·|zeroPairs d|)`
elements. -/
theorem card_uCompHat_fiber_le (d : Vec) (t : Tq_kem) :
    (univ.filter fun P : Tq_kem × Tq_kem => uCompHat d P = t).card ≤
      q_kem ^ (256 + 2 * (zeroPairs d).card) := by
  classical
  -- pass to the coordinatewise form on `Fin 128 → (pair × pair)`
  let e : Tq_kem × Tq_kem ≃ (Fin 128 → (ZMod q_kem × ZMod q_kem) × (ZMod q_kem × ZMod q_kem)) :=
    (Equiv.arrowProdEquivProdArrow _ _ _).symm
  let f : Fin 128 → (ZMod q_kem × ZMod q_kem) × (ZMod q_kem × ZMod q_kem) →
      ZMod q_kem × ZMod q_kem := fun ℓ y =>
    basemulPair (gammaKem ℓ) y.1 (nttKem (d 0) ℓ) + basemulPair (gammaKem ℓ) y.2 (nttKem (d 1) ℓ)
  have hset : (univ.filter fun P : Tq_kem × Tq_kem => uCompHat d P = t) =
      (Fintype.piFinset fun ℓ => univ.filter fun y => f ℓ y = t ℓ).map e.symm.toEmbedding := by
    ext P
    simp only [mem_filter, mem_univ, true_and, mem_map_equiv, Equiv.symm_symm,
      Fintype.mem_piFinset, funext_iff]
    rfl
  rw [hset, card_map, Fintype.card_piFinset]
  have hb : ∀ ℓ, (univ.filter fun y => f ℓ y = t ℓ).card ≤
      if ℓ ∈ zeroPairs d then q_kem ^ 4 else q_kem ^ 2 := by
    intro ℓ
    split_ifs with hℓ
    · refine (card_le_univ _).trans (le_of_eq ?_)
      simp only [Fintype.card_prod, ZMod.card]
      ring
    · simp only [zeroPairs, mem_filter, mem_univ, true_and, not_and_or] at hℓ
      exact card_basemul_fiber_le _ (gammaKem_not_isSquare ℓ) _ _ _ hℓ
  calc ∏ ℓ, (univ.filter fun y => f ℓ y = t ℓ).card
      ≤ ∏ ℓ : Fin 128, (if ℓ ∈ zeroPairs d then q_kem ^ 4 else q_kem ^ 2) :=
        Finset.prod_le_prod' fun ℓ _ => hb ℓ
    _ = q_kem ^ (256 + 2 * (zeroPairs d).card) := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        have h1 : (univ.filter fun ℓ => ℓ ∈ zeroPairs d) = zeroPairs d := by
          ext ℓ; simp
        have h2 : (univ.filter fun ℓ => ℓ ∉ zeroPairs d).card = 128 - (zeroPairs d).card := by
          rw [Finset.filter_not, Finset.card_sdiff_of_subset (subset_univ _), h1, card_univ,
            Fintype.card_fin]
        have hle : (zeroPairs d).card ≤ 128 := by
          have := card_le_univ (zeroPairs d)
          simpa using this
        rw [h1, h2, ← pow_mul, ← pow_mul, ← pow_add]
        exact congrArg (fun n => q_kem ^ n) (by omega)

set_option linter.constructorNameAsVariable false in
/-- At most `|S| · q^(768 + 2·|zeroPairs d|)` matrices `A` have `uComp A d ∈ S`: the two
entries of the first column determine `uComp A d`, and through the transform their
`128` quadratic components are independent, each uniform on a component where `d`
does not vanish. -/
theorem card_uComp_mem_le (d : Vec) (S : Finset Rq) :
    (univ.filter fun A : Mat => uComp A d ∈ S).card ≤
      S.card * q_kem ^ (768 + 2 * (zeroPairs d).card) := by
  -- the first column
  let π : Mat → Rq × Rq := fun A => (A 0 0, A 1 0)
  have hπ : ∀ A, uComp A d = ringMul (π A).1 (d 0) + ringMul (π A).2 (d 1) := fun A =>
    uComp_eq A d
  have hcardRq : Fintype.card Rq = q_kem ^ 256 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  -- fibers of `π` have at most `q^512` elements
  have hfib : ∀ p ∈ (univ.filter fun A : Mat => uComp A d ∈ S).image π,
      ((univ.filter fun A : Mat => uComp A d ∈ S).filter fun A => π A = p).card ≤
        q_kem ^ 512 := by
    intro p _
    refine le_trans (card_le_card_of_injOn (fun A : Mat => (A 0 1, A 1 1))
      (fun _ _ => mem_univ _) ?_) ?_
    · intro A hA B hB h
      rw [mem_coe, mem_filter] at hA hB
      simp only [Prod.mk.injEq] at h
      have hAB := hA.2.trans hB.2.symm
      simp only [π, Prod.mk.injEq] at hAB
      funext i j
      fin_cases i <;> fin_cases j
      · exact hAB.1
      · exact h.1
      · exact hAB.2
      · exact h.2
    · rw [card_univ, Fintype.card_prod, hcardRq, ← pow_add]
  -- the image of `π` lies in the pairs whose combination is in `S`
  have himg : (univ.filter fun A : Mat => uComp A d ∈ S).image π ⊆
      univ.filter fun p : Rq × Rq => ringMul p.1 (d 0) + ringMul p.2 (d 1) ∈ S := by
    intro p hp
    rw [mem_image] at hp
    rw [mem_filter_univ]
    cases hp with
    | intro A hA =>
      rw [mem_filter_univ] at hA
      rw [← hA.2, ← hπ A]
      exact hA.1
  -- pairs through the transform
  have hpairs : (univ.filter fun p : Rq × Rq =>
      ringMul p.1 (d 0) + ringMul p.2 (d 1) ∈ S).card ≤
        S.card * q_kem ^ (256 + 2 * (zeroPairs d).card) := by
    let N : Rq × Rq → Tq_kem × Tq_kem := fun p => (nttKem p.1, nttKem p.2)
    have hN : Function.Injective N := fun p p' h => by
      simp only [N, Prod.mk.injEq] at h
      exact Prod.ext (nttKem_injective h.1) (nttKem_injective h.2)
    have hmem : ∀ p : Rq × Rq, ringMul p.1 (d 0) + ringMul p.2 (d 1) ∈ S ↔
        uCompHat d (N p) ∈ S.image nttKem := by
      intro p
      rw [← nttKem_uComp_pair]
      constructor
      · intro h
        exact mem_image_of_mem _ h
      · intro h
        obtain ⟨y, hy, hyx⟩ := mem_image.mp h
        rwa [← nttKem_injective hyx]
    simp_rw [hmem]
    -- the preimage of `S.image nttKem` is covered by the fibers over its elements
    have hcover : (univ.filter fun P : Tq_kem × Tq_kem => uCompHat d P ∈ S.image nttKem) ⊆
        (S.image nttKem).biUnion fun t => univ.filter fun P : Tq_kem × Tq_kem =>
          uCompHat d P = t := by
      intro P hP
      rw [mem_filter] at hP
      rw [mem_biUnion]
      refine ⟨uCompHat d P, hP.2, ?_⟩
      rw [mem_filter_univ]
    have hmaps : Set.MapsTo N
        ↑(univ.filter fun p : Rq × Rq => uCompHat d (N p) ∈ S.image nttKem)
        ↑(univ.filter fun P : Tq_kem × Tq_kem => uCompHat d P ∈ S.image nttKem) := by
      intro p hp
      rw [mem_coe, mem_filter_univ] at hp ⊢
      exact hp
    calc (univ.filter fun p : Rq × Rq => uCompHat d (N p) ∈ S.image nttKem).card
        ≤ (univ.filter fun P : Tq_kem × Tq_kem => uCompHat d P ∈ S.image nttKem).card :=
          card_le_card_of_injOn N hmaps hN.injOn
      _ ≤ ∑ t ∈ S.image nttKem,
            (univ.filter fun P : Tq_kem × Tq_kem => uCompHat d P = t).card :=
          (card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ _t ∈ S.image nttKem, q_kem ^ (256 + 2 * (zeroPairs d).card) :=
          Finset.sum_le_sum fun t _ => card_uCompHat_fiber_le d t
      _ ≤ S.card * q_kem ^ (256 + 2 * (zeroPairs d).card) := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ card_image_le
  calc (univ.filter fun A : Mat => uComp A d ∈ S).card
      ≤ q_kem ^ 512 * ((univ.filter fun A : Mat => uComp A d ∈ S).image π).card :=
        card_le_mul_card_image _ _ hfib
    _ ≤ q_kem ^ 512 * (S.card * q_kem ^ (256 + 2 * (zeroPairs d).card)) :=
        Nat.mul_le_mul_left _ ((card_le_card himg).trans hpairs)
    _ = S.card * q_kem ^ (768 + 2 * (zeroPairs d).card) := by
        rw [mul_left_comm, ← pow_add]
        exact congrArg (fun n => S.card * q_kem ^ n) (by omega)

/-! ## Collisions and the compression windows -/

/-- The polynomials whose `i`-th coefficient lies in `compress10CollWindow (e' i) (e i)`
for every `i`: the values of `uComp A (r - r')` compatible with a coefficientwise
`Compress_{10}` collision of the first ciphertext components at noise `e` and `e'`. -/
def collWindowSet (e e' : Rq) : Finset Rq :=
  Fintype.piFinset fun i => compress10CollWindow (e' i) (e i)

/-- `collWindowSet` has at most `7^256` elements. -/
theorem card_collWindowSet_le (e e' : Rq) : (collWindowSet e e').card ≤ 7 ^ 256 := by
  rw [collWindowSet, Fintype.card_piFinset]
  calc ∏ i, (compress10CollWindow (e' i) (e i)).card ≤ ∏ _i : Fin 256, 7 :=
        Finset.prod_le_prod' fun i _ => card_compress10CollWindow_le _ _
    _ = 7 ^ 256 := by simp

open CompressedPKE (MLKEM512CT mlkem512Compress mlkem512CompressedScheme)

/-- Encryption in `mlkem512CompressedScheme`, with the record fields unfolded. -/
theorem enc_unfold (pk : Mat × Vec) (m : Msg) (sd : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2) :
    mlkem512CompressedScheme.enc pk m sd =
      mlkem512Compress
        (vecAdd (matVecMul (matTranspose pk.1) (sampleVec 3 sd.1)) (sampleVec 2 sd.2.1),
          ringAdd (ringAdd (vecDot pk.2 (sampleVec 3 sd.1)) (samplePoly 2 sd.2.2))
            (msgEncode m)) :=
  congrArg mlkem512Compress rfl

/-- A ciphertext collision of two seeds under `pk = (A, t)` forces the first
coefficientwise `Compress_{10}` values to agree, which puts
`uComp A (sampleVec 3 r - sampleVec 3 r')` in `collWindowSet` at the noise
polynomials `sampleVec 2 e 0` and `sampleVec 2 e' 0`. -/
theorem uComp_sub_mem_collWindowSet_of_collision (pk : Mat × Vec) (m : Msg)
    (sd sd' : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2)
    (h : mlkem512CompressedScheme.enc pk m sd = mlkem512CompressedScheme.enc pk m sd') :
    uComp pk.1 (sampleVec 3 sd.1 - sampleVec 3 sd'.1) ∈
      collWindowSet (sampleVec 2 sd.2.1 0) (sampleVec 2 sd'.2.1 0) := by
  rw [enc_unfold, enc_unfold] at h
  have hu := congrArg (fun c : MLKEM512CT => c.1 0) h
  simp only [mlkem512Compress, CompressedPKE.compressCT, vecAdd] at hu
  rw [collWindowSet, Fintype.mem_piFinset]
  intro i
  have hi : Compress.compress_d 10
      (matVecMul (matTranspose pk.1) (sampleVec 3 sd.1) 0 i + sampleVec 2 sd.2.1 0 i) =
      Compress.compress_d 10
        (matVecMul (matTranspose pk.1) (sampleVec 3 sd'.1) 0 i + sampleVec 2 sd'.2.1 0 i) :=
    congrFun hu i
  rw [compress10CollWindow, mem_filter]
  refine ⟨mem_univ _, matVecMul (matTranspose pk.1) (sampleVec 3 sd'.1) 0 i, ?_⟩
  rw [uComp_sub]
  simp only [uComp, Pi.sub_apply]
  have hre : ∀ x y z : ZMod q_kem, x + (y - x) + z = y + z := fun x y z => by ring
  rw [hre]
  exact hi.symm

/-! ## The count of noise blocks whose difference vanishes on many NTT components -/

/-- The `512` bit windows of a rank-2 block at `η = 3`, indexed by component and
coefficient. -/
noncomputable def blockWindows : PrfVecBlock 3 ≃ (Fin 2 × Fin 256 → SamplerCbd.Win 3) :=
  (Equiv.piCongrRight fun _ =>
      Equiv.ofBijective _ (SamplerCbd.windowMap_bijective 3 (by norm_num))).trans
    (Equiv.curry (Fin 2) (Fin 256) (SamplerCbd.Win 3)).symm

/-- Window `(i, j)` of a block is window `j` of component `i`. -/
theorem blockWindows_apply (r : PrfVecBlock 3) (p : Fin 2 × Fin 256) :
    blockWindows r p = SamplerCbd.windowMap 3 (r p.1) p.2 := rfl

/-- A rank-2 vector as a function of component and coefficient. -/
def flatVec (v : Vec) : Fin 2 × Fin 256 → ZMod q_kem := fun p => v p.1 p.2

/-- The coefficients of the `η = 3` sampler on a block are `cbdCoeff3` on its windows. -/
theorem cbdCoeff3_comp_blockWindows (r : PrfVecBlock 3) :
    cbdCoeff3 ∘ blockWindows r = flatVec (sampleVec 3 r) := by
  funext p
  simp only [Function.comp_apply, blockWindows_apply, flatVec, sampleVec, samplePoly_three_eq]

/-- The two coordinates of the transform of each component at the NTT indices in `T`,
as an additive map on flattened rank-2 vectors. -/
def nttRestrict (T : Finset (Fin 128)) :
    (Fin 2 × Fin 256 → ZMod q_kem) →+ (Fin 2 × T × Bool → ZMod q_kem) where
  toFun x := fun p =>
    if p.2.2 then (nttKem (fun j => x (p.1, j)) p.2.1).2 else (nttKem (fun j => x (p.1, j)) p.2.1).1
  map_zero' := by
    funext p
    have h0 : (fun j => (0 : Fin 2 × Fin 256 → ZMod q_kem) (p.1, j)) = 0 := rfl
    rw [h0, nttKem_zero]
    simp only [Pi.zero_apply, Prod.fst_zero, Prod.snd_zero, ite_self]
  map_add' := by
    intro x y
    funext p
    have h : (fun j => (x + y) (p.1, j)) = (fun j => x (p.1, j)) + (fun j => y (p.1, j)) := rfl
    rw [h, nttKem_add]
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
    split_ifs <;> rfl

/-- `nttRestrict T` on a flattened vector reads the transform of each component. -/
theorem nttRestrict_flatVec (T : Finset (Fin 128)) (v : Vec) (p : Fin 2 × T × Bool) :
    nttRestrict T (flatVec v) p =
      if p.2.2 then (nttKem (v p.1) p.2.1).2 else (nttKem (v p.1) p.2.1).1 := rfl

/-- The pivot coordinates for `m` NTT indices: the first `2m` coefficients of each
component. -/
def pivotSet (m : ℕ) : Finset (Fin 2 × Fin 256) := univ.filter fun p => p.2.val < 2 * m

/-- `pivotSet m` has `4m` elements for `m ≤ 128`. -/
theorem card_pivotSet (m : ℕ) (hm : m ≤ 128) : (pivotSet m).card = 4 * m := by
  have hset : pivotSet m = (univ : Finset (Fin 2)) ×ˢ (univ.filter fun j : Fin 256 => j.val < 2 * m) := by
    ext p
    simp [pivotSet]
  rw [hset, card_product, Fin.card_filter_val_lt, card_univ, Fintype.card_fin]
  omega

/-- `interleave 0 0 = 0`. -/
theorem interleave_zero : interleave 0 0 = 0 := by
  funext i
  simp only [interleave, coeffsOfPairs, Pi.zero_apply, ite_self]

/-- `bitRev7` is injective. -/
theorem bitRev7_injective : Function.Injective bitRev7 :=
  Function.Involutive.injective bitRev7_bitRev7

/-- **`pivotSet T.card` is a set of pivot coordinates of `nttRestrict T`.** A flattened
vector supported on the first `2·|T|` coefficients of each component whose transforms
vanish on `T` is zero. -/
theorem nttRestrict_pivot_eq_zero (T : Finset (Fin 128)) (x : Fin 2 × Fin 256 → ZMod q_kem)
    (hsupp : ∀ p, p ∉ pivotSet T.card → x p = 0) (h0 : nttRestrict T x = 0) : x = 0 := by
  have hT : (T.image bitRev7).card = T.card := card_image_of_injective T bitRev7_injective
  funext p
  obtain ⟨i, j⟩ := p
  set a : Fin 256 → ZMod q_kem := fun j => x (i, j) with ha
  have hvan : ∀ ℓ ∈ T, nttKem a ℓ = 0 := by
    intro ℓ hℓ
    have h1 := congrFun h0 (i, ⟨ℓ, hℓ⟩, false)
    have h2 := congrFun h0 (i, ⟨ℓ, hℓ⟩, true)
    simp only [nttRestrict, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Bool.false_eq_true, if_false,
      if_true, Pi.zero_apply] at h1 h2
    exact Prod.ext h1 h2
  have hsupp' : ∀ q : Fin 256, 2 * T.card ≤ q.val → a q = 0 := by
    intro q hq
    apply hsupp
    simp only [pivotSet, mem_filter_univ, not_lt]
    exact hq
  have he : evens a = 0 := by
    refine nttHalf_pivot_eq_zero (T.image bitRev7) (evens a) ?_ ?_
    · intro q hq
      rw [hT] at hq
      apply hsupp'
      simp only [pairFst_val]
      omega
    · intro k hk
      obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp hk
      have := congrArg Prod.fst (hvan ℓ hℓ)
      simpa [nttKem] using this
  have ho : odds a = 0 := by
    refine nttHalf_pivot_eq_zero (T.image bitRev7) (odds a) ?_ ?_
    · intro q hq
      rw [hT] at hq
      apply hsupp'
      simp only [pairSnd_val]
      omega
    · intro k hk
      obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp hk
      have := congrArg Prod.snd (hvan ℓ hℓ)
      simpa [nttKem] using this
  have : a = 0 := by
    rw [← interleave_evens_odds a, he, ho, interleave_zero]
  exact congrFun this j

/-- `T ⊆ zeroPairs (sampleVec 3 r - sampleVec 3 r')` is the equation
`nttRestrict T (cbdCoeff3 ∘ blockWindows r) = nttRestrict T (flatVec (sampleVec 3 r'))`. -/
theorem subset_zeroPairs_iff (T : Finset (Fin 128)) (r r' : PrfVecBlock 3) :
    T ⊆ zeroPairs (sampleVec 3 r - sampleVec 3 r') ↔
      nttRestrict T (cbdCoeff3 ∘ blockWindows r) = nttRestrict T (flatVec (sampleVec 3 r')) := by
  rw [cbdCoeff3_comp_blockWindows]
  constructor
  · intro h
    funext p
    obtain ⟨i, ⟨ℓ, hℓ⟩, b⟩ := p
    have hz := h hℓ
    simp only [zeroPairs, mem_filter_univ] at hz
    have hi : nttKem (sampleVec 3 r i) ℓ = nttKem (sampleVec 3 r' i) ℓ := by
      have hsub : nttKem (sampleVec 3 r i - sampleVec 3 r' i) ℓ = 0 := by
        fin_cases i
        · exact hz.1
        · exact hz.2
      rw [nttKem_sub, Pi.sub_apply, sub_eq_zero] at hsub
      exact hsub
    simp only [nttRestrict_flatVec, hi]
  · intro h ℓ hℓ
    simp only [zeroPairs, mem_filter_univ]
    have hi : ∀ i : Fin 2, nttKem (sampleVec 3 r i - sampleVec 3 r' i) ℓ = 0 := by
      intro i
      have h1 := congrFun h (i, ⟨ℓ, hℓ⟩, false)
      have h2 := congrFun h (i, ⟨ℓ, hℓ⟩, true)
      simp only [nttRestrict_flatVec, Bool.false_eq_true, if_false, if_true] at h1 h2
      rw [nttKem_sub, Pi.sub_apply, sub_eq_zero]
      exact Prod.ext h1 h2
    exact ⟨hi 0, hi 1⟩

/-- The `η = 3` window type has `64` elements. -/
theorem card_win3 : Fintype.card (SamplerCbd.Win 3) = 64 := by
  simp [SamplerCbd.Win]

/-- **Anticoncentration of the noise difference on `m` NTT components.** For every
`T` of `m ≤ 128` NTT indices and every fixed block `r'`, at most
`20^(4m) · 64^(512 - 4m)` blocks `r` have `sampleVec 3 r - sampleVec 3 r'` vanishing
on `T`. -/
theorem card_zeroPairs_superset_le (T : Finset (Fin 128)) (r' : PrfVecBlock 3) :
    (univ.filter fun r : PrfVecBlock 3 => T ⊆ zeroPairs (sampleVec 3 r - sampleVec 3 r')).card ≤
      20 ^ (4 * T.card) * 64 ^ (512 - 4 * T.card) := by
  have hm : T.card ≤ 128 := by
    have := card_le_univ T
    simpa using this
  have hset : (univ.filter fun r : PrfVecBlock 3 =>
      T ⊆ zeroPairs (sampleVec 3 r - sampleVec 3 r')) =
      (univ.filter fun ω : Fin 2 × Fin 256 → SamplerCbd.Win 3 =>
        nttRestrict T (cbdCoeff3 ∘ ω) =
          nttRestrict T (flatVec (sampleVec 3 r'))).map blockWindows.symm.toEmbedding := by
    ext r
    rw [mem_map_equiv, Equiv.symm_symm, mem_filter_univ, mem_filter_univ, subset_zeroPairs_iff]
  rw [hset, card_map]
  have h := card_filter_pivot_le (nttRestrict T) (pivotSet T.card)
    (nttRestrict_pivot_eq_zero T) cbdCoeff3 20 card_cbdCoeff3_eq_le
    (nttRestrict T (flatVec (sampleVec 3 r')))
  rwa [card_pivotSet _ hm, card_win3, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h

set_option linter.constructorNameAsVariable false in
/-- **At most `C(128, 40) · 20^160 · 64^352` blocks `r` have `sampleVec 3 r - sampleVec 3 r'`
vanishing on `40` or more NTT components.** -/
theorem card_zeroPairs_ge_le (r' : PrfVecBlock 3) :
    (univ.filter fun r : PrfVecBlock 3 =>
      40 ≤ (zeroPairs (sampleVec 3 r - sampleVec 3 r')).card).card ≤
      Nat.choose 128 40 * (20 ^ 160 * 64 ^ 352) := by
  have hsub : (univ.filter fun r : PrfVecBlock 3 =>
      40 ≤ (zeroPairs (sampleVec 3 r - sampleVec 3 r')).card) ⊆
      (powersetCard 40 (univ : Finset (Fin 128))).biUnion fun T =>
        univ.filter fun r : PrfVecBlock 3 => T ⊆ zeroPairs (sampleVec 3 r - sampleVec 3 r') := by
    intro r hr
    rw [mem_filter_univ] at hr
    rw [mem_biUnion]
    obtain ⟨T, hT, hTcard⟩ := exists_subset_card_eq hr
    refine ⟨T, mem_powersetCard.mpr ⟨subset_univ _, hTcard⟩, ?_⟩
    rw [mem_filter_univ]
    exact hT
  calc (univ.filter fun r : PrfVecBlock 3 =>
        40 ≤ (zeroPairs (sampleVec 3 r - sampleVec 3 r')).card).card
      ≤ ∑ T ∈ powersetCard 40 (univ : Finset (Fin 128)),
          (univ.filter fun r : PrfVecBlock 3 =>
            T ⊆ zeroPairs (sampleVec 3 r - sampleVec 3 r')).card :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ T ∈ powersetCard 40 (univ : Finset (Fin 128)), 20 ^ 160 * 64 ^ 352 := by
        refine Finset.sum_le_sum fun T hT => ?_
        have hT := (mem_powersetCard.mp hT).2
        have := card_zeroPairs_superset_le T r'
        rwa [hT] at this
    _ = Nat.choose 128 40 * (20 ^ 160 * 64 ^ 352) := by
        rw [Finset.sum_const_nat fun _ _ => rfl, card_powersetCard, card_univ, Fintype.card_fin]

/-! ## The collision indicator against the two events -/

/-- The encryption seed type of ML-KEM-512: the `PRF_η` blocks of `r`, `e₁` and `e₂`. -/
abbrev Seed : Type := PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2

/-- The indicator of the first event: the difference of the `η = 3` noise blocks of `sd`
and `sd'` vanishes on `40` or more NTT components. -/
def manyZeros (sd sd' : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2) : ℝ≥0∞ :=
  if 40 ≤ (zeroPairs (sampleVec 3 sd.1 - sampleVec 3 sd'.1)).card then 1 else 0

/-- The first component of the `η = 2` noise vector of a seed. The index `0 : Fin 2` is
elaborated once here; a term that names the first noise polynomial through `noise1`
carries no proof of `NeZero 2` of its own, so two such terms are syntactically equal
and the unifier never evaluates the window set to compare them. -/
def noise1 (sd : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2) : Rq := sampleVec 2 sd.2.1 0

/-- The indicator of the second event at the matrix `A`: the noise difference vanishes
on fewer than `40` NTT components and `uComp A` of it lies in the compression window
set at the `η = 2` noise polynomials of the two seeds. -/
def windowHit (A : Mat) (sd sd' : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2) : ℝ≥0∞ :=
  if ¬ 40 ≤ (zeroPairs (sampleVec 3 sd.1 - sampleVec 3 sd'.1)).card ∧
      uComp A (sampleVec 3 sd.1 - sampleVec 3 sd'.1) ∈
        collWindowSet (noise1 sd) (noise1 sd') then 1 else 0

/-- The collision indicator of two seeds at a key is at most the sum of the two event
indicators at the matrix of the key. -/
theorem collision_le_indicators (pk : Mat × Vec) (m : Msg)
    (sd sd' : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2) :
    (if mlkem512CompressedScheme.enc pk m sd = mlkem512CompressedScheme.enc pk m sd' then
        (1 : ℝ≥0∞) else 0) ≤
      manyZeros sd sd' + windowHit pk.1 sd sd' := by
  by_cases h : mlkem512CompressedScheme.enc pk m sd = mlkem512CompressedScheme.enc pk m sd'
  · rw [if_pos h]
    by_cases h40 : 40 ≤ (zeroPairs (sampleVec 3 sd.1 - sampleVec 3 sd'.1)).card
    · have hz : manyZeros sd sd' = 1 := if_pos h40
      rw [hz]
      exact le_self_add
    · have hw : windowHit pk.1 sd sd' = 1 := by
        unfold windowHit
        split_ifs with hc
        · rfl
        · exfalso
          apply hc
          refine ⟨h40, ?_⟩
          unfold noise1
          rw [enc_unfold, enc_unfold] at h
          have hu := congrArg (fun c : MLKEM512CT => c.1 0) h
          simp only [mlkem512Compress, CompressedPKE.compressCT, vecAdd] at hu
          rw [collWindowSet, Fintype.mem_piFinset]
          intro i
          have hi : Compress.compress_d 10
              (matVecMul (matTranspose pk.1) (sampleVec 3 sd.1) 0 i + sampleVec 2 sd.2.1 0 i) =
              Compress.compress_d 10
                (matVecMul (matTranspose pk.1) (sampleVec 3 sd'.1) 0 i +
                  sampleVec 2 sd'.2.1 0 i) :=
            congrFun hu i
          rw [compress10CollWindow, mem_filter]
          refine ⟨mem_univ _, matVecMul (matTranspose pk.1) (sampleVec 3 sd'.1) 0 i, ?_⟩
          rw [uComp_sub]
          simp only [uComp, Pi.sub_apply]
          have hre : ∀ x y z : ZMod q_kem, x + (y - x) + z = y + z := fun x y z => by ring
          rw [hre]
          exact hi.symm
      have hz : manyZeros sd sd' = 0 := if_neg h40
      rw [hw, hz, zero_add]
  · rw [if_neg h]
    exact zero_le

end CatCrypt.Crypto.MLKEM.CollisionSpread

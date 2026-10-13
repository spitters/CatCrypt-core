/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.Compress
public import CatCryptCore.Crypto.MLKEM.Libcrux.RqAlgebra
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Tactic.NormNum.Prime

/-!
# Coefficient maps for the ML-KEM ring `Rq_kem`

The ring `Rq_kem = (ZMod 3329)[X]/(X^256 + 1)` of FIPS 203 §2.4, the maps between it
and the coefficient representation `Fin 256 → ZMod 3329`, the `Array Int` marshalling
used by the extracted ML-KEM code, and the degree-one pair layout `Tq_kem` of the
NTT domain.

The ring is `Libcrux.RqAlgebra.Rq`, the carrier of the IND-CCA development; `q_kem`,
`mlkem_poly`, `mlkem_poly_monic` and `Rq_kem` are that module's names re-exported here,
so that every ML-KEM statement is over one ring.

`q = 3329 = 13 · 2^8 + 1` carries a primitive 256-th root of unity but no primitive
512-th root, so the ML-KEM transform is incomplete: it splits `X^256 + 1` into 128
quadratic factors `X^2 - ζ^(2·BitRev7 j + 1)` rather than 256 linear ones. An element
of the NTT domain is therefore 128 pairs of coefficients, which is what `Tq_kem`
records. The transform itself and the degree-one products in each factor are stated
elsewhere; this module fixes only the layout and its bijection with the coefficient
representation.

Compression and decompression are the functions `Compress.compress_d` and
`Compress.decompress_d` of `CatCrypt.Crypto.MLKEM.Compress`. This module lifts them
to coefficient vectors and relates the round trip to the FIPS 203 §4.2.1 bound in
`ZMod 3329`, where the reduction modulo `2^d` in `compress_d` can wrap.

## Main definitions

* `q_kem`, `mlkem_poly`, `Rq_kem` — the modulus, `X^256 + 1`, and the quotient ring
* `coeffsToRqKem` / `rqKemToCoeffs` — the coefficient maps
* `arrayIntToRqKem` / `rqKemToArrayInt` — `Array Int` marshalling
* `Tq_kem`, `pairsOfCoeffs`, `coeffsOfPairs`, `coeffsEquivPairs` — the pair layout
* `compressCoeffs` / `decompressCoeffs` — FIPS 203 §4.2.1 applied coefficientwise
* `centeredAbs` — the distance of an element of `ZMod q_kem` from zero on the circle,
  the definition of `Compress.centeredAbs` named in this namespace

## Main results

* `rqKem_roundtrip` / `coeffs_roundtrip` — the two coefficient round trips
* `coeffsToRqKem_add` / `coeffsToRqKem_sub` / `coeffsToRqKem_const_mul` — linearity
* `pairs_roundtrip` / `coeffsOfPairs_roundtrip` — the pair layout is a bijection
* `compress_decompress_centered` — for `1 ≤ d ≤ 12`, decompression after compression
  moves a coefficient by at most `Compress.errorBound d` on the circle `ZMod q_kem`
  (the statement `Compress.decompress_compress_centered`)
* `compressCoeff_decompressCoeff` — for `d < 12`, compression after decompression is
  the identity (the statement `Compress.compress_decompress`)
* `compressCoeffs_decompressCoeffs_centered` — the coefficientwise form
* `errorBound_du`, `errorBound_dv` — the bound at the ML-KEM parameters `d = 10, 4`

## References

* NIST FIPS 203 (2024), §2.4, §4.2.1, §4.3
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.Spec.Coeffs

open Polynomial AdjoinRoot
open CatCrypt.Crypto.MLKEM

/-! ## The ML-KEM ring -/

/-- The ML-KEM modulus `q = 3329`, the modulus of `Libcrux.RqAlgebra`. -/
abbrev q_kem : ℕ := Libcrux.RqAlgebra.q

/-- `q_kem` agrees with the modulus of `CatCrypt.Crypto.MLKEM.Compress`. -/
theorem q_kem_eq_compress_q : q_kem = Compress.q := rfl

/-- `3329` is prime. -/
theorem q_kem_prime : Nat.Prime q_kem := Fact.out

/-- The polynomial `X^256 + 1` over `ZMod q_kem`: `Libcrux.RqAlgebra.mlkem_poly`. -/
noncomputable abbrev mlkem_poly : (ZMod q_kem)[X] := Libcrux.RqAlgebra.mlkem_poly

/-- `mlkem_poly` is monic. -/
lemma mlkem_poly_monic : mlkem_poly.Monic := Libcrux.RqAlgebra.mlkem_poly_monic

/-- `X^256 + 1` has natural degree `256`. -/
lemma mlkem_poly_natDegree : mlkem_poly.natDegree = 256 := by
  unfold mlkem_poly Libcrux.RqAlgebra.mlkem_poly
  rw [← Polynomial.C_1]
  exact Polynomial.natDegree_X_pow_add_C

/-- `X^256 + 1` has degree `256`. -/
lemma mlkem_poly_degree : mlkem_poly.degree = (256 : ℕ) :=
  (Polynomial.degree_eq_natDegree mlkem_poly_monic.ne_zero).trans
    (congrArg _ mlkem_poly_natDegree)

/-- `Rq_kem = (ZMod 3329)[X]/(X^256 + 1)`: the ML-KEM polynomial ring,
`Libcrux.RqAlgebra.Rq`. Its algebraic instances are that module's. -/
noncomputable abbrev Rq_kem := Libcrux.RqAlgebra.Rq

/-- A `k`-dimensional vector over `Rq_kem`. -/
abbrev KemVec (k : ℕ) := Fin k → Rq_kem

/-- A `k × k` matrix over `Rq_kem`. -/
abbrev KemMat (k : ℕ) := Fin k → Fin k → Rq_kem

/-! ## Coefficient maps -/

/-- The `i`-th coefficient of an element of `Rq_kem`: the `i`-th coefficient of its
unique representative of degree `< 256`. -/
noncomputable def rqKemToCoeffs (a : Rq_kem) : Fin 256 → ZMod q_kem :=
  fun i => (modByMonicHom mlkem_poly_monic a).coeff i.val

/-- The element of `Rq_kem` with coefficients `cs`. -/
noncomputable def coeffsToRqKem (cs : Fin 256 → ZMod q_kem) : Rq_kem :=
  mk mlkem_poly (∑ i : Fin 256, Polynomial.monomial i.val (cs i))

/-- A sum of monomials of index `< 256` has degree `< 256`. -/
lemma degree_coeffs_poly_lt (cs : Fin 256 → ZMod q_kem) :
    (∑ j : Fin 256, Polynomial.monomial j.val (cs j)).degree < (256 : ℕ) := by
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro j _
  exact (Polynomial.degree_monomial_le j.val (cs j)).trans_lt
    (WithBot.coe_lt_coe.mpr j.isLt)

/-- Building a ring element from coefficients and reading them back is the identity. -/
theorem rqKem_roundtrip (cs : Fin 256 → ZMod q_kem) :
    rqKemToCoeffs (coeffsToRqKem cs) = cs := by
  ext ⟨i, hi⟩
  simp only [rqKemToCoeffs, coeffsToRqKem, modByMonicHom_mk]
  have hlt : (∑ j : Fin 256, Polynomial.monomial j.val (cs j)).degree
      < mlkem_poly.degree := by
    rw [mlkem_poly_degree]; exact degree_coeffs_poly_lt cs
  rw [(modByMonic_eq_self_iff mlkem_poly_monic).mpr hlt, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp
  · intro j _ hj; rw [if_neg (Fin.val_ne_of_ne hj)]
  · exact absurd (Finset.mem_univ _)

/-- Reading the coefficients of a ring element and rebuilding it is the identity. -/
theorem coeffs_roundtrip (a : Rq_kem) : coeffsToRqKem (rqKemToCoeffs a) = a := by
  induction a using AdjoinRoot.induction_on with
  | _ p =>
    simp only [coeffsToRqKem, rqKemToCoeffs, modByMonicHom_mk]
    have h := sum_modByMonic_coeff mlkem_poly_monic (p := p)
      (n := 256) (le_of_eq mlkem_poly_degree)
    rw [h]
    exact mk_leftInverse mlkem_poly_monic (mk mlkem_poly p)

/-- `coeffsToRqKem` is injective, by the round trip. -/
theorem coeffsToRqKem_injective : Function.Injective coeffsToRqKem := by
  intro a b h
  rw [← rqKem_roundtrip a, ← rqKem_roundtrip b, h]

/-! ## Linearity -/

/-- `coeffsToRqKem` carries pointwise addition to ring addition. -/
theorem coeffsToRqKem_add (f g : Fin 256 → ZMod q_kem) :
    coeffsToRqKem (f + g) = coeffsToRqKem f + coeffsToRqKem g := by
  unfold coeffsToRqKem; simp only [Pi.add_apply]
  simp_rw [map_add (Polynomial.monomial _)]
  rw [Finset.sum_add_distrib, map_add]

/-- `coeffsToRqKem` carries pointwise subtraction to ring subtraction. -/
theorem coeffsToRqKem_sub (f g : Fin 256 → ZMod q_kem) :
    coeffsToRqKem (f - g) = coeffsToRqKem f - coeffsToRqKem g := by
  unfold coeffsToRqKem; simp only [Pi.sub_apply]
  simp_rw [map_sub (Polynomial.monomial _)]
  rw [Finset.sum_sub_distrib, map_sub]

/-- `coeffsToRqKem` carries pointwise scaling by a constant to multiplication by the
image of that constant in `Rq_kem`. -/
theorem coeffsToRqKem_const_mul (c : ZMod q_kem) (f : Fin 256 → ZMod q_kem) :
    coeffsToRqKem (fun i => c * f i) = of mlkem_poly c * coeffsToRqKem f := by
  unfold coeffsToRqKem
  rw [AdjoinRoot.of, RingHom.comp_apply, ← map_mul, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
  rw [Polynomial.C_mul_monomial]

/-- `rqKemToCoeffs` carries ring addition to pointwise addition. -/
theorem rqKemToCoeffs_add (a b : Rq_kem) :
    rqKemToCoeffs (a + b) = rqKemToCoeffs a + rqKemToCoeffs b := by
  funext i
  simp [rqKemToCoeffs, map_add]

/-- `rqKemToCoeffs` carries ring subtraction to pointwise subtraction. -/
theorem rqKemToCoeffs_sub (a b : Rq_kem) :
    rqKemToCoeffs (a - b) = rqKemToCoeffs a - rqKemToCoeffs b := by
  funext i
  simp [rqKemToCoeffs, map_sub]

/-- The element of `Rq_kem` with all coefficients zero is `0`. -/
theorem coeffsToRqKem_zero : coeffsToRqKem 0 = 0 := by
  simp [coeffsToRqKem]

/-! ## `Array Int` marshalling

The extracted ML-KEM code represents a polynomial as an `Array Int` of length 256. -/

/-- The coefficient function of an `Array Int`, each entry reduced modulo `q_kem`. -/
def arrayIntToCoeffs (arr : Array Int) : Fin 256 → ZMod q_kem :=
  fun i => Int.cast (arr.getD i.val 0)

/-- The `Array Int` of the canonical representatives of a coefficient function. -/
def coeffsToArrayInt (cs : Fin 256 → ZMod q_kem) : Array Int :=
  Array.ofFn (fun i : Fin 256 => ((cs i).val : Int))

/-- The element of `Rq_kem` an `Array Int` represents. -/
noncomputable def arrayIntToRqKem (arr : Array Int) : Rq_kem :=
  coeffsToRqKem (arrayIntToCoeffs arr)

/-- The `Array Int` representing an element of `Rq_kem`. -/
noncomputable def rqKemToArrayInt (a : Rq_kem) : Array Int :=
  coeffsToArrayInt (rqKemToCoeffs a)

/-- `arrayIntToCoeffs` is a left inverse of `coeffsToArrayInt`. -/
theorem arrayIntToCoeffs_coeffsToArrayInt (cs : Fin 256 → ZMod q_kem) :
    arrayIntToCoeffs (coeffsToArrayInt cs) = cs := by
  funext i
  simp only [arrayIntToCoeffs, coeffsToArrayInt, Array.getD, Array.size_ofFn, i.isLt]
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- `arrayIntToRqKem` inverts `rqKemToArrayInt`. -/
theorem arrayIntToRqKem_rqKemToArrayInt (a : Rq_kem) :
    arrayIntToRqKem (rqKemToArrayInt a) = a := by
  simp only [arrayIntToRqKem, rqKemToArrayInt, arrayIntToCoeffs_coeffsToArrayInt,
    coeffs_roundtrip]

/-- The `k`-vector over `Rq_kem` an `Array (Array Int)` represents. -/
noncomputable def arrayIntToKemVec (k : ℕ) (arr : Array (Array Int)) : KemVec k :=
  fun i => arrayIntToRqKem (arr.getD i.val #[])

/-- The `Array (Array Int)` representing a `k`-vector over `Rq_kem`. -/
noncomputable def kemVecToArrayInt (k : ℕ) (v : KemVec k) : Array (Array Int) :=
  Array.ofFn (fun i : Fin k => rqKemToArrayInt (v i))

/-! ## The degree-one pair layout of the NTT domain

`q_kem - 1 = 13 · 2^8`, so `ZMod q_kem` has a primitive 256-th root of unity and no
primitive 512-th root. `X^256 + 1` therefore factors over `ZMod q_kem` into 128
quadratics rather than 256 linear factors, and an element of the NTT domain is a
family of 128 degree-one residues. `Tq_kem` records such a family as 128 coefficient
pairs, pair `j` holding the residue `t_{2j} + t_{2j+1} X` of the `j`-th factor. -/

/-- The NTT domain of ML-KEM: 128 pairs of coefficients in `ZMod q_kem`. -/
abbrev Tq_kem : Type := Fin 128 → ZMod q_kem × ZMod q_kem

/-- The index of the constant coefficient of pair `j`. -/
def pairFst (j : Fin 128) : Fin 256 := ⟨2 * j.val, by have := j.isLt; omega⟩

/-- The index of the linear coefficient of pair `j`. -/
def pairSnd (j : Fin 128) : Fin 256 := ⟨2 * j.val + 1, by have := j.isLt; omega⟩

/-- The pair containing index `i`. -/
def pairIndex (i : Fin 256) : Fin 128 := ⟨i.val / 2, by have := i.isLt; omega⟩

/-- The 128 coefficient pairs of a 256-coefficient family. -/
def pairsOfCoeffs (f : Fin 256 → ZMod q_kem) : Tq_kem :=
  fun j => (f (pairFst j), f (pairSnd j))

/-- The 256 coefficients of a family of 128 pairs. -/
def coeffsOfPairs (t : Tq_kem) : Fin 256 → ZMod q_kem :=
  fun i => if i.val % 2 = 0 then (t (pairIndex i)).1 else (t (pairIndex i)).2

/-- Splitting coefficients into pairs and concatenating them back is the identity. -/
theorem coeffsOfPairs_roundtrip (f : Fin 256 → ZMod q_kem) :
    coeffsOfPairs (pairsOfCoeffs f) = f := by
  funext i
  have hi := i.isLt
  by_cases h : i.val % 2 = 0
  · have : pairFst (pairIndex i) = i := by
      apply Fin.ext
      simp only [pairFst, pairIndex]
      omega
    simp [coeffsOfPairs, pairsOfCoeffs, h, this]
  · have : pairSnd (pairIndex i) = i := by
      apply Fin.ext
      simp only [pairSnd, pairIndex]
      omega
    simp [coeffsOfPairs, pairsOfCoeffs, h, this]

/-- Concatenating pairs into coefficients and splitting them back is the identity. -/
theorem pairs_roundtrip (t : Tq_kem) : pairsOfCoeffs (coeffsOfPairs t) = t := by
  funext j
  have hj := j.isLt
  have h0 : pairIndex (pairFst j) = j := by
    apply Fin.ext; simp only [pairIndex, pairFst]; omega
  have h1 : pairIndex (pairSnd j) = j := by
    apply Fin.ext; simp only [pairIndex, pairSnd]; omega
  have e0 : (pairFst j).val % 2 = 0 := by simp only [pairFst]; omega
  have e1 : ¬ ((pairSnd j).val % 2 = 0) := by simp only [pairSnd]; omega
  simp only [pairsOfCoeffs, coeffsOfPairs, h0, h1, e0, e1, if_true, if_false]

/-- `pairsOfCoeffs` is a bijection between the coefficient and NTT layouts. -/
noncomputable def coeffsEquivPairs : (Fin 256 → ZMod q_kem) ≃ Tq_kem where
  toFun := pairsOfCoeffs
  invFun := coeffsOfPairs
  left_inv := coeffsOfPairs_roundtrip
  right_inv := pairs_roundtrip

/-! ## Compression on the circle `ZMod q_kem`

The distance `centeredAbs` on the circle `ZMod q_kem` and the round-trip bound
`Compress.decompress_compress_centered` are those of `CatCrypt.Crypto.MLKEM.Compress`;
`centeredAbs`, `centeredAbs_sub_le` and `centeredAbs_zero_sub_le` are exported into this
namespace. -/

export CatCrypt.Crypto.MLKEM.Compress (centeredAbs centeredAbs_sub_le centeredAbs_zero_sub_le)

/-- FIPS 203 §4.2.1 `Compress_d` at the ML-KEM modulus. -/
def compressCoeff (d : ℕ) (x : ZMod q_kem) : ZMod (2 ^ d) := Compress.compress_d d x

/-- FIPS 203 §4.2.1 `Decompress_d` at the ML-KEM modulus. -/
def decompressCoeff (d : ℕ) (y : ZMod (2 ^ d)) : ZMod q_kem := Compress.decompress_d d y

/-- `Compress_d` applied to each of the 256 coefficients of a polynomial. -/
def compressCoeffs (d : ℕ) (f : Fin 256 → ZMod q_kem) : Fin 256 → ZMod (2 ^ d) :=
  fun i => compressCoeff d (f i)

/-- `Decompress_d` applied to each of the 256 coefficients of a polynomial. -/
def decompressCoeffs (d : ℕ) (g : Fin 256 → ZMod (2 ^ d)) : Fin 256 → ZMod q_kem :=
  fun i => decompressCoeff d (g i)

/-- FIPS 203 §4.2.1 round-trip bound in `ZMod q_kem`, the statement
`Compress.decompress_compress_centered` for `compressCoeff` and `decompressCoeff`.

Decompressing the compression of `x` moves `x` by at most `Compress.errorBound d`,
measured on the circle `ZMod q_kem`. The reduction modulo `2 ^ d` inside
`Compress.compress_d` is included: when it wraps, `x` lies within
`Compress.errorBound d` of `q_kem` and the decompressed value is `0`.

## Scope

`1 ≤ d ≤ 12`. The upper bound gives `2 ^ d / 2 < q_kem`, which is what makes the
decompressed natural number already reduced modulo `q_kem`. It holds for every
FIPS 203 compression parameter: `d_u ∈ {10, 11}`, `d_v ∈ {4, 5}`, `d = 1` for the
message encoding and `d = 12` for the 12-bit byte encoding. -/
theorem compress_decompress_centered (d : ℕ) (hd : 1 ≤ d) (hd12 : d ≤ 12)
    (x : ZMod q_kem) :
    centeredAbs (decompressCoeff d (compressCoeff d x) - x) ≤ Compress.errorBound d :=
  Compress.decompress_compress_centered d hd hd12 x

/-- FIPS 203 §4.2.1: `compressCoeff d (decompressCoeff d y) = y` for `d < 12`, the
statement `Compress.compress_decompress` for `compressCoeff` and `decompressCoeff`. -/
theorem compressCoeff_decompressCoeff (d : ℕ) (hd : d < 12) (y : ZMod (2 ^ d)) :
    compressCoeff d (decompressCoeff d y) = y :=
  Compress.compress_decompress d hd y

/-- The coefficientwise form of `compress_decompress_centered`. -/
theorem compressCoeffs_decompressCoeffs_centered (d : ℕ) (hd : 1 ≤ d) (hd12 : d ≤ 12)
    (f : Fin 256 → ZMod q_kem) (i : Fin 256) :
    centeredAbs (decompressCoeffs d (compressCoeffs d f) i - f i)
      ≤ Compress.errorBound d :=
  compress_decompress_centered d hd hd12 (f i)

/-- The round-trip bound at `d_u = 10`, the ML-KEM-512/768 ciphertext parameter.
A static check pinning the bound of `Compress.errorBound` at a FIPS 203 parameter. -/
theorem errorBound_du : Compress.errorBound 10 = 2 := by norm_num [Compress.errorBound]

/-- The round-trip bound at `d_v = 4`, the ML-KEM-512/768 ciphertext parameter.
A static check pinning the bound of `Compress.errorBound` at a FIPS 203 parameter. -/
theorem errorBound_dv : Compress.errorBound 4 = 104 := by norm_num [Compress.errorBound]

end CatCrypt.Crypto.MLKEM.Spec.Coeffs

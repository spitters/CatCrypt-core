/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import CatCryptCore.Crypto.MLKEM.Spec.Coeffs
public import CatCryptCore.Crypto.Lattice.BitReversalGeneric
public import CatCryptCore.Crypto.Lattice.ConcreteNttRoots
public import CatCryptCore.Crypto.Lattice.DFTBijectionGeneric
public import CatCryptCore.Crypto.Lattice.NegacyclicTransformGeneric
public import CatCryptCore.Crypto.Lattice.SignedNegacyclicConv
public import CatCryptCore.Crypto.Lattice.Negacyclic

/-!
# The ML-KEM number-theoretic transform

The FIPS 203 §4.3 transform of `Rq_kem = (ZMod 3329)[X]/(X^256 + 1)` into the 128
degree-one residues of `Tq_kem`, its `BitRev7` output ordering, the quadratic moduli
`X^2 - ζ^(2·BitRev7 j + 1)`, and the base multiplication in each of them.

The transform is the length-128 twisted transform
`NegacyclicTransformGeneric.ndft` at twist root `ζ = 17`, applied separately to the
even- and odd-indexed coefficient subsequences. `ζ` has order 256 in `ZMod 3329`, so
`ζ^2` is a primitive 128-th root and the generic negacyclic development applies at
length 128 — the length at which `X^256 + 1 = (Y^128 + 1)|_{Y = X^2}` splits
completely; see `## The length of the transform`.

Writing `a = a_e(X^2) + X · a_o(X^2)` with `a_e`, `a_o` of degree `< 128`, the product
in `Rq_kem` has halves

  `(a·b)_e = a_e ⋆ b_e + Y · (a_o ⋆ b_o)`,  `(a·b)_o = a_e ⋆ b_o + a_o ⋆ b_e`,

with `⋆` the length-128 negacyclic convolution and `Y ·` the negacyclic shift
`negaShift`. `negaMulKem` is that pair of formulas, read back through the coefficient
interleaving, and `nttKem_negaMulKem` transforms it into `basemulKem`.

## Main definitions

* `zetaKem` — the ML-KEM root `ζ = 17`
* `bitRev7`, `gammaKem` — the output ordering and the quadratic modulus root
  `ζ^(2·BitRev7 j + 1)` of pair `j`
* `evens`, `odds`, `interleave` — the even/odd coefficient split of `Fin 256`
* `nttHalf`, `nttKem` — the length-128 twisted transform and the ML-KEM transform
  into `Tq_kem`
* `invNttHalf`, `invNttKem` — the inverse of the length-128 twisted transform and the
  ML-KEM inverse transform (FIPS 203 Algorithm 10)
* `negaShift` — multiplication by `Y` in `(ZMod 3329)[Y]/(Y^128 + 1)`
* `negaMulKem` — the product of `Rq_kem` in the even/odd decomposition
* `polyMulKem` — the length-256 signed negacyclic product of coefficient vectors
* `basemulPair`, `basemulKem` — base multiplication on a pair and on `Tq_kem`

## Main results

* `zetaKem_sq_isPrimitiveRoot` — `ζ^2` is a primitive 128-th root, which is what
  the generic negacyclic development needs at length 128
* `nttHalf_negaConv` — the transform diagonalizes the length-128 negacyclic
  convolution, an instance of `NegacyclicTransformGeneric.ndft_negaConv`
* `negaConvKem_eq_signed` — that convolution is the signed convolution of
  `(ZMod 3329)[Y]/(Y^128 + 1)`
* `nttHalf_negaShift` — the transform carries `negaShift` to multiplication by the
  pair's modulus root `ζ^(2k+1)`
* `basemulPair_modByMonic` — `basemulPair γ` is the product of two degree-one
  residues modulo `X^2 - γ`
* `nttKem_negaMulKem` — `nttKem (negaMulKem a b) = basemulKem (nttKem a) (nttKem b)`
* `coeffsToRqKem_polyMulKem` — `polyMulKem` is multiplication in `Rq_kem`
* `sum_fin256_pairs` — a sum over `Fin 256` as a sum over the 128 index pairs
* `negaShift_signedNegaConv` — the negacyclic shift of a signed convolution, termwise
* `evens_polyMulKem`, `odds_polyMulKem` — the two halves of the length-256 signed
  product
* `negaMulKem_eq_polyMulKem` — the even/odd decomposition is the length-256 signed
  product
* `nttKem_rqKemToCoeffs_mul` — the transform carries multiplication in `Rq_kem` to
  `basemulKem`
* `invNttKem_nttKem`, `nttKem_invNttKem` — the inverse transform and the transform
  are mutually inverse: `invNttKem (nttKem a) = a` and `nttKem (invNttKem t) = t`
* `inv_cast_128`, `invNttHalf_apply` — the scaling of the inverse transform is
  `128⁻¹ = 3303`
* `polyMulKem_eq_invNttKem`, `rqKem_mul_eq_invNttKem` — the product of `Rq_kem` is the
  inverse transform of the base multiplication of the transforms

## The length of the transform

The generic negacyclic transform is instantiated at length 128. Its hypothesis
`IsPrimitiveRoot (ψ^2) n` at `n = 256` forces `ψ` to have order 512, and
`512 ∤ 3329 - 1 = 13 · 2^8`, so `ZMod 3329` has no such root. The product of
`Rq_kem` is therefore carried to `basemulKem`, the base multiplication in the 128
quadratic moduli (`nttKem_rqKemToCoeffs_mul`).

`bitRev7` enters only through `gammaKem` and the output index of `nttKem`.

## References

* NIST FIPS 203 (2024), §2.4.5, §4.3
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.Spec.Ntt

open Finset
open CatCrypt.Crypto.MLKEM.Spec.Coeffs
open CatCrypt.Crypto.Lattice.ConcreteNttRoots
open CatCrypt.Crypto.Lattice.NegacyclicTransformGeneric
open CatCrypt.Crypto.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Lattice.NTTFullInversionGeneric (idft idft_dft)
open CatCrypt.Crypto.Lattice.DFTBijectionGeneric (dft_idft)

/-! ## The root of unity -/

/-- The ML-KEM transform root `ζ = 17`, of order 256 in `ZMod 3329`. -/
def zetaKem : ZMod q_kem := 17

/-- `ζ` is a primitive 256-th root of unity. -/
theorem zetaKem_isPrimitiveRoot : IsPrimitiveRoot zetaKem 256 :=
  isPrimitiveRoot_17_256

/-- `ζ` is a primitive `2 · 128`-th root of unity, the twist-root hypothesis of the
length-128 negacyclic development. -/
theorem zetaKem_isPrimitiveRoot_two_mul : IsPrimitiveRoot zetaKem (2 * 128) :=
  zetaKem_isPrimitiveRoot

/-- `ζ^2` is a primitive 128-th root of unity. -/
theorem zetaKem_sq_isPrimitiveRoot : IsPrimitiveRoot (zetaKem ^ 2) 128 :=
  zetaKem_isPrimitiveRoot.pow (by norm_num) (by norm_num)

/-- `ζ` is nonzero. -/
theorem zetaKem_ne_zero : zetaKem ≠ 0 := by
  intro h
  have := zetaKem_isPrimitiveRoot.pow_eq_one
  rw [h, zero_pow (by norm_num)] at this
  exact zero_ne_one this

/-- `ζ^128 = -1`: the sign the negacyclic wraparound contributes. -/
theorem zetaKem_pow_128 : zetaKem ^ 128 = -1 :=
  CatCrypt.Crypto.Lattice.SignedNegacyclicConv.psi_pow_n
    (n := 128) zetaKem_isPrimitiveRoot_two_mul

/-! ## Output ordering and the quadratic moduli -/

/-- The 7-bit reversal `BitRev7` of FIPS 203 §4.3, the output ordering of the
transform. -/
def bitRev7 (i : Fin 128) : Fin 128 :=
  CatCrypt.Crypto.Lattice.BitReversalGeneric.bitrevFin 7 i

/-- `BitRev7` is an involution. -/
theorem bitRev7_bitRev7 (i : Fin 128) : bitRev7 (bitRev7 i) = i :=
  CatCrypt.Crypto.Lattice.BitReversalGeneric.bitrevFin_involutive 7 i

/-- The root `ζ^(2·BitRev7 j + 1)` of the quadratic modulus `X^2 - γ_j` of pair `j`. -/
def gammaKem (j : Fin 128) : ZMod q_kem := zetaKem ^ (2 * (bitRev7 j).val + 1)

/-! ## The even/odd coefficient split -/

/-- The even-indexed coefficients of a 256-coefficient family. -/
def evens (a : Fin 256 → ZMod q_kem) : Fin 128 → ZMod q_kem := fun j => a (pairFst j)

/-- The odd-indexed coefficients of a 256-coefficient family. -/
def odds (a : Fin 256 → ZMod q_kem) : Fin 128 → ZMod q_kem := fun j => a (pairSnd j)

/-- The 256-coefficient family with the given even- and odd-indexed halves. -/
def interleave (e o : Fin 128 → ZMod q_kem) : Fin 256 → ZMod q_kem :=
  coeffsOfPairs (fun j => (e j, o j))

/-- The even half of an interleaving is the half it was built from. -/
@[simp] theorem evens_interleave (e o : Fin 128 → ZMod q_kem) : evens (interleave e o) = e := by
  funext j
  exact congrArg Prod.fst (congrFun (pairs_roundtrip (fun j => (e j, o j))) j)

/-- The odd half of an interleaving is the half it was built from. -/
@[simp] theorem odds_interleave (e o : Fin 128 → ZMod q_kem) : odds (interleave e o) = o := by
  funext j
  exact congrArg Prod.snd (congrFun (pairs_roundtrip (fun j => (e j, o j))) j)

/-- Splitting a coefficient family into halves and interleaving them back is the
identity. -/
theorem interleave_evens_odds (a : Fin 256 → ZMod q_kem) :
    interleave (evens a) (odds a) = a :=
  coeffsOfPairs_roundtrip a

/-! ## The transform -/

/-- The length-128 twisted transform at twist root `ζ`:
`nttHalf x k = Σ_j x_j · ζ^(j(2k+1))`. -/
def nttHalf (x : Fin 128 → ZMod q_kem) : Fin 128 → ZMod q_kem := ndft zetaKem x

/-- The closed form of `nttHalf`: the twist and the `ζ^2` twiddle combine into the odd
exponent `j(2k+1)`. -/
theorem nttHalf_apply (x : Fin 128 → ZMod q_kem) (k : Fin 128) :
    nttHalf x k = ∑ j : Fin 128, x j * zetaKem ^ (j.val * (2 * k.val + 1)) := by
  simp only [nttHalf, ndft, dft, twist]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_assoc, ← pow_mul, ← pow_add]
  congr 1
  ring

/-- `nttHalf` is additive. -/
theorem nttHalf_add (x y : Fin 128 → ZMod q_kem) (k : Fin 128) :
    nttHalf (x + y) k = nttHalf x k + nttHalf y k := by
  simp only [nttHalf_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **The ML-KEM forward transform.** Pair `j` of the NTT domain holds the length-128
transforms of the even and odd coefficient halves, read at the bit-reversed index
`BitRev7 j` (FIPS 203 §4.3). -/
def nttKem (a : Fin 256 → ZMod q_kem) : Tq_kem :=
  fun j => (nttHalf (evens a) (bitRev7 j), nttHalf (odds a) (bitRev7 j))

/-! ## The inverse transform -/

/-- `128` is invertible in `ZMod 3329`. -/
theorem cast_128_ne_zero : ((128 : ℕ) : ZMod q_kem) ≠ 0 := by decide

/-- `128⁻¹ = 3303` in `ZMod 3329`, the scaling factor of the inverse transform
(FIPS 203 Algorithm 10). -/
theorem inv_cast_128 : ((128 : ℕ) : ZMod q_kem)⁻¹ = 3303 :=
  inv_eq_of_mul_eq_one_left (by decide)

/-- The inverse of the length-128 twisted transform: synthesis by `idft` at `ζ^2`,
which carries the scaling by `128⁻¹`, followed by the untwist by `ζ`. -/
def invNttHalf (v : Fin 128 → ZMod q_kem) : Fin 128 → ZMod q_kem :=
  untwist zetaKem (idft 128 (zetaKem ^ 2) v)

/-- The closed form of `invNttHalf`, with the scaling `128⁻¹ = 3303`:
`invNttHalf v j = 3303 · (Σ_k v_k · ζ^(-2jk)) · ζ^(-j)`. -/
theorem invNttHalf_apply (v : Fin 128 → ZMod q_kem) (j : Fin 128) :
    invNttHalf v j
      = 3303 * (∑ k : Fin 128, v k * ((zetaKem ^ 2)⁻¹) ^ (k.val * j.val))
        * (zetaKem⁻¹) ^ j.val := by
  simp only [invNttHalf, untwist, idft, inv_cast_128]

/-- `invNttHalf` is a left inverse of `nttHalf`. -/
theorem invNttHalf_nttHalf (x : Fin 128 → ZMod q_kem) : invNttHalf (nttHalf x) = x := by
  have h : nttHalf x = dft 128 (zetaKem ^ 2) (twist zetaKem x) := rfl
  rw [invNttHalf, h, idft_dft zetaKem_sq_isPrimitiveRoot cast_128_ne_zero,
    untwist_twist zetaKem_ne_zero]

/-- `invNttHalf` is a right inverse of `nttHalf`. -/
theorem nttHalf_invNttHalf (v : Fin 128 → ZMod q_kem) : nttHalf (invNttHalf v) = v := by
  have h : nttHalf (invNttHalf v)
      = dft 128 (zetaKem ^ 2) (twist zetaKem (invNttHalf v)) := rfl
  rw [h, invNttHalf, twist_untwist zetaKem_ne_zero,
    dft_idft zetaKem_sq_isPrimitiveRoot cast_128_ne_zero]

/-- **The ML-KEM inverse transform** (FIPS 203 Algorithm 10). The first and second
components of the 128 pairs, read at the bit-reversed index, are the length-128
transforms of the even and odd coefficient halves; each is inverted by `invNttHalf`,
which scales by `128⁻¹ = 3303`, and the two halves are interleaved. -/
def invNttKem (t : Tq_kem) : Fin 256 → ZMod q_kem :=
  interleave (invNttHalf (fun k => (t (bitRev7 k)).1))
    (invNttHalf (fun k => (t (bitRev7 k)).2))

/-- **The inverse transform inverts the transform**: `invNttKem (nttKem a) = a` for
every coefficient vector `a`. -/
theorem invNttKem_nttKem (a : Fin 256 → ZMod q_kem) : invNttKem (nttKem a) = a := by
  have he : (fun k => (nttKem a (bitRev7 k)).1) = nttHalf (evens a) := by
    funext k
    simp only [nttKem, bitRev7_bitRev7]
  have ho : (fun k => (nttKem a (bitRev7 k)).2) = nttHalf (odds a) := by
    funext k
    simp only [nttKem, bitRev7_bitRev7]
  rw [invNttKem, he, ho, invNttHalf_nttHalf, invNttHalf_nttHalf, interleave_evens_odds]

/-- **The transform inverts the inverse transform**: `nttKem (invNttKem t) = t` for
every element `t` of the NTT domain. -/
theorem nttKem_invNttKem (t : Tq_kem) : nttKem (invNttKem t) = t := by
  funext j
  simp only [nttKem, invNttKem, evens_interleave, odds_interleave, nttHalf_invNttHalf,
    bitRev7_bitRev7]

/-! ## Base multiplication -/

/-- The product of two degree-one residues modulo `X^2 - γ`, in coefficient pairs:
`(a₀ + a₁X)(b₀ + b₁X) = (a₀b₀ + γ a₁b₁) + (a₀b₁ + a₁b₀) X`. -/
def basemulPair (γ : ZMod q_kem) (s t : ZMod q_kem × ZMod q_kem) :
    ZMod q_kem × ZMod q_kem :=
  (s.1 * t.1 + γ * (s.2 * t.2), s.1 * t.2 + s.2 * t.1)

/-- **FIPS 203 §4.3.1 `MultiplyNTTs`.** `basemulPair` in each of the 128 quadratic
components, at that component's modulus root `gammaKem j`. -/
def basemulKem (s t : Tq_kem) : Tq_kem := fun j => basemulPair (gammaKem j) (s j) (t j)

/-- `basemulPair γ` computes the product of two degree-one polynomials modulo
`X^2 - γ`. An instance of the generic `Negacyclic.basemul_mod`. -/
theorem basemulPair_modByMonic (γ : ZMod q_kem) (s t : ZMod q_kem × ZMod q_kem) :
    ((Polynomial.C s.1 + Polynomial.C s.2 * Polynomial.X)
        * (Polynomial.C t.1 + Polynomial.C t.2 * Polynomial.X))
      %ₘ CatCrypt.Crypto.Lattice.Negacyclic.quadPoly γ
      = Polynomial.C (basemulPair γ s t).1
        + Polynomial.C (basemulPair γ s t).2 * Polynomial.X :=
  CatCrypt.Crypto.Lattice.Negacyclic.basemul_mod γ s.1 s.2 t.1 t.2

/-! ## The negacyclic shift -/

/-- Multiplication by `Y` in `(ZMod 3329)[Y]/(Y^128 + 1)`: shift the coefficients up
by one and negate the coefficient that wraps. -/
def negaShift (x : Fin 128 → ZMod q_kem) : Fin 128 → ZMod q_kem :=
  fun j => if 0 < j.val then x ⟨j.val - 1, by have := j.isLt; omega⟩ else -x (Fin.last 127)

/-- The transform carries `negaShift` to multiplication by `ζ^(2k+1)`, the root of the
quadratic modulus of component `k`. -/
theorem nttHalf_negaShift (x : Fin 128 → ZMod q_kem) (k : Fin 128) :
    nttHalf (negaShift x) k = zetaKem ^ (2 * k.val + 1) * nttHalf x k := by
  set t : ZMod q_kem := zetaKem ^ (2 * k.val + 1) with ht
  have htpow : t ^ 128 = -1 := by
    rw [ht, ← pow_mul, mul_comm, pow_mul, zetaKem_pow_128, pow_succ, pow_mul]
    norm_num
  have hexp : ∀ (z : Fin 128 → ZMod q_kem),
      nttHalf z k = ∑ j : Fin 128, z j * t ^ j.val := by
    intro z
    rw [nttHalf_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ht, ← pow_mul, Nat.mul_comm (2 * k.val + 1) j.val]
  have hzero : negaShift x 0 = -x (Fin.last 127) := by simp [negaShift]
  have hsucc : ∀ i : Fin 127, negaShift x i.succ * t ^ (i.succ : Fin 128).val
      = t * (x i.castSucc * t ^ (i.castSucc : Fin 128).val) := by
    intro i
    have h1 : negaShift x i.succ = x i.castSucc := by
      simp only [negaShift, Fin.val_succ, Nat.succ_sub_one, ite_eq_left (Nat.succ_pos i.val)]
      rfl
    rw [h1, show ((i.succ : Fin 128)).val = ((i.castSucc : Fin 128)).val + 1 from rfl, pow_succ]
    ring
  rw [hexp (negaShift x), hexp x, Fin.sum_univ_succ (f := fun j : Fin 128 => negaShift x j * t ^ j.val),
    Fin.sum_univ_castSucc (f := fun j : Fin 128 => x j * t ^ j.val)]
  simp only [hzero, hsucc]
  rw [← Finset.mul_sum]
  have hfin : t * (x (Fin.last 127) * t ^ ((Fin.last 127 : Fin 128)).val)
      = -x (Fin.last 127) := by
    rw [show ((Fin.last 127 : Fin 128)).val = 127 from rfl,
      show t * (x (Fin.last 127) * t ^ 127) = x (Fin.last 127) * t ^ 128 by ring, htpow]
    ring
  rw [mul_add, hfin, show ((0 : Fin 128)).val = 0 from rfl, pow_zero, mul_one]
  ring

/-! ## The product of `Rq_kem` in the even/odd decomposition -/

/-- The length-128 negacyclic convolution at twist root `ζ`. -/
def negaConvKem (x y : Fin 128 → ZMod q_kem) : Fin 128 → ZMod q_kem :=
  negaConv zetaKem x y

/-- `negaConvKem` is the signed convolution `Σ_{u} ± x_u y_{k-u}`, with the sign `-1`
exactly on the terms whose index wraps. An instance of
`SignedNegacyclicConv.negaConv_eq_signed`. -/
theorem negaConvKem_eq_signed (x y : Fin 128 → ZMod q_kem) :
    negaConvKem x y
      = CatCrypt.Crypto.Lattice.SignedNegacyclicConv.signedNegaConv x y :=
  CatCrypt.Crypto.Lattice.SignedNegacyclicConv.negaConv_eq_signed
    zetaKem_isPrimitiveRoot_two_mul x y

/-- The transform diagonalizes the length-128 negacyclic convolution. An instance of
`NegacyclicTransformGeneric.ndft_negaConv` at `ζ^2`, which is a primitive 128-th
root. -/
theorem nttHalf_negaConv (x y : Fin 128 → ZMod q_kem) (k : Fin 128) :
    nttHalf (negaConvKem x y) k = nttHalf x k * nttHalf y k :=
  ndft_negaConv zetaKem_sq_isPrimitiveRoot zetaKem_ne_zero x y k

/-- **The product of `Rq_kem` in the even/odd decomposition.** With
`a = a_e(X^2) + X·a_o(X^2)` and `X^2 = Y`, the halves of `a · b` are
`a_e ⋆ b_e + Y·(a_o ⋆ b_o)` and `a_e ⋆ b_o + a_o ⋆ b_e`, with `⋆` the length-128
negacyclic convolution. -/
def negaMulKem (a b : Fin 256 → ZMod q_kem) : Fin 256 → ZMod q_kem :=
  interleave
    (negaConvKem (evens a) (evens b) + negaShift (negaConvKem (odds a) (odds b)))
    (negaConvKem (evens a) (odds b) + negaConvKem (odds a) (evens b))

/-- **The ML-KEM transform carries the product to base multiplication.** The
`γ a₁ b₁` term of `basemulPair` is the image of the negacyclic shift under
`nttHalf_negaShift`, at `γ = ζ^(2·BitRev7 j + 1) = gammaKem j`. -/
theorem nttKem_negaMulKem (a b : Fin 256 → ZMod q_kem) :
    nttKem (negaMulKem a b) = basemulKem (nttKem a) (nttKem b) := by
  funext j
  have hfst : (nttKem (negaMulKem a b) j).1 = (basemulKem (nttKem a) (nttKem b) j).1 := by
    simp only [nttKem, negaMulKem, basemulKem, basemulPair, evens_interleave]
    rw [nttHalf_add, nttHalf_negaConv, nttHalf_negaShift, nttHalf_negaConv, gammaKem]
  have hsnd : (nttKem (negaMulKem a b) j).2 = (basemulKem (nttKem a) (nttKem b) j).2 := by
    simp only [nttKem, negaMulKem, basemulKem, basemulPair, odds_interleave]
    rw [nttHalf_add, nttHalf_negaConv, nttHalf_negaConv]
  exact Prod.ext hfst hsnd

/-! ## The product in `Rq_kem` -/

/-- The length-256 negacyclic product of coefficient vectors: coefficient `k` of the
product is `∑_i ± a i * b (k - i)`, negative exactly on the wrapped indices. -/
def polyMulKem (a b : Fin 256 → ZMod q_kem) : Fin 256 → ZMod q_kem :=
  CatCrypt.Crypto.Lattice.SignedNegacyclicConv.signedNegaConv a b

/-- `X ^ 256 = -1` in `Rq_kem`. -/
lemma root_pow_256 : (AdjoinRoot.root mlkem_poly : Rq_kem) ^ 256 = -1 := by
  have h : (AdjoinRoot.mk mlkem_poly)
      (Polynomial.X ^ 256 + 1 : Polynomial (ZMod q_kem)) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  linear_combination h

/-- `coeffsToRqKem` as a sum of scaled powers of the root. -/
lemma coeffsToRqKem_eq_sum (cs : Fin 256 → ZMod q_kem) :
    coeffsToRqKem cs
      = ∑ i : Fin 256,
          AdjoinRoot.of mlkem_poly (cs i) * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ i.val := by
  unfold coeffsToRqKem
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X]
  rfl

/-- The wrap-around sign of the negacyclic product, at the level of root powers. -/
lemma root_pow_add (i j : Fin 256) :
    (AdjoinRoot.root mlkem_poly : Rq_kem) ^ (i.val + j.val)
      = (if i.val ≤ (j + i).val then (1 : Rq_kem) else -1)
        * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ ((j + i).val) := by
  have hi := i.isLt
  have hj := j.isLt
  have hval : (j + i).val = (i.val + j.val) % 256 := by
    simp [Fin.add_def, Nat.add_comm]
  rcases lt_or_ge (i.val + j.val) 256 with h | h
  · rw [hval, Nat.mod_eq_of_lt h, ite_eq_left (by omega)]
    ring
  · have hmod : (i.val + j.val) % 256 = i.val + j.val - 256 := by omega
    rw [hval, hmod, ite_eq_right (by omega)]
    have hsplit : i.val + j.val = 256 + (i.val + j.val - 256) := by omega
    conv_lhs => rw [hsplit]
    rw [pow_add, root_pow_256]

/-- **`polyMulKem` is multiplication in `Rq_kem`.** -/
theorem coeffsToRqKem_polyMulKem (a b : Fin 256 → ZMod q_kem) :
    coeffsToRqKem (polyMulKem a b) = coeffsToRqKem a * coeffsToRqKem b := by
  rw [coeffsToRqKem_eq_sum, coeffsToRqKem_eq_sum, coeffsToRqKem_eq_sum,
    Finset.sum_mul_sum]
  have hR : ∀ i j : Fin 256,
      (AdjoinRoot.of mlkem_poly (a i) * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ i.val)
        * (AdjoinRoot.of mlkem_poly (b j) * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ j.val)
      = AdjoinRoot.of mlkem_poly (a i * b j)
        * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ (i.val + j.val) := by
    intro i j; rw [map_mul, pow_add]; ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hR i j))]
  have hL : ∀ k : Fin 256,
      AdjoinRoot.of mlkem_poly (polyMulKem a b k)
          * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ k.val
        = ∑ i : Fin 256,
            (if i.val ≤ k.val
              then AdjoinRoot.of mlkem_poly (a i * b (k - i))
                * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ k.val
              else -(AdjoinRoot.of mlkem_poly (a i * b (k - i))
                * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ k.val)) := by
    intro k
    simp only [polyMulKem, CatCrypt.Crypto.Lattice.SignedNegacyclicConv.signedNegaConv,
      map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hc : i.val ≤ k.val <;> simp [hc, map_neg]
  rw [Finset.sum_congr rfl (fun k _ => hL k), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine (Fintype.sum_equiv (Equiv.addRight i)
    (fun j : Fin 256 =>
      (if i.val ≤ (j + i).val
        then AdjoinRoot.of mlkem_poly (a i * b ((j + i) - i))
          * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ ((j + i)).val
        else -(AdjoinRoot.of mlkem_poly (a i * b ((j + i) - i))
          * (AdjoinRoot.root mlkem_poly : Rq_kem) ^ ((j + i)).val))) _ (fun j => rfl)).symm.trans ?_
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_sub_cancel_right, root_pow_add i j]
  by_cases hc : i.val ≤ (j + i).val <;> simp [hc]

/-! ## The parity split -/

open CatCrypt.Crypto.Lattice.SignedNegacyclicConv (signedNegaConv)

/-- The index of the constant coefficient of pair `u` is `2u`. -/
theorem pairFst_val (u : Fin 128) : (pairFst u).val = 2 * u.val := rfl

/-- The index of the linear coefficient of pair `u` is `2u + 1`. -/
theorem pairSnd_val (u : Fin 128) : (pairSnd u).val = 2 * u.val + 1 := rfl

/-- A sum over `Fin 256` as a sum over the 128 index pairs. -/
theorem sum_fin256_pairs {M : Type*} [AddCommMonoid M] (f : Fin 256 → M) :
    ∑ i : Fin 256, f i = ∑ u : Fin 128, (f (pairFst u) + f (pairSnd u)) := by
  have h0 : ∀ u : Fin 128, finProdFinEquiv (u, (0 : Fin 2)) = pairFst u := by
    intro u; apply Fin.ext; simp [finProdFinEquiv, pairFst]
  have h1 : ∀ u : Fin 128, finProdFinEquiv (u, (1 : Fin 2)) = pairSnd u := by
    intro u; apply Fin.ext; simp [finProdFinEquiv, pairSnd]; omega
  rw [← Equiv.sum_comp (finProdFinEquiv (m := 128) (n := 2)) f, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun u _ => by rw [Fin.sum_univ_two, h0, h1])

/-- `(1 : Fin 128)` has value `1`. -/
private theorem one_val_128 : (1 : Fin 128).val = 1 := rfl

/-- Even index minus even index, in `Fin 256`. -/
theorem pairFst_sub_pairFst (m u : Fin 128) : pairFst m - pairFst u = pairFst (m - u) := by
  apply Fin.ext
  have := u.isLt; have := m.isLt
  simp only [Fin.val_sub, pairFst_val]
  omega

/-- Odd index minus odd index, in `Fin 256`. -/
theorem pairSnd_sub_pairSnd (m u : Fin 128) : pairSnd m - pairSnd u = pairFst (m - u) := by
  apply Fin.ext
  have := u.isLt; have := m.isLt
  simp only [Fin.val_sub, pairFst_val, pairSnd_val]
  omega

/-- Odd index minus even index, in `Fin 256`. -/
theorem pairSnd_sub_pairFst (m u : Fin 128) : pairSnd m - pairFst u = pairSnd (m - u) := by
  apply Fin.ext
  have := u.isLt; have := m.isLt
  simp only [Fin.val_sub, pairFst_val, pairSnd_val]
  omega

/-- Even index minus odd index, in `Fin 256`: the half-index drops by one further,
which is the wraparound the negacyclic shift records. -/
theorem pairFst_sub_pairSnd (m u : Fin 128) : pairFst m - pairSnd u = pairSnd (m - u - 1) := by
  apply Fin.ext
  have := u.isLt; have := m.isLt
  simp only [Fin.val_sub, pairFst_val, pairSnd_val, one_val_128]
  omega

/-- The negacyclic shift of a signed convolution, termwise: the sign is `+` exactly
on `u < m`, and at `m = 0` the shift's negation and the empty `+` range agree. -/
theorem negaShift_signedNegaConv (x y : Fin 128 → ZMod q_kem) (m : Fin 128) :
    negaShift (signedNegaConv x y) m
      = ∑ u : Fin 128,
          (if u.val < m.val then x u * y (m - u - 1) else -(x u * y (m - u - 1))) := by
  simp only [negaShift]
  by_cases hm : 0 < m.val
  · rw [ite_eq_left hm]
    have hidx : ∀ u : Fin 128,
        (⟨m.val - 1, by have := m.isLt; omega⟩ : Fin 128) - u = m - u - 1 := by
      intro u
      apply Fin.ext
      have := u.isLt; have := m.isLt
      simp only [Fin.val_sub, one_val_128]
      omega
    simp only [signedNegaConv]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [hidx u]
    by_cases h : u.val < m.val
    · rw [ite_eq_left (show u.val ≤ m.val - 1 by omega), ite_eq_left h]
    · rw [ite_eq_right (show ¬ u.val ≤ m.val - 1 by omega), ite_eq_right h]
  · have hm0 : m.val = 0 := by omega
    rw [ite_eq_right hm]
    have hidx : ∀ u : Fin 128, (Fin.last 127 : Fin 128) - u = m - u - 1 := by
      intro u
      apply Fin.ext
      have := u.isLt
      simp only [Fin.val_sub, one_val_128, hm0, Fin.val_last]
      omega
    simp only [signedNegaConv]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have hcond : u.val ≤ (Fin.last 127 : Fin 128).val := by
      have := u.isLt; rw [Fin.val_last]; omega
    rw [ite_eq_left hcond, hidx u, ite_eq_right (show ¬ u.val < m.val by omega)]

/-- The even-index term of coefficient `2m` of the length-256 signed product. -/
theorem term_even_even (a b : Fin 256 → ZMod q_kem) (m u : Fin 128) :
    (if (pairFst u).val ≤ (pairFst m).val
        then a (pairFst u) * b (pairFst m - pairFst u)
        else -(a (pairFst u) * b (pairFst m - pairFst u)))
      = (if u.val ≤ m.val then evens a u * evens b (m - u)
        else -(evens a u * evens b (m - u))) := by
  rw [pairFst_sub_pairFst]
  have := u.isLt; have := m.isLt
  by_cases h : u.val ≤ m.val
  · rw [ite_eq_left (show (pairFst u).val ≤ (pairFst m).val by
      simp only [pairFst_val]; omega), ite_eq_left h]; rfl
  · rw [ite_eq_right (show ¬ (pairFst u).val ≤ (pairFst m).val by
      simp only [pairFst_val]; omega), ite_eq_right h]; rfl

/-- The odd-index term of coefficient `2m` of the length-256 signed product. -/
theorem term_even_odd (a b : Fin 256 → ZMod q_kem) (m u : Fin 128) :
    (if (pairSnd u).val ≤ (pairFst m).val
        then a (pairSnd u) * b (pairFst m - pairSnd u)
        else -(a (pairSnd u) * b (pairFst m - pairSnd u)))
      = (if u.val < m.val then odds a u * odds b (m - u - 1)
        else -(odds a u * odds b (m - u - 1))) := by
  rw [pairFst_sub_pairSnd]
  have := u.isLt; have := m.isLt
  by_cases h : u.val < m.val
  · rw [ite_eq_left (show (pairSnd u).val ≤ (pairFst m).val by
      simp only [pairFst_val, pairSnd_val]; omega), ite_eq_left h]; rfl
  · rw [ite_eq_right (show ¬ (pairSnd u).val ≤ (pairFst m).val by
      simp only [pairFst_val, pairSnd_val]; omega), ite_eq_right h]; rfl

/-- The even-index term of coefficient `2m + 1` of the length-256 signed product. -/
theorem term_odd_even (a b : Fin 256 → ZMod q_kem) (m u : Fin 128) :
    (if (pairFst u).val ≤ (pairSnd m).val
        then a (pairFst u) * b (pairSnd m - pairFst u)
        else -(a (pairFst u) * b (pairSnd m - pairFst u)))
      = (if u.val ≤ m.val then evens a u * odds b (m - u)
        else -(evens a u * odds b (m - u))) := by
  rw [pairSnd_sub_pairFst]
  have := u.isLt; have := m.isLt
  by_cases h : u.val ≤ m.val
  · rw [ite_eq_left (show (pairFst u).val ≤ (pairSnd m).val by
      simp only [pairFst_val, pairSnd_val]; omega), ite_eq_left h]; rfl
  · rw [ite_eq_right (show ¬ (pairFst u).val ≤ (pairSnd m).val by
      simp only [pairFst_val, pairSnd_val]; omega), ite_eq_right h]; rfl

/-- The odd-index term of coefficient `2m + 1` of the length-256 signed product. -/
theorem term_odd_odd (a b : Fin 256 → ZMod q_kem) (m u : Fin 128) :
    (if (pairSnd u).val ≤ (pairSnd m).val
        then a (pairSnd u) * b (pairSnd m - pairSnd u)
        else -(a (pairSnd u) * b (pairSnd m - pairSnd u)))
      = (if u.val ≤ m.val then odds a u * evens b (m - u)
        else -(odds a u * evens b (m - u))) := by
  rw [pairSnd_sub_pairSnd]
  have := u.isLt; have := m.isLt
  by_cases h : u.val ≤ m.val
  · rw [ite_eq_left (show (pairSnd u).val ≤ (pairSnd m).val by
      simp only [pairSnd_val]; omega), ite_eq_left h]; rfl
  · rw [ite_eq_right (show ¬ (pairSnd u).val ≤ (pairSnd m).val by
      simp only [pairSnd_val]; omega), ite_eq_right h]; rfl

/-- The even half of the length-256 signed product: the even-index terms give
`a_e ⋆ b_e` and the odd-index terms give the negacyclic shift of `a_o ⋆ b_o`. -/
theorem evens_polyMulKem (a b : Fin 256 → ZMod q_kem) :
    evens (polyMulKem a b)
      = negaConvKem (evens a) (evens b) + negaShift (negaConvKem (odds a) (odds b)) := by
  funext m
  rw [Pi.add_apply]
  simp only [negaConvKem_eq_signed]
  rw [negaShift_signedNegaConv]
  show polyMulKem a b (pairFst m) = _
  simp only [polyMulKem, signedNegaConv]
  rw [sum_fin256_pairs, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl
    (fun u _ => by simp only [term_even_even, term_even_odd])

/-- The odd half of the length-256 signed product: `a_e ⋆ b_o + a_o ⋆ b_e`. -/
theorem odds_polyMulKem (a b : Fin 256 → ZMod q_kem) :
    odds (polyMulKem a b)
      = negaConvKem (evens a) (odds b) + negaConvKem (odds a) (evens b) := by
  funext m
  rw [Pi.add_apply]
  simp only [negaConvKem_eq_signed]
  show polyMulKem a b (pairSnd m) = _
  simp only [polyMulKem, signedNegaConv]
  rw [sum_fin256_pairs, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl
    (fun u _ => by simp only [term_odd_even, term_odd_odd])

/-- **The even/odd decomposition is the length-256 signed product.** -/
theorem negaMulKem_eq_polyMulKem (a b : Fin 256 → ZMod q_kem) :
    negaMulKem a b = polyMulKem a b := by
  rw [negaMulKem, ← evens_polyMulKem, ← odds_polyMulKem, interleave_evens_odds]

/-- The coefficients of a product in `Rq_kem` are the length-256 signed product of
the coefficients. -/
theorem rqKemToCoeffs_mul (x y : Rq_kem) :
    rqKemToCoeffs (x * y) = polyMulKem (rqKemToCoeffs x) (rqKemToCoeffs y) := by
  have h : coeffsToRqKem (polyMulKem (rqKemToCoeffs x) (rqKemToCoeffs y)) = x * y := by
    rw [coeffsToRqKem_polyMulKem, coeffs_roundtrip, coeffs_roundtrip]
  rw [← h, rqKem_roundtrip]

/-- **The ML-KEM transform carries multiplication in `Rq_kem` to base
multiplication.** -/
theorem nttKem_rqKemToCoeffs_mul (x y : Rq_kem) :
    nttKem (rqKemToCoeffs (x * y))
      = basemulKem (nttKem (rqKemToCoeffs x)) (nttKem (rqKemToCoeffs y)) := by
  rw [rqKemToCoeffs_mul, ← negaMulKem_eq_polyMulKem, nttKem_negaMulKem]

/-- The length-256 signed negacyclic product of two coefficient vectors is the inverse
transform of the base multiplication of their transforms. -/
theorem polyMulKem_eq_invNttKem (a b : Fin 256 → ZMod q_kem) :
    polyMulKem a b = invNttKem (basemulKem (nttKem a) (nttKem b)) := by
  rw [← nttKem_negaMulKem, invNttKem_nttKem, negaMulKem_eq_polyMulKem]

/-- **The `Rq_kem` product through the transform** (FIPS 203 §4.3.1): multiplication in
`Rq_kem` is the inverse transform of the base multiplication of the transforms. -/
theorem rqKem_mul_eq_invNttKem (x y : Rq_kem) :
    x * y = coeffsToRqKem (invNttKem
      (basemulKem (nttKem (rqKemToCoeffs x)) (nttKem (rqKemToCoeffs y)))) := by
  rw [← nttKem_rqKemToCoeffs_mul, invNttKem_nttKem, coeffs_roundtrip]

end CatCrypt.Crypto.MLKEM.Spec.Ntt

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# Concrete NTT Roots of Unity for ML-KEM and ML-DSA

This file constructs the concrete primitive roots of unity used by the
number-theoretic transforms (NTT) of ML-KEM (FIPS 203) and ML-DSA (FIPS 204).
These are the facts that let the generic NTT theorems be instantiated
at the real crypto parameters.

* ML-KEM works in `ZMod 3329` with polynomial degree `n = 256`; the standard
  NTT root is `ζ = 17`, a primitive `256`-th root of unity (`3329 - 1 = 2^8 * 13`,
  so `256 ∣ 3329 - 1`).
* ML-DSA works in `ZMod 8380417` with a negacyclic `512`-th root `ζ = 1753`
  (`8380417 - 1 = 2^13 * 1023`, so `512 ∣ 8380417 - 1`).

## References
* NIST FIPS 203 (ML-KEM), FIPS 204 (ML-DSA)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Lattice.ConcreteNttRoots

/-! ## Primality facts (so `ZMod q` is a field) -/

/-- The ML-KEM modulus 3329 is prime. -/
instance fact_prime_3329 : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- The ML-DSA modulus 8380417 is prime. -/
instance fact_prime_8380417 : Fact (Nat.Prime 8380417) := ⟨by norm_num⟩

/-! ## ML-KEM root of unity: ζ = 17 is a primitive 256-th root in `ZMod 3329`

`256 = 2^8` is a prime power, so by `orderOf_eq_prime_pow` it suffices to show
`17^256 = 1` and `17^128 ≠ 1`. Both are concrete computations in `ZMod 3329`
closed by kernel evaluation (`decide +kernel`). -/

/-- `(17 : ZMod 3329)^256 = 1`. -/
theorem pow_256_17_eq_one : (17 : ZMod 3329) ^ 256 = 1 := by decide +kernel

/-- `(17 : ZMod 3329)^128 ≠ 1`, ruling out a smaller order (a divisor of 256
    smaller than 256 must divide 128). -/
theorem pow_128_17_ne_one : (17 : ZMod 3329) ^ 128 ≠ 1 := by decide +kernel

/-- The multiplicative order of `17` in `ZMod 3329` is exactly `256`. -/
theorem orderOf_17_eq_256 : orderOf (17 : ZMod 3329) = 256 := by
  have h : orderOf (17 : ZMod 3329) = 2 ^ (7 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 7)
      (by simpa using pow_128_17_ne_one)
      (by simpa using pow_256_17_eq_one)
  simpa using h

/-- **ML-KEM NTT root.** `ζ = 17` is a primitive `256`-th root of unity in
    `ZMod 3329`. This is the fact instantiating the generic NTT
    theorems at the ML-KEM parameters (FIPS 203). -/
theorem isPrimitiveRoot_17_256 : IsPrimitiveRoot (17 : ZMod 3329) 256 :=
  IsPrimitiveRoot.iff_orderOf.mpr orderOf_17_eq_256

/-- `(256 : ZMod 3329) ≠ 0`. Needed downstream to invert the transform length
    in `idft_dft` / `nttMul_eq_cyclicConv'`. -/
theorem n_ne_zero_3329 : (256 : ZMod 3329) ≠ 0 := by decide

/-! ## ML-DSA root of unity: ζ = 1753 is a primitive 512-th root in `ZMod 8380417`

`512 = 2^9` is a prime power, so by `orderOf_eq_prime_pow` it suffices to show
`1753^512 = 1` and `1753^256 ≠ 1`. ML-DSA uses `ζ = 1753` for its negacyclic
NTT (FIPS 204); `8380417 - 1 = 2^13 * 1023`, so `512 ∣ 8380417 - 1`. -/

/-- `(1753 : ZMod 8380417)^512 = 1`. -/
theorem pow_512_1753_eq_one : (1753 : ZMod 8380417) ^ 512 = 1 := by decide +kernel

/-- `(1753 : ZMod 8380417)^256 ≠ 1`. -/
theorem pow_256_1753_ne_one : (1753 : ZMod 8380417) ^ 256 ≠ 1 := by decide +kernel

/-- The multiplicative order of `1753` in `ZMod 8380417` is exactly `512`. -/
theorem orderOf_1753_eq_512 : orderOf (1753 : ZMod 8380417) = 512 := by
  have h : orderOf (1753 : ZMod 8380417) = 2 ^ (8 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 8)
      (by simpa using pow_256_1753_ne_one)
      (by simpa using pow_512_1753_eq_one)
  simpa using h

/-- **ML-DSA NTT root.** `ζ = 1753` is a primitive `512`-th root of unity in
    `ZMod 8380417`. This instantiates the generic negacyclic NTT theorems at the
    ML-DSA parameters (FIPS 204). -/
theorem isPrimitiveRoot_1753_512 : IsPrimitiveRoot (1753 : ZMod 8380417) 512 :=
  IsPrimitiveRoot.iff_orderOf.mpr orderOf_1753_eq_512

/-- `(256 : ZMod 8380417) ≠ 0`. Needed downstream to invert the transform
    length in the ML-DSA negacyclic NTT inversion. -/
theorem n_ne_zero_8380417 : (256 : ZMod 8380417) ≠ 0 := by decide

end CatCrypt.Crypto.Lattice.ConcreteNttRoots

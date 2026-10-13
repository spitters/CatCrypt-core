/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Tactic.NormNum.Prime

/-!
# ML-KEM Polynomial Ring Rq

Defines the concrete polynomial ring `Rq = (ZMod 3329)[X] / (X^256 + 1)` used
in ML-KEM (CRYSTALS-Kyber), using Mathlib's `AdjoinRoot`.

## Main definitions

* `q` — the ML-KEM modulus (3329, prime)
* `mlkem_poly` — the polynomial `X^256 + 1` over `ZMod q`
* `Rq` — the quotient ring `(ZMod q)[X] / (X^256 + 1)`
* `RqVec k` — vectors of `k` ring elements
* `RqMat k` — `k × k` matrices of ring elements

## Instances

All standard algebraic instances (`CommRing`, `Fintype`, `DecidableEq`, `Nonempty`)
are derived from Mathlib's `AdjoinRoot` infrastructure.

## References

* NIST FIPS 203: ML-KEM specification
* EasyCrypt: `formosa-crypto/formosa-mlkem` (abstract `R` type)
-/

@[expose] public section

namespace CatCrypt.Crypto.MLKEM.Libcrux.RqAlgebra

open Polynomial

/-! ## The ML-KEM modulus -/

/-- ML-KEM modulus: `q = 3329` is prime. -/
abbrev q : ℕ := 3329

instance : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-! ## The cyclotomic polynomial -/

/-- The polynomial `X^256 + 1` over `ZMod q`. -/
noncomputable def mlkem_poly : (ZMod q)[X] := X ^ 256 + 1

/-- `mlkem_poly` is monic (leading coefficient is 1). -/
lemma mlkem_poly_monic : mlkem_poly.Monic := by
  unfold mlkem_poly
  have : (1 : (ZMod q)[X]) = C 1 := by simp
  rw [this]
  exact monic_X_pow_add_C (1 : ZMod q) (by simp)

/-! ## The quotient ring Rq -/

/-- `Rq = (ZMod q)[X] / (X^256 + 1)`: the ML-KEM polynomial ring.

    This is a commutative ring with `q^256 = 3329^256` elements. -/
noncomputable abbrev Rq := AdjoinRoot mlkem_poly

-- Algebraic instances from Mathlib
noncomputable instance : CommRing Rq := AdjoinRoot.instCommRing _
noncomputable instance : DecidableEq Rq := AdjoinRoot.instDecidableEq _

-- Finiteness chain: monic → Module.Finite → Finite → Fintype
instance : Module.Finite (ZMod q) Rq := mlkem_poly_monic.finite_adjoinRoot
instance : Finite Rq := Module.finite_of_finite (ZMod q)
noncomputable instance : Fintype Rq := Fintype.ofFinite Rq
instance : Nonempty Rq := ⟨0⟩

/-! ## Vectors and Matrices -/

/-- Vectors of `k` ring elements (function type, automatically `Fintype`). -/
abbrev RqVec (k : ℕ) := Fin k → Rq

/-- Square matrices of ring elements (function type, automatically `Fintype`). -/
abbrev RqMat (k : ℕ) := Fin k → Fin k → Rq

end CatCrypt.Crypto.MLKEM.Libcrux.RqAlgebra

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Prime

/-!
# Verified `ZMod 3329` — the ML-KEM prime field

A computable, verified Lean reference implementation of `Z/3329Z` for use
by the ML-KEM bridge (`MlkemHaxLowCTBridge`) to replace opaque encoder
round-trip axioms with proven identities.

`q = 3329 = 13 · 256 + 1` is the prime modulus for ML-KEM-512/768/1024
(FIPS 203). Since 3329 is prime, `ZMod 3329` is a field — Mathlib provides
the full ring/field structure automatically once `Fact (Nat.Prime 3329)`
is in scope.

## API

* `Zq3329 := ZMod 3329` — the verified field
* `Zq3329.ofNat`, `Zq3329.toNat`, `Zq3329.asInt`, `Zq3329.fromInt` —
  encoders to/from `Nat`/`Int`
* `Zq3329.fromInt_asInt` — the proved round-trip identity used by bridge
  proofs to discharge previously-axiomatised encoder round-trips.

This file replaces no infrastructure; it adds a verified-field layer
underneath the existing ML-KEM bridge's structural bijection axioms.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-- ML-KEM is prime: `q = 3329`. -/
instance fact_prime_3329 : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- The ML-KEM prime field. An `abbrev` so the `ZMod` field/ring
    structure flows through transparently. -/
abbrev Zq3329 : Type := ZMod 3329

namespace Zq3329

/-! ## Field axioms — inherited from `Mathlib.Data.ZMod.Basic` -/

/-- `Zq3329` is a field. -/
example : Field Zq3329 := inferInstance

/-- `Zq3329` is a commutative ring. -/
example : CommRing Zq3329 := inferInstance

/-! ## Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod 3329) into `Zq3329`. -/
def fromNat (n : Nat) : Zq3329 := (n : ZMod 3329)

/-- Project a `Zq3329` element to a `Nat` in `[0..3328]` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Zq3329) : Nat := ZMod.val g

/-- Project a `Zq3329` element to an `Int`. -/
def asInt (g : Zq3329) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Zq3329` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Zq3329 := (i : ZMod 3329)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Zq3329) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Zq3329) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..3329)`. -/
theorem asNat_lt (g : Zq3329) : asNat g < 3329 := by
  unfold asNat
  exact ZMod.val_lt g

end Zq3329

end CatCrypt.Util

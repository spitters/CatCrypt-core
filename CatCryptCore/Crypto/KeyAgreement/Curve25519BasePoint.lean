/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KeyAgreement.Curve25519LadderU

/-!
# The base point `u = 9` of Curve25519 and its order

`B9` is the point `(9, v₉)` of Curve25519 with the v-coordinate
`v₉ = 14781619447589544791020593568409986887264606134616475288964881837755586237401` of
RFC 7748 §4.1. Its additive order is the prime `ℓ = curve25519SubgroupOrder`.

The order is computed with the x-only ladder. The ladder over the 253 bits of `ℓ`, started at
the projective x-coordinate `(9, 1)` of `B9`, ends in a first component with `Z = 0`; this is a
kernel computation of 253 ladder steps over `Fp25519` (`B9_ladder_snd`). By
`xladderFold_projMul` that component is a nonzero multiple of the projective x-coordinate of
`ℓ • B9`, so the second coordinate of the latter vanishes and `ℓ • B9` is the identity.

## Main definitions

* `B9v`, `B9` — the v-coordinate and the point

## Main results

* `B9_nonsingular` — `(9, v₉)` is a nonsingular point of the curve
* `uCoord_B9` — `uCoord B9 = 9`
* `B9_order_nsmul`, `B9_addOrder` — `ℓ • B9 = 0` and `addOrderOf B9 = ℓ`
* `x25519_base_spec_B9` — the base-point function of the X25519 specification is clamped scalar
  multiplication of `B9`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ECC

open CatCrypt.Crypto.KeyAgreement.X25519

/-- The v-coordinate of the base point `u = 9` (RFC 7748 §4.1). -/
def B9v : Fp25519 :=
  14781619447589544791020593568409986887264606134616475288964881837755586237401

/-- `(9, v₉)` satisfies `v₉² = 9³ + 486662 · 9² + 9` and `2 · v₉ ≠ 0`. -/
theorem B9_nonsingular : (montgomeryW (486662 : Fp25519)).toAffine.Nonsingular 9 B9v := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', montgomeryW_equation]
  simp only [montgomeryW_a₁, montgomeryW_a₃, zero_mul, add_zero]
  refine ⟨by decide +kernel, Or.inr (by decide +kernel)⟩

/-- **The base point `u = 9` of Curve25519** (RFC 7748 §4.1). -/
def B9 : Curve25519Point := .some 9 B9v B9_nonsingular

theorem B9_ne_zero : B9 ≠ 0 := by
  intro h
  cases h

theorem uCoord_B9 : uCoord B9 = 9 := by
  simp [B9, uCoord, curve25519_xProj_eq, xProjW_some]

/-- The 253 bits of `ℓ`, least significant first, represent `ℓ`. -/
theorem bitsToNat_bitsOfMSB_subgroupOrder :
    bitsToNat (Spec.bitsOfMSB 253 curve25519SubgroupOrder).reverse = curve25519SubgroupOrder := by
  rw [Spec.bitsToNat_reverse_bitsOfMSB, Nat.mod_eq_of_lt]
  rw [curve25519SubgroupOrder_eq]
  norm_num

/-- **The ladder over the bits of `ℓ` at `(9, 1)` ends with `Z = 0`**, a kernel computation of
253 ladder steps over `Fp25519`. -/
theorem B9_ladder_snd :
    (xladderFold (curve25519Params Fp25519).a24 ((9 : Fp25519), 1)
      (Spec.bitsOfMSB 253 curve25519SubgroupOrder).reverse).1.2 = 0 := by
  decide +kernel

/-- **`ℓ • B9 = 0`.** -/
theorem B9_order_nsmul : curve25519SubgroupOrder • B9 = 0 := by
  have hu : uCoord B9 ≠ 0 := by
    rw [uCoord_B9, show (9 : Fp25519) = ((9 : ℕ) : Fp25519) by norm_cast]
    exact fp25519_small_ne_zero (by norm_num) (by norm_num)
  have h := (xladderFold_projMul B9 hu (Spec.bitsOfMSB 253 curve25519SubgroupOrder).reverse).1
  rw [xProj_eq_uCoord B9_ne_zero, uCoord_B9, bitsToNat_bitsOfMSB_subgroupOrder] at h
  obtain ⟨c, hc, hst⟩ := h
  have hz := congrArg Prod.snd hst
  rw [B9_ladder_snd] at hz
  by_contra hne
  rw [xProj_eq_uCoord hne, mul_one] at hz
  exact hc hz.symm

/-- **The base point has order `ℓ`.** -/
theorem B9_addOrder : addOrderOf B9 = curve25519SubgroupOrder :=
  addOrderOf_eq_prime B9_order_nsmul B9_ne_zero

instance factB9AddOrder : Fact (addOrderOf B9 = curve25519SubgroupOrder) :=
  ⟨B9_addOrder⟩

/-- **The base-point function of the X25519 specification** is clamped scalar multiplication of
`B9`: it returns the encoding of `clampScalar (natOfLeBytes sk) • B9`. -/
theorem x25519_base_spec_B9 (sk : Vector UInt8 32) :
    Spec.x25519_base_spec sk =
      encU (clampScalar (natOfLeBytes sk) • (⟨B9, AddSubgroup.mem_zmultiples B9⟩ : G25519 B9)) :=
  x25519_base_spec_encU uCoord_B9 sk

end CatCrypt.Crypto.ECC

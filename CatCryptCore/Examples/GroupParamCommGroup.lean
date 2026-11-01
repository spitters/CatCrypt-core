/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.GroupParam
public import CatCryptCore.ForMathlib.ZModPow
public import Mathlib.Algebra.Field.ZMod

/-!
# The group parameters of a commutative group of prime order

A finite commutative group `G` of prime order `q` with an element `g` of order `q` gives group
parameters `GroupParam.ofCommGroup G g q`: the scalars are the field `ZMod q`, the generator
exponentiation is `exp s = g ^ s.val` and the exponentiation of an element is
`groupExp h s = h ^ s.val`, both by the representative `s.val < q`; the group operations are
those of `G`. These are the exponentiations of exponential ElGamal over an element of order `q`,
which encrypts `m` with coins `r` under `K` as `(g ^ r.val, g ^ m.val · K ^ r.val)`, so the
Σ-protocols over `GroupParam` state relations on its ciphertexts at these parameters.

## Main definitions

* `GroupParam.ofCommGroup` — the group parameters of `G` with generator `g` of order
  `q = |G|`, `q` prime.

## Main results

* `GroupParam.card_scalar_ofCommGroup` — the parameters have `q` scalars.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.GroupParam

variable (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (g : G) (q : ℕ) [Fact q.Prime]

/-- **The group parameters of a commutative group of prime order.** For a finite commutative
group `G` of prime order `q` and `g` of order `q`: scalars `ZMod q`, `exp s = g ^ s.val`,
`groupExp h s = h ^ s.val`, the group operations of `G` and the field operations of `ZMod q`. -/
@[implicit_reducible]
noncomputable def ofCommGroup (hq : orderOf g = q) (hcard : Fintype.card G = q) : GroupParam where
  G := G
  Scalar := ZMod q
  neG := ⟨1⟩
  neScalar := ⟨0⟩
  generator := g
  identity := 1
  exp s := g ^ s.val
  groupExp h s := h ^ s.val
  scalarAdd a b := a + b
  scalarMul a b := a * b
  scalarSub a b := a - b
  scalarDiv a b := a / b
  scalarNeg a := -a
  scalarZero := 0
  groupMul a b := a * b
  groupInv a := a⁻¹
  scalarOne := 1
  exp_add x y := ZMod.pow_val_add_of_pow_eq_one (hcard ▸ pow_card_eq_one) x y
  exp_zero := by rw [ZMod.val_zero, pow_zero]
  div_mul_cancel x _ hy := div_mul_cancel₀ x hy
  groupExp_generator _ := rfl
  groupExp_exp w e := (ZMod.pow_val_mul_of_pow_eq_one (hcard ▸ pow_card_eq_one) w e).symm
  groupExp_one h := by rw [ZMod.val_one, pow_one]
  groupExp_add _ a b := ZMod.pow_val_add_of_pow_eq_one (hcard ▸ pow_card_eq_one) a b
  scalarSub_ne_zero _ _ hab := sub_ne_zero.mpr hab
  groupMul_identity := mul_one
  identity_groupMul := one_mul
  groupMul_inv := mul_inv_cancel
  inv_groupMul := inv_mul_cancel
  groupMul_assoc := mul_assoc
  groupExp_zero _ := by rw [ZMod.val_zero, pow_zero]
  scalarMul_one := mul_one
  groupInv_groupExp _ e := (ZMod.pow_val_neg_of_pow_eq_one (hcard ▸ pow_card_eq_one) e).symm
  scalarSub_eq := sub_eq_add_neg
  scalarAdd_neg := add_neg_cancel
  exp_surj := (ZMod.pow_val_bijective hq hcard).2
  exp_inj _ _ h := ZMod.pow_val_injective hq h
  scalarAdd_comm := add_comm
  scalarAdd_assoc := add_assoc
  scalarMul_add := mul_add
  scalarAdd_mul := add_mul
  scalarMul_comm := mul_comm
  scalarAdd_zero := add_zero
  scalarZero_add := zero_add
  scalarNeg_add := neg_add_cancel
  scalarNeg_zero := neg_zero
  scalarNeg_add_distrib := neg_add
  scalarMul_zero := mul_zero
  scalarZero_mul := zero_mul
  mul_div_cancel a _ hb := mul_div_cancel_right₀ a hb
  scalarMul_assoc := mul_assoc

/-- The group parameters of `G` have `q` scalars. -/
theorem card_scalar_ofCommGroup (hq : orderOf g = q) (hcard : Fintype.card G = q) :
    Fintype.card (ofCommGroup G g q hq hcard).Scalar = q :=
  ZMod.card q

end CatCrypt.Examples.GroupParam

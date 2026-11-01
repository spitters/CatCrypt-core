/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Powers by the representative of an element of `ZMod q`

For an element `x` of a monoid with `x ^ q = 1`, the power `x ^ a.val` by the representative
`a.val < q` of `a : ZMod q` is additive and multiplicative in `a`, and in a group it is inverted
by negation. For an element `g` of order `q`, `a ↦ g ^ a.val` is injective, and it is a
bijection onto a finite group of order `q`.

## Main results

* `ZMod.pow_val_add_of_pow_eq_one` — `x ^ (a + b).val = x ^ a.val * x ^ b.val`.
* `ZMod.pow_val_mul_of_pow_eq_one` — `x ^ (a * b).val = (x ^ a.val) ^ b.val`.
* `ZMod.pow_val_neg_of_pow_eq_one` — `x ^ (-a).val = (x ^ a.val)⁻¹`.
* `ZMod.pow_val_injective` — for `g` of order `q`, `a ↦ g ^ a.val` is injective.
* `ZMod.pow_val_bijective` — for `g` of order `q` in a finite group of order `q`, it is
  bijective.
-/

@[expose] public section

set_option autoImplicit false

namespace ZMod

variable {q : ℕ}

/-- For `x ^ q = 1`, the power by the representative of a sum is the product of the powers. -/
theorem pow_val_add_of_pow_eq_one [NeZero q] {M : Type*} [Monoid M] {x : M} (hx : x ^ q = 1)
    (a b : ZMod q) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [val_add, ← pow_eq_pow_mod _ hx, pow_add]

/-- For `x ^ q = 1`, the power by the representative of a product is the iterated power. -/
theorem pow_val_mul_of_pow_eq_one {M : Type*} [Monoid M] {x : M} (hx : x ^ q = 1)
    (a b : ZMod q) : x ^ (a * b).val = (x ^ a.val) ^ b.val := by
  rw [val_mul, ← pow_eq_pow_mod _ hx, pow_mul]

/-- For `x ^ q = 1`, the power by the representative of `-a` is the inverse of the power by the
representative of `a`. -/
theorem pow_val_neg_of_pow_eq_one [NeZero q] {G : Type*} [Group G] {x : G} (hx : x ^ q = 1)
    (a : ZMod q) : x ^ (-a).val = (x ^ a.val)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (by
    rw [← pow_val_add_of_pow_eq_one hx, add_neg_cancel, val_zero, pow_zero])).symm

/-- For `g` of order `q`, the power by the representative is injective on `ZMod q`. -/
theorem pow_val_injective [NeZero q] {M : Type*} [Monoid M] {g : M} (hq : orderOf g = q) :
    Function.Injective fun a : ZMod q => g ^ a.val := fun a b h =>
  val_injective q (pow_injOn_Iio_orderOf (Set.mem_Iio.2 (hq ▸ val_lt a))
    (Set.mem_Iio.2 (hq ▸ val_lt b)) h)

/-- For `g` of order `q` in a finite group of order `q`, the power by the representative is a
bijection from `ZMod q`. -/
theorem pow_val_bijective [NeZero q] {G : Type*} [Group G] [Fintype G] {g : G}
    (hq : orderOf g = q) (hcard : Fintype.card G = q) :
    Function.Bijective fun a : ZMod q => g ^ a.val :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨pow_val_injective hq, by rw [card, hcard]⟩

end ZMod

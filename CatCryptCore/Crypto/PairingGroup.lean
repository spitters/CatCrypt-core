/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import CatCryptCore.Core.Code

/-!
# Bilinear Pairing Groups

This file defines bilinear pairing groups (Type III pairings) integrated with Mathlib's
algebraic hierarchy.

## Main definitions

* `PairingGroup` — class bundling G₁, G₂, GT with bilinear, non-degenerate pairing
* `e_bilinear` — `e(g₁^a, g₂^b) = e(g₁, g₂)^(a*b)`
* `zpowZMod₁/₂` — exponentiation by ZMod elements
* `srs₁/srs₂` — Structured Reference Strings for KZG

## References

* [Kate, Zaverucha, Goldberg, *Constant-Size Commitments to Polynomials and Their
  Applications*, ASIACRYPT 2010]
-/

namespace CatCrypt.Crypto

open CatCrypt.Core

/-! ## Pairing Group Class -/

/-- A bilinear pairing group (Type III setting).

Groups are in multiplicative notation with `CommGroup` instances.
The pairing `e : G₁ → G₂ → GT` is bilinear and non-degenerate. -/
class PairingGroup where
  /-- Source group 1 -/
  G₁ : Type
  /-- Source group 2 -/
  G₂ : Type
  /-- Target group -/
  GT : Type
  /-- Prime order of all groups -/
  p : ℕ
  [instPrime : Fact (Nat.Prime p)]
  [instCommGroupG₁ : CommGroup G₁]
  [instFintypeG₁ : Fintype G₁]
  [instDecEqG₁ : DecidableEq G₁]
  [instCommGroupG₂ : CommGroup G₂]
  [instFintypeG₂ : Fintype G₂]
  [instDecEqG₂ : DecidableEq G₂]
  [instCommGroupGT : CommGroup GT]
  [instFintypeGT : Fintype GT]
  [instDecEqGT : DecidableEq GT]
  /-- Cardinality constraints -/
  cardG₁ : Fintype.card G₁ = p
  cardG₂ : Fintype.card G₂ = p
  /-- Generator of G₁ -/
  g₁ : G₁
  /-- Generator of G₂ -/
  g₂ : G₂
  /-- g₁ generates G₁ -/
  g₁_generates : ∀ x : G₁, ∃ n : ℤ, x = g₁ ^ n
  /-- g₂ generates G₂ -/
  g₂_generates : ∀ x : G₂, ∃ n : ℤ, x = g₂ ^ n
  /-- Bilinear pairing function -/
  e : G₁ → G₂ → GT
  /-- Bilinearity in first argument -/
  e_mul_left : ∀ (a b : G₁) (y : G₂), e (a * b) y = e a y * e b y
  /-- Bilinearity in second argument -/
  e_mul_right : ∀ (x : G₁) (a b : G₂), e x (a * b) = e x a * e x b
  /-- Non-degeneracy: e(g₁, g₂) ≠ 1 -/
  e_nondeg : e g₁ g₂ ≠ 1

attribute [instance] PairingGroup.instPrime
  PairingGroup.instCommGroupG₁ PairingGroup.instFintypeG₁ PairingGroup.instDecEqG₁
  PairingGroup.instCommGroupG₂ PairingGroup.instFintypeG₂ PairingGroup.instDecEqG₂
  PairingGroup.instCommGroupGT PairingGroup.instFintypeGT PairingGroup.instDecEqGT

namespace PairingGroup

variable {P : PairingGroup}

/-! ## Nonempty instances -/

instance instNonemptyG₁ : Nonempty P.G₁ := ⟨1⟩
instance instNonemptyG₂ : Nonempty P.G₂ := ⟨1⟩
instance instNonemptyGT : Nonempty P.GT := ⟨1⟩

/-! ## Basic pairing lemmas -/

@[simp]
theorem e_one_left (y : P.G₂) : P.e 1 y = 1 := by
  have h := P.e_mul_left 1 1 y
  rw [one_mul] at h
  -- h : P.e 1 y = P.e 1 y * P.e 1 y, hence self-mul-self = self → = 1
  have h2 : P.e 1 y * 1 = P.e 1 y * P.e 1 y := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

@[simp]
theorem e_one_right (x : P.G₁) : P.e x 1 = 1 := by
  have h := P.e_mul_right x 1 1
  rw [one_mul] at h
  have h2 : P.e x 1 * 1 = P.e x 1 * P.e x 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

theorem e_inv_left (x : P.G₁) (y : P.G₂) : P.e x⁻¹ y = (P.e x y)⁻¹ := by
  have h : P.e x⁻¹ y * P.e x y = 1 := by
    rw [← P.e_mul_left, inv_mul_cancel, e_one_left]
  exact mul_eq_one_iff_eq_inv.mp h

theorem e_inv_right (x : P.G₁) (y : P.G₂) : P.e x y⁻¹ = (P.e x y)⁻¹ := by
  have h : P.e x y⁻¹ * P.e x y = 1 := by
    rw [← P.e_mul_right, inv_mul_cancel, e_one_right]
  exact mul_eq_one_iff_eq_inv.mp h

/-! ## Power lemmas -/

theorem e_pow_left (n : ℕ) (y : P.G₂) :
    P.e (P.g₁ ^ n) y = (P.e P.g₁ y) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, P.e_mul_left, ih, pow_succ]

theorem e_pow_right (x : P.G₁) (n : ℕ) :
    P.e x (P.g₂ ^ n) = (P.e x P.g₂) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, P.e_mul_right, ih, pow_succ]

theorem e_zpow_left (n : ℤ) (y : P.G₂) :
    P.e (P.g₁ ^ n) y = (P.e P.g₁ y) ^ n := by
  cases n with
  | ofNat k => simp [zpow_natCast, e_pow_left]
  | negSucc k =>
    simp only [zpow_negSucc]
    rw [e_inv_left, e_pow_left]

theorem e_zpow_right (x : P.G₁) (n : ℤ) :
    P.e x (P.g₂ ^ n) = (P.e x P.g₂) ^ n := by
  cases n with
  | ofNat k => simp [zpow_natCast, e_pow_right]
  | negSucc k =>
    simp only [zpow_negSucc]
    rw [e_inv_right, e_pow_right]

/-- The key bilinearity theorem: `e(g₁^a, g₂^b) = e(g₁, g₂)^(a*b)` -/
theorem e_bilinear (a b : ℤ) :
    P.e (P.g₁ ^ a) (P.g₂ ^ b) = (P.e P.g₁ P.g₂) ^ (a * b) := by
  rw [e_zpow_left, e_zpow_right, ← zpow_mul, mul_comm]

/-- Pairing is symmetric in exponents -/
theorem e_zpow_zpow (a b : ℤ) :
    P.e (P.g₁ ^ a) (P.g₂ ^ b) = P.e (P.g₁ ^ b) (P.g₂ ^ a) := by
  rw [e_bilinear, e_bilinear, mul_comm]

/-! ## ZMod exponentiation -/

/-- Exponentiate by a `ZMod P.p` element via its value representative -/
noncomputable def zpowZMod₁ (x : P.G₁) (a : ZMod P.p) : P.G₁ :=
  x ^ (a.val : ℤ)

noncomputable def zpowZMod₂ (x : P.G₂) (a : ZMod P.p) : P.G₂ :=
  x ^ (a.val : ℤ)

noncomputable def zpowZModT (x : P.GT) (a : ZMod P.p) : P.GT :=
  x ^ (a.val : ℤ)

/-- Notation: `x ^ᵍ a` for ZMod exponentiation in G₁.

The exponent binds tighter than relational/arithmetic operators, so
`g ^ᵍ s = a * pk ^ᵍ c` parses as `(g ^ᵍ s) = (a * (pk ^ᵍ c))`. -/
scoped notation:75 x:75 " ^ᵍ " a:76 => zpowZMod₁ x a

/-- Notation: `x ^ʰ a` for ZMod exponentiation in G₂ (same precedence as `^ᵍ`). -/
scoped notation:75 x:75 " ^ʰ " a:76 => zpowZMod₂ x a

/-! ## Generator order -/

/-- g₁ has order p (since it generates G₁ of cardinality p) -/
theorem orderOf_g₁ : orderOf P.g₁ = P.p := by
  rw [← P.cardG₁, ← Nat.card_eq_fintype_card]
  exact orderOf_eq_card_of_forall_mem_zpowers
    (fun x => let ⟨n, hn⟩ := P.g₁_generates x; ⟨n, hn.symm⟩)

/-- g₂ has order p -/
theorem orderOf_g₂ : orderOf P.g₂ = P.p := by
  rw [← P.cardG₂, ← Nat.card_eq_fintype_card]
  exact orderOf_eq_card_of_forall_mem_zpowers
    (fun x => let ⟨n, hn⟩ := P.g₂_generates x; ⟨n, hn.symm⟩)

/-- g₁ ^ p = 1 -/
theorem g₁_pow_p : P.g₁ ^ P.p = 1 := by
  rw [← orderOf_g₁]; exact pow_orderOf_eq_one _

/-- g₁ ^ n = g₁ ^ (n % p) -/
theorem g₁_pow_mod (n : ℕ) : P.g₁ ^ n = P.g₁ ^ (n % P.p) := by
  conv_lhs => rw [← Nat.div_add_mod n P.p]
  rw [pow_add, pow_mul, g₁_pow_p, one_pow, one_mul]

/-- g₂ ^ n = g₂ ^ (n % p) -/
theorem g₂_pow_mod (n : ℕ) : P.g₂ ^ n = P.g₂ ^ (n % P.p) := by
  conv_lhs => rw [← Nat.div_add_mod n P.p]
  rw [pow_add, pow_mul]
  rw [← orderOf_g₂]; rw [pow_orderOf_eq_one]; rw [one_pow, one_mul]

/-! ## zpowZMod lemmas -/

/-- Any element of G₁ raised to p is 1 -/
theorem pow_p_eq_one_G₁ (x : P.G₁) : x ^ P.p = 1 := by
  rw [← P.cardG₁]; exact pow_card_eq_one

/-- Any element of G₁: x ^ n = x ^ (n % p) -/
theorem pow_mod_G₁ (x : P.G₁) (n : ℕ) : x ^ n = x ^ (n % P.p) := by
  conv_lhs => rw [← Nat.div_add_mod n P.p]
  rw [pow_add, pow_mul, pow_p_eq_one_G₁, one_pow, one_mul]

/-- Composition: (x ^ᵍ a) ^ᵍ b = x ^ᵍ (a * b) for any x in G₁ -/
theorem zpowZMod₁_zpowZMod₁ (x : P.G₁) (a b : ZMod P.p) :
    zpowZMod₁ (P := P) (zpowZMod₁ (P := P) x a) b = zpowZMod₁ (P := P) x (a * b) := by
  simp only [zpowZMod₁, zpow_natCast]
  rw [← pow_mul]
  conv_lhs => rw [pow_mod_G₁]
  congr 1; exact (ZMod.val_mul a b).symm

/-- g₁ ^ᵍ a = g₁ ^ a.val (ℕ version) -/
theorem zpowZMod₁_eq_pow (a : ZMod P.p) :
    zpowZMod₁ (P := P) P.g₁ a = P.g₁ ^ a.val := by
  unfold zpowZMod₁; rw [zpow_natCast]

/-- g₂ ^ʰ a = g₂ ^ a.val (ℕ version) -/
theorem zpowZMod₂_eq_pow (a : ZMod P.p) :
    zpowZMod₂ (P := P) P.g₂ a = P.g₂ ^ a.val := by
  unfold zpowZMod₂; rw [zpow_natCast]

/-- g₁ ^ᵍ (a + b) = (g₁ ^ᵍ a) * (g₁ ^ᵍ b) -/
theorem zpowZMod₁_add (a b : ZMod P.p) :
    zpowZMod₁ (P := P) P.g₁ (a + b) =
    zpowZMod₁ (P := P) P.g₁ a * zpowZMod₁ (P := P) P.g₁ b := by
  simp only [zpowZMod₁_eq_pow, ← pow_add]
  conv_rhs => rw [g₁_pow_mod]
  congr 1
  exact ZMod.val_add a b

/-- g₂ ^ʰ (a + b) = (g₂ ^ʰ a) * (g₂ ^ʰ b) -/
theorem zpowZMod₂_add (a b : ZMod P.p) :
    zpowZMod₂ (P := P) P.g₂ (a + b) =
    zpowZMod₂ (P := P) P.g₂ a * zpowZMod₂ (P := P) P.g₂ b := by
  simp only [zpowZMod₂_eq_pow, ← pow_add]
  conv_rhs => rw [g₂_pow_mod]
  congr 1
  exact ZMod.val_add a b

/-- (g₁ ^ᵍ a)⁻¹ = g₁ ^ᵍ (-a) -/
theorem zpowZMod₁_neg (a : ZMod P.p) :
    (zpowZMod₁ (P := P) P.g₁ a)⁻¹ = zpowZMod₁ (P := P) P.g₁ (-a) := by
  have h : zpowZMod₁ (P := P) P.g₁ (-a) * zpowZMod₁ (P := P) P.g₁ a = 1 := by
    rw [← zpowZMod₁_add, neg_add_cancel, zpowZMod₁_eq_pow, ZMod.val_zero, pow_zero]
  exact (mul_eq_one_iff_eq_inv.mp h).symm

/-- (g₂ ^ʰ a)⁻¹ = g₂ ^ʰ (-a) -/
theorem zpowZMod₂_neg (a : ZMod P.p) :
    (zpowZMod₂ (P := P) P.g₂ a)⁻¹ = zpowZMod₂ (P := P) P.g₂ (-a) := by
  have h : zpowZMod₂ (P := P) P.g₂ (-a) * zpowZMod₂ (P := P) P.g₂ a = 1 := by
    rw [← zpowZMod₂_add, neg_add_cancel, zpowZMod₂_eq_pow, ZMod.val_zero, pow_zero]
  exact (mul_eq_one_iff_eq_inv.mp h).symm

/-- g₁ ^ᵍ (a - b) = g₁ ^ᵍ a * (g₁ ^ᵍ b)⁻¹ -/
theorem zpowZMod₁_sub (a b : ZMod P.p) :
    zpowZMod₁ (P := P) P.g₁ (a - b) =
    zpowZMod₁ (P := P) P.g₁ a * (zpowZMod₁ (P := P) P.g₁ b)⁻¹ := by
  rw [sub_eq_add_neg, zpowZMod₁_add, zpowZMod₁_neg]

/-- g₂ ^ʰ (a - b) = g₂ ^ʰ a * (g₂ ^ʰ b)⁻¹ -/
theorem zpowZMod₂_sub (a b : ZMod P.p) :
    zpowZMod₂ (P := P) P.g₂ (a - b) =
    zpowZMod₂ (P := P) P.g₂ a * (zpowZMod₂ (P := P) P.g₂ b)⁻¹ := by
  rw [sub_eq_add_neg, zpowZMod₂_add, zpowZMod₂_neg]

/-- g₁ ^ᵍ (a * b) = g₁ ^ (a.val * b.val) mod p -/
theorem zpowZMod₁_mul (a b : ZMod P.p) :
    zpowZMod₁ (P := P) P.g₁ (a * b) = P.g₁ ^ (a.val * b.val) := by
  simp only [zpowZMod₁_eq_pow]
  conv_rhs => rw [g₁_pow_mod]
  congr 1
  exact ZMod.val_mul a b

/-- Product of zpowZMod₁ over a finset equals zpowZMod₁ of the sum -/
theorem zpowZMod₁_finprod {ι : Type*} [DecidableEq ι]
    (f : ι → ZMod P.p) (s : Finset ι) :
    (∏ i ∈ s, zpowZMod₁ (P := P) P.g₁ (f i)) =
    zpowZMod₁ (P := P) P.g₁ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp [zpowZMod₁_eq_pow]
  | @insert a s' hmem ih =>
    rw [Finset.prod_insert hmem, Finset.sum_insert hmem, zpowZMod₁_add, ih]

/-- Product of zpowZMod₁ over Fin univ -/
theorem zpowZMod₁_finprod_univ {n : ℕ} (f : Fin n → ZMod P.p) :
    (∏ i : Fin n, zpowZMod₁ (P := P) P.g₁ (f i)) =
    zpowZMod₁ (P := P) P.g₁ (∑ i : Fin n, f i) := by
  exact zpowZMod₁_finprod _ Finset.univ

/-- e(g₁, g₂)^p = 1 -/
theorem eT_pow_p : (P.e P.g₁ P.g₂) ^ P.p = 1 := by
  rw [← e_pow_left]; rw [pow_p_eq_one_G₁]; exact e_one_left _

/-- e(g₁, g₂) ^ n = e(g₁, g₂) ^ (n % p) -/
theorem eT_pow_mod (n : ℕ) :
    (P.e P.g₁ P.g₂) ^ n = (P.e P.g₁ P.g₂) ^ (n % P.p) := by
  conv_lhs => rw [← Nat.div_add_mod n P.p]
  rw [pow_add, pow_mul, eT_pow_p, one_pow, one_mul]

/-- Pairing with zpowZMod: e(g₁^ᵍa, g₂^ʰb) = e(g₁,g₂)^(a.val * b.val) -/
theorem e_zpowZMod (a b : ZMod P.p) :
    P.e (zpowZMod₁ (P := P) P.g₁ a) (zpowZMod₂ (P := P) P.g₂ b) =
    (P.e P.g₁ P.g₂) ^ ((a.val : ℤ) * (b.val : ℤ)) := by
  unfold zpowZMod₁ zpowZMod₂
  exact e_bilinear a.val b.val

/-- Key: e(g₁ ^ᵍ (a*b), g₂) = e(g₁ ^ᵍ a, g₂ ^ʰ b) -/
theorem e_zpowZMod_prod (a b : ZMod P.p) :
    P.e (zpowZMod₁ (P := P) P.g₁ (a * b)) P.g₂ =
    P.e (zpowZMod₁ (P := P) P.g₁ a) (zpowZMod₂ (P := P) P.g₂ b) := by
  -- LHS = (e g₁ g₂) ^ (a*b).val, RHS = (e g₁ g₂) ^ (a.val * b.val)
  -- These are equal because (e g₁ g₂)^p = 1 and (a*b).val ≡ a.val * b.val (mod p)
  unfold zpowZMod₁ zpowZMod₂
  rw [e_zpow_left, e_bilinear]
  rw [show (a.val : ℤ) * (b.val : ℤ) = ((a.val * b.val : ℕ) : ℤ) from by push_cast; ring]
  rw [zpow_natCast, zpow_natCast]
  conv_rhs => rw [eT_pow_mod]
  congr 1; exact ZMod.val_mul a b

/-! ## General power lemmas (for arbitrary group elements) -/

/-- e(x^n, y) = e(x, y)^n for every x ∈ G₁ -/
theorem e_pow_left_general (x : P.G₁) (n : ℕ) (y : P.G₂) :
    P.e (x ^ n) y = (P.e x y) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, P.e_mul_left, ih, pow_succ]

/-- e(x^n, y) = e(x, y)^n for integer exponent -/
theorem e_zpow_left_general (x : P.G₁) (n : ℤ) (y : P.G₂) :
    P.e (x ^ n) y = (P.e x y) ^ n := by
  cases n with
  | ofNat k => simp [zpow_natCast, e_pow_left_general]
  | negSucc k =>
    simp only [zpow_negSucc]
    rw [e_inv_left, e_pow_left_general]

/-- e(zpowZMod₁ x a, y) = e(x, y) ^ a.val for any x ∈ G₁ -/
theorem e_zpowZMod_left (x : P.G₁) (a : ZMod P.p) (y : P.G₂) :
    P.e (zpowZMod₁ (P := P) x a) y = (P.e x y) ^ (a.val : ℤ) := by
  unfold zpowZMod₁
  exact e_zpow_left_general x a.val y

/-! ## Order-theoretic lemmas -/

/-- e(g₁, g₂) has order p in GT -/
theorem orderOf_eT : orderOf (P.e P.g₁ P.g₂) = P.p := by
  have h_dvd : orderOf (P.e P.g₁ P.g₂) ∣ P.p :=
    orderOf_dvd_of_pow_eq_one eT_pow_p
  have h_ne_one : P.e P.g₁ P.g₂ ≠ 1 := P.e_nondeg
  have h_ord_ne_one : orderOf (P.e P.g₁ P.g₂) ≠ 1 := by
    intro h; rw [orderOf_eq_one_iff] at h; exact h_ne_one h
  exact (P.instPrime.out.eq_one_or_self_of_dvd _ h_dvd).resolve_left h_ord_ne_one

/-- Non-degeneracy gives first-argument injectivity:
    if e(x, g₂) = 1, then x = 1. -/
theorem e_first_arg_eq_one (x : P.G₁) (h : P.e x P.g₂ = 1) : x = 1 := by
  obtain ⟨n, rfl⟩ := P.g₁_generates x
  rw [e_zpow_left] at h
  -- h : (P.e P.g₁ P.g₂) ^ n = 1, so orderOf(eT) | n
  have h_dvd : (P.p : ℤ) ∣ n := by
    rw [← orderOf_eT]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h
  obtain ⟨k, hk⟩ := h_dvd
  rw [hk, zpow_mul, zpow_natCast, g₁_pow_p, one_zpow]

/-- Generalized non-degeneracy: e(x, g₂^c) = 1 and c ≠ 0 implies x = 1. -/
theorem e_first_arg_eq_one_general (x : P.G₁) (c : ZMod P.p) (hc : c ≠ 0)
    (h : P.e x (zpowZMod₂ (P := P) P.g₂ c) = 1) : x = 1 := by
  haveI : NeZero P.p := ⟨P.instPrime.out.ne_zero⟩
  apply e_first_arg_eq_one
  unfold zpowZMod₂ at h
  rw [e_zpow_right] at h
  rw [zpow_natCast] at h
  by_contra h_ne
  have hetp : (P.e x P.g₂) ^ P.p = 1 := by
    rw [← e_pow_left_general, pow_p_eq_one_G₁]; exact e_one_left _
  have h_ord_p : orderOf (P.e x P.g₂) = P.p :=
    (P.instPrime.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hetp)).resolve_left
      (by rw [orderOf_eq_one_iff]; exact h_ne)
  have h_dvd : orderOf (P.e x P.g₂) ∣ c.val := orderOf_dvd_of_pow_eq_one h
  rw [h_ord_p] at h_dvd
  exact (by rwa [ne_eq, ZMod.val_eq_zero] : c.val ≠ 0)
    (Nat.eq_zero_of_dvd_of_lt h_dvd (ZMod.val_lt c))

/-- g₁ ^ᵍ a = 1 iff a = 0 -/
theorem zpowZMod₁_eq_one_iff (a : ZMod P.p) :
    zpowZMod₁ (P := P) P.g₁ a = 1 ↔ a = 0 := by
  constructor
  · intro h
    unfold zpowZMod₁ at h
    have h_dvd : (orderOf P.g₁ : ℤ) ∣ (a.val : ℤ) :=
      orderOf_dvd_iff_zpow_eq_one.mpr h
    rw [orderOf_g₁, Int.natCast_dvd_natCast] at h_dvd
    have hlt := ZMod.val_lt a
    have := Nat.eq_zero_of_dvd_of_lt h_dvd hlt
    rwa [ZMod.val_eq_zero] at this
  · intro h; rw [h]; simp [zpowZMod₁, ZMod.val_zero]

/-! ## Power bijection -/

/-- `x ^ᵍ 1 = x` -/
theorem zpowZMod₁_one (x : P.G₁) : zpowZMod₁ (P := P) x 1 = x := by
  unfold zpowZMod₁; rw [ZMod.val_one]; simp

/-- In `ZMod p` with `p` prime, nonzero elements satisfy `a * a⁻¹ = 1`. -/
private theorem zpow_mul_inv_cancel (a : ZMod P.p) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [ZMod.mul_inv_eq_gcd]
  have : Nat.Coprime a.val P.p :=
    Nat.Coprime.symm (P.instPrime.out.coprime_iff_not_dvd.mpr
      fun h => ha ((ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt a))))
  simp [this]

/-- `x ↦ x ^ᵍ sk` is a bijection on G₁ when `sk ≠ 0`.

    The inverse is `x ↦ x ^ᵍ sk⁻¹`. This uses the composition law
    `zpowZMod₁_zpowZMod₁` and the fact that `ZMod p` is a field. -/
noncomputable def zpowZMod₁_right_equiv (sk : ZMod P.p) (hsk : sk ≠ 0) :
    P.G₁ ≃ P.G₁ where
  toFun := fun x => zpowZMod₁ (P := P) x sk
  invFun := fun x => zpowZMod₁ (P := P) x sk⁻¹
  left_inv x := by
    show zpowZMod₁ (P := P) (zpowZMod₁ (P := P) x sk) sk⁻¹ = x
    rw [zpowZMod₁_zpowZMod₁, zpow_mul_inv_cancel _ hsk, zpowZMod₁_one]
  right_inv x := by
    show zpowZMod₁ (P := P) (zpowZMod₁ (P := P) x sk⁻¹) sk = x
    rw [zpowZMod₁_zpowZMod₁]
    have : sk⁻¹ * sk = 1 := by rw [mul_comm]; exact zpow_mul_inv_cancel _ hsk
    rw [this, zpowZMod₁_one]

@[simp]
theorem zpowZMod₁_right_equiv_apply (sk : ZMod P.p) (hsk : sk ≠ 0) (x : P.G₁) :
    zpowZMod₁_right_equiv (P := P) sk hsk x = zpowZMod₁ (P := P) x sk := rfl

/-! ## SRS (Structured Reference String) -/

/-- The Structured Reference String for KZG: `[g₁, g₁^α, g₁^(α²), ..., g₁^(αᵗ)]` -/
noncomputable def srs₁ (α : ZMod P.p) (t : ℕ) : Fin (t + 1) → P.G₁ :=
  fun i => P.g₁ ^ᵍ (α ^ i.val)

/-- SRS in G₂: `[g₂, g₂^α]` (just two elements needed for verification) -/
noncomputable def srs₂ (α : ZMod P.p) : P.G₂ × P.G₂ :=
  (P.g₂, P.g₂ ^ʰ α)

end PairingGroup

end CatCrypt.Crypto

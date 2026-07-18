/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Relational.Rules

/-!
# XOR Bijection Library

This file provides reusable XOR bijection infrastructure for cryptographic proofs.

## Overview

Many CatCrypt proofs rely on the fact that XOR with a fixed value is a bijection.
This file centralizes the definition and key theorems, eliminating duplication
across 20+ example files.

## Main definitions

* `xorEquiv` - General XOR bijection for any type with an involutive XOR operation
* `boolXorBij` - XOR bijection on `Bool` (the most commonly used specialization)

## Main results

* `rHoare_sample_xor` - Sampling a key and applying XOR has the same distribution
  as sampling directly (coupling lemma)
* `advantage_zero_of_xor` - Zero advantage corollary for XOR-based games

## References

* [Shannon, Communication Theory of Secrecy Systems, 1949]
-/

namespace CatCrypt.Prob.XorBij

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Crypto

/-! ## General XOR Equivalence -/

/-- XOR with a fixed value is an equivalence for any involutive binary operation.

    Given an operation `op` satisfying `op (op a b) b = a` for all `a b`,
    `xorEquiv op h x` is the equivalence `a ↦ op a x` with inverse `r ↦ op r x`. -/
def xorEquiv {α : Type} (op : α → α → α)
    (hInvol : ∀ a b, op (op a b) b = a) (x : α) : α ≃ α where
  toFun k := op k x
  invFun r := op r x
  left_inv k := hInvol k x
  right_inv r := hInvol r x

/-! ## Bool XOR Bijection -/

/-- XOR with a fixed `Bool` is a bijection.

    This is the fundamental property used in OTP, PRF, MAC, PRG, and many other
    cryptographic proofs; it is shared here rather than duplicated per file. -/
def boolXorBij (x : Bool) : Bool ≃ Bool where
  toFun k := xor k x
  invFun r := xor r x
  left_inv k := by cases k <;> cases x <;> rfl
  right_inv r := by cases r <;> cases x <;> rfl

@[simp]
theorem boolXorBij_apply (x k : Bool) : boolXorBij x k = xor k x := rfl

@[simp]
theorem boolXorBij_symm (x : Bool) : (boolXorBij x).symm = boolXorBij x := by
  ext r; cases r <;> cases x <;> rfl

/-! ## Product XOR Bijection -/

/-- XOR bijection on `Bool × Bool` (component-wise).

    Used in PRPCCA for ciphertext-space bijections. -/
def prodBoolXorBij (c : Bool × Bool) : (Bool × Bool) ≃ (Bool × Bool) where
  toFun k := (xor k.1 c.1, xor k.2 c.2)
  invFun r := (xor r.1 c.1, xor r.2 c.2)
  left_inv k := by simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  right_inv r := by simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

@[simp]
theorem prodBoolXorBij_apply (c k : Bool × Bool) :
    prodBoolXorBij c k = (xor k.1 c.1, xor k.2 c.2) := rfl

/-! ## Coupling Lemma

The key theorem: sampling a key uniformly and applying XOR with a fixed message
is indistinguishable from sampling uniformly.

This eliminates the ~15-line coupling proof pattern repeated across ~10 files. -/

/-- Core coupling: for any bijection family, sampling a key and applying the
    bijection is coupled with uniform sampling via `eqPost`.

    This is the general pattern:
    - Real: `k ← sample α; pure (f k)`
    - Ideal: `sample α`
    - Coupled via bijection `f : α ≃ α` -/
theorem rHoare_sample_bij {α : Type} [Fintype α] [Nonempty α]
    (f : α ≃ α) :
    rHoare eqPre
      (do let k ← SPComp.sample α; SPComp.pure (f k))
      (SPComp.sample α) eqPost := by
  intro h₁ h₂ hheq
  simp only [eqPre] at hheq
  subst hheq
  simp only [SPComp.monad_bind_eq]
  rw [SPComp.sample_bind_pure, SPComp.sample_bind_pure_id]
  have hCoupling := liftR_uniform_bij f
  apply liftR_bind hCoupling
  intro k r hkr
  apply liftR_pure
  grind

/-- Coupling for Bool XOR: sampling a key and XORing with a message has the same
    distribution as sampling directly.

    **Real game**: `k ← sample Bool; pure (xor k m)`
    **Ideal game**: `sample Bool`

    This is the single most commonly needed coupling in CatCrypt examples. -/
theorem rHoare_sample_xor (m : Bool) :
    rHoare eqPre
      (do let k ← SPComp.sample Bool; SPComp.pure (xor k m))
      (SPComp.sample Bool) eqPost :=
  rHoare_sample_bij (boolXorBij m)

/-- Coupling for product Bool XOR. -/
theorem rHoare_sample_prod_xor (c : Bool × Bool) :
    rHoare eqPre
      (do let k ← SPComp.sample (Bool × Bool); SPComp.pure (xor k.1 c.1, xor k.2 c.2))
      (SPComp.sample (Bool × Bool)) eqPost :=
  rHoare_sample_bij (prodBoolXorBij c)

/-! ## Zero Advantage Corollaries -/

/-- If real game is `sample key >> apply bijection` and ideal game is `sample`,
    then every adversary has zero advantage. -/
theorem advantage_zero_of_bij {α : Type} [Fintype α] [Nonempty α]
    (f : α ≃ α) (A : α → SPComp Bool) :
    AdvantageA (do let k ← SPComp.sample α; SPComp.pure (f k))
               (SPComp.sample α) A = 0 :=
  advantage_zero_of_rHoare _ _ (rHoare_sample_bij f) A

/-- Zero advantage for Bool XOR games. -/
theorem advantage_zero_of_xor (m : Bool) (A : Bool → SPComp Bool) :
    AdvantageA (do let k ← SPComp.sample Bool; SPComp.pure (xor k m))
               (SPComp.sample Bool) A = 0 :=
  advantage_zero_of_bij (boolXorBij m) A

/-! ## XOR Algebraic Helpers -/

/-- XOR is self-inverse: `xor (xor a b) b = a` -/
theorem xor_self_inverse (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

/-- XOR with false is identity -/
@[simp] theorem xor_false_right (b : Bool) : xor b false = b := by cases b <;> rfl

/-- XOR with true is negation -/
@[simp] theorem xor_true_right (b : Bool) : xor b true = !b := by cases b <;> rfl

end CatCrypt.Prob.XorBij

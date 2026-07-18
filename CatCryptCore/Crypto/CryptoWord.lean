/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Prob.XorBij

/-!
# CryptoWord Typeclass

Abstract interface for word types used in cryptographic constructions.

## Overview

Currently `Word = Bool` is hardcoded in `PRFPRG.lean`. This typeclass provides
an abstract interface so new constructions (like CBC mode) can be written
generically while existing Bool-specific proofs remain untouched.

## Main definitions

* `SampleableType` — base typeclass: `Fintype + Nonempty + DecidableEq + Inhabited`
* `CryptoWord` — extends `SampleableType` with involutive XOR (`wxor`)
* `wxorEquiv` — bijection from `wxor_cancel`
* `rHoare_sample_wxor` — coupling lemma for wxor

## Main results

* `advantage_zero_of_wxor` — zero advantage for wxor-based games
* `SampleableType Bool` / `CryptoWord Bool` instances
* `SampleableType (BitVec n)` / `CryptoWord (BitVec n)` instances
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Prob.XorBij

/-! ## Typeclass Hierarchy -/

/-- Base class for types that can be uniformly sampled in CatCrypt games.
    Requires `Fintype` (for uniform distribution), `Nonempty` (distribution is
    well-defined), `DecidableEq` (for equality checks in games), and `Inhabited`
    (for default values in extraction bridges). -/
class SampleableType (W : Type) where
  [fintype : Fintype W]
  [nonempty : Nonempty W]
  [deceq : DecidableEq W]
  [inhabited : Inhabited W]

attribute [instance] SampleableType.fintype SampleableType.nonempty
  SampleableType.deceq SampleableType.inhabited

/-- Abstract word type for cryptographic constructions.
    Extends `SampleableType` with an involutive XOR operation, needed for
    one-time-pad style proofs (symmetric ratchet, PSK injection, etc.). -/
class CryptoWord (W : Type) extends SampleableType W where
  /-- The XOR-like operation -/
  wxor : W → W → W
  /-- wxor is involutive: `wxor (wxor a b) b = a` -/
  wxor_cancel : ∀ a b, wxor (wxor a b) b = a
  /-- wxor is commutative -/
  wxor_comm : ∀ a b, wxor a b = wxor b a

/-! ## Bool Instances -/

instance : SampleableType Bool where

instance : CryptoWord Bool where
  wxor := xor
  wxor_cancel a b := by cases a <;> cases b <;> rfl
  wxor_comm a b := by cases a <;> cases b <;> rfl

/-- For Bool, wxor is definitionally xor. -/
theorem boolCryptoWord_wxor_eq_xor : (CryptoWord.wxor : Bool → Bool → Bool) = xor := rfl

/-! ## BitVec Instance -/

/-- `Fintype` instance for `BitVec n` via the bijection with `Fin (2^n)`.
Marked `@[irreducible]` to prevent kernel reduction of `2^n` for large `n`
(e.g., `BitVec 256`). The instance is still found by typeclass search. -/
@[irreducible]
noncomputable instance instFintypeBitVec (n : Nat) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2^n)) {
    toFun := BitVec.ofFin
    invFun := BitVec.toFin
    left_inv := fun i => by ext; simp
    right_inv := fun bv => by ext; simp
  }

/-- `BitVec n` is sampleable (finite, nonempty, decidable equality, inhabited). -/
@[irreducible]
noncomputable instance instSampleableTypeBitVec (n : Nat) : SampleableType (BitVec n) where
  fintype := instFintypeBitVec n

/-- `BitVec n` forms a `CryptoWord` with `wxor = XOR`.
    This enables all CatCrypt security proofs to work at any bit width,
    including the concrete `BitVec 256` level matching P-256 / SHA-256.
    Marked `@[irreducible]` to prevent kernel reduction for large `n`. -/
@[irreducible]
noncomputable instance instCryptoWordBitVec (n : Nat) : CryptoWord (BitVec n) where
  toSampleableType := instSampleableTypeBitVec n
  wxor a b := a ^^^ b
  wxor_cancel a b := by simp [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  wxor_comm a b := by simp [BitVec.xor_comm]

/-! ## Derived Properties -/

variable {W : Type} [CryptoWord W]

/-- Left cancellation: `wxor a (wxor a b) = b`.
    Follows from `wxor_cancel` and `wxor_comm`. -/
theorem CryptoWord.wxor_left_cancel (a b : W) :
    CryptoWord.wxor a (CryptoWord.wxor a b) = b := by
  rw [CryptoWord.wxor_comm a (CryptoWord.wxor a b)]
  rw [CryptoWord.wxor_comm a b]
  exact CryptoWord.wxor_cancel b a

/-! ## XOR Equivalence (Bijection) -/

/-- wxor with a fixed value is an equivalence (bijection).
    This is the CryptoWord analogue of `boolXorBij` from `XorBij.lean`. -/
def wxorEquiv (x : W) : W ≃ W where
  toFun k := CryptoWord.wxor k x
  invFun r := CryptoWord.wxor r x
  left_inv k := CryptoWord.wxor_cancel k x
  right_inv r := CryptoWord.wxor_cancel r x

@[simp]
theorem wxorEquiv_apply (x k : W) : wxorEquiv x k = CryptoWord.wxor k x := rfl

/-! ## Coupling Lemma -/

/-- Sampling a key and applying wxor has the same distribution as sampling directly.
    CryptoWord analogue of `rHoare_sample_xor`. -/
theorem rHoare_sample_wxor (m : W) :
    rHoare eqPre
      (do let k ← SPComp.sample W; SPComp.pure (CryptoWord.wxor k m))
      (SPComp.sample W) eqPost :=
  rHoare_sample_bij (wxorEquiv m)

/-! ## Zero Advantage -/

/-- Zero advantage for wxor-based games.
    CryptoWord analogue of `advantage_zero_of_xor`. -/
theorem advantage_zero_of_wxor (m : W) (A : W → SPComp Bool) :
    AdvantageA (do let k ← SPComp.sample W; SPComp.pure (CryptoWord.wxor k m))
               (SPComp.sample W) A = 0 :=
  advantage_zero_of_bij (wxorEquiv m) A

end CatCrypt.Crypto

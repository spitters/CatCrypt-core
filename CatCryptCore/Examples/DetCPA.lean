/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.ForkingLemma

/-!
# Deterministic CPA Impossibility

This file formalizes the impossibility of CPA-secure deterministic encryption
from Chapter 7.1 of "The Joy of Cryptography".

## Overview

Any deterministic encryption scheme can be broken by a simple adversary that
encrypts the same message twice and checks if the ciphertexts match. For the
XOR-based scheme `enc(k, m) = xor k m`, we show that the distinguishing
advantage is exactly 1.

No UC wrapper — this is an attack/insecurity result.

## References

* [Rosulek, The Joy of Cryptography, Section 7.1]
-/

namespace CatCryptCore.Examples.DetCPA

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto
open CatCrypt.Crypto.ForkingLemma

open scoped ENNReal

/-! ## Deterministic Encryption Scheme -/

/-- A deterministic encryption scheme: enc(key, msg) → ciphertext. -/
structure DetEncScheme where
  enc : Bool → Bool → Bool

/-- XOR-based deterministic encryption: enc(k, m) = xor k m. -/
def xorDet : DetEncScheme := ⟨xor⟩

/-! ## Two-Encryption Game -/

/-- Game: encrypt two messages under the same random key, return ciphertext pair. -/
noncomputable def det_enc_pair (E : DetEncScheme) (m₁ m₂ : Bool) :
    SPComp (Bool × Bool) := do
  let k ← SPComp.sample Bool
  SPComp.pure (E.enc k m₁, E.enc k m₂)

/-- Equality-checking adversary: returns true iff both ciphertexts are equal. -/
noncomputable def eq_adversary : (Bool × Bool) → SPComp Bool :=
  fun (c₁, c₂) => SPComp.pure (c₁ == c₂)

/-! ## Insecurity Proof -/

/-- For the XOR scheme encrypting the same message twice:
    the adversary always returns true (advantage 1 side). -/
private theorem same_msg_prTrue (m : Bool) :
    prTrue ((det_enc_pair xorDet m m).bind eq_adversary) Heap.empty = 1 := by
  unfold det_enc_pair eq_adversary xorDet
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [prTrue_bind_sample_Bool]
  -- xor k m == xor k m = true for all k
  simp only [show (xor false m == xor false m) = true from by cases m <;> rfl,
             show (xor true m == xor true m) = true from by cases m <;> rfl,
             prTrue_pure_bool, ite_true, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- For the XOR scheme encrypting different messages:
    the adversary always returns false (advantage 0 side). -/
private theorem diff_msg_prTrue (m : Bool) :
    prTrue ((det_enc_pair xorDet m (!m)).bind eq_adversary) Heap.empty = 0 := by
  unfold det_enc_pair eq_adversary xorDet
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [prTrue_bind_sample_Bool]
  -- xor k m == xor k (!m) = false for all k
  simp only [show (xor false m == xor false (!m)) = false from by cases m <;> rfl,
             show (xor true m == xor true (!m)) = false from by cases m <;> rfl,
             prTrue_pure_bool]
  simp

/-- **Main theorem**: XOR deterministic encryption is completely insecure.

    The equality-checking adversary achieves advantage 1 when distinguishing
    same-message encryption from different-message encryption. -/
theorem det_enc_xor_insecure (m : Bool) :
    AdvantageA (det_enc_pair xorDet m m) (det_enc_pair xorDet m (!m)) eq_adversary = 1 := by
  unfold AdvantageA Advantage
  rw [same_msg_prTrue, diff_msg_prTrue]
  simp

end CatCryptCore.Examples.DetCPA

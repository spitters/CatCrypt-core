/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code

/-!
# Encryption Scheme Definition

This file defines the structure of symmetric encryption schemes for use
in cryptographic security proofs.

## Main definitions

* `EncScheme` - A symmetric encryption scheme with key generation, encryption, and decryption
* `EncScheme.Correct` - Correctness property: decryption inverts encryption
* `EncScheme.IsDeterministic` - Predicate for deterministic encryption
* `ProbEncScheme` - Probabilistic encryption with explicit randomness
* `DetEncScheme` - Deterministic encryption scheme

## References

* [Bellare & Rogaway, Introduction to Modern Cryptography]
* [Katz & Lindell, Introduction to Modern Cryptography]
-/

namespace CatCrypt.Crypto

open CatCrypt.Core

/-- A symmetric encryption scheme.

An encryption scheme consists of:
- Key, Plaintext, and Ciphertext types
- A probabilistic key generation algorithm
- A probabilistic encryption algorithm
- A probabilistic decryption algorithm

The type requirements (Fintype, Nonempty) are needed for:
- Key: uniform sampling in key generation
- Ciphertext: supporting one-time pad style encryption where
  ciphertexts are sampled/XORed with keys

Note: Decryption returns `Option Plaintext` to handle decryption failures
(e.g., authenticated encryption modes). -/
structure EncScheme where
  /-- Key type -/
  Key : Type
  /-- Plaintext type -/
  Plaintext : Type
  /-- Ciphertext type -/
  Ciphertext : Type
  /-- Keys form a finite type (for uniform sampling) -/
  [finKey : Fintype Key]
  /-- Keys are nonempty (for uniform sampling) -/
  [neKey : Nonempty Key]
  /-- Ciphertexts form a finite type (for OTP-style constructions) -/
  [finCt : Fintype Ciphertext]
  /-- Ciphertexts are nonempty (for OTP-style constructions) -/
  [neCt : Nonempty Ciphertext]
  /-- Probabilistic key generation -/
  keyGen : SPComp Key
  /-- Probabilistic encryption -/
  encrypt : Key → Plaintext → SPComp Ciphertext
  /-- Probabilistic decryption (may fail) -/
  decrypt : Key → Ciphertext → SPComp (Option Plaintext)

attribute [instance] EncScheme.finKey EncScheme.neKey EncScheme.finCt EncScheme.neCt

namespace EncScheme

variable (E : EncScheme)

/-! ## Correctness Property -/

/-- Correctness: decryption of encryption returns the original message.

For a deterministic scheme, this means:
  ∀ k m, decrypt k (encrypt k m) = some m

For probabilistic schemes, we require that for any randomness used in encryption,
decryption recovers the original message. We express this using support membership.

Note: This requires that for all ciphertexts c in the support of encrypt k m,
decryption returns some m. -/
def Correct : Prop :=
  ∀ (k : E.Key) (m : E.Plaintext) (h : Heap),
    ∀ c h', (c, h') ∈ (E.encrypt k m h).support →
      ∀ result h'', (result, h'') ∈ (E.decrypt k c h').support →
        result = some m

/-- Strong correctness: decryption always succeeds and returns original message.
    This is expressed as equality of distributions after bind. -/
def StrongCorrect : Prop :=
  ∀ (k : E.Key) (m : E.Plaintext) (h : Heap),
    (E.encrypt k m h).bind (fun (c, h') => E.decrypt k c h') =
    (E.encrypt k m h).bind (fun (_, h') => CatCrypt.Prob.SDistr.pure (some m, h'))

/-! ## Determinism -/

/-- Deterministic encryption: encrypt is a pure function of key and message.
    The encryption produces a single deterministic ciphertext. -/
def IsDeterministic : Prop :=
  ∃ f : E.Key → E.Plaintext → E.Ciphertext,
    ∀ k m, E.encrypt k m = SPComp.pure (f k m)

/-- Deterministic decryption: decrypt is a pure function of key and ciphertext. -/
def HasDeterministicDecrypt : Prop :=
  ∃ f : E.Key → E.Ciphertext → Option E.Plaintext,
    ∀ k c, E.decrypt k c = SPComp.pure (f k c)

/-- A fully deterministic scheme has both deterministic encryption and decryption. -/
def IsFullyDeterministic : Prop :=
  E.IsDeterministic ∧ E.HasDeterministicDecrypt

/-! ## Simple Correctness for Deterministic Schemes -/

/-- Simple correctness condition for schemes with deterministic encrypt/decrypt.
    This is easier to prove and implies the general Correct property. -/
def SimpleCorrect (encryptF : E.Key → E.Plaintext → E.Ciphertext)
    (decryptF : E.Key → E.Ciphertext → Option E.Plaintext) : Prop :=
  ∀ k m, decryptF k (encryptF k m) = some m

/-- If a scheme has deterministic encrypt/decrypt satisfying SimpleCorrect,
    then it satisfies the general Correct property. -/
theorem correct_of_simple_correct
    (encryptF : E.Key → E.Plaintext → E.Ciphertext)
    (decryptF : E.Key → E.Ciphertext → Option E.Plaintext)
    (hEnc : ∀ k m, E.encrypt k m = SPComp.pure (encryptF k m))
    (hDec : ∀ k c, E.decrypt k c = SPComp.pure (decryptF k c))
    (hSimple : SimpleCorrect E encryptF decryptF) : E.Correct := by
  intro k m h c h' hc result h'' hresult
  -- Encrypt is pure, so support is a singleton
  rw [hEnc] at hc
  simp only [SPComp.pure] at hc
  -- hc : (c, h') ∈ (SDistr.pure (encryptF k m, h)).support
  -- Use mem_support_iff: x ∈ d.support ↔ d (some x) ≠ 0
  rw [CatCrypt.Prob.SDistr.mem_support_iff] at hc
  -- For pure a, (pure a)(some x) ≠ 0 iff x = a
  simp only [CatCrypt.Prob.SDistr.pure, PMF.pure_apply, ne_eq] at hc
  -- hc : (if (encryptF k m, h) = (c, h') then 1 else 0) ≠ 0
  by_cases heq : (encryptF k m, h) = (c, h')
  · -- If equal, extract components using Prod.mk.injEq
    rw [Prod.mk.injEq] at heq
    obtain ⟨hceq, hh'eq⟩ := heq
    subst hceq hh'eq
    -- Now handle decryption
    rw [hDec] at hresult
    simp only [SPComp.pure] at hresult
    rw [CatCrypt.Prob.SDistr.mem_support_iff] at hresult
    simp only [CatCrypt.Prob.SDistr.pure, PMF.pure_apply, ne_eq] at hresult
    by_cases heq2 : (decryptF k (encryptF k m), h) = (result, h'')
    · rw [Prod.mk.injEq] at heq2
      obtain ⟨hreq, _⟩ := heq2
      rw [← hreq, hSimple]
    · -- The condition in the if is (decryptF k (encryptF k m), h) = (result, h'')
      -- We need to use the fact that the condition is false to simplify
      have hcond : ¬((some (result, h'')) = (some (decryptF k (encryptF k m), h))) :=
        fun h => heq2 (Option.some.inj h).symm
      rw [if_neg hcond] at hresult
      exact absurd rfl hresult
  · -- If not equal, probability is 0, contradiction
    have hcond : ¬((some (c, h')) = (some (encryptF k m, h))) :=
      fun h => heq (Option.some.inj h).symm
    rw [if_neg hcond] at hc
    exact absurd rfl hc

end EncScheme

/-! ## Deterministic Encryption Scheme -/

/-- A deterministic encryption scheme where encryption and decryption are pure functions.
    This is a special case useful for schemes like OTP, block ciphers, etc. -/
structure DetEncScheme where
  /-- Key type -/
  Key : Type
  /-- Plaintext type -/
  Plaintext : Type
  /-- Ciphertext type -/
  Ciphertext : Type
  /-- Keys form a finite type (for uniform sampling) -/
  [finKey : Fintype Key]
  /-- Keys are nonempty (for uniform sampling) -/
  [neKey : Nonempty Key]
  /-- Ciphertexts form a finite type -/
  [finCt : Fintype Ciphertext]
  /-- Ciphertexts are nonempty -/
  [neCt : Nonempty Ciphertext]
  /-- Deterministic encryption function -/
  encryptF : Key → Plaintext → Ciphertext
  /-- Deterministic decryption function -/
  decryptF : Key → Ciphertext → Option Plaintext

attribute [instance] DetEncScheme.finKey DetEncScheme.neKey DetEncScheme.finCt DetEncScheme.neCt

namespace DetEncScheme

variable (D : DetEncScheme)

/-- Convert a deterministic scheme to a general encryption scheme. -/
noncomputable def toEncScheme : EncScheme where
  Key := D.Key
  Plaintext := D.Plaintext
  Ciphertext := D.Ciphertext
  finKey := D.finKey
  neKey := D.neKey
  finCt := D.finCt
  neCt := D.neCt
  keyGen := SPComp.sample D.Key
  encrypt := fun k m => SPComp.pure (D.encryptF k m)
  decrypt := fun k c => SPComp.pure (D.decryptF k c)

/-- Correctness for deterministic schemes: decrypt inverts encrypt. -/
def Correct : Prop :=
  ∀ k m, D.decryptF k (D.encryptF k m) = some m

/-- Encryption is injective in the message for each key. -/
def EncryptInjective : Prop :=
  ∀ k m₁ m₂, D.encryptF k m₁ = D.encryptF k m₂ → m₁ = m₂

/-- Correctness implies encryption is injective. -/
theorem encrypt_injective_of_correct (hCorr : D.Correct) : D.EncryptInjective := by
  intro k m₁ m₂ henc
  have h1 := hCorr k m₁
  have h2 := hCorr k m₂
  rw [henc] at h1
  rw [h1] at h2
  injection h2

/-- A correct deterministic scheme gives a correct general scheme. -/
theorem toEncScheme_correct (hCorr : D.Correct) : D.toEncScheme.Correct := by
  apply EncScheme.correct_of_simple_correct
  · intro k m; rfl
  · intro k c; rfl
  · exact hCorr

end DetEncScheme

/-! ## Probabilistic Encryption Scheme with Explicit Randomness -/

/-- A probabilistic encryption scheme with explicit randomness.
    This models schemes like ElGamal, RSA-OAEP, etc. where encryption
    uses random coins that can be made explicit. -/
structure ProbEncScheme extends EncScheme where
  /-- Randomness type used in encryption -/
  Randomness : Type
  /-- Randomness is finite (for uniform sampling) -/
  [finRand : Fintype Randomness]
  /-- Randomness is nonempty -/
  [neRand : Nonempty Randomness]
  /-- Deterministic encryption with explicit randomness -/
  encryptR : Key → toEncScheme.Plaintext → Randomness → toEncScheme.Ciphertext
  /-- Probabilistic encryption samples randomness and applies encryptR -/
  encrypt_eq : ∀ k m, toEncScheme.encrypt k m = do
    let r ← SPComp.sample Randomness
    SPComp.pure (encryptR k m r)

attribute [instance] ProbEncScheme.finRand ProbEncScheme.neRand

namespace ProbEncScheme

variable (P : ProbEncScheme)

/-- Correctness for probabilistic schemes: for all randomness, decrypt recovers message.
    This uses the base scheme's Correct property specialized to the encrypted ciphertext. -/
def Correct : Prop :=
  P.toEncScheme.Correct

/-- Simple correctness when decryption is also deterministic. -/
def SimpleCorrect (decryptF : P.Key → P.toEncScheme.Ciphertext → Option P.toEncScheme.Plaintext) : Prop :=
  ∀ k m r, decryptF k (P.encryptR k m r) = some m

end ProbEncScheme

/-! ## Basic Lemmas -/

namespace EncScheme

/-- A deterministic scheme is IsDeterministic. -/
theorem det_scheme_is_deterministic (D : DetEncScheme) :
    D.toEncScheme.IsDeterministic :=
  ⟨D.encryptF, fun _ _ => rfl⟩

/-- A deterministic scheme has deterministic decryption. -/
theorem det_scheme_has_det_decrypt (D : DetEncScheme) :
    D.toEncScheme.HasDeterministicDecrypt :=
  ⟨D.decryptF, fun _ _ => rfl⟩

/-- A deterministic scheme is fully deterministic. -/
theorem det_scheme_is_fully_deterministic (D : DetEncScheme) :
    D.toEncScheme.IsFullyDeterministic :=
  ⟨det_scheme_is_deterministic D, det_scheme_has_det_decrypt D⟩

end EncScheme

end CatCrypt.Crypto

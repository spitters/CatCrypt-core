/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.Encryption

/-!
# Standard Security Definitions

This file provides abstract security definitions for the most common
cryptographic security notions. These serve as a reference catalog and
provide reusable building blocks for security proofs.

## Main definitions

### Indistinguishability
* `INDCPA_Game` — IND-CPA (Indistinguishability under Chosen Plaintext Attack)
* `INDCCA_Game` — IND-CCA (Indistinguishability under Chosen Ciphertext Attack)

### Pseudorandomness
* `PRFScheme` — Pseudorandom function family
* `PRF_Game` — PRF indistinguishability game

### Authentication
* `MACScheme` — Message authentication code
* `EUF_CMA_Game` — Existential Unforgeability under Chosen Message Attack

## Concrete instantiations

These abstract definitions are instantiated in the example files:
* `CatCrypt.Examples.INDCPA` — IND-CPA for `EncScheme`
* `CatCrypt.Examples.INDCCA` — IND-CCA for `EncScheme`
* `CatCrypt.Examples.PRF` — PRF security for Bool-based PRF
* `CatCrypt.Examples.MAC` — MAC security for Bool-based MAC
* `CatCrypt.Examples.Schnorr` — EUF-CMA for Schnorr signatures
* `CatCrypt.Examples.ElGamal` — IND-CPA for ElGamal PKE
* `CatCrypt.Examples.PKE.Scheme` — OT-CPA and MT-CPA for PKE

## References

* [Bellare & Rogaway, Introduction to Modern Cryptography]
* [Katz & Lindell, Introduction to Modern Cryptography, 3rd ed.]
* [Rosulek, The Joy of Cryptography]
-/

namespace CatCrypt.Crypto.SecurityDefs

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open scoped ENNReal

/-! ## IND-CPA: Indistinguishability under Chosen Plaintext Attack -/

/-- IND-CPA game for a symmetric encryption scheme.

    The adversary chooses two messages and receives an encryption of one.
    The game returns the ciphertext; the adversary tries to guess which
    message was encrypted.

    - `INDCPA_Game E m₀ m₁ true` — encrypts `m₀` (left/real)
    - `INDCPA_Game E m₀ m₁ false` — encrypts `m₁` (right/ideal) -/
noncomputable def INDCPA_Game (E : EncScheme) (m₀ m₁ : E.Plaintext) (b : Bool) :
    SPComp E.Ciphertext := do
  let k ← E.keyGen
  E.encrypt k (if b then m₀ else m₁)

/-- IND-CPA advantage: distinguishing probability between left and right. -/
noncomputable def INDCPA_Adv (E : EncScheme) (m₀ m₁ : E.Plaintext)
    (A : E.Ciphertext → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (INDCPA_Game E m₀ m₁ true) (INDCPA_Game E m₀ m₁ false) A

/-! ## PRF: Pseudorandom Function -/

/-- A pseudorandom function family. -/
structure PRFScheme where
  /-- Key type -/
  Key : Type
  /-- Input (domain) type -/
  Input : Type
  /-- Output (range) type -/
  Output : Type
  [finKey : Fintype Key]
  [neKey : Nonempty Key]
  [finOutput : Fintype Output]
  [neOutput : Nonempty Output]
  /-- The PRF evaluation function -/
  eval : Key → Input → Output

attribute [instance] PRFScheme.finKey PRFScheme.neKey PRFScheme.finOutput PRFScheme.neOutput

/-- PRF real game: evaluate PRF with random key. -/
noncomputable def PRF_Real (F : PRFScheme) (x : F.Input) : SPComp F.Output := do
  let k ← SPComp.sample F.Key
  SPComp.pure (F.eval k x)

/-- PRF ideal game: return a uniformly random value. -/
noncomputable def PRF_Ideal (F : PRFScheme) : SPComp F.Output :=
  SPComp.sample F.Output

/-- PRF advantage: distinguishing PRF output from random. -/
noncomputable def PRF_Adv (F : PRFScheme) (x : F.Input)
    (A : F.Output → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (PRF_Real F x) (PRF_Ideal F) A

/-! ## MAC: Message Authentication Code -/

/-- A message authentication code scheme. -/
structure MACScheme where
  /-- Key type -/
  Key : Type
  /-- Message type -/
  Message : Type
  /-- Tag type -/
  Tag : Type
  [finKey : Fintype Key]
  [neKey : Nonempty Key]
  [finTag : Fintype Tag]
  [neTag : Nonempty Tag]
  [decTag : DecidableEq Tag]
  /-- Tag generation -/
  mac : Key → Message → Tag
  /-- Verification (default: recompute and compare) -/
  verify : Key → Message → Tag → Bool :=
    fun k m t => t == mac k m

attribute [instance] MACScheme.finKey MACScheme.neKey MACScheme.finTag MACScheme.neTag
  MACScheme.decTag

/-- EUF-CMA real game (simplified, single-query):
    adversary receives a tag on message m and tries to forge on m*.

    Returns true if the adversary's forgery attempt verifies. -/
noncomputable def EUF_CMA_Real (M : MACScheme) (m : M.Message) (m_star : M.Message)
    (t_star : M.Tag) : SPComp Bool := do
  let k ← SPComp.sample M.Key
  let _t := M.mac k m  -- tag given to adversary
  SPComp.pure (M.verify k m_star t_star)

/-- EUF-CMA advantage: probability of successful forgery. -/
noncomputable def EUF_CMA_Adv (M : MACScheme) (m m_star : M.Message) (t_star : M.Tag)
    (A : Bool → SPComp Bool) : ℝ≥0∞ :=
  prTrue (EUF_CMA_Real M m m_star t_star >>= A) Heap.empty

/-! ## Advantage Bounds -/

/-- If a PRF is perfect (PRF output = random for all inputs), PRF advantage is 0. -/
theorem PRF_Adv_zero_of_rHoare (F : PRFScheme) (x : F.Input)
    (h : rHoare eqPre (PRF_Real F x) (PRF_Ideal F) eqPost) :
    ∀ A, PRF_Adv F x A = 0 :=
  advantage_zero_of_rHoare _ _ h

/-- If encryption is perfectly indistinguishable, IND-CPA advantage is 0. -/
theorem INDCPA_Adv_zero_of_rHoare (E : EncScheme) (m₀ m₁ : E.Plaintext)
    (h : rHoare eqPre (INDCPA_Game E m₀ m₁ true) (INDCPA_Game E m₀ m₁ false) eqPost) :
    ∀ A, INDCPA_Adv E m₀ m₁ A = 0 :=
  advantage_zero_of_rHoare _ _ h

end CatCrypt.Crypto.SecurityDefs

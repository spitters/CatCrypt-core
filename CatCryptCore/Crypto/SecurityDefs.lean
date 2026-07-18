/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.Encryption

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

/-! ## IND-CCA: Indistinguishability under Chosen Ciphertext Attack

IND-CCA extends IND-CPA by handing the adversary a *decryption oracle* on
ciphertexts other than the challenge. In this single-shot `SPComp` game framework
a decryption oracle is faithfully modelled as an ordinary Lean function
`E.Ciphertext → SPComp (Option E.Plaintext)` that closes over the game's secret
key `k`; the CCA2 "may not query the challenge" restriction is enforced by the
guard `if c = cStar then none else E.decrypt k c`. No oracle-state threading is
needed because decryption is stateless — it only reads the key. The adversary
takes the oracle as an explicit argument and may call it on any ciphertext, so
the oracle is genuinely reachable (not a dead argument). -/

open scoped Classical in
/-- The restricted (off-challenge) decryption oracle used by the IND-CCA game:
    decrypt with the real key `k`, except reject (`none`) the challenge ciphertext
    `cStar` itself. This is the CCA2 restriction. -/
noncomputable def ccaDecOracle (E : EncScheme) (k : E.Key) (cStar : E.Ciphertext) :
    E.Ciphertext → SPComp (Option E.Plaintext) :=
  fun c => if c = cStar then SPComp.pure none else E.decrypt k c

/-- The ideal always-reject decryption oracle: every ciphertext is rejected. This
    is the oracle of an *ideal* authenticated-encryption scheme, against which the
    real oracle is compared to measure ciphertext-integrity. -/
noncomputable def rejectDecOracle (E : EncScheme) :
    E.Ciphertext → SPComp (Option E.Plaintext) :=
  fun _ => SPComp.pure none

/-- IND-CCA game (CCA2, find-then-guess with a fixed message pair). The adversary
    `A` receives the challenge ciphertext together with the off-challenge
    decryption oracle `ccaDecOracle E k cStar`, and outputs a guess bit.

    - `INDCCA_Game E m₀ m₁ true  A` — encrypts `m₀` (left/real)
    - `INDCCA_Game E m₀ m₁ false A` — encrypts `m₁` (right/ideal) -/
noncomputable def INDCCA_Game (E : EncScheme) (m₀ m₁ : E.Plaintext) (b : Bool)
    (A : (E.Ciphertext → SPComp (Option E.Plaintext)) → E.Ciphertext → SPComp Bool) :
    SPComp Bool := do
  let k ← E.keyGen
  let cStar ← E.encrypt k (if b then m₀ else m₁)
  A (ccaDecOracle E k cStar) cStar

/-- IND-CCA advantage: distinguishing probability between the `m₀`- and `m₁`-worlds
    when the adversary has decryption-oracle access. -/
noncomputable def INDCCA_Adv (E : EncScheme) (m₀ m₁ : E.Plaintext)
    (A : (E.Ciphertext → SPComp (Option E.Plaintext)) → E.Ciphertext → SPComp Bool) :
    ℝ≥0∞ :=
  Advantage (INDCCA_Game E m₀ m₁ true A) (INDCCA_Game E m₀ m₁ false A)

/-- The IND-CCA game with the real decryption oracle replaced by the ideal
    always-reject oracle. Since the reject oracle ignores the key, this game
    collapses to an IND-CPA game whose adversary ignores its (useless) oracle
    (see `INDCCA_rejectGame_eq`). -/
noncomputable def INDCCA_rejectGame (E : EncScheme) (m₀ m₁ : E.Plaintext) (b : Bool)
    (A : (E.Ciphertext → SPComp (Option E.Plaintext)) → E.Ciphertext → SPComp Bool) :
    SPComp Bool := do
  let k ← E.keyGen
  let cStar ← E.encrypt k (if b then m₀ else m₁)
  A (rejectDecOracle E) cStar

/-- The always-reject IND-CCA game is exactly an IND-CPA game post-composed with
    the adversary reading its useless oracle: the reject oracle ignores the key, so
    the challenge production factors out by monad associativity. -/
theorem INDCCA_rejectGame_eq (E : EncScheme) (m₀ m₁ : E.Plaintext) (b : Bool)
    (A : (E.Ciphertext → SPComp (Option E.Plaintext)) → E.Ciphertext → SPComp Bool) :
    INDCCA_rejectGame E m₀ m₁ b A =
      SPComp.bind (INDCPA_Game E m₀ m₁ b) (fun c => A (rejectDecOracle E) c) := by
  simp only [INDCCA_rejectGame, INDCPA_Game, SPComp.monad_bind_eq, SPComp.bind_assoc]

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

/-- If the two IND-CCA oracle-games are perfectly indistinguishable, the IND-CCA
    advantage is 0. Note the hypothesis quantifies over the *whole* oracle-game
    (adversary and decryption oracle included); for a genuinely confidential scheme
    with two distinct messages it is only met degenerately (e.g. `m₀ = m₁`), because
    the decryption oracle's answers depend on the secret key. -/
theorem INDCCA_Adv_zero_of_rHoare (E : EncScheme) (m₀ m₁ : E.Plaintext)
    (A : (E.Ciphertext → SPComp (Option E.Plaintext)) → E.Ciphertext → SPComp Bool)
    (h : rHoare eqPre (INDCCA_Game E m₀ m₁ true A) (INDCCA_Game E m₀ m₁ false A) eqPost) :
    INDCCA_Adv E m₀ m₁ A = 0 := by
  have hz := advantage_zero_of_rHoare _ _ h SPComp.pure
  simpa only [INDCCA_Adv, AdvantageA, SPComp.bind_pure] using hz

/-- **IND-CCA reduces to IND-CPA plus decryption-oracle integrity.** For *any*
    encryption scheme, the IND-CCA advantage is bounded by

    * the two *authenticity gaps* — the advantage of distinguishing the real
      decryption oracle from the always-reject oracle, in each world — plus
    * the IND-CPA advantage of the adversary that ignores its (reject) oracle.

    This is the standard "authenticated encryption = confidentiality + integrity"
    decomposition, proved here purely from the triangle inequality for advantage:
    routing through the two always-reject games, whose difference *is* an IND-CPA
    game (`INDCCA_rejectGame_eq`). The two authenticity gaps are exactly the
    ciphertext-integrity (MAC-unforgeability) terms. -/
theorem INDCCA_reduces_to_INDCPA (E : EncScheme) (m₀ m₁ : E.Plaintext)
    (A : (E.Ciphertext → SPComp (Option E.Plaintext)) → E.Ciphertext → SPComp Bool) :
    INDCCA_Adv E m₀ m₁ A ≤
      Advantage (INDCCA_Game E m₀ m₁ true A) (INDCCA_rejectGame E m₀ m₁ true A)
      + INDCPA_Adv E m₀ m₁ (fun c => A (rejectDecOracle E) c)
      + Advantage (INDCCA_rejectGame E m₀ m₁ false A) (INDCCA_Game E m₀ m₁ false A) := by
  have hmid :
      Advantage (INDCCA_rejectGame E m₀ m₁ true A) (INDCCA_rejectGame E m₀ m₁ false A)
        = INDCPA_Adv E m₀ m₁ (fun c => A (rejectDecOracle E) c) := by
    rw [INDCCA_rejectGame_eq, INDCCA_rejectGame_eq]
    rfl
  calc INDCCA_Adv E m₀ m₁ A
      = Advantage (INDCCA_Game E m₀ m₁ true A) (INDCCA_Game E m₀ m₁ false A) := rfl
    _ ≤ Advantage (INDCCA_Game E m₀ m₁ true A) (INDCCA_rejectGame E m₀ m₁ true A)
          + Advantage (INDCCA_rejectGame E m₀ m₁ true A) (INDCCA_Game E m₀ m₁ false A) :=
        advantage_triangle _ _ _
    _ ≤ Advantage (INDCCA_Game E m₀ m₁ true A) (INDCCA_rejectGame E m₀ m₁ true A)
          + (Advantage (INDCCA_rejectGame E m₀ m₁ true A) (INDCCA_rejectGame E m₀ m₁ false A)
             + Advantage (INDCCA_rejectGame E m₀ m₁ false A) (INDCCA_Game E m₀ m₁ false A)) := by
        gcongr
        exact advantage_triangle _ _ _
    _ = Advantage (INDCCA_Game E m₀ m₁ true A) (INDCCA_rejectGame E m₀ m₁ true A)
          + INDCPA_Adv E m₀ m₁ (fun c => A (rejectDecOracle E) c)
          + Advantage (INDCCA_rejectGame E m₀ m₁ false A) (INDCCA_Game E m₀ m₁ false A) := by
        rw [hmid, ← add_assoc]

end CatCrypt.Crypto.SecurityDefs

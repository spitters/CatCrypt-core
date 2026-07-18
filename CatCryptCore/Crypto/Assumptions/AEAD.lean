/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.CryptoWord

/-!
# AEAD (Authenticated Encryption with Associated Data) Security

This file defines the IND-CCA2 security notion for AEAD schemes at the
abstract `Word := Bool` level.

## AEAD Games

The AEAD security game captures the difficulty of distinguishing:
- **Real**: encrypt returns real ciphertext
- **Ideal**: encrypt returns random ciphertext (of same length)

## Main definitions

* `AEADDef` — an AEAD scheme (encrypt + decrypt)
* `AEAD_Game_Real` / `AEAD_Game_Ideal` — real/ideal AEAD games
* `AEAD_Advantage` — advantage of an adversary in breaking AEAD

## Usage in EDHOC

EDHOC uses AES-CCM-16-64-128 for:
1. Encrypting message 3 (containing initiator's credential + MAC_3)
2. Encrypting message 4 (optional, containing EAD_4)
3. Message 2 uses XOR encryption (KEYSTREAM_2), not AEAD

Each AEAD operation contributes one `ε_aead` to the security bound.

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| Game structure | `AEAD_Game_Real`/`Ideal` | Boneh-Shoup Def. 9.1 (IND-CPA for SKE) |
| Advantage | `Advantage(Real, Ideal)` | `|Pr[W₀] - Pr[W₁]|` |
| Formulation | Indistinguishability (real vs random) | Equiv. to IND-CCA2 for nonce-based AEAD |

**Equivalent formalizations:**
- EasyCrypt: `AEAD` theory in various protocol formalizations
- CryptoVerif: `IND-CPA` / `INT-CTXT` macros (split formulation)

**Note:** `AEAD_Advantage` uses an IND-CPA formulation (real ciphertext vs random,
no decryption oracle). `AEAD_CCA_Advantage` adds a decryption oracle for full
IND-CCA2 security. The standard AEAD security combines IND-CPA + INT-CTXT;
the IND-CCA2 formulation captures both. Use `AEAD_CCA_Advantage` for protocols
where the adversary can submit chosen ciphertexts (multi-message, interactive).
`AEAD_CPA_le_CCA` shows that IND-CCA2 implies IND-CPA.

## References

* Rogaway, *Authenticated-Encryption with Associated-Data*, CCS 2002
* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §9.5
* RFC 9528 — EDHOC, Section 5.3-5.4
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## AEAD Definition -/

/-- Abstract AEAD scheme definition, parametric over `SampleableType W`.

- `encrypt key plaintext ad` → ciphertext
- `decrypt key ciphertext ad` → plaintext (or ⊥) -/
structure AEADDef (W : Type) [SampleableType W] where
  /-- AEAD encryption: (key, plaintext, associated_data) → ciphertext.
  Models `aes_ccm_encrypt_tag_8` in lakers' `Crypto` trait. -/
  encrypt : W → W → W → W
  /-- AEAD decryption: (key, ciphertext, associated_data) → plaintext.
  Models `aes_ccm_decrypt_tag_8` in lakers' `Crypto` trait.
  Returns the plaintext (abstract level doesn't model decryption failure). -/
  decrypt : W → W → W → W

/-! ## AEAD Games -/

/-- Type of AEAD adversary: receives a ciphertext and must distinguish
real encryption from random. -/
abbrev AEAD_Adversary (W : Type) := W → SPComp Bool

/-- AEAD real game: sample random key, encrypt the adversary's chosen plaintext. -/
noncomputable def AEAD_Game_Real (D : AEADDef W) (pt ad : W)
    (A : AEAD_Adversary W) : SPComp Bool := do
  let key ← SPComp.sample W
  let ct := D.encrypt key pt ad
  A ct

/-- AEAD ideal game: adversary receives a random ciphertext. -/
noncomputable def AEAD_Game_Ideal (A : AEAD_Adversary W) : SPComp Bool := do
  let ct ← SPComp.sample W
  A ct

/-- AEAD advantage: ability to distinguish real encryption from random. -/
noncomputable def AEAD_Advantage (D : AEADDef W) (pt ad : W)
    (A : AEAD_Adversary W) : ℝ≥0∞ :=
  Advantage (AEAD_Game_Real D pt ad A) (AEAD_Game_Ideal A)

/-! ## IsPure Proofs -/

theorem AEAD_Game_Real_isPure (D : AEADDef W) (pt ad : W)
    (A : AEAD_Adversary W) (hA : ∀ x, SPComp.IsPure (A x)) :
    SPComp.IsPure (AEAD_Game_Real D pt ad A) := by
  unfold AEAD_Game_Real
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro key
  exact hA _

theorem AEAD_Game_Ideal_isPure (A : AEAD_Adversary W)
    (hA : ∀ x, SPComp.IsPure (A x)) :
    SPComp.IsPure (AEAD_Game_Ideal A) := by
  unfold AEAD_Game_Ideal
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro ct
  exact hA ct

/-! ## IND-CCA2 AEAD Games (with decryption oracle)

Standard AEAD security requires both confidentiality (IND-CPA) and
integrity (INT-CTXT). The IND-CCA2 formulation gives the adversary
access to both encryption and decryption oracles, combining both
properties into a single game.

### References

- Rogaway, *Authenticated-Encryption with Associated-Data*, CCS 2002
- Bellare & Namprempre, *Authenticated Encryption: Relations among Notions
  and Analysis of the Generic Composition Paradigm*, ASIACRYPT 2000
-/

/-- IND-CCA2 AEAD adversary: receives encryption and decryption oracles. -/
structure AEAD_CCA_Adversary (W : Type) where
  /-- The adversary's computation, given:
      - An encryption oracle: (plaintext, ad) → ciphertext
      - A decryption oracle: (ciphertext, ad) → plaintext option
      Returns a distinguishing bit. -/
  run : (W → W → SPComp W) → (W → W → SPComp (Option W)) → SPComp Bool

/-- IND-CCA2 real game: adversary gets real encryption and real decryption. -/
noncomputable def AEAD_CCA_Game_Real (D : AEADDef W)
    (A : AEAD_CCA_Adversary W) : SPComp Bool := do
  let key ← SPComp.sample W
  let enc_oracle : W → W → SPComp W := fun pt ad =>
    SPComp.pure (D.encrypt key pt ad)
  let dec_oracle : W → W → SPComp (Option W) := fun ct ad =>
    SPComp.pure (some (D.decrypt key ct ad))
  A.run enc_oracle dec_oracle

/-- IND-CCA2 ideal game: encryption returns random, decryption always rejects. -/
noncomputable def AEAD_CCA_Game_Ideal
    (A : AEAD_CCA_Adversary W) : SPComp Bool := do
  let _key ← SPComp.sample W
  let enc_oracle : W → W → SPComp W := fun _pt _ad =>
    SPComp.sample W
  let dec_oracle : W → W → SPComp (Option W) := fun _ct _ad =>
    SPComp.pure none
  A.run enc_oracle dec_oracle

/-- IND-CCA2 AEAD advantage: ability to distinguish real enc+dec from
    random enc + reject-all dec. -/
noncomputable def AEAD_CCA_Advantage (D : AEADDef W)
    (A : AEAD_CCA_Adversary W) : ℝ≥0∞ :=
  Advantage (AEAD_CCA_Game_Real D A) (AEAD_CCA_Game_Ideal A)

/-- IND-CCA2 implies IND-CPA: any IND-CPA adversary can be lifted to
    an IND-CCA2 adversary that ignores the decryption oracle. -/
noncomputable def AEAD_CPA_to_CCA (pt ad : W) (A : AEAD_Adversary W) :
    AEAD_CCA_Adversary W where
  run enc_oracle _dec_oracle := do
    let ct ← enc_oracle pt ad
    A ct

/-- Sampling and discarding the result does not change a computation.
    `SPComp.sample` has total mass 1, so `bind (sample W) (fun _ => M) = M`. -/
private theorem sample_bind_const (M : SPComp Bool) :
    SPComp.bind (SPComp.sample W) (fun _ => M) = M := by
  funext h
  simp only [SPComp.bind_def, SPComp.sample]
  rw [SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  -- Goal: SDistr.bind (SDistr.uniform W) (fun _ => M h) = M h
  unfold SDistr.bind SDistr.fail SDistr.uniform
  rw [PMF.bind_map]
  exact PMF.bind_const _ _

theorem AEAD_CPA_le_CCA (D : AEADDef W) (pt ad : W)
    (A : AEAD_Adversary W) :
    AEAD_Advantage D pt ad A ≤
    AEAD_CCA_Advantage D (AEAD_CPA_to_CCA pt ad A) := by
  unfold AEAD_Advantage AEAD_CCA_Advantage Advantage
  unfold AEAD_Game_Real AEAD_Game_Ideal
  unfold AEAD_CCA_Game_Real AEAD_CCA_Game_Ideal AEAD_CPA_to_CCA
  simp only [SPComp.monad_bind_eq, SPComp.pure_bind, sample_bind_const]
  exact le_refl _

/-! ## IsPure Proofs (CCA) -/

theorem AEAD_CCA_Game_Real_isPure (D : AEADDef W)
    (A : AEAD_CCA_Adversary W)
    (hA : ∀ (enc : W → W → SPComp W) (dec : W → W → SPComp (Option W)),
      (∀ x y, SPComp.IsPure (enc x y)) →
      (∀ x y, SPComp.IsPure (dec x y)) →
      SPComp.IsPure (A.run enc dec)) :
    SPComp.IsPure (AEAD_CCA_Game_Real D A) := by
  unfold AEAD_CCA_Game_Real
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro key
  exact hA _ _ (fun _ _ => SPComp.pure_isPure _) (fun _ _ => SPComp.pure_isPure _)

theorem AEAD_CCA_Game_Ideal_isPure
    (A : AEAD_CCA_Adversary W)
    (hA : ∀ (enc : W → W → SPComp W) (dec : W → W → SPComp (Option W)),
      (∀ x y, SPComp.IsPure (enc x y)) →
      (∀ x y, SPComp.IsPure (dec x y)) →
      SPComp.IsPure (A.run enc dec)) :
    SPComp.IsPure (AEAD_CCA_Game_Ideal A) := by
  unfold AEAD_CCA_Game_Ideal
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro _
  exact hA _ _ (fun _ _ => SPComp.sample_isPure _) (fun _ _ => SPComp.pure_isPure _)

/-! ## Keyed AEAD Games (KDM + Key Leakage)

### Non-Standard Assumption

`AEAD_Keyed_Advantage` combines two non-standard properties:
1. **Key-dependent messages (KDM)**: plaintext and associated data depend on the key
   via `pt ad : W → W`, rather than being fixed constants.
2. **Key leakage**: the real game outputs `(ciphertext, key)` as a pair, leaking
   the secret key alongside the ciphertext.

Standard `AEAD_Advantage` does NOT imply `AEAD_Keyed_Advantage`. In general,
KDM security requires additional assumptions (e.g., random oracle / ideal cipher).

### Literature

- KDM security: Black, Rogaway, Shrimpton, *Encryption-Scheme Security in the
  Presence of Key-Dependent Messages*, SAC 2003
- KDM for public-key: Applebaum et al., *Key-Dependent Message Security*, 2014
- Leakage resilience: Dodis et al., *Public-Key Encryption Schemes with Auxiliary
  Inputs*, TCC 2010; Dziembowski, Pietrzak, *Leakage-Resilient Cryptography*, 2008

### Usage

Used by EDHOC (genuinely needed: `th_3` depends on `prk_3e2m`, creating a circular
key dependency). Also used by SSH, Kerberos, and HPKE multi-message (Phase B).
Not needed by HPKE single-shot modes (standard `AEAD_Advantage` suffices). -/

/-- AEAD keyed real game: sample key, output (ciphertext, key) pair.
The plaintext and associated data may depend on the key (key-dependent messages). -/
noncomputable def aead_keyed_real (D : AEADDef W)
    (pt ad : W → W) : SPComp (W × W) :=
  SPComp.bind (SPComp.sample W) (fun key =>
    SPComp.pure (D.encrypt key (pt key) (ad key), key))

/-- AEAD keyed ideal game: sample independent random pair. -/
noncomputable def aead_keyed_ideal : SPComp (W × W) :=
  SPComp.sample (W × W)

/-- AEAD keyed advantage: distinguishing real encryption+key from random pair. -/
noncomputable def AEAD_Keyed_Advantage (D : AEADDef W) (pt ad : W → W)
    (A : W × W → SPComp Bool) : ENNReal :=
  AdvantageA (aead_keyed_real D pt ad) aead_keyed_ideal A

theorem aead_keyed_real_isPure (D : AEADDef W) (pt ad : W → W) :
    SPComp.IsPure (aead_keyed_real D pt ad) := by
  unfold aead_keyed_real
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro _
  exact SPComp.pure_isPure _

theorem aead_keyed_ideal_isPure : SPComp.IsPure (aead_keyed_ideal (W := W)) :=
  SPComp.sample_isPure _

end CatCrypt.Crypto.Assumptions

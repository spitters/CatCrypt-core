/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Crypto.Assumptions.AEAD
public import CatCryptCore.Crypto.Assumptions.OWF
public import CatCryptCore.Crypto.Signatures.Scheme

/-!
# Sender Keys: the cryptographic interface

The class `SenderKeysCrypto` collects the operations of Signal's Sender Keys group-messaging
ratchet (libsignal `sender_keys.rs`). Each group member keeps a chain key, advanced once per
message, and a signing key, with which it signs each broadcast. The security statements of
`Security` are parametric over every instance.

The four primitives are:
1. `kdf_msg`, chain key to message key (HMAC-SHA256 with the label of the message key);
2. `kdf_chain`, chain key to next chain key (HMAC-SHA256 with the label of the chain key);
3. `aead_encrypt` / `aead_decrypt`, the authenticated cipher, with an explicit nonce;
4. `keygen` / `sign` / `verify`, the signature scheme.

## The nonce

libsignal derives the nonce of a message from its iteration counter. Every message key
encrypts one message, so the confidentiality statement needs one-time security of the cipher
only, and the model fixes the nonce to `default` (`senderKeysAEAD`): the AEAD game of a
uniform key does not depend on the nonce used with that key.

## Main definitions

* `SenderKeysCrypto` — the primitives
* `senderKeysPRG` — one step of the chain, `k ↦ (kdf_msg k, kdf_chain k)`, as a PRG
* `senderKeysAEAD` — the cipher at the fixed nonce as an `AEADDef`
* `senderKeysSigScheme` — the signature scheme as a `SigScheme`

## References

* Signal, *Sesame* and the Sender Keys specification, <https://signal.org/docs/>
* Balbás, Collins, Gajland, *WhatsUpp with Sender Keys? Analysis, Improvements and Security
  Proofs*, ASIACRYPT 2023
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SenderKeys.Dependencies

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signatures

variable {W : Type} [CryptoWord W]

/-- The primitives of Sender Keys. Keys, plaintexts, ciphertexts, associated data, nonces and
signatures are words of the type `W`. -/
class SenderKeysCrypto (W : Type) [CryptoWord W] where
  /-- Message-key derivation from the chain key. -/
  kdf_msg : W → W
  /-- Chain-key advance. -/
  kdf_chain : W → W
  /-- Authenticated encryption: `(key, nonce, aad, plaintext) ↦ ciphertext`. -/
  aead_encrypt : W → W → W → W → W
  /-- Authenticated decryption: `(key, nonce, aad, ciphertext) ↦ some plaintext`, or `none`
  on a rejected ciphertext. -/
  aead_decrypt : W → W → W → W → Option W
  /-- Signing with the signing key. -/
  sign : W → W → SPComp W
  /-- Verification with the verification key. -/
  verify : W → W → W → Bool
  /-- Generation of a pair (verification key, signing key). -/
  keygen : SPComp (W × W)
  /-- `keygen` is heap-independent. -/
  keygen_isPure : SPComp.IsPure keygen
  /-- `sign sk m` is heap-independent. -/
  sign_isPure : ∀ (sk m : W), SPComp.IsPure (sign sk m)

/-- One step of the key-derivation chain as a pseudorandom generator: the chain key `k` is
stretched to the message key `kdf_msg k` and the next chain key `kdf_chain k`. -/
def senderKeysPRG (deps : SenderKeysCrypto W) : PRGDef W (W × W) :=
  ⟨fun k => (deps.kdf_msg k, deps.kdf_chain k)⟩

/-- The cipher at the fixed nonce `default` as an AEAD: `encrypt key pt ad` is
`aead_encrypt key default ad pt`. -/
def senderKeysAEAD (deps : SenderKeysCrypto W) : AEADDef W W where
  encrypt key pt ad := deps.aead_encrypt key default ad pt
  decrypt key ct ad := deps.aead_decrypt key default ad ct

/-- The signature scheme of Sender Keys as a `SigScheme` over `W`. -/
def senderKeysSigScheme (deps : SenderKeysCrypto W) : SigScheme W W W W where
  keygen := deps.keygen
  sign   := deps.sign
  verify := deps.verify

end CatCrypt.Crypto.Signal.SenderKeys.Dependencies

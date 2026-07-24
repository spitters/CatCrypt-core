/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code

/-!
# Cryptobox Scheme Definitions

Abstract type definitions and scheme records for NaCl's Cryptobox construction.
Cryptobox combines a Non-Interactive Key Exchange (NIKE, e.g., X25519) with a
Nonce-Based Symmetric Encryption Scheme (NBSES, e.g., XSalsa20-Poly1305) to
achieve Public-Key Authenticated Encryption (PKAE).

## Main definitions

* `NBSES` — Nonce-based symmetric encryption scheme (enc/dec with shared key + nonce)
* `NIKEScheme` — Non-interactive key exchange (pkgen + deterministic shared key derivation)
* `KeyInjection` — Injection between NIKE and NBSES key spaces
* `SID` — Session identifier (canonical pair of public keys)
* `sortSID` — Canonical ordering for session IDs

## Design choices

Following the Rocq SSProve Cryptobox (nominal-ssprove), all key types (PK, SK,
SharedKey) are `Fintype` to enable uniform sampling. Messages and ciphertexts
are also `Fintype` for simplicity (the Rocq version uses `choice_type` which
allows infinite types, but Lean's `SPComp.sample` requires `Fintype`).

All scheme operations are pure `SPComp` computations (no state). State is
introduced only in the game definitions (PKEY, KEY, SAE, etc.).

## References

* Dupressoir et al., "Bringing SSP to EasyCrypt — A Security Proof for Cryptobox" (CSF 2022)
* Myssenburg et al., Rocq SSProve Cryptobox (nominal-ssprove)
* Bernstein, Lange, Schwabe, "NaCl: Networking and Cryptography library"
-/

namespace CatCrypt.Examples.Cryptobox

open CatCrypt.Core

/-! ## Abstract types

These are parameters throughout the Cryptobox formalization.
Each file will declare the necessary variables. -/

universe u

/-- Abstract type bundle for Cryptobox.
    All types are finite (for uniform sampling) and have decidable equality
    (for map lookups and equality checks in games). -/
class CryptoTypes where
  PK : Type
  SK : Type
  SharedKey : Type
  Nonce : Type
  M : Type
  C : Type
  [finPK : Fintype PK]
  [finSK : Fintype SK]
  [finSharedKey : Fintype SharedKey]
  [finNonce : Fintype Nonce]
  [finM : Fintype M]
  [finC : Fintype C]
  [inhPK : Inhabited PK]
  [inhSK : Inhabited SK]
  [inhSharedKey : Inhabited SharedKey]
  [inhNonce : Inhabited Nonce]
  [inhM : Inhabited M]
  [inhC : Inhabited C]
  [decPK : DecidableEq PK]
  [decSK : DecidableEq SK]
  [decSharedKey : DecidableEq SharedKey]
  [decNonce : DecidableEq Nonce]
  [decM : DecidableEq M]
  [decC : DecidableEq C]

attribute [instance] CryptoTypes.finPK CryptoTypes.finSK CryptoTypes.finSharedKey
  CryptoTypes.finNonce CryptoTypes.finM CryptoTypes.finC
  CryptoTypes.inhPK CryptoTypes.inhSK CryptoTypes.inhSharedKey
  CryptoTypes.inhNonce CryptoTypes.inhM CryptoTypes.inhC
  CryptoTypes.decPK CryptoTypes.decSK CryptoTypes.decSharedKey
  CryptoTypes.decNonce CryptoTypes.decM CryptoTypes.decC

/-! ## Nonce-Based Symmetric Encryption Scheme (NBSES)

Corresponds to Rocq's `NBSES_scheme`. In NaCl, this is XSalsa20-Poly1305.
All operations are pure `SPComp` (no state, no oracle access). -/

variable [CT : CryptoTypes] in
/-- Nonce-Based Symmetric Encryption Scheme.
    Parameterized by a `CryptoTypes` instance providing the abstract types. -/
structure NBSES where
  /-- Probabilistic encryption: key → message → nonce → ciphertext -/
  enc : CT.SharedKey → CT.M → CT.Nonce → SPComp CT.C
  /-- Decryption: key → ciphertext → nonce → message (may fail for AEAD) -/
  dec : CT.SharedKey → CT.C → CT.Nonce → SPComp (Option CT.M)

/-! ## Non-Interactive Key Exchange (NIKE)

Corresponds to Rocq's `NIKE_scheme`. In NaCl, this is X25519.
The shared key computation is deterministic (pure function). -/

variable [CT : CryptoTypes] in
/-- Non-Interactive Key Exchange scheme. -/
structure NIKEScheme where
  /-- Key pair generation (probabilistic) -/
  pkgen : SPComp (CT.PK × CT.SK)
  /-- Shared key derivation (deterministic).
      Given a remote public key and local secret key, computes a shared secret.
      In NaCl: X25519(sk, pk). -/
  sharedkey : CT.PK → CT.SK → CT.SharedKey

/-! ## Key Injection

Corresponds to Rocq's `inj` record. Maps between NIKE shared keys and
NBSES shared keys. In practice, this is often the identity or a hash. -/

variable [CT : CryptoTypes] in
/-- Injection between key spaces (NIKE shared keys ↔ NBSES shared keys).
    Allows composing NIKE and NBSES even if their key types differ abstractly. -/
structure KeyInjection where
  /-- Encode a NIKE shared key for use as an NBSES key -/
  encode : CT.SharedKey → CT.SharedKey
  /-- Decode back -/
  decode : CT.SharedKey → CT.SharedKey
  /-- Round-trip: decode ∘ encode = id -/
  cancels : ∀ k, decode (encode k) = k

/-! ## Session Identifiers (SID)

A session ID is a canonical pair of public keys identifying a communication
session between two parties. The canonical ordering ensures both parties
compute the same SID regardless of who is sender/receiver. -/

variable [CT : CryptoTypes]

/-- Session identifier: a pair of public keys. -/
abbrev SID := CT.PK × CT.PK

/-- Canonical sort for session IDs.
    Ensures `sortSID pk_a pk_b = sortSID pk_b pk_a`. -/
noncomputable def sortSID [LinearOrder CT.PK] (pk1 pk2 : CT.PK) : SID :=
  if pk1 ≤ pk2 then (pk1, pk2) else (pk2, pk1)

/-- sortSID is symmetric: the order of arguments doesn't matter. -/
theorem sortSID_comm [LinearOrder CT.PK] (pk1 pk2 : CT.PK) :
    sortSID pk1 pk2 = sortSID pk2 pk1 := by
  unfold sortSID
  split <;> split <;> first | rfl | (congr 1 <;> order)

/-! ## NIKE Commutativity

The key property for Cryptobox: the shared key is the same regardless of
which party acts as sender/receiver. This is stated as a property of
(NIKEScheme, pkgen output) pairs rather than as a field of NIKEScheme,
following the Rocq approach. -/

/-- NIKE commutativity: shared key is the same regardless of role.
    For honestly generated key pairs (pk_a, sk_a) and (pk_b, sk_b):
    `sharedkey pk_a sk_b = sharedkey pk_b sk_a` -/
def NIKEScheme.Commutative (N : @NIKEScheme CT) : Prop :=
  ∀ (pk_a sk_a pk_b sk_b : _),
    N.pkgen = SPComp.pure (pk_a, sk_a) →
    N.pkgen = SPComp.pure (pk_b, sk_b) →
    N.sharedkey pk_a sk_b = N.sharedkey pk_b sk_a

/-! ## Nonce-Based Public-key Encryption Scheme (NBPES/PKAE)

The target construction: public-key authenticated encryption.
Corresponds to Rocq's `NBPES_scheme`. -/

/-- Nonce-Based Public-key Encryption Scheme (PKAE target). -/
structure NBPES where
  /-- Key pair generation -/
  pkgen : SPComp (CT.PK × CT.SK)
  /-- Encryption: sender's SK, receiver's PK, message, nonce → ciphertext -/
  enc : CT.SK → CT.PK → CT.M → CT.Nonce → SPComp CT.C
  /-- Decryption: receiver's SK, sender's PK, ciphertext, nonce → message -/
  dec : CT.SK → CT.PK → CT.C → CT.Nonce → SPComp (Option CT.M)

/-! ## Cryptobox Construction

The main construction: combine NIKE + NBSES into a PKAE scheme. -/

/-- Construct a PKAE scheme from NIKE + NBSES + key injection.
    This is the Cryptobox construction:
    - pkgen = NIKE.pkgen
    - enc(sk_s, pk_r, m, n) = NBSES.enc(inj(NIKE.sharedkey(pk_r, sk_s)), m, n)
    - dec(sk_r, pk_s, c, n) = NBSES.dec(inj(NIKE.sharedkey(pk_s, sk_r)), c, n) -/
noncomputable def cryptobox
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT) : NBPES where
  pkgen := N.pkgen
  enc sk_s pk_r m n :=
    let k := N.sharedkey pk_r sk_s
    E.enc (I.encode k) m n
  dec sk_r pk_s c n :=
    let k := N.sharedkey pk_s sk_r
    E.dec (I.encode k) c n

/-! ## Operation identifiers

Fixed natural number identifiers for each oracle operation.
These correspond to the Rocq operation IDs and are used for
interface matching in the package system. -/

/-- Operation ID for key generation -/
def opGEN : Nat := 2
/-- Operation ID for corrupt set public key -/
def opCSETPK : Nat := 3
/-- Operation ID for get secret key -/
def opGETSK : Nat := 4
/-- Operation ID for check honest public key -/
def opHONPK : Nat := 5
/-- Operation ID for NIKE shared key computation -/
def opSHAREDKEY : Nat := 24
/-- Operation ID for honest key set -/
def opSET : Nat := 27
/-- Operation ID for corrupt key set -/
def opCSET : Nat := 28
/-- Operation ID for key get -/
def opGET : Nat := 29
/-- Operation ID for honesty check -/
def opHON : Nat := 30
/-- Operation ID for encryption -/
def opENC : Nat := 31
/-- Operation ID for decryption -/
def opDEC : Nat := 32

end CatCrypt.Examples.Cryptobox

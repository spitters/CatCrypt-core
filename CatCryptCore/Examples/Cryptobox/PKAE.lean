/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Cryptobox.Scheme
import CatCryptCore.Examples.Cryptobox.PKEY
import CatCryptCore.Crypto.Advantage
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

/-!
# PKAE: Public-Key Authenticated Encryption Game

The PKAE game is the target security definition for Cryptobox. It captures
the combined security of NIKE + NBSES as a public-key authenticated encryption
scheme.

## Overview

Two variants parameterized by `b : Bool`:
- `b = false` (real): encryption and decryption use the actual shared key
  derived from the NIKE scheme
- `b = true` (ideal): for honest-honest sessions, encryption returns a
  uniformly random ciphertext (logging the query), and decryption checks the
  log instead of decrypting; for pairs involving a corrupt key, the real
  scheme is used

The PKAE game internally creates PKEY oracles (with collision-free = true) for
key management, and provides additional encryption/decryption oracles.

## Oracles

- `pgen`: Generate an honest key pair (delegates to PKEY GEN)
- `pcsetpk`: Register a corrupt public key (delegates to PKEY CSETPK)
- `penc`: Encrypt a message from sender to receiver under a nonce
- `pdec`: Decrypt a ciphertext from sender to receiver under a nonce

## References

* Rocq SSProve: theories/Cryptobox/PKAE.v
* Dupressoir et al., CSF 2022 (Section 4.4)
-/

namespace CatCrypt.Examples.Cryptobox.PKAEGame

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto
open scoped ENNReal

variable [CT : CryptoTypes] [LinearOrder CT.PK]

/-! ## Heap Locations

State specific to the PKAE game. Location IDs start at 500 to avoid
collisions with PKEY (100-range), KEY (200-range), SAE (300-range),
and NIKE (400-range) locations. -/

/-- Encryption log indexed by `(PK, PK, Nonce)`: maps each (sender, receiver, nonce)
    triple to an optional `(M, C)` pair recorded during ideal encryption.
    Used in the ideal game to answer decryption queries consistently. -/
@[reducible] noncomputable def pkaeLogLoc : Location :=
  ⟨500, CT.PK × CT.PK × CT.Nonce → Option (CT.M × CT.C)⟩

/-! ## Oracle Definitions

Each oracle is an `SPComp` computation that reads/writes heap locations.
The `b : Bool` parameter switches between real and ideal behavior for
encryption and decryption. -/

/-- PKAE encryption oracle.

    Given sender and receiver public keys, a message, and a nonce:
    1. Retrieve the sender's secret key via `pkeyO.getsk`
    2. Check honesty of both parties via `pkeyO.honpk`
    3. If both honest AND `b = true` (ideal): sample a random ciphertext,
       log the `(message, ciphertext)` pair, and return the ciphertext
    4. Otherwise (real, or at least one corrupt): compute the shared key
       via `N.sharedkey`, apply key injection, and encrypt with `E.enc` -/
noncomputable def pkaeEncOracle (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (b : Bool) (pkeyO : PKEYOracles)
    (pk_s pk_r : CT.PK) (m : CT.M) (n : CT.Nonce) : SPComp CT.C := do
  let sk_s ← pkeyO.getsk pk_s
  let hon_s ← pkeyO.honpk pk_s
  let hon_r ← pkeyO.honpk pk_r
  if b && hon_s && hon_r then do
    let log ← SPComp.get pkaeLogLoc
    let idx := (pk_s, pk_r, n)
    -- Nonce reuse check: fail if this (sender, receiver, nonce) was already used
    match log idx with
    | some _ => SPComp.fail
    | none => SPComp.pure ()
    let c ← SPComp.sample CT.C
    SPComp.set pkaeLogLoc
      (Function.update log idx (some (m, c)) :
        CT.PK × CT.PK × CT.Nonce → Option (CT.M × CT.C))
    SPComp.pure c
  else do
    let k := N.sharedkey pk_r sk_s
    E.enc (I.encode k) m n

/-- PKAE decryption oracle.

    Given sender and receiver public keys, a ciphertext, and a nonce:
    1. Retrieve the receiver's secret key via `pkeyO.getsk`
    2. Check honesty of both parties via `pkeyO.honpk`
    3. If both honest AND `b = true` (ideal): look up the encryption log
       for the *reverse* direction `(pk_r, pk_s, n)`:
       - If found and the ciphertext matches: return the logged plaintext
       - Otherwise: return `none` (no decryption in ideal world for
         ciphertexts not produced by the encryption oracle)
    4. Otherwise (real, or at least one corrupt): compute the shared key
       via `N.sharedkey`, apply key injection, and decrypt with `E.dec` -/
noncomputable def pkaeDecOracle (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (b : Bool) (pkeyO : PKEYOracles)
    (pk_s pk_r : CT.PK) (c : CT.C) (n : CT.Nonce) : SPComp (Option CT.M) := do
  let sk_r ← pkeyO.getsk pk_r
  let hon_s ← pkeyO.honpk pk_s
  let hon_r ← pkeyO.honpk pk_r
  if b && hon_s && hon_r then do
    -- Look up the log for the reverse direction: sender encrypted to receiver
    let log ← SPComp.get pkaeLogLoc
    let idx := (pk_s, pk_r, n)
    match log idx with
    | some (m, c') =>
      if c == c' then SPComp.pure (some m)
      else SPComp.pure none
    | none => SPComp.pure none
  else do
    let k := N.sharedkey pk_s sk_r
    E.dec (I.encode k) c n

/-! ## Oracle Record -/

/-- Oracle interface for PKAE games.
    Provides key generation, corrupt key registration, encryption, and
    decryption oracles. -/
structure PKAEOracles where
  /-- Generate a fresh honest key pair -/
  pgen : Unit → SPComp CT.PK
  /-- Register an adversary-chosen public key as corrupt -/
  pcsetpk : CT.PK → SPComp Unit
  /-- Encrypt: sender PK, receiver PK, message, nonce → ciphertext -/
  penc : CT.PK → CT.PK → CT.M → CT.Nonce → SPComp CT.C
  /-- Decrypt: sender PK, receiver PK, ciphertext, nonce → optional message -/
  pdec : CT.PK → CT.PK → CT.C → CT.Nonce → SPComp (Option CT.M)

/-! ## PKAE Game -/

/-- PKAE game parameterized by `b`:
    - `b = false`: real — encrypt/decrypt with actual NIKE shared keys
    - `b = true`: ideal — honest-honest encryption returns random ciphertext,
      decryption checks log; corrupt sessions use real keys

    Internally creates PKEY oracles with collision-free = true, which is
    justified by the PKEY switching lemma. -/
noncomputable def GPKAE (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (b : Bool) (A : PKAEOracles → SPComp Bool) : SPComp Bool :=
  let pkeyO : PKEYOracles :=
    { gen := fun _ => genOracle N true,
      csetpk := csetpkOracle,
      getsk := getskOracle,
      honpk := honpkOracle }
  A { pgen := pkeyO.gen,
      pcsetpk := pkeyO.csetpk,
      penc := pkaeEncOracle N E I b pkeyO,
      pdec := pkaeDecOracle N E I b pkeyO }

/-! ## PKAE Advantage -/

/-- PKAE advantage: distinguishing distance between real and ideal games.
    Measures the adversary's ability to distinguish real encryption from
    random ciphertexts in the PKAE game. -/
noncomputable def pkaeAdvantage (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (GPKAE N E I false A) (GPKAE N E I true A)

end CatCrypt.Examples.Cryptobox.PKAEGame

/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Cryptobox.Scheme
import CatCryptCore.Crypto.Advantage
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

/-!
# SAE: Single-instance Authenticated Encryption Game

The SAE game captures the security of a single symmetric encryption instance,
parameterized by a Nonce-Based Symmetric Encryption Scheme (NBSES).

## Overview

Two variants parameterized by `b : Bool`:
- `b = false` (real): encrypt and decrypt using the actual shared key
- `b = true` (ideal): encryption returns a random ciphertext (and logs the
  plaintext-ciphertext pair), decryption checks the log instead of using the key

## Oracles

- `sgen`: Generate and store a random shared key
- `senc`: Encrypt a message under a nonce (real or ideal)
- `sdec`: Decrypt a ciphertext under a nonce (real or log-based)

## References

* Rocq SSProve: theories/Cryptobox/SAE.v
* Dupressoir et al., CSF 2022 (Section 4.3)
-/

namespace CatCrypt.Examples.Cryptobox

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto
open scoped ENNReal

variable [CT : CryptoTypes]

/-! ## Heap Locations

State is stored in the global heap via typed locations.
Locations are `@[reducible]` so that `.ty` reduces for type checking. -/

/-- The single shared encryption key. -/
@[reducible] noncomputable def saeKeyLoc : Location := ⟨300, CT.SharedKey⟩

/-- Encryption log indexed by nonce: maps each nonce to an optional
    (plaintext, ciphertext) pair recorded during ideal encryption. -/
@[reducible] noncomputable def saeLogLoc : Location :=
  ⟨301, CT.Nonce → Option (CT.M × CT.C)⟩

/-- Whether the key has been generated. -/
@[reducible] noncomputable def saeInitLoc : Location := ⟨302, Bool⟩

/-! ## Oracle Definitions

Each oracle is an `SPComp` computation that reads/writes heap locations.
The `b : Bool` parameter in `saeEncOracle` and `saeDecOracle` switches
between real and ideal behavior. -/

/-- SGEN oracle: generate and store a fresh random shared key.
    Fails if the key has already been generated. -/
noncomputable def saeGenOracle (_E : @NBSES CT) : SPComp Unit := do
  let init ← SPComp.get saeInitLoc
  if init then SPComp.fail
  else SPComp.pure ()
  let k ← SPComp.sample CT.SharedKey
  SPComp.set saeKeyLoc k
  SPComp.set saeInitLoc true

/-- SENC oracle: encrypt a message under a nonce.
    - `b = false` (real): encrypt with the stored key
    - `b = true` (ideal): sample a random ciphertext, log the (message, ciphertext)
      pair at the given nonce; fails if the nonce was already used (honesty check) -/
noncomputable def saeEncOracle (E : @NBSES CT) (b : Bool)
    (m : CT.M) (n : CT.Nonce) : SPComp CT.C := do
  let init ← SPComp.get saeInitLoc
  if !init then SPComp.fail
  else SPComp.pure ()
  if b then do
    let log ← SPComp.get saeLogLoc
    -- Honest nonce: must not have been used before
    match log n with
    | some _ => SPComp.fail
    | none => SPComp.pure ()
    let c ← SPComp.sample CT.C
    SPComp.set saeLogLoc
      (Function.update log n (some (m, c)) : CT.Nonce → Option (CT.M × CT.C))
    SPComp.pure c
  else do
    let k ← SPComp.get saeKeyLoc
    E.enc k m n

/-- SDEC oracle: decrypt a ciphertext under a nonce.
    - `b = false` (real): decrypt with the stored key
    - `b = true` (ideal): look up the nonce in the log; if the ciphertext matches
      the logged one, return the logged plaintext; otherwise fail -/
noncomputable def saeDecOracle (E : @NBSES CT) (b : Bool)
    (c : CT.C) (n : CT.Nonce) : SPComp (Option CT.M) := do
  let init ← SPComp.get saeInitLoc
  if !init then SPComp.fail
  else SPComp.pure ()
  if b then do
    let log ← SPComp.get saeLogLoc
    match log n with
    | some (m, c') =>
      if c == c' then SPComp.pure (some m)
      else SPComp.fail
    | none => SPComp.fail
  else do
    let k ← SPComp.get saeKeyLoc
    E.dec k c n

/-! ## Oracle Record -/

/-- Oracle interface for SAE games. -/
structure SAEOracles where
  sgen : Unit → SPComp Unit
  senc : CT.M → CT.Nonce → SPComp CT.C
  sdec : CT.C → CT.Nonce → SPComp (Option CT.M)

/-! ## SAE Game -/

/-- SAE game parameterized by real/ideal behavior `b`.
    - `b = false`: real — encrypt/decrypt with actual key
    - `b = true`: ideal — encrypt returns random ciphertext, decrypt checks log -/
noncomputable def SAE (E : @NBSES CT) (b : Bool)
    (A : SAEOracles → SPComp Bool) : SPComp Bool :=
  A { sgen := fun _ => saeGenOracle E,
      senc := saeEncOracle E b,
      sdec := saeDecOracle E b }

/-! ## SAE Advantage -/

/-- SAE advantage: distinguishing distance between real and ideal games. -/
noncomputable def saeAdvantage (E : @NBSES CT)
    (A : SAEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (SAE E false A) (SAE E true A)

end CatCrypt.Examples.Cryptobox

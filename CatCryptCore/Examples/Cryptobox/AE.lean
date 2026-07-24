/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Cryptobox.Scheme
import CatCryptCore.Examples.Cryptobox.KEY
import CatCryptCore.Examples.Cryptobox.SAE
import CatCryptCore.Crypto.Advantage
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

/-!
# AE: Multi-instance Authenticated Encryption Game

The AE game captures the security of authenticated encryption across multiple
sessions, composing the KEY game (shared key management) with per-session
encryption/decryption.

## Overview

Two variants parameterized by `b : Bool`:
- `b = false` (real): encrypt and decrypt using the actual shared key from KEY
- `b = true` (ideal): for honest sessions, encryption returns a random ciphertext
  (logged per session and nonce), decryption checks the log; for corrupt sessions,
  real encryption/decryption is used

## Oracles

- `aenc`: Encrypt a message for a session under a nonce
- `adec`: Decrypt a ciphertext for a session under a nonce

The AE oracles internally query KEY oracles for key retrieval and honesty checks.

## References

* Rocq SSProve: theories/Cryptobox/AE.v
* Dupressoir et al., CSF 2022 (Section 4.4)
-/

namespace CatCrypt.Examples.Cryptobox

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto
open scoped ENNReal

variable [CT : CryptoTypes]

/-! ## Heap Locations

Per-session encryption log, indexed by `(SID, Nonce)`. -/

/-- Per-session encryption log: maps each `(SID, Nonce)` pair to an optional
    `(plaintext, ciphertext)` pair recorded during ideal encryption. -/
@[reducible] noncomputable def aeLogLoc : Location :=
  ⟨500, (SID × CT.Nonce) → Option (CT.M × CT.C)⟩

/-! ## Oracle Definitions

Each oracle retrieves the shared key and honesty flag from the KEY oracles,
then behaves either as real encryption/decryption or ideal (log-based)
depending on `b` and the honesty of the session. -/

/-- AE encryption oracle.
    - Gets the shared key for the session via `keyO.kget`
    - Checks honesty via `keyO.khon`
    - If `b = false` (real): encrypt with `E.enc (I.encode k) m n`
    - If `b = true` AND the session is honest: sample a random ciphertext,
      log the `(message, ciphertext)` pair at `(sid, n)`
    - If `b = true` but the session is corrupt: real encryption -/
noncomputable def aeEncOracle (E : @NBSES CT) (I : @KeyInjection CT) (b : Bool)
    (keyO : KEYOracles) (sid : SID) (m : CT.M) (n : CT.Nonce) : SPComp CT.C := do
  let k ← keyO.kget sid
  let hon ← keyO.khon sid
  if b && hon then do
    let log ← SPComp.get aeLogLoc
    let c ← SPComp.sample CT.C
    SPComp.set aeLogLoc
      (Function.update log (sid, n) (some (m, c)) :
        (SID × CT.Nonce) → Option (CT.M × CT.C))
    SPComp.pure c
  else
    E.enc (I.encode k) m n

/-- AE decryption oracle.
    - Gets the shared key for the session via `keyO.kget`
    - Checks honesty via `keyO.khon`
    - If `b = false` (real): decrypt with `E.dec (I.encode k) c n`
    - If `b = true` AND the session is honest: look up `(sid, n)` in the log;
      if the ciphertext matches the logged one, return the logged plaintext;
      otherwise return `none`
    - If `b = true` but the session is corrupt: real decryption -/
noncomputable def aeDecOracle (E : @NBSES CT) (I : @KeyInjection CT) (b : Bool)
    (keyO : KEYOracles) (sid : SID) (c : CT.C) (n : CT.Nonce) :
    SPComp (Option CT.M) := do
  let k ← keyO.kget sid
  let hon ← keyO.khon sid
  if b && hon then do
    let log ← SPComp.get aeLogLoc
    match log (sid, n) with
    | some (m, c') =>
      if c == c' then SPComp.pure (some m)
      else SPComp.pure none
    | none => SPComp.pure none
  else
    E.dec (I.encode k) c n

/-! ## Oracle Record -/

/-- Oracle interface for AE games. -/
structure AEOracles where
  aenc : SID → CT.M → CT.Nonce → SPComp CT.C
  adec : SID → CT.C → CT.Nonce → SPComp (Option CT.M)

/-! ## AE Game

The AE game composes KEY oracles internally: the adversary gets access to
both AE oracles (encrypt/decrypt) and KEY oracles (key management). -/

/-- AE game parameterized by real/ideal behavior `b`.
    - `b = false`: real — encrypt/decrypt with actual shared keys
    - `b = true`: ideal — honest sessions use random ciphertexts and log-based
      decryption; corrupt sessions still use real encryption

    The adversary receives both AE oracles and KEY oracles. -/
noncomputable def GAE (E : @NBSES CT) (I : @KeyInjection CT) (b : Bool)
    (keyO : KEYOracles) (A : AEOracles → SPComp Bool) : SPComp Bool :=
  A { aenc := aeEncOracle E I b keyO,
      adec := aeDecOracle E I b keyO }

/-! ## AE Advantage -/

/-- AE advantage: distinguishing distance between real and ideal AE games
    with fixed KEY oracles. -/
noncomputable def aeAdvantage (E : @NBSES CT) (I : @KeyInjection CT)
    (keyO : KEYOracles) (A : AEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (GAE E I false keyO A) (GAE E I true keyO A)

end CatCrypt.Examples.Cryptobox

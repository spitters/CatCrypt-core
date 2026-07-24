/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Cryptobox.Scheme
import CatCryptCore.Crypto.Advantage
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# KEY: Shared Key Management Game

The KEY game manages shared keys indexed by session identifiers (SID).

## Overview

Two variants parameterized by `b : Bool`:
- `b = false` (real): stores actual shared keys provided by the caller
- `b = true` (ideal): replaces honest keys with freshly sampled random keys

## Oracles

- `kset`: Honest key set — stores actual key (real) or random key (ideal)
- `kcset`: Corrupt key set — always stores the provided key directly
- `kget`: Retrieve the stored shared key for a session
- `khon`: Check whether a session's key was set honestly

## References

* Rocq SSProve: theories/Cryptobox/KEY.v
* Dupressoir et al., CSF 2022 (Section 4.2)
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

/-- Shared key storage: `SID → SharedKey`. Default: all `default`. -/
@[reducible] noncomputable def keyStoreLoc : Location := ⟨200, SID → CT.SharedKey⟩

/-- Honesty flags for shared keys: `SID → Bool`. Default: all `false` (unset). -/
@[reducible] noncomputable def keyHonestLoc : Location := ⟨201, SID → Bool⟩

/-! ## Oracle Definitions

Each oracle is an `SPComp` computation that reads/writes heap locations.
The `b : Bool` parameter in `keySetOracle` switches between real and ideal behavior. -/

/-- KSET oracle: set the shared key for a session.
    If the session already has a key set (honest or corrupt), fails.
    If `b = false` (real): stores the provided key `k`.
    If `b = true` (ideal): samples a fresh random key and stores that instead. -/
noncomputable def keySetOracle (b : Bool) (sid : SID) (k : CT.SharedKey) : SPComp Unit := do
  let honest ← SPComp.get keyHonestLoc
  let store ← SPComp.get keyStoreLoc
  if honest sid then SPComp.fail
  else SPComp.pure ()
  if b then do
    let k' ← SPComp.sample CT.SharedKey
    SPComp.set keyStoreLoc (Function.update store sid k' : SID → CT.SharedKey)
  else
    SPComp.set keyStoreLoc (Function.update store sid k : SID → CT.SharedKey)
  SPComp.set keyHonestLoc (Function.update honest sid true : SID → Bool)

/-- KCSET oracle: corrupt key set — always stores the provided key directly.
    Marks the session as not honest (corrupt). -/
noncomputable def keyCsetOracle (sid : SID) (k : CT.SharedKey) : SPComp Unit := do
  let honest ← SPComp.get keyHonestLoc
  let store ← SPComp.get keyStoreLoc
  if honest sid then SPComp.fail
  else SPComp.pure ()
  SPComp.set keyStoreLoc (Function.update store sid k : SID → CT.SharedKey)

/-- KGET oracle: retrieve the stored shared key for a session. -/
noncomputable def keyGetOracle (sid : SID) : SPComp CT.SharedKey := do
  let store ← SPComp.get keyStoreLoc
  SPComp.pure (store sid)

/-- KHON oracle: check whether a session's key was set honestly. -/
noncomputable def keyHonOracle (sid : SID) : SPComp Bool := do
  let honest ← SPComp.get keyHonestLoc
  SPComp.pure (honest sid)

/-! ## Oracle Record -/

/-- Oracle interface for KEY games. -/
structure KEYOracles where
  kset : SID → CT.SharedKey → SPComp Unit
  kcset : SID → CT.SharedKey → SPComp Unit
  kget : SID → SPComp CT.SharedKey
  khon : SID → SPComp Bool

/-! ## KEY Game -/

/-- KEY game parameterized by real/ideal behavior `b`.
    - `b = false`: real — honest keys are stored as provided
    - `b = true`: ideal — honest keys are replaced with random samples -/
noncomputable def KEY (b : Bool)
    (A : KEYOracles → SPComp Bool) : SPComp Bool :=
  A { kset := keySetOracle b,
      kcset := keyCsetOracle,
      kget := keyGetOracle,
      khon := keyHonOracle }

end CatCrypt.Examples.Cryptobox

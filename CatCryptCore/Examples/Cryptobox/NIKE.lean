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
# NIKE: Non-Interactive Key Exchange Game

The NIKE game captures the security of the shared key exchange component
of Cryptobox. It has two variants parameterized by `b : Bool`:

- `b = false` (real): the shared key is computed via `N.sharedkey`
- `b = true` (ideal): for honest-honest pairs the shared key is sampled
  uniformly at random; for pairs involving a corrupt key the real shared
  key is returned

The NIKE game builds on top of the PKEY oracles (key generation, corruption
tracking, secret key retrieval, and honesty checks).

## References

* Rocq SSProve: theories/Cryptobox/NIKE.v
* Dupressoir et al., CSF 2022 (Section 4.2)
-/

namespace CatCrypt.Examples.Cryptobox

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Crypto
open scoped ENNReal

variable [CT : CryptoTypes] [LinearOrder CT.PK]

/-! ## Heap Locations

State specific to the NIKE game. Location IDs start at 400 to avoid
collisions with PKEY locations (100-range). -/

/-- Stored shared keys indexed by canonical session ID. -/
@[reducible] noncomputable def nikeKeysLoc : Location :=
  ⟨400, SID → Option CT.SharedKey⟩

/-- Honesty flags for sessions: whether both parties are honest. -/
@[reducible] noncomputable def nikeHonestLoc : Location :=
  ⟨401, SID → Bool⟩

/-! ## Oracle Definitions -/

/-- Shared key oracle for the NIKE game.

    Given sender and receiver public keys:
    1. Check honesty of both keys via `pkeyO.honpk`
    2. Retrieve sender's secret key via `pkeyO.getsk`
    3. Compute the canonical session ID via `sortSID`
    4. Look up whether a key was already stored for this session
    5. If `b = false` (real) or either party is corrupt: compute the real
       shared key via `N.sharedkey`
    6. If `b = true` (ideal) and both parties are honest: sample a
       uniformly random shared key
    7. Store and return the key -/
noncomputable def sharedkeyOracle (N : @NIKEScheme CT) (b : Bool)
    (pkeyO : PKEYOracles) (pk_s pk_r : CT.PK) : SPComp CT.SharedKey := do
  let hon_s ← pkeyO.honpk pk_s
  let hon_r ← pkeyO.honpk pk_r
  let sk_s ← pkeyO.getsk pk_s
  let sid := sortSID pk_s pk_r
  let keys ← SPComp.get nikeKeysLoc
  match keys sid with
  | some k => SPComp.pure k
  | none => do
    let k ←
      if b && hon_s && hon_r then
        SPComp.sample CT.SharedKey
      else
        SPComp.pure (N.sharedkey pk_r sk_s)
    let honMap ← SPComp.get nikeHonestLoc
    SPComp.set nikeKeysLoc (Function.update keys sid (some k) : SID → Option CT.SharedKey)
    SPComp.set nikeHonestLoc (Function.update honMap sid (hon_s && hon_r) : SID → Bool)
    SPComp.pure k

/-! ## Oracle Record -/

/-- Oracle interface for the NIKE game. -/
structure NIKEOracles where
  sharedkey : CT.PK → CT.PK → SPComp CT.SharedKey

/-! ## NIKE Game -/

/-- NIKE game parameterized by `b`:
    - `b = false`: real shared keys
    - `b = true`: ideal (random) shared keys for honest pairs

    The adversary receives both PKEY oracles (for key management) and
    the NIKE oracle (for shared key queries). -/
noncomputable def GNIKE (N : @NIKEScheme CT) (b : Bool)
    (pkeyO : PKEYOracles) (A : PKEYOracles → NIKEOracles → SPComp Bool) :
    SPComp Bool :=
  A pkeyO { sharedkey := sharedkeyOracle N b pkeyO }

/-! ## NIKE Advantage -/

/-- NIKE advantage: distinguishing real from ideal shared keys. -/
noncomputable def nikeAdvantage (N : @NIKEScheme CT)
    (pkeyO : PKEYOracles)
    (A : PKEYOracles → NIKEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (GNIKE N false pkeyO A) (GNIKE N true pkeyO A)

end CatCrypt.Examples.Cryptobox

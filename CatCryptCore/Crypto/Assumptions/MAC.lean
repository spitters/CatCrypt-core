/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.CryptoWord

/-!
# MAC (Message Authentication Code) EUF-CMA Security

This file defines the EUF-CMA security notion for MAC schemes at the
abstract `CryptoWord W` level.

## MAC Games

The MAC security game captures the difficulty of forging a valid tag:
- **Real**: tag is computed using the secret MAC key
- **Ideal**: tag is a random value (unforgeable)

For game-hopping proofs (SSH, Kerberos), we use an indistinguishability
formulation rather than existential forgery, which is equivalent up to
a factor of `1/|W|` for single-query adversaries.

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| Game structure | `MAC_Game_Real`/`Ideal` | Boneh-Shoup Def. 6.1 (PRF) |
| Advantage | `Advantage(Real, Ideal)` | `|Pr[W₀] - Pr[W₁]|` |
| Formulation | Indistinguishability (real vs random tag) | Equiv. to SUF-CMA for single query |

**Note:** This uses an indistinguishability formulation rather than EUF-CMA (existential
unforgeability). The two are equivalent up to a factor of `1/|W|` for single-query
adversaries. The indistinguishability formulation composes better with game-hopping.

**Equivalent formalizations:**
- CryptoVerif: `SUF-CMA(mac, verify, key)` macro

## References

* Bellare, Kilian, Rogaway. *The Security of the Cipher Block Chaining Message
  Authentication Code.* JCSS 2000.
* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §6.3
* Cade, Blanchet. *From Computationally-Proved Protocol Specifications to
  Implementations.* JCS 2015.
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## MAC Definition -/

/-- Abstract MAC scheme definition, parametric over `SampleableType W`.

- `mac key message` → tag
- `verify key message tag` → Bool -/
structure MACDef (W : Type) [SampleableType W] where
  /-- MAC computation: (key, message) → tag -/
  mac : W → W → W
  /-- MAC verification: (key, message, tag) → Bool -/
  verify : W → W → W → Bool

/-! ## MAC Games -/

/-- Type of MAC adversary: receives a (message, tag) pair and must
distinguish real MAC from random tag. -/
abbrev MAC_Adversary (W : Type) := W → SPComp Bool

/-- MAC real game: sample random key, compute tag on adversary's message. -/
noncomputable def MAC_Game_Real (D : MACDef W) (msg : W)
    (A : MAC_Adversary W) : SPComp Bool := do
  let key ← SPComp.sample W
  let tag := D.mac key msg
  A tag

/-- MAC ideal game: adversary receives a random tag. -/
noncomputable def MAC_Game_Ideal (A : MAC_Adversary W) : SPComp Bool := do
  let tag ← SPComp.sample W
  A tag

/-- MAC advantage: ability to distinguish real tag from random. -/
noncomputable def MAC_Advantage (D : MACDef W) (msg : W)
    (A : MAC_Adversary W) : ℝ≥0∞ :=
  Advantage (MAC_Game_Real D msg A) (MAC_Game_Ideal A)

/-! ## IsPure Proofs -/

theorem MAC_Game_Real_isPure (D : MACDef W) (msg : W)
    (A : MAC_Adversary W) (hA : ∀ x, SPComp.IsPure (A x)) :
    SPComp.IsPure (MAC_Game_Real D msg A) := by
  unfold MAC_Game_Real
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro key
  exact hA _

theorem MAC_Game_Ideal_isPure (A : MAC_Adversary W)
    (hA : ∀ x, SPComp.IsPure (A x)) :
    SPComp.IsPure (MAC_Game_Ideal A) := by
  unfold MAC_Game_Ideal
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro tag
  exact hA tag

/-! ## Keyed MAC Games (KDM + Key Leakage)

### Non-Standard Assumption

`MAC_Keyed_Advantage` combines key-dependent messages (`msg : W → W`) with key
leakage (outputs `(tag, key)` as a pair). Same KDM + leakage pattern as
`AEAD_Keyed_Advantage`.

### Literature

Same as `AEAD_Keyed_Advantage`: Black-Rogaway-Shrimpton 2003, Applebaum et al.
2014, Dodis et al. 2010.

### Usage

Used by SSH and Kerberos hybrid arguments. -/

/-- MAC keyed real game: sample key, output (tag, key) pair. -/
noncomputable def mac_keyed_real (D : MACDef W) (msg : W → W) : SPComp (W × W) :=
  SPComp.bind (SPComp.sample W) (fun key =>
    SPComp.pure (D.mac key (msg key), key))

/-- MAC keyed ideal game: sample independent random pair. -/
noncomputable def mac_keyed_ideal : SPComp (W × W) :=
  SPComp.sample (W × W)

/-- MAC keyed advantage. -/
noncomputable def MAC_Keyed_Advantage (D : MACDef W) (msg : W → W)
    (A : W × W → SPComp Bool) : ENNReal :=
  AdvantageA (mac_keyed_real D msg) mac_keyed_ideal A

theorem mac_keyed_real_isPure (D : MACDef W) (msg : W → W) :
    SPComp.IsPure (mac_keyed_real D msg) := by
  unfold mac_keyed_real
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro _
  exact SPComp.pure_isPure _

theorem mac_keyed_ideal_isPure : SPComp.IsPure (mac_keyed_ideal (W := W)) :=
  SPComp.sample_isPure _

end CatCrypt.Crypto.Assumptions

/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.CryptoWord

/-!
# RSA One-Way Assumption

This file defines the RSA one-wayness assumption at the abstract `CryptoWord W`
level, used for the FDH signature scheme.

## RSA Game

The RSA game captures the difficulty of inverting the RSA function:
- Challenger samples RSA key pair and random `y ∈ Z_N*`
- Adversary must find `x` such that `rsa(pk, x) = y`

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| Game structure | `RSA_Game_Real` | Boneh-Shoup Def. 10.2 |
| Advantage | `Advantage(Real, Ideal)` | `Pr[RSAadv]` |
| Formulation | Inversion game | Standard one-wayness |

**Equivalent formalizations:**
- EasyCrypt: `RSA` theory
- CryptoVerif: `OW(f, inv, key)` macro

## References

* Rivest, Shamir, Adleman. *A Method for Obtaining Digital Signatures and
  Public-Key Cryptosystems.* CACM 1978.
* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §10.3, Def. 10.2
* Blanchet, Pointcheval. *Automated Security Proofs with Sequences of Games.*
  CRYPTO 2006.
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## RSA Definition -/

/-- Abstract RSA definition, parametric over `SampleableType W`.

- `rsa pk x` → `y` (the RSA function under public key)
- `rsa_inv sk y` → `x` (the RSA inverse under secret key)
- `keygen` → `(sk, pk)` -/
structure RSADef (W : Type) [SampleableType W] where
  /-- RSA function: (public_key, preimage) → image -/
  rsa : W → W → W
  /-- RSA inverse: (secret_key, image) → preimage -/
  rsa_inv : W → W → W
  /-- RSA key generation: `(secret_key, public_key)` -/
  keygen : SPComp (W × W)
  /-- Key generation is heap-independent -/
  keygen_isPure : SPComp.IsPure keygen
/-! ## RSA Games -/

/-- Type of RSA adversary: receives `(pk, y)` and must find `x` with `rsa(pk, x) = y`. -/
abbrev RSA_Adversary (W : Type) := W → W → SPComp W

/-- RSA inversion game (real): adversary tries to invert `rsa(pk, ·)`.

Returns `true` if the adversary successfully inverts. -/
noncomputable def RSA_Game_Real (D : RSADef W) (A : RSA_Adversary W) : SPComp Bool := do
  let ⟨_sk, pk⟩ ← D.keygen
  let x ← SPComp.sample W        -- random preimage
  let y := D.rsa pk x             -- challenge = rsa(pk, x)
  let x' ← A pk y                 -- adversary's guess
  SPComp.pure (D.rsa pk x' == y)  -- check if rsa(pk, x') = y

/-- RSA inversion game (ideal): always returns `false`. -/
noncomputable def RSA_Game_Ideal (D : RSADef W) (A : RSA_Adversary W) : SPComp Bool := do
  let ⟨_sk, pk⟩ ← D.keygen
  let x ← SPComp.sample W
  let y := D.rsa pk x
  let _x' ← A pk y
  SPComp.pure false

/-- RSA advantage: distinguishing advantage for the inversion game. -/
noncomputable def RSA_Advantage (D : RSADef W)
    (A : RSA_Adversary W) : ℝ≥0∞ :=
  Advantage (RSA_Game_Real D A) (RSA_Game_Ideal D A)

/-! ## IsPure Proofs -/

theorem RSA_Game_Real_isPure (D : RSADef W) (A : RSA_Adversary W)
    (hA : ∀ x y, SPComp.IsPure (A x y)) :
    SPComp.IsPure (RSA_Game_Real D A) := by
  unfold RSA_Game_Real
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_, pk⟩
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro x
  apply SPComp.bind_isPure (hA pk _); intro x'
  exact SPComp.pure_isPure _

end CatCrypt.Crypto.Assumptions

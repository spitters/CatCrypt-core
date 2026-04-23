/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.CryptoWord

/-!
# Decisional Diffie-Hellman (DDH) Assumption

This file defines the DDH assumption parametrically over any `CryptoWord W`,
following the pattern of `DL.lean` for discrete logarithm.

## DDH Game

The DDH game captures the difficulty of distinguishing:
- **Real**: `(g^a, g^b, g^{ab})` — the true DH shared secret
- **Ideal**: `(g^a, g^b, g^c)` — a random group element

At the abstract level with `Word : CryptoWord W`, the DDH game becomes:
- **Real**: sample `a, b`, give `(ecdh(a, G), ecdh(b, G), ecdh(a, ecdh(b, G)))` to adversary
- **Ideal**: sample `a, b, c`, give `(ecdh(a, G), ecdh(b, G), c)` to adversary

## Main definitions

* `DDHDef` — a Diffie-Hellman group (ecdh operation + key generation)
* `DDH_Game_Real` / `DDH_Game_Ideal` — the real/ideal DDH games
* `DDH_Advantage` — advantage of an adversary in breaking DDH

## Usage in EDHOC

EDHOC Method 3 (STAT-STAT) uses 3 DH operations:
1. Ephemeral-ephemeral: `ecdh(x, g_y)` — for `prk_2e`
2. Static-ephemeral: `ecdh(r, g_x)` — for `prk_3e2m`
3. Static-ephemeral: `ecdh(i, g_y)` — for `prk_4e3m`

Each DH operation contributes one `ε_ddh` to the security bound.

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| Game structure | `DDH_Game_Real`/`Ideal` | Boneh-Shoup Def. 11.2 |
| Advantage | `Advantage(Real, Ideal)` | `|Pr[W₀] - Pr[W₁]|` |
| Key generation | `DDHDef.keygen` | Implicit in group sampling |

**Equivalent formalizations:**
- EasyCrypt: `DDH` theory in `ec-toolbox/theories/crypto/DDH.ec`
- CryptoVerif: `DDH(G, Z, g, exp, exp', mult)` macro
- CatCrypt codebase variants:
  - `Examples/ElGamal.lean`: `DDH_real`/`DDH_ideal` over `CyclicGroup G` (group-theoretic)
  - `ElectionGuard/Security.lean`: `DDH_real`/`DDH_random` over `EGParams G` (election-specific)

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §11.4, Def. 11.2
* Katz & Lindell, *Introduction to Modern Cryptography*, §8.3, Def. 8.62
* Diffie & Hellman, *New Directions in Cryptography*, IEEE-IT 1976
* RFC 9528 — EDHOC, Section 9 (security considerations)
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## DDH Definition -/

/-- Abstract Diffie-Hellman group definition, parametric over `SampleableType W`.

- `ecdh a b` models scalar multiplication in the group
- `keygen` samples a key pair `(private, public)` -/
structure DDHDef (W : Type) [SampleableType W] where
  /-- DH key agreement: `ecdh(private_key, public_key)` → shared_secret.
  Models `p256_ecdh` in lakers' `Crypto` trait. -/
  ecdh : W → W → W
  /-- Key generation: produces `(private_key, public_key)`.
  Models `p256_generate_key_pair` in lakers' `Crypto` trait. -/
  keygen : SPComp (W × W)
  /-- Key generation is heap-independent. -/
  keygen_isPure : SPComp.IsPure keygen

/-! ## DDH Games -/

/-- Type of DDH adversary: receives a DH triple and must distinguish real from ideal. -/
abbrev DDH_Adversary (W : Type) := W → W → W → SPComp Bool

/-- DDH real game: adversary receives `(g^a, g^b, ecdh(a, g^b))`.
The third element is the true DH shared secret. -/
noncomputable def DDH_Game_Real (D : DDHDef W) (A : DDH_Adversary W) : SPComp Bool := do
  let ⟨a, g_a⟩ ← D.keygen
  let ⟨b, g_b⟩ ← D.keygen
  let shared := D.ecdh a g_b  -- = g^{ab}
  A g_a g_b shared

/-- DDH ideal game: adversary receives `(g^a, g^b, c)` where `c` is random. -/
noncomputable def DDH_Game_Ideal (D : DDHDef W) (A : DDH_Adversary W) : SPComp Bool := do
  let ⟨_, g_a⟩ ← D.keygen
  let ⟨_b, g_b⟩ ← D.keygen
  let c ← SPComp.sample W  -- random, independent of a, b
  A g_a g_b c

/-- DDH advantage: ability to distinguish `(g^a, g^b, g^{ab})` from `(g^a, g^b, random)`. -/
noncomputable def DDH_Advantage (D : DDHDef W) (A : DDH_Adversary W) : ℝ≥0∞ :=
  Advantage (DDH_Game_Real D A) (DDH_Game_Ideal D A)

/-! ## IsPure Proofs -/

theorem DDH_Game_Real_isPure (D : DDHDef W) (A : DDH_Adversary W)
    (hA : ∀ x y z, SPComp.IsPure (A x y z)) :
    SPComp.IsPure (DDH_Game_Real D A) := by
  unfold DDH_Game_Real
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨a, g_a⟩
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨b, g_b⟩
  exact hA g_a g_b (D.ecdh a g_b)

theorem DDH_Game_Ideal_isPure (D : DDHDef W) (A : DDH_Adversary W)
    (hA : ∀ x y z, SPComp.IsPure (A x y z)) :
    SPComp.IsPure (DDH_Game_Ideal D A) := by
  unfold DDH_Game_Ideal
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_, g_a⟩
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_b, g_b⟩
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro c
  exact hA g_a g_b c

end CatCrypt.Crypto.Assumptions

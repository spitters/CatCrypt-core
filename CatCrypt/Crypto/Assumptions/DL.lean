/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.PairingGroup
import CatCrypt.Crypto.Advantage

/-!
# Discrete Logarithm Assumption

This file defines the DL (Discrete Logarithm) assumption for pairing groups.
The DL assumption is used for the hiding property of KZG.

## Main definitions

* `DL_Game` — The DL game in G₁: adversary receives `g₁^x` and must find `x`
* `DL_Advantage` — Advantage of an adversary in breaking DL

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| Game structure | `DL_Game` | Boneh-Shoup Def. 10.4 |
| Advantage | `prTrue(DL_Game)` | `Pr[DLadv]` |
| Group | `PairingGroup P` | Cyclic group of prime order |

**Equivalent formalizations:**
- EasyCrypt: `DLog` theory in `ec-toolbox/theories/crypto/CDH_DDH.ec`
- CryptoVerif: `DL(G, Z, g, exp, exp')` macro

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §10.5, Def. 10.4
* Katz & Lindell, *Introduction to Modern Cryptography*, §9.3
* [Palak, Haines, *Formal Verification of KZG Polynomial Commitments*, ESORICS 2025]
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open PairingGroup
open scoped ENNReal

variable (P : PairingGroup)

/-! ## Discrete Logarithm Game -/

/-- Type of DL adversary: receives a group element h = g₁^x, must output x -/
abbrev DL_Adversary := P.G₁ → SPComp (ZMod P.p)

/-- The discrete log game in G₁: sample x, give g₁^x to adversary, check answer -/
noncomputable def DL_Game (A : DL_Adversary P) : SPComp Bool := do
  let x ← SPComp.sample (ZMod P.p)
  let h := P.g₁ ^ᵍ x
  let guess ← A h
  SPComp.pure (decide (guess = x))

/-- Advantage of adversary A in breaking the DL assumption -/
noncomputable def DL_Advantage (A : DL_Adversary P) : ℝ≥0∞ :=
  prTrue (DL_Game P A) Heap.empty

end CatCrypt.Crypto.Assumptions

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Crypto.Assumptions.PRP
public import CatCryptCore.Tactics.VC

/-!
# MAC Domain Extension

This file formalizes domain extension techniques for MACs, specifically
Encrypted CBC-MAC (ECBC-MAC) and CMAC, following Boneh-Shoup §6.4.

## Problem

Raw CBC-MAC is only secure for **fixed-length** messages. For
variable-length messages, an adversary can extend a valid MAC to a
longer message (length-extension attack). Domain extension techniques
fix this vulnerability.

## Constructions

### ECBC-MAC (Encrypted CBC-MAC)

ECBC-MAC uses two independent keys:
  `ecbc(k₁, k₂, m) = E(k₂, cbcmac(k₁, m))`

The final encryption with an independent key `k₂` prevents the
length-extension attack.

### CMAC (Cipher-based MAC)

CMAC avoids the second key by deriving two subkeys from the main key:
  - `k₁` = main CBC-MAC key
  - `k₂`, `k₃` = subkeys derived from `k₁` via `E(k₁, 0)`

The last block is XORed with a subkey before the final encryption,
depending on whether padding was needed.

## Security Bounds

* ECBC-MAC, block cipher a PRP: `ε_prp(B₁) + ε_prp(B₂) + (q(q-1)/2 + qℓ(qℓ-1)/2 +
  2(qℓ)²) / |B|` (`ecbc_prf_bound`)
* CMAC, block cipher a PRP: `ε_prp(B) + (σ+1)σ/2 / |B| + (4(σ+1)² + 1) / |B|`
  (`cmac_prf_bound`)

This file defines the constructions, their one-shot real/ideal games and
and advantages; its games take no query count. The
adaptive `q`-query PRF bound for ECBC-MAC over messages of at most `ℓ` blocks is
`ecbc_prf_bound` in `CatCrypt.Crypto.Constructions.ECBCPRF`, stated in the games of
`CatCryptCore.Crypto.PRPPRFSwitching`, where `ecbc_eq_ecbc_eval` identifies its
construction with `ecbc_eval`. The adaptive bound for CMAC over messages of total
length at most `σ` blocks is `cmac_prf_bound` in `CatCrypt.Crypto.Constructions.CMACPRF`.

## Cross-Validation

| Property | This file | Textbook | Standard |
|----------|-----------|----------|----------|
| ECBC-MAC def | `ECBCMAC` | BS Construction 6.4 | — |
| ECBC advantage | `ECBC_Advantage` | BS Thm. 6.3 | — |
| CMAC def | `cmac_eval`, `CMAC_Advantage` | BS §6.4.2 | NIST SP 800-38B |

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §6.4
* NIST SP 800-38B. *Recommendation for Block Cipher Modes of Operation:
  The CMAC Mode for Authentication.* 2005.
* Black, Rogaway. *CBC MACs for Arbitrary-Length Messages: The Three-Key
  Constructions.* CRYPTO 2000.
* Iwata, Kurosawa. *OMAC: One-Key CBC MAC.* FSE 2003.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.MACDomainExtension

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## CBC-MAC (Raw, Fixed-Length)

Raw CBC-MAC for reference. This is only secure for fixed-length messages.
For variable-length security, use ECBC-MAC or CMAC below. -/

/-- Block cipher parameters for MAC constructions.

    | Parameter | Role | Typical instantiation |
    |-----------|------|-----------------------|
    | `W` | block type | `{0,1}^128` |
    | `enc` | block cipher | AES |
    | `blockBits` | security parameter | 128 | -/
structure BlockCipherDef (W : Type) [SampleableType W] where
  /-- Block cipher: key → plaintext → ciphertext. -/
  enc : W → W → W
  /-- Block size in bits. -/
  blockBits : ℕ

/-- Raw CBC-MAC: chain the block cipher over message blocks.

    `cbcmac(k, [m₁, m₂, ..., mₗ])`:
    - `s₀ = 0` (or provided IV)
    - `sᵢ = E(k, sᵢ₋₁ ⊕ mᵢ)`
    - output `sₗ`

    Only secure for fixed-length messages. -/
def raw_cbcmac {W : Type} [CryptoWord W]
    (B : BlockCipherDef W) (k : W) (iv : W) : List W → W
  | [] => iv
  | block :: rest =>
    let chained := B.enc k (CryptoWord.wxor iv block)
    raw_cbcmac B k chained rest

@[simp]
theorem raw_cbcmac_nil {W : Type} [CryptoWord W]
    (B : BlockCipherDef W) (k iv : W) :
    raw_cbcmac B k iv [] = iv := rfl

@[simp]
theorem raw_cbcmac_cons {W : Type} [CryptoWord W]
    (B : BlockCipherDef W) (k iv : W) (block : W) (rest : List W) :
    raw_cbcmac B k iv (block :: rest) =
    raw_cbcmac B k (B.enc k (CryptoWord.wxor iv block)) rest := rfl

/-! ## ECBC-MAC (Encrypted CBC-MAC)

ECBC-MAC (BS Construction 6.4) adds a final encryption with an
independent key to prevent length-extension attacks:

  `ecbc(k₁, k₂, m) = E(k₂, cbcmac(k₁, m))`

This makes CBC-MAC secure for variable-length messages. -/

/-- Encrypted CBC-MAC (ECBC-MAC): CBC-MAC with final encryption.

    Uses two independent keys:
    - `k₁` : CBC-MAC key (chaining)
    - `k₂` : final encryption key (prevents length extension)

    `ecbc(k₁, k₂, m) = E(k₂, cbcmac(k₁, m))` -/
structure ECBCMAC (W : Type) [CryptoWord W] where
  /-- Underlying block cipher. -/
  cipher : BlockCipherDef W

/-- Evaluate ECBC-MAC on a message.

    `ecbc_eval E k₁ k₂ iv msg = E(k₂, cbcmac(k₁, msg))` -/
def ecbc_eval {W : Type} [CryptoWord W]
    (E : ECBCMAC W) (k₁ k₂ : W) (iv : W) (msg : List W) : W :=
  let inner := raw_cbcmac E.cipher k₁ iv msg
  E.cipher.enc k₂ inner

/-! ## ECBC-MAC Security Games -/

/-- ECBC-MAC real game: sample two independent keys, evaluate ECBC. -/
noncomputable def ecbc_real {W : Type} [CryptoWord W]
    (E : ECBCMAC W) (iv : W) (msg : List W) : SPComp W := do
  let k₁ ← SPComp.sample W
  let k₂ ← SPComp.sample W
  SPComp.pure (ecbc_eval E k₁ k₂ iv msg)

/-- ECBC-MAC advantage: distinguishing real tag from random. -/
noncomputable def ECBC_Advantage {W : Type} [CryptoWord W]
    (E : ECBCMAC W) (iv : W) (msg : List W)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (ecbc_real E iv msg) (SPComp.sample W) A

/-! ## CMAC (Cipher-based MAC)

CMAC (NIST SP 800-38B) avoids the second key of ECBC-MAC by deriving
subkeys from the main key. This saves one key's worth of key material.

CMAC uses:
- Main key `k` for CBC-MAC chaining
- Subkey `k₂ = L · 2` where `L = E(k, 0)` (for complete last block)
- Subkey `k₃ = L · 4` (for padded last block)

The last message block is XORed with the appropriate subkey before
the final CBC-MAC step. -/

/-- CMAC evaluation (simplified): uses subkey XOR on the last block.

    `cmac_eval B k subkey iv msg`:
    1. CBC-MAC all blocks except the last
    2. XOR the last block with `subkey`
    3. Apply one more block cipher call

    For simplicity, we model the single-subkey case (complete last block).
    The padded case uses a different subkey but the same structure. -/
def cmac_eval {W : Type} [CryptoWord W]
    (B : BlockCipherDef W) (k : W) (subkey : W) (iv : W) : List W → W
  | [] => B.enc k (CryptoWord.wxor iv subkey)
  | [last] => B.enc k (CryptoWord.wxor (CryptoWord.wxor iv last) subkey)
  | block :: rest =>
    let chained := B.enc k (CryptoWord.wxor iv block)
    cmac_eval B k subkey chained rest

/-! ## CMAC games

The one-shot games of CMAC. The adaptive PRF bound of CMAC (OMAC1, Iwata-Kurosawa
FSE 2003), stated over a block cipher with doubling in `GF(2^n)`, is
`CMACPRF.cmac_prf_bound`. -/

/-- CMAC real game: sample key, derive subkey, evaluate CMAC. -/
noncomputable def cmac_real {W : Type} [CryptoWord W]
    (B : BlockCipherDef W) (zero iv : W) (msg : List W) : SPComp W := do
  let k ← SPComp.sample W
  let subkey := B.enc k zero
  SPComp.pure (cmac_eval B k subkey iv msg)

/-- CMAC ideal game: uniformly random tag. -/
noncomputable def cmac_ideal (W : Type) [SampleableType W]
    (_msg : List W) : SPComp W :=
  SPComp.sample W

/-- CMAC advantage. -/
noncomputable def CMAC_Advantage {W : Type} [CryptoWord W]
    (B : BlockCipherDef W) (zero iv : W) (msg : List W)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (cmac_real B zero iv msg) (cmac_ideal W msg) A

end CatCrypt.Crypto.Constructions.MACDomainExtension

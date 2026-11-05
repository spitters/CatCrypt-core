/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Libcrux.Extraction.Libcrux_specs
public import CatCryptCore.Crypto.Libcrux.ConcreteInstances
public import CatCryptCore.Crypto.HKDF_UC

/-!
# HKDF-SHA256 Bridge: libcrux-specs → CatCrypt UC Security

Bridges the concrete HKDF-SHA256 implementation from libcrux-specs to
CatCrypt's abstract `HKDFDef` typeclass. The game bound `hkdf_advantage_bound`
at the concrete implementation is registered as a `GameAdvBoundC` instance, and
concrete UC emulation follows by `UCFromGameC.uc`.

## Architecture

```
libcrux-specs/src/hkdf.rs          (Rust, hkdf_extract/expand)
        ↓  opaque Lean defs
Extraction/Libcrux_specs.lean       (hkdf_extract_32, hkdf_expand_32)
        ↓  field assignment
Bridge_HKDF.lean (this file)        (concreteHKDF : HKDFDef)
        ↓  hkdf_advantage_bound, UCFromGameC.uc
HKDF_UC.lean                        (game bound)
```

## Key Results

| Definition / Theorem | Role |
|-----|------|
| `concreteHKDF` | `HKDFDef (Vector UInt8 32)` from libcrux-specs |
| `concreteHKDF_extract_eq` | `concreteHKDF.extract = hkdf_extract_32` |
| `concreteHKDF_expand_eq` | `concreteHKDF.expand = hkdf_expand_32` |
| `concrete_hkdf_uc_secure` | UC theorem for libcrux-specs HKDF |

## Cryptographic Assumptions

No PRF assumption on HMAC-SHA256 is stated: the bound of
`concrete_hkdf_uc_secure` is the sum of the Extract and Expand advantages of
explicit reductions built from the adversary and the environment.

## References

* RFC 5869 — HKDF
* `CatCryptCore.Crypto.HKDF_UC` — abstract security proof
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Libcrux.Bridge_HKDF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.HKDF_UC
open CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs
open CatCrypt.Crypto.Libcrux.ConcreteInstances
open scoped ENNReal

/-! ## Concrete HKDF Definition -/

/-- Concrete HKDF-SHA256 from libcrux-specs.

Uses the opaque `hkdf_extract_32` and `hkdf_expand_32` from the extraction.
These correspond to the Rust implementations:
- `hkdf_extract_32(salt, ikm) = hmac_sha256(salt, ikm)` (RFC 5869 §2.2)
- `hkdf_expand_32(prk, info) = hmac_sha256(prk, info || 0x01)[0..32]` (RFC 5869 §2.3) -/
noncomputable def concreteHKDF : HKDFDef (Vector UInt8 32) where
  extract := hkdf_extract_32
  expand := hkdf_expand_32

/-! ## Connecting Lemmas -/

@[simp]
theorem concreteHKDF_extract_eq : concreteHKDF.extract = hkdf_extract_32 := rfl

@[simp]
theorem concreteHKDF_expand_eq : concreteHKDF.expand = hkdf_expand_32 := rfl

/-! ## UC Security Theorem -/

open CatCrypt.Crypto.UCConcrete

/-- Every distinguisher `D` separates the HKDF games of `concreteHKDF` at the input
`(ikm, info)` by at most `hkdfBound concreteHKDF (ikm, info) D`, the HMAC-SHA256
Extract advantage of `hkdfExtractReduction` plus the Expand advantage of `D`
(`hkdf_advantage_bound`). -/
instance libcruxHKDFGameAdvBoundC :
    GameAdvBoundC (fun i : Vector UInt8 32 × Vector UInt8 32 => hkdf_real concreteHKDF i.1 i.2)
      (fun _ : Vector UInt8 32 × Vector UInt8 32 => hkdf_ideal (W := Vector UInt8 32))
      (hkdfBound concreteHKDF) :=
  ⟨fun i D => hkdf_advantage_bound concreteHKDF i.1 i.2 D⟩

/-- **Concrete HKDF-SHA256 UC security from libcrux-specs**, `UCFromGameC.uc` at
`libcruxHKDFGameAdvBoundC`, simulator `S = A`.

The libcrux-specs HKDF-SHA256 implementation concretely UC-emulates the ideal
random KDF functionality with bound `hkdfBound concreteHKDF`: the HMAC-SHA256
Extract advantage of `hkdfExtractReduction` plus the Expand advantage, at the
distinguisher built from the adversary and the environment. -/
theorem concrete_hkdf_uc_secure (V : Type) :
    UCEmulatesCSim (hkdfSpec (Vector UInt8 32) V)
      (hkdfReal concreteHKDF) hkdfIdeal id (gameUCBound (hkdfBound concreteHKDF)) :=
  (inferInstance : UCFromGameC
    (fun i : Vector UInt8 32 × Vector UInt8 32 => hkdf_real concreteHKDF i.1 i.2)
    (fun _ => hkdf_ideal) V (hkdfBound concreteHKDF)).uc

/-! ## Verification -/

-- concreteHKDF fields are definitionally equal to extraction functions
example : concreteHKDF.extract = hkdf_extract_32 := rfl
example : concreteHKDF.expand = hkdf_expand_32 := rfl

end CatCrypt.Crypto.Libcrux.Bridge_HKDF

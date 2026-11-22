/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# libcrux-specs: HMAC and HKDF at the lengths of the Signal ratchet

The key-derivation functions of the Signal Double Ratchet call HMAC-SHA256 on a one-byte
message (`KDF_CK`) and HKDF-SHA256 Expand for 64 bytes under the 14-byte info string
`"WhisperRatchet"` (`KDF_RK`). The constants below are the fixed-length variants at these
lengths, of the same kind as `hmac_sha256_32` and `hkdf_expand_32` of `Libcrux_specs`: opaque
inhabited terms at the stated Lean signatures. No property of them is assumed, so a theorem
stated over them holds for every function of these signatures.

## Main definitions

* `hmac_sha256_1` — HMAC-SHA256 under a 32-byte key on a one-byte message
* `hkdf_expand_64` — HKDF-SHA256 Expand of 64 bytes from a 32-byte PRK under a 14-byte info
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs

/-- HMAC-SHA256 under a 32-byte key on a one-byte message, as an opaque function. -/
opaque hmac_sha256_1 : Vector UInt8 32 → Vector UInt8 1 → Vector UInt8 32

/-- HKDF-SHA256 Expand of 64 bytes from a 32-byte PRK under a 14-byte info string, as an opaque
function. -/
opaque hkdf_expand_64 : Vector UInt8 32 → Vector UInt8 14 → Vector UInt8 64

end CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs

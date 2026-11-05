/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Crypto.AKE.X3DH.Extraction.X3dh_haxpipe
public import CatCryptCore.Crypto.EdDSA.Bridge
public import CatCryptCore.Crypto.EdDSA.Extraction.Eddsa_haxpipe

/-!
# X3DH EdDSA Bridge: X3DH Signing through the Extracted EdDSA

Defines the `sign` and `verify` operations of the X3DH dependency record through the
hax-extracted EdDSA code (`Eddsa.sign`, `Eddsa.verify`) under an `EddsaDeps` instance.

## Architecture

```
Libcrux/GroupOps.lean            (ed25519_* opaque ops)
        ↓
EdDSA/Bridge.lean                (concreteEddsaDeps : EddsaDeps)
        ↓  Eddsa.sign / Eddsa.verify
X3DH/EdDSA_Bridge.lean (this)    (x3dh_sign / x3dh_verify using EdDSA)
        ↓
X3DH/SurfaceDeps.lean            (defaultX3dhDeps: sign and verify fields)
```

## Nonce

The signing nonce is `nonce_hash sk msg`, an opaque deterministic function of the private
key and the message, in the manner of Ed25519 (RFC 8032). Signal's XEdDSA signs with a
nonce that additionally hashes 64 random bytes; `x3dh_sign` is the deterministic variant.
No security property of the signature is stated in this file.

## References

* Signal XEdDSA specification
* RFC 8032 — EdDSA
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.X3DH.EdDSA_Bridge

open CatCrypt.Crypto.EdDSA.Bridge
open Eddsa

/-! ## Nonce Hash -/

/-- Deterministic nonce derivation: `nonce = hash(sk, msg)`, an opaque function of the
    private key and the message. -/
opaque nonce_hash : Array Int → Array Int → Array Int

/-! ## X3DH Sign/Verify via EdDSA -/

/-- X3DH signing through the extracted EdDSA.

    `sign(sk, msg) = EdDSA.sign(sk, nonce_hash(sk, msg), msg)`

    The signature is the concatenation of `(R, s)` components. -/
def x3dh_sign [EddsaDeps] (sk msg : Array Int) : Array Int :=
  let k := nonce_hash sk msg
  let sig := Eddsa.sign sk k msg
  -- Concatenate R and s into a single array (64 bytes total)
  sig.1 ++ sig.2

/-- X3DH verification through the extracted EdDSA.

    `verify(pk, msg, sig_bytes) = EdDSA.verify(pk, msg, (R, s))`

    The signature bytes are split into R (first 32) and s (second 32). -/
def x3dh_verify [EddsaDeps] (pk msg sig_bytes : Array Int) : Bool :=
  let r := sig_bytes.toList.take 32 |>.toArray
  let s := sig_bytes.toList.drop 32 |>.toArray
  Eddsa.verify pk msg (r, s)

end CatCrypt.Crypto.Signal.X3DH.EdDSA_Bridge

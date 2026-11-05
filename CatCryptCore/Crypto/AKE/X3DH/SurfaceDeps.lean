/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHPassive
public import CatCryptCore.Crypto.AKE.X3DHPassiveHops
public import CatCryptCore.Crypto.Libcrux.Bridge_X25519
public import CatCryptCore.Crypto.Libcrux.Bridge_HKDF
public import CatCryptCore.Crypto.AKE.X3DH.Extraction.X3dh_haxpipe
public import CatCryptCore.Crypto.AKE.X3DH.EdDSA_Bridge
public import CatCryptCore.Crypto.AKE.X3DH.ExtractedCorrespondence
public import CatCryptCore.Hax.ReprBridge

/-!
# X3DH SurfaceDeps: Extraction-to-Security Bridge

Wraps the opaque libcrux-specs primitives into the dependency record `X3dh.X3dhDeps` of the
extracted X3DH code and derives the end-to-end bound of the extracted handshake from the
abstract reduction.

## Architecture

```
x3dh-hax (Rust) → haxpipeT → X3dh.create_bundle, X3dh.initiate (Array Int)
                                             │  defaultX3dhDeps: x25519_base,
                                             │  x25519_scalarmult, x3dhKdf through
                                             │  vecToArrayInt / decodeKey; Ed25519
                                             ▼
          defaultX3dhHom : X3dhHom toX3DHParams vecToArrayInt x25519_base
                                             │  x3dh_extracted_eq
                                             ▼
     x3dh_extracted toX3DHParams vecToArrayInt = (x3dh_real toX3DHParams).map encOut
                                             │  advantageA_map, x3dh_advantage_le
                                             ▼
              x3dh_extracted_e2e_secure : bound x3dhKIReductionBound
```

The extraction computes on byte arrays and the model on `Vector UInt8 32`. The instance
`defaultX3dhDeps` decodes its arguments (`decodeKey`, total, the inverse of `vecToArrayInt`),
applies the libcrux-specs operation and encodes the result, so that `vecToArrayInt` carries
each operation of the extraction to the model (`defaultX3dhHom`).

## Key Primitives

- `dh`: X25519 (`x25519_scalarmult` via `concreteDDH_X25519`)
- `kdf`: HKDF-SHA256 composition on the 4 DH shared secrets
- `sign`, `verify`: Ed25519 (`EdDSA_Bridge.x3dh_sign`, `EdDSA_Bridge.x3dh_verify`)

## Security Bound

The DDH advantages of four hop reductions and the KDF advantage of one reduction, at the KI
adversary of the distinguisher precomposed with the encoding.

## References

* Marlinspike, Perrin — *The X3DH Key Agreement Protocol*, 2016
* the Rust crate `x3dh-hax` — protocol source
* `X3DH/ExtractedCorrespondence.lean` — the extracted session and its bound
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.X3DH.SurfaceDeps

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Signal.X3DH
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.HKDF_UC
open CatCrypt.Crypto.Libcrux.Bridge_X25519
open CatCrypt.Crypto.Libcrux.Bridge_HKDF
open CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs
open CatCrypt.Hax.ReprBridge
open scoped ENNReal

/-- The ghost record of the typestate FSM (`X3dhGhost` of the Rust crate
    `x3dh-hax`): the ghost state is the ordered trace of
    communication actions. Each hook appends the header `[kind, tag, n]`
    followed by the `n` payload entries, with `kind` `0` for `send_init` (tag
    `0`, payload the three init-message components concatenated) and `2` for
    `event`. -/
def x3dhGhostRecord (kind : Int) (ghost : Array Int) (tag : Int) (payload : Array Int) :
    Array Int :=
  ghost ++ #[kind, tag, payload.size] ++ payload

/-- A byte array read as a 32-byte key: entry `i` truncated to a byte, `0` past the end. The
decoding is total and inverts `vecToArrayInt` (`decodeKey_vecToArrayInt`). -/
def decodeKey (a : Array Int) : Vector UInt8 32 :=
  Vector.ofFn fun i => (a.getD i 0).toNat.toUInt8

/-- `decodeKey` inverts `vecToArrayInt`. -/
theorem decodeKey_vecToArrayInt (v : Vector UInt8 32) : decodeKey (vecToArrayInt v) = v := by
  ext i hi
  simp [decodeKey, vecToArrayInt]

/-! ## Surface KDF -/

/-- Signal X3DH KDF: combines 4 DH shared secrets via a tree of HKDF-Extract
operations. Models `HKDF(0 || DH1 || DH2 || DH3 || DH4)` as a composition
tree, which is standard for modelling multi-input PRF extraction. -/
noncomputable def x3dhKdf
    (dh1 dh2 dh3 dh4 : Vector UInt8 32) : Vector UInt8 32 :=
  concreteHKDF.extract
    (concreteHKDF.extract dh1 dh2)
    (concreteHKDF.extract dh3 dh4)

/-! ## Parameter Record -/

/-- Concrete X3DH parameters using libcrux-specs X25519 + HKDF-SHA256.

The `dh` field is the abstract DDH record from `Bridge_X25519`; the `kdf`
field composes HKDF extracts. Key generation samples a private key `sk` and
returns `(sk, x25519_base sk)`. -/
noncomputable def toX3DHParams : X3DHParams (Vector UInt8 32) where
  dh := concreteDDH_X25519
  kdf := x3dhKdf

/-! ## Extraction instance -/

/-- The operations of the extraction on byte arrays. `dh_pub`, `dh` and `kdf` are
`x25519_base`, `x25519_scalarmult` and `x3dhKdf` on the decoded keys, encoded back by
`vecToArrayInt`; `sign` and `verify` are Ed25519 through `EdDSA_Bridge`; the ghost hooks
`event` and `send_init` append to the trace (`x3dhGhostRecord`). -/
noncomputable instance defaultX3dhDeps : X3dh.X3dhDeps where
  dh_pub a := vecToArrayInt (x25519_base (decodeKey a))
  sign := EdDSA_Bridge.x3dh_sign
  verify := EdDSA_Bridge.x3dh_verify
  dh a b := vecToArrayInt (x25519_scalarmult (decodeKey a) (decodeKey b))
  kdf a b c d :=
    vecToArrayInt (x3dhKdf (decodeKey a) (decodeKey b) (decodeKey c) (decodeKey d))
  event := x3dhGhostRecord 2
  send_init ghost msg := x3dhGhostRecord 0 ghost 0 (msg.1 ++ msg.2.1 ++ msg.2.2)

/-- `vecToArrayInt` carries the operations of `defaultX3dhDeps` to those of `toX3DHParams`,
with public-key map `x25519_base`. -/
theorem defaultX3dhHom :
    ExtractedCorrespondence.X3dhHom toX3DHParams vecToArrayInt x25519_base where
  dh_pub x := by
    change vecToArrayInt (x25519_base (decodeKey (vecToArrayInt x))) = _
    rw [decodeKey_vecToArrayInt]
  dh x y := by
    change vecToArrayInt (x25519_scalarmult (decodeKey (vecToArrayInt x))
      (decodeKey (vecToArrayInt y))) = _
    rw [decodeKey_vecToArrayInt, decodeKey_vecToArrayInt]
    rfl
  kdf a b c d := by
    change vecToArrayInt (x3dhKdf (decodeKey (vecToArrayInt a)) (decodeKey (vecToArrayInt b))
      (decodeKey (vecToArrayInt c)) (decodeKey (vecToArrayInt d))) = _
    simp only [decodeKey_vecToArrayInt]
    rfl

/-! ## End-to-end security of the extracted handshake -/

/-- **X3DH end-to-end security of the extracted handshake** with libcrux X25519 and
HKDF-SHA256.

Given X25519 Diffie-Hellman correctness (`X25519Commutes`), the advantage of every
distinguisher `D` between the session computed by the extracted `create_bundle` and `initiate`
of `x3dh-hax` at `defaultX3dhDeps` (`x3dh_extracted`) and the encoded ideal session is at most
`x3dhKIReductionBound toX3DHParams` at the KI adversary of `D` precomposed with the encoding:
the DDH advantages of the four hop reductions plus the KDF advantage of the KDF reduction.
The statement is an advantage bound between two distributions, not a UC emulation.

Delegates to `ExtractedCorrespondence.x3dh_extracted_advantage_le` at `defaultX3dhHom`. -/
theorem x3dh_extracted_e2e_secure (hX : X25519Commutes)
    (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA (ExtractedCorrespondence.x3dh_extracted toX3DHParams vecToArrayInt)
        ((x3dh_ideal toX3DHParams).map (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      Session.X3DHHops.x3dhKIReductionBound toX3DHParams
        (Session.X3DHHops.kiAdversaryOfDistinguisher toX3DHParams
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) :=
  ExtractedCorrespondence.x3dh_extracted_advantage_le defaultX3dhHom rfl hX D

end CatCrypt.Crypto.Signal.X3DH.SurfaceDeps

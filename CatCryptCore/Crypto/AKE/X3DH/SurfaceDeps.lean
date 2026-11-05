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
                                             │  x25519_scalarmult, x3dhKdfCtx through
                                             │  vecToArrayInt / decodeKey / decodeCtx
                                             ▼
   defaultX3dhHom : X3dhHom concreteDDH_X25519 x3dhEncCtx x3dhKdfModel vecToArrayInt x25519_base
                                             │  x3dh_extracted_eq
                                             ▼
   x3dh_extracted concreteDDH_X25519 vecToArrayInt (x3dhEncCtx (sid, a, b))
     = (x3dh_real (toX3DHParamsAt sid a b)).map encOut
                                             │  advantageA_map, x3dh_advantage_le
                                             ▼
              x3dh_extracted_e2e_secure : bound x3dhKIReductionBound
```

The extraction computes on byte arrays and the model on `Vector UInt8 32`. The instance
`defaultX3dhDeps` decodes its arguments (`decodeKey`, total, the inverse of `vecToArrayInt`),
applies the libcrux-specs operation and encodes the result, so that `vecToArrayInt` carries
each operation of the extraction to the model (`defaultX3dhHom`). The session context
`(sid, initiator, responder)` is encoded as the array of its three numbers (`x3dhEncCtx`); the
KDF reads it as a 32-byte block, eight little-endian bytes per number (`decodeCtx`), and
extracts it with the first node of its HKDF tree.

## Key Primitives

- `dh`: X25519 (`x25519_scalarmult` via `concreteDDH_X25519`)
- `kdf`: HKDF-SHA256 composition on the session context and the 4 DH shared secrets
- `sign`, `verify`: Ed25519 (`EdDSA_Bridge.x3dh_sign`, `EdDSA_Bridge.x3dh_verify`)

## Security Bound

The DDH advantages of four hop reductions and the KDF advantage of one reduction, at the KI
adversary of the distinguisher precomposed with the encoding.

## References

* Marlinspike, Perrin — *The X3DH Key Agreement Protocol*, 2016
* the Rust crate `x3dh-hax` of https://github.com/spitters/signal-hax — protocol source
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
open CatCrypt.Crypto.UCTransparent.FAKE (SessionId PartyId)
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

/-- The X3DH KDF with a session context: the 32-byte context block `ctx` is extracted with the
first node `Extract(DH1, DH2)` of the tree of `x3dhKdf`. -/
noncomputable def x3dhKdfCtx
    (ctx dh1 dh2 dh3 dh4 : Vector UInt8 32) : Vector UInt8 32 :=
  concreteHKDF.extract
    (concreteHKDF.extract ctx (concreteHKDF.extract dh1 dh2))
    (concreteHKDF.extract dh3 dh4)

/-- The X3DH KDF with a session context and without the one-time prekey: the three
Diffie-Hellman values `DH1`, `DH2`, `DH3` and the context block `ctx` combined in the form of
`x3dhKdfCtx`. -/
noncomputable def x3dhKdf3Ctx (ctx dh1 dh2 dh3 : Vector UInt8 32) : Vector UInt8 32 :=
  concreteHKDF.extract (concreteHKDF.extract ctx (concreteHKDF.extract dh1 dh2)) dh3

/-! ## Session contexts -/

/-- The byte-array encoding of a session context `(sid, initiator, responder)`: the array of
its three numbers. -/
def x3dhEncCtx (c : ExtractedCorrespondence.X3dhCtx) : Array Int :=
  #[(c.1 : Int), (c.2.1 : Int), (c.2.2 : Int)]

/-- A context array read as a 32-byte block: byte `i` is byte `i % 8` (little-endian) of entry
`i / 8`, `0` past the end. On numbers below `2 ^ 64` the block of `x3dhEncCtx c` determines
`c`. -/
def decodeCtx (a : Array Int) : Vector UInt8 32 :=
  Vector.ofFn fun i => ((a.getD (i.val / 8) 0).toNat / 256 ^ (i.val % 8)).toUInt8

/-- The model KDF at a session context: `x3dhKdfCtx` at the block of the encoded context. -/
noncomputable def x3dhKdfModel (c : ExtractedCorrespondence.X3dhCtx) :
    Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 :=
  x3dhKdfCtx (decodeCtx (x3dhEncCtx c))

/-- The model KDF without the one-time prekey at a session context: `x3dhKdf3Ctx` at the block
of the encoded context. -/
noncomputable def x3dhKdf3Model (c : ExtractedCorrespondence.X3dhCtx) :
    Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 :=
  x3dhKdf3Ctx (decodeCtx (x3dhEncCtx c))

/-! ## Parameter Record -/

/-- Concrete X3DH parameters using libcrux-specs X25519 + HKDF-SHA256.

The `dh` field is the abstract DDH record from `Bridge_X25519`; the `kdf`
field composes HKDF extracts. Key generation samples a private key `sk` and
returns `(sk, x25519_base sk)`. -/
noncomputable def toX3DHParams : X3DHParams (Vector UInt8 32) where
  dh := concreteDDH_X25519
  kdf := x3dhKdf

/-- The concrete X3DH parameters of the session `sid` between the initiator `a` and the
responder `b`: X25519 and the model KDF `x3dhKdfModel` at the context `(sid, a, b)`. -/
noncomputable def toX3DHParamsAt (sid : SessionId) (a b : PartyId) :
    X3DHParams (Vector UInt8 32) :=
  ExtractedCorrespondence.ctxParams concreteDDH_X25519 x3dhKdfModel (sid, a, b)

/-! ## Extraction instance -/

/-- The operations of the extraction on byte arrays. `dh_pub`, `dh`, `kdf` and `kdf3` are
`x25519_base`, `x25519_scalarmult`, `x3dhKdfCtx` and `x3dhKdf3Ctx` on the decoded context and
keys, encoded back by `vecToArrayInt`; `sign` and `verify` are Ed25519 through
`EdDSA_Bridge`; the ghost hooks `event` and `send_init` append to the trace
(`x3dhGhostRecord`). -/
noncomputable instance defaultX3dhDeps : X3dh.X3dhDeps where
  dh_pub a := vecToArrayInt (x25519_base (decodeKey a))
  sign := EdDSA_Bridge.x3dh_sign
  verify := EdDSA_Bridge.x3dh_verify
  dh a b := vecToArrayInt (x25519_scalarmult (decodeKey a) (decodeKey b))
  kdf ctx a b c d := vecToArrayInt
    (x3dhKdfCtx (decodeCtx ctx) (decodeKey a) (decodeKey b) (decodeKey c) (decodeKey d))
  kdf3 ctx a b c :=
    vecToArrayInt (x3dhKdf3Ctx (decodeCtx ctx) (decodeKey a) (decodeKey b) (decodeKey c))
  event := x3dhGhostRecord 2
  send_init ghost msg := x3dhGhostRecord 0 ghost 0 (msg.1 ++ msg.2.1 ++ msg.2.2)

/-- `vecToArrayInt` and `x3dhEncCtx` carry the operations of `defaultX3dhDeps` to X25519 and
the model KDF `x3dhKdfModel`, with public-key map `x25519_base`. -/
theorem defaultX3dhHom :
    ExtractedCorrespondence.X3dhHom concreteDDH_X25519 x3dhEncCtx x3dhKdfModel vecToArrayInt
      x25519_base where
  dh_pub x := by
    change vecToArrayInt (x25519_base (decodeKey (vecToArrayInt x))) = _
    rw [decodeKey_vecToArrayInt]
  dh x y := by
    change vecToArrayInt (x25519_scalarmult (decodeKey (vecToArrayInt x))
      (decodeKey (vecToArrayInt y))) = _
    rw [decodeKey_vecToArrayInt, decodeKey_vecToArrayInt]
    rfl
  kdf c a b d e := by
    change vecToArrayInt (x3dhKdfCtx (decodeCtx (x3dhEncCtx c)) (decodeKey (vecToArrayInt a))
      (decodeKey (vecToArrayInt b)) (decodeKey (vecToArrayInt d))
      (decodeKey (vecToArrayInt e))) = _
    simp only [decodeKey_vecToArrayInt]
    rfl

/-- `vecToArrayInt` and `x3dhEncCtx` carry `kdf3` of `defaultX3dhDeps` to `x3dhKdf3Model`. -/
theorem defaultX3dhKdf3Hom :
    ExtractedCorrespondence.X3dhKdf3Hom x3dhEncCtx vecToArrayInt x3dhKdf3Model := by
  intro c a b d
  change vecToArrayInt (x3dhKdf3Ctx (decodeCtx (x3dhEncCtx c)) (decodeKey (vecToArrayInt a))
    (decodeKey (vecToArrayInt b)) (decodeKey (vecToArrayInt d))) = _
  simp only [decodeKey_vecToArrayInt]
  rfl

/-! ## End-to-end security of the extracted handshake -/

/-- **X3DH end-to-end security of the extracted handshake** with libcrux X25519 and
HKDF-SHA256, in the session `sid` between the initiator `a` and the responder `b`.

Given X25519 Diffie-Hellman correctness (`X25519Commutes`), the advantage of every
distinguisher `D` between the session computed by the extracted `create_bundle` and `initiate`
of `x3dh-hax` at `defaultX3dhDeps` and the context `x3dhEncCtx (sid, a, b)` (`x3dh_extracted`)
and the encoded ideal session is at most `x3dhKIReductionBound (toX3DHParamsAt sid a b)` at the
KI adversary of `D` precomposed with the encoding: the DDH advantages of the four hop
reductions plus the KDF advantage of the KDF reduction, for the model KDF at the context
`(sid, a, b)`. The statement is an advantage bound between two distributions, not a UC
emulation.

Delegates to `ExtractedCorrespondence.x3dh_extracted_advantage_le` at `defaultX3dhHom`. -/
theorem x3dh_extracted_e2e_secure (hX : X25519Commutes) (sid : SessionId) (a b : PartyId)
    (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA
        (ExtractedCorrespondence.x3dh_extracted concreteDDH_X25519 vecToArrayInt
          (x3dhEncCtx (sid, a, b)))
        ((x3dh_ideal (toX3DHParamsAt sid a b)).map
          (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      Session.X3DHHops.x3dhKIReductionBound (toX3DHParamsAt sid a b)
        (Session.X3DHHops.kiAdversaryOfDistinguisher (toX3DHParamsAt sid a b)
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) :=
  ExtractedCorrespondence.x3dh_extracted_advantage_le defaultX3dhHom rfl hX sid a b D

/-- **X3DH end-to-end security of the extracted handshake without the one-time prekey**, with
libcrux X25519 and HKDF-SHA256, in the session `sid` between the initiator `a` and the
responder `b`.

Given `X25519Commutes`, the advantage of every distinguisher `D` between the session computed
by the extracted `create_bundle` and `initiate` at `use_opk = false` and the context
`x3dhEncCtx (sid, a, b)` and the encoded ideal session is at most `x3dhKIReductionBound` of
`noOpkParams (toX3DHParamsAt sid a b) (x3dhKdf3Model (sid, a, b))`, the parameters whose KDF is
the three-value model KDF at the context, at the KI adversary of `D` precomposed with the
encoding. The statement is an advantage bound between two distributions, not a UC
emulation. -/
theorem x3dh_extracted_noOpk_e2e_secure (hX : X25519Commutes) (sid : SessionId)
    (a b : PartyId) (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA
        (ExtractedCorrespondence.x3dh_extractedAt concreteDDH_X25519 vecToArrayInt
          (x3dhEncCtx (sid, a, b)) false)
        ((x3dh_ideal (toX3DHParamsAt sid a b)).map
          (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      Session.X3DHHops.x3dhKIReductionBound
        (ExtractedCorrespondence.noOpkParams (toX3DHParamsAt sid a b)
          (x3dhKdf3Model (sid, a, b)))
        (Session.X3DHHops.kiAdversaryOfDistinguisher
          (ExtractedCorrespondence.noOpkParams (toX3DHParamsAt sid a b)
            (x3dhKdf3Model (sid, a, b)))
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) :=
  ExtractedCorrespondence.x3dh_extracted_noOpk_advantage_le defaultX3dhHom defaultX3dhKdf3Hom
    rfl hX sid a b D

end CatCrypt.Crypto.Signal.X3DH.SurfaceDeps

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
public import CatCryptCore.Crypto.AKE.X3DH.PassiveG25519
public import CatCryptCore.Crypto.KeyAgreement.Curve25519BasePoint
public import CatCryptCore.Crypto.KeyAgreement.Curve25519DHGroup
public import CatCryptCore.Hax.ReprBridge

/-!
# X3DH SurfaceDeps: Extraction-to-Security Bridge

Wraps an X25519 scalar multiplication `sm` and base-point function `bp`, with the libcrux-specs
HKDF-SHA256 and Ed25519, into the dependency record `X3dh.X3dhDeps` of the extracted X3DH code
(`x3dhDepsOf sm bp`) and derives the end-to-end bound of the extracted handshake from the
abstract reduction. The instance `defaultX3dhDeps` takes the opaque libcrux functions
`x25519_scalarmult`, `x25519_base`, and `specX3dhDeps` the RFC 7748 specification
`Spec.x25519_spec`, `Spec.x25519_base_spec`.

## Architecture

```
x3dh-hax (Rust) → haxpipeT → X3dh.create_bundle, X3dh.initiate (Array Int)
                                             │  x3dhDepsOf sm bp: bp, sm,
                                             │  x3dhKdfCtx through
                                             │  vecToArrayInt / decodeKey / decodeCtx,
                                             │  valid_pub = subgroupCheckU B9 ∘ decodeKey
                                             ▼
   x3dhHomOf hX : X3dhHom (x25519DDHOf sm bp) x3dhEncCtx x3dhKdfModel vecToArrayInt bp
                                                    (hX : X25519HomOf sm bp B)
                                             │  x3dh_extracted_eq
                                             ▼
   x3dh_extracted (x25519DDHOf sm bp) vecToArrayInt (x3dhEncCtx (sid, a, b))
     = (x3dh_real (toX3DHParamsAtOf sm bp sid a b)).map encOut
                                             │  advantageA_map, x3dh_advantage_le_G25519_of_hom
                                             ▼
   x3dh_extracted_e2e_secure_of_hom : bound x3dhG25519Bound B + 24 * Δ25519
       at libcrux (X25519Hom B):       x3dh_extracted_e2e_secure
       at the specification and B9:    x3dh_spec_e2e_secure, no X25519 hypothesis
```

The extraction computes on byte arrays and the model on `Vector UInt8 32`. The instance
`defaultX3dhDeps` decodes its arguments (`decodeKey`, total, the inverse of `vecToArrayInt`),
applies the libcrux-specs operation and encodes the result, so that `vecToArrayInt` carries
each operation of the extraction to the model (`defaultX3dhHom`). The session context
`(sid, initiator, responder)` is encoded as the array of its three numbers (`x3dhEncCtx`); the
KDF reads it as a 32-byte block, eight little-endian bytes per number (`decodeCtx`), and
extracts it with the first node of its HKDF tree.

The input check `valid_pub` that `initiate` and `respond` apply to the peer public keys is a
leaf primitive of the crate and enters the instance as its specification: the subgroup check
`subgroupCheckU B9` of the base point `B9` (u-coordinate `9`) on the decoded key. It accepts
exactly the encodings of the points `P` of Curve25519 with `ℓ • P = 0`
(`defaultX3dh_valid_pub_iff`), the same strings as the check of every point of order `ℓ`, so it
accepts the encoding of every element of `G25519 B` (`defaultX3dh_valid_pub_encU`) and, under
`X25519HomOf sm bp B`, every public key `bp sk`; on these keys `initiate` and `respond` return
`some` of the computations `initiate_checked` and `respond_checked`.

## Key Primitives

- `dh_pub`, `dh`: the X25519 functions `bp`, `sm` (the model's `x25519DDHOf sm bp`; at libcrux
  `concreteDDH_X25519`)
- `kdf`: HKDF-SHA256 composition on the session context and the 4 DH shared secrets
- `sign`, `verify`: Ed25519 (`EdDSA_Bridge.x3dh_sign`, `EdDSA_Bridge.x3dh_verify`)
- `valid_pub`: the subgroup check `subgroupCheckU B9` of the decoded key

## Security Bound

Under the RFC 7748 correctness of `sm`, `bp` on the prime-order subgroup `G25519 B` of
Curve25519 (`X25519HomOf sm bp B`; for libcrux the hypothesis `X25519Hom B`, for the
specification at `B9` the theorem `X25519HomOf.spec_B9`): the standard DDH advantages in
`G25519 B` of four hop reductions (each composed with the encoding of the triple), the
advantage against the model KDF on the encodings of four uniform subgroup elements of one
reduction, at the KI adversary of the distinguisher precomposed with the encoding, and
`24 * Δ25519` for the clamped scalars (`5 * Δ25519` for each DDH hop and `4 * Δ25519` for the
KDF inputs).

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
open CatCrypt.Crypto.Libcrux.Bridge_X25519Group
open CatCrypt.Crypto.ECC (Curve25519Point curve25519SubgroupOrder Δ25519)
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

/-- The X3DH parameters of the session `sid` between the initiator `a` and the responder `b`
at the X25519 functions `sm`, `bp`: the DDH record `x25519DDHOf sm bp` and the model KDF
`x3dhKdfModel` at the context `(sid, a, b)`. -/
noncomputable def toX3DHParamsAtOf (sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32)
    (bp : Vector UInt8 32 → Vector UInt8 32) (sid : SessionId) (a b : PartyId) :
    X3DHParams (Vector UInt8 32) :=
  ExtractedCorrespondence.ctxParams (x25519DDHOf sm bp) x3dhKdfModel (sid, a, b)

/-- The concrete X3DH parameters of the session `sid` between the initiator `a` and the
responder `b`: X25519 and the model KDF `x3dhKdfModel` at the context `(sid, a, b)`. -/
noncomputable def toX3DHParamsAt (sid : SessionId) (a b : PartyId) :
    X3DHParams (Vector UInt8 32) :=
  toX3DHParamsAtOf x25519_scalarmult x25519_base sid a b

/-! ## Extraction instance -/

/-- The operations of the extraction on byte arrays at the X25519 functions `sm` and `bp`.
`dh_pub`, `dh`, `kdf` and `kdf3` are `bp`, `sm`, `x3dhKdfCtx` and `x3dhKdf3Ctx` on the decoded
context and keys, encoded back by `vecToArrayInt`; `sign` and `verify` are Ed25519 through
`EdDSA_Bridge`; the input check `valid_pub` is the subgroup check `subgroupCheckU B9` of the
decoded key; the ghost hooks `event` and `send_init` append to the trace
(`x3dhGhostRecord`). -/
@[reducible] noncomputable def x3dhDepsOf
    (sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32)
    (bp : Vector UInt8 32 → Vector UInt8 32) : X3dh.X3dhDeps where
  dh_pub a := vecToArrayInt (bp (decodeKey a))
  sign := EdDSA_Bridge.x3dh_sign
  valid_pub a := ECC.subgroupCheckU ECC.B9 (decodeKey a)
  verify := EdDSA_Bridge.x3dh_verify
  dh a b := vecToArrayInt (sm (decodeKey a) (decodeKey b))
  kdf ctx a b c d := vecToArrayInt
    (x3dhKdfCtx (decodeCtx ctx) (decodeKey a) (decodeKey b) (decodeKey c) (decodeKey d))
  kdf3 ctx a b c :=
    vecToArrayInt (x3dhKdf3Ctx (decodeCtx ctx) (decodeKey a) (decodeKey b) (decodeKey c))
  event := x3dhGhostRecord 2
  send_init ghost msg := x3dhGhostRecord 0 ghost 0 (msg.1 ++ msg.2.1 ++ msg.2.2)

/-- The operations of the extraction with the libcrux X25519: `x3dhDepsOf` at
`x25519_scalarmult` and `x25519_base`. -/
noncomputable instance defaultX3dhDeps : X3dh.X3dhDeps :=
  x3dhDepsOf x25519_scalarmult x25519_base

open CatCrypt.Crypto.KeyAgreement.X25519 in
/-- The operations of the extraction with the X25519 functions of the RFC 7748 specification:
`x3dhDepsOf` at `Spec.x25519_spec` and `Spec.x25519_base_spec`. -/
@[reducible] noncomputable def specX3dhDeps : X3dh.X3dhDeps :=
  x3dhDepsOf Spec.x25519_spec Spec.x25519_base_spec

/-- **The input check of `defaultX3dhDeps` as an order condition.** The check accepts an array
exactly when its decoded key is the encoding of the u-coordinate of a point `P` of Curve25519
with `ℓ • P = 0`. -/
theorem defaultX3dh_valid_pub_iff (a : Array Int) :
    X3dh.valid_pub a = true ↔ ∃ P : Curve25519Point,
      curve25519SubgroupOrder • P = 0 ∧ ECC.leBytesOfNat (ECC.uCoord P).val = decodeKey a :=
  ECC.subgroupCheckU_iff_nsmul_eq_zero ECC.B9_addOrder _

/-- The input check of `defaultX3dhDeps` accepts the encoding of every point of the subgroup
generated by a point `B` of order `ℓ`. -/
theorem defaultX3dh_valid_pub_encU {B : Curve25519Point}
    [Fact (addOrderOf B = curve25519SubgroupOrder)] (T : ECC.G25519 B) :
    X3dh.valid_pub (vecToArrayInt (ECC.encU T)) = true := by
  change ECC.subgroupCheckU ECC.B9 (decodeKey (vecToArrayInt (ECC.encU T))) = true
  rw [decodeKey_vecToArrayInt]
  exact ECC.subgroupCheckU_encU_of_addOrderOf ECC.B9_addOrder Fact.out T

/-- Under `X25519HomOf sm bp B`, `vecToArrayInt` and `x3dhEncCtx` carry the operations of
`x3dhDepsOf sm bp` to the DDH record `x25519DDHOf sm bp` and the model KDF `x3dhKdfModel`, with
public-key map `bp`, and the input check accepts every encoded public key: a public key is the
encoding of a point of `G25519 B`. -/
theorem x3dhHomOf {B : Curve25519Point} [Fact (addOrderOf B = curve25519SubgroupOrder)]
    {sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32}
    {bp : Vector UInt8 32 → Vector UInt8 32} (hX : X25519HomOf sm bp B) :
    @ExtractedCorrespondence.X3dhHom _ _ (x3dhDepsOf sm bp) (x25519DDHOf sm bp) x3dhEncCtx
      x3dhKdfModel vecToArrayInt bp := by
  let _ : X3dh.X3dhDeps := x3dhDepsOf sm bp
  exact {
    dh_pub := fun x => by
      change vecToArrayInt (bp (decodeKey (vecToArrayInt x))) = _
      rw [decodeKey_vecToArrayInt]
    dh := fun x y => by
      change vecToArrayInt (sm (decodeKey (vecToArrayInt x)) (decodeKey (vecToArrayInt y))) = _
      rw [decodeKey_vecToArrayInt, decodeKey_vecToArrayInt]
    kdf := fun c a b d e => by
      change vecToArrayInt (x3dhKdfCtx (decodeCtx (x3dhEncCtx c)) (decodeKey (vecToArrayInt a))
        (decodeKey (vecToArrayInt b)) (decodeKey (vecToArrayInt d))
        (decodeKey (vecToArrayInt e))) = _
      simp only [decodeKey_vecToArrayInt]
      rfl
    valid_pub := fun x => by
      rw [hX.base_eq_pub]
      change ECC.subgroupCheckU ECC.B9 (decodeKey (vecToArrayInt (ECC.encU _))) = true
      rw [decodeKey_vecToArrayInt]
      exact ECC.subgroupCheckU_encU_of_addOrderOf ECC.B9_addOrder Fact.out _ }

/-- Under `X25519Hom B`, `vecToArrayInt` and `x3dhEncCtx` carry the operations of
`defaultX3dhDeps` to X25519 and the model KDF `x3dhKdfModel`, with public-key map
`x25519_base`, and the input check accepts every encoded public key: a public key is the
encoding of a point of `G25519 B`. -/
theorem defaultX3dhHom {B : Curve25519Point} [Fact (addOrderOf B = curve25519SubgroupOrder)]
    (hX : X25519Hom B) :
    ExtractedCorrespondence.X3dhHom concreteDDH_X25519 x3dhEncCtx x3dhKdfModel vecToArrayInt
      x25519_base :=
  x3dhHomOf hX

/-- `vecToArrayInt` and `x3dhEncCtx` carry `kdf3` of `x3dhDepsOf sm bp` to `x3dhKdf3Model`. -/
theorem x3dhKdf3HomOf (sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32)
    (bp : Vector UInt8 32 → Vector UInt8 32) :
    @ExtractedCorrespondence.X3dhKdf3Hom _ (x3dhDepsOf sm bp) x3dhEncCtx vecToArrayInt
      x3dhKdf3Model := by
  intro c a b d
  change vecToArrayInt (x3dhKdf3Ctx (decodeCtx (x3dhEncCtx c)) (decodeKey (vecToArrayInt a))
    (decodeKey (vecToArrayInt b)) (decodeKey (vecToArrayInt d))) = _
  simp only [decodeKey_vecToArrayInt]
  rfl

/-- `vecToArrayInt` and `x3dhEncCtx` carry `kdf3` of `defaultX3dhDeps` to `x3dhKdf3Model`. -/
theorem defaultX3dhKdf3Hom :
    ExtractedCorrespondence.X3dhKdf3Hom x3dhEncCtx vecToArrayInt x3dhKdf3Model :=
  x3dhKdf3HomOf x25519_scalarmult x25519_base

/-! ## End-to-end security of the extracted handshake -/

/-- **X3DH end-to-end security of the extracted handshake at X25519 functions** `sm`, `bp` and
HKDF-SHA256, in the session `sid` between the initiator `a` and the responder `b`, from DDH in
the prime-order subgroup of Curve25519.

Given the RFC 7748 correctness of `sm`, `bp` on the subgroup `G25519 B` generated by a point `B`
of order `ℓ` (`X25519HomOf sm bp B`), the advantage of every distinguisher `D` between the
session computed by the extracted `create_bundle` and `initiate` of `x3dh-hax` at
`x3dhDepsOf sm bp` and the context `x3dhEncCtx (sid, a, b)` and the encoded ideal session is at
most `x3dhG25519Bound B (toX3DHParamsAtOf sm bp sid a b)` at the KI adversary of `D`
precomposed with the encoding, plus `24 * Δ25519`. The statement is an advantage bound between
two distributions, not a UC emulation. Delegates to `ExtractedCorrespondence.x3dh_extracted_eq`
at `x3dhHomOf hX` and `G25519.x3dh_advantage_le_G25519_of_hom`. -/
theorem x3dh_extracted_e2e_secure_of_hom {B : Curve25519Point}
    [Fact (addOrderOf B = curve25519SubgroupOrder)]
    {sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32}
    {bp : Vector UInt8 32 → Vector UInt8 32} (hX : X25519HomOf sm bp B) (sid : SessionId)
    (a b : PartyId) (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA
        (@ExtractedCorrespondence.x3dh_extracted _ _ (x3dhDepsOf sm bp) (x25519DDHOf sm bp)
          vecToArrayInt (x3dhEncCtx (sid, a, b)))
        ((x3dh_ideal (toX3DHParamsAtOf sm bp sid a b)).map
          (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      G25519.x3dhG25519Bound B (toX3DHParamsAtOf sm bp sid a b)
        (Session.X3DHHops.kiAdversaryOfDistinguisher (toX3DHParamsAtOf sm bp sid a b)
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) + 24 * Δ25519 := by
  let _ : X3dh.X3dhDeps := x3dhDepsOf sm bp
  rw [ExtractedCorrespondence.x3dh_extracted_eq (x3dhHomOf hX) rfl sid a b, advantageA_map]
  exact G25519.x3dh_advantage_le_G25519_of_hom hX _ rfl _

/-- **X3DH end-to-end security of the extracted handshake** with libcrux X25519 and
HKDF-SHA256, in the session `sid` between the initiator `a` and the responder `b`, from DDH in
the prime-order subgroup of Curve25519.

Given the RFC 7748 correctness of X25519 on the subgroup `G25519 B` generated by a point `B` of
order `ℓ` (`X25519Hom B`), the advantage of every distinguisher `D` between the session
computed by the extracted `create_bundle` and `initiate` of `x3dh-hax` at `defaultX3dhDeps` and
the context `x3dhEncCtx (sid, a, b)` (`x3dh_extracted`) and the encoded ideal session is at
most `x3dhG25519Bound B (toX3DHParamsAt sid a b)` at the KI adversary of `D` precomposed with
the encoding, plus `24 * Δ25519`: the standard DDH advantages in `G25519 B` of the four hop
reductions composed with the encoding of the triple, the advantage against the model KDF at the
context `(sid, a, b)` on the encodings of four uniform subgroup elements, and the statistical
distance of clamped scalars from uniform exponents at each of the twenty-four exponent draws.
The statement is an advantage bound between two distributions, not a UC emulation.

The extracted `initiate` applies the input check to the bundle, which it passes, since the
bundle holds public keys. The theorem is `x3dh_extracted_e2e_secure_of_hom` at
`X25519Hom B`. -/
theorem x3dh_extracted_e2e_secure {B : Curve25519Point}
    [Fact (addOrderOf B = curve25519SubgroupOrder)] (hX : X25519Hom B) (sid : SessionId)
    (a b : PartyId) (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA
        (ExtractedCorrespondence.x3dh_extracted concreteDDH_X25519 vecToArrayInt
          (x3dhEncCtx (sid, a, b)))
        ((x3dh_ideal (toX3DHParamsAt sid a b)).map
          (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      G25519.x3dhG25519Bound B (toX3DHParamsAt sid a b)
        (Session.X3DHHops.kiAdversaryOfDistinguisher (toX3DHParamsAt sid a b)
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) + 24 * Δ25519 :=
  x3dh_extracted_e2e_secure_of_hom hX sid a b D

/-- **X3DH end-to-end security of the extracted handshake without the one-time prekey at
X25519 functions** `sm`, `bp`, in the session `sid` between the initiator `a` and the responder
`b`, from DDH in the prime-order subgroup of Curve25519.

Given `X25519HomOf sm bp B`, the advantage of every distinguisher `D` between the session
computed by the extracted `create_bundle` and `initiate` at `x3dhDepsOf sm bp`, `use_opk = false`
and the context `x3dhEncCtx (sid, a, b)` and the encoded ideal session is at most
`x3dhG25519Bound B` of `noOpkParams (toX3DHParamsAtOf sm bp sid a b) (x3dhKdf3Model (sid, a, b))`
at the KI adversary of `D` precomposed with the encoding, plus `24 * Δ25519`. The statement is
an advantage bound between two distributions, not a UC emulation. -/
theorem x3dh_extracted_noOpk_e2e_secure_of_hom {B : Curve25519Point}
    [Fact (addOrderOf B = curve25519SubgroupOrder)]
    {sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32}
    {bp : Vector UInt8 32 → Vector UInt8 32} (hX : X25519HomOf sm bp B) (sid : SessionId)
    (a b : PartyId) (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA
        (@ExtractedCorrespondence.x3dh_extractedAt _ _ (x3dhDepsOf sm bp) (x25519DDHOf sm bp)
          vecToArrayInt (x3dhEncCtx (sid, a, b)) false)
        ((x3dh_ideal (toX3DHParamsAtOf sm bp sid a b)).map
          (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      G25519.x3dhG25519Bound B
        (ExtractedCorrespondence.noOpkParams (toX3DHParamsAtOf sm bp sid a b)
          (x3dhKdf3Model (sid, a, b)))
        (Session.X3DHHops.kiAdversaryOfDistinguisher
          (ExtractedCorrespondence.noOpkParams (toX3DHParamsAtOf sm bp sid a b)
            (x3dhKdf3Model (sid, a, b)))
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) + 24 * Δ25519 := by
  let _ : X3dh.X3dhDeps := x3dhDepsOf sm bp
  rw [ExtractedCorrespondence.x3dh_extracted_noOpk_eq (x3dhHomOf hX) (x3dhKdf3HomOf sm bp) rfl
    sid a b, advantageA_map]
  exact G25519.x3dh_advantage_le_G25519_of_hom hX _ rfl _

/-- **X3DH end-to-end security of the extracted handshake without the one-time prekey**, with
libcrux X25519 and HKDF-SHA256, in the session `sid` between the initiator `a` and the
responder `b`, from DDH in the prime-order subgroup of Curve25519.

Given `X25519Hom B`, the advantage of every distinguisher `D` between the session computed by
the extracted `create_bundle` and `initiate` at `use_opk = false` and the context
`x3dhEncCtx (sid, a, b)` and the encoded ideal session is at most `x3dhG25519Bound B` of
`noOpkParams (toX3DHParamsAt sid a b) (x3dhKdf3Model (sid, a, b))`, the parameters whose KDF is
the three-value model KDF at the context, at the KI adversary of `D` precomposed with the
encoding, plus `24 * Δ25519`. The statement is an advantage bound between two distributions,
not a UC emulation. -/
theorem x3dh_extracted_noOpk_e2e_secure {B : Curve25519Point}
    [Fact (addOrderOf B = curve25519SubgroupOrder)] (hX : X25519Hom B) (sid : SessionId)
    (a b : PartyId) (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA
        (ExtractedCorrespondence.x3dh_extractedAt concreteDDH_X25519 vecToArrayInt
          (x3dhEncCtx (sid, a, b)) false)
        ((x3dh_ideal (toX3DHParamsAt sid a b)).map
          (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      G25519.x3dhG25519Bound B
        (ExtractedCorrespondence.noOpkParams (toX3DHParamsAt sid a b)
          (x3dhKdf3Model (sid, a, b)))
        (Session.X3DHHops.kiAdversaryOfDistinguisher
          (ExtractedCorrespondence.noOpkParams (toX3DHParamsAt sid a b)
            (x3dhKdf3Model (sid, a, b)))
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) + 24 * Δ25519 :=
  x3dh_extracted_noOpk_e2e_secure_of_hom hX sid a b D

/-! ## The extracted handshake at the X25519 specification -/

section Spec

open CatCrypt.Crypto.KeyAgreement.X25519

/-- **X3DH end-to-end security of the extracted handshake at the X25519 specification**, in the
session `sid` between the initiator `a` and the responder `b`, from DDH in the subgroup
`G25519 B9` generated by the base point of RFC 7748.

The advantage of every distinguisher `D` between the session computed by the extracted
`create_bundle` and `initiate` of `x3dh-hax` at `specX3dhDeps` (`Spec.x25519_spec`,
`Spec.x25519_base_spec`, HKDF-SHA256, Ed25519) and the context `x3dhEncCtx (sid, a, b)` and the
encoded ideal session is at most `x3dhG25519Bound B9` at the parameters
`toX3DHParamsAtOf Spec.x25519_spec Spec.x25519_base_spec sid a b` and the KI adversary of `D`
precomposed with the encoding, plus `24 * Δ25519`. The correctness of the specification on the
subgroup is the theorem `X25519HomOf.spec_B9`, so the statement has no X25519 hypothesis. -/
theorem x3dh_spec_e2e_secure (sid : SessionId) (a b : PartyId)
    (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA
        (@ExtractedCorrespondence.x3dh_extracted _ _ specX3dhDeps
          (x25519DDHOf Spec.x25519_spec Spec.x25519_base_spec) vecToArrayInt
          (x3dhEncCtx (sid, a, b)))
        ((x3dh_ideal (toX3DHParamsAtOf Spec.x25519_spec Spec.x25519_base_spec sid a b)).map
          (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      G25519.x3dhG25519Bound ECC.B9
          (toX3DHParamsAtOf Spec.x25519_spec Spec.x25519_base_spec sid a b)
        (Session.X3DHHops.kiAdversaryOfDistinguisher
          (toX3DHParamsAtOf Spec.x25519_spec Spec.x25519_base_spec sid a b)
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) + 24 * Δ25519 :=
  x3dh_extracted_e2e_secure_of_hom X25519HomOf.spec_B9 sid a b D

/-- **X3DH end-to-end security of the extracted handshake without the one-time prekey at the
X25519 specification**, in the session `sid` between the initiator `a` and the responder `b`:
the bound of `x3dh_extracted_noOpk_e2e_secure_of_hom` at `specX3dhDeps` and `B9`, with no X25519
hypothesis. -/
theorem x3dh_spec_noOpk_e2e_secure (sid : SessionId) (a b : PartyId)
    (D : Array Int × X3DHTranscript (Array Int) → SPComp Bool) :
    AdvantageA
        (@ExtractedCorrespondence.x3dh_extractedAt _ _ specX3dhDeps
          (x25519DDHOf Spec.x25519_spec Spec.x25519_base_spec) vecToArrayInt
          (x3dhEncCtx (sid, a, b)) false)
        ((x3dh_ideal (toX3DHParamsAtOf Spec.x25519_spec Spec.x25519_base_spec sid a b)).map
          (ExtractedCorrespondence.encOut vecToArrayInt)) D ≤
      G25519.x3dhG25519Bound ECC.B9
        (ExtractedCorrespondence.noOpkParams
          (toX3DHParamsAtOf Spec.x25519_spec Spec.x25519_base_spec sid a b)
          (x3dhKdf3Model (sid, a, b)))
        (Session.X3DHHops.kiAdversaryOfDistinguisher
          (ExtractedCorrespondence.noOpkParams
            (toX3DHParamsAtOf Spec.x25519_spec Spec.x25519_base_spec sid a b)
            (x3dhKdf3Model (sid, a, b)))
          (D ∘ ExtractedCorrespondence.encOut vecToArrayInt)) + 24 * Δ25519 :=
  x3dh_extracted_noOpk_e2e_secure_of_hom X25519HomOf.spec_B9 sid a b D

end Spec

end CatCrypt.Crypto.Signal.X3DH.SurfaceDeps

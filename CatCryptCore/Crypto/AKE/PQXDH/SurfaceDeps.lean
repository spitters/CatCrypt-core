/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Libcrux.Bridge_HKDF
public import CatCryptCore.Crypto.Libcrux.Bridge_MLKEM
public import CatCryptCore.Crypto.Libcrux.Bridge_X25519
public import CatCryptCore.Crypto.Libcrux.ConcreteInstances
public import CatCryptCore.Crypto.AKE.PQXDH.Extraction.Pqxdh_haxpipe
public import CatCryptCore.Crypto.AKE.PQXDH.ExtractedCorrespondence
public import CatCryptCore.Crypto.AKE.PQXDH.PassiveG25519
public import CatCryptCore.Crypto.AKE.X3DH.EdDSA_Bridge
public import CatCryptCore.Hax.ReprBridge

/-!
# PQXDH SurfaceDeps: Extraction-to-Security Bridge

Wraps an X25519 scalar multiplication `sm` and base-point function `bp`, with the libcrux-specs
ML-KEM-768, HKDF-SHA256 and Ed25519, into the dependency record `Pqxdh.PqxdhDeps` of the
extracted PQXDH code (`pqxdhDepsOf sm bp`) and derives the bound and the key agreement of the
extracted handshake from the passive model. The instance `defaultPqxdhDeps` takes the opaque
libcrux functions `x25519_scalarmult`, `x25519_base`, and `specPqxdhDeps` the RFC 7748
specification `Spec.x25519_spec`, `Spec.x25519_base_spec`.

## Architecture

```
pqxdh-hax (Rust) → haxpipeT → Pqxdh.create_bundle, Pqxdh.initiate (Array Int)
                                   │  pqxdhDepsOf sm bp: bp, sm,
                                   │  mlkem768_keygen / _encaps / _decaps, pqxdhKdf through
                                   │  vecToArrayInt / decodeVecAt; Ed25519
                                   ▼
     pqxdhHomOf sm bp : PqxdhHom (toPassiveParamsOf sm bp) libcruxEnc bp
                                   │  pqxdh_extracted_eq
                                   ▼
  pqxdh_extracted P libcruxEnc = (pqxdh_real P).map encOut,  P = toPassiveParamsOf sm bp
                                   │  advantageA_map, pqxdh_advantage_le_G25519_of_hom
                                   ▼
  pqxdh_extracted_e2e_secure_of_hom : bound pqxdhG25519Bound B + 24 * Δ25519
                                       (hX : X25519HomOf sm bp B)
      at libcrux (X25519Hom B):        pqxdh_extracted_e2e_secure
      at the specification and B9:     pqxdh_spec_e2e_secure, no X25519 hypothesis
```

The extraction computes on byte arrays and the model on byte vectors. The instance
`defaultPqxdhDeps` decodes its arguments (`decodeVecAt`, total, the inverse of
`vecToArrayInt`; the 64-byte KEM seed is read as the two 32-byte seeds `(d, z)` of FIPS 203),
applies the libcrux-specs operation and encodes the result, so that `libcruxEnc` carries each
operation of the extraction to the model (`pqxdhHomOf`, at libcrux `defaultPqxdhHom`).

## Ciphersuite

- DH: the X25519 functions `bp`, `sm` (the model's `x25519DDHOf sm bp`; at libcrux
  `x25519_base`, `x25519_scalarmult` and `concreteDDH_X25519`).
- KEM: ML-KEM-768 (`mlkem768_keygen`, `mlkem768_encaps`, `mlkem768_decaps`).
- KDF: `pqxdhKdf`, a tree of HKDF-SHA256 extracts (`concreteHKDF.extract`) on the four
  Diffie-Hellman values and the KEM secret.
- `sign`, `verify`: Ed25519 (`EdDSA_Bridge.x3dh_sign`, `EdDSA_Bridge.x3dh_verify`).
- `kem_pk_encode`: `kemPkDigest`, SHA-256 of the encoded ML-KEM-768 public key, the message
  the second signature of the bundle signs.

## Security Bound

For the extracted handshake (`pqxdh_extracted_e2e_secure_of_hom`), under the RFC 7748
correctness of `sm`, `bp` on the prime-order subgroup `G25519 B` of Curve25519
(`X25519HomOf sm bp B`; for libcrux the hypothesis `X25519Hom B`, for the specification at `B9`
the theorem `X25519HomOf.spec_B9`): the ML-KEM-768
real-or-random advantage of one reduction, the standard DDH advantages in `G25519 B` of four
hop reductions (each composed with the encoding of the triple), the advantage against the
model KDF on the encodings of four uniform subgroup elements and a uniform KEM secret of one
reduction, at the KI adversary of the distinguisher precomposed with the encoding, and
`24 * Δ25519` for the clamped scalars (`5 * Δ25519` for each DDH hop and `4 * Δ25519` for the
Diffie-Hellman inputs of the KDF) (`CatCryptCore.Crypto.AKE.PQXDHPassiveKeygen`,
`CatCryptCore.Crypto.AKE.PQXDH.PassiveG25519`; time certificates in `PQXDHPassiveHopsTimed`).
The statement is an advantage bound between two distributions, not a UC emulation.

## References

* Signal — *The PQXDH Key Agreement Protocol*, September 2023
* the Rust crate `pqxdh-hax` of https://github.com/spitters/signal-hax — protocol source
* `PQXDH/ExtractedCorrespondence.lean` — the extracted session and its bound
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDH.SurfaceDeps

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Libcrux.Bridge_HKDF
open CatCrypt.Crypto.Libcrux.Bridge_MLKEM
open CatCrypt.Crypto.Libcrux.ConcreteInstances
open CatCrypt.Crypto.Libcrux.Bridge_X25519
open CatCrypt.Crypto.Libcrux.Bridge_X25519Group
open CatCrypt.Crypto.ECC (Curve25519Point curve25519SubgroupOrder Δ25519)
open CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.PQXDHPassive
open CatCrypt.Crypto.Signal.PQXDH.ExtractedCorrespondence
open CatCrypt.Hax.ReprBridge
open scoped ENNReal

/-- 32-byte vectors: X25519 keys and values, KEM messages and secrets, session keys. -/
abbrev V32 := Vector UInt8 32

/-- Uniform sampling of a pair of 32-byte vectors, the ML-KEM-768 key generation seeds
`(d, z)`. -/
noncomputable instance instSampleableTypeV32Pair : SampleableType (V32 × V32) where
  fintype := inferInstance
  nonempty := inferInstance
  deceq := inferInstance
  inhabited := inferInstance

/-! ## Surface KDF -/

/-- PQXDH KDF: combine the 4 DH shared secrets via a tree of HKDF-Extract
operations, then absorb the ML-KEM shared secret. Models
`HKDF(DH1 || DH2 || DH3 || DH4 || KEM_SS)` as a composition tree. -/
noncomputable def pqxdhKdf
    (dhs : V32 × V32 × V32 × V32) (kem_ss : V32) : V32 :=
  let ⟨dh1, dh2, dh3, dh4⟩ := dhs
  let dh_combined :=
    concreteHKDF.extract (concreteHKDF.extract dh1 dh2)
                         (concreteHKDF.extract dh3 dh4)
  concreteHKDF.extract dh_combined kem_ss

/-- SHA-256 of an encoded ML-KEM-768 public key (1184 bytes): the 32-byte message that
`kem_pk_encode` of the ML-KEM-768 instance of `pqxdh-hax` returns and the bundle signs.
libcrux-specs states SHA-256 on 32-byte inputs only (`sha256_32`); this input length is an
opaque function of the same kind. -/
opaque kemPkDigest : Vector UInt8 1184 → V32

/-! ## Byte decoding -/

/-- The `n` bytes of a byte array from offset `off`: entry `off + i` truncated to a byte, `0`
past the end. The decoding is total and inverts `vecToArrayInt` at offset `0`. -/
def decodeVecAt (n off : Nat) (a : Array Int) : Vector UInt8 n :=
  Vector.ofFn fun i => (a.getD (off + i) 0).toNat.toUInt8

/-- `decodeVecAt` at offset `0` inverts `vecToArrayInt`. -/
theorem decodeVecAt_vecToArrayInt {n : Nat} (v : Vector UInt8 n) :
    decodeVecAt n 0 (vecToArrayInt v) = v := by
  ext i hi
  simp [decodeVecAt, vecToArrayInt]

/-- The encoding of a pair of 32-byte seeds: the concatenation of the two arrays. -/
def encSeed (s : V32 × V32) : Array Int := vecToArrayInt s.1 ++ vecToArrayInt s.2

/-- The first 32 bytes of `encSeed s` decode to the first seed. -/
theorem decodeVecAt_encSeed_fst (s : V32 × V32) : decodeVecAt 32 0 (encSeed s) = s.1 := by
  ext i hi
  simp [decodeVecAt, encSeed, vecToArrayInt, Array.getD_eq_getD_getElem?,
    Array.getElem?_append]

/-- The 32 bytes of `encSeed s` from offset `32` decode to the second seed. -/
theorem decodeVecAt_encSeed_snd (s : V32 × V32) : decodeVecAt 32 32 (encSeed s) = s.2 := by
  ext i hi
  simp [decodeVecAt, encSeed, vecToArrayInt, Array.getD_eq_getD_getElem?,
    Array.getElem?_append]

/-! ## The libcrux model parameters -/

/-- PQXDH parameters of the passive model with the X25519 functions `sm`, `bp` (the DDH record
`x25519DDHOf sm bp`), libcrux-specs ML-KEM-768 (key generation from the seeds `(d, z)`,
encapsulation from a 32-byte message) and the KDF `pqxdhKdf`. -/
noncomputable def toPassiveParamsOf (sm : V32 → V32 → V32) (bp : V32 → V32) :
    PassiveParams V32 (Vector UInt8 1184) (Vector UInt8 2400) (Vector UInt8 1088) (V32 × V32)
    where
  dh := x25519DDHOf sm bp
  kemKeygen := mlkem768_keygen
  kemEncaps pk m := ((mlkem768_encaps pk m).2, (mlkem768_encaps pk m).1)
  kemDecaps := mlkem768_decaps
  kdf a b c d k := pqxdhKdf (a, b, c, d) k

/-- PQXDH parameters of the passive model with libcrux-specs X25519, ML-KEM-768 and the KDF
`pqxdhKdf`: `toPassiveParamsOf` at `x25519_scalarmult` and `x25519_base`. -/
noncomputable def toPassiveParams :
    PassiveParams V32 (Vector UInt8 1184) (Vector UInt8 2400) (Vector UInt8 1088) (V32 × V32) :=
  toPassiveParamsOf x25519_scalarmult x25519_base

/-- The encodings of the libcrux values: `vecToArrayInt` on every byte vector, and the
concatenation on the pair of seeds. -/
def libcruxEnc :
    PqxdhEnc V32 (Vector UInt8 1184) (Vector UInt8 2400) (Vector UInt8 1088) (V32 × V32) where
  w := vecToArrayInt
  pk := vecToArrayInt
  sk := vecToArrayInt
  ct := vecToArrayInt
  seed := encSeed

/-! ## Extraction instance -/

/-- The ghost record of the typestate FSM (`PqxdhGhost` of the Rust crate `pqxdh-hax`): the
ghost state is the ordered trace of communication actions. Each hook appends the header
`[kind, tag, n]` followed by the `n` payload entries, with `kind` `0` for `send_msg` (tag `0`)
and `2` for `event`. -/
def pqxdhGhostRecord (kind : Int) (ghost : Array Int) (tag : Int) (payload : Array Int) :
    Array Int :=
  ghost ++ #[kind, tag, payload.size] ++ payload

/-- The operations of the extraction on byte arrays at the X25519 functions `sm` and `bp`.
`dh_pub`, `dh`, the KEM operations and `kdf` are `bp`, `sm`, ML-KEM-768 and `pqxdhKdf` on the
decoded arguments, encoded back by `vecToArrayInt`; `kem_pk_encode` is `kemPkDigest` on the
decoded public key; `sign` and `verify` are Ed25519 through `EdDSA_Bridge`; the ghost hooks
`event` and `send_msg` append to the trace (`pqxdhGhostRecord`). -/
@[reducible] noncomputable def pqxdhDepsOf (sm : V32 → V32 → V32) (bp : V32 → V32) :
    Pqxdh.PqxdhDeps where
  dh_pub a := vecToArrayInt (bp (decodeVecAt 32 0 a))
  kem_keygen a :=
    (vecToArrayInt (mlkem768_keygen (decodeVecAt 32 0 a, decodeVecAt 32 32 a)).1,
      vecToArrayInt (mlkem768_keygen (decodeVecAt 32 0 a, decodeVecAt 32 32 a)).2)
  sign := X3DH.EdDSA_Bridge.x3dh_sign
  kem_pk_encode pk := vecToArrayInt (kemPkDigest (decodeVecAt 1184 0 pk))
  verify := X3DH.EdDSA_Bridge.x3dh_verify
  dh a b := vecToArrayInt (sm (decodeVecAt 32 0 a) (decodeVecAt 32 0 b))
  kem_encaps pk r :=
    (vecToArrayInt (mlkem768_encaps (decodeVecAt 1184 0 pk) (decodeVecAt 32 0 r)).2,
      vecToArrayInt (mlkem768_encaps (decodeVecAt 1184 0 pk) (decodeVecAt 32 0 r)).1)
  kdf a b c d e :=
    vecToArrayInt (pqxdhKdf (decodeVecAt 32 0 a, decodeVecAt 32 0 b, decodeVecAt 32 0 c,
      decodeVecAt 32 0 d) (decodeVecAt 32 0 e))
  kem_decaps sk ct :=
    vecToArrayInt (mlkem768_decaps (decodeVecAt 2400 0 sk) (decodeVecAt 1088 0 ct))
  event := pqxdhGhostRecord 2
  send_msg ghost msg := pqxdhGhostRecord 0 ghost 0 msg

/-- The operations of the extraction with the libcrux X25519: `pqxdhDepsOf` at
`x25519_scalarmult` and `x25519_base`. -/
noncomputable instance defaultPqxdhDeps : Pqxdh.PqxdhDeps :=
  pqxdhDepsOf x25519_scalarmult x25519_base

open CatCrypt.Crypto.KeyAgreement.X25519 in
/-- The operations of the extraction with the X25519 functions of the RFC 7748 specification:
`pqxdhDepsOf` at `Spec.x25519_spec` and `Spec.x25519_base_spec`. -/
@[reducible] noncomputable def specPqxdhDeps : Pqxdh.PqxdhDeps :=
  pqxdhDepsOf Spec.x25519_spec Spec.x25519_base_spec

/-- `libcruxEnc` carries the operations of `pqxdhDepsOf sm bp` to those of
`toPassiveParamsOf sm bp`, with public-key map `bp`. -/
theorem pqxdhHomOf (sm : V32 → V32 → V32) (bp : V32 → V32) :
    @PqxdhHom _ _ _ _ _ _ (pqxdhDepsOf sm bp) (toPassiveParamsOf sm bp) libcruxEnc bp := by
  let _ : Pqxdh.PqxdhDeps := pqxdhDepsOf sm bp
  exact {
    dh_pub := fun x => by
      change vecToArrayInt (bp (decodeVecAt 32 0 (vecToArrayInt x))) =
        vecToArrayInt (bp x)
      rw [decodeVecAt_vecToArrayInt]
    dh := fun x y => by
      change vecToArrayInt (sm (decodeVecAt 32 0 (vecToArrayInt x))
        (decodeVecAt 32 0 (vecToArrayInt y))) = vecToArrayInt (sm x y)
      rw [decodeVecAt_vecToArrayInt, decodeVecAt_vecToArrayInt]
    kem_keygen := fun sd => by
      change (vecToArrayInt (mlkem768_keygen (decodeVecAt 32 0 (encSeed sd),
          decodeVecAt 32 32 (encSeed sd))).1,
        vecToArrayInt (mlkem768_keygen (decodeVecAt 32 0 (encSeed sd),
          decodeVecAt 32 32 (encSeed sd))).2) =
        (vecToArrayInt (mlkem768_keygen sd).1, vecToArrayInt (mlkem768_keygen sd).2)
      rw [decodeVecAt_encSeed_fst, decodeVecAt_encSeed_snd]
    kem_encaps := fun pk m => by
      change (vecToArrayInt (mlkem768_encaps (decodeVecAt 1184 0 (vecToArrayInt pk))
          (decodeVecAt 32 0 (vecToArrayInt m))).2,
        vecToArrayInt (mlkem768_encaps (decodeVecAt 1184 0 (vecToArrayInt pk))
          (decodeVecAt 32 0 (vecToArrayInt m))).1) =
        (vecToArrayInt (mlkem768_encaps pk m).2, vecToArrayInt (mlkem768_encaps pk m).1)
      rw [decodeVecAt_vecToArrayInt, decodeVecAt_vecToArrayInt]
    kem_decaps := fun sk c => by
      change vecToArrayInt (mlkem768_decaps (decodeVecAt 2400 0 (vecToArrayInt sk))
        (decodeVecAt 1088 0 (vecToArrayInt c))) = vecToArrayInt (mlkem768_decaps sk c)
      rw [decodeVecAt_vecToArrayInt, decodeVecAt_vecToArrayInt]
    kdf := fun a b c d k => by
      change vecToArrayInt (pqxdhKdf (decodeVecAt 32 0 (vecToArrayInt a),
        decodeVecAt 32 0 (vecToArrayInt b), decodeVecAt 32 0 (vecToArrayInt c),
        decodeVecAt 32 0 (vecToArrayInt d)) (decodeVecAt 32 0 (vecToArrayInt k))) =
        vecToArrayInt (pqxdhKdf (a, b, c, d) k)
      simp only [decodeVecAt_vecToArrayInt] }

/-- `libcruxEnc` carries the operations of `defaultPqxdhDeps` to those of `toPassiveParams`,
with public-key map `x25519_base`. -/
theorem defaultPqxdhHom : PqxdhHom toPassiveParams libcruxEnc x25519_base :=
  pqxdhHomOf x25519_scalarmult x25519_base

/-! ## Security of the extracted handshake -/

/-- **PQXDH key indistinguishability of the extracted handshake at X25519 functions** `sm`,
`bp`, with libcrux ML-KEM-768 and the HKDF-SHA256 KDF, from the KEM assumption and DDH in the
prime-order subgroup of Curve25519.

Given the RFC 7748 correctness of `sm`, `bp` on the subgroup `G25519 B` generated by a point `B`
of order `ℓ` (`X25519HomOf sm bp B`), the advantage of every distinguisher `D` between the
session computed by the extracted `create_bundle` and `initiate` of `pqxdh-hax` at
`pqxdhDepsOf sm bp` and the encoded ideal session is at most
`pqxdhG25519Bound B (toPassiveParamsOf sm bp)` at the KI adversary of `D` precomposed with the
encoding, plus `24 * Δ25519`. Delegates to `ExtractedCorrespondence.pqxdh_extracted_eq` at
`pqxdhHomOf` and `G25519.pqxdh_advantage_le_G25519_of_hom`. -/
theorem pqxdh_extracted_e2e_secure_of_hom {B : Curve25519Point}
    [Fact (addOrderOf B = curve25519SubgroupOrder)] {sm : V32 → V32 → V32} {bp : V32 → V32}
    (hX : X25519HomOf sm bp B) (D : Array Int × ExtractedTranscript → SPComp Bool) :
    AdvantageA
        (@pqxdh_extracted _ _ _ _ _ _ _ (pqxdhDepsOf sm bp) (toPassiveParamsOf sm bp)
          libcruxEnc)
        ((pqxdh_ideal (toPassiveParamsOf sm bp)).map (encOut libcruxEnc)) D ≤
      G25519.pqxdhG25519Bound B (toPassiveParamsOf sm bp)
        (kiAdversaryOfDistinguisher (toPassiveParamsOf sm bp) (D ∘ encOut libcruxEnc)) +
          24 * Δ25519 := by
  let _ : Pqxdh.PqxdhDeps := pqxdhDepsOf sm bp
  rw [pqxdh_extracted_eq (pqxdhHomOf sm bp) rfl, advantageA_map]
  exact G25519.pqxdh_advantage_le_G25519_of_hom hX _ rfl _

/-- **PQXDH key indistinguishability of the extracted handshake** with libcrux X25519,
ML-KEM-768 and the HKDF-SHA256 KDF, from the KEM assumption and DDH in the prime-order subgroup
of Curve25519.

Given the RFC 7748 correctness of X25519 on the subgroup `G25519 B` generated by a point `B` of
order `ℓ` (`X25519Hom B`), the advantage of every distinguisher `D` between the session
computed by the extracted `create_bundle` and `initiate` of `pqxdh-hax` at `defaultPqxdhDeps`
(`pqxdh_extracted`) and the encoded ideal session is at most
`pqxdhG25519Bound B toPassiveParams` at the KI adversary of `D` precomposed with the encoding,
plus `24 * Δ25519`: the ML-KEM-768 advantage of the KEM reduction, the standard DDH advantages
in `G25519 B` of the four hop reductions composed with the encoding of the triple, the
advantage against `pqxdhKdf` on the encodings of four uniform subgroup elements and a uniform
KEM secret of the KDF reduction, and the statistical distance of clamped scalars from uniform
exponents at each of the twenty-four exponent draws.

The theorem is `pqxdh_extracted_e2e_secure_of_hom` at `X25519Hom B`. -/
theorem pqxdh_extracted_e2e_secure {B : Curve25519Point}
    [Fact (addOrderOf B = curve25519SubgroupOrder)] (hX : X25519Hom B)
    (D : Array Int × ExtractedTranscript → SPComp Bool) :
    AdvantageA (pqxdh_extracted toPassiveParams libcruxEnc)
        ((pqxdh_ideal toPassiveParams).map (encOut libcruxEnc)) D ≤
      G25519.pqxdhG25519Bound B toPassiveParams
        (kiAdversaryOfDistinguisher toPassiveParams (D ∘ encOut libcruxEnc)) + 24 * Δ25519 :=
  pqxdh_extracted_e2e_secure_of_hom hX D

open CatCrypt.Crypto.KeyAgreement.X25519 in
/-- **PQXDH key indistinguishability of the extracted handshake at the X25519 specification**,
with libcrux ML-KEM-768 and the HKDF-SHA256 KDF, from the KEM assumption and DDH in the subgroup
`G25519 B9` generated by the base point of RFC 7748.

The advantage of every distinguisher `D` between the session computed by the extracted
`create_bundle` and `initiate` of `pqxdh-hax` at `specPqxdhDeps` (`Spec.x25519_spec`,
`Spec.x25519_base_spec`) and the encoded ideal session is at most `pqxdhG25519Bound B9` at the
parameters `toPassiveParamsOf Spec.x25519_spec Spec.x25519_base_spec` and the KI adversary of
`D` precomposed with the encoding, plus `24 * Δ25519`. The correctness of the specification on
the subgroup is the theorem `X25519HomOf.spec_B9`, so the statement has no X25519
hypothesis. -/
theorem pqxdh_spec_e2e_secure (D : Array Int × ExtractedTranscript → SPComp Bool) :
    AdvantageA
        (@pqxdh_extracted _ _ _ _ _ _ _ specPqxdhDeps
          (toPassiveParamsOf Spec.x25519_spec Spec.x25519_base_spec) libcruxEnc)
        ((pqxdh_ideal (toPassiveParamsOf Spec.x25519_spec Spec.x25519_base_spec)).map
          (encOut libcruxEnc)) D ≤
      G25519.pqxdhG25519Bound ECC.B9 (toPassiveParamsOf Spec.x25519_spec Spec.x25519_base_spec)
        (kiAdversaryOfDistinguisher (toPassiveParamsOf Spec.x25519_spec Spec.x25519_base_spec)
          (D ∘ encOut libcruxEnc)) + 24 * Δ25519 :=
  pqxdh_extracted_e2e_secure_of_hom X25519HomOf.spec_B9 D

/-- **Key agreement of the extracted handshake.** Given X25519 Diffie-Hellman correctness and
ML-KEM-768 correctness on seeds and messages (`toPassiveParams.KemCorrect`), the responder's
key computed by the extracted `respond` from the bundle's KEM secret key and the initiator's
message is the initiator's key. -/
theorem pqxdh_extracted_agree (hX : X25519Commutes) (hK : toPassiveParams.KemCorrect)
    (a e b s o m : V32) (sd : V32 × V32) :
    Pqxdh.respond (vecToArrayInt b) (vecToArrayInt s) (vecToArrayInt o)
        (Pqxdh.create_bundle (vecToArrayInt b) (vecToArrayInt s) (vecToArrayInt o)
          (encSeed sd)).2
        (Pqxdh.initiate (vecToArrayInt a) (vecToArrayInt e)
          (Pqxdh.create_bundle (vecToArrayInt b) (vecToArrayInt s) (vecToArrayInt o)
            (encSeed sd)).1 (vecToArrayInt m) true).2.1
        true =
      (Pqxdh.initiate (vecToArrayInt a) (vecToArrayInt e)
        (Pqxdh.create_bundle (vecToArrayInt b) (vecToArrayInt s) (vecToArrayInt o)
          (encSeed sd)).1 (vecToArrayInt m) true).1 :=
  respond_agree defaultPqxdhHom hX hK a e b s o m sd

end CatCrypt.Crypto.Signal.PQXDH.SurfaceDeps

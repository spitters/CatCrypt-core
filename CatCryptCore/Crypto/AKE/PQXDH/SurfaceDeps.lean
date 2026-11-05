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
public import CatCryptCore.Crypto.AKE.X3DH.EdDSA_Bridge
public import CatCryptCore.Hax.ReprBridge

/-!
# PQXDH SurfaceDeps: Extraction-to-Security Bridge

Wraps the opaque libcrux-specs primitives into the dependency record `Pqxdh.PqxdhDeps` of the
extracted PQXDH code and derives the bound and the key agreement of the extracted handshake
from the passive model.

## Architecture

```
pqxdh-hax (Rust) → haxpipeT → Pqxdh.create_bundle, Pqxdh.initiate (Array Int)
                                   │  defaultPqxdhDeps: x25519_base, x25519_scalarmult,
                                   │  mlkem768_keygen / _encaps / _decaps, pqxdhKdf through
                                   │  vecToArrayInt / decodeVecAt; Ed25519
                                   ▼
        defaultPqxdhHom : PqxdhHom toPassiveParams libcruxEnc x25519_base
                                   │  pqxdh_extracted_eq
                                   ▼
  pqxdh_extracted toPassiveParams libcruxEnc = (pqxdh_real toPassiveParams).map encOut
                                   │  advantageA_map, pqxdh_advantage_le
                                   ▼
          pqxdh_extracted_e2e_secure : bound pqxdhKIReductionBound
```

The extraction computes on byte arrays and the model on byte vectors. The instance
`defaultPqxdhDeps` decodes its arguments (`decodeVecAt`, total, the inverse of
`vecToArrayInt`; the 64-byte KEM seed is read as the two 32-byte seeds `(d, z)` of FIPS 203),
applies the libcrux-specs operation and encodes the result, so that `libcruxEnc` carries each
operation of the extraction to the model (`defaultPqxdhHom`).

## Ciphersuite

- DH: X25519 (`x25519_base`, `x25519_scalarmult`; the model's `concreteDDH_X25519`).
- KEM: ML-KEM-768 (`mlkem768_keygen`, `mlkem768_encaps`, `mlkem768_decaps`).
- KDF: `pqxdhKdf`, a tree of HKDF-SHA256 extracts (`concreteHKDF.extract`) on the four
  Diffie-Hellman values and the KEM secret.
- `sign`, `verify`: Ed25519 (`EdDSA_Bridge.x3dh_sign`, `EdDSA_Bridge.x3dh_verify`).
- `kem_pk_encode`: `kemPkDigest`, SHA-256 of the encoded ML-KEM-768 public key, the message
  the second signature of the bundle signs.

## The ideal DDH game at X25519

The core `DDH_Game_Ideal` samples its third value uniformly from `Vector UInt8 32`, which
outputs of RFC 7748 X25519 never are, so the DDH advantage at `concreteDDH_X25519` is not
small for every adversary. The bound below uses this advantage only at the explicit hop
reductions it names.

## Security Bound

For the extracted handshake (`pqxdh_extracted_e2e_secure`): the KEM advantage of one reduction,
the DDH advantages of four reductions and the KDF advantage of one reduction, at the KI
adversary of the distinguisher precomposed with the encoding
(`CatCryptCore.Crypto.AKE.PQXDHPassiveHops`; time certificates in `PQXDHPassiveHopsTimed`).
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

/-- PQXDH parameters of the passive model with libcrux-specs X25519, ML-KEM-768 (key
generation from the seeds `(d, z)`, encapsulation from a 32-byte message) and the KDF
`pqxdhKdf`. -/
noncomputable def toPassiveParams :
    PassiveParams V32 (Vector UInt8 1184) (Vector UInt8 2400) (Vector UInt8 1088) (V32 × V32)
    where
  dh := concreteDDH_X25519
  kemKeygen := mlkem768_keygen
  kemEncaps pk m := ((mlkem768_encaps pk m).2, (mlkem768_encaps pk m).1)
  kemDecaps := mlkem768_decaps
  kdf a b c d k := pqxdhKdf (a, b, c, d) k

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

/-- The operations of the extraction on byte arrays. `dh_pub`, `dh`, the KEM operations and
`kdf` are `x25519_base`, `x25519_scalarmult`, ML-KEM-768 and `pqxdhKdf` on the decoded
arguments, encoded back by `vecToArrayInt`; `kem_pk_encode` is `kemPkDigest` on the decoded
public key; `sign` and `verify` are Ed25519 through `EdDSA_Bridge`; the ghost hooks `event`
and `send_msg` append to the trace (`pqxdhGhostRecord`). -/
noncomputable instance defaultPqxdhDeps : Pqxdh.PqxdhDeps where
  dh_pub a := vecToArrayInt (x25519_base (decodeVecAt 32 0 a))
  kem_keygen a :=
    (vecToArrayInt (mlkem768_keygen (decodeVecAt 32 0 a, decodeVecAt 32 32 a)).1,
      vecToArrayInt (mlkem768_keygen (decodeVecAt 32 0 a, decodeVecAt 32 32 a)).2)
  sign := X3DH.EdDSA_Bridge.x3dh_sign
  kem_pk_encode pk := vecToArrayInt (kemPkDigest (decodeVecAt 1184 0 pk))
  verify := X3DH.EdDSA_Bridge.x3dh_verify
  dh a b := vecToArrayInt (x25519_scalarmult (decodeVecAt 32 0 a) (decodeVecAt 32 0 b))
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

/-- `libcruxEnc` carries the operations of `defaultPqxdhDeps` to those of `toPassiveParams`,
with public-key map `x25519_base`. -/
theorem defaultPqxdhHom : PqxdhHom toPassiveParams libcruxEnc x25519_base where
  dh_pub x := by
    change vecToArrayInt (x25519_base (decodeVecAt 32 0 (vecToArrayInt x))) =
      vecToArrayInt (x25519_base x)
    rw [decodeVecAt_vecToArrayInt]
  dh x y := by
    change vecToArrayInt (x25519_scalarmult (decodeVecAt 32 0 (vecToArrayInt x))
      (decodeVecAt 32 0 (vecToArrayInt y))) = vecToArrayInt (x25519_scalarmult x y)
    rw [decodeVecAt_vecToArrayInt, decodeVecAt_vecToArrayInt]
  kem_keygen sd := by
    change (vecToArrayInt (mlkem768_keygen (decodeVecAt 32 0 (encSeed sd),
        decodeVecAt 32 32 (encSeed sd))).1,
      vecToArrayInt (mlkem768_keygen (decodeVecAt 32 0 (encSeed sd),
        decodeVecAt 32 32 (encSeed sd))).2) =
      (vecToArrayInt (mlkem768_keygen sd).1, vecToArrayInt (mlkem768_keygen sd).2)
    rw [decodeVecAt_encSeed_fst, decodeVecAt_encSeed_snd]
  kem_encaps pk m := by
    change (vecToArrayInt (mlkem768_encaps (decodeVecAt 1184 0 (vecToArrayInt pk))
        (decodeVecAt 32 0 (vecToArrayInt m))).2,
      vecToArrayInt (mlkem768_encaps (decodeVecAt 1184 0 (vecToArrayInt pk))
        (decodeVecAt 32 0 (vecToArrayInt m))).1) =
      (vecToArrayInt (mlkem768_encaps pk m).2, vecToArrayInt (mlkem768_encaps pk m).1)
    rw [decodeVecAt_vecToArrayInt, decodeVecAt_vecToArrayInt]
  kem_decaps sk c := by
    change vecToArrayInt (mlkem768_decaps (decodeVecAt 2400 0 (vecToArrayInt sk))
      (decodeVecAt 1088 0 (vecToArrayInt c))) = vecToArrayInt (mlkem768_decaps sk c)
    rw [decodeVecAt_vecToArrayInt, decodeVecAt_vecToArrayInt]
  kdf a b c d k := by
    change vecToArrayInt (pqxdhKdf (decodeVecAt 32 0 (vecToArrayInt a),
      decodeVecAt 32 0 (vecToArrayInt b), decodeVecAt 32 0 (vecToArrayInt c),
      decodeVecAt 32 0 (vecToArrayInt d)) (decodeVecAt 32 0 (vecToArrayInt k))) =
      vecToArrayInt (pqxdhKdf (a, b, c, d) k)
    simp only [decodeVecAt_vecToArrayInt]

/-! ## Security of the extracted handshake -/

/-- **PQXDH key indistinguishability of the extracted handshake** with libcrux X25519,
ML-KEM-768 and the HKDF-SHA256 KDF.

Given X25519 Diffie-Hellman correctness (`X25519Commutes`), the advantage of every
distinguisher `D` between the session computed by the extracted `create_bundle` and `initiate`
of `pqxdh-hax` at `defaultPqxdhDeps` (`pqxdh_extracted`) and the encoded ideal session is at
most `pqxdhKIReductionBound toPassiveParams` at the KI adversary of `D` precomposed with the
encoding: the ML-KEM-768 advantage of the KEM reduction, the DDH advantages of the four hop
reductions and the KDF advantage of the KDF reduction.

Delegates to `ExtractedCorrespondence.pqxdh_extracted_advantage_le` at `defaultPqxdhHom`. -/
theorem pqxdh_extracted_e2e_secure (hX : X25519Commutes)
    (D : Array Int × ExtractedTranscript → SPComp Bool) :
    AdvantageA (pqxdh_extracted toPassiveParams libcruxEnc)
        ((pqxdh_ideal toPassiveParams).map (encOut libcruxEnc)) D ≤
      pqxdhKIReductionBound toPassiveParams
        (kiAdversaryOfDistinguisher toPassiveParams (D ∘ encOut libcruxEnc)) :=
  pqxdh_extracted_advantage_le defaultPqxdhHom rfl hX D

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

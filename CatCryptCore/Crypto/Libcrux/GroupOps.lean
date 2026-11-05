/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Elliptic Curve Group Operations: Opaque Declarations

Hand-transcribed type signatures for group-level elliptic curve operations
on Ed25519 and P-256, extending the DDH-level `Libcrux_specs.lean` to
support EdDSA, ECDSA, and SPAKE2 protocols.

## Motivation

The existing `Libcrux_specs.lean` provides only DDH-level primitives
(`x25519_scalarmult`, `p256_scalar_mult_32`). Signature schemes (EdDSA,
ECDSA) and PAKE protocols (SPAKE2) need finer-grained group operations:
point addition, scalar arithmetic, base-point multiplication, etc.

## Ed25519 Operations

| Function | ref10 / libsodium analogue | Description |
|----------|--------------|-------------|
| `ed25519_base_point` | `ED25519_BASEPOINT` | Generator G |
| `ed25519_point_add` | `ge_add(P, Q)` | P + Q on Edwards curve |
| `ed25519_scalar_mul` | `sc_mul(a, b)` | a * b in scalar field |
| `ed25519_scalar_add` | `sc_add(a, b)` | a + b in scalar field |
| `ed25519_scalar_basemul` | `ge_scalarmult_base(s)` | s * G |
| `ed25519_group_mul` | `ge_scalarmult(s, P)` | s * P (scalar-point mul) |

## P-256 Operations

| Function | Reference analogue | Description |
|----------|--------------|-------------|
| `p256_base_point` | `P256_GENERATOR` | Generator G |
| `p256_point_add` | `point_add(P, Q)` | P + Q on Weierstrass curve |
| `p256_scalar_mul_point` | `scalar_mult(k, P)` | k * P |
| `p256_scalar_add` | `scalar_add(a, b)` | a + b mod n |
| `p256_scalar_mul_scalar` | `scalar_mul(a, b)` | a * b mod n |
| `p256_scalar_inv` | `scalar_inv(a)` | a^{-1} mod n |
| `p256_point_x` | `point_x(P)` | x-coordinate extraction |
| `p256_point_sub` | `point_sub(P, Q)` | P - Q on Weierstrass curve |

## Design

Each operation is an `opaque` Lean constant, as in `Libcrux_specs.lean`. No proof
unfolds them, so every theorem stated over them holds for any implementation of these
signatures: the constants act as parameters. No algebraic property is stated in this file.

The analogue columns of the tables and the `Reference:` lines of the docstrings give the
names of the corresponding functions in reference implementations of the curves (the
ref10 / libsodium names `ge_*` and `sc_*` for Ed25519); they name no function of this
library or of a crate it is extracted from.

## References

* RFC 8032 -- Edwards-Curve Digital Signature Algorithm (EdDSA)
* NIST FIPS 186-5 -- Digital Signature Standard (DSS)
* RFC 9382 -- SPAKE2, a PAKE
* `Libcrux_specs.lean` -- DDH-level operations (X25519, P-256)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Libcrux.GroupOps

/-! ## Ed25519 Group Operations -/

/-- Ed25519 base point (generator G) in compressed form.
    Reference: `ED25519_BASEPOINT_COMPRESSED` (32 bytes). -/
opaque ed25519_base_point : Vector UInt8 32

/-- Ed25519 point addition: `P + Q` on the Edwards curve.
    Reference: `ge_add(P: &[u8; 32], Q: &[u8; 32]) -> [u8; 32]`.
    Both inputs and output are compressed Edwards points. -/
opaque ed25519_point_add : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- Ed25519 scalar multiplication (scalar-point): `s * P`.
    Reference: `ge_scalarmult(s: &[u8; 32], P: &[u8; 32]) -> [u8; 32]`.
    Used by the EdDSA extraction as `group_mul`. -/
opaque ed25519_group_mul : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- Ed25519 scalar multiplication in the scalar field: `a * b mod l`.
    Reference: `sc_mul(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32]`.
    Where `l` is the order of the Ed25519 base point. -/
opaque ed25519_scalar_mul : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- Ed25519 scalar addition in the scalar field: `a + b mod l`.
    Reference: `sc_add(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32]`. -/
opaque ed25519_scalar_add : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- Ed25519 base-point multiplication: `s * G`.
    Reference: `ge_scalarmult_base(s: &[u8; 32]) -> [u8; 32]`.
    Shorthand for `ed25519_group_mul s ed25519_base_point`. -/
opaque ed25519_scalar_basemul : Vector UInt8 32 → Vector UInt8 32

/-- Ed25519 challenge hash: `H(R || pk || msg) mod l`.
    Reference: `hash_challenge(r: &[u8; 32], pk: &[u8; 32], msg: &[u8; 32]) -> [u8; 32]`.
    Used for the EdDSA verification equation. -/
opaque ed25519_hash_challenge :
  Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## P-256 Group Operations -/

/-- P-256 base point (generator G) in compressed form.
    Reference: `P256_GENERATOR` (32 bytes, x-coordinate). -/
opaque p256_base_point : Vector UInt8 32

/-- P-256 point addition: `P + Q` on the Weierstrass curve.
    Reference: `point_add(P: &P256Point, Q: &P256Point) -> P256Point`.
    Compressed to 32-byte representation. -/
opaque p256_point_add : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- P-256 scalar-point multiplication: `k * P`.
    Reference: `scalar_mult(k: &[u8; 32], P: &P256Point) -> P256Point`.
    Compressed to 32-byte representation. -/
opaque p256_scalar_mul_point : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- P-256 scalar addition: `a + b mod n`.
    Reference: `scalar_add(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32]`.
    Where `n` is the order of the P-256 base point. -/
opaque p256_scalar_add : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- P-256 scalar multiplication (scalar field): `a * b mod n`.
    Reference: `scalar_mul(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32]`. -/
opaque p256_scalar_mul_scalar : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- P-256 scalar modular inverse: `a^{-1} mod n`.
    Reference: `scalar_inv(a: &[u8; 32]) -> [u8; 32]`.
    Used in ECDSA signing: `s = k^{-1} * (e + r * d)`. -/
opaque p256_scalar_inv : Vector UInt8 32 → Vector UInt8 32

/-- P-256 x-coordinate extraction: `x(P)`.
    Reference: `point_x(P: &P256Point) -> [u8; 32]`.
    Maps a curve point to its affine x-coordinate (reduced mod n for ECDSA). -/
opaque p256_point_x : Vector UInt8 32 → Vector UInt8 32

/-- P-256 point subtraction: `P - Q` on the Weierstrass curve.
    Reference: `point_sub(P: &P256Point, Q: &P256Point) -> P256Point`.
    Equivalent to `point_add(P, point_neg(Q))`. Used by SPAKE2. -/
opaque p256_point_sub : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- P-256 hash-to-scalar: `H(msg) mod n`.
    Reference: `hash_to_scalar(msg: &[u8; 32]) -> [u8; 32]`.
    Used by ECDSA for message hashing. -/
opaque p256_hash_to_scalar : Vector UInt8 32 → Vector UInt8 32

/-- P-256 transcript hash: `H(data)`.
    Reference: `hash(data: &[u8; 32]) -> [u8; 32]`.
    Used by SPAKE2 for key confirmation. -/
opaque p256_hash : Vector UInt8 32 → Vector UInt8 32

/-- P-256 SPAKE2 M constant (nothing-up-my-sleeve point).
    RFC 9382 Appendix A: M for P-256. -/
opaque p256_spake2_M : Vector UInt8 32

/-- P-256 SPAKE2 N constant (nothing-up-my-sleeve point).
    RFC 9382 Appendix A: N for P-256. -/
opaque p256_spake2_N : Vector UInt8 32

end CatCrypt.Crypto.Libcrux.GroupOps

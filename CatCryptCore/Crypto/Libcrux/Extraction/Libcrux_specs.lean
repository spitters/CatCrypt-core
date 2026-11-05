/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# libcrux-specs Extraction: Pure Crypto Function Signatures

Hand-transcribed type signatures from `libcrux/specs/libcrux-specs/src/`.
The Rust implementations are pure (no I/O, no panics for valid inputs),
so we model them as total Lean functions via `opaque` declarations.

## Source Files

| Module | Rust source | Main functions |
|--------|------------|----------------|
| SHA-256 | `sha256.rs` | `sha256` |
| HMAC | `hmac.rs` | `hmac_sha256` |
| HKDF | `hkdf.rs` | `hkdf_extract`, `hkdf_expand` |
| AES | `aes.rs` | `aes128_encrypt` |
| AES-GCM | `aes_gcm.rs` | `aes128_gcm_encrypt` |
| X25519 | `curve25519.rs` | `x25519_scalarmult`, `x25519_base` |
| P-256 | `p256.rs` | `scalar_mult`, `base_mult` |

## Design

Each Rust function is an `opaque` Lean constant of the Rust signature. The constants are
inhabited terms, so they add no axiom to `#print axioms`, and no proof unfolds them. Every
theorem stated over them therefore holds for any implementation of these signatures: the
constants act as parameters of the theorems. No property of the functions is stated in this
file; security statements over them bound advantages by those of explicit reductions.

## Fixed-Length Convention

The abstract type classes use `W → W → W` where `W = Vector UInt8 32`.
The Rust specs use mixed sizes (`[u8; 16]`, `[u8; 32]`, `&[u8]`).
The constants below are the fixed-length variants at the 32-byte level.

## References

* `libcrux/specs/libcrux-specs/src/` — Rust source
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs

/-! ## SHA-256 (sha256.rs) -/

/-- SHA-256 hash. Rust: `sha256(msg: &[u8]) -> [u8; 32]`.
    We model the fixed-length variant `sha256([u8; 32]) -> [u8; 32]`. -/
opaque sha256_32 : Vector UInt8 32 → Vector UInt8 32

/-! ## HMAC-SHA256 (hmac.rs) -/

/-- HMAC-SHA256. Rust: `hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32]`.
    Fixed-length variant: both key and message are 32 bytes. -/
opaque hmac_sha256_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## HKDF-SHA256 (hkdf.rs) -/

/-- HKDF-Extract: `PRK = HMAC-SHA256(salt, IKM)`.
    Rust: `hkdf_extract(salt: &[u8], ikm: &[u8]) -> [u8; 32]`.
    Fixed-length: 32-byte salt, 32-byte IKM → 32-byte PRK.
    Specializes to non-empty salt case. -/
opaque hkdf_extract_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- HKDF-Expand (first 32 bytes): `T(1) = HMAC-SHA256(PRK, info || 0x01)`.
    Rust: `hkdf_expand(prk: &[u8; 32], info: &[u8], length: usize) -> Vec<u8>`.
    Fixed-length: 32-byte PRK, 32-byte info → first 32 bytes of OKM.
    This is sufficient for HPKE/EDHOC where we only need 32 bytes of output. -/
opaque hkdf_expand_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## AES-128 (aes.rs) -/

/-- AES-128 block encryption.
    Rust: `aes128_encrypt(key: [u8; 16], plaintext: [u8; 16]) -> [u8; 16]`. -/
opaque aes128_encrypt : Vector UInt8 16 → Vector UInt8 16 → Vector UInt8 16

/-! ## AES-128-GCM (aes_gcm.rs) -/

/-- AES-128-GCM authenticated encryption (simplified fixed-length model).
    In the real Rust spec, AES-GCM takes (key, nonce, aad, plaintext) and
    produces (ciphertext, tag). For the abstract AEAD bridge, we model the
    combined operation on fixed-length 32-byte buffers.

    Semantic interpretation: `aes128_gcm_seal(key, plaintext, aad)` = ciphertext,
    where the nonce is derived deterministically (or passed as part of the key). -/
opaque aes128_gcm_seal_32 :
    Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- AES-128-GCM authenticated decryption (simplified fixed-length model). -/
opaque aes128_gcm_open_32 :
    Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## X25519 (curve25519.rs)

The intended denotation of both constants is RFC 7748 X25519. No theorem of this library
depends on it: the DDH game over `concreteDDH_X25519` treats the function as a black box.
-/

/-- X25519 scalar multiplication (RFC 7748 Diffie-Hellman).
    Computes `k * u` on Curve25519 with the RFC 7748 §5 clamp on `k` and
    high-bit mask on `u`. -/
opaque x25519_scalarmult : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- X25519 base point multiplication: `k * 9`. -/
opaque x25519_base : Vector UInt8 32 → Vector UInt8 32

/-! ## P-256 (p256.rs) -/

/-- P-256 scalar multiplication.
    Rust: `scalar_mult(k: &[u8; 32], p: &P256Point) -> P256Point`.
    We model the compressed form: 32-byte scalar × 32-byte point → 32-byte point.
    (In practice, the x-coordinate suffices for ECDH.) -/
opaque p256_scalar_mult_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- P-256 base point multiplication: `k * G`.
    Rust: `base_mult(k: &[u8; 32]) -> P256Point`.
    Compressed to 32-byte x-coordinate. -/
opaque p256_base_mult_32 : Vector UInt8 32 → Vector UInt8 32

/-! ## ristretto255 -/

/-- ristretto255 variable-base scalar multiplication.
    Rust: `scalar_mult(scalar: [u8; 32], point: [u8; 32]) -> [u8; 32]`.
    Computes `scalar * point` on the ristretto255 group. -/
opaque ristretto255_scalar_mult_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- ristretto255 fixed-base scalar multiplication: `scalar * G`.
    Rust: `base_mult(scalar: [u8; 32]) -> [u8; 32]`.
    Used for key generation: `public_key = base_mult(private_key)`. -/
opaque ristretto255_base_mult_32 : Vector UInt8 32 → Vector UInt8 32

/-- ristretto255 point addition: `p1 + p2`.
    Rust: `point_add(p1: [u8; 32], p2: [u8; 32]) -> [u8; 32]`. -/
opaque ristretto255_point_add_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- ristretto255 scalar modular inversion: `scalar^{-1} mod ell`.
    Rust: `scalar_invert(scalar: [u8; 32]) -> [u8; 32]`. -/
opaque ristretto255_scalar_invert_32 : Vector UInt8 32 → Vector UInt8 32

/-! ## SHA-512 (sha512.rs) -/

/-- SHA-512 hash (64-byte output).
    Rust: `sha512(msg: &[u8]) -> [u8; 64]`.
    Fixed-length: 64-byte input → 64-byte output (for Ed25519 internal hashing). -/
opaque sha512_64 : Vector UInt8 64 → Vector UInt8 64

/-! ## BLAKE2s (blake2.rs) -/

/-- BLAKE2s-256 hash (32-byte output).
    Rust: `blake2s(msg: &[u8], key: &[u8]) -> [u8; 32]`.
    Fixed-length: 32-byte message, 32-byte key → 32-byte tag. -/
opaque blake2s_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## SHA-3 (sha3.rs) -/

/-- SHA3-256 hash (32-byte output).
    Rust: `sha3_256(msg: &[u8]) -> [u8; 32]`.
    Fixed-length: 32-byte input → 32-byte output. -/
opaque sha3_256_32 : Vector UInt8 32 → Vector UInt8 32

/-! ## Poly1305 (poly1305.rs) -/

/-- Poly1305 MAC.
    Rust: `poly1305(msg: &[u8], key: &[u8; 32]) -> [u8; 16]`.
    Fixed-length: 32-byte key, 32-byte message → 16-byte tag. -/
opaque poly1305_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 16

/-! ## ChaCha20-Poly1305 (chacha20poly1305.rs) -/

/-- ChaCha20-Poly1305 AEAD encryption (simplified fixed-length model).
    Rust: `chacha20poly1305_encrypt(key, nonce, aad, plaintext) -> (ciphertext, tag)`.
    Fixed-length: 32-byte key, 32-byte plaintext, 32-byte AAD → 32-byte ciphertext.
    The nonce is derived or passed as part of the key in the abstract model. -/
opaque chacha20poly1305_seal_32 :
    Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-- ChaCha20-Poly1305 AEAD decryption (simplified fixed-length model). -/
opaque chacha20poly1305_open_32 :
    Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32

/-! ## Ed25519 (ed25519.rs) -/

/-- Ed25519 public key derivation.
    Rust: `ed25519_public_key(secret_key: &[u8; 32]) -> [u8; 32]`.
    Computes `A = clamp(H(sk)[..32]) * B` where B is the Ed25519 base point. -/
opaque ed25519_public_key : Vector UInt8 32 → Vector UInt8 32

/-- Ed25519 signature.
    Rust: `ed25519_sign(secret_key: &[u8; 32], msg: &[u8]) -> [u8; 64]`.
    Fixed-length: 32-byte message → 64-byte signature.
    The full Ed25519 signing algorithm (RFC 8032). -/
opaque ed25519_sign_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 64

/-- Ed25519 verification.
    Rust: `ed25519_verify(public_key: &[u8; 32], msg: &[u8], signature: &[u8; 64]) -> bool`.
    Fixed-length: 32-byte public key, 32-byte message, 64-byte signature → Bool. -/
opaque ed25519_verify_32 : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 64 → Bool

/-! ## ECDSA-P256 (ecdsa_p256.rs) -/

/-- ECDSA-P256 signature (simplified fixed-length model).
    Rust: `ecdsa_p256_sign(secret_key, msg_hash, k) -> (r, s)`.
    Fixed-length: 32-byte secret key, 32-byte hash, 32-byte nonce → 32-byte pair. -/
opaque ecdsa_p256_sign_32 :
    Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 × Vector UInt8 32

/-- ECDSA-P256 verification (simplified fixed-length model).
    Returns whether the (r, s) signature is valid for the given hash under the public key. -/
opaque ecdsa_p256_verify_32 :
    Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 × Vector UInt8 32 → Bool

end CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs

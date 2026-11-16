//! ML-KEM-768: Hax-extractable pure Rust SPECIFICATION (proof anchor).
//!
//! ## Role (see `HAX_REFERENCE_ROLE.md`)
//!
//! This crate is the **role-2 crypto-proof anchor** — the schoolbook ML-KEM
//! *shape* CatCrypt's ML-KEM security proofs are stated against. Three things
//! connect to it, at three different strengths — stated precisely so the anchor
//! is not read as more than it is:
//!
//! - **The security proof is abstract.** `mlkem_cca_security` (FO transform over
//!   module-LWE, hashes as random oracles) and `FullSecurity` are stated over
//!   `MLKEMParams`, *not* over this crate's body — they do not import the
//!   extraction. They establish ML-KEM-shape IND-CCA under MLWE + RO leaves.
//! - **The polynomial arithmetic is tied, up to the encryption formula.**
//!   `MlkemHaxLowCTBridge`'s `*_eq_verified` prove this extraction's ring-op
//!   leaves equal a verified `ZMod 3329` reference (`NttPolyVerified`), and
//!   `SurfaceDeps` CONN-2c (`mlkem_extracted_encrypt_backbone_binding_uc`)
//!   composes them into the KEM ciphertext formula: the pre-compression `(u,v)`
//!   provably equal `u = Aᵀr + e1`, `v = t·r + e2 + encode(m)` in that ring. The
//!   tie reaches the encryption *expression*, stopping before the lossy
//!   compression, PRF/CBD sampling, and byte (en/de)coding (the modeled
//!   boundary). It is definitional `rfl` (fragile under a `cargo hax` regen — see
//!   the corres/ascend note below).
//! - **The whole-KEM bridge is not yet closed.** The `*_e2e_uc_secure` theorems
//!   in `SurfaceDeps` route through a `MlkemDeps` typeclass that has no fields, so
//!   they do not yet constrain this crate's KEM composition. Carrying the
//!   encryption-backbone tie the rest of the way — the byte-exact `kpke_* ≡ base
//!   module-LWE PKE` including the compression-error analysis — is the research-
//!   grade frontier; the corres / ascend / ParamTransfer machinery is the
//!   intended route, replacing the `rfl` ties with parametricity transport.
//!
//! It is **FIPS-203-conformant and NIST-KAT-validated**: `tests/nist_kat.rs`
//! drives this crate's own keygen/encaps/decaps on the official ML-KEM-768 NIST
//! KAT vectors (libcrux `mlkem768_nistkats.json`) and asserts SHA3-256(ek),
//! SHA3-256(dk), SHA3-256(ct) and the shared secret byte-for-byte. The `specs/`
//! module provides a real, byte-exact FIPS-202 Keccak (SHA3-256/512, SHAKE-128/256)
//! in pure dependency-free Rust, separately pinned against the published FIPS-202
//! digests.
//!
//! The polynomial *layer* (`poly.rs`) still exposes a schoolbook negacyclic
//! multiply (kept for the ring-op security tie below), but the KEM itself runs
//! in the real FIPS-203 **NTT domain**: `poly.rs` also provides plain-integer
//! `ntt`/`inv_ntt`/`ntt_mul` (Algorithms 9–11), self-checked against schoolbook,
//! so the stored t̂/ŝ and the compressed (u, v) are byte-identical to FIPS-203.
//! Byte encoding (FIPS 203 §4.2.1), compression (§4.2.3), CBD (§4.2.2), K-PKE
//! (§5) and the FO KEM (§6-7) all follow the FIPS-203 structure.
//!
//! **The independently-emitted sibling crate [`crates/catcrypt-mlkem768`]** is
//! the compiler-emitted NTT-domain deployment (verified CatCrypt compiler +
//! PQClean Keccak), also NIST-KAT-gated. Both crates realize the SAME abstract
//! ML-KEM shape (NTT ≅ schoolbook: same ring elements, different representation);
//! the role-2 security proved here applies to that shape.
//!
//! Extraction mechanics (faest-hax methodology): `src/` modules are
//! hax-extractable (fixed-size arrays, bounded loops); the Lean bridge connects
//! the extraction to the CatCrypt ML-KEM formalization.

pub mod types;
pub mod field;
pub mod poly;
pub mod encode;
pub mod compress;
pub mod cbd;
pub mod kpke;
pub mod mlkem;

pub mod specs;

pub use types::*;

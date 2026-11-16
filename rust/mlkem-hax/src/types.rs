//! ML-KEM-768 type definitions and constants (FIPS 203).
//!
//! All types use fixed-size arrays for hax extraction compatibility.
//! Maps to CatCrypt's ML-KEM-768 concrete parameter set.

/// Field modulus q = 3329.
pub const Q: u32 = 3329;

/// Polynomial degree n = 256.
pub const N: usize = 256;

/// Module rank k = 3 (ML-KEM-768).
pub const K: usize = 3;

/// CBD parameter η₁ = 2.
pub const ETA1: usize = 2;

/// CBD parameter η₂ = 2.
pub const ETA2: usize = 2;

/// Compression parameter d_u = 10.
pub const DU: u32 = 10;

/// Compression parameter d_v = 4.
pub const DV: u32 = 4;

/// Shared secret size: 32 bytes.
pub const SS_BYTES: usize = 32;

/// Seed size: 32 bytes.
pub const SEED_BYTES: usize = 32;

/// Polynomial: 256 coefficients in [0, q).
/// Maps to CatCrypt's `Rq = (ZMod 3329)[X]/(X^256 + 1)`.
pub type Poly = [u16; N];

/// Polynomial vector of dimension k.
/// Maps to CatCrypt's `RqVec K768`.
pub type PolyVec = [Poly; K];

/// Polynomial matrix k × k.
/// Maps to CatCrypt's `RqMat K768`.
pub type PolyMat = [PolyVec; K];

/// Encryption key (IndCPA public key): encoded t̂ + seed ρ.
/// Size = 12 * k * n/8 + 32 = 12 * 3 * 32 + 32 = 1184 bytes.
pub const EK_BYTES: usize = 1184;

/// Decryption key (full ML-KEM secret key):
/// dk_pke ‖ ek ‖ H(ek) ‖ z
/// Size = 384*k + 1184 + 32 + 32 = 2400 bytes.
pub const DK_BYTES: usize = 2400;

/// Ciphertext: compressed (u, v).
/// Size = 32*d_u*k + 32*d_v = 960 + 128 = 1088 bytes.
pub const CT_BYTES: usize = 1088;

/// Inner PKE encryption key.
pub type IndcpaEk = [u8; EK_BYTES];

/// Inner PKE decryption key: encoded ŝ.
/// Size = 12 * k * n/8 = 1152 bytes.
pub const INDCPA_DK_BYTES: usize = 1152;
pub type IndcpaDk = [u8; INDCPA_DK_BYTES];

/// Full ML-KEM decapsulation key.
pub type DecapsKey = [u8; DK_BYTES];

/// Ciphertext.
pub type Ciphertext = [u8; CT_BYTES];

/// Shared secret.
pub type SharedSecret = [u8; SS_BYTES];

/// Randomness for key generation: d (32 bytes).
pub type KeygenSeed = [u8; SEED_BYTES];

/// Randomness for encapsulation: m (32 bytes).
pub type EncapsRand = [u8; SS_BYTES];

/// Zero polynomial.
pub const ZERO_POLY: Poly = [0u16; N];

/// Zero polynomial vector.
pub const ZERO_VEC: PolyVec = [ZERO_POLY; K];

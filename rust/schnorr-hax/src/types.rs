//! Schnorr signature type definitions.
//!
//! All types use fixed-size arrays for hax extraction compatibility.

/// Scalar field element: 32 bytes (big-endian).
/// Maps to CatCrypt's `SchnorrScalar`.
pub type SchnorrScalar = [u8; 32];

/// Serialized group element: 32 bytes (compressed point).
/// Maps to CatCrypt's `SchnorrPoint`.
pub type SchnorrPoint = [u8; 32];

/// Zero scalar (additive identity).
pub const ZERO_SCALAR: SchnorrScalar = [0u8; 32];

/// Zero point (used as placeholder; identity is group-dependent).
pub const ZERO_POINT: SchnorrPoint = [0u8; 32];

/// Schnorr signature: (R, s) where R = g^k and s = k + H(R, pk, msg) * sk.
/// Maps to CatCrypt's `SchnorrSignature`.
#[derive(Clone, Copy, Debug)]
pub struct SchnorrSignature {
    /// Commitment R = g^k.
    pub r: SchnorrPoint,
    /// Response s = k + H(R, pk, msg) * sk.
    pub s: SchnorrScalar,
}

/// Default (zero) signature.
pub const ZERO_SIGNATURE: SchnorrSignature = SchnorrSignature {
    r: ZERO_POINT,
    s: ZERO_SCALAR,
};

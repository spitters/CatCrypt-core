//! Schnorr signature scheme: keygen, sign, verify.
//!
//! All functions are parameterized by the `SchnorrCrypto` trait for
//! group independence.

use crate::types::*;

/// Abstract cryptographic operations for Schnorr signatures.
///
/// Implementors provide concrete group and hash operations.
/// All operations are pure functions with no side effects.
pub trait SchnorrCrypto: Copy {
    /// Scalar addition: a + b mod q.
    fn scalar_add(a: &SchnorrScalar, b: &SchnorrScalar) -> SchnorrScalar;

    /// Scalar multiplication: a * b mod q.
    fn scalar_mul(a: &SchnorrScalar, b: &SchnorrScalar) -> SchnorrScalar;

    /// Scalar multiplicative inverse: a^{-1} mod q.
    /// Precondition: a != 0.
    fn scalar_inv(a: &SchnorrScalar) -> SchnorrScalar;

    /// Scalar multiplication on the group: s * P.
    /// (In multiplicative notation: P^s.)
    fn group_mul(s: &SchnorrScalar, p: &SchnorrPoint) -> SchnorrPoint;

    /// Group element addition: P + Q (group operation).
    /// (In multiplicative notation: P * Q.)
    fn group_add(a: &SchnorrPoint, b: &SchnorrPoint) -> SchnorrPoint;

    /// Hash to challenge scalar: c = H(R, pk, msg).
    fn hash_challenge(r: &SchnorrPoint, pk: &SchnorrPoint, msg: &[u8; 32]) -> SchnorrScalar;

    /// The group generator G (base point).
    fn generator() -> SchnorrPoint;

    /// The group identity element (point at infinity / zero in additive notation).
    fn identity() -> SchnorrPoint;
}

/// Scalar equality check (byte-by-byte comparison).
pub fn scalar_eq(a: &SchnorrScalar, b: &SchnorrScalar) -> bool {
    let mut eq = true;
    for i in 0..32 {
        if a[i] != b[i] {
            eq = false;
        }
    }
    eq
}

/// Point equality check (byte-by-byte comparison).
pub fn point_eq(a: &SchnorrPoint, b: &SchnorrPoint) -> bool {
    let mut eq = true;
    for i in 0..32 {
        if a[i] != b[i] {
            eq = false;
        }
    }
    eq
}

/// Key generation: given secret key sk, compute public key pk = g^sk.
///
/// Returns (sk, pk).
pub fn keygen<C: SchnorrCrypto>(sk: &SchnorrScalar) -> (SchnorrScalar, SchnorrPoint) {
    let pk = C::group_mul(sk, &C::generator());
    (*sk, pk)
}

/// Sign: given secret key sk, nonce k, and message msg, produce a Schnorr signature.
///
/// Computes:
///   R = g^k
///   c = H(R, pk, msg)
///   s = k + c * sk
///
/// Returns SchnorrSignature { r: R, s: s }.
pub fn sign<C: SchnorrCrypto>(
    sk: &SchnorrScalar,
    k: &SchnorrScalar,
    msg: &[u8; 32],
) -> SchnorrSignature {
    let (_, pk) = keygen::<C>(sk);
    let r = C::group_mul(k, &C::generator());
    let c = C::hash_challenge(&r, &pk, msg);
    let c_sk = C::scalar_mul(&c, sk);
    let s = C::scalar_add(k, &c_sk);
    SchnorrSignature { r, s }
}

/// Verify: check that g^s == R + H(R, pk, msg) * pk.
///
/// Returns true if the signature is valid.
pub fn verify<C: SchnorrCrypto>(
    pk: &SchnorrPoint,
    msg: &[u8; 32],
    sig: &SchnorrSignature,
) -> bool {
    // c = H(R, pk, msg)
    let c = C::hash_challenge(&sig.r, pk, msg);

    // LHS: g^s
    let lhs = C::group_mul(&sig.s, &C::generator());

    // RHS: R + c * pk
    let c_pk = C::group_mul(&c, pk);
    let rhs = C::group_add(&sig.r, &c_pk);

    // Check: g^s == R + c * pk
    point_eq(&lhs, &rhs)
}

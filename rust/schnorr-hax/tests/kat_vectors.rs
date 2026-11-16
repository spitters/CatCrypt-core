//! Known Answer Tests for Schnorr signatures.
//!
//! Since the protocol logic is parameterized by `SchnorrCrypto`, we provide
//! a toy concrete implementation over the additive group Z_q (q = 65521 prime)
//! and verify correctness: field axioms, keygen, sign, verify, and failure cases.
//!
//! ## Toy group (same approach as frost-hax)
//!
//! We use an additive group over Z_{65521} (the largest prime < 2^16).
//! Scalar field and group share the same modulus q, ensuring consistency
//! between scalar arithmetic and group operations:
//! - group_add(A, B) = (A + B) mod q   (group operation)
//! - group_mul(s, P) = s * P mod q     (scalar multiplication)
//! - Generator G = 3
//! - Schnorr: s*G = k*G + c*(sk*G) = (k + c*sk)*G
//!
//! This is NOT cryptographic; it validates protocol logic only.

use schnorr_hax::types::*;
use schnorr_hax::scheme::*;

// ============================================================
// Toy SchnorrCrypto: additive group Z_q, q = 65521 (prime)
// ============================================================

const TOY_Q: u64 = 65521; // scalar field = group order (prime)
const TOY_G: u64 = 3;     // generator (arbitrary non-zero element)

// --- Scalar/group operations (both mod q) ---

fn qadd(a: u64, b: u64) -> u64 { (a + b) % TOY_Q }
#[allow(dead_code)]
fn qsub(a: u64, b: u64) -> u64 { (a + TOY_Q - b % TOY_Q) % TOY_Q }
fn qmul(a: u64, b: u64) -> u64 { (a * b) % TOY_Q }

fn qpow(mut base: u64, mut exp: u64) -> u64 {
    let mut result: u64 = 1;
    base %= TOY_Q;
    while exp > 0 {
        if exp & 1 == 1 { result = qmul(result, base); }
        exp >>= 1;
        base = qmul(base, base);
    }
    result
}

fn qinv(a: u64) -> u64 { qpow(a, TOY_Q - 2) }

// --- Encoding helpers ---

fn u64_to_scalar(v: u64) -> SchnorrScalar {
    let mut s = ZERO_SCALAR;
    let bytes = (v % TOY_Q).to_be_bytes();
    s[24..32].copy_from_slice(&bytes);
    s
}

fn scalar_to_u64(s: &SchnorrScalar) -> u64 {
    let mut v: u64 = 0;
    for i in 24..32 { v = (v << 8) | s[i] as u64; }
    v % TOY_Q
}

fn u64_to_point(v: u64) -> SchnorrPoint {
    let mut p = ZERO_POINT;
    let bytes = (v % TOY_Q).to_be_bytes();
    p[24..32].copy_from_slice(&bytes);
    p
}

fn point_to_u64(p: &SchnorrPoint) -> u64 {
    let mut v: u64 = 0;
    for i in 24..32 { v = (v << 8) | p[i] as u64; }
    v % TOY_Q
}

// --- FrostCrypto-style hash helper ---

fn hash_bytes_to_u64(data: &[u8]) -> u64 {
    let mut h: u64 = 1;
    for &b in data { h = (h.wrapping_mul(31).wrapping_add(b as u64)) % TOY_Q; }
    if h == 0 { 1 } else { h }
}

// --- SchnorrCrypto impl ---

#[derive(Copy, Clone)]
struct ToyCrypto;

impl SchnorrCrypto for ToyCrypto {
    fn scalar_add(a: &SchnorrScalar, b: &SchnorrScalar) -> SchnorrScalar {
        u64_to_scalar(qadd(scalar_to_u64(a), scalar_to_u64(b)))
    }

    fn scalar_mul(a: &SchnorrScalar, b: &SchnorrScalar) -> SchnorrScalar {
        u64_to_scalar(qmul(scalar_to_u64(a), scalar_to_u64(b)))
    }

    fn scalar_inv(a: &SchnorrScalar) -> SchnorrScalar {
        u64_to_scalar(qinv(scalar_to_u64(a)))
    }

    fn group_mul(s: &SchnorrScalar, p: &SchnorrPoint) -> SchnorrPoint {
        // Additive group: s * P mod q (scalar multiplication = multiplication)
        u64_to_point(qmul(scalar_to_u64(s), point_to_u64(p)))
    }

    fn group_add(a: &SchnorrPoint, b: &SchnorrPoint) -> SchnorrPoint {
        // Additive group: A + B mod q
        u64_to_point(qadd(point_to_u64(a), point_to_u64(b)))
    }

    fn hash_challenge(r: &SchnorrPoint, pk: &SchnorrPoint, msg: &[u8; 32]) -> SchnorrScalar {
        let rv = point_to_u64(r);
        let pkv = point_to_u64(pk);
        let mv = hash_bytes_to_u64(msg);
        u64_to_scalar(qadd(qadd(rv, pkv), mv))
    }

    fn generator() -> SchnorrPoint { u64_to_point(TOY_G) }
    fn identity() -> SchnorrPoint { u64_to_point(0) }
}

// ============================================================
// 1. Field axioms: commutativity, associativity, inverse
// ============================================================

#[test]
fn kat_field_axioms() {
    // Commutativity
    assert_eq!(qmul(42, 17), qmul(17, 42), "mul commutativity");
    assert_eq!(qadd(42, 17), qadd(17, 42), "add commutativity");

    // Associativity
    assert_eq!(qmul(qmul(3, 5), 7), qmul(3, qmul(5, 7)), "mul associativity");
    assert_eq!(qadd(qadd(3, 5), 7), qadd(3, qadd(5, 7)), "add associativity");

    // Inverse
    for &a in &[1u64, 2, 42, 1000, 65520] {
        assert_eq!(qmul(a, qinv(a)), 1, "a * a^(-1) = 1 for a={}", a);
    }

    // Additive identity
    for &a in &[0u64, 1, 42, 65520] {
        assert_eq!(qadd(a, 0), a, "a + 0 = a for a={}", a);
    }

    // Multiplicative identity
    for &a in &[0u64, 1, 42, 65520] {
        assert_eq!(qmul(a, 1), a, "a * 1 = a for a={}", a);
    }

    // Verify q is prime (Fermat test)
    assert_eq!(qpow(2, TOY_Q - 1), 1, "Fermat test: 2^(q-1) = 1");
    assert_eq!(qpow(7, TOY_Q - 1), 1, "Fermat test: 7^(q-1) = 1");
}

// ============================================================
// 2. Scalar roundtrip
// ============================================================

#[test]
fn kat_scalar_roundtrip() {
    for &v in &[0u64, 1, 42, 1000, 65520] {
        let s = u64_to_scalar(v);
        assert_eq!(scalar_to_u64(&s), v % TOY_Q, "scalar roundtrip for v={}", v);
    }
    // Point roundtrip
    for &v in &[0u64, 1, 42, 1000, 65520] {
        let p = u64_to_point(v);
        assert_eq!(point_to_u64(&p), v % TOY_Q, "point roundtrip for v={}", v);
    }
}

// ============================================================
// 3. Keygen: pk = sk * G
// ============================================================

#[test]
fn kat_keygen() {
    let sk = u64_to_scalar(42);
    let (returned_sk, pk) = keygen::<ToyCrypto>(&sk);

    // Returned sk should be the same
    assert!(scalar_eq(&returned_sk, &sk), "keygen returns same sk");

    // pk = sk * G = 42 * 3 = 126 (mod q)
    let expected_pk = qmul(42, TOY_G);
    assert_eq!(point_to_u64(&pk), expected_pk, "pk = sk * G");

    // Different sk gives different pk
    let sk2 = u64_to_scalar(99);
    let (_, pk2) = keygen::<ToyCrypto>(&sk2);
    assert!(!point_eq(&pk, &pk2), "different sk => different pk");
}

// ============================================================
// 4. Sign + verify roundtrip
// ============================================================

#[test]
fn kat_sign_verify_roundtrip() {
    let sk = u64_to_scalar(42);
    let k = u64_to_scalar(7);
    let msg = [0u8; 32];

    let sig = sign::<ToyCrypto>(&sk, &k, &msg);

    // Verify the signature
    let (_, pk) = keygen::<ToyCrypto>(&sk);
    assert!(verify::<ToyCrypto>(&pk, &msg, &sig), "sign + verify roundtrip");

    // Manual verification of the equation:
    // R = k * G = 7 * 3 = 21
    assert_eq!(point_to_u64(&sig.r), qmul(7, TOY_G), "R = k * G");

    // c = H(R, pk, msg)
    let c = ToyCrypto::hash_challenge(&sig.r, &pk, &msg);
    // s = k + c * sk
    let expected_s = qadd(7, qmul(scalar_to_u64(&c), 42));
    assert_eq!(scalar_to_u64(&sig.s), expected_s, "s = k + c * sk");
}

// ============================================================
// 5. Wrong message fails
// ============================================================

#[test]
fn kat_wrong_message_fails() {
    let sk = u64_to_scalar(42);
    let k = u64_to_scalar(7);
    let msg = [0u8; 32];
    let mut wrong_msg = [0u8; 32];
    wrong_msg[0] = 1;

    let sig = sign::<ToyCrypto>(&sk, &k, &msg);
    let (_, pk) = keygen::<ToyCrypto>(&sk);

    assert!(verify::<ToyCrypto>(&pk, &msg, &sig), "correct message should verify");
    assert!(!verify::<ToyCrypto>(&pk, &wrong_msg, &sig), "wrong message should fail");
}

// ============================================================
// 6. Wrong key fails
// ============================================================

#[test]
fn kat_wrong_key_fails() {
    let sk = u64_to_scalar(42);
    let k = u64_to_scalar(7);
    let msg = [0u8; 32];

    let sig = sign::<ToyCrypto>(&sk, &k, &msg);

    // Wrong public key
    let wrong_sk = u64_to_scalar(99);
    let (_, wrong_pk) = keygen::<ToyCrypto>(&wrong_sk);
    let (_, correct_pk) = keygen::<ToyCrypto>(&sk);

    assert!(verify::<ToyCrypto>(&correct_pk, &msg, &sig), "correct key should verify");
    assert!(!verify::<ToyCrypto>(&wrong_pk, &msg, &sig), "wrong key should fail");
}

// ============================================================
// 7. Tampered signature fails
// ============================================================

#[test]
fn kat_tampered_signature_fails() {
    let sk = u64_to_scalar(42);
    let k = u64_to_scalar(7);
    let msg = [0u8; 32];

    let sig = sign::<ToyCrypto>(&sk, &k, &msg);
    let (_, pk) = keygen::<ToyCrypto>(&sk);

    assert!(verify::<ToyCrypto>(&pk, &msg, &sig), "original signature should verify");

    // Tamper with s
    let bad_s = ToyCrypto::scalar_add(&sig.s, &u64_to_scalar(1));
    let tampered_sig_s = SchnorrSignature { r: sig.r, s: bad_s };
    assert!(!verify::<ToyCrypto>(&pk, &msg, &tampered_sig_s), "tampered s should fail");

    // Tamper with R
    let bad_r = ToyCrypto::group_add(&sig.r, &u64_to_point(1));
    let tampered_sig_r = SchnorrSignature { r: bad_r, s: sig.s };
    assert!(!verify::<ToyCrypto>(&pk, &msg, &tampered_sig_r), "tampered R should fail");
}

// ============================================================
// 8. RFC 8032 Ed25519 structure (32-byte scalar, 32-byte point)
// ============================================================

#[test]
fn kat_rfc8032_structure() {
    // Ed25519 uses 32-byte scalars and 32-byte compressed points.
    // Our types match this structure.
    let sk: SchnorrScalar = [0u8; 32];
    let pk: SchnorrPoint = [0u8; 32];
    let _sig = SchnorrSignature { r: pk, s: sk };

    // Signature is (R: 32 bytes, s: 32 bytes) = 64 bytes total,
    // matching Ed25519 signature format.
    assert_eq!(
        core::mem::size_of::<SchnorrSignature>(),
        64,
        "signature = 64 bytes (R || s), matching Ed25519 format"
    );
}

// ============================================================
// 9. Type sizes
// ============================================================

#[test]
fn kat_type_sizes() {
    assert_eq!(core::mem::size_of::<SchnorrScalar>(), 32, "SchnorrScalar = 32 bytes");
    assert_eq!(core::mem::size_of::<SchnorrPoint>(), 32, "SchnorrPoint = 32 bytes");
    assert_eq!(core::mem::size_of::<SchnorrSignature>(), 64, "SchnorrSignature = 64 bytes");
    assert_eq!(ZERO_SCALAR, [0u8; 32], "ZERO_SCALAR is all zeros");
    assert_eq!(ZERO_POINT, [0u8; 32], "ZERO_POINT is all zeros");
}

// ============================================================
// 10. Hash challenge determinism
// ============================================================

#[test]
fn kat_hash_challenge_determinism() {
    let r = u64_to_point(21);
    let pk = u64_to_point(126);
    let msg = [0u8; 32];

    let c1 = ToyCrypto::hash_challenge(&r, &pk, &msg);
    let c2 = ToyCrypto::hash_challenge(&r, &pk, &msg);

    assert!(scalar_eq(&c1, &c2), "hash_challenge is deterministic");

    // Different inputs give different outputs
    let mut msg2 = [0u8; 32];
    msg2[0] = 1;
    let c3 = ToyCrypto::hash_challenge(&r, &pk, &msg2);
    assert!(!scalar_eq(&c1, &c3), "different msg => different challenge");

    let r2 = u64_to_point(22);
    let c4 = ToyCrypto::hash_challenge(&r2, &pk, &msg);
    assert!(!scalar_eq(&c1, &c4), "different R => different challenge");

    let pk2 = u64_to_point(127);
    let c5 = ToyCrypto::hash_challenge(&r, &pk2, &msg);
    assert!(!scalar_eq(&c1, &c5), "different pk => different challenge");
}

// ============================================================
// 11. Signature determinism
// ============================================================

#[test]
fn kat_signature_determinism() {
    let sk = u64_to_scalar(42);
    let k = u64_to_scalar(7);
    let msg = [0u8; 32];

    let sig1 = sign::<ToyCrypto>(&sk, &k, &msg);
    let sig2 = sign::<ToyCrypto>(&sk, &k, &msg);

    assert!(point_eq(&sig1.r, &sig2.r), "R is deterministic");
    assert!(scalar_eq(&sig1.s, &sig2.s), "s is deterministic");
}

// ============================================================
// 12. Multiple messages
// ============================================================

#[test]
fn kat_multiple_messages() {
    let sk = u64_to_scalar(42);
    let (_, pk) = keygen::<ToyCrypto>(&sk);

    // Sign three different messages with different nonces
    let msgs: [[u8; 32]; 3] = {
        let mut m = [[0u8; 32]; 3];
        m[0][0] = 1;
        m[1][0] = 2;
        m[2][0] = 3;
        m
    };
    let nonces = [u64_to_scalar(11), u64_to_scalar(13), u64_to_scalar(17)];

    for i in 0..3 {
        let sig = sign::<ToyCrypto>(&sk, &nonces[i], &msgs[i]);
        assert!(
            verify::<ToyCrypto>(&pk, &msgs[i], &sig),
            "message {} should verify", i
        );

        // Cross-verification should fail: sig for msg[i] should not verify against msg[(i+1)%3]
        let other_msg_idx = (i + 1) % 3;
        assert!(
            !verify::<ToyCrypto>(&pk, &msgs[other_msg_idx], &sig),
            "sig for msg[{}] should not verify against msg[{}]", i, other_msg_idx
        );
    }
}

// ============================================================
// 13. Identity element
// ============================================================

#[test]
fn kat_identity_element() {
    let id = ToyCrypto::identity();
    assert_eq!(point_to_u64(&id), 0, "identity is 0 in additive group");

    // P + identity = P
    let p = u64_to_point(42);
    let sum = ToyCrypto::group_add(&p, &id);
    assert!(point_eq(&sum, &p), "P + identity = P");

    // identity + P = P
    let sum2 = ToyCrypto::group_add(&id, &p);
    assert!(point_eq(&sum2, &p), "identity + P = P");

    // 0 * P = identity
    let zero = u64_to_scalar(0);
    let zero_p = ToyCrypto::group_mul(&zero, &p);
    assert!(point_eq(&zero_p, &id), "0 * P = identity");

    // 1 * P = P
    let one = u64_to_scalar(1);
    let one_p = ToyCrypto::group_mul(&one, &p);
    assert!(point_eq(&one_p, &p), "1 * P = P");
}

// ============================================================
// 14. Generator properties
// ============================================================

#[test]
fn kat_generator_properties() {
    let g = ToyCrypto::generator();
    assert_eq!(point_to_u64(&g), TOY_G, "generator = 3");

    // G != identity
    let id = ToyCrypto::identity();
    assert!(!point_eq(&g, &id), "generator != identity");

    // G != 0 (redundant with above for additive group, but conceptually distinct)
    assert_ne!(point_to_u64(&g), 0, "generator is non-zero");

    // s * G for various scalars
    for &s_val in &[1u64, 2, 3, 42, 65520] {
        let s = u64_to_scalar(s_val);
        let result = ToyCrypto::group_mul(&s, &g);
        let expected = qmul(s_val, TOY_G);
        assert_eq!(
            point_to_u64(&result), expected,
            "{} * G = {} * {} = {} (mod q)", s_val, s_val, TOY_G, expected
        );
    }

    // Scalar multiplication distributes: (a + b) * G = a*G + b*G
    let a = u64_to_scalar(42);
    let b = u64_to_scalar(17);
    let a_plus_b = ToyCrypto::scalar_add(&a, &b);
    let lhs = ToyCrypto::group_mul(&a_plus_b, &g);
    let rhs = ToyCrypto::group_add(
        &ToyCrypto::group_mul(&a, &g),
        &ToyCrypto::group_mul(&b, &g),
    );
    assert!(point_eq(&lhs, &rhs), "(a+b)*G = a*G + b*G");
}

// ============================================================
// 15. Verification equation algebra
// ============================================================

#[test]
fn kat_verification_equation_algebra() {
    // Directly verify the Schnorr equation: s*G = R + c*pk
    // where R = k*G, pk = sk*G, s = k + c*sk, c = H(R, pk, msg).
    //
    // LHS: s*G = (k + c*sk)*G = k*G + c*sk*G = R + c*pk = RHS
    let sk_val: u64 = 100;
    let k_val: u64 = 37;
    let _sk = u64_to_scalar(sk_val);
    let _k = u64_to_scalar(k_val);

    let pk_val = qmul(sk_val, TOY_G);
    let r_val = qmul(k_val, TOY_G);
    let pk = u64_to_point(pk_val);
    let r = u64_to_point(r_val);

    let msg = [0u8; 32];
    let c = ToyCrypto::hash_challenge(&r, &pk, &msg);
    let c_val = scalar_to_u64(&c);

    // s = k + c * sk (mod q)
    let s_val = qadd(k_val, qmul(c_val, sk_val));
    let s = u64_to_scalar(s_val);

    // LHS: s * G
    let lhs_val = qmul(s_val, TOY_G);

    // RHS: R + c * pk = k*G + c * sk * G = (k + c*sk) * G
    let rhs_val = qadd(r_val, qmul(c_val, pk_val));

    assert_eq!(lhs_val, rhs_val, "s*G = R + c*pk (algebraically)");

    // Also verify via the API
    let sig = SchnorrSignature { r, s };
    assert!(verify::<ToyCrypto>(&pk, &msg, &sig), "API verify agrees");
}

// ============================================================
// Cross-library validation: k256 (secp256k1)
// ============================================================

/// Compare scalar arithmetic (add, mul) with the k256 crate over
/// the secp256k1 scalar field. Both implementations must satisfy
/// the same field axioms.
#[test]
fn test_cross_schnorr_scalar_arithmetic() {
    use k256::elliptic_curve::ops::Reduce;
    use k256::Scalar;
    use k256::U256;

    // Test case: a = 42, b = 17
    // In any prime field: a + b = 59, a * b = 714

    // k256 scalars (secp256k1 order ~ 2^256)
    let a_k256 = <Scalar as Reduce<U256>>::reduce_bytes(
        &{
            let mut bytes = [0u8; 32];
            bytes[31] = 42;
            bytes.into()
        }
    );
    let b_k256 = <Scalar as Reduce<U256>>::reduce_bytes(
        &{
            let mut bytes = [0u8; 32];
            bytes[31] = 17;
            bytes.into()
        }
    );

    // Addition: a + b
    let sum_k256 = a_k256 + b_k256;
    let sum_bytes: [u8; 32] = sum_k256.to_bytes().into();
    assert_eq!(sum_bytes[31], 59, "k256: 42 + 17 = 59 (last byte)");
    // All other bytes should be 0 for small values
    for i in 0..31 {
        assert_eq!(sum_bytes[i], 0, "k256 sum byte {} should be 0", i);
    }

    // Multiplication: a * b = 714
    let prod_k256 = a_k256 * b_k256;
    let prod_bytes: [u8; 32] = prod_k256.to_bytes().into();
    // 714 = 0x02CA -> bytes[30] = 0x02, bytes[31] = 0xCA
    assert_eq!(prod_bytes[30], 0x02, "k256: 42*17 high byte");
    assert_eq!(prod_bytes[31], 0xCA, "k256: 42*17 low byte");

    // Same in our toy field
    let sum_toy = qadd(42, 17);
    assert_eq!(sum_toy, 59, "toy: 42 + 17 = 59");
    let prod_toy = qmul(42, 17);
    assert_eq!(prod_toy, 714, "toy: 42 * 17 = 714");

    // Both fields agree for small values (below both moduli)
    assert_eq!(sum_toy, sum_bytes[31] as u64);
    assert_eq!(prod_toy, (prod_bytes[30] as u64) * 256 + prod_bytes[31] as u64);
}

/// Verify that the secp256k1 generator point bytes from k256 match
/// the SEC 1 standard (uncompressed form starts with 0x04, compressed
/// with 0x02 or 0x03).
#[test]
fn test_cross_schnorr_generator() {
    use k256::AffinePoint;
    use k256::elliptic_curve::sec1::ToEncodedPoint;

    // The secp256k1 generator G (SEC 2, Section 2.7.1)
    let g = AffinePoint::GENERATOR;
    let encoded = g.to_encoded_point(false); // uncompressed

    // Uncompressed point starts with 0x04
    assert_eq!(encoded.as_bytes()[0], 0x04, "uncompressed prefix");

    // Total length: 1 + 32 + 32 = 65 bytes
    assert_eq!(encoded.len(), 65, "uncompressed secp256k1 point = 65 bytes");

    // Generator x-coordinate first byte (from SEC 2):
    // G_x = 0x79BE667E...
    assert_eq!(encoded.as_bytes()[1], 0x79, "G_x first byte = 0x79");

    // Compressed form
    let compressed = g.to_encoded_point(true);
    // Compressed point: 1 + 32 = 33 bytes
    assert_eq!(compressed.len(), 33, "compressed secp256k1 point = 33 bytes");
    // Prefix is 0x02 (even y) or 0x03 (odd y)
    assert!(
        compressed.as_bytes()[0] == 0x02 || compressed.as_bytes()[0] == 0x03,
        "compressed prefix must be 0x02 or 0x03"
    );

    // Our toy crypto uses 32-byte points (matching Ed25519/Schnorr convention)
    assert_eq!(
        core::mem::size_of::<SchnorrPoint>(), 32,
        "our SchnorrPoint = 32 bytes (Ed25519 convention)"
    );
}

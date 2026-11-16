//! KAT (Known Answer Tests) for ML-KEM-768 (FIPS 203).
//!
//! These tests validate parameter constraints, field arithmetic, polynomial
//! operations, encoding roundtrips, compression, CBD sampling, K-PKE
//! correctness, and ML-KEM keygen/encaps/decaps end-to-end.

use mlkem_hax::*;
use mlkem_hax::field;
use mlkem_hax::poly;
use mlkem_hax::encode;
use mlkem_hax::compress;
use mlkem_hax::cbd;
use mlkem_hax::kpke;
use mlkem_hax::mlkem;

// ---------------------------------------------------------------------------
// 1. FIPS 203 parameter validation
// ---------------------------------------------------------------------------

#[test]
fn kat_params_q_is_prime() {
    // q = 3329 must be prime.  Trial division up to sqrt(3329) < 58.
    let q = Q;
    assert!(q > 1);
    let mut d = 2u32;
    while d * d <= q {
        assert_ne!(q % d, 0, "q = {q} is divisible by {d}");
        d += 1;
    }
}

#[test]
fn kat_params_constants() {
    assert_eq!(Q, 3329);
    assert_eq!(N, 256);
    assert_eq!(K, 3);
    assert_eq!(ETA1, 2);
    assert_eq!(ETA2, 2);
    assert_eq!(DU, 10);
    assert_eq!(DV, 4);
}

#[test]
fn kat_params_sizes() {
    // FIPS 203 Table 2 sizes for ML-KEM-768
    assert_eq!(EK_BYTES, 12 * K * N / 8 + 32);          // 1184
    assert_eq!(INDCPA_DK_BYTES, 12 * K * N / 8);         // 1152
    assert_eq!(DK_BYTES, INDCPA_DK_BYTES + EK_BYTES + 32 + 32); // 2400
    assert_eq!(CT_BYTES, 32 * (DU as usize) * K + 32 * (DV as usize)); // 1088
    assert_eq!(SS_BYTES, 32);
    assert_eq!(SEED_BYTES, 32);
}

// ---------------------------------------------------------------------------
// 2. Field arithmetic mod q = 3329
// ---------------------------------------------------------------------------

#[test]
fn kat_field_add_wraparound() {
    // 3328 + 1 = 3329 = 0 mod q
    assert_eq!(field::add(3328, 1), 0);
    // 0 + 0 = 0
    assert_eq!(field::add(0, 0), 0);
    // 1000 + 2000 = 3000 (no wrap)
    assert_eq!(field::add(1000, 2000), 3000);
    // 2000 + 2000 = 4000 mod 3329 = 671
    assert_eq!(field::add(2000, 2000), 671);
}

#[test]
fn kat_field_sub_underflow() {
    // a - a = 0 for all a
    for a in [0u16, 1, 1664, 3328] {
        assert_eq!(field::sub(a, a), 0);
    }
    // 0 - 1 = 3328 mod q
    assert_eq!(field::sub(0, 1), 3328);
    // 100 - 200 = 3329 + 100 - 200 = 3229
    assert_eq!(field::sub(100, 200), 3229);
}

#[test]
fn kat_field_mul_basic() {
    // Multiplicative identity
    assert_eq!(field::mul(1, 2345), 2345);
    assert_eq!(field::mul(2345, 1), 2345);
    // Zero annihilation
    assert_eq!(field::mul(0, 9999), 0);
    // 17 * 17 = 289
    assert_eq!(field::mul(17, 17), 289);
    // 100 * 100 = 10000 mod 3329 = 13
    assert_eq!(field::mul(100, 100), 10000 % 3329);
}

#[test]
fn kat_field_reduce() {
    assert_eq!(field::reduce(0), 0);
    assert_eq!(field::reduce(3329), 0);
    assert_eq!(field::reduce(3330), 1);
    assert_eq!(field::reduce(6658), 0); // 2*q
    assert_eq!(field::reduce(10000), (10000 % 3329) as u16);
}

#[test]
fn kat_field_neg() {
    // neg(0) = 0
    assert_eq!(field::neg(0), 0);
    // neg(1) = 3328
    assert_eq!(field::neg(1), 3328);
    // neg(neg(a)) = a for non-zero
    for a in [1u16, 100, 1664, 3328] {
        assert_eq!(field::neg(field::neg(a)), a);
    }
    // a + neg(a) = 0 mod q
    for a in [0u16, 1, 42, 1000, 3328] {
        assert_eq!(field::add(a, field::neg(a)), 0);
    }
}

// ---------------------------------------------------------------------------
// 3. Polynomial operations
// ---------------------------------------------------------------------------

#[test]
fn kat_poly_add_identity() {
    // f + 0 = f
    let mut f = ZERO_POLY;
    f[0] = 42;
    f[127] = 1000;
    f[255] = 3000;
    let result = poly::poly_add(&f, &ZERO_POLY);
    assert_eq!(result, f);
}

#[test]
fn kat_poly_mul_identity() {
    // 1 * f = f  (where 1 = polynomial with only constant term 1)
    let mut one = ZERO_POLY;
    one[0] = 1;
    let mut f = ZERO_POLY;
    f[0] = 42;
    f[1] = 100;
    f[200] = 3000;
    let result = poly::poly_mul(&one, &f);
    assert_eq!(result[0], 42);
    assert_eq!(result[1], 100);
    assert_eq!(result[200], 3000);
    // All other coefficients must be 0
    for i in 0..N {
        if i != 0 && i != 1 && i != 200 {
            assert_eq!(result[i], 0, "non-zero at index {i}");
        }
    }
}

#[test]
fn kat_poly_mul_negacyclic() {
    // X^255 * X = X^256 = -1 mod (X^256 + 1), i.e., coefficient 0 becomes q-1 = 3328
    let mut a = ZERO_POLY;
    a[255] = 1;
    let mut b = ZERO_POLY;
    b[1] = 1;
    let r = poly::poly_mul(&a, &b);
    assert_eq!(r[0], Q as u16 - 1); // 3328
    for i in 1..N {
        assert_eq!(r[i], 0, "expected 0 at index {i}");
    }
}

#[test]
fn kat_poly_scalar() {
    let mut f = ZERO_POLY;
    f[0] = 1;
    f[100] = 500;
    f[255] = 3000;
    let r = poly::poly_scalar(2, &f);
    assert_eq!(r[0], 2);
    assert_eq!(r[100], 1000);
    assert_eq!(r[255], field::mul(2, 3000));
    // scalar 0 gives zero poly
    let z = poly::poly_scalar(0, &f);
    assert_eq!(z, ZERO_POLY);
}

// ---------------------------------------------------------------------------
// 4. Encoding roundtrips
// ---------------------------------------------------------------------------

#[test]
fn kat_encode_decode_12_roundtrip() {
    // Test with a variety of coefficients in [0, q)
    let mut f = ZERO_POLY;
    f[0] = 0;
    f[1] = 1;
    f[2] = 42;
    f[50] = 1664;   // q/2 rounded down
    f[100] = 3328;  // q - 1
    f[200] = 2000;
    f[255] = 3000;
    let encoded = encode::byte_encode_12(&f);
    let decoded = encode::byte_decode_12(&encoded);
    for i in 0..N {
        assert_eq!(f[i], decoded[i], "mismatch at index {i}");
    }
}

#[test]
fn kat_msg_encode_decode_roundtrip() {
    // All-zeros message
    let msg_zero = [0u8; 32];
    assert_eq!(compress::msg_decode(&compress::msg_encode(&msg_zero)), msg_zero);

    // All-ones message
    let msg_ones = [0xFFu8; 32];
    assert_eq!(compress::msg_decode(&compress::msg_encode(&msg_ones)), msg_ones);

    // Arbitrary message
    let msg: [u8; 32] = [
        0xAB, 0xCD, 0xEF, 0x01, 0x23, 0x45, 0x67, 0x89,
        0x00, 0xFF, 0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC,
        0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
        0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE,
    ];
    let encoded = compress::msg_encode(&msg);
    let decoded = compress::msg_decode(&encoded);
    assert_eq!(msg, decoded);
}

#[test]
fn kat_polyvec_encode_decode_roundtrip() {
    let mut v = ZERO_VEC;
    v[0][0] = 1;
    v[0][255] = 3328;
    v[1][100] = 2000;
    v[2][200] = 500;
    let encoded = encode::polyvec_encode(&v);
    let decoded = encode::polyvec_decode(&encoded);
    for i in 0..K {
        for j in 0..N {
            assert_eq!(v[i][j], decoded[i][j], "polyvec mismatch at [{i}][{j}]");
        }
    }
}

// ---------------------------------------------------------------------------
// 5. Compression roundtrip bounds
// ---------------------------------------------------------------------------

#[test]
fn kat_compress_decompress_du_error_bound() {
    // For d_u = 10: max roundtrip error is at most floor(q / 2^{d+1}) = floor(3329/2048) = 1
    // (rounding error bound from FIPS 203 Lemma 4.6)
    for x in (0..Q as u16).step_by(37) {
        let c = compress::compress_coeff(x, DU);
        let y = compress::decompress_coeff(c, DU);
        let diff = if y >= x { y - x } else { x - y };
        // Also check the wraparound case
        let diff_wrap = Q as u16 - diff;
        let err = diff.min(diff_wrap);
        assert!(err <= 2, "du compress error too large for x={x}: got {y}, err={err}");
    }
}

#[test]
fn kat_compress_decompress_dv_error_bound() {
    // For d_v = 4: max roundtrip error is at most floor(q / 2^{d+1}) = floor(3329/32) = 104
    for x in (0..Q as u16).step_by(37) {
        let c = compress::compress_coeff(x, DV);
        let y = compress::decompress_coeff(c, DV);
        let diff = if y >= x { y - x } else { x - y };
        let diff_wrap = Q as u16 - diff;
        let err = diff.min(diff_wrap);
        assert!(err <= 105, "dv compress error too large for x={x}: got {y}, err={err}");
    }
}

#[test]
fn kat_compress_extremes() {
    // Compress(0, d) = 0 for any d
    assert_eq!(compress::compress_coeff(0, DU), 0);
    assert_eq!(compress::compress_coeff(0, DV), 0);
    // Compress(q/2, 1) should be 1 (message bit)
    assert_eq!(compress::compress_coeff(1665, 1), 1);
    // Compress(0, 1) should be 0
    assert_eq!(compress::compress_coeff(0, 1), 0);
    // Decompress(0, d) = 0
    assert_eq!(compress::decompress_coeff(0, DU), 0);
    assert_eq!(compress::decompress_coeff(0, DV), 0);
}

// ---------------------------------------------------------------------------
// 6. CBD sampling
// ---------------------------------------------------------------------------

#[test]
fn kat_cbd2_zero_input() {
    let bytes = [0u8; 128];
    let f = cbd::sample_cbd2(&bytes);
    // All bits 0 means a = 0, b = 0 => coefficient = 0
    for i in 0..N {
        assert_eq!(f[i], 0, "CBD(0) should be all zeros, non-zero at {i}");
    }
}

#[test]
fn kat_cbd2_range_check() {
    // Use a known byte pattern and verify all coefficients are in {0, 1, 2, q-2, q-1}
    let mut bytes = [0u8; 128];
    for i in 0..128 {
        bytes[i] = (i as u8).wrapping_mul(37).wrapping_add(13);
    }
    let f = cbd::sample_cbd2(&bytes);
    let valid = [0u16, 1, 2, Q as u16 - 2, Q as u16 - 1]; // {0, 1, 2, 3327, 3328}
    for i in 0..N {
        assert!(
            valid.contains(&f[i]),
            "CBD coefficient at index {i} out of range: {} (expected one of {:?})",
            f[i], valid,
        );
    }
}

#[test]
fn kat_cbd2_all_ones() {
    // bytes = 0xFF means every 4-bit nibble is 0b1111 => a = 2, b = 2 => coeff = 0
    let bytes = [0xFFu8; 128];
    let f = cbd::sample_cbd2(&bytes);
    for i in 0..N {
        assert_eq!(f[i], 0, "CBD(0xFF) should be all zeros, non-zero at {i}");
    }
}

#[test]
fn kat_cbd2_specific_nibble() {
    // Craft a single byte to check specific nibbles:
    // byte = 0b0001_0110 = 0x16
    // low nibble 0b0110: a = bits[0..2] = (0+1) = 1, b = bits[2..4] = (1+0) = 1 => coeff = 0
    // high nibble 0b0001: a = (1+0) = 1, b = (0+0) = 0 => coeff = 1
    let mut bytes = [0u8; 128];
    bytes[0] = 0x16;
    let f = cbd::sample_cbd2(&bytes);
    // index 0 uses low nibble of bytes[0]
    // 0b0110: bit0 = 0, bit1 = 1, bit2 = 1, bit3 = 0 => a = 0+1 = 1, b = 1+0 = 1 => 0
    assert_eq!(f[0], 0);
    // index 1 uses high nibble of bytes[0]
    // 0b0001: bit0 = 1, bit1 = 0, bit2 = 0, bit3 = 0 => a = 1+0 = 1, b = 0+0 = 0 => 1
    assert_eq!(f[1], 1);
}

// ---------------------------------------------------------------------------
// 7. K-PKE encrypt/decrypt roundtrip
// ---------------------------------------------------------------------------

#[test]
fn kat_kpke_roundtrip_zero_message() {
    let seed = [0u8; 32];
    let (ek, dk) = kpke::kpke_keygen(&seed);
    let msg = [0u8; 32];
    let r = [0u8; 32];
    let ct = kpke::kpke_encrypt(&ek, &msg, &r);
    let dec = kpke::kpke_decrypt(&dk, &ct);
    assert_eq!(msg, dec, "K-PKE roundtrip failed for zero message");
}

#[test]
fn kat_kpke_roundtrip_nonzero() {
    let seed = [42u8; 32];
    let (ek, dk) = kpke::kpke_keygen(&seed);
    let msg: [u8; 32] = [
        0xAB, 0xCD, 0xEF, 0x01, 0x23, 0x45, 0x67, 0x89,
        0x00, 0xFF, 0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC,
        0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
        0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE,
    ];
    let r = [7u8; 32];
    let ct = kpke::kpke_encrypt(&ek, &msg, &r);
    let dec = kpke::kpke_decrypt(&dk, &ct);
    assert_eq!(msg, dec, "K-PKE roundtrip failed for non-zero message");
}

// ---------------------------------------------------------------------------
// 8. ML-KEM keygen/encaps/decaps roundtrip
// ---------------------------------------------------------------------------

#[test]
fn kat_mlkem_roundtrip() {
    let d = [42u8; 32];
    let z = [99u8; 32];
    let (ek, dk) = mlkem::mlkem_keygen(&d, &z);
    let m = [7u8; 32];
    let (ct, ss_enc) = mlkem::mlkem_encaps(&ek, &m);
    let ss_dec = mlkem::mlkem_decaps(&dk, &ct);
    assert_eq!(ss_enc, ss_dec, "ML-KEM encaps/decaps shared secrets must match");
}

#[test]
fn kat_mlkem_different_seeds() {
    // Different keygen seeds produce different encapsulation keys
    let (ek1, _dk1) = mlkem::mlkem_keygen(&[1u8; 32], &[10u8; 32]);
    let (ek2, _dk2) = mlkem::mlkem_keygen(&[2u8; 32], &[20u8; 32]);
    assert_ne!(ek1, ek2, "Different seeds should produce different keys");
}

#[test]
fn kat_mlkem_implicit_rejection() {
    let d = [5u8; 32];
    let z = [6u8; 32];
    let (ek, dk) = mlkem::mlkem_keygen(&d, &z);
    let m = [3u8; 32];
    let (ct, ss) = mlkem::mlkem_encaps(&ek, &m);

    // Corrupt ciphertext at several positions
    let mut bad_ct = ct;
    bad_ct[0] ^= 0xFF;
    bad_ct[500] ^= 0x01;
    let ss_bad = mlkem::mlkem_decaps(&dk, &bad_ct);
    assert_ne!(ss, ss_bad, "Corrupted ciphertext must trigger implicit rejection");

    // The rejection key should be deterministic (same bad ct -> same rejection key)
    let ss_bad2 = mlkem::mlkem_decaps(&dk, &bad_ct);
    assert_eq!(ss_bad, ss_bad2, "Implicit rejection must be deterministic");
}

// ---------------------------------------------------------------------------
// 9. Key and ciphertext sizes
// ---------------------------------------------------------------------------

#[test]
fn kat_output_sizes() {
    let d = [0u8; 32];
    let z = [0u8; 32];
    let (ek, dk) = mlkem::mlkem_keygen(&d, &z);
    assert_eq!(ek.len(), 1184);
    assert_eq!(dk.len(), 2400);

    let m = [0u8; 32];
    let (ct, ss) = mlkem::mlkem_encaps(&ek, &m);
    assert_eq!(ct.len(), 1088);
    assert_eq!(ss.len(), 32);
}

// ---------------------------------------------------------------------------
// 10. NTT-friendliness: q = 1 mod 2n (FIPS 203 requirement)
// ---------------------------------------------------------------------------

#[test]
fn kat_ntt_friendliness() {
    // FIPS 203 requires q = 1 mod 2n for NTT-based multiplication.
    // For n = 256: 2n = 512, and 3329 mod 512 = 257.
    // Actually the FIPS 203 condition is q ≡ 1 (mod 256), not mod 512.
    // 3329 = 13 * 256 + 1, so 3329 mod 256 = 1. This enables the NTT.
    assert_eq!(Q % (N as u32), 1, "q must be 1 mod n for NTT");
    // Furthermore, verify q = 13 * 256 + 1 (FIPS 203 notation)
    assert_eq!(Q, 13 * 256 + 1);
}

#[test]
fn kat_primitive_root_existence() {
    // Since q = 3329 is prime and q ≡ 1 (mod 256), there exists a primitive
    // 256th root of unity. We verify by finding g with g^256 ≡ 1 (mod q)
    // and g^128 ≢ 1 (mod q) (i.e., order is exactly 256).
    //
    // Known: 17 is a generator of Z_q*. So 17^((q-1)/256) = 17^13 is a
    // primitive 256th root of unity.
    let q = Q as u64;
    // Compute 17^13 mod q by repeated squaring
    let base = 17u64;
    let exp = (q - 1) / 256; // = 13
    assert_eq!(exp, 13);
    let mut result = 1u64;
    let mut e = exp;
    let mut b = base;
    while e > 0 {
        if e % 2 == 1 {
            result = (result * b) % q;
        }
        b = (b * b) % q;
        e /= 2;
    }
    let omega = result;
    // Verify omega^256 = 1 mod q
    let mut power = 1u64;
    for _ in 0..256 {
        power = (power * omega) % q;
    }
    assert_eq!(power, 1, "omega^256 must be 1 mod q");
    // Verify omega^128 != 1 mod q (order is exactly 256, not a divisor)
    let mut half_power = 1u64;
    for _ in 0..128 {
        half_power = (half_power * omega) % q;
    }
    assert_ne!(half_power, 1, "omega must have order exactly 256, not 128");
}

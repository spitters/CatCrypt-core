//! Compression/decompression for ML-KEM (FIPS 203 §4.2.3).
//!
//! Compress_d(x) = ⌈(2^d / q) · x⌋ mod 2^d
//! Decompress_d(y) = ⌈(q / 2^d) · y⌋
//!
//! For ML-KEM-768: d_u = 10, d_v = 4.

use crate::types::*;
use crate::field;

/// Compress a single coefficient to d bits.
/// Compress_d(x) = round((2^d * x) / q) mod 2^d.
pub fn compress_coeff(x: u16, d: u32) -> u16 {
    let two_d = 1u32 << d;
    let val = ((x as u32) * two_d + (Q / 2)) / Q;
    (val % two_d) as u16
}

/// Decompress a single d-bit value back to [0, q).
/// Decompress_d(y) = round((q * y) / 2^d).
pub fn decompress_coeff(y: u16, d: u32) -> u16 {
    let two_d = 1u32 << d;
    let val = ((y as u32) * Q + (two_d / 2)) / two_d;
    field::reduce(val)
}

/// Compress a polynomial with d_u = 10 bits.
pub fn poly_compress_du(f: &Poly) -> [u8; 320] {
    // 10 bits * 256 / 8 = 320 bytes
    let mut r = [0u8; 320];
    for i in 0..N / 4 {
        let c0 = compress_coeff(f[4 * i], DU) as u32;
        let c1 = compress_coeff(f[4 * i + 1], DU) as u32;
        let c2 = compress_coeff(f[4 * i + 2], DU) as u32;
        let c3 = compress_coeff(f[4 * i + 3], DU) as u32;
        // Pack four 10-bit values into 5 bytes
        r[5 * i] = (c0 & 0xFF) as u8;
        r[5 * i + 1] = ((c0 >> 8) | ((c1 & 0x3F) << 2)) as u8;
        r[5 * i + 2] = ((c1 >> 6) | ((c2 & 0xF) << 4)) as u8;
        r[5 * i + 3] = ((c2 >> 4) | ((c3 & 0x3) << 6)) as u8;
        r[5 * i + 4] = (c3 >> 2) as u8;
    }
    r
}

/// Decompress a polynomial from d_u = 10 bits.
pub fn poly_decompress_du(b: &[u8; 320]) -> Poly {
    let mut f = ZERO_POLY;
    for i in 0..N / 4 {
        let b0 = b[5 * i] as u32;
        let b1 = b[5 * i + 1] as u32;
        let b2 = b[5 * i + 2] as u32;
        let b3 = b[5 * i + 3] as u32;
        let b4 = b[5 * i + 4] as u32;
        f[4 * i] = decompress_coeff(((b0 | ((b1 & 0x3) << 8)) & 0x3FF) as u16, DU);
        f[4 * i + 1] = decompress_coeff((((b1 >> 2) | ((b2 & 0xF) << 6)) & 0x3FF) as u16, DU);
        f[4 * i + 2] = decompress_coeff((((b2 >> 4) | ((b3 & 0x3F) << 4)) & 0x3FF) as u16, DU);
        f[4 * i + 3] = decompress_coeff((((b3 >> 6) | (b4 << 2)) & 0x3FF) as u16, DU);
    }
    f
}

/// Compress a polynomial with d_v = 4 bits.
pub fn poly_compress_dv(f: &Poly) -> [u8; 128] {
    // 4 bits * 256 / 8 = 128 bytes
    let mut r = [0u8; 128];
    for i in 0..N / 2 {
        let c0 = compress_coeff(f[2 * i], DV);
        let c1 = compress_coeff(f[2 * i + 1], DV);
        r[i] = (c0 | (c1 << 4)) as u8;
    }
    r
}

/// Decompress a polynomial from d_v = 4 bits.
pub fn poly_decompress_dv(b: &[u8; 128]) -> Poly {
    let mut f = ZERO_POLY;
    for i in 0..N / 2 {
        f[2 * i] = decompress_coeff((b[i] & 0xF) as u16, DV);
        f[2 * i + 1] = decompress_coeff((b[i] >> 4) as u16, DV);
    }
    f
}

/// Compress a polynomial vector with d_u = 10.
/// Output: k * 320 = 960 bytes.
pub fn polyvec_compress(v: &PolyVec) -> [u8; 960] {
    let mut r = [0u8; 960];
    for i in 0..K {
        let compressed = poly_compress_du(&v[i]);
        for j in 0..320 {
            r[i * 320 + j] = compressed[j];
        }
    }
    r
}

/// Decompress a polynomial vector from d_u = 10.
pub fn polyvec_decompress(b: &[u8; 960]) -> PolyVec {
    let mut v = ZERO_VEC;
    for i in 0..K {
        let mut chunk = [0u8; 320];
        for j in 0..320 {
            chunk[j] = b[i * 320 + j];
        }
        v[i] = poly_decompress_du(&chunk);
    }
    v
}

/// Encode a single message bit per coefficient: 0 → 0, 1 → ⌈q/2⌉ = 1665.
/// FIPS 203 §4.2.1, d = 1.
pub fn msg_encode(msg: &[u8; SS_BYTES]) -> Poly {
    let mut f = ZERO_POLY;
    for i in 0..SS_BYTES {
        for bit in 0..8 {
            let b = (msg[i] >> bit) & 1;
            f[8 * i + bit] = if b == 1 { 1665 } else { 0 };
        }
    }
    f
}

/// Decode message from polynomial: coefficient closer to q/2 → 1, else 0.
pub fn msg_decode(f: &Poly) -> [u8; SS_BYTES] {
    let mut msg = [0u8; SS_BYTES];
    for i in 0..SS_BYTES {
        let mut byte_val = 0u8;
        for bit in 0..8 {
            let c = f[8 * i + bit];
            // compress_1: round(2*c/q) mod 2
            let compressed = compress_coeff(c, 1);
            byte_val |= (compressed as u8) << bit;
        }
        msg[i] = byte_val;
    }
    msg
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compress_decompress_du() {
        let c = compress_coeff(1665, DU); // q/2 → should be 2^10/2 = 512
        let d = decompress_coeff(c, DU);
        // Should be close to 1665
        let diff = if d > 1665 { d - 1665 } else { 1665 - d };
        assert!(diff <= 2, "compress/decompress error too large: {diff}");
    }

    #[test]
    fn test_compress_decompress_dv() {
        let c = compress_coeff(1665, DV); // q/2 → 2^4/2 = 8
        assert_eq!(c, 8);
        let d = decompress_coeff(c, DV);
        let diff = if d > 1665 { d - 1665 } else { 1665 - d };
        assert!(diff <= (Q as u16) / 16, "compress/decompress_dv error too large");
    }

    #[test]
    fn test_msg_roundtrip() {
        let msg = [0xAB, 0xCD, 0xEF, 0x01, 0x23, 0x45, 0x67, 0x89,
                   0x00, 0xFF, 0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC,
                   0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
                   0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE];
        let encoded = msg_encode(&msg);
        let decoded = msg_decode(&encoded);
        assert_eq!(msg, decoded);
    }
}

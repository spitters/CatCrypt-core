//! Byte encoding/decoding for polynomials (FIPS 203 §4.2.1).
//!
//! ByteEncode_d: Poly → [u8; 32*d] encodes each coefficient in d bits.
//! ByteDecode_d: [u8; 32*d] → Poly decodes d-bit coefficients.
//!
//! For ML-KEM-768: d=12 for uncompressed, d=10/d=4 for compressed.

use crate::types::*;

/// Encode a polynomial with 12 bits per coefficient.
/// Output: 12 * 256 / 8 = 384 bytes.
pub fn byte_encode_12(f: &Poly) -> [u8; 384] {
    let mut r = [0u8; 384];
    for i in 0..N / 2 {
        let a = f[2 * i] as u32;
        let b = f[2 * i + 1] as u32;
        // Pack two 12-bit values into 3 bytes (little-endian)
        r[3 * i] = (a & 0xFF) as u8;
        r[3 * i + 1] = ((a >> 8) | ((b & 0xF) << 4)) as u8;
        r[3 * i + 2] = ((b >> 4) & 0xFF) as u8;
    }
    r
}

/// Decode a polynomial from 12 bits per coefficient.
pub fn byte_decode_12(b: &[u8; 384]) -> Poly {
    let mut f = ZERO_POLY;
    for i in 0..N / 2 {
        let b0 = b[3 * i] as u32;
        let b1 = b[3 * i + 1] as u32;
        let b2 = b[3 * i + 2] as u32;
        f[2 * i] = ((b0 | ((b1 & 0xF) << 8)) % Q) as u16;
        f[2 * i + 1] = (((b1 >> 4) | (b2 << 4)) % Q) as u16;
    }
    f
}

/// Encode a polynomial vector (k polynomials, 12 bits each).
/// Output: k * 384 = 1152 bytes.
pub fn polyvec_encode(v: &PolyVec) -> [u8; 1152] {
    let mut r = [0u8; 1152];
    for i in 0..K {
        let encoded = byte_encode_12(&v[i]);
        for j in 0..384 {
            r[i * 384 + j] = encoded[j];
        }
    }
    r
}

/// Decode a polynomial vector from bytes.
pub fn polyvec_decode(b: &[u8; 1152]) -> PolyVec {
    let mut v = ZERO_VEC;
    for i in 0..K {
        let mut chunk = [0u8; 384];
        for j in 0..384 {
            chunk[j] = b[i * 384 + j];
        }
        v[i] = byte_decode_12(&chunk);
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode_12_roundtrip() {
        let mut f = ZERO_POLY;
        f[0] = 42;
        f[1] = 3328;
        f[100] = 1000;
        f[255] = 2500;
        let encoded = byte_encode_12(&f);
        let decoded = byte_decode_12(&encoded);
        assert_eq!(decoded[0], 42);
        assert_eq!(decoded[1], 3328);
        assert_eq!(decoded[100], 1000);
        assert_eq!(decoded[255], 2500);
    }

    #[test]
    fn test_polyvec_encode_decode_roundtrip() {
        let mut v = ZERO_VEC;
        v[0][0] = 1;
        v[1][100] = 2000;
        v[2][255] = 3000;
        let encoded = polyvec_encode(&v);
        let decoded = polyvec_decode(&encoded);
        assert_eq!(decoded[0][0], 1);
        assert_eq!(decoded[1][100], 2000);
        assert_eq!(decoded[2][255], 3000);
    }
}

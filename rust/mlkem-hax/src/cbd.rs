//! Centered Binomial Distribution sampling (FIPS 203 §4.2.2, Algorithm 7).
//!
//! SamplePolyCBD_η(B): sample polynomial with coefficients from CBD(η).
//! For ML-KEM-768: η₁ = η₂ = 2, so each coefficient uses 4 bits of randomness.
//!
//! CBD(2): count 1-bits in two pairs of bits, take difference.

use crate::types::*;
use crate::field;

/// Sample a polynomial from CBD(η = 2).
/// Input: 64 * η = 128 bytes of randomness.
/// Output: polynomial with coefficients in {-2, -1, 0, 1, 2} mod q.
pub fn sample_cbd2(bytes: &[u8; 128]) -> Poly {
    let mut f = ZERO_POLY;
    for i in 0..N {
        // Each coefficient uses 4 bits: 2 for a, 2 for b
        let byte_idx = i / 2;
        let bit_offset = (i % 2) * 4;
        let bits = (bytes[byte_idx] >> bit_offset) & 0xF;
        let a = ((bits >> 0) & 1) + ((bits >> 1) & 1);
        let b = ((bits >> 2) & 1) + ((bits >> 3) & 1);
        // coefficient = a - b mod q
        f[i] = field::sub(a as u16, b as u16);
    }
    f
}

/// Sample a polynomial vector from CBD(η).
/// Each polynomial needs 128 bytes (η=2), total: k * 128 = 384 bytes.
pub fn sample_cbd_vec(bytes: &[u8], eta_bytes: usize) -> PolyVec {
    let mut v = ZERO_VEC;
    for i in 0..K {
        let offset = i * eta_bytes;
        let mut chunk = [0u8; 128];
        for j in 0..eta_bytes.min(128) {
            if offset + j < bytes.len() {
                chunk[j] = bytes[offset + j];
            }
        }
        v[i] = sample_cbd2(&chunk);
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cbd2_zero_input() {
        let bytes = [0u8; 128];
        let f = sample_cbd2(&bytes);
        // All bits 0: a=0, b=0 → coeff = 0
        for i in 0..N {
            assert_eq!(f[i], 0);
        }
    }

    #[test]
    fn test_cbd2_range() {
        // Random-ish input
        let mut bytes = [0u8; 128];
        for i in 0..128 {
            bytes[i] = (i * 37 + 13) as u8;
        }
        let f = sample_cbd2(&bytes);
        // All coefficients should be in {0, 1, 2, q-1, q-2} mod q
        for j in 0..N {
            let c = f[j];
            assert!(c <= 2 || c >= Q as u16 - 2,
                    "CBD coefficient out of range: {c}");
        }
    }
}

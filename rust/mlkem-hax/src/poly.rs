//! Polynomial arithmetic mod (X^256 + 1) over Z_q (FIPS 203 §4.3).
//!
//! Uses schoolbook multiplication (O(n²)). This is a spec implementation;
//! production code uses NTT for O(n log n) performance.
//!
//! Maps to CatCrypt's `Rq = AdjoinRoot (X^256 + 1)` ring operations.

use crate::types::*;
use crate::field;

/// Polynomial addition: coefficient-wise mod q.
pub fn poly_add(a: &Poly, b: &Poly) -> Poly {
    let mut r = ZERO_POLY;
    for i in 0..N {
        r[i] = field::add(a[i], b[i]);
    }
    r
}

/// Polynomial subtraction: coefficient-wise mod q.
pub fn poly_sub(a: &Poly, b: &Poly) -> Poly {
    let mut r = ZERO_POLY;
    for i in 0..N {
        r[i] = field::sub(a[i], b[i]);
    }
    r
}

/// Polynomial multiplication mod (X^256 + 1) using schoolbook.
///
/// Negacyclic convolution: for degree ≥ 256, subtract (since X^256 = -1).
pub fn poly_mul(a: &Poly, b: &Poly) -> Poly {
    let mut r = [0u32; N];
    for i in 0..N {
        for j in 0..N {
            let prod = a[i] as u32 * b[j] as u32;
            let idx = i + j;
            if idx < N {
                r[idx] = (r[idx] + prod) % Q;
            } else {
                // X^(idx) = -X^(idx-256) in X^256+1
                let wrap = idx - N;
                r[wrap] = (r[wrap] + Q - (prod % Q)) % Q;
            }
        }
    }
    let mut out = ZERO_POLY;
    for k in 0..N {
        out[k] = r[k] as u16;
    }
    out
}

/// Scalar multiplication: c * f.
pub fn poly_scalar(c: u16, f: &Poly) -> Poly {
    let mut r = ZERO_POLY;
    for i in 0..N {
        r[i] = field::mul(c, f[i]);
    }
    r
}

/// Inner product of two polynomial vectors: Σ a[i] * b[i].
pub fn polyvec_dot(a: &PolyVec, b: &PolyVec) -> Poly {
    let mut acc = ZERO_POLY;
    for i in 0..K {
        let prod = poly_mul(&a[i], &b[i]);
        acc = poly_add(&acc, &prod);
    }
    acc
}

/// Matrix-vector multiplication: A * s (each row dot with s).
pub fn mat_vec_mul(a: &PolyMat, s: &PolyVec) -> PolyVec {
    let mut r = ZERO_VEC;
    for i in 0..K {
        r[i] = polyvec_dot(&a[i], s);
    }
    r
}

/// Transpose a k×k matrix.
pub fn mat_transpose(a: &PolyMat) -> PolyMat {
    let mut r = [ZERO_VEC; K];
    for i in 0..K {
        for j in 0..K {
            r[i][j] = a[j][i];
        }
    }
    r
}

/// Vector addition: component-wise polynomial add.
pub fn polyvec_add(a: &PolyVec, b: &PolyVec) -> PolyVec {
    let mut r = ZERO_VEC;
    for i in 0..K {
        r[i] = poly_add(&a[i], &b[i]);
    }
    r
}

/// Vector subtraction: component-wise polynomial sub.
pub fn polyvec_sub(a: &PolyVec, b: &PolyVec) -> PolyVec {
    let mut r = ZERO_VEC;
    for i in 0..K {
        r[i] = poly_sub(&a[i], &b[i]);
    }
    r
}

// ---------------------------------------------------------------------------
// Number-Theoretic Transform (FIPS 203 §4.3, Algorithms 9–11).
//
// Plain integer arithmetic in Z_q (no Montgomery form): the standard
// representatives produced here are exactly what FIPS-203 encodes, so the
// stored t̂/ŝ and the compressed (u, v) are byte-identical to the NIST KAT.
// ζ = 17 is the primitive 256-th root of unity.
// ---------------------------------------------------------------------------

/// Reverse the low 7 bits of `x` (BitRev7).
fn bitrev7(x: usize) -> usize {
    let mut r = 0usize;
    for b in 0..7usize {
        r |= ((x >> b) & 1) << (6 - b);
    }
    r
}

/// `base^exp mod q` by repeated squaring.
fn pow_mod(base: u32, exp: u32) -> u32 {
    let mut result = 1u32;
    let mut b = base % Q;
    let mut e = exp;
    while e > 0 {
        if e & 1 == 1 {
            result = (result * b) % Q;
        }
        b = (b * b) % Q;
        e >>= 1;
    }
    result
}

/// ζ^{BitRev7(k)} mod q — the NTT twiddle factor for butterfly group `k`.
fn zeta(k: usize) -> u32 {
    pow_mod(17, bitrev7(k) as u32)
}

/// Forward NTT (Algorithm 9): standard order → bit-reversed NTT domain.
pub fn ntt(f: &Poly) -> Poly {
    let mut r = *f;
    let mut k = 1usize;
    let mut len = 128usize;
    while len >= 2 {
        let mut start = 0usize;
        while start < N {
            let z = zeta(k);
            k += 1;
            for j in start..start + len {
                let t = (z * (r[j + len] as u32)) % Q;
                r[j + len] = ((r[j] as u32 + Q - t) % Q) as u16;
                r[j] = ((r[j] as u32 + t) % Q) as u16;
            }
            start += 2 * len;
        }
        len >>= 1;
    }
    r
}

/// Inverse NTT (Algorithm 10): bit-reversed NTT domain → standard order.
pub fn inv_ntt(f: &Poly) -> Poly {
    let mut r = *f;
    let mut k = 127usize;
    let mut len = 2usize;
    while len <= 128 {
        let mut start = 0usize;
        while start < N {
            let z = zeta(k);
            k = k.wrapping_sub(1);
            for j in start..start + len {
                let t = r[j];
                r[j] = ((t as u32 + r[j + len] as u32) % Q) as u16;
                let diff = (r[j + len] as u32 + Q - t as u32) % Q;
                r[j + len] = ((z * diff) % Q) as u16;
            }
            start += 2 * len;
        }
        len <<= 1;
    }
    // Multiply by 128^{-1} mod q = 3303.
    let ninv = 3303u32;
    for i in 0..N {
        r[i] = ((ninv * r[i] as u32) % Q) as u16;
    }
    r
}

/// Base-case multiply of two degree-1 polys mod (X² − γ) (Algorithm 12).
fn basemul(a0: u32, a1: u32, b0: u32, b1: u32, gamma: u32) -> (u16, u16) {
    let c0 = (a0 * b0 + ((a1 * b1) % Q) * gamma) % Q;
    let c1 = (a0 * b1 + a1 * b0) % Q;
    (c0 as u16, c1 as u16)
}

/// Multiply two polynomials in the NTT domain (Algorithm 11): pointwise product
/// of 128 degree-1 blocks with twiddle γ_i = ζ^{2·BitRev7(i)+1}.
pub fn ntt_mul(a: &Poly, b: &Poly) -> Poly {
    let mut r = ZERO_POLY;
    for i in 0..128 {
        let gamma = pow_mod(17, (2 * bitrev7(i) + 1) as u32);
        let (c0, c1) = basemul(
            a[2 * i] as u32,
            a[2 * i + 1] as u32,
            b[2 * i] as u32,
            b[2 * i + 1] as u32,
            gamma,
        );
        r[2 * i] = c0;
        r[2 * i + 1] = c1;
    }
    r
}

/// NTT-domain vector inner product: Σ_i ntt_mul(a[i], b[i]).
pub fn ntt_dot(a: &PolyVec, b: &PolyVec) -> Poly {
    let mut acc = ZERO_POLY;
    for i in 0..K {
        acc = poly_add(&acc, &ntt_mul(&a[i], &b[i]));
    }
    acc
}

/// NTT-domain matrix-vector product: r[i] = Σ_j ntt_mul(a[i][j], s[j]).
pub fn ntt_mat_vec(a: &PolyMat, s: &PolyVec) -> PolyVec {
    let mut r = ZERO_VEC;
    for i in 0..K {
        r[i] = ntt_dot(&a[i], s);
    }
    r
}

/// Apply the forward NTT to every component of a vector.
pub fn polyvec_ntt(v: &PolyVec) -> PolyVec {
    let mut r = ZERO_VEC;
    for i in 0..K {
        r[i] = ntt(&v[i]);
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poly_add_zero() {
        let a = ZERO_POLY;
        let b = ZERO_POLY;
        assert_eq!(poly_add(&a, &b), ZERO_POLY);
    }

    #[test]
    fn test_poly_mul_one() {
        // 1 * f = f
        let mut one = ZERO_POLY;
        one[0] = 1;
        let mut f = ZERO_POLY;
        f[0] = 42;
        f[1] = 100;
        let r = poly_mul(&one, &f);
        assert_eq!(r[0], 42);
        assert_eq!(r[1], 100);
    }

    #[test]
    fn test_poly_mul_negacyclic() {
        // X^255 * X = X^256 = -1 mod (X^256+1)
        let mut a = ZERO_POLY;
        a[255] = 1;
        let mut b = ZERO_POLY;
        b[1] = 1;
        let r = poly_mul(&a, &b);
        // X^256 wraps to -1 at index 0
        assert_eq!(r[0], Q as u16 - 1); // -1 mod q = 3328
    }

    #[test]
    fn test_ntt_roundtrip() {
        // inv_ntt(ntt(f)) == f
        let mut f = ZERO_POLY;
        for i in 0..N {
            f[i] = ((i * 7 + 3) as u32 % Q) as u16;
        }
        let back = inv_ntt(&ntt(&f));
        assert_eq!(back, f, "NTT roundtrip failed");
    }

    #[test]
    fn test_ntt_mul_matches_schoolbook() {
        // inv_ntt(ntt_mul(ntt(a), ntt(b))) == schoolbook negacyclic product.
        let mut a = ZERO_POLY;
        let mut b = ZERO_POLY;
        for i in 0..N {
            a[i] = ((i * 13 + 1) as u32 % Q) as u16;
            b[i] = ((i * 5 + 17) as u32 % Q) as u16;
        }
        let via_ntt = inv_ntt(&ntt_mul(&ntt(&a), &ntt(&b)));
        let via_school = poly_mul(&a, &b);
        assert_eq!(via_ntt, via_school, "NTT multiply != schoolbook multiply");
    }

    #[test]
    fn test_mat_transpose_involution() {
        let mut a = [ZERO_VEC; K];
        a[0][1][0] = 42;
        a[1][2][0] = 99;
        let at = mat_transpose(&a);
        let att = mat_transpose(&at);
        assert_eq!(att[0][1][0], 42);
        assert_eq!(att[1][2][0], 99);
    }
}

//! K-PKE: CPA-secure PKE inner scheme (FIPS 203 §5).
//!
//! Algorithms 12-14:
//! - K-PKE.KeyGen(d): generate encryption/decryption key pair
//! - K-PKE.Encrypt(ek, m, r): deterministic encryption
//! - K-PKE.Decrypt(dk, c): decryption
//!
//! Uses schoolbook polynomial multiplication (spec-level, not NTT-optimized).

use crate::types::*;
use crate::poly;
use crate::encode;
use crate::compress;
use crate::cbd;
use crate::specs::sha3;

/// Rejection sampler (FIPS 203 §4.2.2, Algorithm 7 inner loop): consume a
/// SHAKE-128 block as 12-bit little-endian pairs, accepting values < q.
/// Writes accepted coefficients into `f` starting at `idx`, returns the new idx.
fn rej_uniform(f: &mut Poly, idx_in: usize, block: &[u8; sha3::SHAKE128_RATE]) -> usize {
    let mut idx = idx_in;
    let mut pos = 0;
    while idx < N && pos + 3 <= sha3::SHAKE128_RATE {
        let b0 = block[pos] as u32;
        let b1 = block[pos + 1] as u32;
        let b2 = block[pos + 2] as u32;
        let d1 = b0 | ((b1 & 0xF) << 8);
        let d2 = (b1 >> 4) | (b2 << 4);
        pos += 3;
        if d1 < Q && idx < N {
            f[idx] = d1 as u16;
            idx += 1;
        }
        if d2 < Q && idx < N {
            f[idx] = d2 as u16;
            idx += 1;
        }
    }
    idx
}

/// SampleNTT (FIPS 203 Algorithm 7): rejection-sample a uniform NTT-domain poly
/// from XOF(ρ ‖ b0 ‖ b1), squeezing SHAKE-128 blocks until 256 coefficients are
/// accepted.
fn sample_ntt(rho: &[u8; 32], b0: u8, b1: u8) -> Poly {
    let mut seed = [0u8; 34];
    for i in 0..32 {
        seed[i] = rho[i];
    }
    seed[32] = b0;
    seed[33] = b1;
    let mut st = sha3::shake128_init(&seed);
    let mut f = ZERO_POLY;
    let mut idx = 0;
    while idx < N {
        let block = sha3::shake128_squeezeblock(&mut st);
        idx = rej_uniform(&mut f, idx, &block);
    }
    f
}

/// Generate the matrix Â in the NTT domain (FIPS 203 §5, K-PKE.KeyGen).
/// Â[i][j] = SampleNTT(XOF(ρ, j, i)) — the non-transposed layout: the two index
/// bytes appended to ρ are (j, i).
fn sample_matrix(rho: &[u8; 32]) -> PolyMat {
    let mut a = [ZERO_VEC; K];
    for i in 0..K {
        for j in 0..K {
            a[i][j] = sample_ntt(rho, j as u8, i as u8);
        }
    }
    a
}

/// K-PKE.KeyGen (FIPS 203, Algorithm 12).
///
/// Input: 32-byte seed d.
/// Output: (ek, dk) encryption/decryption keys.
pub fn kpke_keygen(d: &KeygenSeed) -> (IndcpaEk, IndcpaDk) {
    // Step 1: (ρ, σ) = G(d ‖ k)  — FIPS 203 domain separation with k = 3.
    let mut g_input = [0u8; 33];
    for i in 0..32 {
        g_input[i] = d[i];
    }
    g_input[32] = K as u8;
    let g_out = sha3::sha3_512(&g_input);
    let mut rho = [0u8; 32];
    let mut sigma = [0u8; 32];
    for i in 0..32 {
        rho[i] = g_out[i];
        sigma[i] = g_out[32 + i];
    }

    // Step 2-4: Sample Â (NTT domain) from ρ.
    let a_hat = sample_matrix(&rho);

    // Step 5-7: Sample s, e from CBD(η₁) using σ (nonces 0..k for s, k..2k for e).
    let mut noise_bytes = [0u8; 768]; // k * 128 * 2
    for n in 0..2 * K {
        let prf_out = sha3::prf(&sigma, n as u8, 128);
        for j in 0..128 {
            noise_bytes[n * 128 + j] = prf_out[j];
        }
    }
    let s = cbd::sample_cbd_vec(&noise_bytes[..K * 128], 128);
    let e = cbd::sample_cbd_vec(&noise_bytes[K * 128..], 128);

    // Step 8: ŝ = NTT(s), ê = NTT(e), t̂ = Â ∘ ŝ + ê (NTT domain).
    let s_hat = poly::polyvec_ntt(&s);
    let e_hat = poly::polyvec_ntt(&e);
    let a_s = poly::ntt_mat_vec(&a_hat, &s_hat);
    let t = poly::polyvec_add(&a_s, &e_hat);

    // Step 9-10: Encode ek = (encode(t̂) ‖ ρ), dk = encode(ŝ).
    let t_bytes = encode::polyvec_encode(&t);
    let mut ek = [0u8; EK_BYTES];
    for j in 0..1152 {
        ek[j] = t_bytes[j];
    }
    for j in 1152..EK_BYTES {
        ek[j] = rho[j - 1152];
    }

    let dk = encode::polyvec_encode(&s_hat);
    let mut dk_out = [0u8; INDCPA_DK_BYTES];
    for k in 0..INDCPA_DK_BYTES {
        dk_out[k] = dk[k];
    }

    (ek, dk_out)
}

/// K-PKE.Encrypt (FIPS 203, Algorithm 13).
///
/// Input: ek (encryption key), m (32-byte message), r (randomness seed).
/// Output: ciphertext c = (c₁ ‖ c₂).
pub fn kpke_encrypt(ek: &IndcpaEk, m: &[u8; SS_BYTES], r: &[u8; 32]) -> Ciphertext {
    // Step 1-2: Decode t from ek, extract ρ
    let mut t_bytes = [0u8; 1152];
    let mut rho = [0u8; 32];
    for i in 0..1152 {
        t_bytes[i] = ek[i];
    }
    for i in 1152..EK_BYTES {
        rho[i - 1152] = ek[i];
    }
    let t_hat = encode::polyvec_decode(&t_bytes);

    // Step 3: Sample Â from ρ, then Âᵀ for encryption (NTT domain).
    let a_hat = sample_matrix(&rho);
    let a_hat_t = poly::mat_transpose(&a_hat);

    // Step 4-6: Sample r, e1 (η₁) and e2 (η₂) from CBD using randomness r
    // (nonces 0..k for r, k..2k for e1, 2k for e2).
    let mut noise_bytes = [0u8; 896]; // (2k+1) * 128
    for n in 0..2 * K + 1 {
        let prf_out = sha3::prf(r, n as u8, 128);
        for j in 0..128 {
            noise_bytes[n * 128 + j] = prf_out[j];
        }
    }
    let r_vec = cbd::sample_cbd_vec(&noise_bytes[..K * 128], 128);
    let e1 = cbd::sample_cbd_vec(&noise_bytes[K * 128..2 * K * 128], 128);
    let mut e2_bytes = [0u8; 128];
    for j in 0..128 {
        e2_bytes[j] = noise_bytes[2 * K * 128 + j];
    }
    let e2 = cbd::sample_cbd2(&e2_bytes);

    // Step 7: r̂ = NTT(r); u = NTT⁻¹(Âᵀ ∘ r̂) + e1.
    let r_hat = poly::polyvec_ntt(&r_vec);
    let at_r_hat = poly::ntt_mat_vec(&a_hat_t, &r_hat);
    let mut u = ZERO_VEC;
    for i in 0..K {
        u[i] = poly::poly_add(&poly::inv_ntt(&at_r_hat[i]), &e1[i]);
    }

    // Step 8: v = NTT⁻¹(t̂ᵀ ∘ r̂) + e2 + encode(m).
    let t_r_hat = poly::ntt_dot(&t_hat, &r_hat);
    let t_r = poly::inv_ntt(&t_r_hat);
    let mu = compress::msg_encode(m);
    let v_partial = poly::poly_add(&t_r, &e2);
    let v = poly::poly_add(&v_partial, &mu);

    // Step 9-10: c = (compress(u) ‖ compress(v))
    let c1 = compress::polyvec_compress(&u);
    let c2 = compress::poly_compress_dv(&v);
    let mut ct = [0u8; CT_BYTES];
    for k in 0..960 {
        ct[k] = c1[k];
    }
    for k in 960..CT_BYTES {
        ct[k] = c2[k - 960];
    }
    ct
}

/// K-PKE.Decrypt (FIPS 203, Algorithm 14).
///
/// Input: dk (decryption key), c (ciphertext).
/// Output: 32-byte message.
pub fn kpke_decrypt(dk: &IndcpaDk, c: &Ciphertext) -> [u8; SS_BYTES] {
    // Step 1: Split ciphertext c = (c₁ ‖ c₂)
    let mut c1_bytes = [0u8; 960];
    let mut c2_bytes = [0u8; 128];
    for i in 0..960 {
        c1_bytes[i] = c[i];
    }
    for i in 960..CT_BYTES {
        c2_bytes[i - 960] = c[i];
    }

    // Step 2-3: Decompress u, v
    let u = compress::polyvec_decompress(&c1_bytes);
    let v = compress::poly_decompress_dv(&c2_bytes);

    // Step 4: Decode ŝ from dk (NTT domain).
    let mut dk_bytes = [0u8; 1152];
    for j in 0..INDCPA_DK_BYTES {
        dk_bytes[j] = dk[j];
    }
    let s_hat = encode::polyvec_decode(&dk_bytes);

    // Step 5: w = v - NTT⁻¹(ŝᵀ ∘ NTT(u)).
    let u_hat = poly::polyvec_ntt(&u);
    let s_u_hat = poly::ntt_dot(&s_hat, &u_hat);
    let s_u = poly::inv_ntt(&s_u_hat);
    let w = poly::poly_sub(&v, &s_u);

    // Step 6: Decode message
    compress::msg_decode(&w)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kpke_correctness() {
        let seed = [42u8; 32];
        let (ek, dk) = kpke_keygen(&seed);

        let msg = [0xAB, 0xCD, 0xEF, 0x01, 0x23, 0x45, 0x67, 0x89,
                   0x00, 0xFF, 0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC,
                   0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
                   0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE];
        let r = [7u8; 32];
        let ct = kpke_encrypt(&ek, &msg, &r);
        let decrypted = kpke_decrypt(&dk, &ct);
        assert_eq!(msg, decrypted, "K-PKE correctness failed");
    }

    #[test]
    fn test_kpke_different_messages() {
        let seed = [1u8; 32];
        let (ek, dk) = kpke_keygen(&seed);
        let r = [3u8; 32];

        let msg1 = [0u8; 32];
        let msg2 = [0xFF; 32];

        let ct1 = kpke_encrypt(&ek, &msg1, &r);
        let ct2 = kpke_encrypt(&ek, &msg2, &r);

        // Different messages should produce different ciphertexts
        assert_ne!(ct1, ct2);

        let dec1 = kpke_decrypt(&dk, &ct1);
        let dec2 = kpke_decrypt(&dk, &ct2);
        assert_eq!(msg1, dec1);
        assert_eq!(msg2, dec2);
    }
}

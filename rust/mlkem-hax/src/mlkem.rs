//! ML-KEM-768: KEM with Fujisaki-Okamoto transform (FIPS 203 §6-7).
//!
//! Algorithms 15-17:
//! - ML-KEM.KeyGen(): generate encapsulation/decapsulation key pair
//! - ML-KEM.Encaps(ek): encapsulate a shared secret
//! - ML-KEM.Decaps(dk, c): decapsulate
//!
//! Maps to CatCrypt's `FO_MLKEM` and `FO_UU` constructions.

use crate::types::*;
use crate::kpke;
use crate::specs::sha3;

/// ML-KEM.KeyGen (FIPS 203, Algorithm 15).
///
/// Input: 32-byte seed d, 32-byte randomness z.
/// Output: (ek, dk) encapsulation/decapsulation key pair.
///
/// dk = (dk_pke ‖ ek ‖ H(ek) ‖ z) where H = SHA3-256.
pub fn mlkem_keygen(d: &KeygenSeed, z: &[u8; 32]) -> (IndcpaEk, DecapsKey) {
    // Step 1: Generate K-PKE keys
    let (ek, dk_pke) = kpke::kpke_keygen(d);

    // Step 2: H(ek) = SHA3-256(ek)
    let h_ek = sha3::sha3_256(&ek);

    // Step 3: Assemble dk = (dk_pke ‖ ek ‖ H(ek) ‖ z)
    let mut dk = [0u8; DK_BYTES];
    // dk_pke (1152 bytes)
    for i in 0..INDCPA_DK_BYTES {
        dk[i] = dk_pke[i];
    }
    // ek (1184 bytes)
    for j in 0..EK_BYTES {
        dk[INDCPA_DK_BYTES + j] = ek[j];
    }
    // H(ek) (32 bytes)
    for j in 0..32 {
        dk[INDCPA_DK_BYTES + EK_BYTES + j] = h_ek[j];
    }
    // z (32 bytes)
    for j in 0..32 {
        dk[INDCPA_DK_BYTES + EK_BYTES + 32 + j] = z[j];
    }

    (ek, dk)
}

/// ML-KEM.Encaps (FIPS 203, Algorithm 16).
///
/// Input: ek (encapsulation key), m (32-byte randomness).
/// Output: (ct, ss) ciphertext and shared secret.
///
/// Steps:
/// 1. (K, r) = G(m ‖ H(ek))   — derive key and encryption randomness
/// 2. c = K-PKE.Encrypt(ek, m, r)
/// 3. Return (c, K)
pub fn mlkem_encaps(ek: &IndcpaEk, m: &EncapsRand) -> (Ciphertext, SharedSecret) {
    // Step 1: H(ek) = SHA3-256(ek)
    let h_ek = sha3::sha3_256(ek);

    // Step 2: G(m ‖ H(ek)) = (K, r)
    let mut g_input = [0u8; 64];
    for i in 0..32 {
        g_input[i] = m[i];
    }
    for i in 32..64 {
        g_input[i] = h_ek[i - 32];
    }
    let g_out = sha3::sha3_512(&g_input);
    let mut k = [0u8; SS_BYTES];
    let mut r = [0u8; 32];
    for j in 0..32 {
        k[j] = g_out[j];
        r[j] = g_out[32 + j];
    }

    // Step 3: c = K-PKE.Encrypt(ek, m, r)
    let ct = kpke::kpke_encrypt(ek, m, &r);

    (ct, k)
}

/// ML-KEM.Decaps (FIPS 203, Algorithm 17).
///
/// Input: dk (decapsulation key), c (ciphertext).
/// Output: ss (shared secret).
///
/// Steps:
/// 1. Extract dk_pke, ek, h, z from dk
/// 2. m' = K-PKE.Decrypt(dk_pke, c)
/// 3. (K', r') = G(m' ‖ h)
/// 4. c' = K-PKE.Encrypt(ek, m', r')
/// 5. If c = c': return K'   (valid ciphertext)
/// 6. Else: return J(z ‖ c)  (implicit rejection)
pub fn mlkem_decaps(dk: &DecapsKey, ct: &Ciphertext) -> SharedSecret {
    // Step 1: Parse dk = (dk_pke ‖ ek ‖ h ‖ z)
    let mut dk_pke = [0u8; INDCPA_DK_BYTES];
    let mut ek = [0u8; EK_BYTES];
    let mut h = [0u8; 32];
    let mut z = [0u8; 32];

    for i in 0..INDCPA_DK_BYTES {
        dk_pke[i] = dk[i];
    }
    for j in 0..EK_BYTES {
        ek[j] = dk[INDCPA_DK_BYTES + j];
    }
    for j in 0..32 {
        h[j] = dk[INDCPA_DK_BYTES + EK_BYTES + j];
    }
    for j in 0..32 {
        z[j] = dk[INDCPA_DK_BYTES + EK_BYTES + 32 + j];
    }

    // Step 2: m' = K-PKE.Decrypt(dk_pke, c)
    let m_prime = kpke::kpke_decrypt(&dk_pke, ct);

    // Step 3: (K', r') = G(m' ‖ h)
    let mut g_input = [0u8; 64];
    for k in 0..32 {
        g_input[k] = m_prime[k];
    }
    for k in 32..64 {
        g_input[k] = h[k - 32];
    }
    let g_out = sha3::sha3_512(&g_input);
    let mut k_prime = [0u8; SS_BYTES];
    let mut r_prime = [0u8; 32];
    for k in 0..32 {
        k_prime[k] = g_out[k];
        r_prime[k] = g_out[32 + k];
    }

    // Step 4: c' = K-PKE.Encrypt(ek, m', r')
    let ct_prime = kpke::kpke_encrypt(&ek, &m_prime, &r_prime);

    // Step 5-6: Check c = c', return K' or J(z ‖ c)
    let mut equal = true;
    for idx in 0..CT_BYTES {
        if ct[idx] != ct_prime[idx] {
            equal = false;
        }
    }

    if equal {
        k_prime
    } else {
        // Implicit rejection: J(z ‖ c) = SHAKE-256(z ‖ c)
        let mut j_input = [0u8; 32 + CT_BYTES];
        for p in 0..32 {
            j_input[p] = z[p];
        }
        for p in 32..32 + CT_BYTES {
            j_input[p] = ct[p - 32];
        }
        sha3::shake256(&j_input, SS_BYTES)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mlkem_correctness() {
        let d = [42u8; 32];
        let z = [99u8; 32];
        let (ek, dk) = mlkem_keygen(&d, &z);

        let m = [7u8; 32];
        let (ct, ss_enc) = mlkem_encaps(&ek, &m);
        let ss_dec = mlkem_decaps(&dk, &ct);

        assert_eq!(ss_enc, ss_dec, "ML-KEM correctness: encaps/decaps shared secrets must match");
    }

    #[test]
    fn test_mlkem_different_randomness() {
        let d = [1u8; 32];
        let z = [2u8; 32];
        let (ek, dk) = mlkem_keygen(&d, &z);

        let m1 = [10u8; 32];
        let m2 = [20u8; 32];
        let (ct1, ss1) = mlkem_encaps(&ek, &m1);
        let (ct2, ss2) = mlkem_encaps(&ek, &m2);

        // Different randomness → different shared secrets
        assert_ne!(ss1, ss2);
        assert_ne!(ct1, ct2);

        // Both should decapsulate correctly
        assert_eq!(ss1, mlkem_decaps(&dk, &ct1));
        assert_eq!(ss2, mlkem_decaps(&dk, &ct2));
    }

    #[test]
    fn test_mlkem_wrong_ciphertext() {
        let d = [5u8; 32];
        let z = [6u8; 32];
        let (ek, dk) = mlkem_keygen(&d, &z);

        let m = [3u8; 32];
        let (ct, ss) = mlkem_encaps(&ek, &m);

        // Corrupt ciphertext
        let mut bad_ct = ct;
        bad_ct[0] ^= 0xFF;
        let ss_bad = mlkem_decaps(&dk, &bad_ct);

        // Should NOT match (implicit rejection)
        assert_ne!(ss, ss_bad, "Corrupted ciphertext should trigger implicit rejection");
    }

    #[test]
    fn test_mlkem_key_sizes() {
        let d = [0u8; 32];
        let z = [0u8; 32];
        let (ek, dk) = mlkem_keygen(&d, &z);
        assert_eq!(ek.len(), EK_BYTES);   // 1184
        assert_eq!(dk.len(), DK_BYTES);   // 2400

        let m = [0u8; 32];
        let (ct, ss) = mlkem_encaps(&ek, &m);
        assert_eq!(ct.len(), CT_BYTES);   // 1088
        assert_eq!(ss.len(), SS_BYTES);   // 32
    }
}

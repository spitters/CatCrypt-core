//! ML-KEM key generation, encapsulation and decapsulation over abstract
//! primitives (FIPS 203, Algorithms 16–18).
//!
//! The three functions below are FIPS 203 ML-KEM.KeyGen_internal (Algorithm 16),
//! ML-KEM.Encaps_internal (Algorithm 17) and ML-KEM.Decaps_internal
//! (Algorithm 18). They take their randomness (d, z, m) as arguments; the
//! randomised wrappers ML-KEM.KeyGen, ML-KEM.Encaps and ML-KEM.Decaps
//! (Algorithms 19–21) draw it and add input checks, and are not part of this
//! crate.
//!
//! Every primitive is an associated function of [`FoOps`]: K-PKE.KeyGen,
//! K-PKE.Encrypt and K-PKE.Decrypt (Algorithms 13–15), H = SHA3-256,
//! G = SHA3-512 split into two halves, J = SHAKE256 with 32 bytes of output,
//! and the ciphertext comparison of Algorithm 18, step 9.
//!
//! Correspondence with the abstract model: the functions match the KEM of FIPS
//! 203 over a PKE `P` with explicit coins, a public-key hash `hpk` and oracles
//! `G : M × Hash → K × R`, `J : Z × C → K`, with
//! `P.keygen = kpke_keygen`, `P.enc = kpke_encrypt`, `P.dec = kpke_decrypt`,
//! `hpk = h`, `G(m, x) = g(m, x)` and `J(z, c) = j(z, c)`.

use crate::types::*;

/// The primitives of the ML-KEM Fujisaki–Okamoto layer.
///
/// An implementation supplies K-PKE and the three hash functions. All
/// operations are deterministic functions of their arguments.
pub trait FoOps: Copy {
    /// K-PKE.KeyGen (FIPS 203, Algorithm 13) on the seed d: returns
    /// (ek_PKE, dk_PKE).
    fn kpke_keygen(d: &Bytes32) -> (EncapsKey, DkPke);

    /// K-PKE.Encrypt (FIPS 203, Algorithm 14) of the message m under ek_PKE
    /// with coins r.
    fn kpke_encrypt(ek: &EncapsKey, m: &Bytes32, r: &Bytes32) -> Ciphertext;

    /// K-PKE.Decrypt (FIPS 203, Algorithm 15) of the ciphertext c under dk_PKE.
    fn kpke_decrypt(dk_pke: &DkPke, c: &Ciphertext) -> Bytes32;

    /// H(ek) = SHA3-256(ek) (FIPS 203, §4.1).
    fn h(ek: &EncapsKey) -> Bytes32;

    /// G(m ‖ h) = SHA3-512(m ‖ h), split into its first and second 32 bytes
    /// (K, r) (FIPS 203, §4.1). The concatenation m ‖ h is formed inside the
    /// implementation, so that a call has the form G(m, h).
    fn g(m: &Bytes32, h: &Bytes32) -> (SharedSecret, Bytes32);

    /// J(z ‖ c) = SHAKE256(z ‖ c, 8·32) (FIPS 203, §4.1).
    fn j(z: &Bytes32, c: &Ciphertext) -> SharedSecret;

    /// Equality of two ciphertexts (FIPS 203, Algorithm 18, step 9). Whether the
    /// comparison runs in constant time is a property of the implementation.
    fn ct_eq(a: &Ciphertext, b: &Ciphertext) -> bool;
}

/// ML-KEM.KeyGen_internal (FIPS 203, Algorithm 16) on the seeds d and z.
///
/// Returns (ek, dk) with dk = dk_PKE ‖ ek ‖ H(ek) ‖ z.
pub fn keygen<F: FoOps>(d: &Bytes32, z: &Bytes32) -> (EncapsKey, DecapsKey) {
    // Step 1: (ek_PKE, dk_PKE) ← K-PKE.KeyGen(d).
    let (ek, dk_pke) = F::kpke_keygen(d);
    // Step 2: ek ← ek_PKE. Step 3: dk ← dk_PKE ‖ ek ‖ H(ek) ‖ z.
    let h_ek = F::h(&ek);
    let mut dk = [0u8; DK_BYTES];
    for i in 0..DK_PKE_BYTES {
        dk[i] = dk_pke[i];
    }
    for i in 0..EK_BYTES {
        dk[DK_EK_OFFSET + i] = ek[i];
    }
    for i in 0..SEED_BYTES {
        dk[DK_H_OFFSET + i] = h_ek[i];
    }
    for i in 0..SEED_BYTES {
        dk[DK_Z_OFFSET + i] = z[i];
    }
    // Step 4: return (ek, dk).
    (ek, dk)
}

/// ML-KEM.Encaps_internal (FIPS 203, Algorithm 17) of the encapsulation key ek
/// with the message m.
///
/// Returns (K, c), in the order of FIPS 203.
pub fn encaps<F: FoOps>(ek: &EncapsKey, m: &Bytes32) -> (SharedSecret, Ciphertext) {
    // Step 1: (K, r) ← G(m ‖ H(ek)).
    let h_ek = F::h(ek);
    let (k, r) = F::g(m, &h_ek);
    // Step 2: c ← K-PKE.Encrypt(ek, m, r).
    let c = F::kpke_encrypt(ek, m, &r);
    // Step 3: return (K, c).
    (k, c)
}

/// ML-KEM.Decaps_internal (FIPS 203, Algorithm 18) of the ciphertext c under
/// the decapsulation key dk.
///
/// The hash h is read from dk, as in FIPS 203. The abstract model recomputes it
/// as `hpk pk` from the public key; the two agree on keys whose stored hash is
/// `h(ek)`, which holds for every dk produced by [`keygen`]. The link between
/// this function and the model takes that key-format invariant as hypothesis.
///
/// Both candidate keys K' and K̄ are computed before the comparison, and the
/// result is selected by the comparison, as in FIPS 203.
pub fn decaps<F: FoOps>(dk: &DecapsKey, c: &Ciphertext) -> SharedSecret {
    // Steps 1–4: parse dk = dk_PKE ‖ ek_PKE ‖ h ‖ z.
    let mut dk_pke = [0u8; DK_PKE_BYTES];
    let mut ek = [0u8; EK_BYTES];
    let mut h = [0u8; SEED_BYTES];
    let mut z = [0u8; SEED_BYTES];
    for i in 0..DK_PKE_BYTES {
        dk_pke[i] = dk[i];
    }
    for i in 0..EK_BYTES {
        ek[i] = dk[DK_EK_OFFSET + i];
    }
    for i in 0..SEED_BYTES {
        h[i] = dk[DK_H_OFFSET + i];
    }
    for i in 0..SEED_BYTES {
        z[i] = dk[DK_Z_OFFSET + i];
    }
    // Step 5: m' ← K-PKE.Decrypt(dk_PKE, c).
    let m_prime = F::kpke_decrypt(&dk_pke, c);
    // Step 6: (K', r') ← G(m' ‖ h).
    let (k_prime, r_prime) = F::g(&m_prime, &h);
    // Step 7: K̄ ← J(z ‖ c).
    let k_bar = F::j(&z, c);
    // Step 8: c' ← K-PKE.Encrypt(ek_PKE, m', r').
    let c_prime = F::kpke_encrypt(&ek, &m_prime, &r_prime);
    // Steps 9–12: return K' if c = c', and K̄ otherwise.
    if F::ct_eq(c, &c_prime) {
        k_prime
    } else {
        k_bar
    }
}

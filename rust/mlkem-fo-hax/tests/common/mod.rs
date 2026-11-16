//! The ML-KEM-768 instance of `FoOps` shared by the integration tests: K-PKE and
//! FIPS 202 SHA-3 from the crate `mlkem-hax`.

use mlkem_fo_hax::fo::FoOps;
use mlkem_fo_hax::types::*;
use mlkem_hax::kpke;
use mlkem_hax::specs::sha3;

/// The ML-KEM-768 instance of `FoOps`: K-PKE and SHA-3 from `mlkem-hax`.
#[derive(Clone, Copy)]
pub struct MlKem768Ops;

impl FoOps for MlKem768Ops {
    fn kpke_keygen(d: &Bytes32) -> (EncapsKey, DkPke) {
        kpke::kpke_keygen(d)
    }

    fn kpke_encrypt(ek: &EncapsKey, m: &Bytes32, r: &Bytes32) -> Ciphertext {
        kpke::kpke_encrypt(ek, m, r)
    }

    fn kpke_decrypt(dk_pke: &DkPke, c: &Ciphertext) -> Bytes32 {
        kpke::kpke_decrypt(dk_pke, c)
    }

    fn h(ek: &EncapsKey) -> Bytes32 {
        sha3::sha3_256(ek)
    }

    fn g(m: &Bytes32, h: &Bytes32) -> (SharedSecret, Bytes32) {
        let mut input = [0u8; 64];
        for i in 0..32 {
            input[i] = m[i];
            input[32 + i] = h[i];
        }
        let out = sha3::sha3_512(&input);
        let mut k = [0u8; SS_BYTES];
        let mut r = [0u8; SEED_BYTES];
        for i in 0..32 {
            k[i] = out[i];
            r[i] = out[32 + i];
        }
        (k, r)
    }

    fn j(z: &Bytes32, c: &Ciphertext) -> SharedSecret {
        let mut input = [0u8; SEED_BYTES + CT_BYTES];
        for i in 0..SEED_BYTES {
            input[i] = z[i];
        }
        for i in 0..CT_BYTES {
            input[SEED_BYTES + i] = c[i];
        }
        sha3::shake256(&input, SS_BYTES)
    }

    fn ct_eq(a: &Ciphertext, b: &Ciphertext) -> bool {
        // Accumulates the difference over all bytes, without an early exit.
        let mut diff = 0u8;
        for i in 0..CT_BYTES {
            diff |= a[i] ^ b[i];
        }
        diff == 0
    }
}

//! Differential test of the generic FO layer against libcrux-ml-kem.
//!
//! For pseudo-random seeds, the generic `keygen::<MlKem768Ops>`, `encaps` and
//! `decaps` of this crate, instantiated with K-PKE and SHA-3 from `mlkem-hax`,
//! are run beside the public derandomised ML-KEM-768 interface of
//! `libcrux-ml-kem` (`mlkem768::generate_key_pair`, `encapsulate`,
//! `decapsulate`) on the same inputs: the key generation seed d ‖ z and the
//! encapsulation coin m. Each trial asserts byte equality of the encapsulation
//! key, the decapsulation key, the ciphertext and the shared secret, of the
//! decapsulation of the honest ciphertext, and of the decapsulation of a
//! ciphertext with one flipped byte (the implicit-rejection branch).

mod common;

use common::MlKem768Ops;
use libcrux_ml_kem::mlkem768;
use mlkem_fo_hax::fo::{decaps, encaps, keygen};
use mlkem_fo_hax::types::*;

type Ops = MlKem768Ops;

/// Number of trials.
const TRIALS: usize = 64;

/// xorshift64* generator, so the inputs are reproducible without a `rand`
/// dependency.
struct Gen(u64);

impl Gen {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn fill(&mut self, out: &mut [u8]) {
        for chunk in out.chunks_mut(8) {
            let w = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&w[..chunk.len()]);
        }
    }
}

#[test]
fn generic_layer_agrees_with_libcrux_mlkem768() {
    let mut gen = Gen(0x9E37_79B9_7F4A_7C15);
    for trial in 0..TRIALS {
        let mut seed = [0u8; 64];
        gen.fill(&mut seed);
        let mut m = [0u8; 32];
        gen.fill(&mut m);
        let mut d = [0u8; 32];
        let mut z = [0u8; 32];
        d.copy_from_slice(&seed[..32]);
        z.copy_from_slice(&seed[32..]);

        // Key generation.
        let kp = mlkem768::generate_key_pair(seed);
        let (ek, dk) = keygen::<Ops>(&d, &z);
        assert_eq!(&ek[..], &kp.pk()[..], "trial {trial}: encapsulation key");
        assert_eq!(&dk[..], &kp.sk()[..], "trial {trial}: decapsulation key");

        // Encapsulation.
        let (ct_ref, ss_ref) = mlkem768::encapsulate(kp.public_key(), m);
        let (ss, ct): (SharedSecret, Ciphertext) = encaps::<Ops>(&ek, &m);
        assert_eq!(&ct[..], &ct_ref.as_slice()[..], "trial {trial}: ciphertext");
        assert_eq!(ss, ss_ref, "trial {trial}: shared secret");

        // Decapsulation of the honest ciphertext.
        let ss_dec_ref = mlkem768::decapsulate(kp.private_key(), &ct_ref);
        assert_eq!(decaps::<Ops>(&dk, &ct), ss_dec_ref, "trial {trial}: decaps");
        assert_eq!(ss_dec_ref, ss_ref, "trial {trial}: libcrux round trip");

        // Decapsulation of a tampered ciphertext (implicit rejection).
        let mut bad = ct;
        let pos = (gen.next_u64() as usize) % CT_BYTES;
        bad[pos] ^= 1 << (gen.next_u64() % 8);
        let bad_ref = mlkem768::MlKem768Ciphertext::from(bad);
        let rej_ref = mlkem768::decapsulate(kp.private_key(), &bad_ref);
        let rej = decaps::<Ops>(&dk, &bad);
        assert_eq!(rej, rej_ref, "trial {trial}: implicit rejection");
        assert_ne!(rej, ss, "trial {trial}: rejection key differs from K");
    }
}

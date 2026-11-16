//! NIST ML-KEM-768 known-answer test, byte-for-byte, gating `cargo test`.
//!
//! Vectors are the official ML-KEM-768 NIST KATs as published in libcrux's
//! `mlkem768_nistkats.json` (`libcrux-ml-kem/cg/tests/`). Each record fixes:
//!   - `key_generation_seed` = d ‖ z (64 bytes)
//!   - SHA3-256(public key), SHA3-256(secret key)
//!   - `encapsulation_seed` = m (32 bytes)
//!   - SHA3-256(ciphertext), and the raw shared secret.
//!
//! The test drives this crate's OWN keygen/encaps/decaps and asserts every
//! public output is byte-identical to the vector, using the crate's OWN
//! SHA3-256 to hash the multi-kilobyte pk/sk/ct down to the pinned digests.

use mlkem_hax::mlkem;
use mlkem_hax::specs::sha3;

/// Parse a lowercase hex string into a byte vector.
fn unhex(s: &str) -> Vec<u8> {
    fn nib(c: u8) -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            b'A'..=b'F' => c - b'A' + 10,
            _ => panic!("bad hex digit"),
        }
    }
    let b = s.as_bytes();
    assert!(b.len() % 2 == 0, "odd hex length");
    let mut out = Vec::with_capacity(b.len() / 2);
    let mut i = 0;
    while i < b.len() {
        out.push((nib(b[i]) << 4) | nib(b[i + 1]));
        i += 2;
    }
    out
}

struct Kat {
    keygen_seed: &'static str, // d || z (64 bytes)
    pk_hash: &'static str,     // SHA3-256(ek)
    sk_hash: &'static str,     // SHA3-256(dk)
    encaps_seed: &'static str, // m (32 bytes)
    ct_hash: &'static str,     // SHA3-256(ct)
    shared_secret: &'static str,
}

// ML-KEM-768 NIST KAT vectors 0 and 1 (libcrux mlkem768_nistkats.json).
const KATS: [Kat; 2] = [
    Kat {
        keygen_seed: "7c9935a0b07694aa0c6d10e4db6b1add2fd81a25ccb148032dcd739936737f2d8626ed79d451140800e03b59b956f8210e556067407d13dc90fa9e8b872bfb8f",
        pk_hash: "f57262661358cde8d3ebf990e5fd1d5b896c992ccfaadb5256b68bbf5943b132",
        sk_hash: "7deef44965b03d76de543ad6ef9e74a2772fa5a9fa0e761120dac767cf0152ef",
        encaps_seed: "147c03f7a5bebba406c8fae1874d7f13c80efe79a3a9a874cc09fe76f6997615",
        ct_hash: "6e777e2cf8054659136a971d9e70252f301226930c19c470ee0688163a63c15b",
        shared_secret: "e7184a0975ee3470878d2d159ec83129c8aec253d4ee17b4810311d198cd0368",
    },
    Kat {
        keygen_seed: "d60b93492a1d8c1c7ba6fc0b733137f3406cee8110a93f170e7a78658af326d9003271531cf27285b8721ed5cb46853043b346a66cba6cf765f1b0eaa40bf672",
        pk_hash: "7b00751eb9b1253231213f8a14f06f0fe1b7a4fdb7d1cfe44c161e577e5e8f0a",
        sk_hash: "3a8c009e8e648ac572d5592e4a92907fae0c1767be41c544b59dc3ffe61f7ded",
        encaps_seed: "cde797df8ce67231f6c5d15811843e01eb2ab84c7490931240822adbddd72046",
        ct_hash: "bce1bf3450f574130b9561ee11565fa41d599d05d2136f10ad2c013eb5d13ca9",
        shared_secret: "5f0c5d9f39d3e724b5a2bd54e69e360f72ffab5d4d6cc5e572fecba80acd4796",
    },
];

fn run_kat(kat: &Kat) {
    let seed = unhex(kat.keygen_seed);
    assert_eq!(seed.len(), 64, "keygen seed = d || z (64 bytes)");
    let mut d = [0u8; 32];
    let mut z = [0u8; 32];
    d.copy_from_slice(&seed[..32]);
    z.copy_from_slice(&seed[32..]);

    let (ek, dk) = mlkem::mlkem_keygen(&d, &z);
    assert_eq!(
        sha3::sha3_256(&ek).to_vec(),
        unhex(kat.pk_hash),
        "SHA3-256(public key) != NIST KAT"
    );
    assert_eq!(
        sha3::sha3_256(&dk).to_vec(),
        unhex(kat.sk_hash),
        "SHA3-256(secret key) != NIST KAT"
    );

    let mseed = unhex(kat.encaps_seed);
    assert_eq!(mseed.len(), 32, "encaps seed = m (32 bytes)");
    let mut m = [0u8; 32];
    m.copy_from_slice(&mseed);

    let (ct, ss) = mlkem::mlkem_encaps(&ek, &m);
    assert_eq!(
        sha3::sha3_256(&ct).to_vec(),
        unhex(kat.ct_hash),
        "SHA3-256(ciphertext) != NIST KAT"
    );
    assert_eq!(ss.to_vec(), unhex(kat.shared_secret), "shared secret != NIST KAT");

    // Round-trip: decaps recovers exactly the encaps shared secret.
    let ss_dec = mlkem::mlkem_decaps(&dk, &ct);
    assert_eq!(ss_dec.to_vec(), unhex(kat.shared_secret), "decaps shared secret != NIST KAT");
}

#[test]
fn nist_kat_0_byte_identical() {
    run_kat(&KATS[0]);
}

#[test]
fn nist_kat_1_byte_identical() {
    run_kat(&KATS[1]);
}

#[test]
fn nist_kat_implicit_reject() {
    // A one-bit-tampered ciphertext must NOT recover the real shared secret.
    let seed = unhex(KATS[0].keygen_seed);
    let mut d = [0u8; 32];
    let mut z = [0u8; 32];
    d.copy_from_slice(&seed[..32]);
    z.copy_from_slice(&seed[32..]);
    let (ek, dk) = mlkem::mlkem_keygen(&d, &z);
    let mseed = unhex(KATS[0].encaps_seed);
    let mut m = [0u8; 32];
    m.copy_from_slice(&mseed);
    let (ct, ss) = mlkem::mlkem_encaps(&ek, &m);

    let mut bad = ct;
    bad[0] ^= 0x01;
    let ss_bad = mlkem::mlkem_decaps(&dk, &bad);
    assert_ne!(ss_bad, ss, "tampered ciphertext still recovered the shared secret");
}

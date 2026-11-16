# mlkem-fo-hax

The Fujisaki–Okamoto layer of ML-KEM-768 (FIPS 203, Algorithms 16–18), generic
over its primitives, written for extraction by hax and Aeneas.

The crate contains ML-KEM.KeyGen_internal, ML-KEM.Encaps_internal and
ML-KEM.Decaps_internal and nothing below them. K-PKE and the hash functions are
the associated functions of the trait `FoOps` (`src/fo.rs`):

| Operation | FIPS 203 |
|---|---|
| `kpke_keygen(d) -> (ek, dk_pke)` | K-PKE.KeyGen, Algorithm 13 |
| `kpke_encrypt(ek, m, r) -> c` | K-PKE.Encrypt, Algorithm 14 |
| `kpke_decrypt(dk_pke, c) -> m` | K-PKE.Decrypt, Algorithm 15 |
| `h(ek)` | H = SHA3-256 |
| `g(m, h) -> (K, r)` | G = SHA3-512 of m ‖ h, split into halves |
| `j(z, c)` | J = SHAKE256 of z ‖ c, 32 bytes |
| `ct_eq(a, b)` | ciphertext comparison, Algorithm 18, step 9 |

The generic functions `keygen<F: FoOps>(d, z) -> (ek, dk)`,
`encaps<F: FoOps>(ek, m) -> (K, c)` and `decaps<F: FoOps>(dk, c) -> K` are
straight-line call sequences over these operations; the only other work is the
(de)serialisation of the decapsulation key dk = dk_PKE ‖ ek ‖ H(ek) ‖ z. They
correspond to the KEM of FIPS 203 over an abstract PKE with explicit coins, a
public-key hash and two random oracles G and J. Decapsulation reads H(ek) from
dk, as FIPS 203 does; a model that recomputes the hash from the public key
agrees with it on every key produced by `keygen`.

The code uses the Rust subset accepted by the extraction tools: fixed-size byte
arrays, `for` loops over `usize` ranges, and no slices, iterators, heap
allocation, early returns or closures. The crate has no dependencies.

## Tests

The tests instantiate `FoOps` with the K-PKE and FIPS 202 SHA-3 of the crate
`mlkem-hax` (a dev-dependency, `tests/common/mod.rs`).

`tests/libcrux_diff.rs` runs the generic layer beside the public, derandomised
ML-KEM-768 interface of the published `libcrux-ml-kem` 0.0.10 on 64
pseudo-random seed pairs and checks byte equality of the encapsulation key, the
decapsulation key, the ciphertext, the shared secret, honest decapsulation and
the decapsulation of a ciphertext with one flipped bit.

`tests/nist_kat.rs` checks:

- the generic `keygen`, `encaps` and `decaps` against the NIST ML-KEM-768
  known-answer vectors 0 and 1 (SHA3-256 of ek, dk and c, and the shared
  secret, byte for byte);
- implicit rejection: a tampered ciphertext decapsulates to J(z ‖ c);
- byte-for-byte agreement with the concrete `mlkem_keygen`, `mlkem_encaps` and
  `mlkem_decaps` of `mlkem-hax` on the KAT inputs and on a tampered ciphertext.

Run with `cargo test`.

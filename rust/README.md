# Rust sources of the extracted crates

Each crate below is the Rust source of a hax extraction in this library. The Lean
side states what the extracted functions compute and which security bound holds for
them.

| Crate | Extraction | Bridge |
|---|---|---|
| `schnorr-hax` | `CatCryptCore/Crypto/Schnorr/Extraction/Schnorr_haxpipe.lean` | `CatCryptCore/Crypto/Schnorr/SurfaceDeps.lean` |
| `mlkem-fo-hax` | `CatCryptCore/Crypto/KEM/MlkemFo/Extraction/MlkemFo_haxpipe.lean` | `CatCryptCore/Crypto/KEM/MlkemFo/SurfaceDeps.lean` |
| `mlkem-hax` | none | test instance of `mlkem-fo-hax` |

## `schnorr-hax`

Schnorr signatures (`keygen`, `sign`, `verify`) generic over a trait `SchnorrCrypto`
with the scalar and group operations, the generator and the challenge hash. The
tests instantiate the trait with secp256k1 and the BIP-340 tagged hashes (RustCrypto
`k256` and `sha2`) and reproduce the BIP-340 signature vectors 0–3 byte for byte.

The bridge interprets the trait's operations through a `GroupParam` and shows that the
EUF-CMA game in the random-oracle model, run on the extracted `keygen`, `sign` and
`verify`, is the game of `SchnorrROM` (`extGameDist_eq`), so the discrete-logarithm
bound holds for the extracted functions (`schnorr_extracted_rom_eufcma`).

## `mlkem-fo-hax`

The Fujisaki–Okamoto layer of ML-KEM-768, FIPS 203 Algorithms 16–18
(`ML-KEM.KeyGen_internal`, `Encaps_internal`, `Decaps_internal`), generic over a trait
`FoOps` with K-PKE key generation, encryption and decryption, the hash functions H, G
and J and the ciphertext comparison. K-PKE and the hash functions are calls to linked
code, so the extraction contains the orchestration only.

The tests instantiate the trait with the K-PKE and SHA-3 of `mlkem-hax`, check the NIST
ML-KEM-768 known-answer vectors 0 and 1 and implicit rejection, and compare the generic
layer byte for byte with the derandomised ML-KEM-768 interface of the published
`libcrux-ml-kem` 0.0.10 on 64 pseudo-random inputs.

The bridge shows, under a record `PkeHom` of how the trait's operations act on the
encodings of a public-key encryption scheme `P`, that the extracted functions compute
`fips203 P hpk` (`encaps_enc`, `decaps_enc`), that the KEM built from them has the
IND-CCA game of `fips203 P hpk`, and that the bound of `fips203_indcca` holds for it
(`extFO_indcca`).

## Regenerating an extraction

The extraction is produced by `haxpipeT` of [hax-lean](https://github.com/spitters/hax-lean)
from the crate's hax frontend export:

```
cargo hax json --use-ids                      # in the crate directory
haxpipeT --hax hax_frontend_export.json --emit-certified --name <Name> > <Name>_haxpipe.lean
```

The committed extraction files are in module form (`module`, `public import`,
`@[expose] public section`).

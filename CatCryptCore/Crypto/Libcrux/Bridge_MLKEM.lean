/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Libcrux.Extraction.Libcrux_specs
public import CatCryptCore.Crypto.Libcrux.ConcreteInstances
public import CatCryptCore.Examples.KEMDEM

/-!
# ML-KEM Bridge: libcrux-specs → CatCrypt `KEMScheme`

Bridges the ML-KEM (FIPS 203) key encapsulation mechanism of libcrux-specs to the KEM schemes
`KEMScheme` of CatCrypt (`CatCryptCore.Examples.KEMDEM`), used by the KEM CKA of the triple
ratchet (`CatCrypt.Crypto.Messaging.kemCKA`) and by the KEM game of PQXDH.

## Architecture

```
libcrux-specs/src/mlkem.rs                 (Rust ML-KEM)
        ↓  opaque
mlkem{768,1024}_keygen, _encaps, _decaps   (deterministic functions of the randomness)
        ↓
concreteMLKEM_768, concreteMLKEM_1024      (KEMScheme: keys, ciphertexts, shared secrets)
```

The three algorithms are opaque deterministic functions of their inputs and of the randomness
(two 32-byte seeds `d`, `z` for key generation, one 32-byte message `m` for encapsulation),
with the byte sizes of FIPS 203: encapsulation keys of 1184 (ML-KEM-768) and 1568 (ML-KEM-1024)
bytes, decapsulation keys of 2400 and 3168 bytes, ciphertexts of 1088 and 1568 bytes, and
32-byte shared secrets. The KEM schemes sample the randomness uniformly. Correctness and
security of the opaque functions are not stated here.

## Key Results

| Definition / Theorem | Role |
|-----|------|
| `concreteMLKEM_768`  | `KEMScheme` for ML-KEM-768 |
| `concreteMLKEM_1024` | `KEMScheme` for ML-KEM-1024 |
| `concreteMLKEM_768_kgen_isPure`, `concreteMLKEM_768_encap_isPure` | purity (also for 1024) |

## References

* FIPS 203 — Module-Lattice-Based Key-Encapsulation Mechanism Standard
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Libcrux.Bridge_MLKEM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Examples.KEMDEM
open CatCrypt.Crypto.Libcrux.ConcreteInstances
open scoped ENNReal

/-! ## ML-KEM opaque specs -/

/-- ML-KEM-768 key generation from the seeds `(d, z)`: encapsulation key (1184 bytes) and
decapsulation key (2400 bytes). Rust: `mlkem768_generate_key_pair`. -/
opaque mlkem768_keygen :
  Vector UInt8 32 × Vector UInt8 32 → Vector UInt8 1184 × Vector UInt8 2400

/-- ML-KEM-768 encapsulation of the message `m` under the encapsulation key: shared secret and
ciphertext (1088 bytes). Rust: `mlkem768_encapsulate`. -/
opaque mlkem768_encaps :
  Vector UInt8 1184 → Vector UInt8 32 → Vector UInt8 32 × Vector UInt8 1088

/-- ML-KEM-768 decapsulation. Rust: `mlkem768_decapsulate`. -/
opaque mlkem768_decaps : Vector UInt8 2400 → Vector UInt8 1088 → Vector UInt8 32

/-- ML-KEM-1024 key generation from the seeds `(d, z)`: encapsulation key (1568 bytes) and
decapsulation key (3168 bytes). Rust: `mlkem1024_generate_key_pair`. -/
opaque mlkem1024_keygen :
  Vector UInt8 32 × Vector UInt8 32 → Vector UInt8 1568 × Vector UInt8 3168

/-- ML-KEM-1024 encapsulation of the message `m` under the encapsulation key: shared secret and
ciphertext (1568 bytes). Rust: `mlkem1024_encapsulate`. -/
opaque mlkem1024_encaps :
  Vector UInt8 1568 → Vector UInt8 32 → Vector UInt8 32 × Vector UInt8 1568

/-- ML-KEM-1024 decapsulation. Rust: `mlkem1024_decapsulate`. -/
opaque mlkem1024_decaps : Vector UInt8 3168 → Vector UInt8 1568 → Vector UInt8 32

/-! ## The KEM schemes -/

/-- ML-KEM-768 as a KEM scheme: uniform seeds and messages, the opaque algorithms. -/
noncomputable def concreteMLKEM_768 :
    KEMScheme (Vector UInt8 1184) (Vector UInt8 2400) (Vector UInt8 32) (Vector UInt8 1088) where
  kgen := (SPComp.sample (Vector UInt8 32 × Vector UInt8 32)).bind fun r =>
    SPComp.pure (mlkem768_keygen r)
  encap pk := (SPComp.sample (Vector UInt8 32)).bind fun m => SPComp.pure (mlkem768_encaps pk m)
  decap := mlkem768_decaps

/-- ML-KEM-1024 as a KEM scheme: uniform seeds and messages, the opaque algorithms. -/
noncomputable def concreteMLKEM_1024 :
    KEMScheme (Vector UInt8 1568) (Vector UInt8 3168) (Vector UInt8 32) (Vector UInt8 1568) where
  kgen := (SPComp.sample (Vector UInt8 32 × Vector UInt8 32)).bind fun r =>
    SPComp.pure (mlkem1024_keygen r)
  encap pk := (SPComp.sample (Vector UInt8 32)).bind fun m => SPComp.pure (mlkem1024_encaps pk m)
  decap := mlkem1024_decaps

/-- The key generation of ML-KEM-768 does not touch the heap. -/
theorem concreteMLKEM_768_kgen_isPure : SPComp.IsPure concreteMLKEM_768.kgen :=
  SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _

/-- The encapsulation of ML-KEM-768 does not touch the heap. -/
theorem concreteMLKEM_768_encap_isPure (pk : Vector UInt8 1184) :
    SPComp.IsPure (concreteMLKEM_768.encap pk) :=
  SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _

/-- The key generation of ML-KEM-1024 does not touch the heap. -/
theorem concreteMLKEM_1024_kgen_isPure : SPComp.IsPure concreteMLKEM_1024.kgen :=
  SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _

/-- The encapsulation of ML-KEM-1024 does not touch the heap. -/
theorem concreteMLKEM_1024_encap_isPure (pk : Vector UInt8 1568) :
    SPComp.IsPure (concreteMLKEM_1024.encap pk) :=
  SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _

end CatCrypt.Crypto.Libcrux.Bridge_MLKEM

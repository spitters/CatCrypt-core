/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FIPS203KEM
public import CatCryptCore.Crypto.MLKEM.MLWE_PKE_Scheme

/-!
# Incremental ML-KEM encapsulation

The encapsulation of `KEM.FIPS203.fips203 (toScheme P) hpk`, FIPS 203 Algorithm 17 over the
MLWE public-key encryption scheme `toScheme P`, splits into two steps, as in the incremental
ML-KEM of the Signal post-quantum ratchet SPQR. The public key `(A, t)` splits into a header
`(A, H(ek))`, the matrix (the stand-in for the seed `ρ` of FIPS 203) and the public-key hash,
and the encapsulation-key vector `t`.

* `encaps1 P g hdr m` — on the header and the message `m`: `(K, r) := g (m, H(ek))`, the first
  ciphertext component `u = Aᵀ r₀ + e₁` of the noise `(r₀, e₁, e₂)` drawn from the seed `r`, the
  state `(r, m)` and the key `K`.
* `encaps2 P st t` — on the state `(r, m)` and the vector `t`: the second ciphertext component
  `v = t · r₀ + e₂ + encode m`.
* `encapsInternal P g hdr t m` — FIPS 203 encapsulation of `m` with the public-key hash read from
  the header: the key `(g (m, H(ek))).1` and the ciphertext of `toScheme P` under the seed
  `(g (m, H(ek))).2`.

## Main results

* `encapsInternal_split` — `encapsInternal` is `encaps1` on the header followed by `encaps2` on
  the state and the vector.
* `mlkem_incr_split` — against fixed oracle functions `g` and `j`, the encapsulation of
  `fips203 (toScheme P) hpk` at `pk = (A, t)` draws `m` uniformly and returns the key of
  `encaps1` on `(A, hpk pk)` and the ciphertext `(u, v)` of `encaps1` and `encaps2`.

## The model

* The oracle `G` of FIPS 203 is the fixed function `g`; `fips203` reads it through
  `KEM.FIPS203.fixedRO2`.
* The ciphertext of `toScheme P` is uncompressed, and the matrix `A` stands for its seed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.IncrementalEncaps

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.KEM.FIPS203 (fips203 fixedRO2 run_encaps_fixed)
open MLWE_PKE_Basic (CT)
open MLWE_PKE_Scheme (toScheme)

variable (P : MLWE_PKE_Scheme.Params) {K Hash : Type}

/-- FIPS 203 encapsulation of `m` with the public-key hash read from the header `(A, h)`:
`(K, r) := g (m, h)`, and the ciphertext of `toScheme P` on `(A, t)` under the seed `r`. -/
noncomputable def encapsInternal (g : P.PT × Hash → K × P.Seed) (hdr : P.Mat × Hash) (t : P.Vec)
    (m : P.PT) : K × CT P.toBasic :=
  ((g (m, hdr.2)).1, (toScheme P).enc (hdr.1, t) m (g (m, hdr.2)).2)

/-- `Encaps1` on the header `(A, h)` and the message `m`: the first ciphertext component
`Aᵀ r₀ + e₁` of the noise drawn from the seed `(g (m, h)).2`, the state (seed, message) and
the key `(g (m, h)).1`. -/
def encaps1 (g : P.PT × Hash → K × P.Seed) (hdr : P.Mat × Hash) (m : P.PT) :
    P.Vec × (P.Seed × P.PT) × K :=
  (P.vec_add (P.mat_vec_mul (P.mat_transpose hdr.1) (P.sampleShort (g (m, hdr.2)).2).1)
      (P.sampleShort (g (m, hdr.2)).2).2.1,
    ((g (m, hdr.2)).2, m), (g (m, hdr.2)).1)

/-- `Encaps2` on the state `(r, m)` and the vector `t`: the second ciphertext component
`t · r₀ + e₂ + encode m` of the noise drawn from the seed `r`. -/
def encaps2 (st : P.Seed × P.PT) (t : P.Vec) : P.R :=
  P.ring_add (P.ring_add (P.vec_dot t (P.sampleShort st.1).1) (P.sampleShort st.1).2.2)
    (P.m_encode st.2)

/-- FIPS 203 encapsulation is `encaps1` on the header followed by `encaps2` on the state and
the vector. -/
theorem encapsInternal_split (g : P.PT × Hash → K × P.Seed) (hdr : P.Mat × Hash) (t : P.Vec)
    (m : P.PT) :
    encapsInternal P g hdr t m =
      ((encaps1 P g hdr m).2.2,
        ((encaps1 P g hdr m).1, encaps2 P (encaps1 P g hdr m).2.1 t)) := by
  simp only [encapsInternal, encaps1, encaps2, toScheme]

variable [Nonempty K]

/-- **Incremental ML-KEM encapsulation.** Against fixed oracle functions `g` and `j`, the
encapsulation of `fips203 (toScheme P) hpk` at `pk = (A, t)` draws `m` uniformly and returns
the key of `encaps1` on the header `(A, hpk pk)` and the ciphertext whose first component is
the output of `encaps1` and whose second component is `encaps2` on its state and `t`. -/
theorem mlkem_incr_split {Z : Type} [Fintype Z] [Nonempty Z]
    (hpk : MLWE_PKE_Basic.PK P.toBasic → Hash) (g : P.PT × Hash → K × P.Seed)
    (j : Z × CT P.toBasic → K) (pk : MLWE_PKE_Basic.PK P.toBasic) :
    OracleAdv.run (fixedRO2 g j) ((fips203 (Z := Z) (toScheme P) hpk).encaps pk) () =
      (PMF.uniformFintype P.PT).map fun m =>
        (((encaps1 P g (pk.1, hpk pk) m).2.2,
          ((encaps1 P g (pk.1, hpk pk) m).1,
            encaps2 P (encaps1 P g (pk.1, hpk pk) m).2.1 pk.2)), ()) := by
  rw [run_encaps_fixed]
  simp only [← encapsInternal_split]
  rfl

end CatCrypt.Crypto.MLKEM.IncrementalEncaps

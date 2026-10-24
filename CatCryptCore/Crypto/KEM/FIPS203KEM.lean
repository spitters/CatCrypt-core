/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.Games
public import CatCryptCore.Crypto.PKE.Games

/-!
# The ML-KEM transform as a KEM with two random oracles

`fips203 P hpk` is the key encapsulation mechanism of FIPS 203, Algorithms 16–18,
over an arbitrary public-key encryption scheme `P : Scheme PK SK M C R` with explicit
coins, a public-key hash `hpk : PK → Hash`, and two random oracles
`G : M × Hash → K × R` and `J : Z × C → K`, as a `KEM.Games.ROM2Scheme`.

* Key generation draws `(pk, sk)` from `P` and a seed `z` uniform in `Z`; the secret
  key is `(sk, pk, z)`. FIPS 203 also stores `H(ek)` in the decapsulation key; it is
  `hpk pk`, recomputed here.
* Encapsulation draws `m` uniform in `M`, sets `(K, r) := G(m, hpk pk)` and returns
  `(K, P.enc pk m r)`.
* Decapsulation of `c` decrypts `m' := P.dec sk c`, sets `(K', r') := G(m', hpk pk)`,
  and returns `K'` when `P.enc pk m' r' = c`; otherwise, and when decryption
  rejects, it returns `J(z, c)`.

## Main definitions

* `fips203 P hpk` — the KEM
* `fips203INDCCAAdvantage P hpk B` — its IND-CCA advantage, `rom2INDCCAAdvantage`
* `fixedRO2 g j` — the two oracles as fixed functions, for pointwise statements
* `tKeyed P f`, `uKeyed Q kdf` — the derandomised PKE with a public-key-dependent
  derandomiser and the U-transform with a key-derivation function and a
  seeded rejection oracle
* `IsTUFactoring P hpk` — the factoring `fips203 = uKeyed[tKeyed[P, G'], J]`

## Main results

* `run_encaps_fixed` — encapsulation against fixed oracles
* `decaps_encaps_fixed` — decapsulation of `P.enc pk m (G (m, hpk pk)).2` returns
  `(G (m, hpk pk)).1` against fixed oracles when `P` decrypts the ciphertext to `m`
* `decaps_encaps_table` — the same against the lazily sampled oracles from a table
  that holds the query of encapsulation
* `isTUFactoring` — `fips203 P hpk` satisfies `IsTUFactoring P hpk`

## The model

* `fips203` is a `KEM.Games.ROM2Scheme`: `G` and `J` are the two lazily sampled
  oracles of `rom2INDCCAGame`, queried on classical inputs.
* `hpk` is a fixed function of the public key. FIPS 203 computes `H(ek)` with
  SHA3-256; `fips203` takes it as a public value determined by the public key.
* The oracle programs of `fips203` query `G` and `J` only on the branch that uses
  the answer, where FIPS 203 evaluates both hashes unconditionally. The two oracles
  are independent, so the answers returned have the same distribution.
* `tKeyed` is `PKE.FOTransformT.tTransform` with a derandomiser `PK → M → R` that
  depends on the public key, and `uKeyed` is `KEM.FOTransformU.uNotBot` with a
  key-derivation function in place of `H(m, c)` and a separate oracle `J` for
  rejection. `isTUFactoring` identifies `fips203 P hpk` with `uKeyed[tKeyed[P, G'], J]` for
  fixed oracle functions `g` and `j`.
* `P` is an arbitrary scheme with explicit coins; no statement fixes K-PKE
  parameters.

## References

* NIST FIPS 203, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*,
  Algorithms 16–18.
* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the
  Fujisaki–Okamoto Transformation*, TCC 2017, ePrint 2017/604.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.FIPS203

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.PKE.Games CatCrypt.Crypto.KEM.Games
open scoped ENNReal

variable {PK SK M C R K Hash Z : Type} [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Nonempty R] [Nonempty K] [DecidableEq C]

/-! ## The transform -/

/-- A query to `G` at `q`, as a program on the two random oracles. -/
noncomputable def gQ (q : M × Hash) : OracleAdv ((M × Hash) ⊕ (Z × C)) ((K × R) ⊕ K) (K × R) :=
  .query (.inl q) fun a => .ret (a.elim id fun _ => Classical.arbitrary (K × R))

/-- A query to `J` at `q`, as a program on the two random oracles. -/
noncomputable def jQ (q : Z × C) : OracleAdv ((M × Hash) ⊕ (Z × C)) ((K × R) ⊕ K) K :=
  .query (.inr q) fun a => .ret (a.elim (fun _ => Classical.arbitrary K) id)

/-- The ML-KEM transform of `P` with public-key hash `hpk`: FIPS 203, Algorithms
16–18, with `G` and `J` as random oracles. The secret key is `(sk, pk, z)`. -/
noncomputable def fips203 (P : Scheme PK SK M C R) (hpk : PK → Hash) :
    ROM2Scheme PK (SK × PK × Z) K C (M × Hash) (K × R) (Z × C) K where
  keygen := P.keygen.bind fun ks =>
    (PMF.uniformFintype Z).map fun z => (ks.1, (ks.2, ks.1, z))
  encaps pk := .rand (PMF.uniformFintype M) fun m =>
    (gQ (m, hpk pk)).bind fun kr => .ret (kr.1, P.enc pk m kr.2)
  decaps sk c := match P.dec sk.1 c with
    | none => (jQ (sk.2.2, c)).bind fun k => .ret (some k)
    | some m => (gQ (m, hpk sk.2.1)).bind fun kr =>
        if P.enc sk.2.1 m kr.2 = c then .ret (some kr.1)
        else (jQ (sk.2.2, c)).bind fun k => .ret (some k)

/-- The IND-CCA advantage of `fips203 P hpk` against `B`, in the two-oracle game
`rom2INDCCAGame`. -/
noncomputable def fips203INDCCAAdvantage [DecidableEq M] [DecidableEq Hash] [DecidableEq Z]
    [Fintype R] [Fintype K] (P : Scheme PK SK M C R) (hpk : PK → Hash) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) : ℝ≥0∞ :=
  rom2INDCCAAdvantage (fips203 P hpk) B

/-! ## Correctness -/

/-- The two oracles as fixed functions `g` and `j`, without state. -/
noncomputable def fixedRO2 (g : M × Hash → K × R) (j : Z × C → K) (_ : Unit) :
    (M × Hash) ⊕ (Z × C) → PMF (((K × R) ⊕ K) × Unit)
  | .inl q => PMF.pure (.inl (g q), ())
  | .inr q => PMF.pure (.inr (j q), ())

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq C] in
@[simp] theorem run_gQ_fixed (g : M × Hash → K × R) (j : Z × C → K) (q : M × Hash) :
    OracleAdv.run (fixedRO2 g j) (gQ (Z := Z) (C := C) q) () = PMF.pure (g q, ()) := by
  simp [gQ, fixedRO2, OracleAdv.run_query, PMF.pure_bind]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [DecidableEq C] in
@[simp] theorem run_jQ_fixed (g : M × Hash → K × R) (j : Z × C → K) (q : Z × C) :
    OracleAdv.run (fixedRO2 g j) (jQ (M := M) (Hash := Hash) (R := R) q) () =
      PMF.pure (j q, ()) := by
  simp [jQ, fixedRO2, OracleAdv.run_query, PMF.pure_bind]

/-- Encapsulation against fixed oracles: a uniform `m` gives the key
`(g (m, hpk pk)).1` and the ciphertext `P.enc pk m (g (m, hpk pk)).2`. -/
theorem run_encaps_fixed (P : Scheme PK SK M C R) (hpk : PK → Hash) (g : M × Hash → K × R)
    (j : Z × C → K) (pk : PK) :
    OracleAdv.run (fixedRO2 g j) ((fips203 P hpk).encaps pk) () =
      (PMF.uniformFintype M).map fun m =>
        (((g (m, hpk pk)).1, P.enc pk m (g (m, hpk pk)).2), ()) := by
  simp [fips203, OracleAdv.run_rand, OracleAdv.run_bind, PMF.map, PMF.pure_bind,
    Function.comp_def]

/-- Decapsulation of the encapsulation of `m` against fixed oracles returns the
encapsulated key when `P` decrypts the ciphertext to `m`. -/
theorem decaps_encaps_fixed (P : Scheme PK SK M C R) (hpk : PK → Hash) (g : M × Hash → K × R)
    (j : Z × C → K) (pk : PK) (sk : SK) (z : Z) (m : M)
    (hdec : P.dec sk (P.enc pk m (g (m, hpk pk)).2) = some m) :
    OracleAdv.run (fixedRO2 g j)
        ((fips203 P hpk).decaps (sk, pk, z) (P.enc pk m (g (m, hpk pk)).2)) () =
      PMF.pure (some (g (m, hpk pk)).1, ()) := by
  simp [fips203, hdec, OracleAdv.run_bind, PMF.pure_bind]

/-- Decapsulation of the encapsulation of `m` against the lazily sampled oracles
returns the encapsulated key and leaves the tables unchanged, when the table of `G`
holds the value `(K, r)` at `(m, hpk pk)` and `P` decrypts the ciphertext to `m`. -/
theorem decaps_encaps_table [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R]
    [Fintype K] (P : Scheme PK SK M C R) (hpk : PK → Hash) (pk : PK) (sk : SK) (z : Z) (m : M)
    (k : K) (r : R) (T : (M × Hash → Option (K × R)) × (Z × C → Option K))
    (hT : T.1 (m, hpk pk) = some (k, r)) (hdec : P.dec sk (P.enc pk m r) = some m) :
    OracleAdv.run ro2Oracle ((fips203 P hpk).decaps (sk, pk, z) (P.enc pk m r)) T =
      PMF.pure (some k, T) := by
  simp [fips203, hdec, gQ, OracleAdv.run_bind, OracleAdv.run_query, ro2Oracle, roOracle, hT,
    PMF.pure_bind, PMF.map]

/-! ## The T/U factoring -/

/-- The transform `T[P, f]` with a derandomiser `f : PK → M → R` depending on the public
key, as a public-key encryption scheme without coins whose secret key includes the
public key. -/
noncomputable def tKeyed (P : Scheme PK SK M C R) (f : PK → M → R) :
    Scheme PK (PK × SK) M C Unit where
  keygen := P.keygen.map fun ks => (ks.1, (ks.1, ks.2))
  enc pk m _ := P.enc pk m (f pk m)
  dec sk c := match P.dec sk.2 c with
    | none => none
    | some m => if P.enc sk.1 m (f sk.1 m) = c then some m else none

/-- The transform `U[Q, kdf, J]` of a coin-free scheme `Q`: the key of `m` is
`kdf pk m`, and rejection returns `J(z, c)` for a seed `z` drawn at key generation. -/
noncomputable def uKeyed (Q : Scheme PK SK M C Unit) (kdf : PK → M → K) :
    KEM.Games.ROMScheme PK (SK × PK × Z) K C (Z × C) K where
  keygen := Q.keygen.bind fun ks =>
    (PMF.uniformFintype Z).map fun z => (ks.1, (ks.2, ks.1, z))
  encaps pk := .rand (PMF.uniformFintype M) fun m => .ret (kdf pk m, Q.enc pk m ())
  decaps sk c := match Q.dec sk.1 c with
    | none => .query (sk.2.2, c) fun k => .ret (some k)
    | some m => .ret (some (kdf sk.2.1 m))

/-- The oracle `J` as a fixed function `j`, without state. -/
noncomputable def fixedJ (j : Z × C → K) (_ : Unit) (q : Z × C) : PMF (K × Unit) :=
  PMF.pure (j q, ())

/-- The factoring `fips203 P hpk = uKeyed[tKeyed[P, G'], J]` with
`G' pk m = (G (m, hpk pk)).2` and key derivation `(G (m, hpk pk)).1`, for fixed oracle
functions `g` and `j`: the two KEMs have the same key-generation distribution, the same
encapsulation, and the same decapsulation on every key and ciphertext. -/
def IsTUFactoring (P : Scheme PK SK M C R) (hpk : PK → Hash) : Prop :=
  ∀ (g : M × Hash → K × R) (j : Z × C → K),
    let U : KEM.Games.ROMScheme PK ((PK × SK) × PK × Z) K C (Z × C) K :=
      uKeyed (tKeyed P fun pk m => (g (m, hpk pk)).2) fun pk m => (g (m, hpk pk)).1
    (fips203 (K := K) P hpk).keygen.map (fun ks => (ks.1, (ks.2.1, ks.2.2.2))) =
        U.keygen.map (fun ks => (ks.1, (ks.2.1.2, ks.2.2.2))) ∧
      (∀ pk, OracleAdv.run (fixedRO2 g j) ((fips203 P hpk).encaps pk) () =
        OracleAdv.run (fixedJ j) (U.encaps pk) ()) ∧
      ∀ pk sk z c, OracleAdv.run (fixedRO2 g j) ((fips203 P hpk).decaps (sk, pk, z) c) () =
        OracleAdv.run (fixedJ j) (U.decaps ((pk, sk), pk, z) c) ()

/-- `fips203 P hpk` factors as `uKeyed[tKeyed[P, G'], J]`. -/
theorem isTUFactoring (P : Scheme PK SK M C R) (hpk : PK → Hash) :
    IsTUFactoring (K := K) (Z := Z) P hpk := by
  intro g j
  refine ⟨?_, ?_, ?_⟩
  · simp [fips203, uKeyed, tKeyed, PMF.map_bind, PMF.map_comp, Function.comp_def]
  · intro pk
    simp [fips203, uKeyed, tKeyed, OracleAdv.run_rand, OracleAdv.run_bind, PMF.pure_bind]
  · intro pk sk z c
    simp only [fips203, uKeyed, tKeyed]
    rcases hd : P.dec sk c with _ | m
    · simp [OracleAdv.run_bind, OracleAdv.run_query, fixedJ, PMF.pure_bind]
    · by_cases he : P.enc pk m (g (m, hpk pk)).2 = c
      · simp [he, OracleAdv.run_bind, PMF.pure_bind]
      · simp [he, OracleAdv.run_bind, OracleAdv.run_query, fixedJ, PMF.pure_bind]

end CatCrypt.Crypto.KEM.FIPS203

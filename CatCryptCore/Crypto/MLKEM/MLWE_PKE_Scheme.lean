/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FOTransform
public import CatCryptCore.Crypto.MLKEM.MLWE_PKE_Basic

/-!
# The basic MLWE PKE as a `PKE.Games.Scheme`

`MLWE_PKE_Basic` describes the base public-key encryption scheme of ML-KEM with
sub-distributions: key generation `kg` samples the matrix uniformly and the secret
and error vectors from `dshort_vec`; encryption `enc` samples `r ← dshort_vec`,
`e1 ← dshort_vec2` and `e2 ← dshort_R`. A `PKE.Games.Scheme` has a total key
distribution and
deterministic encryption over uniform coins. FIPS 203 derives every noise sample
from a uniform seed through a deterministic sampler (`SamplePolyCBD ∘ PRF`), so the
scheme is presented here with explicit seed types and samplers: `Params` extends
`MLWE_PKE_Basic.Params` by a seed type `Seed` with a sampler `sampleShort` for the
encryption noise `(r, e1, e2)` and a seed type `KeySeed` with a sampler `sampleKey`
for the key-generation noise `(s, e)`, together with the hypotheses that the
pushforward of the uniform seed distribution along each sampler is the corresponding
product of short distributions.

## The model

* The fields `sampleShort_eq` and `sampleKey_eq` of `Params` state that a uniform
  seed pushed through the sampler has exactly the short distribution of the scheme;
  in particular `dshort_vec`, `dshort_vec2` and `dshort_R` are total. The samplers
  `sampleShort` and `sampleKey` are parameters of `Params`.
* `toScheme P` is the base PKE `MLWE_PKE_Basic`. The Fujisaki–Okamoto theorem
  `KEM.FOTransform.foNotBot_indcca_of_indcpa` applies to `toScheme P`, giving a bound
  on `foNotBot (toScheme P)` in terms of the IND-CPA advantage of the base PKE,
  which `indcpaGame_eq` and `indcpaAdvantage_eq_absDiff` relate to the
  sub-distribution games of `MLWE_PKE_Basic`.

## Main definitions

* `Params` — `MLWE_PKE_Basic.Params` with seeded noise samplers
* `toScheme P` — the base PKE as a `PKE.Games.Scheme` with coins `P.Seed`

## Main results

* `keygen_eq`, `encDist_eq`, `dec_eq` — the algorithms of `toScheme P` are those of
  `MLWE_PKE_Basic`
* `indcpaGame_eq` — the IND-CPA game of `toScheme P` is the sub-distribution IND-CPA
  game of `MLWE_PKE_Basic` with a stateful adversary
* `advantage_pmfGame_eq_absDiff`, `indcpaAdvantage_eq_absDiff` — the IND-CPA
  advantage is the absolute difference of the two `true`-probabilities
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MLWE_PKE_Scheme

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.PKE.Games
open CatCrypt.Crypto.KEM.FOTransform (prTrue_pmfGame_true)
open scoped ENNReal

/-- `MLWE_PKE_Basic.Params` with a seed type and a deterministic sampler for the
encryption noise `(r, e1, e2)` and for the key-generation noise `(s, e)`. The
pushforward of the uniform seed along each sampler is the product of the short
distributions of the scheme. -/
structure Params extends toBasic : MLWE_PKE_Basic.Params where
  /-- Seed type of the encryption noise. -/
  Seed : Type
  [finSeed : Fintype Seed]
  [neSeed : Nonempty Seed]
  /-- The encryption noise `(r, e1, e2)` derived from a seed. -/
  sampleShort : Seed → Vec × Vec × R
  /-- A uniform seed pushed through `sampleShort` has the distribution of
  `r ← dshort_vec`, `e1 ← dshort_vec2`, `e2 ← dshort_R`. -/
  sampleShort_eq : (do let sd ← SDistr.uniform Seed; SDistr.pure (sampleShort sd)) =
    (do let r ← dshort_vec; let e1 ← dshort_vec2; let e2 ← dshort_R; SDistr.pure (r, e1, e2))
  /-- Seed type of the key-generation noise. -/
  KeySeed : Type
  [finKeySeed : Fintype KeySeed]
  [neKeySeed : Nonempty KeySeed]
  /-- The key-generation noise `(s, e)` derived from a seed. -/
  sampleKey : KeySeed → Vec × Vec
  /-- A uniform seed pushed through `sampleKey` has the distribution of
  `s, e ← dshort_vec`. -/
  sampleKey_eq : (do let sd ← SDistr.uniform KeySeed; SDistr.pure (sampleKey sd)) =
    (do let s ← dshort_vec; let e ← dshort_vec; SDistr.pure (s, e))

attribute [instance] Params.finSeed Params.neSeed Params.finKeySeed Params.neKeySeed

variable (P : Params)

/-! ## The scheme -/

/-- The base PKE of `P` as a scheme with uniform coins `P.Seed`: key generation
samples the matrix and a key seed uniformly, encryption derives its noise from the
coins by `sampleShort`, and decryption is `m_decode (v - s·u)`. -/
noncomputable def toScheme :
    Scheme (MLWE_PKE_Basic.PK P.toBasic) (MLWE_PKE_Basic.SK P.toBasic) P.PT
      (MLWE_PKE_Basic.CT P.toBasic) P.Seed where
  keygen := (PMF.uniformOfFintype P.Mat).bind fun A =>
    (PMF.uniformOfFintype P.KeySeed).map fun ks =>
      ((A, P.vec_add (P.mat_vec_mul A (P.sampleKey ks).1) (P.sampleKey ks).2), (P.sampleKey ks).1)
  enc pk m sd :=
    (P.vec_add (P.mat_vec_mul (P.mat_transpose pk.1) (P.sampleShort sd).1) (P.sampleShort sd).2.1,
     P.ring_add (P.ring_add (P.vec_dot pk.2 (P.sampleShort sd).1) (P.sampleShort sd).2.2)
       (P.m_encode m))
  dec sk c := some (P.m_decode (P.ring_sub c.2 (P.vec_dot sk c.1)))

/-! ## Bridge lemmas between `PMF` and `SDistr` -/

/-- `SDistr.bind` of a total distribution is `PMF.bind`. -/
theorem sdistr_bind_map_some {α β : Type} (p : PMF α) (f : α → SDistr β) :
    SDistr.bind (p.map some) f = p.bind f := by
  unfold SDistr.bind
  rw [PMF.bind_map]
  rfl

/-- The `true`-probability of a total distribution. -/
theorem prTrue_map_some (p : PMF Bool) : prTrue (p.map some) = p true := by
  (unfold CatCrypt.Crypto.MLKEM.prTrue; simp_all [PMF.map_apply])

/-- `Advantage` between two heap-independent games is the absolute difference of
their `true`-probabilities. -/
theorem advantage_pmfGame_eq_absDiff (p q : PMF Bool) :
    Advantage (liftPMF p) (liftPMF q) = absDiff (p true) (q true) := by
  simp only [Advantage, prTrue_pmfGame_true]
  rfl

/-! ## The algorithms of `toScheme P` are those of `MLWE_PKE_Basic` -/

theorem keygen_eq : (toScheme P).keygen.map some = MLWE_PKE_Basic.kg P.toBasic := by
  have h := P.sampleKey_eq
  simp only [SDistr.monad_bind_eq] at h
  simp only [MLWE_PKE_Basic.kg, SDistr.monad_bind_eq, toScheme, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  have hkg : ∀ A : P.Mat,
      SDistr.bind P.dshort_vec (fun s => SDistr.bind P.dshort_vec fun e =>
        SDistr.pure ((A, P.vec_add (P.mat_vec_mul A s) e), s)) =
      SDistr.bind (SDistr.bind P.dshort_vec fun s => SDistr.bind P.dshort_vec fun e =>
        SDistr.pure (s, e)) fun se =>
        SDistr.pure ((A, P.vec_add (P.mat_vec_mul A se.1) se.2), se.1) := by
    intro A
    simp only [SDistr.bind_assoc, SDistr.pure_bind]
  simp only [hkg, ← h, SDistr.uniform, sdistr_bind_map_some]
  simp only [SDistr.bind, PMF.bind_bind, SDistr.pure, PMF.pure_bind]
  rfl

theorem encDist_eq (pk : MLWE_PKE_Basic.PK P.toBasic) (m : P.PT) :
    ((toScheme P).encDist pk m).map some = MLWE_PKE_Basic.enc P.toBasic pk m := by
  obtain ⟨A, t⟩ := pk
  have h := P.sampleShort_eq
  simp only [SDistr.monad_bind_eq] at h
  simp only [MLWE_PKE_Basic.enc, SDistr.monad_bind_eq, Scheme.encDist, toScheme, PMF.map_comp,
    Function.comp_def]
  have henc :
      SDistr.bind P.dshort_vec (fun r => SDistr.bind P.dshort_vec2 fun e1 =>
        SDistr.bind P.dshort_R fun e2 =>
          SDistr.pure (P.vec_add (P.mat_vec_mul (P.mat_transpose A) r) e1,
            P.ring_add (P.ring_add (P.vec_dot t r) e2) (P.m_encode m))) =
      SDistr.bind (SDistr.bind P.dshort_vec fun r => SDistr.bind P.dshort_vec2 fun e1 =>
        SDistr.bind P.dshort_R fun e2 => SDistr.pure (r, e1, e2)) fun x =>
        SDistr.pure (P.vec_add (P.mat_vec_mul (P.mat_transpose A) x.1) x.2.1,
          P.ring_add (P.ring_add (P.vec_dot t x.1) x.2.2) (P.m_encode m)) := by
    simp only [SDistr.bind_assoc, SDistr.pure_bind]
  rw [henc, ← h, SDistr.bind_assoc]
  simp only [SDistr.pure_bind, SDistr.uniform, sdistr_bind_map_some]
  rfl

theorem dec_eq (sk : MLWE_PKE_Basic.SK P.toBasic) (c : MLWE_PKE_Basic.CT P.toBasic) :
    SDistr.pure ((toScheme P).dec sk c) = MLWE_PKE_Basic.dec P.toBasic sk c := rfl

/-! ## The IND-CPA game -/

/-- The IND-CPA game of `toScheme P` against `A` is the IND-CPA game of
`MLWE_PKE_Basic` with the stateful adversary `A` lifted to sub-distributions. -/
theorem indcpaGame_eq
    (A : INDCPAAdversary (MLWE_PKE_Basic.PK P.toBasic) P.PT (MLWE_PKE_Basic.CT P.toBasic))
    (b : Bool) :
    (indcpaGame (toScheme P) A b).map some =
      ((do
        let (pk, _sk) ← MLWE_PKE_Basic.kg P.toBasic
        let x ← (A.choose pk).map some
        let c ← MLWE_PKE_Basic.enc P.toBasic pk (if b then x.1 else x.2.1)
        (A.guess x.2.2 c).map some) : SDistr Bool) := by
  simp only [SDistr.monad_bind_eq, ← keygen_eq, ← encDist_eq, sdistr_bind_map_some, indcpaGame,
    PMF.map_bind]

/-- The IND-CPA advantage of `toScheme P` is the absolute difference of the
`true`-probabilities of the two challenge bits. -/
theorem indcpaAdvantage_eq_absDiff
    (A : INDCPAAdversary (MLWE_PKE_Basic.PK P.toBasic) P.PT (MLWE_PKE_Basic.CT P.toBasic)) :
    indcpaAdvantage (toScheme P) A =
      absDiff (CatCrypt.Crypto.prTrue (liftPMF (indcpaGame (toScheme P) A true)) Heap.empty)
        (CatCrypt.Crypto.prTrue (liftPMF (indcpaGame (toScheme P) A false)) Heap.empty) := rfl

/-- The IND-CPA advantage of `toScheme P` in the vocabulary of `MLWE_PKE_Basic`: the
absolute difference of the `true`-probabilities of the sub-distribution games. -/
theorem indcpaAdvantage_eq_absDiff_prTrue
    (A : INDCPAAdversary (MLWE_PKE_Basic.PK P.toBasic) P.PT (MLWE_PKE_Basic.CT P.toBasic)) :
    indcpaAdvantage (toScheme P) A =
      absDiff (prTrue ((indcpaGame (toScheme P) A true).map some))
        (prTrue ((indcpaGame (toScheme P) A false).map some)) := by
  rw [indcpaAdvantage, advantage_pmfGame_eq_absDiff, prTrue_map_some, prTrue_map_some]

end CatCrypt.Crypto.MLKEM.MLWE_PKE_Scheme

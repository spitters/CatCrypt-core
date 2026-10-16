/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Tactics.AutoHopRegistry
public meta import CatCryptCore.Tactics.AutoHopRegistry

/-!
# Key encapsulation: security games with public keys and decapsulation oracles

A key encapsulation mechanism `Scheme PK SK K C` has probabilistic key generation
and encapsulation and deterministic decapsulation `decaps sk c : Option K`. A KEM
in the random-oracle model, `ROMScheme PK SK K C D H`, has encapsulation and
decapsulation given as oracle programs querying a random oracle `D → H`; the
challenger samples the oracle lazily with a table `D → Option H`.

The IND-CPA and IND-CCA games follow Hofheinz–Hövelmanns–Kiltz (TCC 2017),
Figure 4, in real-or-random form: the adversary receives the public key, the
challenge encapsulation `c*` and either the encapsulated key (`b = true`) or an
independent uniform key (`b = false`). In the IND-CCA games the adversary has a
decapsulation oracle, which the challenger answers with `none` on `c*`; in the
random-oracle game it also has the random oracle, shared with the challenger's
encapsulation and decapsulation. The advantage is the distance between the two
values of `b`, which is twice `|Pr[b' = b] − 1/2|`.

## Main definitions

* `Scheme`, `Scheme.corrErr`
* `indcpaGame`, `indcpaAdvantage`
* `INDCCAAdversary`, `decapsOracle`, `indccaGame`, `indccaAdvantage`
* `ROMScheme`, `ROMINDCCAAdversary`, `romCCAOracle`, `romINDCCAGame`,
  `romINDCCAAdvantage`
* `ro2Oracle`, `ROM2Scheme`, `ROM2INDCCAAdversary`, `rom2CCAOracle`, `rom2INDCCAGame`,
  `rom2INDCCAAdvantage` — the same with two independent random oracles

## References

* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the
  Fujisaki–Okamoto Transformation*, TCC 2017, ePrint 2017/604, Section 2.2.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.Games

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

/-- A key encapsulation mechanism with public keys `PK`, secret keys `SK`, keys `K`
and encapsulations `C`. -/
structure Scheme (PK SK K C : Type) where
  /-- Key generation, returning `(pk, sk)`. -/
  keygen : PMF (PK × SK)
  /-- Encapsulation, returning `(key, encapsulation)`. -/
  encaps : PK → PMF (K × C)
  /-- Decapsulation; `none` rejects. -/
  decaps : SK → C → Option K

variable {PK SK K C : Type}

/-- The probability that decapsulation of a fresh encapsulation does not return
the encapsulated key. -/
noncomputable def Scheme.corrErr [DecidableEq K] (S : Scheme PK SK K C) : ℝ≥0∞ :=
  (S.keygen.bind fun ks => (S.encaps ks.1).map fun x =>
    decide (S.decaps ks.2 x.2 ≠ some x.1)) true

section Standard

variable [Fintype K] [Nonempty K] (S : Scheme PK SK K C)

/-- The IND-CPA experiment in real-or-random form. -/
noncomputable def indcpaGame (A : PK → C → K → PMF Bool) (b : Bool) : PMF Bool :=
  S.keygen.bind fun ks => (S.encaps ks.1).bind fun x =>
    (PMF.uniformOfFintype K).bind fun k₁ => A ks.1 x.2 (if b then x.1 else k₁)

/-- The IND-CPA advantage: the `Advantage` between the games of the two challenge bits.
Registered with `@[hop_metric]`, which unfolds it to that `Advantage`. -/
@[hop_metric] noncomputable def indcpaAdvantage (A : PK → C → K → PMF Bool) : ℝ≥0∞ :=
  Advantage (pmfGame (indcpaGame S A true)) (pmfGame (indcpaGame S A false))

/-- The decapsulation oracle for `sk`, answering `none` on the challenge `c*`. -/
noncomputable def decapsOracle [DecidableEq C] (sk : SK) (cstar : C) (_ : Unit) (c : C) :
    PMF (Option K × Unit) :=
  PMF.pure (if c = cstar then none else S.decaps sk c, ())

variable (PK K C) in
/-- An IND-CCA adversary with at most `q` decapsulation queries. -/
structure INDCCAAdversary (q : ℕ) : Type 1 where
  /-- The adversary on the public key, the challenge and the key. -/
  run : PK → C → K → OracleAdv C (Option K) Bool
  /-- The query bound. -/
  isQueryBound : ∀ pk c k, (run pk c k).IsQueryBound q

/-- The IND-CCA experiment in real-or-random form. -/
noncomputable def indccaGame [DecidableEq C] {q : ℕ} (A : INDCCAAdversary PK K C q) (b : Bool) :
    PMF Bool :=
  S.keygen.bind fun ks => (S.encaps ks.1).bind fun x =>
    (PMF.uniformOfFintype K).bind fun k₁ =>
      (OracleAdv.run (decapsOracle S ks.2 x.2) (A.run ks.1 x.2 (if b then x.1 else k₁)) ()).map
        Prod.fst

/-- The IND-CCA advantage. -/
noncomputable def indccaAdvantage [DecidableEq C] {q : ℕ} (A : INDCCAAdversary PK K C q) :
    ℝ≥0∞ :=
  Advantage (pmfGame (indccaGame S A true)) (pmfGame (indccaGame S A false))

end Standard

/-! ## Random-oracle model -/

section ROM

variable {D H : Type} [DecidableEq D] [Fintype H] [Nonempty H]

variable (PK SK K C D H) in
/-- A KEM in the random-oracle model with oracle `D → H`: encapsulation and
decapsulation are oracle programs. -/
structure ROMScheme where
  /-- Key generation, returning `(pk, sk)`. -/
  keygen : PMF (PK × SK)
  /-- Encapsulation, returning `(key, encapsulation)`. -/
  encaps : PK → OracleAdv D H (K × C)
  /-- Decapsulation; `none` rejects. -/
  decaps : SK → C → OracleAdv D H (Option K)

variable [Fintype K] [Nonempty K] [DecidableEq C]

/-- The oracle of the IND-CCA game in the random-oracle model for secret key `sk`
and challenge `c*`, on the random-oracle table: `inl d` is a random-oracle query,
`inr c` a decapsulation query, answered `none` on `c*` and otherwise by running
decapsulation against the shared table. -/
noncomputable def romCCAOracle (S : ROMScheme PK SK K C D H) (sk : SK) (cstar : C)
    (T : D → Option H) : D ⊕ C → PMF ((H ⊕ Option K) × (D → Option H))
  | .inl d => (roOracle T d).map fun x => (.inl x.1, x.2)
  | .inr c => if c = cstar then PMF.pure (.inr none, T) else
      (OracleAdv.run roOracle (S.decaps sk c) T).map fun x => (.inr x.1, x.2)

variable (PK K C D H) in
/-- An IND-CCA adversary in the random-oracle model with at most `qH` random-oracle
queries and `qD` decapsulation queries. -/
structure ROMINDCCAAdversary (qH qD : ℕ) : Type 1 where
  /-- The adversary on the public key, the challenge and the key. -/
  run : PK → C → K → OracleAdv (D ⊕ C) (H ⊕ Option K) Bool
  /-- The random-oracle query bound. -/
  isQueryBoundH : ∀ pk c k, (run pk c k).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qH
  /-- The decapsulation query bound. -/
  isQueryBoundD : ∀ pk c k, (run pk c k).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qD

/-- The IND-CCA experiment in the random-oracle model in real-or-random form: the
challenger generates keys, runs encapsulation against the empty table, and runs
the adversary against `romCCAOracle` from the resulting table. -/
noncomputable def romINDCCAGame (S : ROMScheme PK SK K C D H) {qH qD : ℕ}
    (A : ROMINDCCAAdversary PK K C D H qH qD) (b : Bool) : PMF Bool :=
  S.keygen.bind fun ks => (OracleAdv.run roOracle (S.encaps ks.1) emptyTable).bind fun x =>
    (PMF.uniformOfFintype K).bind fun k₁ =>
      (OracleAdv.run (romCCAOracle S ks.2 x.1.2) (A.run ks.1 x.1.2 (if b then x.1.1 else k₁))
        x.2).map Prod.fst

/-- The IND-CCA advantage in the random-oracle model. -/
noncomputable def romINDCCAAdvantage (S : ROMScheme PK SK K C D H) {qH qD : ℕ}
    (A : ROMINDCCAAdversary PK K C D H qH qD) : ℝ≥0∞ :=
  Advantage (pmfGame (romINDCCAGame S A true)) (pmfGame (romINDCCAGame S A false))

end ROM

/-! ## Two random oracles -/

section ROM2

variable {DG HG DH HH : Type} [DecidableEq DG] [Fintype HG] [Nonempty HG]
  [DecidableEq DH] [Fintype HH] [Nonempty HH]

/-- Two independent lazily sampled random oracles `G : DG → HG` and `H : DH → HH` on a
pair of tables. -/
noncomputable def ro2Oracle (T : (DG → Option HG) × (DH → Option HH)) :
    DG ⊕ DH → PMF ((HG ⊕ HH) × ((DG → Option HG) × (DH → Option HH)))
  | .inl d => (roOracle T.1 d).map fun x => (.inl x.1, (x.2, T.2))
  | .inr d => (roOracle T.2 d).map fun x => (.inr x.1, (T.1, x.2))

variable (PK SK K C DG HG DH HH) in
/-- A KEM in the random-oracle model with two random oracles `G : DG → HG` and
`H : DH → HH`: encapsulation and decapsulation are oracle programs. -/
structure ROM2Scheme where
  /-- Key generation, returning `(pk, sk)`. -/
  keygen : PMF (PK × SK)
  /-- Encapsulation, returning `(key, encapsulation)`. -/
  encaps : PK → OracleAdv (DG ⊕ DH) (HG ⊕ HH) (K × C)
  /-- Decapsulation; `none` rejects. -/
  decaps : SK → C → OracleAdv (DG ⊕ DH) (HG ⊕ HH) (Option K)

variable [Fintype K] [Nonempty K] [DecidableEq C]

/-- The oracle of the IND-CCA game with two random oracles for secret key `sk` and
challenge `c*`: `inl d` is a random-oracle query and `inr c` a decapsulation query,
answered `none` on `c*` and otherwise by running decapsulation against the shared
tables. -/
noncomputable def rom2CCAOracle (S : ROM2Scheme PK SK K C DG HG DH HH) (sk : SK) (cstar : C)
    (T : (DG → Option HG) × (DH → Option HH)) :
    (DG ⊕ DH) ⊕ C → PMF (((HG ⊕ HH) ⊕ Option K) × ((DG → Option HG) × (DH → Option HH)))
  | .inl d => (ro2Oracle T d).map fun x => (.inl x.1, x.2)
  | .inr c => if c = cstar then PMF.pure (.inr none, T) else
      (OracleAdv.run ro2Oracle (S.decaps sk c) T).map fun x => (.inr x.1, x.2)

variable (PK K C DG HG DH HH) in
/-- An IND-CCA adversary with two random oracles, asking at most `qRO` random-oracle
queries (to either oracle) and `qD` decapsulation queries. -/
structure ROM2INDCCAAdversary (qRO qD : ℕ) : Type 1 where
  /-- The adversary on the public key, the challenge and the key. -/
  run : PK → C → K → OracleAdv ((DG ⊕ DH) ⊕ C) ((HG ⊕ HH) ⊕ Option K) Bool
  /-- The random-oracle query bound. -/
  isQueryBoundRO : ∀ pk c k,
    (run pk c k).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qRO
  /-- The decapsulation query bound. -/
  isQueryBoundD : ∀ pk c k,
    (run pk c k).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qD

/-- The IND-CCA experiment with two random oracles in real-or-random form. -/
noncomputable def rom2INDCCAGame (S : ROM2Scheme PK SK K C DG HG DH HH) {qRO qD : ℕ}
    (A : ROM2INDCCAAdversary PK K C DG HG DH HH qRO qD) (b : Bool) : PMF Bool :=
  S.keygen.bind fun ks =>
    (OracleAdv.run ro2Oracle (S.encaps ks.1) (emptyTable, emptyTable)).bind fun x =>
      (PMF.uniformOfFintype K).bind fun k₁ =>
        (OracleAdv.run (rom2CCAOracle S ks.2 x.1.2) (A.run ks.1 x.1.2 (if b then x.1.1 else k₁))
          x.2).map Prod.fst

/-- The IND-CCA advantage with two random oracles. -/
noncomputable def rom2INDCCAAdvantage (S : ROM2Scheme PK SK K C DG HG DH HH) {qRO qD : ℕ}
    (A : ROM2INDCCAAdversary PK K C DG HG DH HH qRO qD) : ℝ≥0∞ :=
  Advantage (pmfGame (rom2INDCCAGame S A true)) (pmfGame (rom2INDCCAGame S A false))

end ROM2

end CatCrypt.Crypto.KEM.Games

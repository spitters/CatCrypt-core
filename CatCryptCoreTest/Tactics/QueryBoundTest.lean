/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.SignerHybrid
public import CatCryptCore.Crypto.KEM.FIPS203Security
public import CatCryptCore.Crypto.KEM.FOTransformTimed
public import CatCryptCore.Crypto.OracleQueryVec
public import CatCryptCore.Tactics.QueryBound

/-!
# Tests of `query_bound`

The goals are the hand-proved query bounds of `FOTransform`, `FOTransformU`, `FIPS203Security` and
`SignerHybrid`, restated. `query_bound only [names]` is used so that a test does not find the
theorem it restates: the names listed are the bounds of the callees. A `fail_if_success` records a
goal that the variant it runs does not close.
-/

set_option autoImplicit false

section FOTransform

open CatCrypt.Crypto CatCrypt.Crypto.KEM.FOTransform CatCrypt.Crypto.KEM.FOTransformU
open CatCrypt.Crypto.KEM.Games

variable {PK SK M C R K : Type} [Fintype R] [Nonempty R] [Fintype M] [Nonempty M]
  [DecidableEq M] [DecidableEq C] [Fintype K] [Nonempty K]

/-- The field `isQueryBoundH` of `absorb`. -/
example {qRO qD : ℕ} (f : M → R) (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD)
    (pk : PK) (c : C) (k : K) :
    ((OracleAdv.simulate (absImpl f) (B.run pk c k) ()).bind fun x => .ret x.1).IsQueryBoundBy
      (Sum.elim (fun _ => 1) fun _ => 0) qRO := by
  query_bound only

/-- The field `isQueryBoundD` of `absorb`. -/
example {qRO qD : ℕ} (f : M → R) (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD)
    (pk : PK) (c : C) (k : K) :
    ((OracleAdv.simulate (absImpl f) (B.run pk c k) ()).bind fun x => .ret x.1).IsQueryBoundBy
      (Sum.elim (fun _ => 0) fun _ => 1) qD := by
  query_bound only

/-- `isQueryBoundBy_simImplFO`. -/
example (cost : M ⊕ (M × C) → ℕ) (hc₁ : ∀ m, cost (.inl m) ≤ 1)
    (hc₂ : ∀ q, cost (.inr q) ≤ 1) (cstar : C) (kstar : K) (st : SimState M C K)
    (d : (M ⊕ (M × C)) ⊕ C) :
    (simImplFO (R := R) cstar kstar st d).IsQueryBoundBy cost
      (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  query_bound only [isQueryBoundBy_liftP, isQueryBound_simImpl]

/-- `isQueryBoundBy_uRedRun` from the bound of its simulator. -/
example {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD)
    (cost : M ⊕ (M × C) → ℕ) (hc₁ : ∀ m, cost (.inl m) ≤ 1) (hc₂ : ∀ q, cost (.inr q) ≤ 1)
    (pk : PK) (c : C) : (uRedRun B pk c).IsQueryBoundBy cost qRO := by
  query_bound only [isQueryBoundBy_simImplFO]

/-- `isQueryBoundBy_uRedRun` through the simulator, one level down. -/
example {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD)
    (cost : M ⊕ (M × C) → ℕ) (hc₁ : ∀ m, cost (.inl m) ≤ 1) (hc₂ : ∀ q, cost (.inr q) ≤ 1)
    (pk : PK) (c : C) : (uRedRun B pk c).IsQueryBoundBy cost qRO := by
  query_bound only [isQueryBoundBy_liftP, isQueryBound_simImpl]

/-- The field `isQueryBoundG` of `uRedROM`. -/
example {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (pk : PK) (c : C) :
    (uRedRun B pk c).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qRO := by
  query_bound only [isQueryBoundBy_uRedRun]

/-- The field `isQueryBoundP` of `uRedROM`. -/
example {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (pk : PK) (c : C) :
    (uRedRun B pk c).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qRO := by
  query_bound only [isQueryBoundBy_uRedRun]

/-- The total count of `uRedROM`. -/
example {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (pk : PK) (c : C) :
    ((uRedROM B).run pk c).IsQueryBoundBy (fun _ => 1) qRO := by
  query_bound only [isQueryBoundBy_uRedRun]

/-- `isQueryBoundBy_liftP` needs an induction: the tactic names the recursive definition. -/
example {α : Type} (cost : M ⊕ (M × C) → ℕ) (hc : ∀ q, cost (.inr q) ≤ 1)
    {A : OracleAdv (M × C) Bool α} {n : ℕ} (hA : A.IsQueryBound n) :
    (liftP (R := R) A).IsQueryBoundBy cost n := by
  fail_if_success query_bound only
  induction A generalizing n with
  | ret a => query_bound only
  | rand p k ih => query_bound only
  | query q k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n => query_bound only

/-- `isQueryBound_lazyDProg`. -/
example (st : SimState M C K) (c : C) {A : Type} (w : K → A) :
    (lazyDProg st c w).IsQueryBound 0 := by
  query_bound only

/-- `isQueryBound_lazyQProg`. -/
example (st : SimState M C K) (q : M × C) {A : Type} (w : K → A) :
    (lazyQProg st q w).IsQueryBound 0 := by
  query_bound only

/-- `isQueryBound_simImpl`. -/
example (cstar : C) (kstar : K) (st : SimState M C K) (d : (M × C) ⊕ C) :
    (simImpl cstar kstar st d).IsQueryBound (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  query_bound only

/-- The field `isQueryBound` of `uReduction`. -/
example {qH qD : ℕ} (B : ROMINDCCAAdversary PK K C (M × C) K qH qD) (pk : PK) (cstar : C)
    (kstar : K) :
    ((OracleAdv.simulate (simImpl cstar kstar) (B.run pk cstar kstar) SimState.init).bind
      fun x => .ret (x.2.found.getD (Classical.arbitrary M))).IsQueryBound qH := by
  query_bound only

/-- Encapsulation of the transform asks two queries. -/
example (P : PKE.Games.Scheme PK SK M C R) (pk : PK) :
    ((foNotBot (K := K) P).encaps pk).IsQueryBound 2 := by
  query_bound only

/-- Decapsulation of the transform asks two queries. -/
example (P : PKE.Games.Scheme PK SK M C R) (sk : (PK × SK) × M) (c : C) :
    ((foNotBot (K := K) P).decaps sk c).IsQueryBound 2 := by
  query_bound only

/-- Encapsulation asks one query of each random oracle. -/
example (P : PKE.Games.Scheme PK SK M C R) (pk : PK) :
    OracleForking.IsQueryBound₂ ((foNotBot (K := K) P).encaps pk) 1 1 := by
  query_bound only

/-- Decapsulation asks at most one query of each random oracle. -/
example (P : PKE.Games.Scheme PK SK M C R) (sk : (PK × SK) × M) (c : C) :
    OracleForking.IsQueryBound₂ ((foNotBot (K := K) P).decaps sk c) 1 1 := by
  query_bound only

/-- A query to `G` calls only the left oracle. -/
example (m : M) :
    OracleAdv.MayOnlyCall (Set.range Sum.inl) (gQ (C := C) (K := K) (R := R) m) := by
  query_bound only

/-- The erased costed handler has the theorem `simImpl.isQueryBound_erase` in an open namespace.
Its erasure theorem has a map of the result on its left side, so it does not rewrite this goal. -/
example (cstar : C) (kstar : K) (st : SimState M C K) (d : (M × C) ⊕ C) (LDCost : C → ℕ)
    (LQCost : M × C → ℕ) :
    (CatCrypt.Crypto.KEM.FOTransformU.simImpl.timed cstar kstar st d LDCost
      LQCost).2.erase.IsQueryBound (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  fail_if_success query_bound only
  query_bound

/-- The erased form of `liftP.timed` is rewritten along `liftP.erase_timed` to `liftP`. -/
example {α : Type} (cost : M ⊕ (M × C) → ℕ) (hc : ∀ q, cost (.inr q) ≤ 1)
    {A : OracleAdv.Timed (M × C) Bool α} {n : ℕ} (hA : A.erase.IsQueryBound n) :
    (liftP.timed (R := R) A).2.erase.IsQueryBoundBy cost n := by
  query_bound only [isQueryBoundBy_liftP]

end FOTransform

section FIPS203

open CatCrypt.Crypto CatCrypt.Crypto.KEM.FIPS203 CatCrypt.Crypto.PKE.Games
open CatCrypt.Crypto.KEM.Games

variable {PK SK M C R K Hash Z : Type} [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]

/-- `isQueryBoundBy_lazyTab`. -/
example {D' R' I V S A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (cost : D' → ℕ) (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) (n : ℕ) :
    (lazyTab (D' := D') (R' := R') tab i set w).IsQueryBoundBy cost n := by
  query_bound only

/-- `isQueryBound_simImplFix`. -/
example (P : Scheme PK SK M C R) (hpk : PK → Hash) (f : M → R) (pk : PK) (cstar : C)
    (kstar : K) (st : SimStateF M C R K Hash Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (simImplFix P hpk f pk cstar kstar st d).IsQueryBound
      (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  query_bound only

/-- `isQueryBoundBy_simImplF` has a charge hypothesis joining the two oracles, whose witness for
the first query of a path is not in the goal. -/
example (P : Scheme PK SK M C R) (hpk : PK → Hash) (pk : PK) (cstar : C)
    (kstar : K) (cost : M ⊕ (M × C) → ℕ) (hc : ∀ m q, cost (.inl m) + cost (.inr q) ≤ 1)
    (st : SimStateF M C R K Hash Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (simImplF P hpk pk cstar kstar st d).IsQueryBoundBy cost
      (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  query_bound only

/-- `isQueryBoundBy_redRun`. -/
example (P : Scheme PK SK M C R) (hpk : PK → Hash) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD)
    (cost : M ⊕ (M × C) → ℕ) (hc : ∀ m q, cost (.inl m) + cost (.inr q) ≤ 1) (pk : PK) (c : C) :
    (redRun P hpk B pk c).IsQueryBoundBy cost qRO := by
  query_bound only [isQueryBoundBy_simImplF]

/-- `isQueryBoundBy_redROM_total`: per-oracle counts sum to the total count. -/
example (P : Scheme PK SK M C R) (hpk : PK → Hash) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) (pk : PK) (c : C) :
    ((redROM P hpk B).run pk c).IsQueryBoundBy (fun _ => 1) (qRO + qRO) := by
  query_bound only

end FIPS203

section FiatShamir

open CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.OracleForking

variable {G : Protocol}

/-- `isQueryBound_hybDistByOf`. -/
example (sgn : G.SignStep)
    (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool) (D D' : G.Sampler) (k : ℕ)
    {qH qS : ℕ} (A : G.Adversary qH qS) (xw : G.Stmt × G.Wit) :
    (hybDistByOf sgn P D D' k A xw).IsQueryBound 1 := by
  query_bound only [isQueryBound_hybRunOf]

end FiatShamir

section Constructs

open CatCrypt.Crypto

/-- All queries of a list, in order. -/
def queryAll {D R : Type} : List D → OracleAdv D R Unit
  | [] => .ret ()
  | d :: ds => .query d fun _ => queryAll ds

/-- A recursive definition takes an induction, with the hypothesis as a known bound. -/
example {D R : Type} (ds : List D) : (queryAll (R := R) ds).IsQueryBound ds.length := by
  induction ds with
  | nil => query_bound only
  | cons d ds ih => query_bound only

/-- A budget left as a metavariable is assigned by the estimator. -/
example {D R : Type} (d : D) : ∃ n, (OracleAdv.query d fun _ : R =>
    OracleAdv.ret ()).IsQueryBound n := by
  refine ⟨?_, ?_⟩
  swap
  · query_bound only

/-- The estimator takes the maximum over branches. -/
example {D R : Type} (b : Bool) (o : Option D) (d : D) :
    ((if b then OracleAdv.query d fun _ : R => OracleAdv.ret () else OracleAdv.ret ()).bind
      fun _ => (match o with
        | some e => OracleAdv.query e fun _ => OracleAdv.ret ()
        | none => OracleAdv.ret ())).IsQueryBound 2 := by
  query_bound only

/-- `isQueryBound_two_query`. -/
example {D R : Type} (d₁ d₂ : D) (g : R → R → Bool) :
    (OracleAdv.query d₁ fun r₁ => OracleAdv.query d₂ fun r₂ =>
      OracleAdv.ret (g r₁ r₂)).IsQueryBound 2 := by
  query_bound only

end Constructs

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.ROM
public import CatCryptCore.Crypto.FiatShamirROM.SignerHybrid
public import CatCryptCore.Crypto.KEM.FIPS203Security
public import CatCryptCore.Crypto.KEM.FOTransformTimed
public import CatCryptCore.Crypto.OracleQueryVec
public import CatCryptCore.Tactics.QueryBound

/-!
# Tests of `query_bound`

The goals are the hand-proved query bounds of `FOTransform`, `FOTransformU`, `FIPS203Security`,
`SignerHybrid`, `FiatShamirROM.Game` and `PoSNSB.Prob.ROM`, restated. `query_bound only [names]` is
used so that a test does not find the theorem it restates: the names listed are the bounds of the callees. A `fail_if_success` records a
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
    | zero => query_bound only
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

/-- `q` queries, each answered by a program of at most `c` queries, cost `q * c` queries. -/
example {D D' R R' α S : Type} {impl : S → D → OracleAdv D' R' (R × S)} {c q : ℕ}
    (himpl : ∀ s d, (impl s d).IsQueryBound c) {A : OracleAdv D R α} (hA : A.IsQueryBound q)
    (s : S) : (OracleAdv.simulate impl A s).IsQueryBound (q * c) := by
  query_bound only

/-- The rule of `q * c` under a bind, with the budget of the first part proposed. -/
example {D D' R R' α S : Type} {impl : S → D → OracleAdv D' R' (R × S)} {c q : ℕ}
    (himpl : ∀ s d, (impl s d).IsQueryBound c) {A : OracleAdv D R α} (hA : A.IsQueryBound q)
    (s : S) : ((OracleAdv.simulate impl A s).bind fun x => .ret x.1).IsQueryBound (q * c) := by
  query_bound only

/-- A two-kind bound of a hypothesis gives the count of each summand. -/
example {D₁ D₂ R α : Type} {A : OracleAdv (D₁ ⊕ D₂) R α} {a b : ℕ}
    (hA : OracleForking.IsQueryBound₂ A a b) : A.IsQueryBoundBy OracleAdv.chargeInr b := by
  query_bound only

/-- A two-kind bound of a hypothesis gives a two-kind bound of a composition. -/
example {D₁ D₂ R α : Type} {A : ℕ → OracleAdv (D₁ ⊕ D₂) R α} {a b : ℕ}
    (hA : ∀ i, OracleForking.IsQueryBound₂ (A i) a b) (d : D₁) :
    OracleForking.IsQueryBound₂ ((A 0).bind fun _ => .query (.inl d) fun _ => A 1)
      (a + 1 + a) (b + b) := by
  query_bound only

/-- A two-kind bound of a hypothesis gives a total count. -/
example {D₁ D₂ R α : Type} {A : OracleAdv (D₁ ⊕ D₂) R α} {a b : ℕ}
    (hA : OracleForking.IsQueryBound₂ A a b) : A.IsQueryBound (a + b) := by
  query_bound only

/-- A query at the budget `0` refutes its hypothesis. -/
example {D R α : Type} {d : D} {k : R → OracleAdv D R α} {B : OracleAdv D R α}
    (hA : (OracleAdv.query d k).IsQueryBound 0) : B.IsQueryBound 0 := by
  query_bound only

end Constructs

section DefinedCharge

open CatCrypt.Crypto CatCrypt.Crypto.KEM.FIPS203

/-- The charge `keyCost keyJ` of `tsum_bad_le` is a defined function. -/
example {M Hash Z C R' α : Type} (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) R' α) (n : ℕ)
    (hA : A.IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) n) :
    A.IsQueryBoundBy (keyCost keyJ) n := by
  query_bound only

end DefinedCharge

section FiatShamirTwoKind

open CatCrypt.Crypto CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.OracleForking

variable {G : Protocol}

/-- The field `isQueryBound` of an adversary of the Fiat-Shamir game is a two-kind bound. -/
example {qH qS : ℕ} (A : G.Adversary qH qS) (x : G.Stmt) :
    (A.run x).IsQueryBoundBy OracleAdv.chargeInr qS := by
  query_bound only

/-- A listed two-kind bound, whose premise is a two-kind hypothesis. -/
example (x : G.Stmt) (A : OracleAdv G.Query G.Answer G.Forgery) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) :
    (withVerify x A).IsQueryBoundBy OracleAdv.chargeInl (h + G.V) := by
  query_bound only [isQueryBound₂_withVerify]

/-- A listed two-kind bound, summed to a total count. -/
example (x : G.Stmt) (A : OracleAdv G.Query G.Answer G.Forgery) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) :
    (withVerify x A).IsQueryBound (h + G.V + q) := by
  query_bound only [isQueryBound₂_withVerify]

end FiatShamirTwoKind

section HashProgram

open CatCryptCore.Consensus.PoSNSB
open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto CatCrypt.Crypto.Signatures

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
  (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
  (U : (L : Fin n → Option (Fin np)) → Fin np →
    @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  (txSel : Slot → Fin np → Tx) (L : Fin n → Option (Fin np)) (ks : Fin np → PK × SK)
  (A : OAdversary Tx Hash np n Hz PK Sig) (m : ℕ) {qc : ℕ}

/-- A hypothesis over `A.AdvState` applies to an argument of type `A.toAdversary.AdvState`. -/
example (hq : ∀ pub ms sl hist tbl mb st, (A.rcv pub ms sl hist tbl mb st).IsQueryBound qc)
    (p : Fin np) (s : HState IP h0 GB U L A) :
    (hRcv Sch IP h0 GB U L ks A m p s).IsQueryBound (qc + m) := by
  query_bound only [isQueryBound_logBlocks]

/-- A hypothesis over `A.AdvState` applies to an argument of type `A.toAdversary.AdvState`. -/
example (hq : ∀ pub sl hist tbl mb st, (A.bake pub sl hist tbl mb st).IsQueryBound qc)
    (p : Fin np) (s : HState IP h0 GB U L A) :
    (hBake Sch IP h0 GB U txSel L ks A m p s).IsQueryBound (qc + m + 1) := by
  query_bound only [isQueryBound_logBlocks]

/-- The product of a list length and a count, distributed at the cons case. -/
example {S : Type} {step : Fin np → S → OracleAdv (BlockDom Tx Hash np Hz) Hash S} {c : ℕ}
    (h : ∀ p s, (step p s).IsQueryBound c) (l : List (Fin np)) (s : S) :
    (hFold step l s).IsQueryBound (l.length * c) := by
  induction l with
  | nil => query_bound only
  | cons p ps ih => query_bound only

/-- The instance binders of a listed theorem that its tree does not determine are synthesized. -/
example (hb : ∀ pub sl hist tbl mb st, (A.bake pub sl hist tbl mb st).IsQueryBound qc)
    (hr : ∀ pub ms sl hist tbl mb st, (A.rcv pub ms sl hist tbl mb st).IsQueryBound qc)
    (s : HState IP h0 GB U L A) :
    (hPhase Sch IP h0 GB U txSel L ks A m s).IsQueryBound (IP.length * (qc + m + 1)) := by
  query_bound only [isQueryBound_hFold, isQueryBound_hRcv, isQueryBound_hBake]

end HashProgram

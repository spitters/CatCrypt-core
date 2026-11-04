/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FOTransformU
public import CatCryptCore.Crypto.PKE.FOTransformT

/-!
# DHKEM is IND-CCA secure under strong Diffie–Hellman in the random-oracle model

`DHKEM` (RFC 9180, §4.1) over a Diffie–Hellman group `G` with scalars `Sc` and
public elements `P` has key pair `(pub x, x)` for a uniform scalar `x`.
Encapsulation to `pk` samples an ephemeral scalar `y` and returns the encapsulation
`enc = pub y` and the key `KDF(dh y pk, (enc, pk))`; decapsulation of `enc` with `x`
returns `KDF(dh x enc, (enc, pub x))`. The key derivation `KDF` (`ExtractAndExpand`
with `kem_context = enc ‖ pkR`) is a random oracle `P × (P × P) → K`.

The strong Diffie–Hellman problem (Abdalla–Bellare–Rogaway, CT-RSA 2001) gives the
adversary `(pub x, pub y)` and an oracle deciding `dh x Y = Z` for queries `(Y, Z)`,
and asks for `dh x (pub y)`. It is the Gap-DH problem with the first element of
every DDH query fixed to `pub x`; every Gap-DH solver with this restriction is a
strong-DH solver. This is the assumption under which Alwen, Blanchet, Hauck, Kiltz,
Lipp and Riepel (EUROCRYPT 2021, §5) prove DHKEM secure; their reduction asks only
DDH queries with first element `pk`.

## Main definitions

* `DHGroup` — scalars, public elements, `pub`, `dh` and `dh a (pub b) = dh b (pub a)`
* `ddhOracle`, `StDHAdversary`, `stdhGame`, `stdhAdvantage` — the strong-DH game
* `dhkem` — DHKEM as a `KEM.Games.ROMScheme`
* `dhkemReduction B` — the strong-DH adversary built from an IND-CCA adversary `B`
  against `dhkem G`: it samples a key `k*`, runs `B` once on `(X, Y, k*)`, answers
  each random-oracle query `(Z, (enc, pk'))` with one DDH query `(enc, Z)` — from a
  table indexed by `enc` when the query passes and `pk' = X`, with `k*` when
  moreover `enc = Y`, and from a table indexed by the whole query otherwise —
  answers decapsulation queries from the table indexed by `enc`, and outputs a `Z`
  passing the DDH check on `Y` found among the queries

## Main results

* `dhkem_indcca` — for every IND-CCA adversary `B` against `dhkem G` with at most
  `qH` random-oracle queries,
  `romINDCCAAdvantage (dhkem G) B ≤ stdhAdvantage G (dhkemReduction G B)`

The advantage on the left is the distance between the real-key and random-key
games of `KEM.Games.romINDCCAGame`: the adversary receives the public key, the
challenge encapsulation and the real or an independent key, and has the random
oracle and a decapsulation oracle refusing the challenge. The reduction asks at
most `qH` DDH queries. The bound has no collision term: decapsulation of every
`enc ≠ enc*` reads the random oracle away from the challenge point.

## Proof outline

1. The real-key and random-key games agree until `B` queries the random oracle at
   the challenge point `(dh y (pub x), (pub y, pub x))` (`oFlag`).
2. The table of the random oracle is re-indexed: points `(Z, (enc, pub x))` with
   `Z = dh x enc` are indexed by `enc`, which is how decapsulation reads them. The
   re-indexed oracle is the simulation of `dhkemReduction B` (`oTwo`).
3. A hit at the challenge point is a query `(Z, (pub y, pub x))` passing the DDH
   check on `pub y`, which the reduction records and outputs.

## References

* R. Barnes, K. Bhargavan, B. Lipp, C. Wood, *Hybrid Public Key Encryption*,
  RFC 9180, §4.1.
* J. Alwen, B. Blanchet, E. Hauck, E. Kiltz, B. Lipp, D. Riepel, *Analysing the
  HPKE Standard*, EUROCRYPT 2021, ePrint 2020/1499, §5.
* M. Abdalla, M. Bellare, P. Rogaway, *The Oracle Diffie-Hellman Assumptions and an
  Analysis of DHIES*, CT-RSA 2001.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.HPKE.DHKEM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.KEM.Games
open CatCrypt.Crypto.KEM.FOTransformU (roOracle_update_ne tsum_map_mul
  tsum_mul_const)
open PMF (tsum_bind_mul)
open CatCrypt.Crypto.Constructions.ECBCPRF (toOuterMeasure_flag_eq toOuterMeasure_le_add_flag
  run_support_rel)
open scoped ENNReal

/-- A Diffie–Hellman group: public elements `pub x` of scalars `x` and the shared
value `dh a B` of a scalar and a public element, with `dh a (pub b) = dh b (pub a)`. -/
structure DHGroup (Sc P : Type) where
  /-- The public element of a scalar. -/
  pub : Sc → P
  /-- The Diffie–Hellman function. -/
  dh : Sc → P → P
  /-- Both parties compute the same shared value. -/
  dh_comm : ∀ a b, dh a (pub b) = dh b (pub a)

variable {Sc P K : Type} [Fintype Sc] [Nonempty Sc] [DecidableEq P] [Fintype K] [Nonempty K]

/-! ## Strong Diffie–Hellman -/

section StDH

/-- The DDH oracle for the secret scalar `x`: on `(Y, Z)` it answers whether
`dh x Y = Z`. -/
noncomputable def ddhOracle (G : DHGroup Sc P) (x : Sc) (_ : Unit) (q : P × P) :
    PMF (Bool × Unit) :=
  PMF.pure (decide (G.dh x q.1 = q.2), ())

variable (P) in
/-- A strong-DH adversary with at most `q` DDH queries. -/
structure StDHAdversary (q : ℕ) : Type 1 where
  /-- The adversary on `(X, Y)`, returning a candidate for the shared value. -/
  run : P → P → OracleAdv (P × P) Bool P
  /-- The query bound. -/
  isQueryBound : ∀ X Y, (run X Y).IsQueryBound q

/-- The strong-DH experiment: sample scalars `x, y`, run the adversary on
`(pub x, pub y)` with the DDH oracle for `x`, and check its output against
`dh x (pub y)`. -/
noncomputable def stdhGame (G : DHGroup Sc P) {q : ℕ} (A : StDHAdversary P q) : PMF Bool :=
  (PMF.uniformFintype Sc).bind fun x => (PMF.uniformFintype Sc).bind fun y =>
    (OracleAdv.run (ddhOracle G x) (A.run (G.pub x) (G.pub y)) ()).map fun r =>
      decide (r.1 = G.dh x (G.pub y))

/-- The strong-DH advantage: the success probability of the experiment. -/
noncomputable def stdhAdvantage (G : DHGroup Sc P) {q : ℕ} (A : StDHAdversary P q) : ℝ≥0∞ :=
  prTrue (liftPMF (stdhGame G A)) Heap.empty

end StDH

/-! ## DHKEM -/

variable (P) in
/-- The domain of the key derivation: the shared value and the KEM context
`(enc, pkR)`. -/
abbrev KDFDom : Type := P × (P × P)

/-- DHKEM over `G` with the key derivation as a random oracle. -/
noncomputable def dhkem (G : DHGroup Sc P) : ROMScheme P Sc K P (KDFDom P) K where
  keygen := (PMF.uniformFintype Sc).map fun x => (G.pub x, x)
  encaps pk := .rand (PMF.uniformFintype Sc) fun y =>
    .query (G.dh y pk, (G.pub y, pk)) fun k => .ret (k, G.pub y)
  decaps sk c := .query (G.dh sk c, (c, G.pub sk)) fun k => .ret (some k)

omit [Fintype K] [Nonempty K] [DecidableEq P] in
/-- **DHKEM is correct for every random-oracle function.** For every generated key pair,
every function `f` answering the key derivation, and every outcome `(k, enc)` of
encapsulation against `f`, decapsulation of `enc` against `f` returns `some k`. -/
theorem dhkem_correct (G : DHGroup Sc P) :
    ∀ kp ∈ (dhkem (K := K) G).keygen.support, ∀ f : KDFDom P → K,
      ∀ e ∈ (OracleAdv.run (CatCrypt.Crypto.PKE.FOTransformT.keyedRO f)
          ((dhkem G).encaps kp.1) ()).support,
        (OracleAdv.run (CatCrypt.Crypto.PKE.FOTransformT.keyedRO f)
          ((dhkem G).decaps kp.2 e.1.2) ()).map Prod.fst = PMF.pure (some e.1.1) := by
  intro kp hkp f e he
  simp only [dhkem, PMF.support_map, Set.mem_image] at hkp
  obtain ⟨x, -, rfl⟩ := hkp
  simp only [dhkem, OracleAdv.run_rand, OracleAdv.run_query, OracleAdv.run_ret,
    CatCrypt.Crypto.PKE.FOTransformT.keyedRO, PMF.pure_bind, PMF.support_bind,
    PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at he
  obtain ⟨y, -, rfl⟩ := he
  simp [dhkem, CatCrypt.Crypto.PKE.FOTransformT.keyedRO, PMF.pure_map, G.dh_comm]

/-! ## The reduction -/

variable (P K) in
/-- The state of the simulation: keys indexed by encapsulations, keys indexed by
random-oracle points, and a shared value found to pass the DDH check on the
challenge. -/
structure SimState where
  /-- Keys indexed by encapsulations. -/
  LD : P → Option K
  /-- Keys indexed by random-oracle points. -/
  LQ : KDFDom P → Option K
  /-- A shared value `Z` with `dh x Y = Z` queried by the adversary. -/
  found : Option P

/-- The initial simulation state. -/
def SimState.init : SimState P K := ⟨fun _ => none, fun _ => none, none⟩

/-- Answer from the table indexed by the encapsulation `c`, sampling and recording a
fresh key. -/
noncomputable def lazyDProg {A : Type} (st : SimState P K) (c : P) (w : K → A) :
    OracleAdv (P × P) Bool (A × SimState P K) :=
  match st.LD c with
  | some k => .ret (w k, st)
  | none => .rand (PMF.uniformFintype K) fun k =>
      .ret (w k, { st with LD := Function.update st.LD c (some k) })

/-- Answer from the table indexed by the point `q`, sampling and recording a fresh
key. -/
noncomputable def lazyQProg {A : Type} (st : SimState P K) (q : KDFDom P) (w : K → A) :
    OracleAdv (P × P) Bool (A × SimState P K) :=
  match st.LQ q with
  | some k => .ret (w k, st)
  | none => .rand (PMF.uniformFintype K) fun k =>
      .ret (w k, { st with LQ := Function.update st.LQ q (some k) })

/-- The simulation of the random oracle and the decapsulation oracle from the public
key `X`, the challenge `Y` and the key `k*`, with DDH queries. -/
noncomputable def simImpl (X Y : P) (kstar : K) (st : SimState P K) :
    KDFDom P ⊕ P → OracleAdv (P × P) Bool ((K ⊕ Option K) × SimState P K)
  | .inl q => .query (q.2.1, q.1) fun b =>
      if (b && decide (q.2.2 = X)) = true then
        (if q.2.1 = Y then .ret (.inl kstar, { st with found := some q.1 })
         else lazyDProg st q.2.1 Sum.inl)
      else lazyQProg st q Sum.inl
  | .inr c => if c = Y then .ret (.inr none, st) else lazyDProg st c fun k => .inr (some k)

theorem isQueryBound_lazyDProg {A : Type} (st : SimState P K) (c : P) (w : K → A) :
    (lazyDProg st c w).IsQueryBound 0 := by
  unfold lazyDProg; split
  · trivial
  · exact fun _ => trivial

theorem isQueryBound_lazyQProg {A : Type} (st : SimState P K) (q : KDFDom P) (w : K → A) :
    (lazyQProg st q w).IsQueryBound 0 := by
  unfold lazyQProg; split
  · trivial
  · exact fun _ => trivial

theorem isQueryBound_simImpl (X Y : P) (kstar : K) (st : SimState P K) (d : KDFDom P ⊕ P) :
    (simImpl X Y kstar st d).IsQueryBound (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  cases d with
  | inl q =>
    intro b
    dsimp only
    split
    · split
      · trivial
      · exact isQueryBound_lazyDProg _ _ _
    · exact isQueryBound_lazyQProg _ _ _
  | inr c =>
    dsimp only [simImpl, Sum.elim_inr]; split
    · trivial
    · exact isQueryBound_lazyDProg _ _ _

/-- The strong-DH adversary built from an IND-CCA adversary `B` against `dhkem G`. It
runs `B` once on `(X, Y, k*)` for a uniform key `k*`, asks one DDH query per
random-oracle query of `B` and none per decapsulation query, and outputs the shared
value found to pass the DDH check on `Y` (`Y` itself if none was found). -/
noncomputable def dhkemReduction {qH qD : ℕ} (B : ROMINDCCAAdversary P K P (KDFDom P) K qH qD) :
    StDHAdversary P qH where
  run X Y := .rand (PMF.uniformFintype K) fun kstar =>
    (OracleAdv.simulate (simImpl X Y kstar) (B.run X Y kstar) SimState.init).bind
      fun x => .ret (x.2.found.getD Y)
  isQueryBound X Y kstar := by
    have h := OracleAdv.isQueryBound_bind
      (OracleAdv.isQueryBound_simulate (simImpl X Y kstar) _ (isQueryBound_simImpl X Y kstar)
        (B.isQueryBoundH X Y kstar) SimState.init)
      (f := fun x => .ret (x.2.found.getD Y)) (n := 0) fun _ => trivial
    simpa using h

/-! ## The challenge hop -/

section ChallengeHop

variable (Sc K) in
/-- The randomness of the IND-CCA experiment: the secret scalar, the ephemeral
scalar and the two candidate keys. -/
structure Draw where
  /-- The secret scalar. -/
  x : Sc
  /-- The ephemeral scalar. -/
  y : Sc
  /-- The encapsulated key. -/
  k₀ : K
  /-- The independent key. -/
  k₁ : K

omit [DecidableEq P] in
variable (Sc K) in
/-- The joint distribution of the randomness of the IND-CCA experiment. -/
noncomputable def setup : PMF (Draw Sc K) :=
  (PMF.uniformFintype Sc).bind fun x => (PMF.uniformFintype Sc).bind fun y =>
    (PMF.uniformFintype K).bind fun k₀ => (PMF.uniformFintype K).map fun k₁ =>
      ⟨x, y, k₀, k₁⟩

/-- Exchange the two candidate keys of a draw. -/
def Draw.swap (d : Draw Sc K) : Draw Sc K := { d with k₀ := d.k₁, k₁ := d.k₀ }

omit [DecidableEq P] in
theorem setup_map_swap : (setup Sc K).map Draw.swap = setup Sc K := by
  simp only [setup, PMF.map_bind, PMF.map_comp]
  refine congrArg _ (funext fun x => congrArg _ (funext fun y => ?_))
  simp only [PMF.map, Function.comp_def, Draw.swap]
  exact PMF.bind_comm _ _ _

variable (G : DHGroup Sc P)

/-- The challenge point of the random oracle for secret scalar `x` and ephemeral
scalar `y`. -/
def kpt (x y : Sc) : KDFDom P := (G.dh y (G.pub x), (G.pub y, G.pub x))

/-- The oracle of the IND-CCA experiment for `dhkem G` with the challenge point
removed from the table: a query at the challenge point returns `v` and sets the
flag. -/
noncomputable def oFlag (x y : Sc) (v : K) (st : (KDFDom P → Option K) × Bool) :
    KDFDom P ⊕ P → PMF ((K ⊕ Option K) × ((KDFDom P → Option K) × Bool))
  | .inl d => if d = kpt G x y then PMF.pure (.inl v, (st.1, true)) else
      (roOracle st.1 d).map fun r => (.inl r.1, (r.2, st.2))
  | .inr c => if c = G.pub y then PMF.pure (.inr none, st) else
      (roOracle st.1 (G.dh x c, (c, G.pub x))).map fun r => (.inr (some r.1), (r.2, st.2))

/-- The distribution of the flagged run; `swap` selects the candidate key stored
at the challenge point. -/
noncomputable def flagDist {qH qD : ℕ} (B : ROMINDCCAAdversary P K P (KDFDom P) K qH qD)
    (swap : Bool) : PMF (Bool × ((KDFDom P → Option K) × Bool)) :=
  (setup Sc K).bind fun d => OracleAdv.run
    (oFlag G d.x d.y (if swap then d.k₁ else d.k₀)) (B.run (G.pub d.x) (G.pub d.y) d.k₀)
    (emptyTable, false)

/-- Storing `v` at the challenge point commutes with each transition of the flagged
oracle and the oracle of the experiment. -/
theorem oFlag_map (x y : Sc) (v : K) (st : (KDFDom P → Option K) × Bool) (d : KDFDom P ⊕ P) :
    (oFlag G x y v st d).map (Prod.map id fun s => Function.update s.1 (kpt G x y) (some v)) =
      romCCAOracle (dhkem G) x (G.pub y) (Function.update st.1 (kpt G x y) (some v)) d := by
  cases d with
  | inl d =>
    by_cases hd : d = kpt G x y
    · subst hd
      simp [oFlag, romCCAOracle, roOracle, PMF.pure_map]
    · simp only [oFlag, romCCAOracle, hd, ite_false, PMF.map_comp]
      rw [← roOracle_update_ne _ _ _ _ hd, PMF.map_comp]
      rfl
  | inr c =>
    by_cases hc : c = G.pub y
    · subst hc
      simp [oFlag, romCCAOracle, PMF.pure_map]
    · have hne : (G.dh x c, (c, G.pub x)) ≠ kpt G x y := fun h =>
        hc (congrArg (fun p => p.2.1) h)
      simp only [oFlag, romCCAOracle, hc, ite_false, PMF.map_comp, dhkem, OracleAdv.run_query,
        OracleAdv.run_ret]
      rw [← roOracle_update_ne _ _ _ _ hne]
      rw [show (fun r : K × (KDFDom P → Option K) => PMF.pure (some r.1, r.2)) =
        PMF.pure ∘ (fun r => (some r.1, r.2)) from rfl, PMF.bind_pure_comp, PMF.map_comp,
        PMF.map_comp]
      rfl

/-- A run of the experiment's oracle from the table holding only `v` at the
challenge point is the flagged run with the flag and the table forgotten. -/
theorem run_romCCAOracle_eq {α : Type} (x y : Sc) (v : K)
    (A : OracleAdv (KDFDom P ⊕ P) (K ⊕ Option K) α) :
    (OracleAdv.run (romCCAOracle (dhkem G) x (G.pub y)) A
      (Function.update emptyTable (kpt G x y) (some v))).map Prod.fst =
    (OracleAdv.run (oFlag G x y v) A (emptyTable, false)).map Prod.fst := by
  have h := OracleAdv.run_map_state (oFlag G x y v) (romCCAOracle (dhkem G) x (G.pub y))
    (fun s => Function.update s.1 (kpt G x y) (some v)) (fun st d => oFlag_map G x y v st d) A
    (emptyTable, false)
  rw [← h, PMF.map_comp]
  rfl

theorem romINDCCAGame_dhkem {qH qD : ℕ} (B : ROMINDCCAAdversary P K P (KDFDom P) K qH qD)
    (b : Bool) :
    romINDCCAGame (dhkem G) B b = (setup Sc K).bind fun d =>
      (OracleAdv.run (oFlag G d.x d.y d.k₀)
        (B.run (G.pub d.x) (G.pub d.y) (if b then d.k₀ else d.k₁)) (emptyTable, false)).map
          Prod.fst := by
  simp only [romINDCCAGame, setup, dhkem, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    OracleAdv.run_rand, OracleAdv.run_query, OracleAdv.run_ret]
  refine congrArg _ (funext fun x => congrArg _ (funext fun y => ?_))
  simp only [roOracle, emptyTable, PMF.bind_map, Function.comp_def, PMF.pure_bind]
  refine congrArg _ (funext fun k₀ => ?_)
  simp only [PMF.map, Function.comp_def]
  refine congrArg _ (funext fun k₁ => ?_)
  exact run_romCCAOracle_eq G x y k₀ _

omit [Fintype Sc] [Nonempty Sc] in
theorem oFlag_apply_true_false (x y : Sc) (v : K) (T : KDFDom P → Option K)
    (d : KDFDom P ⊕ P) (a : K ⊕ Option K) (T' : KDFDom P → Option K) :
    oFlag G x y v (T, true) d (a, (T', false)) = 0 := by
  cases d with
  | inl d =>
    simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rw [PMF.map_apply]; simp
  | inr c =>
    simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rw [PMF.map_apply]; simp

omit [Fintype Sc] [Nonempty Sc] in
theorem oFlag_apply_false_eq (x y : Sc) (v v' : K) (st : (KDFDom P → Option K) × Bool)
    (d : KDFDom P ⊕ P) (a : K ⊕ Option K) (T' : KDFDom P → Option K) :
    oFlag G x y v st d (a, (T', false)) = oFlag G x y v' st d (a, (T', false)) := by
  cases d with
  | inl d =>
    simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rfl
  | inr c => rfl

/-- **Challenge hop.** The IND-CCA advantage against `dhkem G` is at most the
probability that the adversary queries the random oracle at the challenge point. -/
theorem romINDCCAAdvantage_le_flag {qH qD : ℕ}
    (B : ROMINDCCAAdversary P K P (KDFDom P) K qH qD) :
    romINDCCAAdvantage (dhkem G) B ≤ (flagDist G B false).toOuterMeasure {r | r.2.2 = true} := by
  have h₁ : romINDCCAGame (dhkem G) B true = (flagDist G B false).map Prod.fst := by
    rw [romINDCCAGame_dhkem, flagDist, PMF.map_bind]
    simp_all
  have h₂ : romINDCCAGame (dhkem G) B false = (flagDist G B true).map Prod.fst := by
    rw [romINDCCAGame_dhkem, flagDist, PMF.map_bind]
    conv_lhs => rw [← setup_map_swap, PMF.bind_map]
    rfl
  have h : ∀ a t, flagDist G B false (a, (t, false)) = flagDist G B true (a, (t, false)) := by
    intro a t
    simp only [flagDist, PMF.bind_apply]
    refine tsum_congr fun d => congrArg _ ?_
    exact OracleAdv.run_apply_flag_false_eq _ _ (oFlag_apply_true_false G _ _ _)
      (oFlag_apply_true_false G _ _ _)
      (fun st e r T' => oFlag_apply_false_eq G _ _ _ _ st e r T') _ _ a t
  unfold romINDCCAAdvantage
  rw [h₁, h₂]
  simp only [Advantage, prTrue_liftPMF_map]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · rw [toOuterMeasure_flag_eq _ _ h]
    simpa only [Set.mem_singleton_iff] using toOuterMeasure_le_add_flag _ _ h {true}
  · simpa only [Set.mem_singleton_iff] using
      toOuterMeasure_le_add_flag _ _ (fun a t => (h a t).symm) {true}

end ChallengeHop

/-! ## The re-indexed oracle -/

section Reindex

/-- Answer from the table indexed by the encapsulation `c`. -/
noncomputable def lazyD {A : Type} (st : SimState P K) (c : P) (w : K → A) :
    PMF (A × (SimState P K × Unit)) :=
  lazyRead st.LD c (fun t => { st with LD := t }) w ()

/-- Answer from the table indexed by the point `q`. -/
noncomputable def lazyQ {A : Type} (st : SimState P K) (q : KDFDom P) (w : K → A) :
    PMF (A × (SimState P K × Unit)) :=
  lazyRead st.LQ q (fun t => { st with LQ := t }) w ()

/-- The re-indexed oracle with selector `sel`, challenge `Y` and key `v`: a
random-oracle query `q` with `sel q` is answered from the table indexed by its
encapsulation (and by `v`, recording `q.1` as found, when the encapsulation is `Y`),
any other query from the table indexed by `q`; a decapsulation query is answered
from the table indexed by the encapsulation. -/
noncomputable def oTwo (sel : KDFDom P → Bool) (Y : P) (v : K) (s : SimState P K × Unit) :
    KDFDom P ⊕ P → PMF ((K ⊕ Option K) × (SimState P K × Unit))
  | .inl q =>
    if sel q = true then
      (if q.2.1 = Y then PMF.pure (.inl v, ({ s.1 with found := some q.1 }, ()))
       else lazyD s.1 q.2.1 Sum.inl)
    else lazyQ s.1 q Sum.inl
  | .inr c => if c = Y then PMF.pure (.inr none, s) else lazyD s.1 c fun k => .inr (some k)

variable (G : DHGroup Sc P)

/-- The DDH selector for the secret scalar `x`: the point `(Z, (c, pk'))` has
`dh x c = Z` and `pk' = pub x`. -/
def selX (x : Sc) (q : KDFDom P) : Bool :=
  decide (G.dh x q.2.1 = q.1) && decide (q.2.2 = G.pub x)

/-- The random-oracle table represented by a simulation state: points selected by
`selX` are read from the table indexed by the encapsulation, other points from the
table indexed by the point. -/
def table (x : Sc) (st : SimState P K) : KDFDom P → Option K :=
  reindexTable (selX G x) (fun q => q.2.1) st.LD st.LQ

omit [Fintype Sc] [Nonempty Sc] [Fintype K] [Nonempty K] in
/-- The only point selected by `selX` with encapsulation `c` is `(dh x c, (c, pub x))`. -/
theorem selX_inj (x : Sc) (c : P) (q : KDFDom P) (hs : selX G x q = true) (hc : q.2.1 = c) :
    q = (G.dh x c, (c, G.pub x)) := by
  obtain ⟨Z, c', pk'⟩ := q
  simp only [selX, Bool.and_eq_true, decide_eq_true_eq] at hs hc
  obtain ⟨rfl, rfl⟩ := hs
  subst hc
  rfl

omit [Fintype Sc] [Nonempty Sc] [Fintype K] [Nonempty K] in
theorem selX_dh (x : Sc) (c : P) : selX G x (G.dh x c, (c, G.pub x)) = true := by
  simp [selX]

omit [Fintype Sc] [Nonempty Sc] [Fintype K] [Nonempty K] in
theorem table_updateLD (x : Sc) (st : SimState P K) (c : P) (k : K) :
    table G x { st with LD := Function.update st.LD c (some k) } =
      Function.update (table G x st) (G.dh x c, (c, G.pub x)) (some k) :=
  reindexTable_update_left _ _ _ _ (selX_dh G x c) rfl (selX_inj G x c) _

omit [Fintype Sc] [Nonempty Sc] [Fintype K] [Nonempty K] in
theorem table_updateLQ (x : Sc) (st : SimState P K) (q : KDFDom P) (k : K)
    (hq : selX G x q = false) :
    table G x { st with LQ := Function.update st.LQ q (some k) } =
      Function.update (table G x st) q (some k) :=
  reindexTable_update_right _ _ _ _ hq _

omit [Fintype Sc] [Nonempty Sc] [Fintype K] [Nonempty K] in
theorem selX_kpt (x y : Sc) : selX G x (kpt G x y) = true := by
  simp [selX, kpt, G.dh_comm]

omit [Fintype Sc] [Nonempty Sc] in
/-- A read of the table indexed by `c` is the random oracle at `(dh x c, (c, pub x))`. -/
theorem lazyD_map_table {A : Type} (x : Sc) (st : SimState P K) (c : P) (w : K → A)
    (b : Bool) (F : K × (KDFDom P → Option K) → A × ((KDFDom P → Option K) × Bool))
    (hF : ∀ k T, F (k, T) = (w k, (T, b))) (hb : st.found.isSome = b) :
    (lazyD st c w).map (Prod.map id fun t => (table G x t.1, t.1.found.isSome)) =
      (roOracle (table G x st) (G.dh x c, (c, G.pub x))).map F :=
  lazyRead_map_reindex_left (j := (G.dh x c, (c, G.pub x))) _ _ _ _ (selX_dh G x c)
    (selX_inj G x c) _ _ _ _ _ fun k t => by simp [hF, table, hb]

omit [Fintype Sc] [Nonempty Sc] in
/-- A read of the table indexed by an unselected point `q` is the random oracle at `q`. -/
theorem lazyQ_map_table {A : Type} (x : Sc) (st : SimState P K) (q : KDFDom P) (w : K → A)
    (hq : selX G x q = false) (b : Bool)
    (F : K × (KDFDom P → Option K) → A × ((KDFDom P → Option K) × Bool))
    (hF : ∀ k T, F (k, T) = (w k, (T, b))) (hb : st.found.isSome = b) :
    (lazyQ st q w).map (Prod.map id fun t => (table G x t.1, t.1.found.isSome)) =
      (roOracle (table G x st) q).map F :=
  lazyRead_map_reindex_right _ _ _ _ hq _ _ _ _ _ fun k t => by simp [hF, table, hb]

omit [Fintype Sc] [Nonempty Sc] in
/-- Reading the table maps the re-indexed oracle with selector `selX` to the flagged
oracle. -/
theorem oTwo_map_table (x y : Sc) (v : K) (s : SimState P K × Unit) (d : KDFDom P ⊕ P) :
    (oTwo (selX G x) (G.pub y) v s d).map
        (Prod.map id fun t => (table G x t.1, t.1.found.isSome)) =
      oFlag G x y v (table G x s.1, s.1.found.isSome) d := by
  obtain ⟨st, u⟩ := s
  cases d with
  | inl q =>
    by_cases hsel : selX G x q = true
    · obtain ⟨Z, c, pk'⟩ := q
      have hsel' := hsel
      simp only [selX, Bool.and_eq_true, decide_eq_true_eq] at hsel'
      obtain ⟨hZ, hpk⟩ := hsel'
      subst hZ hpk
      by_cases hc : c = G.pub y
      · subst hc
        have hq : ((G.dh x (G.pub y), (G.pub y, G.pub x)) : KDFDom P) = kpt G x y := by
          simp [kpt, G.dh_comm]
        rw [hq] at hsel ⊢
        simp only [oTwo, hsel, ite_true, oFlag]
        simp only [kpt, ite_true, PMF.pure_map]
        rfl
      · have hq : ((G.dh x c, (c, G.pub x)) : KDFDom P) ≠ kpt G x y := fun h =>
          hc (congrArg (fun p => p.2.1) h)
        simp only [oTwo, hsel, ite_true, hc, ite_false, oFlag, hq]
        exact lazyD_map_table G x st c _ _ _ (fun _ _ => rfl) rfl
    · have hsel' : selX G x q = false := by simpa using hsel
      have hq : q ≠ kpt G x y := by
        intro h; rw [h, selX_kpt] at hsel'; exact Bool.noConfusion hsel'
      simp only [oTwo, hsel', Bool.false_eq_true, ite_false, oFlag, hq]
      exact lazyQ_map_table G x st q _ hsel' _ _ (fun _ _ => rfl) rfl
  | inr c =>
    by_cases hc : c = G.pub y
    · subst hc; simp [oTwo, oFlag, PMF.pure_map]
    · simp only [oTwo, oFlag, hc, ite_false]
      exact lazyD_map_table G x st c _ _ _ (fun _ _ => rfl) rfl

end Reindex

/-! ## The simulation -/

section Simulation

variable (G : DHGroup Sc P)

omit [Fintype Sc] [Nonempty Sc] in
theorem run_lazyDProg {A : Type} (x : Sc) (st : SimState P K) (c : P) (w : K → A) :
    (OracleAdv.run (ddhOracle G x) (lazyDProg st c w) ()).map
      (fun r => (r.1.1, (r.1.2, r.2))) = lazyD st c w := by
  unfold lazyDProg lazyD lazyRead
  split <;> rename_i h <;> simp [h, PMF.pure_map, PMF.map_bind]
  rfl

omit [Fintype Sc] [Nonempty Sc] in
theorem run_lazyQProg {A : Type} (x : Sc) (st : SimState P K) (q : KDFDom P) (w : K → A) :
    (OracleAdv.run (ddhOracle G x) (lazyQProg st q w) ()).map
      (fun r => (r.1.1, (r.1.2, r.2))) = lazyQ st q w := by
  unfold lazyQProg lazyQ lazyRead
  split <;> rename_i h <;> simp [h, PMF.pure_map, PMF.map_bind]
  rfl

omit [Fintype Sc] [Nonempty Sc] in
/-- The composite oracle of the reduction is the re-indexed oracle with the DDH
selector. -/
theorem simOracle_eq_oTwo (x : Sc) (Y : P) (v : K) (s : SimState P K × Unit)
    (d : KDFDom P ⊕ P) :
    OracleAdv.simOracle (simImpl (G.pub x) Y v) (ddhOracle G x) s d =
      oTwo (selX G x) Y v s d := by
  obtain ⟨st, u⟩ := s
  cases d with
  | inl q =>
    simp only [OracleAdv.simOracle, simImpl, oTwo, OracleAdv.run_query, ddhOracle, PMF.pure_bind,
      selX]
    split_ifs
    · simp [PMF.pure_map]
    · exact run_lazyDProg G x st q.2.1 Sum.inl
    · exact run_lazyQProg G x st q Sum.inl
  | inr c =>
    simp only [OracleAdv.simOracle, simImpl, oTwo]
    split_ifs
    · simp [PMF.pure_map]
    · exact run_lazyDProg G x st c _

theorem found_of_mem_support_lazyD {A : Type} {st : SimState P K} {c : P} {w : K → A}
    {r : A × (SimState P K × Unit)} (hr : r ∈ (lazyD st c w).support) :
    r.2.1.found = st.found :=
  eq_of_mem_support_lazyRead SimState.found (fun _ => rfl) hr

theorem found_of_mem_support_lazyQ {A : Type} {st : SimState P K} {q : KDFDom P} {w : K → A}
    {r : A × (SimState P K × Unit)} (hr : r ∈ (lazyQ st q w).support) :
    r.2.1.found = st.found :=
  eq_of_mem_support_lazyRead SimState.found (fun _ => rfl) hr

/-- A found shared value passes the DDH check on the challenge. -/
def FoundValid (x : Sc) (Y : P) (st : SimState P K) : Prop :=
  ∀ Z, st.found = some Z → G.dh x Y = Z

omit [Fintype Sc] [Nonempty Sc] in
/-- On every outcome of a run of the re-indexed oracle with the DDH selector from the
initial state, a found shared value passes the DDH check on the challenge. -/
theorem foundValid_of_mem_support {α : Type} (x : Sc) (Y : P) (v : K)
    (A : OracleAdv (KDFDom P ⊕ P) (K ⊕ Option K) α) (r : α × (SimState P K × Unit))
    (hr : r ∈ (OracleAdv.run (oTwo (selX G x) Y v) A (SimState.init, ())).support) :
    FoundValid G x Y r.2.1 := by
  have h := run_support_rel (oTwo (selX G x) Y v)
    (fun a b => FoundValid G x Y a.1 → FoundValid G x Y b.1) (fun _ h => h)
    (fun _ _ _ h₁ h₂ h => h₂ (h₁ h)) ?_ A (SimState.init, ()) r hr
  · exact h fun Z hZ => by simp [SimState.init] at hZ
  · intro s d z hz hs
    cases d with
    | inl q =>
      simp only [oTwo] at hz
      split_ifs at hz with hsel hc
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        intro Z hZ
        simp only [Option.some.injEq] at hZ
        subst hZ
        simp only [selX, Bool.and_eq_true, decide_eq_true_eq] at hsel
        rw [← hc]; exact hsel.1
      · intro Z hZ; rw [found_of_mem_support_lazyD hz] at hZ; exact hs Z hZ
      · intro Z hZ; rw [found_of_mem_support_lazyQ hz] at hZ; exact hs Z hZ
    | inr c =>
      simp only [oTwo] at hz
      split_ifs at hz
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hs
      · intro Z hZ; rw [found_of_mem_support_lazyD hz] at hZ; exact hs Z hZ

omit [Fintype Sc] [Nonempty Sc] [Fintype K] [Nonempty K] in
theorem table_init (x : Sc) : table G x (SimState.init : SimState P K) = emptyTable := by
  funext q; simp [table, reindexTable, SimState.init, emptyTable]

omit [Fintype Sc] [Nonempty Sc] in
/-- **Per-draw bound.** For fixed scalars, the probability that the flagged run hits
the challenge point is at most the probability that the simulation outputs the
shared value of the challenge. -/
theorem flag_le (x y : Sc) (v : K) (A : OracleAdv (KDFDom P ⊕ P) (K ⊕ Option K) Bool) :
    (OracleAdv.run (oFlag G x y v) A (emptyTable, false)).toOuterMeasure
        {r | r.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.simOracle (simImpl (G.pub x) (G.pub y) v) (ddhOracle G x)) A
        (SimState.init, ())).toOuterMeasure
          {r | r.2.1.found.getD (G.pub y) = G.dh x (G.pub y)} := by
  have hs : OracleAdv.simOracle (simImpl (G.pub x) (G.pub y) v) (ddhOracle G x) =
      oTwo (selX G x) (G.pub y) v :=
    funext fun s => funext fun d => simOracle_eq_oTwo G x (G.pub y) v s d
  have h1 : (OracleAdv.run (oFlag G x y v) A (emptyTable, false)).toOuterMeasure
      {r | r.2.2 = true} =
      (OracleAdv.run (oTwo (selX G x) (G.pub y) v) A (SimState.init, ())).toOuterMeasure
        {r | r.2.1.found.isSome = true} := by
    have h := OracleAdv.run_map_state (oTwo (selX G x) (G.pub y) v) (oFlag G x y v)
      (fun t => (table G x t.1, t.1.found.isSome))
      (fun s d => oTwo_map_table G x y v s d) A (SimState.init, ())
    simp only [table_init] at h
    rw [show ((SimState.init : SimState P K).found.isSome) = false from rfl] at h
    rw [← h, PMF.toOuterMeasure_map_apply]
    rfl
  rw [h1, hs]
  refine PMF.toOuterMeasure_mono _ fun r ⟨hr, hsupp⟩ => ?_
  have hv := foundValid_of_mem_support G x (G.pub y) v A r hsupp
  simp only [Set.mem_ofPred_eq, Option.isSome_iff_exists] at hr ⊢
  obtain ⟨Z, hZ⟩ := hr
  rw [hZ, Option.getD_some]
  exact (hv Z hZ).symm

end Simulation

/-! ## Summing over the draws -/

section Summation

variable (G : DHGroup Sc P)

omit [DecidableEq P] in
theorem tsum_setup_mul (F : Draw Sc K → ℝ≥0∞) :
    ∑' d, setup Sc K d * F d = ∑' x, PMF.uniformFintype Sc x *
      ∑' y, PMF.uniformFintype Sc y * ∑' k₀, PMF.uniformFintype K k₀ *
        ∑' k₁, PMF.uniformFintype K k₁ * F ⟨x, y, k₀, k₁⟩ := by
  simp only [setup, tsum_bind_mul, tsum_map_mul]

omit [Fintype Sc] [Nonempty Sc] in
/-- The strong-DH success probability of `dhkemReduction B` for fixed scalars. -/
theorem dhkemReduction_prob {qH qD : ℕ} (B : ROMINDCCAAdversary P K P (KDFDom P) K qH qD)
    (x y : Sc) :
    ((OracleAdv.run (ddhOracle G x) ((dhkemReduction B).run (G.pub x) (G.pub y)) ()).map
      fun r => decide (r.1 = G.dh x (G.pub y))).toOuterMeasure {b | b = true} =
    ∑' k, PMF.uniformFintype K k *
      (OracleAdv.run (OracleAdv.simOracle (simImpl (G.pub x) (G.pub y) k) (ddhOracle G x))
        (B.run (G.pub x) (G.pub y) k) (SimState.init, ())).toOuterMeasure
          {r | r.2.1.found.getD (G.pub y) = G.dh x (G.pub y)} := by
  unfold dhkemReduction
  dsimp only
  rw [OracleAdv.run_rand, PMF.map_bind, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun k => congrArg _ ?_
  rw [OracleAdv.run_bind, OracleAdv.run_simulate, PMF.bind_map]
  simp only [OracleAdv.run_ret, Function.comp_def, PMF.map_bind, PMF.pure_map,
    PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_pure_apply]
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun r => ?_
  by_cases h : r.2.1.found.getD (G.pub y) = G.dh x (G.pub y) <;>
    simp [Set.indicator, h]

theorem stdhAdvantage_dhkemReduction {qH qD : ℕ}
    (B : ROMINDCCAAdversary P K P (KDFDom P) K qH qD) :
    stdhAdvantage G (dhkemReduction B) =
      ∑' x, PMF.uniformFintype Sc x * ∑' y, PMF.uniformFintype Sc y *
        ∑' k, PMF.uniformFintype K k *
          (OracleAdv.run (OracleAdv.simOracle (simImpl (G.pub x) (G.pub y) k) (ddhOracle G x))
            (B.run (G.pub x) (G.pub y) k) (SimState.init, ())).toOuterMeasure
              {r | r.2.1.found.getD (G.pub y) = G.dh x (G.pub y)} := by
  rw [stdhAdvantage, prTrue_liftPMF_toOuterMeasure, stdhGame]
  simp only [PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun x => congrArg _ (tsum_congr fun y => congrArg _ ?_)
  exact dhkemReduction_prob G B x y

end Summation

/-! ## The theorem -/

/-- **DHKEM is IND-CCA secure under strong Diffie–Hellman in the random-oracle model**
(Alwen–Blanchet–Hauck–Kiltz–Lipp–Riepel, EUROCRYPT 2021, §5). For every
Diffie–Hellman group `G` and every IND-CCA adversary `B` against `dhkem G` asking at
most `qH` random-oracle queries,

`romINDCCAAdvantage (dhkem G) B ≤ stdhAdvantage G (dhkemReduction B)`.

The adversary receives the public key `pub x`, the challenge encapsulation and the
real or an independent uniform key, and has the random oracle and a decapsulation
oracle refusing the challenge encapsulation. The reduction `dhkemReduction B` runs
`B` once and asks at most `qH` DDH queries, all with first element `pub x`. -/
theorem dhkem_indcca {qH qD : ℕ} (G : DHGroup Sc P)
    (B : ROMINDCCAAdversary P K P (KDFDom P) K qH qD) :
    romINDCCAAdvantage (dhkem G) B ≤ stdhAdvantage G (dhkemReduction B) := by
  refine (romINDCCAAdvantage_le_flag G B).trans ?_
  rw [flagDist, PMF.toOuterMeasure_bind_apply, stdhAdvantage_dhkemReduction, tsum_setup_mul]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  refine ENNReal.tsum_le_tsum fun y => mul_le_mul_right ?_ _
  refine ENNReal.tsum_le_tsum fun k₀ => mul_le_mul_right ?_ _
  simp only [Bool.false_eq_true, ite_false, tsum_mul_const]
  exact flag_le G x y k₀ _

end CatCrypt.Crypto.HPKE.DHKEM

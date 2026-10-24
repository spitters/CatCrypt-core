/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.StraightLine

/-!
# Fiat–Shamir in the random-oracle model: straight-line extraction by key classes

The straight-line extractor of `FiatShamirROM.StraightLine` with a bad-answer
probability for each key class. For key classes `κ`, a class-wise log extractor
(`Protocol.LogExtractorCls G rel N κ ε εS`) bounds the probability that a fresh
oracle answer at a point of class `c` is bad by `ε c`, and the probability that the
entries programmed by one simulated signing attempt contain a bad one by `εS`. The
simulator places the evaluated entry `i` of an attempt at a point of class `ecls i`.

The extraction flag of the instrumented game is bounded class by class: a hash
query at a point of class `c` sets it with probability at most `ε c`, a signing
query with probability at most `Σ_c μe c·ε c + εS`, where `μe c` counts the
evaluated entries of class `c`. The bad draws of a run are summed over a family of
query costs (`OracleAdv.run_badDraw_le_sum`).

## Main definitions

* `OracleAdv.run_badDraw_le_sum` — bad draws with a family of query costs
* `Protocol.Classes.μe` — the number of evaluated entries of an attempt in a class
* `Protocol.LogExtractorCls G rel N κ ε εS` — a log extractor with class-wise
  bad-answer probabilities
* `slReductionCls E A` — the reduction running the instrumented game once and
  applying the extractor
* `Protocol.LogExtractor.toCls` — a log extractor as a class-wise one for the
  partition into one class

## Main results

* `run_sl_flag_le_cls` — a run sets the extraction flag with probability at most
  the sum over the classes of its class costs times `ε c`, plus its signing
  queries times `εS`
* `simAdvantage_le_slCls` — the simulated-game advantage is at most the relation
  advantage of `slReductionCls E A` plus `Σ_c (q c + Vc c + μe c·qS)·ε c + qS·εS`
* `fiatShamir_rom_eufcma_slCls` — the EUF-CMA bound of straight-line extraction
  with class-wise extraction and signing-hop terms
* `slReductionCls_toCls` — the class-wise reduction of `E.toCls` is `slReduction E`
* `fiatShamir_rom_eufcma_sl` — for a log extractor `E` and every adversary with at
  most `qH` hash and `qS` signing queries, the EUF-CMA advantage is at most the
  relation advantage of `slReduction E A`, plus `(qH + V + μ·qS)·ε`, plus the
  signing-hop terms of `Protocol.eufcmaAdvantage_le_simAdvantage_perKey`; it is
  `fiatShamir_rom_eufcma_slCls` at `E.toCls` and the partition into one class
* `sim_wins_le_sl`, `simAdvantage_le_sl` — the per-statement and simulated-game
  bounds for a log extractor, from their class-wise forms
* `fiatShamir_rom_eufcma_sl_cls`, `fiatShamir_rom_eufcma_sl_stat` — the bound of
  `fiatShamir_rom_eufcma_sl` with class-wise signing-hop terms, and with constant
  HVZK distance and key bound
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open scoped ENNReal

/-! ## Bad draws with a family of costs -/

variable {D R α : Type}

/-- **Bad draws with a family of costs.** Let every call `O s d` from a state `s`
without `bad` reach a `bad` state with probability at most `Σ_c cost c d · ε c`. A
run of an adversary whose queries cost at most `n c` in total for the cost `cost c`
on every path, started from a state without `bad`, ends in a `bad` state with
probability at most `Σ_c n c · ε c`. -/
theorem run_badDraw_le_sum {ι S : Type} [Fintype ι] (O : S → D → PMF (R × S))
    (bad : S → Prop) (cost : ι → D → ℕ) (ε : ι → ℝ≥0∞)
    (hstep : ∀ s d, ¬ bad s → (O s d).toOuterMeasure {x | bad x.2} ≤ ∑ c, cost c d * ε c)
    (A : OracleAdv D R α) (n : ι → ℕ) (hA : ∀ c, A.IsQueryBoundBy (cost c) (n c)) (s : S)
    (hs : ¬ bad s) :
    (run O A s).toOuterMeasure {y | bad y.2} ≤ ∑ c, n c * ε c := by
  classical
  induction A generalizing n s with
  | ret a => simp [PMF.toOuterMeasure_pure_apply, hs]
  | rand p k ih =>
    rw [run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (run O (k b) s).toOuterMeasure {y | bad y.2}
        ≤ ∑' b, p b * ∑ c, n c * ε c :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b n (fun c => hA c b) s hs
      _ = ∑ c, n c * ε c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    rw [run_query, PMF.toOuterMeasure_bind_apply]
    calc ∑' x, O s d x * (run O (k x.1) x.2).toOuterMeasure {y | bad y.2}
        ≤ ∑' x, ({x : R × S | bad x.2}.indicator (O s d) x +
            O s d x * ∑ c, ((n c - cost c d : ℕ) : ℝ≥0∞) * ε c) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : bad x.2
          · rw [Set.indicator_of_mem (show x ∈ {x : R × S | bad x.2} from hx)]
            refine (mul_le_of_le_one_right' ?_).trans le_self_add
            exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
              ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
          · rw [Set.indicator_of_notMem (show x ∉ {x : R × S | bad x.2} from hx), zero_add]
            gcongr
            exact ih x.1 _ (fun c => (hA c).2 x.1) x.2 hx
      _ = (O s d).toOuterMeasure {x | bad x.2} + ∑ c, ((n c - cost c d : ℕ) : ℝ≥0∞) * ε c := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
      _ ≤ ∑ c, cost c d * ε c + ∑ c, ((n c - cost c d : ℕ) : ℝ≥0∞) * ε c := by
          gcongr; exact hstep s d hs
      _ = ∑ c, n c * ε c := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' (hA c).1]

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

/-! ## Class-wise log extractors and the reduction -/

namespace Protocol

variable (G : Protocol)

/-- The number of evaluated entries of an attempt in the class `c`. -/
def Classes.μe {G : Protocol} (κ : G.Classes) (c : κ.ι) : ℕ :=
  (Finset.univ.filter fun i => G.ev i = true ∧ κ.ecls i = c).card

/-- **Class-wise log extractor** for the relation `rel` on tables with at most `N`
entries, for the key classes `κ`. The extractor `ext` reads the statement, the
tables and the forgery. The simulator places the evaluated entry `i` at a point of
class `ecls i`. A fresh oracle answer at a point of class `c` satisfies `Bad` with
probability at most `ε c`, and the programmed entries of one simulated signing
attempt contain a bad one with probability at most `εS`, for tables with at most `N`
entries. At every reachable state with at most `N` table entries and the extraction
flag cleared, a winning forgery gives a witness. -/
structure LogExtractorCls (rel : G.Stmt → G.Wit → Prop) (N : ℕ) (κ : G.Classes)
    (ε : κ.ι → ℝ≥0∞) (εS : ℝ≥0∞) where
  /-- The extractor on the statement, the final tables and the forgery. -/
  ext : G.Stmt → G.Tables → G.Forgery → G.Wit
  /-- The fresh answer `e` at the point `k` is bad given the tables `t`. -/
  Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool
  /-- The simulator point of the entry `i` is in the class `ecls i`. -/
  simKey_cls : ∀ x m s (v : Fin G.μ → G.Ch) (i : Fin G.μ) (k : G.Key),
    G.simKey x m s v i = some k → κ.cls k = κ.ecls i
  /-- A uniform answer at a point of class `c` is bad with probability at most
  `ε c`. -/
  bad_le : ∀ x t k, t.size ≤ N →
    (PMF.uniformFintype G.Ch).toOuterMeasure {e | Bad x t k e = true} ≤ ε (κ.cls k)
  /-- The programmed entries of a simulated attempt from the tables `t` on uniform
  values and simulator randomness contain an entry that is bad given the tables after
  the evaluated entries with probability at most `εS`. -/
  simBad_le : ∀ x t m, t.size ≤ N →
    (sampleVec G fun e (s : G.SimRand) =>
      (G.simTrace t.lookup x m e s).2.1.any fun p =>
        Bad x (hashAll t (G.simTrace t.lookup x m e s).1) p.1 p.2).toOuterMeasure
        {c | c = true} ≤ εS
  /-- On tables with at most `N` entries and without the extraction flag, a winning
  forgery gives a witness. -/
  sound : ∀ x (s : SLState G) (f : G.Forgery), SLReach N Bad x s → s.2 = false →
    s.1.1.size ≤ N → wins x (f, s.1) = true → rel x (ext x s.1.1 f)

variable {G}

/-- A log extractor is a class-wise log extractor for the partition into one class,
with the bound `ε` for every answer and the number of programmed entries times `ε`
for the programmed entries of an attempt. -/
def LogExtractor.toCls {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {ε : ℝ≥0∞}
    (E : G.LogExtractor rel N ε) :
    G.LogExtractorCls rel N (Classes.unit G) (fun _ => ε)
      ((Finset.univ.filter fun i => G.ev i = false).card * ε) where
  ext := E.ext
  Bad := E.Bad
  simKey_cls _ _ _ _ _ _ _ := rfl
  bad_le := E.bad_le
  simBad_le := E.simBad_le
  sound := E.sound

end Protocol

section Reduction

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
  {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞}

/-- The instrumented simulated run on the statement `x` with the bad predicate of a
class-wise log extractor, the challenger's verifier queries included. -/
noncomputable def slRunCls (E : G.LogExtractorCls rel N κ ε εS) {qH qS : ℕ}
    (A : G.Adversary qH qS) (x : G.Stmt) : PMF (G.Forgery × SLState G) :=
  OracleAdv.run (toOracle (slStep N E.Bad x)) (withVerify x (A.run x))
    ((Protocol.Tables.empty, false), false)

/-- **The class-wise straight-line reduction.** On the statement `x`, run the
instrumented simulated game once and apply the extractor to the final tables and
the forgery. -/
noncomputable def slReductionCls (E : G.LogExtractorCls rel N κ ε εS) {qH qS : ℕ}
    (A : G.Adversary qH qS) : G.Stmt → PMF G.Wit :=
  fun x => (slRunCls E A x).map fun y => E.ext x y.2.1.1 y.1

/-- The class-wise reduction of a log extractor viewed as a class-wise one is its
straight-line reduction. -/
theorem slReductionCls_toCls {ε : ℝ≥0∞} (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (A : G.Adversary qH qS) : slReductionCls E.toCls A = slReduction E A := rfl

end Reduction

/-! ## The extraction flag by classes -/

section Flag

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
  {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞} {α : Type}

/-- The evaluated entry `i` of a simulated signing attempt from the tables `t`
satisfies `slEvalBadAt` with probability at most `ε (ecls i)` when it is evaluated,
and never otherwise. -/
theorem slEvalBadAt_le_cls (E : G.LogExtractorCls rel N κ ε εS) (x : G.Stmt)
    (t : G.Tables) (m : G.Msg) (s : G.SimRand) (i : Fin G.μ) :
    (PMF.uniformFintype (Fin G.μ → G.Ch)).toOuterMeasure
        {e | slEvalBadAt N E.Bad x t m e s i = true} ≤ if G.ev i then ε (κ.ecls i) else 0 := by
  cases hi : G.ev i with
  | false =>
    simp only [Bool.false_eq_true, ite_false, nonpos_iff_eq_zero]
    refine MeasureTheory.measure_mono_null (fun e he => ?_) MeasureTheory.measure_empty
    simp [slEvalBadAt, Protocol.simKey_eq_none_of_ev_false x m s _ hi] at he
  | true =>
    simp only [ite_true]
    let B : Option G.Key × List (G.Key × G.Ch) → G.Ch → Bool := fun z c =>
      match z.1 with
      | some k => decide (κ.cls k = κ.ecls i) && ((t.lookup k).isNone &&
          (decide ((hashAll t z.2).size ≤ N) && E.Bad x (hashAll t z.2) k c))
      | none => false
    have hset : {e | slEvalBadAt N E.Bad x t m e s i = true} =
        {e | B (G.simKey x m s (G.simVals t.lookup x m s e) i,
          G.simTraceBefore t.lookup x m e s i) (e i) = true} := by
      ext e
      simp only [Set.mem_ofPred_eq, slEvalBadAt, B]
      cases hk : G.simKey x m s (G.simVals t.lookup x m s e) i with
      | none => rfl
      | some k =>
        have hc := E.simKey_cls x m s _ i k hk
        cases hl : t.lookup k with
        | some _ => simp [hl]
        | none =>
          rw [Protocol.simVals_apply t.lookup x m s e i, hk]
          simp [hl, hc]
    rw [hset]
    refine uniform_pi_le_of_update_invariant i _ (fun e c => ?_) B fun z => ?_
    · rw [Protocol.simKey_update hi e c i le_rfl, Protocol.simTraceBefore_update hi e c]
    · obtain ⟨k, l⟩ := z
      cases k with
      | none => simp [B]
      | some k =>
        by_cases hc : κ.cls k = κ.ecls i
        · by_cases hl : (t.lookup k).isNone = true
          · by_cases hN : (hashAll t l).size ≤ N
            · simpa [B, hc, hl, hN] using E.bad_le x (hashAll t l) k hN
            · simp [B, hN]
          · simp [B, hl]
        · simp [B, hc]

/-- The evaluated entries of a simulated signing attempt from the tables `t` contain
one satisfying `slEvalBadAt` with probability at most `Σ_c μe c·ε c`. -/
theorem slEvalBad_le_cls (E : G.LogExtractorCls rel N κ ε εS) (x : G.Stmt) (t : G.Tables)
    (m : G.Msg) (s : G.SimRand) :
    (PMF.uniformFintype (Fin G.μ → G.Ch)).toOuterMeasure
        {e | (List.finRange G.μ).any (slEvalBadAt N E.Bad x t m e s) = true} ≤
      ∑ c, (κ.μe c : ℝ≥0∞) * ε c := by
  calc _ ≤ (PMF.uniformFintype (Fin G.μ → G.Ch)).toOuterMeasure
          (⋃ i, {e | slEvalBadAt N E.Bad x t m e s i = true}) :=
        MeasureTheory.measure_mono fun e he => by simpa using he
    _ ≤ ∑' i, (PMF.uniformFintype (Fin G.μ → G.Ch)).toOuterMeasure
          {e | slEvalBadAt N E.Bad x t m e s i = true} := MeasureTheory.measure_iUnion_le _
    _ ≤ ∑ i, if G.ev i then ε (κ.ecls i) else 0 := by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun i _ => slEvalBadAt_le_cls E x t m s i
    _ = _ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
          ← Finset.sum_fiberwise _ κ.ecls]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2],
          Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
        rfl

/-- The class costs of a query for the instrumented game: for the class `c`, one
for a hash query at a point of class `c` and `μe c` for a signing query; for `none`,
one for a signing query. -/
def slCostCls (κ : G.Classes) : Option κ.ι → G.Query → ℕ
  | some c => fun d => κ.hashCost c d + Sum.elim (fun _ => 0) (fun _ => κ.μe c) d
  | none => Sum.elim (fun _ => 0) fun _ => 1

/-- The bad-answer probabilities of the class costs: `ε c` for the class `c` and
`εS` for `none`. -/
def slEpsCls (ε : κ.ι → ℝ≥0∞) (εS : ℝ≥0∞) : Option κ.ι → ℝ≥0∞
  | some c => ε c
  | none => εS

/-- From a state with the extraction flag cleared, one call sets it with probability
at most `ε (cls k)` for a hash query at `k` and `Σ_c μe c·ε c + εS` for a signing
query. -/
theorem slStep_flag_le_cls (E : G.LogExtractorCls rel N κ ε εS) (x : G.Stmt)
    (s : SLState G) (d : G.Query) (hs : ¬ s.2 = true) :
    (toOracle (slStep N E.Bad x) s d).toOuterMeasure {o | o.2.2 = true} ≤
      ∑ o, (slCostCls κ o d : ℝ≥0∞) * slEpsCls ε εS o := by
  obtain ⟨⟨t, b⟩, β⟩ := s
  simp only [Bool.not_eq_true] at hs
  subst hs
  rw [Fintype.sum_option]
  cases d with
  | inl k =>
    simp only [slCostCls, slEpsCls, Protocol.Classes.hashCost, Sum.elim_inl, add_zero,
      Nat.cast_zero, zero_mul, zero_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul,
      one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [toOracle, slStep, slHashStep]
    cases t.lookup k with
    | some e => simp [Step.toPMF, PMF.toOuterMeasure_pure_apply]
    | none =>
      simp only [Step.toPMF, PMF.toOuterMeasure_map_apply]
      by_cases hN : t.size ≤ N
      · simpa [Set.preimage, hN] using E.bad_le x t k hN
      · simp [Set.preimage, hN]
  | inr m =>
    simp only [slCostCls, slEpsCls, Protocol.Classes.hashCost, Sum.elim_inr, zero_add,
      Nat.cast_one, one_mul]
    simp only [toOracle, slStep, Step.toPMF]
    have hmap : (sampleVec G (slSignOut N E.Bad x t b false m)).toOuterMeasure
        {o | o.2.2 = true} = ((sampleVec G (slSignOut N E.Bad x t b false m)).map
          fun o => o.2.2).toOuterMeasure {c | c = true} := by
      rw [PMF.toOuterMeasure_map_apply]
      rfl
    rw [hmap, sampleVec_map, add_comm]
    refine (sampleVec_or_le (fun e s => (List.finRange G.μ).any (slEvalBadAt N E.Bad x t m e s))
      (fun e s => decide (t.size ≤ N) && (G.simTrace t.lookup x m e s).2.1.any fun p =>
        E.Bad x (hashAll t (G.simTrace t.lookup x m e s).1) p.1 p.2)).trans ?_
    refine add_le_add (sampleVec_le_of_forall _ fun s' => slEvalBad_le_cls E x t m s') ?_
    by_cases hN : t.size ≤ N
    · simpa [hN] using E.simBad_le x t m hN
    · simp [hN, sampleVec, PMF.bind_const]

/-- **The extraction flag by classes.** A run whose queries cost at most `n o` for
the class costs `slCostCls κ o`, from a state with the extraction flag cleared, sets
it with probability at most `Σ_o n o·slEpsCls ε εS o`. -/
theorem run_sl_flag_le_cls (E : G.LogExtractorCls rel N κ ε εS) (x : G.Stmt)
    (A : OracleAdv G.Query G.Answer α) (n : Option κ.ι → ℕ)
    (hA : ∀ o, A.IsQueryBoundBy (slCostCls κ o) (n o)) (s : SLState G) (hs : ¬ s.2 = true) :
    (OracleAdv.run (toOracle (slStep N E.Bad x)) A s).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ o, (n o : ℝ≥0∞) * slEpsCls ε εS o :=
  OracleAdv.run_badDraw_le_sum (toOracle (slStep N E.Bad x)) (fun s => s.2 = true)
    (slCostCls κ) (slEpsCls ε εS) (slStep_flag_le_cls E x) A n hA s hs

/-- The verified run of an adversary with at most `qH` hash and `qS` signing
queries whose hash queries at points of class `c` cost at most `q c` costs at most
`q c + Vc c + μe c·qS` for the class `c` and `qS` for `none`. -/
theorem isQueryBoundBy_withVerify_slCostCls (x : G.Stmt) {qH qS : ℕ}
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) (o : Option κ.ι) :
    (withVerify x (A.run x)).IsQueryBoundBy (slCostCls κ o)
      (Option.elim o qS fun c => q c + κ.Vc c + κ.μe c * qS) := by
  have hB := isQueryBound₂_withVerify x _ qH qS (A.isQueryBound x)
  cases o with
  | none =>
    have := hB.isQueryBoundBy 0 1
    rw [zero_mul, zero_add, one_mul] at this
    exact this
  | some c =>
    have := (isQueryBoundBy_withVerify_cls κ c x _ _ (hq c)).add (hB.isQueryBoundBy 0 (κ.μe c))
    rw [zero_mul, zero_add] at this
    exact this

end Flag

/-! ## The bound -/

section Bound

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
  {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞}

/-- At one statement, winning the simulated game has probability at most the
probability that the class-wise extractor finds a witness from the instrumented run,
plus `Σ_c (q c + Vc c + μe c·qS)·ε c + qS·εS`. -/
theorem sim_wins_le_slCls (E : G.LogExtractorCls rel N κ ε εS) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) (x : G.Stmt) :
    (OracleAdv.run (toOracle (simStep x)) (withVerify x (A.run x))
        (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true} ≤
      (slReductionCls E A x).toOuterMeasure {w | rel x w} +
        (∑ c, ((q c + κ.Vc c + κ.μe c * qS : ℕ) : ℝ≥0∞) * ε c + qS * εS) := by
  have hB := isQueryBound₂_withVerify x _ qH qS (A.isQueryBound x)
  have hflag := run_sl_flag_le_cls E x _ _
    (isQueryBoundBy_withVerify_slCostCls x A q (hq x)) ((Protocol.Tables.empty, false), false)
    (by simp)
  rw [Fintype.sum_option] at hflag
  simp only [Option.elim, slEpsCls] at hflag
  have hproj := run_sl_map_fst N E.Bad x (withVerify x (A.run x))
    ((Protocol.Tables.empty, false), false)
  rw [← hproj, PMF.toOuterMeasure_map_apply, slReductionCls, PMF.toOuterMeasure_map_apply]
  refine le_trans ?_ (add_le_add le_rfl ((hflag.trans_eq (add_comm _ _))))
  rw [← PMF.toOuterMeasure_apply_inter_support]
  refine (MeasureTheory.measure_mono ?_).trans (MeasureTheory.measure_union_le _ _)
  rintro y ⟨hw, hy⟩
  by_cases hf : y.2.2 = true
  · exact Or.inr hf
  · obtain ⟨hr, hsz⟩ := run_sl_reach N E.Bad hlen x _ _ _ hB _ SLReach.empty
      (by simpa [Protocol.Tables.size, Protocol.Tables.empty] using hN) y hy
    exact Or.inl (E.sound x y.2 y.1 hr (by simpa using hf) hsz hw)

/-- The simulated-game advantage of an adversary with at most `qH` hash and `qS`
signing queries whose hash queries at points of class `c` are at most `q c` is at
most the relation advantage of `slReductionCls E A` plus
`Σ_c (q c + Vc c + μe c·qS)·ε c + qS·εS`. -/
theorem simAdvantage_le_slCls (E : G.LogExtractorCls rel N κ ε εS) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    simAdvantage A ≤ G.relAdvantage rel (slReductionCls E A) +
      (∑ c, ((q c + κ.Vc c + κ.μe c * qS : ℕ) : ℝ≥0∞) * ε c + qS * εS) := by
  unfold simAdvantage simGame
  rw [prTrue_gameDist, Protocol.relAdvantage_eq_tsum]
  calc _ ≤ ∑' xw, G.gen xw * ((slReductionCls E A xw.1).toOuterMeasure {w | rel xw.1 w} +
          (∑ c, ((q c + κ.Vc c + κ.μe c * qS : ℕ) : ℝ≥0∞) * ε c + qS * εS)) :=
        ENNReal.tsum_le_tsum fun xw =>
          mul_le_mul_right (sim_wins_le_slCls E hN hlen A q hq xw.1) _
    _ = _ := by
        generalize (∑ c, ((q c + κ.Vc c + κ.μe c * qS : ℕ) : ℝ≥0∞) * ε c + qS * εS) = K
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **EUF-CMA security of Fiat–Shamir signatures by class-wise straight-line
extraction.** For a protocol `G` with key classes `κ` whose simulated traces have at
most `μ` evaluated and programmed entries, generated pairs with statistical HVZK
distance `δ (x, w)` and class-wise key bound `Γ (x, w)`, a class-wise log extractor
`E` for `rel` on tables with at most `N ≥ qH + V + μ·qS` entries with bad-answer
probabilities `ε c` and programmed-entry bound `εS`, and every adversary `A` with
at most `qH` hash and `qS` signing queries whose hash queries at points of class `c`
are at most `q c` on every path,

`eufcmaAdvantage A ≤ relAdvantage (slReductionCls E A)
  + Σ_c (q c + Vc c + μe c·qS)·ε c + qS·εS
  + E_{(x,w) ← gen}[qS·δ(x, w) + Σ_c qS·(q c + Vc c + μc c·qS)·Γ(x, w) c]`. -/
theorem fiatShamir_rom_eufcma_slCls (E : G.LogExtractorCls rel N κ ε εS) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    {δ : G.Stmt × G.Wit → ℝ≥0∞} {Γ : G.Stmt × G.Wit → κ.ι → ℝ≥0∞}
    (hZK : ∀ xw ∈ G.gen.support, G.StatHVZKAt xw.1 xw.2 (δ xw))
    (hΓ : ∀ xw ∈ G.gen.support, G.KeyBoundClsAt κ xw.1 xw.2 (Γ xw))
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    eufcmaAdvantage A ≤ G.relAdvantage rel (slReductionCls E A) +
      (∑ c, ((q c + κ.Vc c + κ.μe c * qS : ℕ) : ℝ≥0∞) * ε c + qS * εS) +
      ∑' xw, G.gen xw * (qS * δ xw +
        ∑ c, ((qS * (q c + κ.Vc c + κ.μc c * qS) : ℕ) : ℝ≥0∞) * Γ xw c) :=
  (Protocol.eufcmaAdvantage_le_simAdvantage_cls κ hZK hΓ A q hq).trans
    (add_le_add (simAdvantage_le_slCls E hN hlen A q hq) le_rfl)

end Bound

/-! ## The bound for a log extractor -/

section PerKey

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {ε : ℝ≥0∞}

/-- The evaluated entries of an attempt in the single class are the evaluated
entries. -/
@[simp] theorem Protocol.Classes.unit_μe :
    (Protocol.Classes.unit G).μe () = (Finset.univ.filter fun i => G.ev i = true).card := by
  simp [Protocol.Classes.μe]

/-- The extraction terms of `E.toCls` for the single class are `(qH + V + μ·qS)·ε`. -/
theorem Protocol.LogExtractor.toCls_flagBound_eq (qH qS : ℕ) :
    ∑ c, ((qH + (Protocol.Classes.unit G).Vc c + (Protocol.Classes.unit G).μe c * qS : ℕ) :
        ℝ≥0∞) * ε + qS * ((Finset.univ.filter fun i => G.ev i = false).card * ε) =
      ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε := by
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin G.μ => G.ev i = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Fintype.sum_unique, Protocol.Classes.unit_Vc, Protocol.Classes.unit_μe, ← mul_assoc,
    ← add_mul]
  congr 1
  rw [show G.μ * qS = (Finset.univ.filter fun i => G.ev i = true).card * qS +
    (Finset.univ.filter fun i => G.ev i = false).card * qS by rw [← add_mul, hcard]]
  push_cast
  ring

/-- An adversary with at most `qH` hash queries asks at most `qH` hash queries in
the single class. -/
theorem Protocol.Adversary.isQueryBoundBy_hashCost_unit {qH qS : ℕ} (A : G.Adversary qH qS)
    (x : G.Stmt) (c : (Protocol.Classes.unit G).ι) :
    (A.run x).IsQueryBoundBy ((Protocol.Classes.unit G).hashCost c) qH :=
  (A.isQueryBound x).isQueryBoundBy_left (fun _ => by simp [Protocol.Classes.hashCost])
    fun _ => rfl

/-- At one statement, winning the simulated game has probability at most the
probability that the extractor finds a witness from the instrumented run, plus
`(qH + V + μ·qS)·ε`. -/
theorem sim_wins_le_sl (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    (A : G.Adversary qH qS) (x : G.Stmt) :
    (OracleAdv.run (toOracle (simStep x)) (withVerify x (A.run x))
        (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true} ≤
      (slReduction E A x).toOuterMeasure {w | rel x w} +
        ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε := by
  have h := sim_wins_le_slCls E.toCls hN hlen A (fun _ => qH) A.isQueryBoundBy_hashCost_unit x
  rwa [slReductionCls_toCls, Protocol.LogExtractor.toCls_flagBound_eq] at h

/-- The simulated-game advantage of an adversary with at most `qH` hash and `qS`
signing queries is at most the relation advantage of `slReduction E A` plus
`(qH + V + μ·qS)·ε`. -/
theorem simAdvantage_le_sl (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    (A : G.Adversary qH qS) :
    simAdvantage A ≤ G.relAdvantage rel (slReduction E A) +
      ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε := by
  have h := simAdvantage_le_slCls E.toCls hN hlen A (fun _ => qH) A.isQueryBoundBy_hashCost_unit
  rwa [slReductionCls_toCls, Protocol.LogExtractor.toCls_flagBound_eq] at h

/-- **EUF-CMA security of Fiat–Shamir signatures by straight-line extraction.** For
a protocol `G` whose simulated traces have at most `μ` evaluated and programmed
entries, generated pairs with statistical HVZK distance `δ (x, w)` and key bound
`γ (x, w)`, a log extractor `E` for `rel` on tables with at most `N ≥ qH + V + μ·qS`
entries with bad-answer probability `ε`, and every adversary `A` with at most `qH`
hash and `qS` signing queries,

`eufcmaAdvantage A ≤ relAdvantage (slReduction E A) + (qH + V + μ·qS)·ε
  + E_{(x,w) ← gen}[qS·δ(x, w) + qS·(qH + V + μ·qS)·γ(x, w)]`,

where `slReduction E A` runs the instrumented simulated game once and applies the
extractor to the final tables and the forgery. -/
theorem fiatShamir_rom_eufcma_sl (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    {δ γ : G.Stmt × G.Wit → ℝ≥0∞}
    (hZK : ∀ xw ∈ G.gen.support, G.StatHVZKAt xw.1 xw.2 (δ xw))
    (hγ : ∀ xw ∈ G.gen.support, G.KeyBoundAt xw.1 xw.2 (γ xw)) (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤ G.relAdvantage rel (slReduction E A) +
      ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε +
      ∑' xw, G.gen xw * (qS * δ xw +
        ((qS * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * γ xw) :=
  (Protocol.eufcmaAdvantage_le_simAdvantage_perKey hZK hγ A).trans
    (add_le_add (simAdvantage_le_sl E hN hlen A) le_rfl)

/-- **Straight-line extraction with key classes.** For a protocol `G` with key
classes `κ` whose simulated traces have at most `μ` evaluated and programmed
entries, generated pairs with statistical HVZK distance `δ (x, w)` and class-wise
key bound `Γ (x, w)`, a log extractor `E` for `rel` on tables with at most
`N ≥ qH + V + μ·qS` entries with bad-answer probability `ε`, and every adversary `A`
with at most `qH` hash and `qS` signing queries whose hash queries at points of
class `c` are at most `q c` on every path,

`eufcmaAdvantage A ≤ relAdvantage (slReduction E A) + (qH + V + μ·qS)·ε
  + E_{(x,w) ← gen}[qS·δ(x, w) + Σ_c qS·(q c + Vc c + μc c·qS)·Γ(x, w) c]`. -/
theorem fiatShamir_rom_eufcma_sl_cls (E : G.LogExtractor rel N ε) (κ : G.Classes)
    {qH qS : ℕ} (hN : qH + G.V + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    {δ : G.Stmt × G.Wit → ℝ≥0∞} {Γ : G.Stmt × G.Wit → κ.ι → ℝ≥0∞}
    (hZK : ∀ xw ∈ G.gen.support, G.StatHVZKAt xw.1 xw.2 (δ xw))
    (hΓ : ∀ xw ∈ G.gen.support, G.KeyBoundClsAt κ xw.1 xw.2 (Γ xw))
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    eufcmaAdvantage A ≤ G.relAdvantage rel (slReduction E A) +
      ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε +
      ∑' xw, G.gen xw * (qS * δ xw +
        ∑ c, ((qS * (q c + κ.Vc c + κ.μc c * qS) : ℕ) : ℝ≥0∞) * Γ xw c) :=
  (Protocol.eufcmaAdvantage_le_simAdvantage_cls κ hZK hΓ A q hq).trans
    (add_le_add (simAdvantage_le_sl E hN hlen A) le_rfl)

/-- **Straight-line extraction with statistical HVZK.** With HVZK distance `δ` and
key bound `γ` at every generated pair, the bound of `fiatShamir_rom_eufcma_sl` is
`relAdvantage (slReduction E A) + (qH + V + μ·qS)·ε + qS·δ + qS·(qH + V + μ·qS)·γ`. -/
theorem fiatShamir_rom_eufcma_sl_stat (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    {δ : ℝ≥0∞} (hZK : G.StatHVZK δ) {γ : ℝ≥0∞} (hγ : G.KeyBound γ)
    (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤ G.relAdvantage rel (slReduction E A) +
      ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε +
      (qS * δ + ((qS * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * γ) := by
  refine (fiatShamir_rom_eufcma_sl E hN hlen (δ := fun _ => δ) (γ := fun _ => γ)
    (fun xw hxw => hZK xw.1 xw.2 hxw) (fun xw hxw => hγ xw.1 xw.2 hxw) A).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end PerKey

end CatCrypt.Crypto.FiatShamirROM

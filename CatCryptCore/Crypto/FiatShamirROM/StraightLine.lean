/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.StatHVZK
public import CatCryptCore.Crypto.OracleBadDraw

/-!
# Fiat–Shamir in the random-oracle model: straight-line extraction from the oracle log

EUF-CMA security of the Fiat–Shamir signatures of a protocol `G : Protocol` whose
witness is extracted from the random-oracle log of one run, without rewinding. A
log extractor (`Protocol.LogExtractor G rel N ε`) gives a witness from the
statement, the final tables and the forgery, and a predicate `Bad x t k e` on a
fresh oracle answer `e` at the point `k` given the tables `t` before it. Each fresh
oracle answer satisfies `Bad` with probability at most `ε`, and the entries
programmed by one simulated signing attempt with probability at most `ε` times the
number of programmed entries, for tables with at most `N` entries.

The instrumented simulated game (`slStep`) runs the simulated oracle of
`FiatShamirROM.Game` and sets an extraction flag when a fresh answer of a hash
query, a fresh answer of an oracle query of the simulator, or an entry programmed
by a simulated signing attempt satisfies `Bad` given the tables before it. A fresh
answer of the simulator is checked like a hash query (`slEvalBadAt`): the
coordinate of the sampled values that gives it is independent of its point and of
the earlier entries (`uniform_pi_le_of_update_invariant`). Extraction is sound when,
at every state reachable through calls from tables with at most `N` entries
(`SLReach`) whose tables have at most `N` entries, a winning forgery
with the extraction flag cleared gives a witness of the relation. The reduction
`slReduction E A` runs the instrumented game once on the statement and applies the
extractor to the final tables and the forgery.

## Main definitions

* `slEvalBadAt N Bad x t m e s i` — the extraction flag of the evaluated entry `i` of
  a simulated signing attempt
* `slStep N Bad x` — the simulated oracle with the extraction flag
* `SLReach N Bad x` — the states reachable by calls from tables with at most `N`
  entries
* `Protocol.LogExtractor G rel N ε` — a log extractor for the relation `rel`
* `Protocol.relGame`, `Protocol.relAdvantage` — the relation game against a
  witness finder and its advantage
* `slReduction E A` — the reduction running the instrumented game once and
  applying the extractor

## Main results

* `run_sl_map_fst` — forgetting the extraction flag maps the instrumented run to the
  run of the simulated game
* `slEvalBad_le` — the evaluated entries of a simulated signing attempt set the
  extraction flag with probability at most `ε` times their number
* `run_sl_flag_le` — a run with at most `h` hash and `q` signing queries sets the
  extraction flag with probability at most `(h + μ·q)·ε`
* `fiatShamir_rom_eufcma_sl` — for every adversary with at most `qH` hash and `qS`
  signing queries, the EUF-CMA advantage is at most the relation advantage of
  `slReduction E A`, plus `(qH + V + μ·qS)·ε`, plus the signing-hop terms of
  `Protocol.eufcmaAdvantage_le_simAdvantage_perKey`
* `fiatShamir_rom_eufcma_sl_stat` — the same with constant HVZK distance and key
  bound

## References

* C. Baum, L. Braun, C. Delpech de Saint Guilhem, M. Klooß, E. Orsini, L. Roy,
  P. Scholl, *Publicly verifiable zero-knowledge and post-quantum signatures from
  VOLE-in-the-head*, CRYPTO 2023.
* M. Fischlin, *Communication-efficient non-interactive proofs of knowledge with
  online extractors*, CRYPTO 2005.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

/-! ## The instrumented simulated game -/

section Instrumented

variable {G : Protocol}

variable (G) in
/-- The state of the instrumented simulated game: the challenger's state and the
extraction flag. -/
abbrev SLState := (G.Tables × Bool) × Bool

/-- A hash query of the instrumented game: `hashStep`, with the extraction flag set
when the tables have at most `N` entries and a fresh value `e` satisfies
`Bad x t k e`. -/
noncomputable def slHashStep (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) (t : G.Tables) (b β : Bool) (k : G.Key) :
    Step G.Answer (SLState G) G.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, ((t, b), β)))
  | none => .fresh fun e =>
    (.inl e, (({ t with hash := t.hash ++ [(k, e)] }, b), β || (decide (t.size ≤ N) && Bad x t k e)))

/-- The evaluated entries of the simulated attempt against `look` before the entry
`i`, with their points and values. -/
def Protocol.simTraceBefore (look : G.Key → Option G.Ch) (x : G.Stmt) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (s : G.SimRand) (i : Fin G.μ) : List (G.Key × G.Ch) :=
  ((List.finRange G.μ).filter fun j => decide (j < i)).filterMap fun j =>
    (G.simKey x m s (G.simVals look x m s e) j).map fun k => (k, G.simVals look x m s e j)

/-- The extraction flag of the entry `i` of a simulated signing attempt from the
tables `t`: the entry has a simulator point `k` undefined in `t`, and its value `c`
satisfies `Bad x u k c` for the tables `u` after the evaluated entries before `i`,
when `u` has at most `N` entries. -/
def slEvalBadAt (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt)
    (t : G.Tables) (m : G.Msg) (e : Fin G.μ → G.Ch) (s : G.SimRand) (i : Fin G.μ) : Bool :=
  match G.simKey x m s (G.simVals t.lookup x m s e) i with
  | some k => (t.lookup k).isNone &&
      (decide ((hashAll t (G.simTraceBefore t.lookup x m e s i)).size ≤ N) &&
        Bad x (hashAll t (G.simTraceBefore t.lookup x m e s i)) k (G.simVals t.lookup x m s e i))
  | none => false

/-- A signing attempt of the instrumented game: `simSignOut`, with the extraction flag
set when an evaluated entry of the simulated trace satisfies `slEvalBadAt`, or when
the tables `t` have at most `N` entries and a programmed entry `(k, c)` of the
simulated trace satisfies `Bad x u k c` for the tables `u` after the evaluated
entries. -/
def slSignOut (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt)
    (t : G.Tables) (b β : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch) (s : G.SimRand) :
    G.Answer × SLState G :=
  ((simSignOut x t b m e s).1, ((simSignOut x t b m e s).2,
    β || (List.finRange G.μ).any (slEvalBadAt N Bad x t m e s) ||
      (decide (t.size ≤ N) && (G.simTrace t.lookup x m e s).2.1.any fun p =>
        Bad x (hashAll t (G.simTrace t.lookup x m e s).1) p.1 p.2)))

/-- The simulated oracle for the statement `x` with the extraction flag. -/
noncomputable def slStep (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) (s : SLState G) : G.Query → Step G.Answer (SLState G) G.Ch
  | .inl k => slHashStep N Bad x s.1.1 s.1.2 s.2 k
  | .inr m => .plain (sampleVec G (slSignOut N Bad x s.1.1 s.1.2 s.2 m))

/-- The states of the instrumented game reachable from the empty tables by calls
from states whose tables have at most `N` entries. -/
inductive SLReach (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt) :
    SLState G → Prop
  | empty : SLReach N Bad x ((Protocol.Tables.empty, false), false)
  | step (s : SLState G) (d : G.Query) (o : G.Answer × SLState G) :
    SLReach N Bad x s → s.1.1.size ≤ N → o ∈ (toOracle (slStep N Bad x) s d).support →
      SLReach N Bad x o.2

end Instrumented

/-! ## Log extractors and the reduction -/

namespace Protocol

variable (G : Protocol)

/-- **Log extractor** for the relation `rel` on tables with at most `N` entries and
bad-answer probability `ε`. The extractor `ext` reads the statement, the tables and
the forgery. A fresh oracle answer satisfies `Bad` with probability at most `ε`, and
the programmed entries of one simulated signing attempt with probability at most
`ε` times the number of programmed entries, for tables with at most `N` entries. At
every reachable state with at most `N` table entries and the extraction flag
cleared, a winning forgery gives a witness. -/
structure LogExtractor (rel : G.Stmt → G.Wit → Prop) (N : ℕ) (ε : ℝ≥0∞) where
  /-- The extractor on the statement, the final tables and the forgery. -/
  ext : G.Stmt → G.Tables → G.Forgery → G.Wit
  /-- The fresh answer `e` at the point `k` is bad given the tables `t`. -/
  Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool
  /-- A uniform answer is bad with probability at most `ε`. -/
  bad_le : ∀ x t k, t.size ≤ N →
    (PMF.uniformOfFintype G.Ch).toOuterMeasure {e | Bad x t k e = true} ≤ ε
  /-- The programmed entries of a simulated attempt from the tables `t` on uniform
  values and simulator randomness contain an entry that is bad given the tables after
  the evaluated entries with probability at most `ε` times the number of programmed
  entries. -/
  simBad_le : ∀ x t m, t.size ≤ N →
    (sampleVec G fun e (s : G.SimRand) =>
      (G.simTrace t.lookup x m e s).2.1.any fun p =>
        Bad x (hashAll t (G.simTrace t.lookup x m e s).1) p.1 p.2).toOuterMeasure
        {c | c = true} ≤ (Finset.univ.filter fun i => G.ev i = false).card * ε
  /-- On tables with at most `N` entries and without the extraction flag, a winning
  forgery gives a witness. -/
  sound : ∀ x (s : SLState G) (f : G.Forgery), SLReach N Bad x s → s.2 = false →
    s.1.1.size ≤ N → wins x (f, s.1) = true → rel x (ext x s.1.1 f)

open Classical in
/-- The relation game for `rel`: sample `(x, w) ← G.gen`, run `B` on `x`, and check
that its output is a witness for `x`. -/
noncomputable def relGame (rel : G.Stmt → G.Wit → Prop) (B : G.Stmt → PMF G.Wit) :
    SPComp Bool :=
  PRPPRF.pmfGame (G.gen.bind fun xw => (B xw.1).map fun w' => decide (rel xw.1 w'))

/-- The advantage in the relation game for `rel`. -/
noncomputable def relAdvantage (rel : G.Stmt → G.Wit → Prop) (B : G.Stmt → PMF G.Wit) :
    ℝ≥0∞ :=
  prTrue (G.relGame rel B) Heap.empty

end Protocol

section Reduction

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {ε : ℝ≥0∞}

/-- The instrumented simulated run on the statement `x`, the challenger's verifier
queries included. -/
noncomputable def slRun (E : G.LogExtractor rel N ε) {qH qS : ℕ} (A : G.Adversary qH qS)
    (x : G.Stmt) : PMF (G.Forgery × SLState G) :=
  OracleAdv.run (toOracle (slStep N E.Bad x)) (withVerify x (A.run x))
    ((Protocol.Tables.empty, false), false)

/-- **The straight-line reduction.** On the statement `x`, run the instrumented
simulated game once and apply the extractor to the final tables and the forgery. -/
noncomputable def slReduction (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (A : G.Adversary qH qS) : G.Stmt → PMF G.Wit :=
  fun x => (slRun E A x).map fun y => E.ext x y.2.1.1 y.1

end Reduction

/-! ## The instrumented game projects to the simulated game -/

section Project

variable {G : Protocol} {α : Type}

theorem programAll_size (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch)) :
    (programAll t b l).1.size ≤ t.size + l.length := by
  induction l generalizing t b with
  | nil => simp [programAll]
  | cons p l ih =>
    unfold programAll
    split
    · have := ih t true
      simp only [List.length_cons]
      omega
    · have := ih { t with prog := t.prog ++ [p] } b
      simp only [Protocol.Tables.size, List.length_append, List.length_cons,
        List.length_nil] at this ⊢
      omega

theorem sampleVec_map {β γ δ : Type} [Fintype β] [Nonempty β]
    (F : (Fin G.μ → G.Ch) → β → γ) (g : γ → δ) :
    (sampleVec G F).map g = sampleVec G fun e y => g (F e y) := by
  simp only [sampleVec, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem slStep_map_fst (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) (s : SLState G) (d : G.Query) :
    (toOracle (slStep N Bad x) s d).map (Prod.map id Prod.fst) = toOracle (simStep x) s.1 d := by
  cases d with
  | inl k =>
    simp only [toOracle, slStep, simStep, slHashStep, hashStep]
    cases s.1.1.lookup k with
    | some e => simp [Step.toPMF, PMF.pure_map]
    | none => simp only [Step.toPMF, PMF.map_comp]; rfl
  | inr m =>
    simp only [toOracle, slStep, simStep, Step.toPMF, sampleVec_map]
    rfl

/-- Forgetting the extraction flag maps the instrumented run to the run of the
simulated game. -/
theorem run_sl_map_fst (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) (A : OracleAdv G.Query G.Answer α) (s : SLState G) :
    (OracleAdv.run (toOracle (slStep N Bad x)) A s).map (Prod.map id Prod.fst) =
      OracleAdv.run (toOracle (simStep x)) A s.1 :=
  OracleAdv.run_map_state _ _ Prod.fst (slStep_map_fst N Bad x) A s

end Project

/-! ## The evaluated entries of a simulated attempt -/

section Evaluated

/-- **One coordinate of a uniform vector.** If `F` does not read the coordinate `i`
and, for every `z`, a uniform value satisfies `B z` with probability at most `ε`,
then a uniform vector `e` satisfies `B (F e) (e i)` with probability at most `ε`. -/
theorem uniform_pi_le_of_update_invariant {ι C Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype C] [Nonempty C] (i : ι) (F : (ι → C) → Z)
    (hF : ∀ e c, F (Function.update e i c) = F e) (B : Z → C → Bool) {ε : ℝ≥0∞}
    (hB : ∀ z, (PMF.uniformOfFintype C).toOuterMeasure {c | B z c = true} ≤ ε) :
    (PMF.uniformOfFintype (ι → C)).toOuterMeasure {e | B (F e) (e i) = true} ≤ ε := by
  rw [← Constructions.ECBCPRF.uniform_bind_update i, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' e, PMF.uniformOfFintype (ι → C) e * ε := by
        refine ENNReal.tsum_le_tsum fun e => ?_
        gcongr
        rw [PMF.toOuterMeasure_map_apply]
        refine le_of_eq_of_le ?_ (hB (F e))
        congr 1
        ext c
        simp [hF]
    _ = ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Sampling the values before the independent value of `β` bounds the probability
of an event by its bound at every value of `β`. -/
theorem sampleVec_le_of_forall {G : Protocol} {β : Type} [Fintype β] [Nonempty β]
    (F : (Fin G.μ → G.Ch) → β → Bool) {c : ℝ≥0∞}
    (h : ∀ y, (PMF.uniformOfFintype (Fin G.μ → G.Ch)).toOuterMeasure {e | F e y = true} ≤ c) :
    (sampleVec G F).toOuterMeasure {b | b = true} ≤ c := by
  have hc : sampleVec G F = (PMF.uniformOfFintype β).bind fun y =>
      (PMF.uniformOfFintype (Fin G.μ → G.Ch)).map fun e => F e y := by
    simp only [sampleVec, PMF.map]
    exact PMF.bind_comm _ _ _
  rw [hc, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' y, PMF.uniformOfFintype β y * c := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        gcongr
        rw [PMF.toOuterMeasure_map_apply]
        exact h y
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The probability that one of two events holds is at most the sum of their
probabilities. -/
theorem sampleVec_or_le {G : Protocol} {β : Type} [Fintype β] [Nonempty β]
    (a b : (Fin G.μ → G.Ch) → β → Bool) :
    (sampleVec G fun e y => a e y || b e y).toOuterMeasure {c | c = true} ≤
      (sampleVec G a).toOuterMeasure {c | c = true} +
        (sampleVec G b).toOuterMeasure {c | c = true} := by
  have hF : ∀ F : (Fin G.μ → G.Ch) → β → Bool, sampleVec G F =
      (sampleVec G fun e y => (e, y)).map fun p => F p.1 p.2 := fun F =>
    (sampleVec_map (fun e y => (e, y)) fun p => F p.1 p.2).symm
  rw [hF, hF a, hF b]
  simp only [PMF.toOuterMeasure_map_apply]
  refine (MeasureTheory.measure_mono fun p hp => ?_).trans (MeasureTheory.measure_union_le _ _)
  simpa [Bool.or_eq_true] using hp

namespace Protocol

variable {G : Protocol} (look : G.Key → Option G.Ch) (x : G.Stmt) (m : G.Msg)
  (s : G.SimRand)

theorem simKey_eq_none_of_ev_false (v : Fin G.μ → G.Ch) {i : Fin G.μ} (h : G.ev i = false) :
    G.simKey x m s v i = none := by
  cases hk : G.simKey x m s v i with
  | none => rfl
  | some k =>
    have := G.simKey_ev x m s v i (by simp [hk])
    simp [h] at this

/-- A programmed entry of a simulated attempt takes its sampled value. -/
theorem simVals_apply_of_ev_false (e : Fin G.μ → G.Ch) {i : Fin G.μ} (h : G.ev i = false) :
    G.simVals look x m s e i = e i := by
  change effVal _ _ e i = e i
  rw [effVal, simKey_eq_none_of_ev_false x m s _ h]
  rfl

/-- The value of the entry `i` of a simulated attempt is the value of `look` at its
simulator point when defined, and its sampled value otherwise. -/
theorem simVals_apply (e : Fin G.μ → G.Ch) (i : Fin G.μ) :
    G.simVals look x m s e i =
      ((G.simKey x m s (G.simVals look x m s e) i).bind look).getD (e i) := by
  change effVal _ _ e i = _
  rw [effVal]
  congr 2
  refine G.simKey_causal x m s _ _ i fun j hj => ?_
  by_cases hji : j < i
  · simp only [hji, if_true]
    rfl
  · simp only [hji, if_false]
    exact (simVals_apply_of_ev_false look x m s e (hj.resolve_left hji)).symm

variable {look x m s}

/-- Changing the sampled value of an evaluated entry `i` changes no value of a
programmed entry or of an entry before `i`. -/
theorem simVals_update_apply {i : Fin G.μ} (hi : G.ev i = true) (e : Fin G.μ → G.Ch)
    (c : G.Ch) (j : Fin G.μ) (hj : j < i ∨ G.ev j = false) :
    G.simVals look x m s (Function.update e i c) j = G.simVals look x m s e j := by
  have hprog : ∀ j', G.ev j' = false →
      G.simVals look x m s (Function.update e i c) j' = G.simVals look x m s e j' := by
    intro j' hj'
    have hne : j' ≠ i := by
      rintro rfl
      simp [hi] at hj'
    rw [simVals_apply_of_ev_false look x m s _ hj', simVals_apply_of_ev_false look x m s _ hj',
      Function.update_of_ne hne]
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    rcases hj with hj | hj
    · rw [simVals_apply look x m s (Function.update e i c) j, simVals_apply look x m s e j,
        Function.update_of_ne (ne_of_lt hj)]
      congr 2
      refine G.simKey_causal x m s _ _ j fun j' hj' => ?_
      rcases hj' with hj' | hj'
      · exact ih j' hj' (Or.inl (lt_trans hj' hj))
      · exact hprog j' hj'
    · exact hprog j hj

/-- Changing the sampled value of an evaluated entry `i` changes neither the simulator
point of an entry `j ≤ i` nor the evaluated entries before `i`. -/
theorem simKey_update {i : Fin G.μ} (hi : G.ev i = true) (e : Fin G.μ → G.Ch) (c : G.Ch)
    (j : Fin G.μ) (hj : j ≤ i) :
    G.simKey x m s (G.simVals look x m s (Function.update e i c)) j =
      G.simKey x m s (G.simVals look x m s e) j :=
  G.simKey_causal x m s _ _ j fun j' hj' =>
    simVals_update_apply hi e c j' (hj'.imp_left fun h => lt_of_lt_of_le h hj)

theorem simTraceBefore_update {i : Fin G.μ} (hi : G.ev i = true) (e : Fin G.μ → G.Ch)
    (c : G.Ch) :
    G.simTraceBefore look x m (Function.update e i c) s i = G.simTraceBefore look x m e s i := by
  refine List.filterMap_congr fun j hj => ?_
  have hji : j < i := by simpa using (List.mem_filter.mp hj).2
  rw [simKey_update hi e c j hji.le, simVals_update_apply hi e c j (Or.inl hji)]

end Protocol

variable {G : Protocol}

/-- The evaluated entry `i` of a simulated signing attempt from the tables `t`
satisfies `slEvalBadAt` with probability at most `ε` when it is evaluated, and never
otherwise. -/
theorem slEvalBadAt_le {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {ε : ℝ≥0∞}
    (E : G.LogExtractor rel N ε) (x : G.Stmt) (t : G.Tables) (m : G.Msg) (s : G.SimRand)
    (i : Fin G.μ) :
    (PMF.uniformOfFintype (Fin G.μ → G.Ch)).toOuterMeasure
        {e | slEvalBadAt N E.Bad x t m e s i = true} ≤ if G.ev i then ε else 0 := by
  cases hi : G.ev i with
  | false =>
    simp only [Bool.false_eq_true, if_false, nonpos_iff_eq_zero]
    refine MeasureTheory.measure_mono_null (fun e he => ?_) MeasureTheory.measure_empty
    simp [slEvalBadAt, Protocol.simKey_eq_none_of_ev_false x m s _ hi] at he
  | true =>
    simp only [if_true]
    let B : Option G.Key × List (G.Key × G.Ch) → G.Ch → Bool := fun z c =>
      match z.1 with
      | some k => (t.lookup k).isNone &&
          (decide ((hashAll t z.2).size ≤ N) && E.Bad x (hashAll t z.2) k c)
      | none => false
    have hset : {e | slEvalBadAt N E.Bad x t m e s i = true} =
        {e | B (G.simKey x m s (G.simVals t.lookup x m s e) i,
          G.simTraceBefore t.lookup x m e s i) (e i) = true} := by
      ext e
      simp only [Set.mem_ofPred_eq, slEvalBadAt, B]
      cases hk : G.simKey x m s (G.simVals t.lookup x m s e) i with
      | none => rfl
      | some k =>
        cases hl : t.lookup k with
        | some _ => simp [hl]
        | none =>
          rw [Protocol.simVals_apply t.lookup x m s e i, hk]
          simp [hl]
    rw [hset]
    refine uniform_pi_le_of_update_invariant i _ (fun e c => ?_) B fun z => ?_
    · rw [Protocol.simKey_update hi e c i le_rfl, Protocol.simTraceBefore_update hi e c]
    · obtain ⟨k, l⟩ := z
      cases k with
      | none => simp [B]
      | some k =>
        by_cases hl : (t.lookup k).isNone = true
        · by_cases hN : (hashAll t l).size ≤ N
          · simpa [B, hl, hN] using E.bad_le x (hashAll t l) k hN
          · simp [B, hN]
        · simp [B, hl]

/-- The evaluated entries of a simulated signing attempt from the tables `t` contain
one satisfying `slEvalBadAt` with probability at most `ε` times the number of
evaluated entries. -/
theorem slEvalBad_le {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {ε : ℝ≥0∞}
    (E : G.LogExtractor rel N ε) (x : G.Stmt) (t : G.Tables) (m : G.Msg) (s : G.SimRand) :
    (PMF.uniformOfFintype (Fin G.μ → G.Ch)).toOuterMeasure
        {e | (List.finRange G.μ).any (slEvalBadAt N E.Bad x t m e s) = true} ≤
      (Finset.univ.filter fun i => G.ev i = true).card * ε := by
  calc _ ≤ (PMF.uniformOfFintype (Fin G.μ → G.Ch)).toOuterMeasure
          (⋃ i, {e | slEvalBadAt N E.Bad x t m e s i = true}) :=
        MeasureTheory.measure_mono fun e he => by simpa using he
    _ ≤ ∑' i, (PMF.uniformOfFintype (Fin G.μ → G.Ch)).toOuterMeasure
          {e | slEvalBadAt N E.Bad x t m e s i = true} := MeasureTheory.measure_iUnion_le _
    _ ≤ ∑ i, if G.ev i then ε else 0 := by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun i _ => slEvalBadAt_le E x t m s i
    _ = _ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

end Evaluated

/-! ## Reachability and the extraction flag -/

section Flag

variable {G : Protocol} {α : Type}

theorem size_hashAll_le (t : G.Tables) (l : List (G.Key × G.Ch)) :
    (hashAll t l).size ≤ t.size + l.length := by
  have := List.length_filter_le (fun p : G.Key × G.Ch => (t.lookup p.1).isNone) l
  simp only [hashAll, Protocol.Tables.size, List.length_append] at this ⊢
  omega

theorem slStep_size (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    (x : G.Stmt) (s : SLState G) (d : G.Query) (o : G.Answer × SLState G)
    (ho : o ∈ (toOracle (slStep N Bad x) s d).support) :
    o.2.1.1.size ≤ s.1.1.size + Sum.elim (fun _ => 1) (fun _ => G.μ) d := by
  cases d with
  | inl k =>
    simp only [toOracle, slStep, slHashStep] at ho
    revert ho
    cases s.1.1.lookup k with
    | some e =>
      intro ho
      simp only [Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      simp
    | none =>
      intro ho
      simp only [Step.toPMF, PMF.support_map, Set.mem_image] at ho
      obtain ⟨e, _, rfl⟩ := ho
      simp [Protocol.Tables.size]
      omega
  | inr m =>
    simp only [toOracle, slStep, Step.toPMF] at ho
    obtain ⟨e, s', rfl⟩ := mem_support_sampleVec ho
    have h0 := size_hashAll_le s.1.1 (G.simTrace s.1.1.lookup x m e s').1
    have h1 := programAll_size (hashAll s.1.1 (G.simTrace s.1.1.lookup x m e s').1) s.1.2
      (G.simTrace s.1.1.lookup x m e s').2.1
    have h2 := hlen s.1.1.lookup x m e s'
    simp only [slSignOut, simSignOut, traceOut, programOut, Sum.elim_inr]
    simp only [Protocol.Tables.size] at h0 h1 ⊢
    omega

/-- A final state of the instrumented run of an adversary with at most `h` hash and
`q` signing queries, from a reachable state whose tables leave room for `h + μ·q`
entries below `N`, is reachable and its tables have at most `N` entries. -/
theorem run_sl_reach (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ) (x : G.Stmt)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (s : SLState G) (hs : SLReach N Bad x s) (hN : s.1.1.size + h + G.μ * q ≤ N)
    (y : α × SLState G) (hy : y ∈ (OracleAdv.run (toOracle (slStep N Bad x)) A s).support) :
    SLReach N Bad x y.2 ∧ y.2.1.1.size ≤ N := by
  induction A generalizing h q s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hs, by dsimp only; omega⟩
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b h q (hA b) s hs hN hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    have hsz := slStep_size N Bad hlen x s d o ho
    have hreach := SLReach.step s d o hs (by omega) ho
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        simp only [Sum.elim_inl] at hsz
        exact ih o.1 h q (hA o.1) o.2 hreach (by omega) hy
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        simp only [Sum.elim_inr] at hsz
        refine ih o.1 h q (hA o.1) o.2 hreach ?_ hy
        rw [Nat.mul_succ] at hN
        omega

/-- From a state with the extraction flag cleared, one call sets it with probability
at most `ε` for a hash query and `μ·ε` for a signing query. -/
theorem slStep_flag_le {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {ε : ℝ≥0∞}
    (E : G.LogExtractor rel N ε) (x : G.Stmt) (s : SLState G) (d : G.Query)
    (hs : ¬ s.2 = true) :
    (toOracle (slStep N E.Bad x) s d).toOuterMeasure {o | o.2.2 = true} ≤
      (Sum.elim (fun _ => 1) (fun _ => G.μ) d : ℕ) * ε := by
  obtain ⟨⟨t, b⟩, β⟩ := s
  simp only [Bool.not_eq_true] at hs
  subst hs
  cases d with
  | inl k =>
    simp only [toOracle, slStep, slHashStep]
    cases t.lookup k with
    | some e => simp [Step.toPMF, PMF.toOuterMeasure_pure_apply]
    | none =>
      simp only [Step.toPMF, PMF.toOuterMeasure_map_apply, Sum.elim_inl, Nat.cast_one, one_mul]
      by_cases hN : t.size ≤ N
      · simpa [Set.preimage, hN] using E.bad_le x t k hN
      · simp [Set.preimage, hN]
  | inr m =>
    simp only [toOracle, slStep, Step.toPMF, Sum.elim_inr]
    have hmap : (sampleVec G (slSignOut N E.Bad x t b false m)).toOuterMeasure
        {o | o.2.2 = true} = ((sampleVec G (slSignOut N E.Bad x t b false m)).map
          fun o => o.2.2).toOuterMeasure {c | c = true} := by
      rw [PMF.toOuterMeasure_map_apply]
      rfl
    rw [hmap, sampleVec_map]
    refine (sampleVec_or_le (fun e s => (List.finRange G.μ).any (slEvalBadAt N E.Bad x t m e s))
      (fun e s => decide (t.size ≤ N) && (G.simTrace t.lookup x m e s).2.1.any fun p =>
        E.Bad x (hashAll t (G.simTrace t.lookup x m e s).1) p.1 p.2)).trans ?_
    have hcard : (((Finset.univ.filter fun i => G.ev i = true).card +
        (Finset.univ.filter fun i => G.ev i = false).card : ℕ) : ℝ≥0∞) = G.μ := by
      congr 1
      simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i : Fin G.μ => G.ev i = true)
    rw [← hcard, Nat.cast_add, add_mul]
    refine add_le_add (sampleVec_le_of_forall _ fun s' => slEvalBad_le E x t m s') ?_
    by_cases hN : t.size ≤ N
    · simpa [hN] using E.simBad_le x t m hN
    · simp [hN, sampleVec, PMF.bind_const]

/-- **The extraction flag.** A run with at most `h` hash and `q` signing queries,
from a state with the extraction flag cleared, sets it with probability at most
`(h + μ·q)·ε`. -/
theorem run_sl_flag_le {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {ε : ℝ≥0∞}
    (E : G.LogExtractor rel N ε) (x : G.Stmt) (A : OracleAdv G.Query G.Answer α)
    (h q : ℕ) (hA : IsQueryBound₂ A h q) (s : SLState G) (hs : ¬ s.2 = true) :
    (OracleAdv.run (toOracle (slStep N E.Bad x)) A s).toOuterMeasure {y | y.2.2 = true} ≤
      ((h + G.μ * q : ℕ) : ℝ≥0∞) * ε := by
  have hB := hA.isQueryBoundBy 1 G.μ
  rw [one_mul] at hB
  exact OracleAdv.run_badDraw_le (toOracle (slStep N E.Bad x)) (fun s => s.2 = true)
    (Sum.elim (fun _ => 1) fun _ => G.μ) ε (slStep_flag_le E x) A _ hB s hs

end Flag

/-! ## The bound -/

section Bound

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {ε : ℝ≥0∞}

/-- The relation advantage as an average over generated pairs. -/
theorem Protocol.relAdvantage_eq_tsum (B : G.Stmt → PMF G.Wit) :
    G.relAdvantage rel B = ∑' xw, G.gen xw * (B xw.1).toOuterMeasure {w | rel xw.1 w} := by
  classical
  unfold Protocol.relAdvantage Protocol.relGame
  rw [prTrue_pmfGame]
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  refine tsum_congr fun xw => ?_
  congr 2
  ext w
  simp

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
  have hB := isQueryBound₂_withVerify x _ qH qS (A.isQueryBound x)
  have hproj := run_sl_map_fst N E.Bad x (withVerify x (A.run x))
    ((Protocol.Tables.empty, false), false)
  rw [← hproj, PMF.toOuterMeasure_map_apply, slReduction, PMF.toOuterMeasure_map_apply]
  refine le_trans ?_ (add_le_add le_rfl
    (run_sl_flag_le E x _ _ _ hB ((Protocol.Tables.empty, false), false) (by simp)))
  rw [← PMF.toOuterMeasure_apply_inter_support]
  refine (MeasureTheory.measure_mono ?_).trans (MeasureTheory.measure_union_le _ _)
  rintro y ⟨hw, hy⟩
  by_cases hf : y.2.2 = true
  · exact Or.inr hf
  · obtain ⟨hr, hsz⟩ := run_sl_reach N E.Bad hlen x _ _ _ hB _ SLReach.empty
      (by simpa [Protocol.Tables.size, Protocol.Tables.empty] using hN) y hy
    exact Or.inl (E.sound x y.2 y.1 hr (by simpa using hf) hsz hw)

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
        ((qS * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * γ xw) := by
  refine (Protocol.eufcmaAdvantage_le_simAdvantage_perKey hZK hγ A).trans
    (add_le_add ?_ le_rfl)
  unfold simAdvantage simGame
  rw [prTrue_gameDist, Protocol.relAdvantage_eq_tsum]
  calc _ ≤ ∑' xw, G.gen xw * ((slReduction E A xw.1).toOuterMeasure {w | rel xw.1 w} +
          ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε) :=
        ENNReal.tsum_le_tsum fun xw => mul_le_mul_right (sim_wins_le_sl E hN hlen A xw.1) _
    _ = _ := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

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

end Bound

end CatCrypt.Crypto.FiatShamirROM

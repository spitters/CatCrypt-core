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
answer of a hash query satisfies `Bad` with probability at most `ε`, and the entries
programmed by one simulated signing attempt with probability at most `μ·ε`, for
tables with at most `N` entries.

The instrumented simulated game (`slStep`) runs the simulated oracle of
`FiatShamirROM.Game` and sets an extraction flag when a fresh answer of a hash
query, or an entry programmed by a simulated signing attempt, satisfies `Bad` given
the tables before the query. Extraction is sound when, at every state reachable
through calls from tables with at most `N` entries (`SLReach`), a winning forgery
with the extraction flag cleared gives a witness of the relation. The reduction
`slReduction E A` runs the instrumented game once on the statement and applies the
extractor to the final tables and the forgery.

## Main definitions

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

/-- A signing attempt of the instrumented game: `simSignOut`, with the extraction flag
set when the tables have at most `N` entries and an entry `(k, e)` of the simulated
view satisfies `Bad x t k e`. -/
def slSignOut (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt)
    (t : G.Tables) (b β : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch) (s : G.SimRand) :
    G.Answer × SLState G :=
  ((simSignOut x t b m e s).1, ((simSignOut x t b m e s).2,
    β || (decide (t.size ≤ N) && (G.simulate x m e s).1.any fun p => Bad x t p.1 p.2)))

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
the forgery. A fresh hash answer satisfies `Bad` with probability at most `ε`, and
the entries of one simulated signing attempt with probability at most `μ·ε`, for
tables with at most `N` entries. At every reachable state with the extraction flag
cleared, a winning forgery gives a witness. -/
structure LogExtractor (rel : G.Stmt → G.Wit → Prop) (N : ℕ) (ε : ℝ≥0∞) where
  /-- The extractor on the statement, the final tables and the forgery. -/
  ext : G.Stmt → G.Tables → G.Forgery → G.Wit
  /-- The fresh answer `e` at the point `k` is bad given the tables `t`. -/
  Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool
  /-- A uniform answer is bad with probability at most `ε`. -/
  bad_le : ∀ x t k, t.size ≤ N →
    (PMF.uniformOfFintype G.Ch).toOuterMeasure {e | Bad x t k e = true} ≤ ε
  /-- The entries of a simulated attempt on uniform values and simulator randomness
  contain a bad one with probability at most `μ·ε`. -/
  simBad_le : ∀ x t m, t.size ≤ N →
    (sampleVec G fun e (s : G.SimRand) =>
      (G.simulate x m e s).1.any fun p => Bad x t p.1 p.2).toOuterMeasure
        {c | c = true} ≤ G.μ * ε
  /-- Without the extraction flag, a winning forgery gives a witness. -/
  sound : ∀ x (s : SLState G) (f : G.Forgery), SLReach N Bad x s → s.2 = false →
    wins x (f, s.1) = true → rel x (ext x s.1.1 f)

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

/-! ## Reachability and the extraction flag -/

section Flag

variable {G : Protocol} {α : Type}

theorem slStep_size (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (hlen : ∀ x m e s, (G.simulate x m e s).1.length ≤ G.μ)
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
    have h1 := programAll_size s.1.1 s.1.2 (G.simulate x m e s').1
    have h2 := hlen x m e s'
    simp only [slSignOut, simSignOut, programOut, Sum.elim_inr]
    simp only [Protocol.Tables.size] at h1 ⊢
    omega

theorem run_sl_reach (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (hlen : ∀ x m e s, (G.simulate x m e s).1.length ≤ G.μ) (x : G.Stmt)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (s : SLState G) (hs : SLReach N Bad x s) (hN : s.1.1.size + h + G.μ * q ≤ N)
    (y : α × SLState G) (hy : y ∈ (OracleAdv.run (toOracle (slStep N Bad x)) A s).support) :
    SLReach N Bad x y.2 := by
  induction A generalizing h q s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hs
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
    by_cases hN : t.size ≤ N
    · simpa [slSignOut, hN] using E.simBad_le x t m hN
    · simp [slSignOut, hN, sampleVec, PMF.bind_const]

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
    (hN : qH + G.V + G.μ * qS ≤ N) (hlen : ∀ x m e s, (G.simulate x m e s).1.length ≤ G.μ)
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
  · refine Or.inl (E.sound x y.2 y.1 ?_ (by simpa using hf) hw)
    exact run_sl_reach N E.Bad hlen x _ _ _ hB _ SLReach.empty
      (by simpa [Protocol.Tables.size, Protocol.Tables.empty] using hN) y hy

/-- **EUF-CMA security of Fiat–Shamir signatures by straight-line extraction.** For
a protocol `G` whose simulated views have at most `μ` entries, generated pairs with
statistical HVZK distance `δ (x, w)` and key bound `γ (x, w)`, a log extractor `E`
for `rel` on tables with at most `N ≥ qH + V + μ·qS` entries with bad-answer
probability `ε`, and every adversary `A` with at most `qH` hash and `qS` signing
queries,

`eufcmaAdvantage A ≤ relAdvantage (slReduction E A) + (qH + V + μ·qS)·ε
  + E_{(x,w) ← gen}[qS·δ(x, w) + qS·μ·(qH + V + μ·qS)·γ(x, w)]`,

where `slReduction E A` runs the instrumented simulated game once and applies the
extractor to the final tables and the forgery. -/
theorem fiatShamir_rom_eufcma_sl (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N) (hlen : ∀ x m e s, (G.simulate x m e s).1.length ≤ G.μ)
    {δ γ : G.Stmt × G.Wit → ℝ≥0∞}
    (hZK : ∀ xw ∈ G.gen.support, G.StatHVZKAt xw.1 xw.2 (δ xw))
    (hγ : ∀ xw ∈ G.gen.support, G.KeyBoundAt xw.1 xw.2 (γ xw)) (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤ G.relAdvantage rel (slReduction E A) +
      ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε +
      ∑' xw, G.gen xw * (qS * δ xw +
        ((qS * G.μ * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * γ xw) := by
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
`relAdvantage (slReduction E A) + (qH + V + μ·qS)·ε + qS·δ + qS·μ·(qH + V + μ·qS)·γ`. -/
theorem fiatShamir_rom_eufcma_sl_stat (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (hN : qH + G.V + G.μ * qS ≤ N) (hlen : ∀ x m e s, (G.simulate x m e s).1.length ≤ G.μ)
    {δ : ℝ≥0∞} (hZK : G.StatHVZK δ) {γ : ℝ≥0∞} (hγ : G.KeyBound γ)
    (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤ G.relAdvantage rel (slReduction E A) +
      ((qH + G.V + G.μ * qS : ℕ) : ℝ≥0∞) * ε +
      (qS * δ + ((qS * G.μ * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * γ) := by
  refine (fiatShamir_rom_eufcma_sl E hN hlen (δ := fun _ => δ) (γ := fun _ => γ)
    (fun xw hxw => hZK xw.1 xw.2 hxw) (fun xw hxw => hγ xw.1 xw.2 hxw) A).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Bound

end CatCrypt.Crypto.FiatShamirROM

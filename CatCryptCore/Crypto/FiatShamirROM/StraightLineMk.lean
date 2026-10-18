/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.EagerMarker

/-!
# Fiat–Shamir in the random-oracle model: straight-line extraction with markers

The class-wise straight-line extractor of `FiatShamirROM.StraightLineCls` on the
marker game of `FiatShamirROM.EagerMarker`. The instrumented marker game
(`slStepMk N M Bad x`) evaluates the markers `M` before every fresh designated hash
query and judges every fresh draw, of a marker or of an answer, by `Bad` on the
tables before it, when they have at most `N` entries. A marker log extractor
(`Protocol.LogExtractorMk G rel N κ M ε εS`) has the bad-answer laws of a class-wise
one and finds a witness at the reachable states of the instrumented marker game.

A hash query at a fresh designated point draws its markers and its answer, so it sets
the extraction flag with probability at most `Σ_c nmc c·ε c + ε desCls`. Since the
marker game wins at least as often as the simulated game (`sim_wins_le_simMk`), the
simulated-game advantage is at most the relation advantage of the marker reduction
plus the class-wise extraction terms with the marker draws added.

## Main definitions

* `slStepMk N M Bad x` — the instrumented marker game
* `SLReachMk N M Bad x` — its reachable states
* `Protocol.LogExtractorMk G rel N κ M ε εS` — a class-wise log extractor on the
  marker game
* `slReductionMk E A` — the reduction running the instrumented marker game once and
  applying the extractor
* `Protocol.LogExtractorCls.toMk` — a class-wise log extractor as a marker one for the
  family without markers

## Main results

* `run_slMk_map_fst` — forgetting the extraction flag maps the instrumented marker run
  to the run of the marker game
* `run_slMk_reach` — the final states of a run with room for `1 + nm` entries per hash
  query below `N` are reachable and have at most `N` entries
* `run_slMk_flag_le_cls` — a run sets the extraction flag with probability at most the
  sum over the classes of its class costs, marker draws included, times `ε c`, plus its
  signing queries times `εS`
* `sim_wins_le_slMk`, `simAdvantage_le_slMk` — the per-statement and simulated-game
  bounds by the marker reduction
* `fiatShamir_rom_eufcma_slMk` — the EUF-CMA bound of straight-line extraction with
  markers
* `slReductionMk_toMk` — the marker reduction of `E.toMk c₀` is `slReductionCls E`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

variable {D R α : Type}

/-- A cost bound scales with the cost. -/
theorem IsQueryBoundBy.mul_left {c : D → ℕ} {A : OracleAdv D R α} {n : ℕ}
    (h : A.IsQueryBoundBy c n) (a : ℕ) : A.IsQueryBoundBy (fun d => a * c d) (a * n) := by
  induction A generalizing n with
  | ret x => trivial
  | rand p k ih => exact fun b => ih b (h b)
  | query d k ih =>
    refine ⟨Nat.mul_le_mul_left a h.1, fun r => ?_⟩
    rw [← Nat.mul_sub]
    exact ih r (h.2 r)

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

open Protocol

/-! ## The instrumented marker game -/

section Instrumented

variable {G : Protocol} {κ : G.Classes}

/-- The tables and the extraction flag after the markers `l` before the designated
point `k`: a marker at a defined point keeps its value, a marker at an undefined point
`p` takes a fresh uniform value `v` recorded in `hash`, and the flag is set when the
tables `t` before it have at most `N` entries and `Bad x t p v`. -/
noncomputable def slMarkTables (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) (M : Markers κ) (k : G.Key) :
    G.Tables → Bool → List (Fin M.nm) → PMF (G.Tables × Bool)
  | t, β, [] => PMF.pure (t, β)
  | t, β, i :: l =>
    match t.lookup (M.pt k t.lookup i) with
    | some _ => slMarkTables N Bad x M k t β l
    | none => (PMF.uniformOfFintype G.Ch).bind fun v =>
      slMarkTables N Bad x M k { t with hash := t.hash ++ [(M.pt k t.lookup i, v)] }
        (β || (decide (t.size ≤ N) && Bad x t (M.pt k t.lookup i) v)) l

/-- A designated hash query of the instrumented marker game: at an undefined point
`k`, the markers are evaluated and the answer `e` is drawn fresh, with the extraction
flag set when the tables `t'` after the markers have at most `N` entries and
`Bad x t' k e`. -/
noncomputable def slMarkStep (N : ℕ) (M : Markers κ)
    (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt) (t : G.Tables) (b β : Bool)
    (k : G.Key) : Step G.Answer (SLState G) G.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, ((t, b), β)))
  | none => .plain ((slMarkTables N Bad x M k t β (List.finRange M.nm)).bind fun tb =>
      (PMF.uniformOfFintype G.Ch).map fun e =>
        (.inl e, (({ tb.1 with hash := tb.1.hash ++ [(k, e)] }, b),
          tb.2 || (decide (tb.1.size ≤ N) && Bad x tb.1 k e))))

/-- The instrumented marker game for the statement `x`: `slStep`, except that a
designated hash query evaluates the markers `M` first. -/
noncomputable def slStepMk (N : ℕ) (M : Markers κ)
    (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt) (s : SLState G) :
    G.Query → Step G.Answer (SLState G) G.Ch
  | .inl k => bif M.des k then slMarkStep N M Bad x s.1.1 s.1.2 s.2 k
      else slHashStep N Bad x s.1.1 s.1.2 s.2 k
  | .inr m => .plain (sampleVec G (slSignOut N Bad x s.1.1 s.1.2 s.2 m))

/-- The states of the instrumented marker game reachable from the empty tables by
calls from states whose tables have at most `N` entries. -/
inductive SLReachMk (N : ℕ) (M : Markers κ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) : SLState G → Prop
  | empty : SLReachMk N M Bad x ((Protocol.Tables.empty, false), false)
  | step (s : SLState G) (d : G.Query) (o : G.Answer × SLState G) :
    SLReachMk N M Bad x s → s.1.1.size ≤ N → o ∈ (toOracle (slStepMk N M Bad x) s d).support →
      SLReachMk N M Bad x o.2

/-- Without markers, the instrumented marker game is the instrumented game. -/
theorem slStepMk_none (N : ℕ) (c₀ : κ.ι) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) : slStepMk N (Markers.none c₀) Bad x = slStep N Bad x := by
  funext s d
  cases d <;> rfl

/-- Without markers, the reachable states of the instrumented marker game are those of
the instrumented game. -/
theorem slReachMk_none_iff (N : ℕ) (c₀ : κ.ι) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) (s : SLState G) : SLReachMk N (Markers.none c₀) Bad x s ↔ SLReach N Bad x s := by
  constructor
  · intro h
    induction h with
    | empty => exact SLReach.empty
    | step s d o _ hs ho ih =>
      rw [slStepMk_none] at ho
      exact SLReach.step s d o ih hs ho
  · intro h
    induction h with
    | empty => exact SLReachMk.empty
    | step s d o _ hs ho ih =>
      rw [← slStepMk_none N c₀] at ho
      exact SLReachMk.step s d o ih hs ho

/-- Away from designated hash queries, the instrumented marker game is the
instrumented game. -/
theorem slStepMk_eq_slStep (N : ℕ) (M : Markers κ)
    (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt) (s : SLState G) (d : G.Query)
    (hd : ∀ k, d = .inl k → M.des k = false) :
    toOracle (slStepMk N M Bad x) s d = toOracle (slStep N Bad x) s d := by
  cases d with
  | inl k => simp only [toOracle, slStepMk, slStep, hd k rfl, cond_false]
  | inr m => rfl

end Instrumented

/-! ## Marker log extractors and the reduction -/

namespace Protocol

variable (G : Protocol)

/-- **Marker log extractor** for the relation `rel` on tables with at most `N`
entries, for the key classes `κ` and the markers `M`. It has the fields of a class-wise
log extractor (`LogExtractorCls`), and at every reachable state of the instrumented
marker game with at most `N` table entries and the extraction flag cleared, a winning
forgery gives a witness. -/
structure LogExtractorMk (rel : G.Stmt → G.Wit → Prop) (N : ℕ) (κ : G.Classes)
    (M : Markers κ) (ε : κ.ι → ℝ≥0∞) (εS : ℝ≥0∞) where
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
    (PMF.uniformOfFintype G.Ch).toOuterMeasure {e | Bad x t k e = true} ≤ ε (κ.cls k)
  /-- The programmed entries of a simulated attempt from the tables `t` on uniform
  values and simulator randomness contain an entry that is bad given the tables after
  the evaluated entries with probability at most `εS`. -/
  simBad_le : ∀ x t m, t.size ≤ N →
    (sampleVec G fun e (s : G.SimRand) =>
      (G.simTrace t.lookup x m e s).2.1.any fun p =>
        Bad x (hashAll t (G.simTrace t.lookup x m e s).1) p.1 p.2).toOuterMeasure
        {c | c = true} ≤ εS
  /-- On reachable states of the marker game with at most `N` table entries and
  without the extraction flag, a winning forgery gives a witness. -/
  sound : ∀ x (s : SLState G) (f : G.Forgery), SLReachMk N M Bad x s → s.2 = false →
    s.1.1.size ≤ N → wins x (f, s.1) = true → rel x (ext x s.1.1 f)

variable {G}

/-- A class-wise log extractor is a marker log extractor for the family without
markers. -/
def LogExtractorCls.toMk {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
    {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞} (E : G.LogExtractorCls rel N κ ε εS) (c₀ : κ.ι) :
    G.LogExtractorMk rel N κ (Markers.none c₀) ε εS where
  ext := E.ext
  Bad := E.Bad
  simKey_cls := E.simKey_cls
  bad_le := E.bad_le
  simBad_le := E.simBad_le
  sound x s f h := E.sound x s f ((slReachMk_none_iff N c₀ E.Bad x s).1 h)

/-- The bad-answer laws of a marker log extractor, as a class-wise log extractor for
the relation that always holds. -/
def LogExtractorMk.toFlagCls {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
    {M : Markers κ} {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞} (E : G.LogExtractorMk rel N κ M ε εS) :
    G.LogExtractorCls (fun _ _ => True) N κ ε εS where
  ext := E.ext
  Bad := E.Bad
  simKey_cls := E.simKey_cls
  bad_le := E.bad_le
  simBad_le := E.simBad_le
  sound _ _ _ _ _ _ _ := trivial

end Protocol

section Reduction

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
  {M : Markers κ} {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞}

/-- The instrumented marker run on the statement `x` with the bad predicate of a
marker log extractor, the challenger's verifier queries included. -/
noncomputable def slRunMk (E : G.LogExtractorMk rel N κ M ε εS) {qH qS : ℕ}
    (A : G.Adversary qH qS) (x : G.Stmt) : PMF (G.Forgery × SLState G) :=
  OracleAdv.run (toOracle (slStepMk N M E.Bad x)) (withVerify x (A.run x))
    ((Protocol.Tables.empty, false), false)

/-- **The marker straight-line reduction.** On the statement `x`, run the
instrumented marker game once and apply the extractor to the final tables and the
forgery. -/
noncomputable def slReductionMk (E : G.LogExtractorMk rel N κ M ε εS) {qH qS : ℕ}
    (A : G.Adversary qH qS) : G.Stmt → PMF G.Wit :=
  fun x => (slRunMk E A x).map fun y => E.ext x y.2.1.1 y.1

/-- The marker reduction of a class-wise log extractor viewed as a marker one without
markers is its class-wise reduction. -/
theorem slReductionMk_toMk (E : G.LogExtractorCls rel N κ ε εS) (c₀ : κ.ι) {qH qS : ℕ}
    (A : G.Adversary qH qS) : slReductionMk (E.toMk c₀) A = slReductionCls E A := rfl

end Reduction

/-! ## Projection and reachability -/

section Project

variable {G : Protocol} {κ : G.Classes} {α : Type}

theorem slMarkTables_map_fst (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) (M : Markers κ) (k : G.Key) (l : List (Fin M.nm)) (t : G.Tables) (β : Bool) :
    (slMarkTables N Bad x M k t β l).map Prod.fst = markTables M k t l := by
  induction l generalizing t β with
  | nil => simp [slMarkTables, markTables, PMF.pure_map]
  | cons i l ih =>
    simp only [slMarkTables, markTables]
    cases t.lookup (M.pt k t.lookup i) with
    | some _ => exact ih t β
    | none =>
      simp only [PMF.map_bind]
      congr 1
      funext v
      exact ih _ _

theorem slStepMk_map_fst (N : ℕ) (M : Markers κ)
    (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt) (s : SLState G) (d : G.Query) :
    (toOracle (slStepMk N M Bad x) s d).map (Prod.map id Prod.fst) =
      toOracle (simStepMk M x) s.1 d := by
  cases d with
  | inl k =>
    cases hd : M.des k with
    | false =>
      simp only [toOracle, slStepMk, simStepMk, slHashStep, markHashStep, hd, cond_false,
        Bool.false_eq_true, if_false]
      cases s.1.1.lookup k with
      | some e => simp [Step.toPMF, PMF.pure_map]
      | none => simp only [Step.toPMF, PMF.map_comp]; rfl
    | true =>
      simp only [toOracle, slStepMk, simStepMk, slMarkStep, markHashStep, hd, cond_true, if_true]
      cases s.1.1.lookup k with
      | some e => simp [Step.toPMF, PMF.pure_map]
      | none =>
        simp only [Step.toPMF, PMF.map_bind]
        rw [← slMarkTables_map_fst N Bad x M k _ s.1.1 s.2, PMF.bind_map]
        congr 1
        funext tb
        rw [Function.comp_apply, PMF.map_comp]
        rfl
  | inr m =>
    simp only [toOracle, slStepMk, simStepMk, Step.toPMF, sampleVec_map]
    rfl

/-- Forgetting the extraction flag maps the instrumented marker run to the run of the
marker game. -/
theorem run_slMk_map_fst (N : ℕ) (M : Markers κ)
    (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool) (x : G.Stmt)
    (A : OracleAdv G.Query G.Answer α) (s : SLState G) :
    (OracleAdv.run (toOracle (slStepMk N M Bad x)) A s).map (Prod.map id Prod.fst) =
      OracleAdv.run (toOracle (simStepMk M x)) A s.1 :=
  OracleAdv.run_map_state _ _ Prod.fst (slStepMk_map_fst N M Bad x) A s

theorem slMarkTables_size (N : ℕ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (x : G.Stmt) (M : Markers κ) (k : G.Key) (l : List (Fin M.nm)) (t : G.Tables) (β : Bool)
    (y : G.Tables × Bool) (hy : y ∈ (slMarkTables N Bad x M k t β l).support) :
    y.1.size ≤ t.size + l.length := by
  induction l generalizing t β with
  | nil =>
    simp only [slMarkTables, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp
  | cons i l ih =>
    simp only [slMarkTables] at hy
    revert hy
    cases t.lookup (M.pt k t.lookup i) with
    | some _ =>
      intro hy
      have := ih t β hy
      simp only [List.length_cons]
      omega
    | none =>
      intro hy
      obtain ⟨v, -, hv⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
      have := ih _ _ hv
      simp only [Protocol.Tables.size, List.length_append, List.length_cons,
        List.length_nil] at this ⊢
      omega

theorem slStepMk_size (N : ℕ) (M : Markers κ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    (x : G.Stmt) (s : SLState G) (d : G.Query) (o : G.Answer × SLState G)
    (ho : o ∈ (toOracle (slStepMk N M Bad x) s d).support) :
    o.2.1.1.size ≤ s.1.1.size + Sum.elim (fun _ => 1 + M.nm) (fun _ => G.μ) d := by
  by_cases hd : ∃ k, d = .inl k ∧ M.des k = true
  · obtain ⟨k, rfl, hk⟩ := hd
    simp only [toOracle, slStepMk, slMarkStep, hk, cond_true] at ho
    simp only [Sum.elim_inl]
    revert ho
    cases s.1.1.lookup k with
    | some e =>
      intro ho
      simp only [Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      simp
    | none =>
      intro ho
      simp only [Step.toPMF] at ho
      obtain ⟨tb, htb, ho⟩ := (PMF.mem_support_bind_iff _ _ _).1 ho
      obtain ⟨e, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ho
      have := slMarkTables_size N Bad x M k _ _ _ tb htb
      simp only [List.length_finRange, Protocol.Tables.size, List.length_append,
        List.length_cons, List.length_nil] at this ⊢
      omega
  · rw [slStepMk_eq_slStep N M Bad x s d fun k hk => by
      cases h : M.des k
      · rfl
      · exact absurd ⟨k, hk, h⟩ hd] at ho
    have := slStep_size N Bad hlen x s d o ho
    cases d with
    | inl k => simp only [Sum.elim_inl] at this ⊢; omega
    | inr m => exact this

/-- A final state of the instrumented marker run of an adversary with at most `h` hash
and `q` signing queries, from a reachable state whose tables leave room for
`(1 + nm)·h + μ·q` entries below `N`, is reachable and its tables have at most `N`
entries. -/
theorem run_slMk_reach (N : ℕ) (M : Markers κ) (Bad : G.Stmt → G.Tables → G.Key → G.Ch → Bool)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ) (x : G.Stmt)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (s : SLState G) (hs : SLReachMk N M Bad x s) (hN : s.1.1.size + (1 + M.nm) * h + G.μ * q ≤ N)
    (y : α × SLState G)
    (hy : y ∈ (OracleAdv.run (toOracle (slStepMk N M Bad x)) A s).support) :
    SLReachMk N M Bad x y.2 ∧ y.2.1.1.size ≤ N := by
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
    have hsz := slStepMk_size N M Bad hlen x s d o ho
    have hreach := SLReachMk.step s d o hs (by omega) ho
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        simp only [Sum.elim_inl] at hsz
        refine ih o.1 h q (hA o.1) o.2 hreach ?_ hy
        rw [Nat.mul_succ] at hN
        omega
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        simp only [Sum.elim_inr] at hsz
        refine ih o.1 h q (hA o.1) o.2 hreach ?_ hy
        rw [Nat.mul_succ] at hN
        omega

end Project

/-! ## The extraction flag -/

section Flag

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
  {M : Markers κ} {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞} {α : Type}

/-- The markers `l` evaluated from a cleared extraction flag set it with probability
at most `Σ_{i ∈ l} ε (cls i)`. -/
theorem slMarkTables_flag_le (E : G.LogExtractorMk rel N κ M ε εS) (x : G.Stmt) (k : G.Key)
    (l : List (Fin M.nm)) (t : G.Tables) :
    (slMarkTables N E.Bad x M k t false l).toOuterMeasure {y | y.2 = true} ≤
      (l.map fun i => ε (M.cls i)).sum := by
  induction l generalizing t with
  | nil => simp [slMarkTables, PMF.toOuterMeasure_pure_apply]
  | cons i l ih =>
    simp only [slMarkTables, List.map_cons, List.sum_cons]
    cases t.lookup (M.pt k t.lookup i) with
    | some _ => exact (ih t).trans le_add_self
    | none =>
      refine (PMF.toOuterMeasure_bind_le_add _ _
        {v | (decide (t.size ≤ N) && E.Bad x t (M.pt k t.lookup i) v) = true} _ _
        fun v hv => ?_).trans (add_le_add ?_ le_rfl)
      · simp only [Set.mem_ofPred_eq, Bool.not_eq_true] at hv
        rw [Bool.false_or, hv]
        exact ih _
      · by_cases hN : t.size ≤ N
        · simpa [hN, M.pt_cls] using E.bad_le x t (M.pt k t.lookup i) hN
        · simp [hN]

/-- The number of markers of each class gives the sum of the bad-answer
probabilities of the markers. -/
theorem sum_finRange_markers (M : Markers κ) :
    ((List.finRange M.nm).map fun i => ε (M.cls i)).sum = ∑ c, (M.nmc c : ℝ≥0∞) * ε c := by
  rw [← Fin.sum_univ_def, ← Finset.sum_fiberwise _ M.cls]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2],
    Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The class costs of a query for the instrumented marker game: the class costs of
the instrumented game, and `nmc c` more for the class `c` at a designated hash
query. -/
def slCostMk (M : Markers κ) : Option κ.ι → G.Query → ℕ
  | some c => fun d => slCostCls κ (some c) d +
      Sum.elim (fun k => bif M.des k then M.nmc c else 0) (fun _ => 0) d
  | none => slCostCls κ none

/-- From a state with the extraction flag cleared, one call of the instrumented marker
game sets it with probability at most the class costs of the call times the bad-answer
probabilities. -/
theorem slStepMk_flag_le (E : G.LogExtractorMk rel N κ M ε εS) (x : G.Stmt)
    (s : SLState G) (d : G.Query) (hs : ¬ s.2 = true) :
    (toOracle (slStepMk N M E.Bad x) s d).toOuterMeasure {o | o.2.2 = true} ≤
      ∑ o, (slCostMk M o d : ℝ≥0∞) * slEpsCls ε εS o := by
  by_cases hd : ∃ k, d = .inl k ∧ M.des k = true
  · obtain ⟨k, rfl, hk⟩ := hd
    obtain ⟨⟨t, b⟩, β⟩ := s
    simp only [Bool.not_eq_true] at hs
    subst hs
    have hrhs : ∑ o, (slCostMk M o (.inl k) : ℝ≥0∞) * slEpsCls ε εS o =
        (∑ c, (M.nmc c : ℝ≥0∞) * ε c) + ε (κ.cls k) := by
      rw [Fintype.sum_option]
      simp only [slCostMk, slCostCls, slEpsCls, Protocol.Classes.hashCost, Sum.elim_inl,
        hk, cond_true, add_zero, Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_ite,
        Nat.cast_one, add_mul, ite_mul, one_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [add_comm]
    rw [hrhs]
    simp only [toOracle, slStepMk, slMarkStep, hk, cond_true]
    cases t.lookup k with
    | some e => simp [Step.toPMF, PMF.toOuterMeasure_pure_apply]
    | none =>
      simp only [Step.toPMF]
      refine (PMF.toOuterMeasure_bind_le_add _ _ {tb | tb.2 = true} _ _
        fun tb htb => ?_).trans
        (add_le_add ((slMarkTables_flag_le E x k _ t).trans_eq (sum_finRange_markers M)) le_rfl)
      simp only [Set.mem_ofPred_eq, Bool.not_eq_true] at htb
      rw [PMF.toOuterMeasure_map_apply]
      by_cases hN : tb.1.size ≤ N
      · simpa [Set.preimage, htb, hN] using E.bad_le x tb.1 k hN
      · simp [Set.preimage, htb, hN]
  · rw [slStepMk_eq_slStep N M E.Bad x s d fun k hk => by
      cases h : M.des k
      · rfl
      · exact absurd ⟨k, hk, h⟩ hd]
    refine (slStep_flag_le_cls E.toFlagCls x s d hs).trans
      (Finset.sum_le_sum fun o _ => ?_)
    gcongr
    cases o with
    | none => exact le_rfl
    | some c => exact Nat.le_add_right _ _

/-- **The extraction flag of the marker game.** A run whose queries cost at most `n o`
for the class costs `slCostMk M o`, from a state with the extraction flag cleared,
sets it with probability at most `Σ_o n o·slEpsCls ε εS o`. -/
theorem run_slMk_flag_le_cls (E : G.LogExtractorMk rel N κ M ε εS) (x : G.Stmt)
    (A : OracleAdv G.Query G.Answer α) (n : Option κ.ι → ℕ)
    (hA : ∀ o, A.IsQueryBoundBy (slCostMk M o) (n o)) (s : SLState G) (hs : ¬ s.2 = true) :
    (OracleAdv.run (toOracle (slStepMk N M E.Bad x)) A s).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ o, (n o : ℝ≥0∞) * slEpsCls ε εS o :=
  OracleAdv.run_badDraw_le_sum (toOracle (slStepMk N M E.Bad x)) (fun s => s.2 = true)
    (slCostMk M) (slEpsCls ε εS) (slStepMk_flag_le E x) A n hA s hs

/-- The verified run of an adversary with at most `qH` hash and `qS` signing
queries whose hash queries at points of class `c` cost at most `q c` costs at most
`q c + Vc c + nmc c·(q desCls + Vc desCls) + μe c·qS` for the class `c` and `qS` for
`none`. -/
theorem isQueryBoundBy_withVerify_slCostMk (M : Markers κ) (x : G.Stmt) {qH qS : ℕ}
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) (o : Option κ.ι) :
    (withVerify x (A.run x)).IsQueryBoundBy (slCostMk M o)
      (Option.elim o qS fun c =>
        q c + κ.Vc c + M.nmc c * (q M.desCls + κ.Vc M.desCls) + κ.μe c * qS) := by
  cases o with
  | none => exact isQueryBoundBy_withVerify_slCostCls x A q hq none
  | some c =>
    have hM := ((isQueryBoundBy_withVerify_cls κ M.desCls x _ _ (hq M.desCls)).mul_left
      (M.nmc c)).of_cost_le (cost' := Sum.elim (fun k => bif M.des k then M.nmc c else 0)
        (fun _ => 0)) fun d => by
      cases d with
      | inl k =>
        cases h : M.des k
        · simp [h]
        · simp [Protocol.Classes.hashCost, M.des_cls k h, h]
      | inr m => exact Nat.zero_le _
    refine ((isQueryBoundBy_withVerify_slCostCls x A q hq (some c)).add hM).mono
      (le_of_eq ?_)
    simp only [Option.elim]
    ring

end Flag

/-! ## The bound -/

section Bound

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
  {M : Markers κ} {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞}

/-- At one statement, winning the simulated game has probability at most the
probability that the marker extractor finds a witness from the instrumented marker
run, plus `Σ_c (q c + Vc c + nmc c·(q desCls + Vc desCls) + μe c·qS)·ε c + qS·εS`. -/
theorem sim_wins_le_slMk (E : G.LogExtractorMk rel N κ M ε εS) {qH qS : ℕ}
    (hN : (1 + M.nm) * (qH + G.V) + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) (x : G.Stmt) :
    (OracleAdv.run (toOracle (simStep x)) (withVerify x (A.run x))
        (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true} ≤
      (slReductionMk E A x).toOuterMeasure {w | rel x w} +
        (∑ c, ((q c + κ.Vc c + M.nmc c * (q M.desCls + κ.Vc M.desCls) + κ.μe c * qS : ℕ) :
          ℝ≥0∞) * ε c + qS * εS) := by
  refine (sim_wins_le_simMk_game M A x).trans ?_
  have hB := isQueryBound₂_withVerify x _ qH qS (A.isQueryBound x)
  have hflag := run_slMk_flag_le_cls E x _ _
    (isQueryBoundBy_withVerify_slCostMk M x A q (hq x)) ((Protocol.Tables.empty, false), false)
    (by simp)
  rw [Fintype.sum_option] at hflag
  simp only [Option.elim, slEpsCls] at hflag
  have hproj := run_slMk_map_fst N M E.Bad x (withVerify x (A.run x))
    ((Protocol.Tables.empty, false), false)
  rw [← hproj, PMF.toOuterMeasure_map_apply, slReductionMk, PMF.toOuterMeasure_map_apply]
  refine le_trans ?_ (add_le_add le_rfl ((hflag.trans_eq (add_comm _ _))))
  rw [← PMF.toOuterMeasure_apply_inter_support]
  refine (MeasureTheory.measure_mono ?_).trans (MeasureTheory.measure_union_le _ _)
  rintro y ⟨hw, hy⟩
  by_cases hf : y.2.2 = true
  · exact Or.inr hf
  · obtain ⟨hr, hsz⟩ := run_slMk_reach N M E.Bad hlen x _ _ _ hB _ SLReachMk.empty
      (by simpa [Protocol.Tables.size, Protocol.Tables.empty] using hN) y hy
    exact Or.inl (E.sound x y.2 y.1 hr (by simpa using hf) hsz hw)

/-- The simulated-game advantage of an adversary with at most `qH` hash and `qS`
signing queries whose hash queries at points of class `c` are at most `q c` is at
most the relation advantage of `slReductionMk E A` plus
`Σ_c (q c + Vc c + nmc c·(q desCls + Vc desCls) + μe c·qS)·ε c + qS·εS`. -/
theorem simAdvantage_le_slMk (E : G.LogExtractorMk rel N κ M ε εS) {qH qS : ℕ}
    (hN : (1 + M.nm) * (qH + G.V) + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    simAdvantage A ≤ G.relAdvantage rel (slReductionMk E A) +
      (∑ c, ((q c + κ.Vc c + M.nmc c * (q M.desCls + κ.Vc M.desCls) + κ.μe c * qS : ℕ) :
        ℝ≥0∞) * ε c + qS * εS) := by
  unfold simAdvantage simGame
  rw [prTrue_gameDist, Protocol.relAdvantage_eq_tsum]
  calc _ ≤ ∑' xw, G.gen xw * ((slReductionMk E A xw.1).toOuterMeasure {w | rel xw.1 w} +
          (∑ c, ((q c + κ.Vc c + M.nmc c * (q M.desCls + κ.Vc M.desCls) + κ.μe c * qS : ℕ) :
            ℝ≥0∞) * ε c + qS * εS)) :=
        ENNReal.tsum_le_tsum fun xw =>
          mul_le_mul_right (sim_wins_le_slMk E hN hlen A q hq xw.1) _
    _ = _ := by
        generalize (∑ c, ((q c + κ.Vc c + M.nmc c * (q M.desCls + κ.Vc M.desCls) +
          κ.μe c * qS : ℕ) : ℝ≥0∞) * ε c + qS * εS) = K
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **EUF-CMA security of Fiat–Shamir signatures by straight-line extraction with
markers.** For a protocol `G` with key classes `κ` whose simulated traces have at most
`μ` evaluated and programmed entries, generated pairs with statistical HVZK distance
`δ (x, w)` and class-wise key bound `Γ (x, w)`, markers `M`, a marker log extractor
`E` for `rel` on tables with at most `N ≥ (1 + nm)·(qH + V) + μ·qS` entries with
bad-answer probabilities `ε c` and programmed-entry bound `εS`, and every adversary
`A` with at most `qH` hash and `qS` signing queries whose hash queries at points of
class `c` are at most `q c` on every path,

`eufcmaAdvantage A ≤ relAdvantage (slReductionMk E A)
  + Σ_c (q c + Vc c + nmc c·(q desCls + Vc desCls) + μe c·qS)·ε c + qS·εS
  + E_{(x,w) ← gen}[qS·δ(x, w) + Σ_c qS·(q c + Vc c + μc c·qS)·Γ(x, w) c]`. -/
theorem fiatShamir_rom_eufcma_slMk (E : G.LogExtractorMk rel N κ M ε εS) {qH qS : ℕ}
    (hN : (1 + M.nm) * (qH + G.V) + G.μ * qS ≤ N)
    (hlen : ∀ look x m e s, (G.simTrace look x m e s).1.length +
      (G.simTrace look x m e s).2.1.length ≤ G.μ)
    {δ : G.Stmt × G.Wit → ℝ≥0∞} {Γ : G.Stmt × G.Wit → κ.ι → ℝ≥0∞}
    (hZK : ∀ xw ∈ G.gen.support, G.StatHVZKAt xw.1 xw.2 (δ xw))
    (hΓ : ∀ xw ∈ G.gen.support, G.KeyBoundClsAt κ xw.1 xw.2 (Γ xw))
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    eufcmaAdvantage A ≤ G.relAdvantage rel (slReductionMk E A) +
      (∑ c, ((q c + κ.Vc c + M.nmc c * (q M.desCls + κ.Vc M.desCls) + κ.μe c * qS : ℕ) :
        ℝ≥0∞) * ε c + qS * εS) +
      ∑' xw, G.gen xw * (qS * δ xw +
        ∑ c, ((qS * (q c + κ.Vc c + κ.μc c * qS) : ℕ) : ℝ≥0∞) * Γ xw c) :=
  (Protocol.eufcmaAdvantage_le_simAdvantage_cls κ hZK hΓ A q hq).trans
    (add_le_add (simAdvantage_le_slMk E hN hlen A q hq) le_rfl)

end Bound

end CatCrypt.Crypto.FiatShamirROM

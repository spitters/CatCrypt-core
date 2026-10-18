/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag

/-!
# Identical until a query in a set

Two stateful oracles `O₁ O₂ : σ → D → PMF (R × σ)` that agree on every query outside a
decidable set `S ⊆ D` give runs of an adaptive adversary whose output distributions
differ, on every event, by at most the probability that the run asks a query in `S`.
That probability is read off the query log: averaged over a secret `x` drawn
independently of the run, it is at most the total query cost times the largest
probability that one query lies in `S x`.

## Main definitions

* `OracleAdv.flagOn S O` — the oracle `O` with a sticky flag set by every query in `S`
* `OracleAdv.withLog O` — the oracle `O` with every query appended to a log

## Main results

* `OracleAdv.run_toOuterMeasure_le_add_flagOn` — for oracles agreeing outside `S`,
  `Pr[run O₁ ∈ E] ≤ Pr[run O₂ ∈ E] + Pr[run asks a query in S]`
* `OracleAdv.run_gap_le_flagOn` — the same for the distance
  `max (Pr₁ - Pr₂) (Pr₂ - Pr₁)` of any output event
* `OracleAdv.run_flagOn_eq_withLog` — the flag is the event that the log holds a query
  in `S`
* `OracleAdv.tsum_flagOn_le` — averaged over a secret `x ~ μ` with
  `μ {x | S x d} ≤ cost d · ε` for every query `d`, a run of query cost at most `n`
  asks a query in `S x` with probability at most `n · ε`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open CatCrypt.Crypto.Constructions.ECBCPRF (toOuterMeasure_flag_eq toOuterMeasure_le_add_flag)
open scoped ENNReal

variable {D R α σ : Type}

/-! ## The flagged and the logging oracle -/

/-- The oracle `O` with a sticky flag that every query in `S` sets. -/
noncomputable def flagOn (S : D → Prop) [DecidablePred S] (O : σ → D → PMF (R × σ)) :
    σ × Bool → D → PMF (R × (σ × Bool)) :=
  fun st d => (O st.1 d).map fun x => (x.1, (x.2, st.2 || decide (S d)))

/-- The oracle `O` with every query appended to a log. -/
noncomputable def withLog (O : σ → D → PMF (R × σ)) :
    σ × List D → D → PMF (R × (σ × List D)) :=
  fun st d => (O st.1 d).map fun x => (x.1, (x.2, d :: st.2))

variable (S : D → Prop) [DecidablePred S]

/-- Forgetting the flag maps a run of `flagOn S O` to the run of `O`. -/
theorem run_flagOn_map (O : σ → D → PMF (R × σ)) (A : OracleAdv D R α) (s : σ) (b : Bool) :
    (run (flagOn S O) A (s, b)).map (Prod.map id Prod.fst) = run O A s :=
  run_map_state (flagOn S O) O Prod.fst
    (fun st d => by simp [flagOn, PMF.map_comp, Function.comp_def]; exact PMF.map_id _) A (s, b)

/-- **Identical until a query in `S`, on outcomes.** Oracles that agree on every
query outside `S` give flagged runs that agree on every outcome with the flag
cleared. -/
theorem run_flagOn_apply_false_eq (O₁ O₂ : σ → D → PMF (R × σ))
    (h : ∀ s d, ¬ S d → O₁ s d = O₂ s d) (A : OracleAdv D R α) (st : σ × Bool) (a : α)
    (t : σ) :
    run (flagOn S O₁) A st (a, (t, false)) = run (flagOn S O₂) A st (a, (t, false)) := by
  have hz : ∀ (O : σ → D → PMF (R × σ)) t d r t',
      flagOn S O (t, true) d (r, (t', false)) = 0 := by
    intro O t d r t'
    simp [flagOn, PMF.map_apply]
  refine run_apply_flag_false_eq _ _ (hz O₁) (hz O₂) (fun s d r t' => ?_) A st a t
  by_cases hd : S d
  · simp [flagOn, PMF.map_apply, hd]
  · simp only [flagOn, h s.1 d hd]

/-- **Identical until a query in `S`.** For oracles that agree on every query outside
`S`, the probability of an output event under the first is at most its probability
under the second plus the probability that the run asks a query in `S`. -/
theorem run_toOuterMeasure_le_add_flagOn (O₁ O₂ : σ → D → PMF (R × σ))
    (h : ∀ s d, ¬ S d → O₁ s d = O₂ s d) (A : OracleAdv D R α) (s : σ) (E : Set α) :
    (run O₁ A s).toOuterMeasure {x | x.1 ∈ E} ≤
      (run O₂ A s).toOuterMeasure {x | x.1 ∈ E} +
        (run (flagOn S O₂) A (s, false)).toOuterMeasure {y | y.2.2 = true} := by
  rw [← run_flagOn_map S O₁ A s false, ← run_flagOn_map S O₂ A s false,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact toOuterMeasure_le_add_flag _ _ (run_flagOn_apply_false_eq S O₁ O₂ h A _) E

/-- Oracles that agree on every query outside `S` ask a query in `S` with the same
probability. -/
theorem run_flagOn_prob_eq (O₁ O₂ : σ → D → PMF (R × σ))
    (h : ∀ s d, ¬ S d → O₁ s d = O₂ s d) (A : OracleAdv D R α) (s : σ) :
    (run (flagOn S O₁) A (s, false)).toOuterMeasure {y | y.2.2 = true} =
      (run (flagOn S O₂) A (s, false)).toOuterMeasure {y | y.2.2 = true} :=
  toOuterMeasure_flag_eq _ _ (run_flagOn_apply_false_eq S O₁ O₂ h A _)

/-- **Distance until a query in `S`.** For oracles that agree on every query outside
`S`, the two output probabilities of any event differ by at most the probability
that the run asks a query in `S`. -/
theorem run_gap_le_flagOn (O₁ O₂ : σ → D → PMF (R × σ))
    (h : ∀ s d, ¬ S d → O₁ s d = O₂ s d) (A : OracleAdv D R α) (s : σ) (E : Set α) :
    max ((run O₁ A s).toOuterMeasure {x | x.1 ∈ E} - (run O₂ A s).toOuterMeasure {x | x.1 ∈ E})
      ((run O₂ A s).toOuterMeasure {x | x.1 ∈ E} - (run O₁ A s).toOuterMeasure {x | x.1 ∈ E}) ≤
      (run (flagOn S O₂) A (s, false)).toOuterMeasure {y | y.2.2 = true} := by
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · exact run_toOuterMeasure_le_add_flagOn S O₁ O₂ h A s E
  · rw [← run_flagOn_prob_eq S O₁ O₂ h A s]
    exact run_toOuterMeasure_le_add_flagOn S O₂ O₁ (fun s d hd => (h s d hd).symm) A s E

/-! ## The flag through the query log -/

/-- The flag of `flagOn S O` is the event that the log of `withLog O` holds a query
in `S`. -/
theorem run_flagOn_eq_withLog (O : σ → D → PMF (R × σ)) (A : OracleAdv D R α) (s : σ) :
    run (flagOn S O) A (s, false) =
      (run (withLog O) A (s, [])).map
        (Prod.map id (Prod.map id fun l => decide (∃ d ∈ l, S d))) := by
  have h := run_map_state (withLog O) (flagOn S O)
    (Prod.map id fun l => decide (∃ d ∈ l, S d))
    (fun st d => by
      simp only [withLog, flagOn, PMF.map_comp]
      congr 1
      funext x
      simp [List.mem_cons, Bool.or_comm]) A (s, [])
  simpa using h.symm

/-- On every outcome of a run of query cost at most `n`, the cost of the log grows by
at most `n`. -/
theorem sum_cost_log_le_of_mem_support (O : σ → D → PMF (R × σ)) (cost : D → ℕ)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBoundBy cost n) (s : σ) (l : List D)
    (y : α × (σ × List D)) (hy : y ∈ (run (withLog O) A (s, l)).support) :
    (y.2.2.map cost).sum ≤ (l.map cost).sum + n := by
  induction A generalizing n s l with
  | ret a =>
    simp only [run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy; simp
  | rand p k ih =>
    simp only [run_rand, PMF.support_bind, Set.mem_iUnion] at hy
    obtain ⟨b, _, hy⟩ := hy
    exact ih b n (hA b) s l hy
  | query d k ih =>
    simp only [run_query, PMF.support_bind, Set.mem_iUnion] at hy
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨hle, hk⟩ := hA
    simp only [withLog, PMF.support_map, Set.mem_image] at hx
    obtain ⟨x', _, rfl⟩ := hx
    have h1 := ih x'.1 (n - cost d) (hk x'.1) x'.2 (d :: l) hy
    simp only [List.map_cons, List.sum_cons] at h1
    omega

/-- A union bound along a list: if each query `d` lies in `S x` with probability at
most `cost d · ε` over `x ~ μ`, some query of the list lies in `S x` with probability
at most the cost of the list times `ε`. -/
theorem toOuterMeasure_exists_mem_le {X : Type} (μ : PMF X) (S : X → D → Prop)
    (cost : D → ℕ) (ε : ℝ≥0∞) (hS : ∀ d, μ.toOuterMeasure {x | S x d} ≤ cost d * ε)
    (l : List D) :
    μ.toOuterMeasure {x | ∃ d ∈ l, S x d} ≤ ((l.map cost).sum : ℝ≥0∞) * ε := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have hset : {x | ∃ d ∈ e :: l, S x d} = {x | S x e} ∪ {x | ∃ d ∈ l, S x d} := by
      ext x; simp
    rw [hset]
    refine (MeasureTheory.measure_union_le _ _).trans ?_
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul]
    exact add_le_add (hS e) ih

/-- **Queries in a secret set, through the log.** Let `x ~ μ` be drawn independently
of the run, and let each query `d` lie in `S x` with probability at most `cost d · ε`.
A run of query cost at most `n` asks a query in `S x` with probability at most
`n · ε`, averaged over `x`. -/
theorem tsum_flagOn_le {X : Type} (μ : PMF X) (S : X → D → Prop) [∀ x, DecidablePred (S x)]
    (O : σ → D → PMF (R × σ)) (cost : D → ℕ) (ε : ℝ≥0∞)
    (hS : ∀ d, μ.toOuterMeasure {x | S x d} ≤ cost d * ε)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBoundBy cost n) (s : σ) :
    ∑' x, μ x * (run (flagOn (S x) O) A (s, false)).toOuterMeasure {y | y.2.2 = true} ≤
      n * ε := by
  classical
  set p := run (withLog O) A (s, [])
  have hx : ∀ x, (run (flagOn (S x) O) A (s, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' y, p y * (if ∃ d ∈ y.2.2, S x d then 1 else 0) := by
    intro x
    rw [run_flagOn_eq_withLog, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun y => ?_
    by_cases h : ∃ d ∈ y.2.2, S x d <;> simp [Set.indicator, h, p]
  have hμ : ∀ l : List D, ∑' x, μ x * (if ∃ d ∈ l, S x d then 1 else 0) =
      μ.toOuterMeasure {x | ∃ d ∈ l, S x d} := by
    intro l
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun x => ?_
    by_cases h : ∃ d ∈ l, S x d <;> simp [Set.indicator, h]
  simp_rw [hx, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  calc ∑' y, ∑' x, μ x * (p y * (if ∃ d ∈ y.2.2, S x d then 1 else 0))
      ≤ ∑' y, p y * (n * ε) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hy : p y = 0
        · simp [hy]
        have hlen : (y.2.2.map cost).sum ≤ n := by
          simpa using sum_cost_log_le_of_mem_support O cost A n hA s [] y
            ((PMF.mem_support_iff _ _).mpr hy)
        calc ∑' x, μ x * (p y * (if ∃ d ∈ y.2.2, S x d then 1 else 0))
            = p y * ∑' x, μ x * (if ∃ d ∈ y.2.2, S x d then 1 else 0) := by
              rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun x => mul_left_comm _ _ _
          _ ≤ p y * (n * ε) := by
              rw [hμ]
              gcongr
              exact (toOuterMeasure_exists_mem_le μ S cost ε hS _).trans
                (by gcongr)
    _ = n * ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end CatCrypt.Crypto.OracleAdv

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleUpTo
public import CatCryptCore.Crypto.Signatures.EUFCMAPMF
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# Programming one point of the lazily sampled random oracle

The lazily sampled random oracle `roOracle` with the point `s` programmed to the value
`y` (`progOracle s y`), and the cost of programming: a run against the oracle whose table
holds `s ↦ y` gives every output event at most its probability against the empty table
plus the probability `queryProb s A` that the run queries `s`.

## Main definitions

* `progOracle` — the lazily sampled oracle with one programmed point
* `queryProb` — the probability that a run from the empty table queries a point

## Main results

* `progOracle_map_update` — recording the programmed point in the table turns
  `progOracle s y` into `roOracle`
* `run_update_le` — programming one point costs at most the probability of querying it
* `run_update_fst_le` — the same for the output bit, in both directions
* `queryProb_eq_log` — the query probability through the query log
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ROProgramming

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

section Programmed

variable {X Y : Type} [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- The lazily sampled random oracle with the point `s` programmed to the value `y`. -/
noncomputable def progOracle (s : X) (y : Y) (T : X → Option Y) (d : X) :
    PMF (Y × (X → Option Y)) :=
  if d = s then PMF.pure (y, T) else roOracle T d

/-- Recording the programmed point in the table turns one call of `progOracle s y` into
    one call of the lazily sampled oracle. -/
theorem progOracle_map_update (s : X) (y : Y) (T : X → Option Y) (d : X) :
    (progOracle s y T d).map (Prod.map id fun T => Function.update T s (some y)) =
      roOracle (Function.update T s (some y)) d := by
  unfold progOracle
  split_ifs with hd
  · subst hd
    simp [roOracle, PMF.pure_map]
  · have hT : Function.update T s (some y) d = T d := Function.update_of_ne hd _ _
    unfold roOracle
    rw [hT]
    rcases T d with _ | h
    · simp only [PMF.map_comp]
      congr 1
      funext h
      simp [Function.update_comm hd]
    · simp [PMF.pure_map]

/-- A run against the oracle whose table holds `s ↦ y` is a run against `progOracle s y`
    from the empty table. -/
theorem run_update_map_fst {α : Type} (s : X) (y : Y) (A : OracleAdv X Y α) :
    (OracleAdv.run roOracle A (Function.update emptyTable s (some y))).map Prod.fst =
      (OracleAdv.run (progOracle s y) A emptyTable).map Prod.fst := by
  rw [← OracleAdv.run_map_state (progOracle s y) roOracle (fun T => Function.update T s (some y))
    (progOracle_map_update s y) A emptyTable, PMF.map_comp]
  rfl

/-- The probability that a run of `A` against the lazily sampled oracle from the empty
    table queries the point `s`. -/
noncomputable def queryProb {α : Type} (s : X) (A : OracleAdv X Y α) : ℝ≥0∞ :=
  (OracleAdv.run (OracleAdv.flagOn (· = s) roOracle) A (emptyTable, false)).toOuterMeasure
    {z | z.2.2 = true}

/-- The probability of an event of the first component as an outer measure. -/
theorem map_apply_eq_toOuterMeasure {α σ : Type} (p : PMF (α × σ)) (f : α → Bool) :
    (p.map fun z => f z.1) true = p.toOuterMeasure {z | z.1 ∈ {a | f a = true}} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- The probability of a value of the first component as an outer measure. -/
theorem map_fst_apply_eq {α σ : Type} (p : PMF (α × σ)) (a : α) :
    (p.map Prod.fst) a = p.toOuterMeasure {x | x.1 ∈ ({a} : Set α)} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Programming one point costs at most the probability of querying it.** A run against
    the oracle whose table holds `s ↦ y` gives every output event at most its probability
    against the empty table plus the probability of querying `s`. -/
theorem run_update_le {α : Type} (s : X) (y : Y) (A : OracleAdv X Y α) (f : α → Bool) :
    ((OracleAdv.run roOracle A (Function.update emptyTable s (some y))).map fun z => f z.1)
        true ≤
      ((OracleAdv.run roOracle A emptyTable).map fun z => f z.1) true + queryProb s A := by
  have hagree : ∀ (T : X → Option Y) d, ¬ (d = s) → progOracle s y T d = roOracle T d :=
    fun T d hd => if_neg hd
  have hmap := OracleAdv.run_map_state (progOracle s y) roOracle
    (fun T => Function.update T s (some y)) (progOracle_map_update s y) A emptyTable
  rw [map_apply_eq_toOuterMeasure, map_apply_eq_toOuterMeasure, ← hmap,
    PMF.toOuterMeasure_map_apply]
  have h := OracleAdv.run_toOuterMeasure_le_add_flagOn (· = s) _ _ hagree A emptyTable
    {a | f a = true}
  exact h

/-- **Programming one point costs at most the probability of querying it**, for the output
    bit and in both directions. -/
theorem run_update_fst_le (s : X) (y : Y) (A : OracleAdv X Y Bool) :
    ((OracleAdv.run roOracle A (Function.update emptyTable s (some y))).map Prod.fst) true ≤
        ((OracleAdv.run roOracle A emptyTable).map Prod.fst) true + queryProb s A ∧
      ((OracleAdv.run roOracle A emptyTable).map Prod.fst) true ≤
        ((OracleAdv.run roOracle A (Function.update emptyTable s (some y))).map Prod.fst) true +
          queryProb s A := by
  have hagree : ∀ (T : X → Option Y) d, ¬ (d = s) → progOracle s y T d = roOracle T d :=
    fun T d hd => if_neg hd
  rw [run_update_map_fst, map_fst_apply_eq, map_fst_apply_eq]
  refine ⟨OracleAdv.run_toOuterMeasure_le_add_flagOn (· = s) _ _ hagree A emptyTable {true}, ?_⟩
  unfold queryProb
  rw [← OracleAdv.run_flagOn_prob_eq (· = s) _ _ hagree A emptyTable]
  exact OracleAdv.run_toOuterMeasure_le_add_flagOn (· = s) _ _
    (fun T d hd => (hagree T d hd).symm) A emptyTable {true}

/-- The query probability through the query log. -/
theorem queryProb_eq_log {α : Type} (s : X) (A : OracleAdv X Y α) :
    queryProb s A = ∑' z, OracleAdv.run (OracleAdv.withLog roOracle) A (emptyTable, []) z *
      (if ∃ d ∈ z.2.2, d = s then 1 else 0) := by
  classical
  unfold queryProb
  rw [OracleAdv.run_flagOn_eq_withLog, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun z => ?_
  by_cases h : ∃ d ∈ z.2.2, d = s <;> simp [Set.indicator]

end Programmed

end CatCrypt.Crypto.ROProgramming

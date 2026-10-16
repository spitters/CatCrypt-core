/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleForkingLemma
public import CatCryptCore.Crypto.OracleSimulation

/-!
# Bad draws in an oracle run

An adversary `A : OracleAdv D R α` runs against a stateful oracle
`O : S → D → PMF (R × S)` (`OracleAdv.run`), and `bad : S → Prop` is a predicate on
oracle states. A query `d` draws `cost d` fresh values, and from every state without
`bad` one call `O s d` reaches a `bad` state with probability at most `cost d · ε`.
When the queries of every path of `A` cost at most `D` in total
(`OracleAdv.IsQueryBoundBy cost A D`), a run from a state without `bad` ends in a
`bad` state with probability at most `D · ε`. The predicate need not be preserved
by the oracle: the bound covers the final state of the run.

## Main results

* `OracleAdv.run_badDraw_le` — a run with total draw cost at most `D`, each draw
  reaching `bad` with probability at most `ε` given the state before it, ends in a
  `bad` state with probability at most `D · ε`
* `OracleAdv.run_badDraw_le_of_isQueryBound` — the case of one draw per query
  under `OracleAdv.IsQueryBound`
* `OracleAdv.IsQueryBound.isQueryBoundBy_one` — a query bound is a cost bound for
  the unit cost
* `OracleForking.IsQueryBound₂.isQueryBoundBy` — a bound of `h` queries of the left
  kind and `q` of the right kind is a cost bound `a·h + b·q` for the costs `a` and
  `b` per query of each kind
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open scoped ENNReal

namespace OracleAdv

variable {D R α : Type}

/-- **Bad draws.** Let every call `O s d` from a state `s` without `bad` reach a
`bad` state with probability at most `cost d · ε`. A run of an adversary whose
queries cost at most `n` in total on every path, started from a state without
`bad`, ends in a `bad` state with probability at most `n · ε`. -/
theorem run_badDraw_le {S : Type} (O : S → D → PMF (R × S)) (bad : S → Prop)
    (cost : D → ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ s d, ¬ bad s → (O s d).toOuterMeasure {x | bad x.2} ≤ cost d * ε)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBoundBy cost n) (s : S) (hs : ¬ bad s) :
    (run O A s).toOuterMeasure {y | bad y.2} ≤ n * ε := by
  classical
  induction A generalizing n s with
  | ret a => simp [PMF.toOuterMeasure_pure_apply, hs]
  | rand p k ih =>
    rw [run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (run O (k b) s).toOuterMeasure {y | bad y.2}
        ≤ ∑' b, p b * (n * ε) :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b n (hA b) s hs
      _ = n * ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    obtain ⟨hle, hk⟩ := hA
    rw [run_query, PMF.toOuterMeasure_bind_apply]
    calc ∑' x, O s d x * (run O (k x.1) x.2).toOuterMeasure {y | bad y.2}
        ≤ ∑' x, ({x : R × S | bad x.2}.indicator (O s d) x +
            O s d x * ((n - cost d : ℕ) * ε)) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : bad x.2
          · rw [Set.indicator_of_mem (show x ∈ {x : R × S | bad x.2} from hx)]
            refine (mul_le_of_le_one_right' ?_).trans le_self_add
            exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
              ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
          · rw [Set.indicator_of_notMem (show x ∉ {x : R × S | bad x.2} from hx), zero_add]
            gcongr
            exact ih x.1 _ (hk x.1) x.2 hx
      _ = (O s d).toOuterMeasure {x | bad x.2} + (n - cost d : ℕ) * ε := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
      _ ≤ cost d * ε + (n - cost d : ℕ) * ε := by gcongr; exact hstep s d hs
      _ = n * ε := by rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hle]

/-- A bound of `n` queries on every path is a bound of total cost `n` for the cost
`1` per query. -/
theorem IsQueryBound.isQueryBoundBy_one {A : OracleAdv D R α} {n : ℕ}
    (hA : A.IsQueryBound n) : A.IsQueryBoundBy (fun _ => 1) n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n => exact ⟨Nat.le_add_left 1 n, fun r => ih r (hA r)⟩

/-- **Bad draws, one per query.** If every call from a state without `bad` reaches
a `bad` state with probability at most `ε`, a run of an adversary asking at most
`n` queries, started from a state without `bad`, ends in a `bad` state with
probability at most `n · ε`. -/
theorem run_badDraw_le_of_isQueryBound {S : Type} (O : S → D → PMF (R × S))
    (bad : S → Prop) (ε : ℝ≥0∞)
    (hstep : ∀ s d, ¬ bad s → (O s d).toOuterMeasure {x | bad x.2} ≤ ε)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBound n) (s : S) (hs : ¬ bad s) :
    (run O A s).toOuterMeasure {y | bad y.2} ≤ n * ε :=
  run_badDraw_le O bad (fun _ => 1) ε (fun s d h => by simpa using hstep s d h) A n
    hA.isQueryBoundBy_one s hs

end OracleAdv

namespace OracleForking

/-- A bound of `h` queries in `D₁` and `q` queries in `D₂` on every path is a bound
of total cost `a·h + b·q` for the cost `a` per query in `D₁` and `b` per query in
`D₂`. -/
theorem IsQueryBound₂.isQueryBoundBy {D₁ D₂ R α : Type} {A : OracleAdv (D₁ ⊕ D₂) R α}
    {h q : ℕ} (hA : IsQueryBound₂ A h q) (a b : ℕ) :
    A.IsQueryBoundBy (Sum.elim (fun _ => a) fun _ => b) (a * h + b * q) := by
  induction A generalizing h q with
  | ret x => trivial
  | rand p k ih => exact fun c => ih c (hA c)
  | query d k ih =>
    cases d with
    | inl d =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        refine ⟨by simp only [Sum.elim_inl]; nlinarith, fun r => ?_⟩
        simpa only [Sum.elim_inl, show a * (h + 1) + b * q - a = a * h + b * q by
          rw [Nat.mul_succ]; omega] using ih r (hA r)
    | inr d =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        refine ⟨by simp only [Sum.elim_inr]; nlinarith, fun r => ?_⟩
        simpa only [Sum.elim_inr, show a * h + b * (q + 1) - b = a * h + b * q by
          rw [Nat.mul_succ]; omega] using ih r (hA r)

end OracleForking

end CatCrypt.Crypto

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCryptCore.Container.ExpectedDN
public meta import CatCryptCore.Core.SPTreeTimed

/-!
# The operational retry loop at expected demands, and the threshold extractor

`retryClocked X p c` (`Container/ExpectedDN.lean`) is the retry loop as a costed function with
expected use counts: at a trial of expected time `T` and a loop cost `c` per trial, its expected
time is `(c + T) / p`. `retryN body n` (`Unary/ExpectedCost.lean`) is the operational loop with
fuel `n` over a cost-instrumented trial. This file proves that the expected cost of the
operational loop is at most the expected time of `retryClocked`, uniformly in the fuel
(`ecost_retryN_le_retryClocked_time`), and the instance at a costed tree with a worst-case time
bound (`ecost_retryN_compileTimed_le`).

The fuel-`n` loops are the Kleene approximants of the unbounded loop, and a bound uniform in `n`
is the upper-invariant bound of the ert calculus for loops (Kaminski et al., Thm. 4.2) at those
approximants.

The threshold extractor `collectN body n k` runs `k` retry loops in sequence and returns the `k`
results; a loop that exhausts its fuel makes the extractor fail. Its expected cost is at most
`k * (C / p)` (`ecost_collectN_le`), by the sequential-composition rule of the ert calculus
(`ecost_bind_le`).

## Main definitions

* `collectN` — the threshold extractor: `k` successes, each found by a retry loop with fuel `n`

## Main results

* `ecost_retryN_le_retryClocked_time`, `ecost_retryN_compileTimed_le`
* `ecost_collectN_le`

## References

* Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja, Federico Olmedo,
  *Weakest Precondition Reasoning for Expected Runtimes of Randomized Algorithms*,
  J. ACM 65(5), 2018 — sequential composition (Table 1), upper invariants for loops (Thm. 4.2).
* Mihir Bellare, Oded Goldreich, *On Defining Proofs of Knowledge*, CRYPTO 1992, §6 — repeating
  an extraction attempt until it succeeds gives expected time `poly / Pr[success]`.

Search words: expected time, retry loop, rewinding, threshold extractor, k-special soundness,
geometric retries, expected demands.
-/

public meta section

set_option autoImplicit false

open scoped NNReal ENNReal

namespace CatCrypt.Container

open CatCrypt.Core CatCrypt.Unary

/-- The fuel-`n` retry loop costs at most the expected time of `retryClocked` in expectation,
uniformly in the fuel: per-trial expected cost at most `c + T` and success probability at least
`p > 0` give `(c + T) / p`. -/
theorem ecost_retryN_le_retryClocked_time {β X : Type} (body : CostComp (Option β))
    {p c T : ℝ≥0} (hp0 : 0 < p) (hp1 : p ≤ 1) (hC : ∀ h, ecost body h ≤ ((c + T : ℝ≥0) : ℝ≥0∞))
    (hfail : ∀ h, failProb body h ≤ 1 - (p : ℝ≥0∞)) (n : ℕ) (h : Heap) (a : X) :
    ecost (retryN body n) h ≤ ((retryClocked X p c).time T a : ℝ≥0∞) := by
  have hp1' : (p : ℝ≥0∞) ≤ 1 := by exact_mod_cast hp1
  refine le_trans (ecost_retryN_le_div body hp1' hC hfail n h) (le_of_eq ?_)
  rw [retryClocked_time, ENNReal.coe_mul, ENNReal.coe_inv hp0.ne', div_eq_mul_inv]

/-- A costed trial with worst-case time `T`, retried: the fuel-`n` loop costs at most the expected
time `T / p` of `retryClocked` at loop cost `0`. -/
theorem ecost_retryN_compileTimed_le {β X : Type} (trial : SPTree.Timed (Option β)) {T : ℕ}
    (ht : trial.TimeBound T) {p : ℝ≥0} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hfail : ∀ h, failProb (compileTimed trial) h ≤ 1 - (p : ℝ≥0∞)) (n : ℕ) (h : Heap) (a : X) :
    ecost (retryN (compileTimed trial) n) h ≤ ((retryClocked X p 0).time T a : ℝ≥0∞) := by
  refine ecost_retryN_le_retryClocked_time _ hp0 hp1 (fun h' => ?_) hfail n h a
  simpa using ecost_compileTimed_le_of_timeBound trial ht h'

/-- The threshold extractor: `k` successes, each found by a retry loop with fuel `n`, returned in
the order found. A loop that exhausts its fuel makes the extractor fail. -/
noncomputable def collectN {β : Type} (body : CostComp (Option β)) (n : ℕ) :
    ℕ → CostComp (List β)
  | 0 => CostComp.pure []
  | k + 1 => CostComp.bind (retryN body n) fun r =>
      match r with
      | some b => CostComp.bind (collectN body n k) fun l => CostComp.pure (b :: l)
      | none => CostComp.fail

/-- **The threshold extractor's expected cost.** Sequencing adds expected times: `k` retry loops,
each at most `C / p` in expectation, cost at most `k * (C / p)`. -/
theorem ecost_collectN_le {β : Type} (body : CostComp (Option β)) {C p : ℝ≥0∞} (hp : p ≤ 1)
    (hC : ∀ h, ecost body h ≤ C) (hfail : ∀ h, failProb body h ≤ 1 - p) (n k : ℕ) (h : Heap) :
    ecost (collectN body n k) h ≤ k * (C / p) := by
  induction k generalizing h with
  | zero => simp [collectN]
  | succ k ih =>
    rw [collectN]
    have hcont : ∀ (r : Option β) (h' : Heap), ecost (match r with
        | some b => CostComp.bind (collectN body n k) fun l => CostComp.pure (b :: l)
        | none => CostComp.fail) h' ≤ k * (C / p) := by
      intro r h'
      cases r with
      | none => simp
      | some b =>
        simpa using ecost_bind_le_add (C₂ := 0) (fun h'' => ih h'')
          (fun l h'' => le_of_eq (ecost_pure (b :: l) h'')) h'
    refine le_trans (ecost_bind_le_add (fun h' => ecost_retryN_le_div body hp hC hfail n h')
      hcont h) (le_of_eq ?_)
    push_cast
    ring

end CatCrypt.Container

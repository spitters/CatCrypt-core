/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DerivePMF
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.Crypto.OracleUpTo

/-!
# Tests for the potential time bound of a costed oracle simulation

* `logRun`: an adversary run against the logged lazily sampled random oracle
  `withLog roOracle` from the empty table. Its costed form is derived by `derive_timed`; the
  step reads the table at its cost companion and a fresh query writes it.

## Main results

* `logRun.pmfStep.table_timed` — one costed step: time `4 + c d` for the companion `c` of the
  table, which grows by at most `3` at every point
* `logRun.timeBound_timed` — the time `T + q * (5 + 3 * q)` of the costed run, by the potential
  corollary `OracleAdv.Timed.timeBound_simulateHat_table`
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.SimulatePotentialTest

open CatCrypt.Crypto

/-- The bit of an adversary run against the logged lazily sampled random oracle from the empty
table. -/
noncomputable def logRun (A : OracleAdv ℕ (Fin 4) Bool) : PMF Bool :=
  (OracleAdv.run (OracleAdv.withLog roOracle) A (emptyTable, [])).map Prod.fst

derive_timed logRun

/-- **One costed step of the oracle.** With the unit of its call, the step takes time at most
`4 + c d` for the companion `c` of the table read at the query `d`; a fresh query writes the
table, whose companion grows by at most `3` at every point. -/
theorem logRun.pmfStep.table_timed (s : ((ℕ → Option (Fin 4)) × (ℕ → ℕ)) × List ℕ) (d : ℕ) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1 (logRun.pmfStep.timed s d))
        (4 + 1 * s.1.2 d) ∧
      OracleAdv.Timed.AllRet (fun y => ∀ x, y.2.1.2 x ≤ s.1.2 x + 3)
        (OracleAdv.Timed.delay 1 (logRun.pmfStep.timed s d)).2 := by
  simp only [logRun.pmfStep.timed, OracleAdv.Timed.delay]
  split <;> simp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.bind,
    OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet] <;> grind

/-- **Time of the costed run.** An adversary of time `T` with at most `q` queries runs against
the costed oracle from the empty table (companion `fun _ => 1`) in time at most
`T + q * (5 + 3 * q)`: the `j`-th query reads a companion of at most `1 + 3 j`. -/
theorem logRun.timeBound_timed {A : OracleAdv.Timed ℕ (Fin 4) Bool} {T q : ℕ}
    (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (logRun.timed A) (T + q * (5 + 3 * q)) := by
  unfold logRun.timed logRun.pmfTree.timed
  have h := OracleAdv.Timed.timeBound_simulateHat_table
    (fun y : ((ℕ → Option (Fin 4)) × (ℕ → ℕ)) × List ℕ => (y.1.1, y.2))
    (fun y => ((fun a => y.1 a, fun _ => 0), y.2)) _ (fun s => s.1.2) id 4 1 3
    logRun.pmfStep.table_timed hA hq (M₀ := 1) (s₀ := ((emptyTable, fun _ => 1), []))
    (fun _ => le_rfl)
  refine (OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.timeBound_bind (n := 0) h.2
    fun _ => ?_)).mono ?_
  · exact ⟨le_rfl, trivial⟩
  · have := h.1
    grind

end CatCrypt.Tactics.SimulatePotentialTest

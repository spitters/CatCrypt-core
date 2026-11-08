/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DerivePMF
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Crypto.OracleUpTo
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.ForMathlib.ListLength
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests for the potential time bound of a costed oracle simulation

* `logRun`: an adversary run against the logged lazily sampled random oracle
  `withLog roOracle` from the empty table. Its costed form is derived by `derive_timed`; the
  step reads the table at its cost companion and a fresh query writes it.

## Main results

* `logRun.timeBound_timed` — the time `T + q * (3 * q + 5)` of the costed run, derived by
  `derive_time_bound` through its simulation rule (the potential corollary
  `OracleAdv.Timed.timeBound_simulateHat_potLe`)
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

derive_time_bound logRun

/-- **Time of the costed run.** An adversary of time `T` with at most `q` queries runs against
the costed oracle from the empty table (companion `fun _ => 1`) in time at most
`T + q * (5 + 3 * q)`: the `j`-th query reads a companion of at most `1 + 3 j`. The bound is that
of the derived theorem `logRun.timeBound_timed`. -/
example {A : OracleAdv.Timed ℕ (Fin 4) Bool} {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (logRun.timed A) (T + q * (5 + 3 * q)) :=
  (logRun.timeBound_timed A hA hq).mono (le_of_eq (by ring))

end CatCrypt.Tactics.SimulatePotentialTest

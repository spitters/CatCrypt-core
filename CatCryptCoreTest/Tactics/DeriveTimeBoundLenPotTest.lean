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
public import CatCryptCore.Tactics.StdCostsMem

/-!
# Tests of the length potential of the simulation rule of `derive_time_bound`

Fresh definitions whose costed forms (`derive_timed`) run an adversary against an oracle whose
state holds lists, so that the potential of the simulation rule reads the lengths of the lists
and of the lists held by their members:

* `logRun`: a log of the queries, each query answered by a membership test in the log; a step
  linear in the length of the log, a bound quadratic in the query count;
* `corrRun`: a log and a list of corruptions, each recording the logged queries up to it, a
  delivery answered by a membership test in every record; a step quadratic in the potential
  (the bound `List.any.timedCost_le_mem` of the scan, its premise closed under the member-length
  atom), a bound cubic in the query count;
* `tabLogRun`: a costed table beside a log, a state with a companion atom and a length atom;
* `dupRun`: a log appended to itself at every step, whose length is not bounded by the potential
  plus a constant, refused.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundLenPotTest

open CatCrypt.Crypto

/-- An oracle that logs its queries and answers whether the query was logged before. -/
noncomputable def logOracle (s : List ℕ) (d : ℕ) : PMF (Bool × List ℕ) :=
  PMF.pure (List.elem d s, d :: s)

/-- The bit of an adversary run against the logging oracle from the empty log. -/
noncomputable def logRun (A : OracleAdv ℕ Bool Bool) : PMF Bool :=
  (OracleAdv.run logOracle A []).map Prod.fst

derive_timed logRun

derive_time_bound logRun

/-- The derived bound: a step linear in the length of the log, a log that grows by one entry per
query, so `T + q * (c₁ * q + c₀)`. -/
example (A : OracleAdv.Timed ℕ Bool Bool) {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (logRun.timed A) (T + q * (4 * q + 3)) :=
  logRun.timeBound_timed A hA hq

/-- A log of queries and a list of corruptions, each recording the logged queries up to it: a
query `.inl d` is logged and answered by whether some corruption recorded `d`, a query `.inr d`
records a corruption at `d`. -/
noncomputable def corrOracle (s : List ℕ × List (ℕ × List ℕ)) :
    ℕ ⊕ ℕ → PMF (Bool × (List ℕ × List (ℕ × List ℕ)))
  | .inl d => PMF.pure (s.2.any (fun c => List.elem d c.2), (d :: s.1, s.2))
  | .inr d => PMF.pure (false, (s.1, (d, s.1.filter (· ≤ d)) :: s.2))

/-- The bit of an adversary run against the corruption oracle from the empty state. -/
noncomputable def corrRun (A : OracleAdv (ℕ ⊕ ℕ) Bool Bool) : PMF Bool :=
  (OracleAdv.run corrOracle A ([], [])).map Prod.fst

derive_timed corrRun

derive_time_bound corrRun

/-- The derived bound: a step quadratic in the potential `n` (a scan of the corruptions with a
scan of each record), `T + q * C (n₀ + q * g)` with `C n = c₀ + c₁ * n + c₂ * (n * n)`, here
`c₀ = 4`, `c₁ = 7`, `c₂ = 4`, `n₀ = 0`, `g = 1`: cubic in `q`. -/
example (A : OracleAdv.Timed (ℕ ⊕ ℕ) Bool Bool) {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (corrRun.timed A)
      (T + q * (7 * (q * 1) + 4 * (q * 1 * (q * 1)) + 4)) :=
  corrRun.timeBound_timed A hA hq

/-- The lazily sampled random oracle beside a log of the queries. -/
noncomputable def tabLogOracle (s : (ℕ → Option Bool) × List ℕ) (d : ℕ) :
    PMF (Bool × ((ℕ → Option Bool) × List ℕ)) :=
  (roOracle s.1 d).map fun x => (x.1, (x.2, d :: s.2))

/-- The bit of an adversary run against the logged random oracle from the empty table. -/
noncomputable def tabLogRun (A : OracleAdv ℕ Bool Bool) : PMF Bool :=
  (OracleAdv.run tabLogOracle A (emptyTable, [])).map Prod.fst

derive_timed tabLogRun

derive_time_bound tabLogRun

/-- The derived bound: the companion of the table and the length of the log under one bound,
`n₀ = 1` (the maximum of the companion of the empty table and the length of the empty log),
`g = 3`. -/
example (A : OracleAdv.Timed ℕ Bool Bool) {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (tabLogRun.timed A) (T + q * (3 * q + 5)) :=
  tabLogRun.timeBound_timed A hA hq

/-- An oracle that appends its log to itself. -/
noncomputable def dupOracle (s : List ℕ) (d : ℕ) : PMF (ℕ × List ℕ) := PMF.pure (d, s ++ s)

/-- The bit of an adversary run against the doubling oracle. -/
noncomputable def dupRun (A : OracleAdv ℕ ℕ Bool) : PMF Bool :=
  (OracleAdv.run dupOracle A [0]).map Prod.fst

derive_timed dupRun

/--
error: `CatCrypt.Tactics.DeriveTimeBoundLenPotTest.dupRun.timeBound_timed` is not proved: no bound: the simulation
  OracleAdv.Timed.simulate (fun s d ↦ OracleAdv.Timed.delay 1 (dupRun.pmfStep.timed s d)) A [0]
is not bounded by the potential corollary: the growth of the companion of the state at a step:
the companion
  (s ++ s).length
is bounded by 2 times the companion before the step
-/
#guard_msgs in
derive_time_bound dupRun

end CatCrypt.Tactics.DeriveTimeBoundLenPotTest

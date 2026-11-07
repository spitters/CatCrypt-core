/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DerivePMF
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Crypto.OracleUpTo

/-!
# Tests of the simulation rule of `derive_time_bound`

Fresh definitions whose costed forms (`derive_timed`) run an adversary against a stateful oracle,
so that their time theorems go through a simulation node of the costed tree:

* `roRun`: the lazily sampled random oracle `roOracle` from the empty table, a state that is a
  costed table alone;
* `flagRun`: the same oracle with a sticky flag (`flagOn`), a state with the table beside a
  Boolean;
* `countRun`: an oracle that counts its queries, a state without a cost companion, whose step has
  a uniform cost;
* `twoRun`: two lazily sampled tables, a state with two cost companions, refused;
* `lenRun`: an oracle whose step reads the length of the state, outside a cost companion,
  refused.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundSimulationTest

open CatCrypt.Crypto

/-- The bit of an adversary run against the lazily sampled random oracle from the empty table. -/
noncomputable def roRun (A : OracleAdv ℕ Bool Bool) : PMF Bool :=
  (OracleAdv.run roOracle A emptyTable).map Prod.fst

derive_timed roRun

derive_time_bound roRun

/-- The derived bound: the `j`-th query reads a companion of at most `1 + 3 j`. -/
example (A : OracleAdv.Timed ℕ Bool Bool) {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (roRun.timed A) (T + q * (3 * q + 5)) :=
  roRun.timeBound_timed A hA hq

/-- The bit of an adversary run against the random oracle with a flag set by the query `0`. -/
noncomputable def flagRun (A : OracleAdv ℕ Bool Bool) : PMF Bool :=
  (OracleAdv.run (OracleAdv.flagOn (fun d => d = 0) roOracle) A (emptyTable, false)).map
    Prod.fst

derive_timed flagRun

derive_time_bound flagRun

/-- The derived bound: the flag adds `3` to the cost of every query. -/
example (A : OracleAdv.Timed ℕ Bool Bool) {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (flagRun.timed A) (T + q * (3 * q + 8)) :=
  flagRun.timeBound_timed A hA hq

/-- An oracle that answers the query count. -/
noncomputable def countOracle (s : ℕ) (_ : ℕ) : PMF (ℕ × ℕ) := PMF.pure (s, s + 1)

/-- The bit of an adversary run against the counting oracle. -/
noncomputable def countRun (A : OracleAdv ℕ ℕ Bool) : PMF Bool :=
  (OracleAdv.run countOracle A 0).map Prod.fst

derive_timed countRun

derive_time_bound countRun

/-- The derived bound: a state without a cost companion, a step of uniform cost `2`. -/
example (A : OracleAdv.Timed ℕ ℕ Bool) {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (countRun.timed A) (T + q * 2) :=
  countRun.timeBound_timed A hA hq

/-- Two lazily sampled tables, the query `.inl d` answered by the first and `.inr d` by the
second. -/
noncomputable def twoOracle (s : (ℕ → Option Bool) × (ℕ → Option Bool)) :
    ℕ ⊕ ℕ → PMF (Bool × ((ℕ → Option Bool) × (ℕ → Option Bool)))
  | .inl d => (roOracle s.1 d).map fun x => (x.1, (x.2, s.2))
  | .inr d => (roOracle s.2 d).map fun x => (x.1, (s.1, x.2))

/-- The bit of an adversary run against two tables. -/
noncomputable def twoRun (A : OracleAdv (ℕ ⊕ ℕ) Bool Bool) : PMF Bool :=
  (OracleAdv.run twoOracle A (emptyTable, emptyTable)).map Prod.fst

derive_timed twoRun

/--
error: `CatCrypt.Tactics.DeriveTimeBoundSimulationTest.twoRun.timeBound_timed` is not proved: no bound: the simulation
  OracleAdv.Timed.simulateHat (fun y ↦ (y.1.1, y.2.1)) (fun y ↦ ((fun a ↦ y.1 a, fun a ↦ 0), fun a ↦ y.2 a, fun a ↦ 0))
    (fun s d ↦ OracleAdv.Timed.delay 1 (twoRun.pmfStep.timed s d)) A ((emptyTable, fun a ↦ 1), emptyTable, fun a ↦ 1)
is not bounded by the potential corollary: the values of type
  ((ℕ → Option Bool) × (ℕ → ℕ)) × (ℕ → Option Bool) × (ℕ → ℕ)
have several cost companions [v.1.2, v.2.2]
-/
#guard_msgs in
derive_time_bound twoRun

/-- An oracle that answers the length of its log, whose step reads the state outside a cost
companion. -/
noncomputable def lenOracle (s : List ℕ) (d : ℕ) : PMF (ℕ × List ℕ) := PMF.pure (s.length, d :: s)

/-- The bit of an adversary run against the oracle of its log length. -/
noncomputable def lenRun (A : OracleAdv ℕ ℕ Bool) : PMF Bool :=
  (OracleAdv.run lenOracle A []).map Prod.fst

derive_timed lenRun

/--
error: `CatCrypt.Tactics.DeriveTimeBoundSimulationTest.lenRun.timeBound_timed` is not proved: no bound: the simulation
  OracleAdv.Timed.simulate (fun s d ↦ OracleAdv.Timed.delay 1 (lenRun.pmfStep.timed s d)) A []
is not bounded by the potential corollary: no bound of a step
  OracleAdv.Timed.delay 1 (lenRun.pmfStep.timed s d)
no bound of the charge
  1 + (1 + List.length.timedCost s)
free of the values bound in the program
-/
#guard_msgs in
derive_time_bound lenRun

end CatCrypt.Tactics.DeriveTimeBoundSimulationTest

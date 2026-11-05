/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgUseBound

/-!
# Tests of use bounds of oracle programs at `{query, tick}`

Fresh definitions, none taken from a protocol: a costed oracle program with two queries, a
handler program with one query, and a handler program with one query and one record. The
composite time and query count come out of one application of the composition rule; a vector
bound is priced into a scalar bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleProg.UseBoundTest

open CatCrypt.Container PFunctor

/-- A program with two queries: it asks on `x`, then on the answer plus one, at step costs `1`
and `2`, and returns the sum of the answers. Time `1 + 1 + 1 + 2 = 5`, two queries. -/
def twoQ (x : ℕ) : Timed ℕ ℕ ℕ :=
  .query x (fun _ => 1) fun o => .query (o + 1) (fun _ => 2) fun o' => .pure (o + o')

/-- A handler program: step cost `1`, then one query on whether `i` is zero. Time `2`, one
query. -/
def hd (i : ℕ) : ℕ × Timed Bool Bool ℕ :=
  (1, .query (decide (i = 0)) (fun _ => 0) fun b => .pure (if b then 0 else i))

/-- A handler program with records: one query, at step cost `1`, and the record `[i]`. Time `2`,
one query, records of length `1`. -/
def hr (i : ℕ) : ℕ × Timed Bool Bool (ℕ × List ℕ) :=
  (0, .query true (fun _ => 1) fun _ => .pure (i, [i]))

theorem twoQ_timeBound (x : ℕ) : (twoQ x).TimeBound 5 := by
  simp [twoQ, Timed.TimeBound]

theorem twoQ_queryCostLe (x : ℕ) : QueryCostLe (fun _ => 1) (twoQ x).erase 2 := by
  simp [twoQ, Timed.erase, QueryCostLe]

theorem hd_bound (i : ℕ) :
    Timed.StepTimeBound (hd i) 2 ∧ QueryCostLe (fun _ => 1) (hd i).2.erase 1 := by
  simp [hd, Timed.StepTimeBound, Timed.TimeBound, Timed.erase, QueryCostLe]

theorem hr_bound (i : ℕ) :
    Timed.StepTimeBound (hr i) 2 ∧ QueryCostLe (fun _ => 1) (hr i).2.erase 1 := by
  simp [hr, Timed.StepTimeBound, Timed.TimeBound, Timed.erase, QueryCostLe]

theorem hr_allRet (i : ℕ) : (hr i).2.AllRet fun rl => rl.2.length ≤ 1 := by
  simp [hr, Timed.AllRet]

/-- The two budgets of `twoQ` as one use bound. -/
theorem twoQ_useBound (x : ℕ) :
    UseBound (useCharge fun _ => 1) (fun _ _ => True) (Timed.toFreeMT (twoQ x)) (budget 2 5) :=
  (Timed.useBound_iff_timeBound_and_queryCostLe _ _ 2 5).2 ⟨twoQ_timeBound x, twoQ_queryCostLe x⟩

/-- `bindQueries`: time `5 + 2 * 2` and `2 * 1` queries from one step of the composition rule. -/
example (x : ℕ) :
    Timed.StepTimeBound (Timed.bindQueries hd (twoQ x)) 9 ∧
      QueryCostLe (fun _ => 1) (Timed.bindQueries hd (twoQ x)).2.erase 2 :=
  Timed.stepTimeBound_bindQueries_queryCostLe _ hd_bound (twoQ_timeBound x) (twoQ_queryCostLe x)

/-- The vector form of the same composite, at general vectors. -/
example (x : ℕ) :
    UseBound (useCharge fun _ => 1) (fun _ _ => True)
      (Timed.stepToFreeMT (Timed.bindQueries hd (twoQ x))) (budget 2 9) := by
  have h := Timed.useBound_bindQueries (fun _ => 1) (twoQ_useBound x)
    (fun i => (Timed.useBound_step_iff _ _ 1 2).2 (hd_bound i))
  refine h.mono fun j => ?_
  cases j <;> norm_num [Timed.queryDemand]

/-- `collectLog`: time `5 + 2 * (2 + 2 * 1 + 1)` and `2 * 1` queries. -/
example (x : ℕ) :
    Timed.StepTimeBound (Timed.collectLog hr (twoQ x)) 15 ∧
      QueryCostLe (fun _ => 1) (Timed.collectLog hr (twoQ x)).2.erase 2 :=
  Timed.stepTimeBound_collectLog_queryCostLe _ hr_bound hr_allRet (twoQ_timeBound x)
    (twoQ_queryCostLe x)

/-- The time component alone, without a query bound on the handler. -/
example (x : ℕ) : Timed.StepTimeBound (Timed.bindQueries hd (twoQ x)) 9 :=
  Timed.timeBound_bindQueries (fun i => (hd_bound i).1) (twoQ_timeBound x) (twoQ_queryCostLe x)

/-- Sequencing behind a step cost: `bindQueries hd (twoQ x)` followed by a continuation of
time `1`, behind `3` units, has time `3 + 9 + 1` and still two queries. -/
example (x : ℕ) :
    Timed.StepTimeBound (Timed.delay (3 + (Timed.bindQueries hd (twoQ x)).1)
        ((Timed.bindQueries hd (twoQ x)).2.bind fun o => (1, .pure o))) 13 ∧
      QueryCostLe (fun _ => 1) (Timed.delay (3 + (Timed.bindQueries hd (twoQ x)).1)
        ((Timed.bindQueries hd (twoQ x)).2.bind fun o => (1, .pure o))).2.erase 2 := by
  refine (Timed.useBound_step_iff _ _ 2 13).1 ((Timed.useBound_step_delay_bind _ 3
    ((Timed.useBound_step_iff _ _ 2 9).2 (Timed.stepTimeBound_bindQueries_queryCostLe _ hd_bound
      (twoQ_timeBound x) (twoQ_queryCostLe x)))
    (v := budget ((0 : ℕ) : ℕ∞) ((1 : ℕ) : ℕ∞)) fun _ => ?_).mono ?_)
  · exact (Timed.useBound_step_iff _ _ 0 1).2 ⟨⟨le_rfl, trivial⟩, trivial⟩
  · intro j
    cases j <;> norm_num

/-- A computation node in front: running a costed tree of time `0` and then `twoQ`, at step
cost `4`, has time `0 + 4 + 5` and two queries, by the computation-node clause and the split of
a step-prefixed bound. -/
example (x : ℕ) :
    Timed.StepTimeBound (0, Timed.lift ℕ (CatCrypt.Core.SPTree.Timed.ret x) (fun _ => 4) twoQ) 9 ∧
      QueryCostLe (fun _ => 1)
        (0, Timed.lift ℕ (CatCrypt.Core.SPTree.Timed.ret x) (fun _ => 4) twoQ).2.erase 2 := by
  refine (Timed.useBound_step_iff _ _ 2 9).1 ((Timed.useBound_step_lift _
    (w := budget ((2 : ℕ) : ℕ∞) ((9 : ℕ) : ℕ∞)) fun b => ?_).mono ?_)
  · exact (Timed.useBound_step_iff _ _ 2 9).2 ⟨⟨by omega, (twoQ_timeBound b).mono (by omega)⟩,
      twoQ_queryCostLe b⟩
  · intro j
    cases j <;> simp [CatCrypt.Core.SPTree.Timed.time_ret]

/-- A vector bound with a price: at ten units per query and one per tick, the priced charge of
`twoQ` folds to at most `10 * 2 + 5`. -/
example (x : ℕ) :
    FreeM.wpFold (OpSpec.chargeUnder (fun a => ∑ j, budget 10 1 j * useCharge (fun _ => 1) a j)
      fun _ _ => True) (Timed.toFreeMT (twoQ x)) (fun _ => 0) ≤ 25 := by
  refine (FreeM.wpFold_chargeUnder_price_le _ _ _ (twoQ_useBound x)).trans ?_
  simp
  norm_num

/-- The query bound of an erased program as a charge fold of its free tree. -/
example :
    FreeM.wpFold (OpSpec.charge fun a => ((EPos.cost (fun _ => 1) a : ℕ) : ℕ∞))
      (toFreeM (.query 1 fun o => .query o fun _ => .pure () : OracleProg ℕ ℕ Unit))
      (fun _ => 0) ≤ 2 :=
  (queryCostLe_iff_wpFold_charge _ _ _).1 (by simp [QueryCostLe])

end CatCrypt.Crypto.OracleProg.UseBoundTest

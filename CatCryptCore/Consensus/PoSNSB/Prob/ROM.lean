/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleEval
public import CatCryptCore.Consensus.PoSNSB.Prob.Hash

/-!
# PoS-NSB: oracle adversaries as queriers

An oracle adversary `A : OracleAdv D R α` determines an adaptive querier in the sense of
`CatCryptCore/Consensus/PoSNSB/Prob/Hash.lean`: given the transcript of the previous queries
and their answers, `A.toQuerier d` replays `A` on the answers of the transcript and returns the
next query of `A`, or the default point `d` when `A` asks no further query. The `k`-th query of
`A.toQuerier d` to `f` is the `k`-th query logged by `OracleAdv.evalOn f A`.

## Main definitions

* `OracleAdv.nextQuery d A tr` — the query of `A` after the answers of the transcript `tr`
* `OracleAdv.toQuerier A d` — the querier of `A` with default point `d`

## Main results

* `OracleAdv.transcript_toQuerier` — the first `k` transcript entries are the first `k` logged
  queries with their answers
* `OracleAdv.query_toQuerier` — the `k`-th query of `A.toQuerier d` is the `k`-th logged query
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCrypt.Crypto

namespace OracleAdv

open CatCryptCore.Consensus.PoSNSB

variable {D R α : Type}

/-- The query of `A` after the answers of the transcript `tr`, with `rand` nodes resolved as in
`evalOn`, or `d` when `A` returns before asking it. -/
noncomputable def nextQuery (d : D) : OracleAdv D R α → List (D × R) → D
  | ret _, _ => d
  | rand p k, tr => nextQuery d (k p.support_nonempty.some) tr
  | query x _, [] => x
  | query _ k, (_, r) :: tr => nextQuery d (k r) tr

/-- The querier of `A` with default point `d`: the next query after a transcript. -/
noncomputable def toQuerier (A : OracleAdv D R α) (d : D) : Querier D R := nextQuery d A

/-- After the first `k` logged queries of `evalOn f A` with their answers, the next query is
the `k`-th logged query. -/
theorem nextQuery_take (d : D) (f : D → R) (A : OracleAdv D R α) (k : ℕ)
    (hk : k < (evalOn f A).2.length) :
    nextQuery d A (((evalOn f A).2.take k).map fun x => (x, f x)) = (evalOn f A).2[k] := by
  induction A generalizing k with
  | ret a => simp at hk
  | rand p g ih => exact ih _ k hk
  | query x g ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [evalOn_query, List.length_cons] at hk
      simp only [evalOn_query, List.take_succ_cons, List.map_cons, List.getElem_cons_succ,
        nextQuery]
      exact ih _ k (by omega)

variable [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- The transcript of the first `k` queries of `A.toQuerier d` to `f` is the list of the first
`k` logged queries of `evalOn f A` with their answers. -/
theorem transcript_toQuerier (A : OracleAdv D R α) (d : D) (f : D → R) (k : ℕ)
    (hk : k ≤ (evalOn f A).2.length) :
    transcript (A.toQuerier d) f k = ((evalOn f A).2.take k).map fun x => (x, f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transcript, ih (by omega), List.take_succ_eq_append_getElem (by omega), List.map_append,
      List.map_singleton]
    simp only [toQuerier, nextQuery_take d f A k (by omega)]

/-- The `k`-th query of `A.toQuerier d` to `f` is the `k`-th query logged by `evalOn f A`. -/
theorem query_toQuerier (A : OracleAdv D R α) (d : D) (f : D → R) (k : ℕ)
    (hk : k < (evalOn f A).2.length) :
    CatCryptCore.Consensus.PoSNSB.query (A.toQuerier d) f k = (evalOn f A).2[k] := by
  rw [CatCryptCore.Consensus.PoSNSB.query, transcript_toQuerier A d f k hk.le]
  exact nextQuery_take d f A k hk

end OracleAdv

end CatCrypt.Crypto

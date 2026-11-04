/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SPCompPMF
public import CatCryptCore.Crypto.OracleAdversary

/-!
# Non-adaptive query lists as oracle adversaries

A game family indexed by a list of queries fixed in advance, answered by a stateless oracle
(possibly keyed by a sampled key), and followed by an arbitrary `SPComp` distinguisher, is
an oracle game against a particular `OracleAdv`: the adversary `queryListAdv ds Dist` asks
the queries `ds` in order and outputs a sample of the output bit of `Dist` on the answers.
This turns bounds on adaptive oracle games into bounds on game families of the form
`hon → SPComp leak` used by the concrete UC route (`UCConcrete.GameAdvBoundC`).

## Main definitions

* `answers O ds` — the answers of a stateless oracle to the queries `ds`
* `listAdv ds k`, `queryListAdv ds Dist` — the adversaries asking `ds` in order

## Main results

* `run_listAdv`, `run_queryListAdv_map_fst` — the runs of these adversaries
* `advantageA_liftPMF_answers` — the distinguishing advantage of `Dist` between the keyed
  and the unkeyed answer games (`liftPMF` of the answer distributions) is the advantage of
  `queryListAdv ds Dist` between the corresponding oracle games
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.QueryList

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Query lists -/

variable {D R : Type}

/-- The answers of the stateless oracle `O` to the queries `ds`, asked in order. -/
noncomputable def answers (O : Unit → D → PMF (R × Unit)) : List D → PMF (List R)
  | [] => PMF.pure []
  | d :: ds => (O () d).bind fun x => (answers O ds).map (x.1 :: ·)

/-- The adversary asking the queries `ds` in order and continuing with `k` on the answers. -/
def listAdv {α : Type} : List D → (List R → OracleAdv D R α) → OracleAdv D R α
  | [], k => k []
  | d :: ds, k => .query d fun r => listAdv ds fun rs => k (r :: rs)

theorem run_listAdv {α : Type} (O : Unit → D → PMF (R × Unit)) (ds : List D)
    (k : List R → OracleAdv D R α) :
    OracleAdv.run O (listAdv ds k) () =
      (answers O ds).bind fun rs => OracleAdv.run O (k rs) () := by
  induction ds generalizing k with
  | nil => simp [listAdv, answers]
  | cons d ds ih =>
    simp only [listAdv, OracleAdv.run_query, answers, PMF.bind_bind]
    refine congrArg _ (funext fun x => ?_)
    obtain ⟨r, ⟨⟩⟩ := x
    simp_all [PMF.bind_map, Function.comp_def]

theorem isQueryBound_listAdv {α : Type} (ds : List D) (k : List R → OracleAdv D R α)
    (hk : ∀ rs, (k rs).IsQueryBound 0) : (listAdv ds k).IsQueryBound ds.length := by
  induction ds generalizing k with
  | nil => exact hk []
  | cons d ds ih => exact fun r => ih _ fun rs => hk _

/-- **Adversary** for a query list: ask the queries `ds` in order, then output a sample of
the output bit of `Dist` on the answers. It asks `|ds|` queries. -/
noncomputable def queryListAdv (ds : List D) (Dist : List R → SPComp Bool) :
    OracleAdv D R Bool :=
  listAdv ds fun rs => .rand (outBool Dist rs) .ret

theorem isQueryBound_queryListAdv (ds : List D) (Dist : List R → SPComp Bool) :
    (queryListAdv ds Dist).IsQueryBound ds.length := by
  solve_by_elim [isQueryBound_listAdv, outBool_apply_true, prTrue_liftPMF_bind]

theorem run_queryListAdv_map_fst (O : Unit → D → PMF (R × Unit)) (ds : List D)
    (Dist : List R → SPComp Bool) :
    (OracleAdv.run O (queryListAdv ds Dist) ()).map Prod.fst =
      (answers O ds).bind (outBool Dist) := by
  simp_all [queryListAdv, run_listAdv, PMF.map_bind, PMF.pure_map]

/-- The advantage of `Dist` between the answers of a keyed oracle under a uniform key and
the answers of an unkeyed oracle to the queries `ds` is the advantage of
`queryListAdv ds Dist` between the corresponding oracle games. -/
theorem advantageA_liftPMF_answers {K : Type} [Fintype K] [Nonempty K]
    (O : K → Unit → D → PMF (R × Unit)) (O' : Unit → D → PMF (R × Unit)) (ds : List D)
    (Dist : List R → SPComp Bool) :
    AdvantageA (liftPMF ((PMF.uniformFintype K).bind fun k => answers (O k) ds))
        (liftPMF (answers O' ds)) Dist =
      Advantage
        (liftPMF ((PMF.uniformFintype K).bind fun k =>
          (OracleAdv.run (O k) (queryListAdv ds Dist) ()).map Prod.fst))
        (liftPMF ((OracleAdv.run O' (queryListAdv ds Dist) ()).map Prod.fst)) := by
  unfold AdvantageA Advantage
  simp only [prTrue_liftPMF_bind, prTrue_liftPMF, run_queryListAdv_map_fst,
    PMF.bind_bind]

end CatCrypt.Crypto.Constructions.QueryList

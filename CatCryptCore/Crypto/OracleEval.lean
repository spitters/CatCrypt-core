/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleSimulation

/-!
# Oracle adversaries evaluated against a fixed function

An oracle adversary `A : OracleAdv D R α` evaluated against a function `f : D → R` answers
every query `d` by `f d`. `OracleAdv.evalOn f A` is the output together with the list of the
queried points in the order they are asked; a `rand p` node is resolved at the point
`p.support_nonempty.some` of the support of `p`.

## Main definitions

* `OracleAdv.evalOn f A` — the output and the list of queries of `A` answered by `f`
* `OracleAdv.NoRand A` — no path of `A` contains a `rand` node
* `OracleAdv.logOracle f` — the oracle answering `d` by `f d` and appending `d` to its state

## Main results

* `OracleAdv.run_logOracle_eq_evalOn` — without `rand` nodes, running `A` against
  `logOracle f` is the point mass at the output of `evalOn f A` with its queries appended to
  the log
* `OracleAdv.length_evalOn_le_of_isQueryBound` — a query bound bounds the number of logged
  queries
* `OracleAdv.evalOn_bind`, `OracleAdv.evalOn_mapQuery` — evaluation of a composition and of a
  renamed adversary
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace OracleAdv

variable {D R D₀ α β : Type}

/-- The output of `A` and the list of its queries, in order, when every query `d` is answered
by `f d` and every `rand p` node is resolved at `p.support_nonempty.some`. -/
noncomputable def evalOn (f : D → R) : OracleAdv D R α → α × List D
  | ret a => (a, [])
  | rand p k => evalOn f (k p.support_nonempty.some)
  | query d k => ((evalOn f (k (f d))).1, d :: (evalOn f (k (f d))).2)

@[simp] theorem evalOn_ret (f : D → R) (a : α) : evalOn f (ret a : OracleAdv D R α) = (a, []) :=
  rfl

@[simp] theorem evalOn_rand (f : D → R) {γ : Type} (p : PMF γ) (k : γ → OracleAdv D R α) :
    evalOn f (rand p k) = evalOn f (k p.support_nonempty.some) := rfl

@[simp] theorem evalOn_query (f : D → R) (d : D) (k : R → OracleAdv D R α) :
    evalOn f (query d k) = ((evalOn f (k (f d))).1, d :: (evalOn f (k (f d))).2) := rfl

/-- Evaluating `A.bind g` evaluates `A`, then `g` on its output; the query lists concatenate. -/
theorem evalOn_bind (f : D → R) (A : OracleAdv D R α) (g : α → OracleAdv D R β) :
    evalOn f (A.bind g) =
      ((evalOn f (g (evalOn f A).1)).1, (evalOn f A).2 ++ (evalOn f (g (evalOn f A).1)).2) := by
  induction A with
  | ret a => rfl
  | rand p k ih => exact ih _
  | query d k ih => simp only [bind, evalOn_query, ih, List.cons_append]

/-- Evaluating the renamed adversary `mapQuery c A` against `f` evaluates `A` against `f ∘ c`
and renames the logged queries. -/
theorem evalOn_mapQuery (f : D₀ → R) (c : D → D₀) (A : OracleAdv D R α) :
    evalOn f (mapQuery c A) = ((evalOn (f ∘ c) A).1, (evalOn (f ∘ c) A).2.map c) := by
  induction A with
  | ret a => rfl
  | rand p k ih => exact ih _
  | query d k ih => simp only [mapQuery, evalOn_query, ih, Function.comp_apply, List.map_cons]

/-- A query bound `q` bounds the number of queries logged by `evalOn`. -/
theorem length_evalOn_le_of_isQueryBound (f : D → R) {A : OracleAdv D R α} {q : ℕ}
    (hA : A.IsQueryBound q) : (evalOn f A).2.length ≤ q := by
  induction A generalizing q with
  | ret a => simp
  | rand p k ih => exact ih _ (hA _)
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q => simpa using ih _ (hA (f d))

/-- No path of `A` contains a `rand` node. -/
def NoRand : OracleAdv D R α → Prop
  | ret _ => True
  | rand _ _ => False
  | query _ k => ∀ r, NoRand (k r)

/-- The oracle that answers `d` by `f d` and appends `d` to its state. -/
noncomputable def logOracle (f : D → R) (l : List D) (d : D) : PMF (R × List D) :=
  PMF.pure (f d, l ++ [d])

/-- Without `rand` nodes, running `A` against `logOracle f` from the log `l` returns the
output of `evalOn f A` and appends its queries to `l`, with probability one. -/
theorem run_logOracle_eq_evalOn (f : D → R) {A : OracleAdv D R α} (hA : A.NoRand)
    (l : List D) : run (logOracle f) A l = PMF.pure ((evalOn f A).1, l ++ (evalOn f A).2) := by
  induction A generalizing l with
  | ret a => simp
  | rand p k ih => exact hA.elim
  | query d k ih =>
    rw [run_query, logOracle, PMF.pure_bind, ih _ (hA _)]
    simp

/-- Without `rand` nodes, the output distribution of `A` against `logOracle f` is the point
mass at the output of `evalOn f A`. -/
theorem run_logOracle_map_fst (f : D → R) {A : OracleAdv D R α} (hA : A.NoRand)
    (l : List D) : (run (logOracle f) A l).map Prod.fst = PMF.pure (evalOn f A).1 := by
  rw [run_logOracle_eq_evalOn f hA, PMF.pure_map]

end OracleAdv

end CatCrypt.Crypto

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleSimulation

/-!
# Substitution of programs for the queries of an oracle adversary

`OracleAdv.subst impl A` replaces every query `d` of the adaptive adversary `A` by the
program `impl d`, which may flip coins and ask queries of another oracle. It is the
simulation `OracleAdv.simulate` with the one-point simulator state `Unit`, with the state
dropped from the output.

## Main definitions

* `OracleAdv.subst impl A` — `A` with each query `d` answered by the program `impl d`

## Main results

* `OracleAdv.subst_ret`, `OracleAdv.subst_rand`, `OracleAdv.subst_query` — the equations
  of `subst` on the constructors
* `OracleAdv.run_subst` — running `subst impl A` against `O` is running `A` against the
  oracle that runs `impl d` against `O`
* `OracleAdv.isQueryBound_subst` — `q` queries, each replaced by a program of at most `c`
  queries, give at most `q * c` queries
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace OracleAdv

variable {D R D' R' α : Type}

/-- The adversary `A` with every query `d` replaced by the program `impl d`: the simulation
`simulate` with the one-point simulator state. -/
def subst (impl : D → OracleAdv D' R' R) (A : OracleAdv D R α) : OracleAdv D' R' α :=
  (simulate (fun (_ : Unit) d => (impl d).bind fun r => ret (r, ())) A ()).bind
    fun x => ret x.1

/-- Unfolding lemma of `subst` at `ret`. -/
@[simp] theorem subst_ret (impl : D → OracleAdv D' R' R) (a : α) :
    subst impl (ret a : OracleAdv D R α) = ret a := rfl

/-- Unfolding lemma of `subst` at `rand`. -/
@[simp] theorem subst_rand (impl : D → OracleAdv D' R' R) {β : Type} (p : PMF β)
    (k : β → OracleAdv D R α) :
    subst impl (rand p k) = rand p fun b => subst impl (k b) := rfl

/-- Unfolding lemma of `subst` at `query`: the query is replaced by its program. -/
@[simp] theorem subst_query (impl : D → OracleAdv D' R' R) (d : D) (k : R → OracleAdv D R α) :
    subst impl (query d k) = (impl d).bind fun r => subst impl (k r) := by
  simp only [subst, simulate, bind_assoc, bind_ret]

/-- Running `subst impl A` against `O` is running `A` against the oracle that answers `d`
by running `impl d` against `O`. -/
theorem run_subst {S : Type} (O : S → D' → PMF (R' × S)) (impl : D → OracleAdv D' R' R)
    (A : OracleAdv D R α) (s : S) :
    run O (subst impl A) s = run (fun s d => run O (impl d) s) A s := by
  induction A generalizing s with
  | ret a => simp only [subst_ret, run_ret]
  | rand p k ih => simp only [subst_rand, run_rand, ih]
  | query d k ih => simp only [subst_query, run_bind, run_query, ih]

/-- An adversary with at most `q` queries, each replaced by a program with at most `c`
queries, gives an adversary with at most `q * c` queries. -/
theorem isQueryBound_subst {impl : D → OracleAdv D' R' R} {c : ℕ}
    (himpl : ∀ d, (impl d).IsQueryBound c) {A : OracleAdv D R α} {q : ℕ}
    (hA : A.IsQueryBound q) : (subst impl A).IsQueryBound (q * c) := by
  induction A generalizing q with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q =>
      rw [subst_query, Nat.succ_mul, Nat.add_comm]
      exact isQueryBound_bind (himpl d) fun r => ih r (hA r)

end OracleAdv

end CatCrypt.Crypto

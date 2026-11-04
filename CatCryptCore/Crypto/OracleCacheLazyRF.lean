/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.EagerLazyRF
public import CatCryptCore.Crypto.OracleCache

/-!
# The lazy random function as a cached run

The lazily sampled random function `lazyRF X t` is the caching handler `cacheImpl` run on `X`
from the table `t`, with each inner call replaced by one uniform draw: a recorded point is
answered from the table and a new point is drawn once. The inner calls of the cached run are the
fresh draws of the lazy table, so that their number on a path is at most the number of distinct
points of `X` outside `t`, which is the growth of the table. `isQueryBound_lazyRF` states the
different fact that `lazyRF X t` asks no query of its own oracle, the draws being sampling nodes.

## Main results

* `lazyRF_eq_subst_simulate_cacheImpl` — the factorization of `lazyRF` through `cacheImpl`;
* `isQueryBound_simulate_cacheImpl_lazyRF` — the cached run under `lazyRF` makes at most as many
  inner calls (fresh draws) as `X` has distinct points outside the table.

Search words: lazy sampling, random function, cache, fresh draws, distinct queries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.SIVNonce

open CatCrypt.Crypto CatCrypt.Crypto.OracleAdv

variable {P V D' R' β : Type} [DecidableEq P] [Fintype V] [Nonempty V]

/-- The lazy random function is the cached run of `X` from the table `t` with each inner call
replaced by a uniform draw. -/
theorem lazyRF_eq_subst_simulate_cacheImpl (X : OracleAdv P V β) (t : List (P × V)) :
    (lazyRF X t : OracleAdv D' R' _) =
      subst (fun _ => .rand (PMF.uniformFintype V) .ret) (simulate cacheImpl X t) := by
  induction X generalizing t with
  | ret b => rfl
  | rand p k ih => simp only [lazyRF, simulate, subst_rand, ih]
  | query p k ih =>
    rcases h : List.lookup p t with _ | v
    · simp only [lazyRF, simulate, cacheImpl, h, OracleAdv.bind, subst, ih]
    · simp only [lazyRF, simulate, cacheImpl, h, bind_ret, ih]

/-- The cached run whose inner calls `lazyRF X t` answers by fresh draws makes at most `n` inner
calls when `X` asks at most `n` distinct points outside the table `t` on each path; in
particular at most the query bound of `X`. -/
theorem isQueryBound_simulate_cacheImpl_lazyRF {X : OracleAdv P V β} {t : List (P × V)} {n : ℕ}
    (hX : X.IsDistinctQueryBoundBy (fun _ => 1) (cacheKeys t) n) :
    (lazyRF X t : OracleAdv D' R' _) =
        subst (fun _ => .rand (PMF.uniformFintype V) .ret) (simulate cacheImpl X t) ∧
      (simulate cacheImpl X t).IsQueryBound n :=
  ⟨lazyRF_eq_subst_simulate_cacheImpl X t, isQueryBound_simulate_cacheImpl hX⟩

end CatCrypt.Crypto.Constructions.SIVNonce

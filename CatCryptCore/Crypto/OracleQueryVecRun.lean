/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleQueryVec

/-!
# Runs of an oracle adversary that asks only some queries

If two oracles agree on a set `Q` of queries at every state, and every query of an oracle
adversary lies in `Q` (`MayOnlyCall Q A`), the runs of the adversary under the two oracles are
equal (`OracleAdv.run_eq_of_mayOnlyCall`). The oracle needs no behaviour away from `Q`.

## Main results

* `OracleAdv.run_eq_of_mayOnlyCall` — oracles that agree on the queries of an adversary give the
  same run
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

/-- **Oracles that agree on the queries of an adversary give the same run.** If `O` and `O'`
agree at every state on the queries of `Q`, and `A` asks only queries of `Q`, then the runs of
`A` under `O` and `O'` are equal. -/
theorem run_eq_of_mayOnlyCall {D R α S : Type} (O O' : S → D → PMF (R × S)) {Q : Set D}
    (hO : ∀ s, ∀ d ∈ Q, O s d = O' s d) {A : OracleAdv D R α} (hA : MayOnlyCall Q A) (s : S) :
    run O A s = run O' A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih =>
    simp only [run_rand]
    exact congrArg _ (funext fun b => ih b (hA b) s)
  | query d k ih =>
    obtain ⟨hd, hk⟩ := mayOnlyCall_query_iff.mp hA
    rw [run_query, run_query, hO s d hd]
    exact congrArg _ (funext fun x => ih x.1 (hk x.1) x.2)

end CatCrypt.Crypto.OracleAdv

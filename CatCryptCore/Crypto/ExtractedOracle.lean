/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ExtractedAlgebra
public import CatCryptCore.Crypto.PKE.FOTransformT

/-!
# Extracted hash calls as random-oracle queries

An extracted hash call interpreted by `AlgInterp.oracleHash H` answers the query `g` with
`H g`, the answer of the stateless oracle `keyedRO H`. A security game in the
random-oracle model queries the lazily sampled oracle `roOracle` instead. For a uniform
`H`, a run of an adversary that receives the oracle's answer at one point `s` and then
queries the oracle itself has the same output distribution under the two oracles. A
protocol whose extracted code computes a key `H(s)` therefore matches a game that
obtains the key by a lazy query at `s`.

## Main results

* `roOracle_emptyTable_eq` — the first query of the lazily sampled oracle
* `roOracle_bind_run_eq_eager` — querying the lazy oracle at `s` from the empty table and
  running `A` on the answer is running `A (f s)` against `keyedRO f` for a uniform `f`
* `AlgInterp.keyedRO_eq_oracleHash` — the answer of `keyedRO H` at `g` is the decoded
  output of the extracted hash `oracleHash H` on the encoding of `g`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Extracted

open CatCrypt.Crypto CatCrypt.Crypto.PKE.FOTransformT

section Eager

variable {M R : Type} [Fintype M] [DecidableEq M] [Fintype R] [Nonempty R]

omit [Fintype M] in
/-- The first query of the lazily sampled oracle samples a uniform answer and records it. -/
theorem roOracle_emptyTable_eq (s : M) :
    roOracle (emptyTable : M → Option R) s =
      (PMF.uniformFintype R).map fun y => (y, Function.update emptyTable s (some y)) := rfl

/-- **Lazy query, eager oracle.** Querying the lazily sampled oracle at `s` from the
    empty table and running `A` on the answer against the same oracle has the output
    distribution of running `A (f s)` against `keyedRO f` for a uniform function `f`. -/
theorem roOracle_bind_run_eq_eager {β : Type} (s : M) (A : R → OracleAdv M R β) :
    (roOracle emptyTable s).bind
        (fun kt => (OracleAdv.run roOracle (A kt.1) kt.2).map Prod.fst) =
      (PMF.uniformFintype (M → R)).bind fun f =>
        (OracleAdv.run (keyedRO f) (A (f s)) ()).map Prod.fst := by
  rw [roOracle_emptyTable_eq, PMF.bind_map, ← extDist_empty]
  simp only [Function.comp_def, run_roOracle_map_fst_eq]
  have h := extDist_map_pair (emptyTable : M → Option R) s rfl
  calc _ = ((PMF.uniformFintype R).bind fun r =>
          (extDist (Function.update emptyTable s (some r))).map fun f => (r, f)).bind
            fun p => (OracleAdv.run (keyedRO p.2) (A p.1) ()).map Prod.fst := by
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    _ = _ := by rw [← h, PMF.bind_map]; rfl

end Eager

namespace AlgInterp

variable {G S R K : Type} [One G] (I : AlgInterp G S R K)

/-- The stateless oracle `keyedRO H` answers the query `g` with the decoded output of
    the extracted hash `oracleHash H` on the encoding of `g`. -/
theorem keyedRO_eq_oracleHash [Nonempty K] (H : G → K) (g : G) :
    keyedRO H () g = PMF.pure ((I.val (I.oracleHash H (I.enc (.grp g)))).toK, ()) := by
  simp [keyedRO]

end AlgInterp

end CatCrypt.Crypto.Extracted

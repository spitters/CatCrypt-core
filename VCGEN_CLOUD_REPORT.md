# SPComp `vcgen` examples: cloud run report

Date: 2026-10-14. Branch `work/spcomp-vcgen`, base commit 39b01ec.
New file: `CatCryptCore/Unary/ExpectationVCGenExamples.lean`. No existing theorem or
definition was changed.

## Results

Proof lines count the non-blank, non-comment lines after `:= by`, statement excluded.

| Original theorem | Original proof lines | `_vcgen` proof lines | Instance used |
|---|---|---|---|
| `ExpectedCost.ecost_bind_le` | 21 | 13 | `SPCompU` |
| `ExpectedCost.ecost_bind` | 20 | 15 (+13 from `ecost_bind_le_vcgen`, used for `≤`) | `SPComp` for `≥` |
| `ecost_compileCharged_le_queryCost` | 42 | 66 | `SPCompU` |
| `BadEvent.prTrue_union_bound` | 46 | 29 | `SPCompU` |
| `ForkingLemma.prTrue_double_sample_pure_bool` | 25 | 30 | both |
| `QueryBound.prBad_induction` (loop invariant) | 14 | 47 | `SPCompU` |
| `ExpectedCost.ecost_retryN_le` (loop invariant) | 29 | 30 | `SPCompU` |

One helper was added: `spec_wpE_lower` (1 line). It is the lower-bound triple
`⦃wpE c post⦄ c ⦃post; e⦄` of an arbitrary computation, the counterpart of
`SPCompU.spec_wpE`.

All seven theorems were proved. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for each of them and for `spec_wpE_lower`. The check was run in a scratch
file, which was then deleted. There is no `sorry`.

## Notes per theorem

* `ecost_bind_le_vcgen`: `vcgen [hc]` with `c` abstract (`SPCompU.spec_wpE`). The
  verification condition (VC) is under `wpE c`. It is closed with `simp only` (`wpE_bind`,
  `wpE_pure`, `wpE_add`) and one `wpE_mono` / `wpE_const_le` step.
* `ecost_bind_vcgen`: `le_antisymm` of `ecost_bind_le_vcgen` and a lower-bound triple on
  `SPComp`, using `spec_wpE_lower` for `c`. The VC is closed with `wpE_congr` and
  `wpE_const_of_lossless`. A `CostComp` program needs `Triple (Prog := SPComp (β × ℕ))`,
  because instance search does not unfold `CostComp` to `SPComp`.
* `ecost_compileCharged_le_queryCost_vcgen`: induction on the tree. `vcgen` processes the
  charged operation of each node, with the subtrees abstract. In the `sample` case `vcgen`
  stops under `∑'` (the known limit), so the bound on the uniform average is proved by
  hand (`tsum_fintype`, `Finset.sum_const`, `ENNReal.inv_mul_cancel`). The proof is longer
  than the original: the original reuses `ecost_bind_le_add` and `ecost_lift_le`, while
  this proof states one triple per constructor.
* `prTrue_union_bound_vcgen`: `vcgen` on the `do` block (`SPCompU.spec_monad_bind`), with
  `bad₁` and `bad₂` abstract. The VC uses `wpE_mono`, a case split on `b₁`, and the purity
  of `bad₂` through `prTrue_isPure_eq`. The proof does not use the purity of `bad₁` or the
  two `NoFail` hypotheses. They are kept, as `_hp₁`, `_hnf₁`, `_hnf₂`, so that the
  statement is the original one.
* `prTrue_double_sample_pure_bool_vcgen`: a lower-bound and an upper-bound triple, each
  `vcgen` followed by `simp only [wpEF_bind, wpEF_sample, wpEF_pure]` under `∑'`, both
  reduce to one counting identity `harith`. The equality is `le_antisymm` of the two. Most
  of the length is the counting identity, which also takes up most of the original.
* `prBad_induction_vcgen` (loop invariant): `repeatStep` is structural recursion, not a
  `forIn` loop, so `vcgen` has no loop to attach an invariant to. The induction on `q` is
  outside `vcgen`. Inside it, the invariant is the family of upper-bound triples
  `⦃[bad] + (n·ε + c)⦄ repeatStep step n ⦃[bad] + c⦄`, indexed by `c`. In the step case
  `vcgen [hr, hs]` composes the instance at `ε + c` with the step triple at `c` and leaves
  one arithmetic VC, `(n+1)·ε + c = n·ε + (ε + c)`. The invariant has to be parametric in
  `c`: with `c` fixed at `0`, the post of `repeatStep step n` does not match the
  precondition of `step` syntactically. Observations:
  * `vcgen [ih (ε + c)]` is rejected ("Could not resolve spec theorem"). Spec arguments
    must be names, so the instances are bound with `have` first.
  * After `simp only [repeatStep]` or a `show` with `_` arguments, `vcgen` reports "could
    not determine the program type of the goal". Stating the step goal as a `have` with
    `(α := PUnit)` annotations on `SPCompU.lift` and `SPComp.bind` works.
  The proof is longer than the original because the original reuses
  `prEventComp_bind_step_le`, which contains the per-step bound.
* `ecost_retryN_le_vcgen` (loop invariant): `retryN` is structural recursion, so the
  induction on the retry budget is again outside `vcgen`. Inside the step, `vcgen [hb]`
  with the body abstract leaves the VC under `wpE body`. The post of the body includes the
  cost already accumulated (`p.2 + q.2`), so no body triple with a fixed post matches. The
  per-round hypotheses `ecost body ≤ C` and `failProb body ≤ q` therefore cannot be given
  to `vcgen` as specs. The VC is closed with `wpE_mono`, `wpE_add`, `wpE_const_mul` and
  `geom_sum_succ`, in the same steps as the original.

## Module form

The new file is not a Lean `module`. `CatCryptCore/Unary/ExpectedCost.lean` declares its
definitions in a `public meta section` without `@[expose]`, so a `module` file cannot
unfold `ecost`, `CostComp.bind`, `compileCharged` or `retryN`; `unfold CostComp.bind`
fails with "definition is not exposed". A non-module file that imports the modules sees the
bodies. Changing `ExpectedCost` to expose them would have changed an existing file, which
the task does not allow.

## Build

* `lake build CatCryptCore.Unary.ExpectationVCGenExamples`: succeeded (2711 jobs). The new
  file produces no warnings.
* Environment: `release.lean-lang.org` and the Mathlib cache host
  `lakecache.blob.core.windows.net` were refused by the network policy (HTTP 403 on
  CONNECT), so `elan` could not install the toolchain and `lake exe cache get` downloaded
  nothing. The Lean 4.33.1 toolchain was installed from the GitHub release zip and linked
  with `elan toolchain link`. Mathlib and the project were built from source.
* Time: building `CatCryptCore.Unary.ExpectationVCGen` from source took 40 min (2696 jobs,
  4 cores). The full run, from setup to the report, took about 65 min. A rebuild of the new
  module alone takes about 5 s.

## Second cloud run: loop invariants through `forIn`

A second run of the same scheduled task worked in parallel. It reached the same results for
the five non-loop theorems, and its version was pushed after the first run's commit above, so
the first run's file is kept unchanged. This section adds only what the second run found
about loop invariants. The new module is `CatCryptCore/Unary/ExpectationVCGenLoops.lean`.
It is a Lean `module`, which works with `import all CatCryptCore.Unary.ExpectedCost`; that
import gives access to the bodies of `ecost`, `CostComp.bind` and `retryN`.

`vcgen` can carry a loop invariant for these two theorems once the loop is written as a
`forIn` over `List.range n` in `SPCompU`. The rule `Spec.forIn_list` of `Std.Internal.Do`
then does the induction, and the proof states the invariant with
`vcgen [specs] invariants · inv`. Neither `_forIn_vcgen` proof contains an induction on `n`.
The cost is one equation lemma per loop, relating the `forIn` presentation to the recursive
definition.

| Theorem | Original lines | `_forIn_vcgen` lines | Equation lemmas (lines) |
|---|---|---|---|
| `prBad_induction` | 14 | 29 | `repeatStep_succ_eq_bind` (10), `forIn_eq_repeatStep` (5) |
| `ecost_retryN_le` | 29 | 31 | `retryStep`, `retryStepU` (4 + 4), `forIn_retryStep_eq` (11) |

* `prBad_induction_forIn_vcgen`: the invariant at a cursor with `m` iterations left is
  `[bad h] + m * ε`. `vcgen` leaves three verification conditions. The initial and final
  conditions close by `simp`. The step condition is the per-step estimate: `wpE_add`,
  `wpE_const_le`, and `h_fresh` or the mass bound, depending on whether `bad h` holds.
  `repeatStep` is left-nested (`repeatStep q >>= step`) while `forIn` is right-nested, so the
  equation lemma first moves the last step to the front (`repeatStep_succ_eq_bind`).
* `ecost_retryN_le_forIn_vcgen`: the accumulated cost is part of the result, so the loop
  state is `(result, cost)` and a `some` result returns `.done`. The invariant is
  `acc.2 + C * ∑_{i < m} q^i`. The step condition uses `wpE_add`, `wpE_const_mul`, `hC`, `hq`
  and `geom_sum_succ`. The equation lemma `forIn_retryStep_eq` generalises over the initial
  cost.
* Practical points:
  * `simp` and `rw` lemmas do not fire on terms that mix the `SPComp` and `SPCompU` types;
    for example `List.forIn_cons` does not fire on `forIn (m := SPCompU)` when the body has
    type `SPComp`. The `retryN` equation lemma is therefore proved for
    `forIn (m := SPComp)` and connected to the `SPCompU` loop by `rfl`.
  * Verification conditions written after `invariants · inv` as `·` bullets are parsed as
    more invariant alternatives, so they have to be addressed with `case vcN ... =>`.
  * `vcgen` also fails with "could not determine the program type of the goal" when the
    spec hypotheses are introduced with `have` inside the `by` block of the triple. It works
    when they are introduced one level up.
* Build: `lake build CatCryptCore.Unary.ExpectationVCGenExamples
  CatCryptCore.Unary.ExpectationVCGenLoops` succeeded (2712 jobs), with no warnings from the
  new module. The two modules can be imported together. `#print axioms` gives
  `[propext, Classical.choice, Quot.sound]` for both `_forIn_vcgen` theorems and both
  equation lemmas; the scratch file was deleted. Time: the from-source Mathlib build took
  about 122 minutes in this container; the proofs took about 30 minutes.

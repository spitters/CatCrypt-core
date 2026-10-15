# SPComp `vcgen` conversions, second set: cloud run report

Date: 2026-10-15. Branch `work/vcgen-conversions`, created from `origin/work/spcomp-vcgen`
at commit 561aa69. New file: `CatCryptCore/Unary/ExpectationVCGenExamples2.lean`. No
existing theorem or definition was changed.

## Results

Proof lines count the non-blank, non-comment lines after `:= by` (for
`prTrue_union_bound_list`, the lines of the match arms), statement excluded. Eleven
theorems were converted. All are proved; there is no `sorry`.

| Original theorem (file) | Original lines | `_vcgen` lines | Instance(s) |
|---|---|---|---|
| `ecost_pure` (`Unary/ExpectedCost`) | 3 | 6 | `SPCompU` |
| `ecost_charge` (`Unary/ExpectedCost`) | 2 | 12 | both |
| `ecost_lift_le` (`Unary/ExpectedCost`) | 9 | 12 | `SPCompU` |
| `ecost_lift_of_lossless` (`Unary/ExpectedCost`) | 9 | 13 (+12 from `ecost_lift_le_vcgen`) | `SPComp` for `≥` |
| `ecost_bind_le_add` (`Unary/ExpectedCost`) | 2 (uses `ecost_bind_le`) | 15 | `SPCompU` |
| `prEventComp_pure` (`Unary/QueryBound`) | 3 | 10 | both |
| `prEventComp_loopGame` (`Unary/QueryBound`) | 9 | 30 | both |
| `prTrue_bind_sample_Bool` (`Crypto/Advantage`) | 10 | 20 | both |
| `BadEvent.prTrue_pure_false_eq_zero` (`Crypto/BadEvent`) | 3 | 6 | `SPCompU` |
| `BadEvent.prTrue_union_bound_list` (`Crypto/BadEvent`) | 23 | 42 | `SPCompU` |
| `DetCPA.diff_msg_prTrue` (`Examples/DetCPA`) | 7 | 8 | `SPCompU` |

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all eleven theorems.
The check was run in a scratch file outside the repository, which was then deleted.

## Notes per theorem

* `ecost_pure_vcgen`, `prTrue_pure_false_eq_zero_vcgen`: one upper-bound triple with
  precondition `0`; `vcgen` and `simp` close it, and `0 ≤ x` gives the equality.
* `ecost_charge_vcgen`, `prEventComp_pure_vcgen`: a lower-bound and an upper-bound triple
  for a single `SPComp.pure`. `vcgen` closes the verification conditions (VCs) of
  `prEventComp_pure_vcgen` itself; `ecost_charge_vcgen` needs one `simp` per triple.
* `ecost_lift_le_vcgen`: `vcgen [hc]` with `c` abstract (`SPCompU.spec_wpE`). The VC is
  `wpE c (fun a => wpEF (pure (a, price)) …) ≤ price`; `wpEF_pure` and `wpE_const_le`
  close it.
* `ecost_lift_of_lossless_vcgen`: `le_antisymm` of `ecost_lift_le_vcgen` and a lower-bound
  triple with `spec_wpE_lower c`. The continuation appears in the VC in eta-reduced form
  `fun a => wpEF (pure (a, price)) post ⊥`, on which `simp [wpEF_pure]` does not fire; a
  local equation `hp` between functions is used instead, then `wpE_const_of_lossless`.
* `ecost_bind_le_add_vcgen`: `vcgen` with `c` abstract; the continuation `f p.1` remains
  under `wpE c` in the VC, as in `ecost_bind_le_vcgen`. After `wpE_bind`, `wpE_add` the VC
  is closed by two `wpE_mono` steps with explicit `post'` and the hypotheses. The original
  is two lines because it reuses `ecost_bind_le`.
* `prEventComp_loopGame_vcgen`: two triples for `loopGame step q b₀` with
  `repeatStep step q` abstract (lower: `spec_wpE_lower`, upper: `SPCompU.spec_wpE`). Each VC
  is equality of two `wpE (repeatStep step q)` terms that differ by `wpEF (pure b₀)` in the
  post-expectation. In the lower-bound case `simp` with a functional equation did not
  rewrite under the eta-reduced binder; `congrArg` with `funext` and `rw [wpEF_pure]` works.
  `wpE_congr` with `(wpEF_pure _ _ _ h').symm` reached the heartbeat limit in `isDefEq`.
* `prTrue_bind_sample_Bool_vcgen`: two triples with `A` abstract. `vcgen` stops at the
  average `2⁻¹ * ∑' b : Bool, …` (the known limit under `tsum`); `tsum_bool` evaluates it,
  and `ring` closes each VC. The lower-bound VC also carries the failure term
  `Lean.Order.bot * (A b s) none`, removed with `lean_order_bot_eq_zero`. vcgen does not
  need a spec for `A`: the VC contains `wp (A b)` directly, which `wp_eq_wpEF` /
  `SPCompU.wp_eq` and `wpEF` unfold to `wpE (A b)`.
* `prTrue_union_bound_list_vcgen`: the recursion on the list is that of the original. In
  the step case `vcgen [hb]` decomposes the `do` block of `bad_union` with the head event
  and `bad_union (b' :: bs)` abstract (generalised to `r`). The VC is closed as in
  `BadEvent.prTrue_union_bound_vcgen` of the first set, using the purity of the tail union
  (`bad_union_isPure_noFail`, `prTrue_isPure_eq`) and the recursive bound. The proof does
  not call `prTrue_union_bound` or `prTrue_union_bound_vcgen`; it repeats that argument
  inline, which is most of its length.
* `diff_msg_prTrue_vcgen`: the counterpart of `same_msg_prTrue_vcgen`. One upper-bound
  triple with precondition `0`; after `vcgen`, `cases m <;> simp [SPCompU.wp_eq]` closes the
  VCs.

## Skipped candidates

* `ecost_bind_le`, `ecost_bind`, `ecost_compileCharged_le_queryCost`, `ecost_retryN_le`,
  `prBad_induction`, `prEventComp_bind_step_le`, `prTrue_union_bound`,
  `same_msg_prTrue`: already converted in the first set.
* `ecost_retryN_le_geometric`, `ecost_retryN_le_div`, `ecost_of_spTreeQueryAdm`,
  `prBad_of_bounded_count`, `advantage_le_query_bound*`, `advantage_le_birthday`,
  `uptobad_advantage`, `lazy_eager_upto_bad`: corollaries of other theorems; they do not
  walk a program.
* `erase_*`, `compileCharged_erase`, `spcomp_sample_bind_const`,
  `lazy_sample_fresh_eq_uniform`, `lazy_eager_equiv`: equalities of programs, not of
  expectations; the `WPMonad` instances give no program equalities.
* `prEvent_pure`, `prEvent_bind_eq`, `prEvent_bind_step_eq_tsum`, `SDistr_bind_apply_some`,
  `prTrue_prFalse_*`, `exists_noFail_tsub_le`: statements about `SDistr` values and
  `tsum` manipulation only.
* `pHoare_bounded_call`, `query_bound_seq`: qualitative `pHoare` (support) statements; the
  instances in `ExpectationVCGen` are quantitative.
* `retryN_support_some`: a support statement by induction.
* `UniversalHash.collision_prTrue_eq`, `forge_prTrue_eq`: equalities between the `prTrue`
  of two programs with an abstract adversary `A`. With bound-only triples each side needs a
  lower and an upper triple (four triples), and the VCs are four-term sums over
  `Bool × Bool` under `tsum`; these were not attempted.
* `PRFMAC.prTrue_pure_empty`: the same argument as `prTrue_pure_false_eq_zero_vcgen` and
  `prEventComp_pure_vcgen`; omitted to avoid importing the PRF/MAC modules.

## Assessment

* For every theorem in this set the `vcgen` proof is longer than the original. The
  originals are short because they reuse lemmas that already contain the computation
  (`wpE_pure`, `ecost_bind_le`, `prTrue_bind_sample`, `prTrue_union_bound`). The fixed cost
  of the `vcgen` route is the statement of each triple (3 to 5 lines with `OrderDual`
  coercions), the bridge `triple_iff_le_wpE` / `SPCompU.triple_iff_wpE_le`, and, for an
  equality, a second triple. For one-statement programs (`pure`, `charge`) this fixed cost
  is the whole proof.
* `vcgen` removes the manual unfolding of `bind`, `pure`, `get`, `set` and `sample`: no proof
  in this set uses `SPComp.bind_assoc`, `SPComp.pure_bind` or `SDistr.bind` lemmas, and the
  VCs are stated in terms of `wpE` of the abstract sub-programs. This is the main gain; it
  pays off for programs with several primitive steps (first set:
  `prTrue_union_bound`, `ecost_bind_le`), not for the short programs here.
* `vcgen` does not shorten proofs where the work is in the VC: sums under `tsum`
  (`prTrue_bind_sample_Bool`), the purity argument of the union bound, and lossless or
  constant bounds of `wpE` of an abstract program.
* Practical points found in this set:
  * Continuations of an abstract sub-program appear in the VC in eta-reduced form
    `fun a => wpEF (pure …) post e`; `simp [wpEF_pure]` does not rewrite them. A functional
    equation (`funext (wpEF_pure _ _ _)`) or `congrArg` with `funext` and `rw` works.
  * In a lower-bound triple at `Lean.Order.bot`, the VC contains `Lean.Order.bot * mass`
    terms; `lean_order_bot_eq_zero` removes them.
  * `vcgen` with an abstract continuation `A b` needs no spec for `A`: the VC contains
    `wp (A b)`, which unfolds to `wpE (A b)`.
  * Universe annotations matter for `Unit` programs: a local lemma quantified over `PUnit`
    gets a universe metavariable and does not match; use `Unit`.

## Build

* `lake build CatCryptCore.Unary.ExpectationVCGenExamples2`: succeeded (2712 jobs). The new
  file produces no warnings. A rebuild of the new module alone takes about 4 s.
* The module is a plain (non-`module`) file importing
  `CatCryptCore.Unary.ExpectationVCGenExamples` (for `spec_wpE_lower`), as in the first
  set, because `CatCryptCore.Unary.ExpectedCost` does not expose the bodies of `ecost`,
  `CostComp.bind` and `CostComp.lift`. It is not added to `CatCryptCore.lean`, as for the
  first set.

## Setup and time

* `elan` was installed from GitHub with no default toolchain. Lean 4.33.1 was downloaded
  from the GitHub release zip and linked with `elan toolchain link` as
  `leanprover/lean4:v4.33.1`. `lake exe cache get` failed on every file (HTTP 403 on
  CONNECT to the cache host) and was stopped; Mathlib and the project were built from
  source.
* Building `CatCryptCore.Unary.ExpectationVCGenExamples`, `ExpectationVCGenLoops` and
  `Examples.UniversalHash` from source took about 40 min (2722 jobs, 4 cores).
* Total time from setup to the report: about 50 min (the proofs, about 10 min, were written
  while the build ran and checked after it).

# AUTO_CORPUS_7 report

Branch `work/auto-corpus-7`, created from `origin/work/auto-corpus` at 7cf4a52. Second proof-simplification pass over the 33 files of the task list: whole-proof and closing-step attempts with `catcrypt_auto?` under a temporary dispatcher import, golf, and deprecation replacement. Mathlib was replayed, not rebuilt, in every build.

## Method

- Temporary import: the highest of `AutoDispatchExt`, `AutoDispatch`, `AutoSets`, `AutoBase` whose import closure does not contain the file (computed from the `import` lines). `AutoDispatchExt` imports `XDijkstra.Rel.XCombinedAutomation` and `XDijkstra.XMvcgenReg`, and through them the other files, so no file of the list could take it. `AutoDispatch` was used for 15 files and `AutoBase` for 18 (per file below).
- Eligible theorems: tactic proofs (`:= by`) whose statement mentions `rHoare`, `Advantage`/`AdvantageA` (also as a substring, e.g. `DeepNomAdvantage`), `sdist`, `prTrue`/`prEvent`, `IsPure`/`NoFail`, or `SPComp` together with an equation. Term-mode proofs were not attempted.
- Whole-proof attempts: on a trial copy with the temporary import, each eligible proof was replaced by `catcrypt_auto? [the lemmas and hypotheses cited in the old proof]` (simp/rw/grind lists, `exact`/`apply` heads, `unfold` targets; names bound inside the old proof dropped, unknown identifiers removed on retry). Suggestions and errors were read from the diagnostics of the trial copy (the same server interface that `lean-query.py diag` uses).
- Closing-step attempts, for the theorems not closed whole: the last tactic of each block, each calc step (`by catcrypt_auto?` in place of a term step), each `simp_all`/`simp only` line; one position per theorem per round, with the rest of the proof unchanged. A position counts as closed only if the suggestion appears and no other error occurs in that theorem.
- Freezing: a suggestion was pasted without the temporary import only if it is not longer in lines than the text it replaces and differs from it. Two further rules were applied: a suggestion was not frozen in place of `rfl` (two such freezes from the first commits were reverted in follow-up commits, see Crypto/NomAdvantage and Deep/Eval), and when the unused-simp-argument linter flagged an argument of a frozen suggestion, the linter's own replacement was used. Every frozen text was then elaborated in the file without the import; texts that failed there (unknown tactic `catcrypt_grind`, `sum_atoms_le`, `hop_chain`, `bind_vcgen`, or other errors) were dropped and the old text kept.
- Golf: automatic trial of merging a single-line `rw [..]`/`simp only [..]` followed by a closing `simp`/`simp_all`/`simp only`/`rfl` into one `simp [..]`/`simp_all [..]`, kept only when the theorem shows no error or warning; plus the unused-simp-argument warnings already present in the base (Relational/Rules, Unary/Bridge).
- Deprecations: no deprecation warning occurs in any of the 33 files at the base, so step 3 made no change.
- Builds: each edited module was built with `lake build CatCryptCore.<Module>` after its edit; the number of warnings in the file was compared with the build before the edit (no increase in any file). A final joint build of all 33 modules completed successfully (2729 jobs).

No statement, definition, import, attribute or declaration name was changed; no declaration was added or deleted; no `sorry` and no `native_decide` was introduced; no hypothesis of the form `∀ A, Adv … ≤ ε` was added. CatCryptCore/Consensus/** was not touched.

## Totals

Lines added/deleted over all files: 155/234 (net 79 fewer). Theorems attempted whole: 270; closed with the import: 70; closed whole by a frozen suggestion: 48. Closing steps replaced by frozen suggestions: 80.

## Lines added/deleted (`git diff --numstat origin/work/auto-corpus`)

| File | added | deleted |
|---|---|---|
| CatCryptCore/Core/Code.lean | 7 | 9 |
| CatCryptCore/Crypto/Advantage.lean | 12 | 16 |
| CatCryptCore/Crypto/BadEvent.lean | 8 | 8 |
| CatCryptCore/Crypto/ForkingLemma.lean | 7 | 9 |
| CatCryptCore/Crypto/HybridArgument.lean | 7 | 7 |
| CatCryptCore/Crypto/NomAdvantage.lean | 5 | 11 |
| CatCryptCore/Crypto/NomPkgBridge.lean | 12 | 15 |
| CatCryptCore/Crypto/SDist.lean | 6 | 10 |
| CatCryptCore/Crypto/UCMonad.lean | 1 | 1 |
| CatCryptCore/Crypto/UCMonad/SPCompInstance.lean | 2 | 2 |
| CatCryptCore/Examples/DetCPA.lean | 3 | 10 |
| CatCryptCore/Relational/Approx.lean | 2 | 4 |
| CatCryptCore/Relational/Rules.lean | 23 | 27 |
| CatCryptCore/Relational/SpanLifting.lean | 1 | 2 |
| CatCryptCore/Unary/Bridge.lean | 9 | 19 |
| CatCryptCore/Unary/ExpectationVCGen.lean | 10 | 11 |
| CatCryptCore/Unary/ExpectationWP.lean | 22 | 36 |
| CatCryptCore/Unary/ExpectedCost.lean | 8 | 21 |
| CatCryptCore/Unary/QueryBound.lean | 10 | 16 |

The other 14 files are unchanged (see "Skipped files and files without change").

## Summary per file

| File | eligible | closed whole with the import | closed whole, frozen | closing steps frozen |
|---|---|---|---|---|
| Core/Code.lean | 17 | 4 | 3 | 3 |
| Crypto/Advantage.lean | 13 | 5 | 5 | 7 |
| Crypto/BadEvent.lean | 18 | 3 | 0 | 8 |
| Crypto/ForkingLemma.lean | 9 | 1 | 0 | 1 |
| Crypto/HybridArgument.lean | 8 | 0 | 0 | 7 |
| Crypto/MultiQueryPRF.lean | 0 | 0 | 0 | 0 |
| Crypto/NomAdvantage.lean | 8 | 6 | 5 | 0 |
| Crypto/NomPkgBridge.lean | 16 | 7 | 4 | 8 |
| Crypto/SDist.lean | 18 | 4 | 4 | 2 |
| Crypto/UC.lean | 6 | 1 | 0 | 0 |
| Crypto/UCMonad.lean | 2 | 0 | 0 | 1 |
| Crypto/UCMonad/SPCompInstance.lean | 6 | 1 | 0 | 2 |
| Deep/Eval.lean | 7 | 1 | 0 | 0 |
| Examples/DetCPA.lean | 3 | 3 | 2 | 0 |
| Relational/Approx.lean | 20 | 0 | 0 | 0 |
| Relational/Judgment.lean | 2 | 0 | 0 | 0 |
| Relational/Rules.lean | 48 | 9 | 2 | 18 |
| Relational/SpanLifting.lean | 1 | 0 | 0 | 0 |
| Unary/Bridge.lean | 11 | 3 | 2 | 5 |
| Unary/ExpectationVCGen.lean | 10 | 4 | 4 | 6 |
| Unary/ExpectationWP.lean | 12 | 9 | 9 | 4 |
| Unary/ExpectedCost.lean | 14 | 6 | 6 | 1 |
| Unary/QueryBound.lean | 9 | 3 | 2 | 7 |
| XDijkstra/Rel/XCombinedAutomation.lean | 4 | 0 | 0 | 0 |
| XDijkstra/Rel/XHybridExample.lean | 0 | 0 | 0 | 0 |
| XDijkstra/Rel/XRelMvcgenControl.lean | 2 | 0 | 0 | 0 |
| XDijkstra/Rel/XRelMvcgen.lean | 1 | 0 | 0 | 0 |
| XDijkstra/Rel/XRelSpecMonad.lean | 0 | 0 | 0 | 0 |
| XDijkstra/Rel/XSDistrSoundness.lean | 2 | 0 | 0 | 0 |
| XDijkstra/XAdvantageHybrid.lean | 3 | 0 | 0 | 0 |
| XDijkstra/XMvcgenControl.lean | 0 | 0 | 0 | 0 |
| XDijkstra/XMvcgen.lean | 0 | 0 | 0 | 0 |
| XDijkstra/XMvcgenReg.lean | 0 | 0 | 0 | 0 |

## Files of the vacuity-sweep findings

Of the files named in the vacuity sweep, only `CatCryptCore/Crypto/BadEvent.lean` is in this task list. It received proof-only edits (8 closing steps, see its section); its statements are unchanged. No file under Crypto/UCAdmClass*, Examples/Cryptobox/**, Crypto/KeyAgreement/Curve25519.lean or Crypto/KeyAgreement/MontgomeryXOnly.lean was edited.

## Skipped files and files without change

- Crypto/MultiQueryPRF.lean: its four theorems have term-mode proofs; no eligible tactic proof, nothing attempted.
- XDijkstra/Rel/XHybridExample.lean, XDijkstra/Rel/XRelSpecMonad.lean, XDijkstra/XMvcgenControl.lean, XDijkstra/XMvcgen.lean, XDijkstra/XMvcgenReg.lean: no theorem statement matches the eligibility criteria (their statements are about the XDijkstra specification monads, `wp`/`XRel` judgments and registration examples).
- XDijkstra/Rel/XCombinedAutomation.lean, XDijkstra/Rel/XRelMvcgenControl.lean, XDijkstra/Rel/XRelMvcgen.lean, XDijkstra/Rel/XSDistrSoundness.lean, XDijkstra/XAdvantageHybrid.lean, Relational/Judgment.lean: attempted, no suggestion closed a theorem or a closing step, no golf candidate kept.
- Crypto/UC.lean: one theorem closed with the import; its suggestion was not frozen (see its section); no other change.
- Deep/Eval.lean: the only frozen suggestion replaced `rfl` and was reverted; the file is unchanged against the base.

## Items for the interface queue

1. At the `AutoBase` level (18 files of this list) the shapes "SPComp equality", "relational rHoare judgment" and "distance inequality" have no arm besides `exact %TERM` and the premise stage `solve_by_elim`. Of the whole-proof failures, 49 have shape "SPComp equality", 34 "relational rHoare judgment", 22 "distance inequality" and 67 "other"; of the closing-step failures, 27 "SPComp equality", 51 "distance inequality", 6 "relational rHoare judgment" and 107 "other". A Lean-only `simp_all`/`grind` arm for "SPComp equality" and "distance inequality" in `AutoBase` (as for "other") would make these attempts informative below `AutoSets`.
2. Suggestions that closed with the `AutoDispatch` import but could not be frozen because they need a dispatcher module: 11 positions in Crypto/BadEvent.lean and Crypto/HybridArgument.lean (`catcrypt_grind` 8, `hop_chain` 1, `sum_atoms_le` 1, `bind_vcgen` 1). These would become usable if those modules imported `AutoSets`/`AutoArms`, which the task does not permit.
3. The premise stage frequently suggests `solve_by_elim [p₁, …, pₙ]` with a long list of file premises (e.g. Core/Code `foldM_singleton`, Crypto/NomAdvantage `runPkg_link` at 182). These were longer than the replaced text or replaced `rfl`. A suggestion trimmed to the premises actually used would be shorter.
4. Unused-variable warnings on statement binders that cannot be removed without a statement change: Unary/Bridge.lean (`hph` at 94 and 104, `hcombine` at 96), Crypto/NomAdvantage.lean (`op'` at 165), Deep/Eval.lean (`op`, 9 positions). Crypto/UC.lean has a universe-level warning on the definition `UCSpec` (line 69).
5. Eligibility by statement text misses the XDijkstra files almost entirely; if they are to be covered by later passes, their judgment forms (`XRel…`, `wp`) would need dispatcher shapes.

## Per-file results

Line numbers refer to the file at the base commit. Failures list the goal shape named by the first line of the `catcrypt_auto?` error ("other" is the dispatcher's catch-all shape). "Suggestion leaves later errors" means `catcrypt_auto?` closed the goal at a position that is not the last step of its branch, so the following tactics failed.

### Core/Code.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 7/9.
- Whole-proof attempts: 17 theorems; closed with the import: 4.
- Theorems closed whole by a frozen suggestion (3):
  - `pure_bind'` (line 109): `simp_all [SDistr.pure_bind, SPComp.bind, pure]`
  - `bind_pure'` (line 115): `simp_all [SPComp.bind, pure, Prod.mk.eta, SDistr.bind_pure]`
  - `sample_bind_pure` (line 130): `simp_all [SPComp.bind, sample, pure, SDistr.bind_assoc, SDistr.pure_bind]`
- Closed with the import, not frozen: `foldM_singleton` (`solve_by_elim [foldM_nil, foldM_cons, isPure_bind_comm_left, isPure_bi`; longer than the old proof).
- Closing steps replaced (3):
  - 149 (`sample_prod_eq`): `simp only [SDistr.bind_assoc, SDistr.pure_bind, this.symm]` → `simp_all [SDistr.bind_assoc, SDistr.pure_bind]`
  - 163 (`bind_pure`): `exact bind_pure' c h` → `simp_all [bind_pure']`
  - 169 (`pure_bind`): `exact pure_bind' a f h` → `simp_all [pure_bind']`
- Step suggestions not frozen: 275 `simp_all [SDistr.pure_bind]` (without the import: rejected in the joint check).
- Golf (1): 273–274 `simp only [bind, hdc h, SDistr.bind_assoc] / simp_all [SDistr.pure_bind]` → `simp_all [bind, hdc h, SDistr.bind_assoc, SDistr.pure_bind]`.
- Failures of `catcrypt_auto?`:
  - `fail_bind` (whole, line 78): SPComp equality
  - `sample_prod_eq` (whole, line 140): SPComp equality
  - `bind_assoc` (whole, line 155): SPComp equality
  - `bind_pure` (whole, line 161): SPComp equality
  - `pure_bind` (whole, line 167): SPComp equality
  - `map_comp` (whole, line 197): SPComp equality
  - `sample_bind_pure_equiv` (whole, line 212): SPComp equality
  - `sample_bind_equiv` (whole, line 228): SPComp equality
  - `bind_sample_bijection` (whole, line 241): SPComp equality
  - `bind_isPure` (whole, line 269): IsPure/NoFail side condition
  - `isPure_bind_comm` (whole, line 285): SPComp equality
  - `isPure_bind_comm_left` (whole, line 302): SPComp equality
  - `foldM_append` (whole, line 339): SPComp equality
  - 146 (`sample_prod_eq`, `simp only [sample, SPComp.bind, SPComp.p`): other
  - 199 (`map_comp`, `simp only [SPComp.map, bind_assoc, pure_`): SPComp equality
  - 217 (`sample_bind_pure_equiv`, `simp only [bind_def, sample, pure, SDist`): other
  - 222 (`sample_bind_pure_equiv`, `rw [← SDistr.bind_assoc, SDistr.uniform_`): other
  - 233 (`sample_bind_equiv`, `simp only [bind_def, sample, SDistr.bind`): other
  - 234 (`sample_bind_equiv`, `exact SDistr.uniform_bind_equiv_comp e (`): other
  - 245 (`bind_sample_bijection`, `simp [sample_bind_equiv]`): SPComp equality
  - 274 (`bind_isPure`, `simp only [bind, hdc h, SDistr.bind_asso`): suggestion leaves later errors in the proof (1)
  - 293 (`isPure_bind_comm`, `simp only [bind, hd₁ h, hd₂ h, SDistr.bi`): other
  - 294 (`isPure_bind_comm`, `exact SDistr.bind_comm d₁ d₂ (fun a b =>`): other
  - 308 (`isPure_bind_comm_left`, `simp only [bind, hd₁, SDistr.bind_assoc,`): other
  - 309 (`isPure_bind_comm_left`, `exact SDistr.bind_comm d₁ (c₂ h) (fun a `): other
  - 344 (`foldM_append`, `simp only [List.cons_append, foldM_cons]`): SPComp equality
  - 346 (`foldM_append`, `simp_all [SPComp.bind_assoc]`): SPComp equality
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 148, 220.

### Crypto/Advantage.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 12/16.
- Whole-proof attempts: 13 theorems; closed with the import: 5.
- Theorems closed whole by a frozen suggestion (5):
  - `advantage_triangle` (line 83): `grind [Advantage, abs_diff_triangle]`
  - `Advantage_sym` (line 180): `simp_all [Advantage, max_comm]`
  - `Advantage_self` (line 184): `simp_all [Advantage, tsub_self, max_self]`
  - `sample_bind_eq` (line 192): `simp_all [SPComp.bind_def, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]`
  - `sample_bind_eq_general` (line 252): `simp_all [SPComp.bind_def, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]`
- Closing steps replaced (7):
  - 113 (`advantage_zero_of_rHoare`): `simp only [SPComp.bind_def, h_distr_eq]` → `simp_all [SPComp.bind_def]`
  - 116 (`advantage_zero_of_rHoare`): `simp only [prTrue, h_bound_eq]` → `simp_all [prTrue]`
  - 120 (`advantage_zero_of_rHoare`): `simp only [tsub_self, max_self]` → `simp_all [tsub_self, max_self]`
  - 169 (`advantage_zero_of_inv`): `exact hA_respects p₂.1 p₁.2 p₂.2 hI_h` → `grind`
  - 174 (`advantage_zero_of_inv`): `simp only [max_self]` → `simp_all [max_self]`
  - 218 (`prTrue_bind_sample_Bool`): `simp [add_comm]` → `simp_all [add_comm]`
  - 267 (`prTrue_bind_sample`): `simp only [SDistr.uniform_apply_none, SDistr.uniform_apply_some, SDistr.fail_apply_some, E` → `simp_all [SDistr.uniform_apply_none, SDistr.uniform_apply_some]`
- Golf (1): 264–265 `rw [tsum_fintype, Fintype.sum_option] / simp_all [SDistr.uniform_apply_none, SDi` → `simp_all [tsum_fintype, Fintype.sum_option, SDistr.uniform_apply_none, SDistr.un`.
- Failures of `catcrypt_auto?`:
  - `advantage_zero_of_rHoare` (whole, line 98): other
  - `advantage_zero_of_inv` (whole, line 138): other
  - `prTrue_le_one` (whole, line 197): distance inequality
  - `prTrue_bind_sample_Bool` (whole, line 207): other
  - `advantage_sample_vs_pure_false` (whole, line 221): other
  - `prTrue_bind_sample` (whole, line 257): other
  - `advantageA_sample_bind` (whole, line 299): other
  - `advantageA_isPure_bind` (whole, line 332): other
  - 118 (`advantage_zero_of_rHoare`, `simp only [AdvantageA, Advantage, h_pr_e`): suggestion leaves later errors in the proof (1)
  - 166 (`advantage_zero_of_inv`, `simp only`): other
  - 170 (`advantage_zero_of_inv`, `simp [hAeq, liftR_refl]`): other
  - 172 (`advantage_zero_of_inv`, `simp only [SPComp.bind, heq_distrs, tsub`): suggestion leaves later errors in the proof (1)
  - 211 (`prTrue_bind_sample_Bool`, `simp only [sample_bind_eq]`): other
  - 212 (`prTrue_bind_sample_Bool`, `simp only [SDistr.bind, PMF.bind_apply]`): other
  - 216 (`prTrue_bind_sample_Bool`, `simp only [SDistr.uniform_apply_none, SD`): suggestion leaves later errors in the proof (1)
  - 230 (`advantage_sample_vs_pure_false`, `apply max_le`): distance inequality
  - 233 (`advantage_sample_vs_pure_false`, `gcongr`): distance inequality
  - 238 (`advantage_sample_vs_pure_false`, `rw [← add_mul, ENNReal.inv_two_add_inv_t`): other
  - 241 (`advantage_sample_vs_pure_false`, `gcongr`): distance inequality
  - 262 (`prTrue_bind_sample`, `simp only [sample_bind_eq_general]`): other
  - 263 (`prTrue_bind_sample`, `simp only [SDistr.bind, PMF.bind_apply]`): other
  - 303 (`advantageA_sample_bind`, `simp only [AdvantageA, Advantage, SPComp`): other
  - 311 (`advantageA_sample_bind`, `exact le_of_le_of_eq (tsub_le_iff_right.`): distance inequality
  - 317 (`advantageA_sample_bind`, `exact le_of_le_of_eq (tsub_le_iff_right.`): distance inequality
  - 318 (`advantageA_sample_bind`, `apply max_le`): distance inequality
  - 319 (`advantageA_sample_bind`, `exact tsub_le_iff_right.mpr (by rw [add_`): distance inequality
  - 320 (`advantageA_sample_bind`, `exact tsub_le_iff_right.mpr (by rw [add_`): distance inequality
  - 338 (`advantageA_isPure_bind`, `simp only [AdvantageA, SPComp.bind_assoc`): other
  - 349 (`advantageA_isPure_bind`, `exact le_of_le_of_eq (tsub_le_iff_right.`): distance inequality
  - 355 (`advantageA_isPure_bind`, `exact le_of_le_of_eq (tsub_le_iff_right.`): distance inequality
  - 366 (`advantageA_isPure_bind`, `simp only [prTrue]`): other
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 200, 203, 204, 235, 242, 359, 360.

### Crypto/BadEvent.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 8/8.
- Whole-proof attempts: 18 theorems; closed with the import: 3.
- Theorems closed whole by a frozen suggestion: none.
- Closed with the import, not frozen: `prTrue_pure_false_eq_zero` (`simp_all [SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injE`; without the import: This simp argument is unused:); `spcomp_sample_prod` (`catcrypt_grind`; without the import: unknown tactic); `lazy_sample_fresh_eq_uniform` (`(simp only [CatCrypt.Core.SPComp.monad_bind_eq]; bind_vcgen)`; without the import: unknown tactic).
- Closing steps replaced (8):
  - 133 (`prTrue_prFalse_none_sum`): `simp [ENNReal.tsum_prod']` → `simp_all [ENNReal.tsum_prod']`
  - 140 (`prTrue_prFalse_eq_one_of_noFail`): `exact h` → `simp_all`
  - 150 (`prFalse_eq_one_sub_prTrue`): `exact (ENNReal.add_sub_cancel_left h_ne_top).symm` → `grind [ENNReal.add_sub_cancel_left]`
  - 196 (`advantage_upto_bad`): `prTrue bad Heap.empty := by ring` → `prTrue bad Heap.empty := by grind`
  - 197 (`advantage_upto_bad`): `_ = 1 + prTrue bad Heap.empty := by rw [tsub_add_cancel_of_le h_p1]` → `_ = 1 + prTrue bad Heap.empty := by simp_all [tsub_add_cancel_of_le h_p1]`
  - 464 (`prTrue_union_bound`): `· simp [SDistr.pure_apply_some]` → `· simp_all [SDistr.pure_apply_some]`
  - 476 (`prTrue_union_bound`): `exact htotal` → `simp_all`
  - 597 (`advantage_hybrid_upto_bad`): `_ = n * ε := by simp [Finset.sum_const, Finset.card_range]` → `_ = n * ε := by simp_all [Finset.sum_const, Finset.card_range]`
- Step suggestions not frozen: 333 `sum_atoms_le` (without the import: unknown tactic); 455 `catcrypt_grind` (without the import: unknown tactic); 976 `catcrypt_grind [sample_fin_ofFn_eq_sequential]` (without the import: unknown tactic); 194 `(gcongr <;> catcrypt_grind)` (without the import: unknown tactic).
- Failures of `catcrypt_auto?`:
  - `prTrue_prFalse_none_sum` (whole, line 124): other
  - `prTrue_prFalse_eq_one_of_noFail` (whole, line 135): other
  - `prFalse_eq_one_sub_prTrue` (whole, line 143): other
  - `advantage_upto_bad_A` (whole, line 230): other
  - `uptobadA_advantage` (whole, line 287): other
  - `exists_noFail_tsub_le` (whole, line 307): other
  - `prTrue_union_bound` (whole, line 431): distance inequality
  - `prTrue_union_bound_list` (whole, line 544): distance inequality
  - `advantage_hybrid_upto_bad` (whole, line 586): distance inequality
  - `MultiQueryGame.single_to_multi_bound` (whole, line 720): distance inequality
  - `spcomp_sample_bind_const` (whole, line 819): SPComp equality
  - `spcomp_sample_bind_equiv_comp` (whole, line 866): SPComp equality
  - `eager_process_eq_sequential` (whole, line 961): SPComp equality
  - `advantage_upto_bad` (whole, line 160): distance inequality
  - `advantageA_le_of_noFail_distinguishers` (whole, line 374): distance inequality
  - 329 (`exists_noFail_tsub_le`, `simp [A, hle, SPComp.pure, SDistr.pure, `): other
  - 335 (`exists_noFail_tsub_le`, `simp only [v, e, hA]`): distance inequality
  - 337 (`exists_noFail_tsub_le`, `simp only [hle, if_true, mul_one]`): distance inequality
  - 463 (`prTrue_union_bound`, `rw [tsum_eq_single Heap.empty]`): suggestion leaves later errors in the proof (1)
  - 466 (`prTrue_union_bound`, `simp only [SDistr.pure_apply_some, Prod.`): suggestion leaves later errors in the proof (1)
  - 736 (`MultiQueryGame.single_to_multi_bound`, `|>.trans (by simp [Finset.sum_const, Fin`): no message
  - 822 (`spcomp_sample_bind_const`, `simp`): SPComp equality
  - 874 (`spcomp_sample_bind_equiv_comp`, `simp only [SDistr.pure_bind]`): other
  - 875 (`spcomp_sample_bind_equiv_comp`, `exact SDistr.uniform_bind_equiv_comp σ (`): other
  - 969 (`eager_process_eq_sequential`, `simp only [Equiv.symm_apply_apply] at h_`): SPComp equality
  - 973 (`eager_process_eq_sequential`, `simp only [qsBij_symm_map qs hnodup]`): SPComp equality
  - 975 (`eager_process_eq_sequential`, `simp_all`): SPComp equality
  - 169 (`advantage_upto_bad`, `exact ENNReal.tsum_le_tsum (fun h' => h.`): monotonicity inequality
  - 175 (`advantage_upto_bad`, `exact ENNReal.tsum_le_tsum (fun h' => h.`): monotonicity inequality
  - 203 (`advantage_upto_bad`, `rw [tsub_add_cancel_of_le h_p0]; ring`): other
  - 379 (`advantageA_le_of_noFail_distinguishers`, `simp only [AdvantageA, Advantage]`): distance inequality
  - 380 (`advantageA_le_of_noFail_distinguishers`, `apply max_le`): distance inequality
  - 382 (`advantageA_le_of_noFail_distinguishers`, `exact hle.trans ((le_max_left _ _).trans`): distance inequality
  - 384 (`advantageA_le_of_noFail_distinguishers`, `exact hle.trans ((le_max_right _ _).tran`): distance inequality
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 148, 242, 294, 314, 323, 440, 572, 591, 594, 596, 968.

### Crypto/ForkingLemma.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 7/9.
- Whole-proof attempts: 9 theorems; closed with the import: 1.
- Theorems closed whole by a frozen suggestion: none.
- Closed with the import, not frozen: `double_sample_sdisrt` (`simp_all [SPComp.bind_def, SPComp.sample, SPComp.pure, SDistr.bind_ass`; longer than the old proof).
- Closing steps replaced (1):
  - 381 (`prTrue_double_sample_pure_bool`): `simp only [Finset.card_filter, Finset.sum_product]` → `grind [Finset.card_filter, Finset.sum_product]`
- Step suggestions not frozen: 202 `simp_all [tsum_ite_eq]` (without the import: rejected in the joint check); 204 `simp_all [false_and, tsum_zero]` (without the import: rejected in the joint check); 234 `simp_all` (without the import: rejected in the joint check); 244 `simp_all [decide_eq_true hQ, decide_eq_true (h hQ)]` (without the import: This simp argument is unused:); 245 `simp_all` (without the import: rejected in the joint check); 282 `grind` (without the import: rejected in the joint check).
- Failures of `catcrypt_auto?`:
  - `prTrue_bind_eq_weighted` (whole, line 181): other
  - `prTrue_pure_bool` (whole, line 195): other
  - `prTrue_sample_pure_bool` (whole, line 207): other
  - `prTrue_pure_decide_mono` (whole, line 239): distance inequality
  - `prTrue_bind_mono` (whole, line 249): distance inequality
  - `prTrue_bind_mono_const` (whole, line 262): distance inequality
  - `prTrue_sample_bind_ge` (whole, line 286): distance inequality
  - `prTrue_double_sample_pure_bool` (whole, line 338): other
  - 187 (`prTrue_bind_eq_weighted`, `simp only [PMF.bind_apply]`): other
  - 198 (`prTrue_pure_bool`, `simp only [SDistr.pure, PMF.pure_apply, `): other
  - 201 (`prTrue_pure_bool`, `simp only [true_and, ite_true]`): suggestion leaves later errors in the proof (1)
  - 215 (`prTrue_sample_pure_bool`, `simp only [SDistr.bind, PMF.bind_apply]`): other
  - 220 (`prTrue_sample_pure_bool`, `simp only [SDistr.uniform_apply_none, ze`): other
  - 222 (`prTrue_sample_pure_bool`, `simp only [SDistr.uniform_apply_some, SD`): other
  - 281 (`prTrue_bind_mono_const`, `ENNReal.tsum_le_tsum fun p => mul_le_mul`): distance inequality
  - 283 (`prTrue_bind_mono_const`, `ENNReal.tsum_mul_left`): other
  - 302 (`prTrue_sample_bind_ge`, `simp [SDistr.uniform_apply_some, SDistr.`): other
  - 350 (`prTrue_double_sample_pure_bool`, `simp only [SDistr.bind, PMF.bind_apply]`): other
  - 353 (`prTrue_double_sample_pure_bool`, `simp only [SDistr.uniform_apply_none, ze`): other
  - 356 (`prTrue_double_sample_pure_bool`, `simp only [PMF.bind_apply]`): other
  - 358 (`prTrue_double_sample_pure_bool`, `simp only [SDistr.uniform_apply_none, ze`): other
  - 359 (`prTrue_double_sample_pure_bool`, `simp only [SDistr.uniform_apply_some, SD`): other
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 192, 258, 278.

### Crypto/HybridArgument.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 7/7.
- Whole-proof attempts: 8 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced (7):
  - 80 (`advantage_hybrid_dep`): `simp [Finset.range_zero, Finset.sum_empty]` → `bound`
  - 90 (`advantage_hybrid_dep`): `rw [Finset.sum_range_succ]` → `simp_all [Finset.sum_range_succ]`
  - 105 (`advantage_hybrid_dep_bool`): `rw [Finset.sum_range_succ]` → `simp_all [Finset.sum_range_succ]`
  - 118 (`advantage_hybrid_uniform`): `advantage_hybrid_dep G A n` → `by solve_by_elim [advantage_hybrid_dep, advantage_hybrid_dep_bool]`
  - 124 (`advantage_hybrid_uniform`): `simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]` → `simp_all [Finset.sum_const, Finset.card_range, nsmul_eq_mul]`
  - 167 (`advantage_hybrid_dep_bound`): `advantage_hybrid_dep G A n` → `by solve_by_elim [advantage_hybrid_dep, advantage_hybrid_dep_bool, advantage_hybrid_zero]`
  - 238 (`advantage_hybrid_nested_eq`): `_ = m * q * ε := by ring` → `_ = m * q * ε := by grind`
- Step suggestions not frozen: 98 `catcrypt_grind [Finset.range_zero, Finset.sum_empty, Advanta` (without the import: unknown tactic); 101 `catcrypt_grind` (without the import: unknown tactic); 122 `catcrypt_grind` (without the import: unknown tactic); 171 `catcrypt_grind` (without the import: unknown tactic); 86 `hop_chain` (without the import: unknown tactic).
- Failures of `catcrypt_auto?`:
  - `advantage_hybrid_dep_bool` (whole, line 93): distance inequality
  - `advantage_hybrid_uniform` (whole, line 112): distance inequality
  - `advantage_hybrid_zero` (whole, line 131): other
  - `advantage_hybrid_bound` (whole, line 147): distance inequality
  - `advantage_hybrid_dep_bound` (whole, line 158): distance inequality
  - `advantage_hybrid_factored` (whole, line 180): distance inequality
  - `advantage_hybrid_nested_eq` (whole, line 232): distance inequality
  - `advantage_hybrid_dep` (whole, line 74): distance inequality
  - 137 (`advantage_hybrid_zero`, `simp only [mul_zero] at hle`): suggestion leaves later errors in the proof (1)
  - 138 (`advantage_hybrid_zero`, `exact le_antisymm hle (zero_le)`): other
  - 154 (`advantage_hybrid_bound`, `exact advantage_hybrid_uniform G A n ε h`): distance inequality
  - 187 (`advantage_hybrid_factored`, `exact advantage_hybrid_uniform G_base (f`): distance inequality
  - 237 (`advantage_hybrid_nested_eq`, `advantage_hybrid_nested G A m q ε hstep`): distance inequality

### Crypto/MultiQueryPRF.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 0 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:

### Crypto/NomAdvantage.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 5/11.
- Whole-proof attempts: 8 theorems; closed with the import: 6.
- Theorems closed whole by a frozen suggestion (5):
  - `DeepNomAdvantage_triangle` (line 93): `simp_all [DeepNomAdvantage, advantage_triangle]`
  - `DeepNomAdvantage_self` (line 99): `simp_all [DeepNomAdvantage, Advantage_self]`
  - `DeepNomAdvantage_comm` (line 105): `simp_all [DeepNomAdvantage, Advantage, max_comm]`
  - `DeepNomAdvantage_congr` (line 135): `simp_all`
  - `DeepNomAdvantage_link` (line 328): `simp_all [DeepNomAdvantage, CatCrypt.Deep.NomPackage.link, runPkg_link_assoc]`
- Closed with the import, not frozen: `DeepNomAdvantage_runPkg_eq` (`simp_all [DeepNomAdvantage, h₀, h₁]`; without the import: This simp argument is unused:).
- Closing steps replaced: none. (182, `runPkg_link`: the suggestion `solve_by_elim [DeepNomAdvantage_congr, …]` for `rfl` was frozen by the first commit and reverted in a follow-up commit, since it replaces `rfl`.)
- Step suggestions not frozen: 601 `solve_by_elim [runPkg_interchange, runPkg_interchange_right,` (without the import: rejected in the joint check); 604 `solve_by_elim [runPkg_interchange, runPkg_interchange_right,` (without the import: rejected in the joint check).
- Failures of `catcrypt_auto?`:
  - `runPkg_link` (whole, line 163): SPComp equality
  - `DeepNomAdvantage_par` (whole, line 564): other
  - 180 (`runPkg_link`, `exact CatCrypt.Deep.eval_substOracle _ _`): SPComp equality
  - 597 (`DeepNomAdvantage_par`, `simp only [DeepNomAdvantage, CatCrypt.De`): other
  - 598 (`DeepNomAdvantage_par`, `congr 1`): other

### Crypto/NomPkgBridge.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 12/15.
- Whole-proof attempts: 16 theorems; closed with the import: 7.
- Theorems closed whole by a frozen suggestion (4):
  - `isPure_bind_eq` (line 94): `simp_all [SPComp.bind, hc h₀, SDistr.bind_assoc, SDistr.pure_bind]`
  - `bind_heapReset` (line 386): `simp_all [SPComp.bind, heapReset, SDistr.pure_bind]`
  - `prTrue_bind_heapReset` (line 391): `simp_all [bind_heapReset, prTrue]`
  - `wrapMainNomPkg_impl_code` (line 443): `simp_all [wrapMainNomPkg]`
- Closed with the import, not frozen: `isPure_bind_some_ne` (`simp_all [hc, SDistr.bind, PMF.bind_apply, SDistr.fail_apply_some, SDi`; without the import: This simp argument is unused:); `prTrue_isPure_eq` (`simp_all [hc, SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add, `; without the import: This simp argument is unused:); `runPkg_wrapMain_eq` (`simp_all [runPkg_link, wrapMainNomPkg, h_main, dite_true, CatCrypt.Dee`; without the import: This simp argument is unused:).
- Closing steps replaced (8):
  - 72 (`SPComp.bind_noFail`): `ring` → `simp_all`
  - 84 (`SPComp.sample_noFail`): `rw [SDistr.pure_apply_none, mul_zero]` → `simp_all [SDistr.pure_apply_none, mul_zero]`
  - 108 (`isPure_noFail_d_none`): `exact h` → `simp_all`
  - 261 (`prTrue_isPure_noFail_bind`): `rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, add_comm]` → `simp_all [ENNReal.tsum_add, ENNReal.tsum_mul_left, add_comm]`
  - 287 (`absDiff_bind_le_advantage`): `· exact prTrue_isPure_eq hd₁ Heap.empty` → `· grind [prTrue_isPure_eq]`
  - 288 (`absDiff_bind_le_advantage`): `· exact prTrue_isPure_eq hd₂ Heap.empty` → `· grind [prTrue_isPure_eq]`
  - 504 (`nomPkg_absorb`): `simp only [CatCrypt.Deep.DeepPackage.link]; exact h_main` → `simp_all [CatCrypt.Deep.DeepPackage.link]`
  - 506 (`nomPkg_absorb`): `simp only [CatCrypt.Deep.DeepPackage.link]; exact h_main` → `simp_all [CatCrypt.Deep.DeepPackage.link]`
- Golf (1): 71–72 `rw [hf a h'] / simp_all` → `simp_all [hf a h']`.
- Failures of `catcrypt_auto?`:
  - `SPComp.pure_noFail` (whole, line 48): IsPure/NoFail side condition
  - `SPComp.bind_noFail` (whole, line 57): IsPure/NoFail side condition
  - `SPComp.sample_noFail` (whole, line 76): IsPure/NoFail side condition
  - `isPure_noFail_d_none` (whole, line 98): other
  - `prTrue_isPure_noFail_bind` (whole, line 239): other
  - `absDiff_bind_le_advantage` (whole, line 267): distance inequality
  - `sdist_le_of_advantage_bool` (whole, line 302): other
  - `sdist_le_of_advantage_absorb` (whole, line 353): other
  - `nomPkg_absorb` (whole, line 482): other
  - 63 (`SPComp.bind_noFail`, `simp only [PMF.bind_apply]`): other
  - 79 (`SPComp.sample_noFail`, `simp only [SPComp.sample, SDistr.bind, P`): other
  - 104 (`isPure_noFail_d_none`, `simp only [SDistr.bind, PMF.bind_apply] `): other
  - 106 (`isPure_noFail_d_none`, `simp only [SDistr.fail_apply_none, mul_o`): suggestion leaves later errors in the proof (1)
  - 251 (`prTrue_isPure_noFail_bind`, `simp only [SDistr.bind, PMF.bind_apply]`): other
  - 256 (`prTrue_isPure_noFail_bind`, `simp only [hnf, zero_mul, zero_add]`): other
  - 286 (`absDiff_bind_le_advantage`, `congr 1`): other
  - 364 (`sdist_le_of_advantage_absorb`, `exact le_trans ha' (hAdv a')`): distance inequality
  - 498 (`nomPkg_absorb`, `exact le_of_eq (by unfold Advantage; rfl`): distance inequality
  - 507 (`nomPkg_absorb`, `simp only [runPkg, h_link_real, h_link_i`): distance inequality
  - 508 (`nomPkg_absorb`, `simp only [Advantage, absDiff_self]`): distance inequality
  - 509 (`nomPkg_absorb`, `exact zero_le`): distance inequality
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 255.

### Crypto/SDist.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 6/10.
- Whole-proof attempts: 18 theorems; closed with the import: 4.
- Theorems closed whole by a frozen suggestion (4):
  - `sdist_self` (line 96): `simp_all [sdist, absDiff_self]`
  - `sdist_sym` (line 99): `simp_all [sdist, absDiff_comm]`
  - `isPure_bind_expand` (line 405): `simp_all [SPComp.bind, hc h₀, SDistr.bind_assoc, SDistr.pure_bind]`
  - `SPComp.initHeap_bind` (line 504): `simp_all [SPComp.bind, SPComp.initHeap, SDistr.pure_bind]`
- Closing steps replaced (2):
  - 343 (`sdist_wkR_le`): `exact zero_le` → `simp_all [zero_le]`
  - 354 (`sdist_wkL_le`): `exact zero_le` → `simp_all [zero_le]`
- Step suggestions not frozen: 438 `solve_by_elim [sdist_comp_right, absDiff_triangle, le_add_of` (without the import: rejected in the joint check); 537 `solve_by_elim [isPure_bind_expand, SPComp.initHeap_bind, prT` (without the import: rejected in the joint check); 540 `solve_by_elim [isPure_bind_expand, SPComp.initHeap_bind, prT` (without the import: rejected in the joint check); 554 `solve_by_elim [absDiff_triangle, le_add_of_absDiff_le, sdist` (without the import: rejected in the joint check).
- Golf (2): 340–341 `simp only [KlSPComp.wkR, absDiff_self] / simp_all [zero_le]` → `simp_all [KlSPComp.wkR, absDiff_self, zero_le]`; 351–352 `simp only [KlSPComp.wkL, absDiff_self] / simp_all [zero_le]` → `simp_all [KlSPComp.wkL, absDiff_self, zero_le]`.
- Failures of `catcrypt_auto?`:
  - `sdist_triangle` (whole, line 104): other
  - `sdist_precomp_le` (whole, line 122): other
  - `sdist_comp_right` (whole, line 131): other
  - `prTrue_bind_eq_weighted` (whole, line 174): other
  - `absDiff_prTrue_bind_le` (whole, line 189): distance inequality
  - `sdist_comp_left` (whole, line 228): other
  - `sdist_comp_left_two` (whole, line 251): other
  - `sdist_comp_left_two_dep` (whole, line 275): elaboration error: unexpected token 'to'; expected term
  - `sdist_wkR_le` (whole, line 319): monotonicity inequality
  - `sdist_wkL_le` (whole, line 346): monotonicity inequality
  - `sdist_comp_add` (whole, line 369): other
  - `sdist_le_of_forall` (whole, line 384): distance inequality
  - `sdist_isPure_le` (whole, line 416): other
  - `sdist_oracleGame_le` (whole, line 515): other
  - 114 (`sdist_triangle`, `apply add_le_add`): distance inequality
  - 115 (`sdist_triangle`, `exact le_iSup₂_of_le D a (le_iSup_of_le `): distance inequality
  - 116 (`sdist_triangle`, `exact le_iSup₂_of_le D a (le_iSup_of_le `): distance inequality
  - 127 (`sdist_precomp_le`, `exact le_iSup₂_of_le D (h a) (le_iSup_of`): distance inequality
  - 146 (`sdist_comp_right`, `exact le_iSup₂_of_le D' a (le_iSup_of_le`): distance inequality
  - 180 (`prTrue_bind_eq_weighted`, `simp only [PMF.bind_apply]`): other
  - 208 (`absDiff_prTrue_bind_le`, `simp only [absDiff]`): distance inequality
  - 209 (`absDiff_prTrue_bind_le`, `apply max_le`): distance inequality
  - 211 (`absDiff_prTrue_bind_le`, `exact le_trans (weighted_bound _ _ _ ε h`): distance inequality
  - 213 (`absDiff_prTrue_bind_le`, `exact le_trans (weighted_bound _ _ _ ε h`): distance inequality
  - 240 (`sdist_comp_left`, `apply absDiff_prTrue_bind_le (f a) _ _ h`): distance inequality
  - 242 (`sdist_comp_left`, `exact le_add_of_absDiff_le (le_iSup₂_of_`): distance inequality
  - 264 (`sdist_comp_left_two`, `exact sdist_comp_left (fun a => SPComp.b`): other
  - 314 (`sdist_comp_left_two_dep`, `exact le_trans hSingle hPerB`): distance inequality
  - 326 (`sdist_wkR_le`, `simp only [KlSPComp.wkR]`): distance inequality
  - 328 (`sdist_wkR_le`, `simp only [SPComp.map]`): distance inequality
  - 340 (`sdist_wkR_le`, `exact le_iSup₂_of_le (fun b => D (Sum.in`): distance inequality
  - 342 (`sdist_wkR_le`, `simp only [KlSPComp.wkR, absDiff_self]`): distance inequality
  - 353 (`sdist_wkL_le`, `simp only [KlSPComp.wkL, absDiff_self]`): distance inequality
  - 356 (`sdist_wkL_le`, `simp only [KlSPComp.wkL, SPComp.map]`): distance inequality
  - 364 (`sdist_wkL_le`, `exact le_iSup₂_of_le (fun b => D (Sum.in`): distance inequality
  - 377 (`sdist_comp_add`, `add_le_add (sdist_comp_right f₁ f₂ g₁) (`): monotonicity inequality
  - 378 (`sdist_comp_add`, `gcongr`): monotonicity inequality
  - 395 (`sdist_le_of_forall`, `exact le_trans this h`): distance inequality
  - 528 (`sdist_oracleGame_le`, `rw [hR A, hR A']`): SPComp equality
  - 530 (`sdist_oracleGame_le`, `rw [hI A, hI A']`): SPComp equality
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 185, 534.

### Crypto/UC.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 0/0.
- Whole-proof attempts: 6 theorems; closed with the import: 1.
- Theorems closed whole by a frozen suggestion: none.
- Closed with the import, not frozen: `mapSum_eq_tensorHom` (`grind [mapSum, KlSPComp.wkR, KlSPComp.wkL, SPComp.map, SPComp.bind_ass`; without the import: this parameter is redundant, environment already contains `CatCrypt.Core.SPComp.bind_assoc` annotate).
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:
  - `mapSum_pure_left` (whole, line 100): SPComp equality
  - `mapSum_pure_right` (whole, line 104): SPComp equality
  - `mapSum_pure_pure` (whole, line 109): other
  - `UCEmulates_of_sdist` (whole, line 164): other
  - `UCEmulates_of_dummy` (whole, line 183): other
  - 102 (`mapSum_pure_left`, `simp [mapSum, SPComp.map, SPComp.pure_bi`): SPComp equality
  - 106 (`mapSum_pure_right`, `simp [mapSum, SPComp.map, SPComp.pure_bi`): SPComp equality
  - 169 (`UCEmulates_of_sdist`, `exact fun A => ⟨A, le_trans (sdist_comp_`): other
  - 192 (`UCEmulates_of_dummy`, `exact ⟨A, le_trans (sdist_comp_right π F`): other

### Crypto/UCMonad.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 1/1.
- Whole-proof attempts: 2 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced (1):
  - 414 (`approxFact_of_sdist`): `rw [this]; exact h` → `simp_all`
- Failures of `catcrypt_auto?`:
  - `approxFact_of_sdist` (whole, line 406): other
  - `UCEmulates_of_sdist` (whole, line 439): other
  - 444 (`UCEmulates_of_sdist`, `exact fun A => ⟨A, le_trans (UCMonadMetr`): other

### Crypto/UCMonad/SPCompInstance.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 2/2.
- Whole-proof attempts: 6 theorems; closed with the import: 1.
- Theorems closed whole by a frozen suggestion: none.
- Closed with the import, not frozen: `mapSumSP_pure_kleisli_comp` (`(unfold UCMonad.mapSumSP; grind [mapSumSP_inr, SPComp.map, SPComp.bind`; without the import: this parameter is redundant, environment already contains `CatCrypt.Core.SPComp.bind_assoc` annotate).
- Closing steps replaced (2):
  - 50 (`spcomp_bind_fail`): `congr 1; funext oa; cases oa <;> rfl` → `grind`
  - 51 (`spcomp_bind_fail`): `_ = PMF.pure none := PMF.bind_const _ _` → `_ = PMF.pure none := by simp_all`
- Failures of `catcrypt_auto?`:
  - `spcomp_bind_fail` (whole, line 43): SPComp equality
  - `mapSumSP_pure_left` (whole, line 72): SPComp equality
  - `mapSumSP_pure_right` (whole, line 76): SPComp equality
  - `mapSumSP_pure_pure` (whole, line 80): other
  - `sdist_mapSumSP_le` (whole, line 96): other
  - 46 (`spcomp_bind_fail`, `simp only [SPComp.bind_def, SPComp.fail]`): other
  - 48 (`spcomp_bind_fail`, `simp only [SDistr.bind, SDistr.fail]`): other
  - 74 (`mapSumSP_pure_left`, `simp [mapSumSP, SPComp.map, SPComp.pure_`): SPComp equality
  - 78 (`mapSumSP_pure_right`, `simp [mapSumSP, SPComp.map, SPComp.pure_`): SPComp equality
  - 102 (`sdist_mapSumSP_le`, `simp only [mapSumSP_inl, SPComp.map, SPC`): distance inequality
  - 103 (`sdist_mapSumSP_le`, `exact le_sup_of_le_left (sdist_le_of_for`): distance inequality
  - 104 (`sdist_mapSumSP_le`, `simp only [mapSumSP_inr, SPComp.map, SPC`): distance inequality
  - 105 (`sdist_mapSumSP_le`, `exact le_sup_of_le_right (sdist_le_of_fo`): distance inequality

### Deep/Eval.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 0/0.
- Whole-proof attempts: 7 theorems; closed with the import: 1.
- Theorems closed whole by a frozen suggestion: none. `eval_rHoare` (line 346) closed with the import by `(unfold CatCrypt.Deep.DeepRHoare; simp_all)`; it was frozen by the first commit and reverted in a follow-up commit, since the old proof is `rfl`. The file is unchanged against the base.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:
  - `RawCode.eval_cast` (whole, line 295): SPComp equality
  - `RawCode.evalWith_cast` (whole, line 302): SPComp equality
  - `RawCode.evalWith_fail` (whole, line 194): other
  - `RawCode.evalWith_eq_eval_no_oracle` (whole, line 206): SPComp equality
  - `evalWith_substOracle` (whole, line 259): SPComp equality
  - `evalWith_congr` (whole, line 273): SPComp equality
  - 266 (`evalWith_substOracle`, `simp only [RawCode.substOracle, RawCode.`): SPComp equality
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 200, 212, 267, 280.

### Examples/DetCPA.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 3/10.
- Whole-proof attempts: 3 theorems; closed with the import: 3.
- Theorems closed whole by a frozen suggestion (2):
  - `diff_msg_prTrue` (line 81): `simp_all [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind, prTrue_bind_sample_Bool, prTrue_pure_bool, det_enc_pair, eq_adversary, xorDet]`
  - `det_enc_xor_insecure` (line 96): `simp_all [same_msg_prTrue, diff_msg_prTrue, AdvantageA, Advantage]`
- Closed with the import, not frozen: `same_msg_prTrue` (`simp_all [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind, p`; without the import: This simp argument is unused:).
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:

### Relational/Approx.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 2/4.
- Whole-proof attempts: 20 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Golf (2): 968–969 `rw [prTrue_bind_eq_weighted, SDistr.tsum_option_eq_add] / simp only [mul_zero, z` → `simp [prTrue_bind_eq_weighted, SDistr.tsum_option_eq_add, mul_zero, zero_add]`; 1066–1067 `rw [prTrue_bind_eq_weighted, SDistr.tsum_option_eq_add] / simp only [mul_zero, z` → `simp [prTrue_bind_eq_weighted, SDistr.tsum_option_eq_add, mul_zero, zero_add]`.
- Failures of `catcrypt_auto?`:
  - `rHoareApprox_bind` (whole, line 826): elaboration error: no suggestion
  - `rHoareApprox_conseq` (whole, line 840): elaboration error: no suggestion
  - `rHoareApprox_liftSDistr` (whole, line 871): elaboration error: no suggestion
  - `rHoareApprox_trans_eq` (whole, line 897): elaboration error: no suggestion
  - `rHoareApprox_upto_bad` (whole, line 926): elaboration error: no suggestion
  - `rHoareApprox_absDiff_prTrue` (whole, line 953): elaboration error: no suggestion
  - `rHoareApprox_advantageA` (whole, line 986): elaboration error: no suggestion
  - `rHoareApprox_sdist` (whole, line 996): elaboration error: no suggestion
  - `prTrue_indicatorAdv_mem` (whole, line 1044): elaboration error: no suggestion
  - `prTrue_indicatorAdv_not_mem` (whole, line 1053): elaboration error: no suggestion
  - `prTrue_bind_weighted'` (whole, line 1063): elaboration error: no suggestion
  - `exists_adv_tvMargin_le` (whole, line 1073): elaboration error: no suggestion
  - `liftRApprox_eqPost_of_forall_absDiff` (whole, line 1121): elaboration error: no suggestion
  - `rHoareApprox_of_forall_absDiff` (whole, line 1137): elaboration error: no suggestion
  - `rHoareApprox_of_advantageA` (whole, line 1192): elaboration error: no suggestion
  - `absDiff_prTrue_le_of_liftRApprox` (whole, line 1216): elaboration error: no suggestion
  - `rHoareApprox_advantageA_of_pre` (whole, line 1245): elaboration error: no suggestion
  - `rHoareApprox_trans_eq_of_pre` (whole, line 1269): elaboration error: no suggestion
  - `rHoareApprox_chain_of_pre` (whole, line 1286): elaboration error: no suggestion
  - `rHoareApprox_chain_const` (whole, line 1309): elaboration error: no suggestion
  - 833 (`rHoareApprox_bind`, `simp only [SPComp.bind_def]`): no message
  - 836 (`rHoareApprox_bind`, `exact hf a b h₁' h₂' hΨ`): no message
  - 882 (`rHoareApprox_liftSDistr`, `exact liftRApprox_of_liftR (liftR_pure ⟨`): no message
  - 937 (`rHoareApprox_upto_bad`, `exact add_le_add (hbad h₁) (hbad h₁)`): no message
  - 962 (`rHoareApprox_absDiff_prTrue`, `rwa [show c.swap.joint (some (p₂, p₁)) =`): no message
  - 964 (`rHoareApprox_absDiff_prTrue`, `exact (hsat p₁ p₂ h0').symm`): no message
  - 990 (`rHoareApprox_advantageA`, `simpa [AdvantageA, Advantage, absDiff] u`): no message
  - 1005 (`rHoareApprox_sdist`, `exact rHoareApprox_absDiff_prTrue h D h₀`): no message
  - 1051 (`prTrue_indicatorAdv_mem`, `rw [SDistr.pure_apply_some, if_pos rfl]`): no message
  - 1059 (`prTrue_indicatorAdv_not_mem`, `rw [SDistr.pure_apply_some, if_neg fun h`): no message
  - 1067 (`prTrue_bind_weighted'`, `simp only [mul_zero, zero_add]`): no message
  - 1087 (`exists_adv_tvMargin_le`, `exact le_of_lt hp`): no message
  - 1088 (`exists_adv_tvMargin_le`, `rw [hv_not p hp, mul_zero, mul_zero]`): no message
  - 1130 (`liftRApprox_eqPost_of_forall_absDiff`, `hA₁.trans (le_of_eq (absDiff_comm _ _) |`): no message
  - 1144 (`rHoareApprox_of_forall_absDiff`, `exact liftRApprox_eqPost_of_forall_absDi`): no message
  - 1198 (`rHoareApprox_of_advantageA`, `simpa [AdvantageA, Advantage, absDiff] u`): no message
  - 1226 (`absDiff_prTrue_le_of_liftRApprox`, `rwa [show c.swap.joint (some (p₂, p₁)) =`): no message
  - 1228 (`absDiff_prTrue_le_of_liftRApprox`, `exact (hsat p₁ p₂ h0').symm`): no message
  - 1250 (`rHoareApprox_advantageA_of_pre`, `simpa [AdvantageA, Advantage, absDiff] u`): no message
  - 1313 (`rHoareApprox_chain_const`, `simpa [Finset.sum_const, Finset.card_ran`): no message

### Relational/Judgment.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 0/0.
- Whole-proof attempts: 2 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:
  - `rHoare_mono_post` (whole, line 61): relational rHoare judgment
  - `rHoare_mono_pre` (whole, line 71): relational rHoare judgment
  - 68 (`rHoare_mono_post`, `exact liftR_mono (fun p₁ p₂ hp => hΨ p₁.`): other
  - 77 (`rHoare_mono_pre`, `exact h h₁ h₂ (hΦ h₁ h₂ hΦ')`): other

### Relational/Rules.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 23/27.
- Whole-proof attempts: 48 theorems; closed with the import: 9.
- Theorems closed whole by a frozen suggestion (2):
  - `advantage_factorization` (line 562): `simp_all [SPComp.bind_assoc G₁ f A, SPComp.bind_assoc G₂ f A, AdvantageA]`
  - `advantage_symm` (line 570): `simp_all [max_comm, Advantage]`
- Closed with the import, not frozen: `SPComp.swap_sample_get` (`(simp only [CatCrypt.Core.SPComp.monad_bind_eq];`; without the import: This simp argument is unused:); `SPComp.swap_get_get` (`(simp only [CatCrypt.Core.SPComp.monad_bind_eq];`; longer than the old proof); `SPComp.swap_set_sample` (`(simp only [CatCrypt.Core.SPComp.monad_bind_eq];`; longer than the old proof); `SPComp.swap_set_get` (`(simp only [CatCrypt.Core.SPComp.monad_bind_eq];`; without the import: This simp argument is unused:); `SPComp.swap_set_set` (`(simp only [CatCrypt.Core.SPComp.monad_bind_eq];`; without the import: this parameter is redundant, environment already contains `CatCrypt.Prob.SDistr.pure_bind` annotated); `get_value_eq` (`(simp only [CatCrypt.Core.SPComp.monad_bind_eq];`; longer than the old proof); `rHoare_rewrite_lhs` (`solve_by_elim [rHoare_swap_lhs, rHoare_conseq, rHoare_symm, rHoare_swa`; longer than the old proof).
- Closing steps replaced (18):
  - 71 (`rHoare_ret_same`): `exact ⟨hΦ, rfl⟩` → `simp_all`
  - 102 (`rHoare_bind`): `exact hf a b h₁' h₂' hΨ` → `(unfold CatCrypt.Prob.liftR; solve_by_elim [rHoare_ret_same])`
  - 116 (`rHoare_refl`): `simp only [eqPost, Prod.mk.injEq] at heq' ⊢ ; exact heq'` → `simp_all [eqPost, Prod.mk.injEq]`
  - 176 (`rHoare_sample_same`): `exact ⟨hΦ, rfl⟩` → `simp_all`
  - 198 (`rHoare_sample_bij`): `exact ⟨hΦ, hfab⟩` → `simp_all`
  - 227 (`rHoare_sample_l`): `exact h a h₁ h₂ hΦ` → `(unfold CatCrypt.Prob.liftR; solve_by_elim [rHoare_sample_same, rHoare_ret_same, rHoare_sa`
  - 251 (`rHoare_sample_r`): `exact h a h₁ h₂ hΦ` → `(unfold CatCrypt.Prob.liftR; solve_by_elim [rHoare_sample_same, rHoare_ret_same, rHoare_sa`
  - 264 (`rHoare_get_sync`): `· exact hΦ` → `· simp_all`
  - 265 (`rHoare_get_sync`): `· exact hSync h₁ h₂ hΦ` → `· grind`
  - 275 (`rHoare_set_sync`): `exact hInv h₁ h₂ hΦ` → `simp_all`
  - 286 (`rHoare_get_l`): `simp only [bind, SPComp.bind, SPComp.get, SDistr.pure_bind]` → `simp_all [SPComp.bind, SPComp.get, SDistr.pure_bind]`
  - 299 (`rHoare_get_r`): `simp only [bind, SPComp.bind, SPComp.get, SDistr.pure_bind]` → `simp_all [SPComp.bind, SPComp.get, SDistr.pure_bind]`
  - 350 (`rHoare_assert`): `exact hΦ` → `simp_all`
  - 605 (`contract_put`): `exact Heap.set_set_same h l v v'` → `grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.get_set_other, Heap.set_set_sam`
  - 661 (`dead_sample`): `exact SDistr.bind_const_eq (k h)` → `simp_all [SDistr.bind_const_eq]`
  - 672 (`dead_get`): `simp only [SPComp.bind_def, SPComp.get_def, SDistr.pure_bind]` → `simp_all [SPComp.bind_def, SPComp.get_def, SDistr.pure_bind]`
  - 689 (`dead_pure`): `rw [SDistr.pure_bind]` → `simp_all [SDistr.pure_bind]`
  - 724 (`rHoare_false`): `exact False.elim hFalse` → `simp_all`
- Step suggestions not frozen: 142 `simp_all [eqPost, Prod.mk.injEq, Prod.ext]` (without the import: This simp argument is unused:); 146 `simp_all [eqPost, Prod.mk.injEq, Prod.ext]` (without the import: This simp argument is unused:); 153 `simp_all [eqPost, Prod.mk.injEq, heq]` (without the import: This simp argument is unused:); 288 `(unfold CatCrypt.Prob.liftR;` (without the import: rejected in the joint check); 301 `(unfold CatCrypt.Prob.liftR;` (without the import: rejected in the joint check); 312 `grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.g` (without the import: this parameter is redundant, environment already contains `CatCrypt.Prob.SDistr.pure_bind` annotated); 314 `(unfold CatCrypt.Prob.liftR;` (without the import: rejected in the joint check); 325 `grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.g` (without the import: this parameter is redundant, environment already contains `CatCrypt.Prob.SDistr.pure_bind` annotated); 327 `(unfold CatCrypt.Prob.liftR;` (without the import: rejected in the joint check); 388 `solve_by_elim [rHoare_conseq, rHoare_symm, rHoare_bind, rHoa` (without the import: rejected in the joint check); 389 `solve_by_elim [rHoare_conseq, rHoare_symm, rHoare_bind, rHoa` (without the import: rejected in the joint check); 406 `(unfold CatCrypt.Prob.liftR;` (without the import: rejected in the joint check); 416 `(unfold CatCrypt.Prob.liftR;` (without the import: rejected in the joint check); 591 `(simp only [CatCrypt.Core.SPComp.monad_bind_eq];` (without the import: rejected in the joint check); 777 `(unfold CatCrypt.Prob.liftR;` (without the import: rejected in the joint check); 817 `(unfold CatCrypt.Prob.liftR;` (without the import: rejected in the joint check).
- Golf (follow-up commit, unused-simp-argument linter): 142, 146, 153 `Prod.mk.injEq` removed from `simp only [eqPost, Prod.mk.injEq]`; 462 `simp only [SPComp.bind, SPComp.sample]` (both arguments flagged unused) deleted. The five pre-existing warnings of the file are gone.
- Failures of `catcrypt_auto?`:
  - `rHoare_conseq` (whole, line 27): relational rHoare judgment
  - `rHoare_symm` (whole, line 38): relational rHoare judgment
  - `rHoare_ret` (whole, line 60): relational rHoare judgment
  - `rHoare_ret_same` (whole, line 67): relational rHoare judgment
  - `rHoare_bind` (whole, line 76): relational rHoare judgment
  - `rHoare_refl` (whole, line 107): relational rHoare judgment
  - `rHoare_trans` (whole, line 126): relational rHoare judgment
  - `rHoare_sample_same` (whole, line 158): relational rHoare judgment
  - `rHoare_sample_bij` (whole, line 179): relational rHoare judgment
  - `rHoare_sample_l` (whole, line 206): relational rHoare judgment
  - `rHoare_sample_r` (whole, line 232): relational rHoare judgment
  - `rHoare_get_sync` (whole, line 256): relational rHoare judgment
  - `rHoare_set_sync` (whole, line 268): relational rHoare judgment
  - `rHoare_get_l` (whole, line 279): relational rHoare judgment
  - `rHoare_get_r` (whole, line 292): relational rHoare judgment
  - `rHoare_put_l` (whole, line 304): relational rHoare judgment
  - `rHoare_put_r` (whole, line 317): relational rHoare judgment
  - `rHoare_fail` (whole, line 334): relational rHoare judgment
  - `rHoare_assert` (whole, line 341): relational rHoare judgment
  - `rHoare_ite` (whole, line 359): relational rHoare judgment
  - `rHoare_if` (whole, line 369): relational rHoare judgment
  - `rHoare_dite` (whole, line 380): relational rHoare judgment
  - `rHoare_swap_lhs` (whole, line 399): relational rHoare judgment
  - `rHoare_swap_rhs` (whole, line 409): relational rHoare judgment
  - `SPComp.swap_sample_sample` (whole, line 423): other
  - `SPComp.swap_get_sample` (whole, line 472): other
  - `SPComp.swap_get_set` (whole, line 521): other
  - `contract_get` (whole, line 587): SPComp equality
  - `contract_put` (whole, line 600): SPComp equality
  - `contract_put_get` (whole, line 614): SPComp equality
  - `dead_sample` (whole, line 653): SPComp equality
  - `dead_get` (whole, line 669): SPComp equality
  - `dead_pure` (whole, line 678): SPComp equality
  - `rHoare_false` (whole, line 721): relational rHoare judgment
  - `rHoare_rewrite_rhs` (whole, line 739): relational rHoare judgment
  - `rHoare_bij_step` (whole, line 766): relational rHoare judgment
  - `rHoare_same_step` (whole, line 807): relational rHoare judgment
  - `rHoare_symm_eq` (whole, line 50): relational rHoare judgment
  - `rHoare_foldM` (whole, line 848): relational rHoare judgment
  - 35 (`rHoare_conseq`, `exact liftR_mono (fun p₁ p₂ hp => hPost `): other
  - 47 (`rHoare_symm`, `exact liftR_mono (fun p₁ p₂ hp => hp) hs`): other
  - 64 (`rHoare_ret`, `exact liftR_pure (h h₁ h₂ hΦ)`): other
  - 88 (`rHoare_bind`, `simp only [SPComp.bind_def]`): other
  - 110 (`rHoare_refl`, `simp only [eqPre] at heq`): other
  - 131 (`rHoare_trans`, `simp only [eqPre] at heq`): other
  - 152 (`rHoare_trans`, `simp only [Prod.mk.injEq] at heq`): suggestion leaves later errors in the proof (1)
  - 166 (`rHoare_sample_same`, `simp only [SPComp.sample]`): other
  - 189 (`rHoare_sample_bij`, `simp only [SPComp.sample]`): other
  - 213 (`rHoare_sample_l`, `simp only [SPComp.bind, SPComp.sample, S`): other
  - 222 (`rHoare_sample_l`, `apply liftR_bind (R := Eq)`): other
  - 223 (`rHoare_sample_l`, `exact liftR_refl (SDistr.uniform σ)`): other
  - 239 (`rHoare_sample_r`, `simp only [SPComp.bind, SPComp.sample, S`): other
  - 247 (`rHoare_sample_r`, `apply liftR_bind (R := Eq)`): other
  - 248 (`rHoare_sample_r`, `exact liftR_refl (SDistr.uniform σ)`): other
  - 261 (`rHoare_get_sync`, `simp only [SPComp.get_def]`): other
  - 273 (`rHoare_set_sync`, `simp only [SPComp.set_def]`): other
  - 337 (`rHoare_fail`, `simp only [SPComp.fail]`): other
  - 338 (`rHoare_fail`, `exact liftR_fail`): other
  - 345 (`rHoare_assert`, `simp only [SPComp.assert]`): other
  - 347 (`rHoare_assert`, `simp only [hp, ↓reduceIte]`): other
  - 348 (`rHoare_assert`, `simp only [SPComp.pure_def]`): other
  - 427 (`SPComp.swap_sample_sample`, `simp only [SPComp.monad_bind_eq, SPComp.`): other
  - 444 (`SPComp.swap_sample_sample`, `rw [SDistr.bind_comm]`): other
  - 476 (`SPComp.swap_get_sample`, `rw [SPComp.swap_sample_get]`): other
  - 525 (`SPComp.swap_get_set`, `rw [SPComp.swap_set_get (hne := hne.symm`): other
  - 603 (`contract_put`, `simp only [SPComp.monad_bind_eq, SPComp.`): suggestion leaves later errors in the proof (1)
  - 617 (`contract_put_get`, `simp only [SPComp.monad_bind_eq, SPComp.`): other
  - 656 (`dead_sample`, `simp only [SPComp.bind_def, SPComp.sampl`): other
  - 659 (`dead_sample`, `simp only [SDistr.pure_bind]`): other
  - 744 (`rHoare_rewrite_rhs`, `rw [heq]; exact h`): relational rHoare judgment
  - 773 (`rHoare_bij_step`, `simp only [SPComp.bind, SPComp.sample, S`): other
  - 813 (`rHoare_same_step`, `simp only [SPComp.bind, SPComp.sample, S`): other
  - 53 (`rHoare_symm_eq`, `refine rHoare_conseq ?_ ?_ h`): relational rHoare judgment
  - 861 (`rHoare_foldM`, `simp only [SPComp.foldM]`): suggestion leaves later errors in the proof (1)
  - 862 (`rHoare_foldM`, `exact rHoare_ret (fun _ _ h => h)`): relational rHoare judgment
  - 868 (`rHoare_foldM`, `simp only [SPComp.foldM_cons]`): relational rHoare judgment
  - 872 (`rHoare_foldM`, `apply rHoare_bind (Ψ := fun b₁ h₁ b₂ h₂ `): relational rHoare judgment
  - 873 (`rHoare_foldM`, `exact h_step 0 (Nat.zero_lt_succ _) a₁ a`): relational rHoare judgment
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 434, 439, 863.

### Relational/SpanLifting.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 1/2.
- Whole-proof attempts: 1 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Golf (1): 63–64 `rw [PMF.bind_apply, SDistr.tsum_option_eq_add] / simp only [SDistr.fail_apply_so` → `simp [PMF.bind_apply, SDistr.tsum_option_eq_add, SDistr.fail_apply_some, mul_zer`.
- Failures of `catcrypt_auto?`:
  - `rHoare_iff_spanLift` (whole, line 165): elaboration error: no suggestion
  - 173 (`rHoare_iff_spanLift`, `exact spanLift_of_liftR (h h₁ h₂ hΦ)`): no message
  - 175 (`rHoare_iff_spanLift`, `exact liftR_of_spanLift (h h₁ h₂ hΦ)`): no message

### Unary/Bridge.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 9/19.
- Whole-proof attempts: 11 theorems; closed with the import: 3.
- Theorems closed whole by a frozen suggestion (2):
  - `perfect_indist_of_no_bad` (line 334): `simp_all [prTrue]`
  - `advantage_zero_of_pHoare_det` (line 354): `solve_by_elim [advantage_zero_of_same_result, advantage_zero_of_both_false, prTrue_eq_zero_of_pHoare, prTrue_eq_one_of_pHoare, perfect_indist_of_no_bad, prTrue_eq_prEventComp, failure_event_lemma]`
- Closed with the import, not frozen: `prTrue_eq_prEventComp` (`simp_all [tsum_bool_prod_eq, decide_true, ite_true, Bool.false_eq_true`; without the import: This simp argument is unused:).
- Closing steps replaced (5):
  - 108 (`rHoare_of_pHoare_r`): `exact hrel h₁ h₂ hR` → `(unfold CatCrypt.Prob.liftR; solve_by_elim [rHoare_of_pHoare_l])`
  - 132 (`prTrue_eq_one_of_pHoare`): `simp at this` → `simp_all`
  - 144 (`prTrue_eq_one_of_pHoare`): `apply ENNReal.tsum_eq_zero.mpr; exact hfalse` → `simp_all [ENNReal.tsum_eq_zero.mpr]`
  - 153 (`prTrue_eq_one_of_pHoare`): `exact htotal` → `simp_all`
  - 168 (`prTrue_eq_zero_of_pHoare`): `exact absurd this (by simp)` → `simp_all`
- Step suggestions not frozen: 179 `simp_all [Advantage, hpr₀, hpr₁, tsub_self, max_self]` (without the import: This simp argument is unused:); 197 `simp_all [Advantage, hpr₀, hpr₁, tsub_self, max_self]` (without the import: This simp argument is unused:).
- Golf (follow-up commit, unused-simp-argument linter): 209 `decide_true` removed from the `simp only` list. The remaining five warnings are pre-existing: three unused-variable warnings on statement binders (`hph`, `hcombine`), which would need a statement change, and two linter warnings with a "Try this" at the `letI` lines 253–254, which were not addressed.
- Failures of `catcrypt_auto?`:
  - `pHoare_of_rHoare_diag` (whole, line 68): other
  - `rHoare_of_pHoare_l` (whole, line 92): relational rHoare judgment
  - `rHoare_of_pHoare_r` (whole, line 102): relational rHoare judgment
  - `prTrue_eq_one_of_pHoare` (whole, line 122): other
  - `prTrue_eq_zero_of_pHoare` (whole, line 159): other
  - `advantage_zero_of_both_false` (whole, line 172): other
  - `advantage_zero_of_same_result` (whole, line 185): other
  - `failure_event_lemma` (whole, line 242): distance inequality
  - 84 (`pHoare_of_rHoare_diag`, `exact (hsat (a, h') p₂ hp₂).2.2`): other
  - 99 (`rHoare_of_pHoare_l`, `exact hrel h₁ h₂ hR`): other
  - 287 (`failure_event_lemma`, `(tsum_some_eq_mass (G₁ h₀)).symm ▸ (by u`): other
  - 308 (`failure_event_lemma`, `ENNReal.tsum_add`): other
  - 310 (`failure_event_lemma`, `add_le_add le_rfl ((bad_true_le G₀).tran`): monotonicity inequality
  - 324 (`failure_event_lemma`, `ENNReal.tsum_add`): other
  - 326 (`failure_event_lemma`, `add_le_add le_rfl ((bad_true_le G₁).tran`): monotonicity inequality

### Unary/ExpectationVCGen.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 10/11.
- Whole-proof attempts: 10 theorems; closed with the import: 4.
- Theorems closed whole by a frozen suggestion (4):
  - `wpEF_pure` (line 106): `simp_all [wpEF, wpE_pure, SPComp.pure, SDistr.pure_apply_none, mul_zero, add_zero]`
  - `wpEF_get` (line 137): `simp_all [wpEF, wpE_get, SPComp.get, SDistr.pure_apply_none, mul_zero, add_zero]`
  - `wpEF_set` (line 142): `solve_by_elim [wpEF_pure, wpEF_bind, wpEF_get, wpEF_sample, spcomp_bind_apply_none, wpEF_mono]`
  - `wpEF_fail` (line 147): `simp_all [wpEF, wpE_fail, SPComp.fail, SDistr.fail_apply_none, mul_one, zero_add]`
- Closing steps replaced (6):
  - 102 (`spcomp_bind_apply_none`): `simp only [SDistr.fail_apply_none, mul_one]` → `simp_all [SDistr.fail_apply_none, mul_one]`
  - 116 (`wpEF_bind`): `ring` → `(unfold CatCrypt.Unary.wpE; grind)`
  - 132 (`wpEF_sample`): `simp [SDistr.uniform_apply_none, SDistr.pure_apply_none]` → `simp_all [SDistr.uniform_apply_none, SDistr.pure_apply_none]`
  - 133 (`wpEF_sample`): `rw [wpEF, wpE_sample, hnone, mul_zero, add_zero]` → `simp_all [wpEF, wpE_sample, mul_zero, add_zero]`
  - 176 (`wp_bot_eq_wpE`): `rw [wp_eq_wpEF, wpEF, lean_order_bot_eq_zero, zero_mul, add_zero]` → `simp_all [wp_eq_wpEF, wpEF, lean_order_bot_eq_zero, zero_mul, add_zero]`
  - 251 (`same_msg_prTrue_vcgen`): `exact (triple_iff_le_wpE _ _ _).1 ht Heap.empty` → `simp_all [triple_iff_le_wpE]`
- Golf (1): 101–102 `rw [PMF.bind_apply, SDistr.tsum_option_eq_add] / simp_all [SDistr.fail_apply_non` → `simp_all [PMF.bind_apply, SDistr.tsum_option_eq_add, SDistr.fail_apply_none, mul`.
- Failures of `catcrypt_auto?`:
  - `spcomp_bind_apply_none` (whole, line 96): other
  - `wpEF_bind` (whole, line 110): other
  - `wpEF_sample` (whole, line 125): other
  - `wp_bot_eq_wpE` (whole, line 173): other
  - `same_msg_prTrue_vcgen` (whole, line 238): other
  - `prEventComp_bind_step_le_vcgen` (whole, line 361): other
  - 113 (`wpEF_bind`, `simp only [wpEF]`): other
  - 397 (`prEventComp_bind_step_le_vcgen`, `simp only [leanOrder_rel_dual_iff, Order`): other
  - 399 (`prEventComp_bind_step_le_vcgen`, `split_ifs <;> simp`): other
  - 402 (`prEventComp_bind_step_le_vcgen`, `exact add_le_add le_rfl (wpE_const_le m `): monotonicity inequality
  - 403 (`prEventComp_bind_step_le_vcgen`, `exact (SPCompU.triple_iff_wpE_le _ _ _).`): other

### Unary/ExpectationWP.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 22/36.
- Whole-proof attempts: 12 theorems; closed with the import: 9.
- Theorems closed whole by a frozen suggestion (9):
  - `sdistrExpect_pure` (line 262): `simp_all [sdistrExpect]`
  - `sdistrExpect_fail` (line 268): `simp_all [sdistrExpect]`
  - `wpE_pure` (line 330): `solve_by_elim [sdistrExpect_pure, sdistrExpect_fail, wpE_eq_tsum, wp_sdistr_eq_tsum, CatCrypt.OrderedMonadAlgebra.μ_bind, CatCrypt.OrderedMonadAlgebra.wp_bind, CatCrypt.OrderedMonadAlgebra.wp_pure, CatCrypt.IsEMAlgebra.bind_eq, sdistrExpect_bind_eq_tsum, CatCrypt.OrderedMonadAlgebra.μ_bind_μ, CatCrypt.OrderedMonadAlgebra.μ_join, CatCrypt.orderedMonadAlgebra_laws_iff]`
  - `wpE_bind` (line 340): `solve_by_elim [wpE_pure, sdistrExpect_pure, wpE_eq_tsum, sdistrExpect_fail, wp_sdistr_eq_tsum, CatCrypt.OrderedMonadAlgebra.μ_bind, sdistrExpect_bind_eq_tsum, CatCrypt.OrderedMonadAlgebra.wp_bind, CatCrypt.OrderedMonadAlgebra.wp_pure, CatCrypt.IsEMAlgebra.bind_eq, CatCrypt.OrderedMonadAlgebra.μ_bind_μ, CatCrypt.OrderedMonadAlgebra.μ_join, CatCrypt.orderedMonadAlgebra_laws_iff]`
  - `wpE_fail` (line 347): `simp_all [wpE_eq_tsum, SPComp.fail]`
  - `wpE_set` (line 356): `solve_by_elim [wpE_pure, wpE_bind, wpE_fail, wpE_get, sdistrExpect_pure, sdistrExpect_fail, wpE_eq_tsum, wp_sdistr_eq_tsum, sdistrExpect_bind_eq_tsum, CatCrypt.OrderedMonadAlgebra.μ_bind, CatCrypt.OrderedMonadAlgebra.wp_bind, CatCrypt.OrderedMonadAlgebra.wp_pure, CatCrypt.IsEMAlgebra.bind_eq, CatCrypt.OrderedMonadAlgebra.μ_bind_μ, CatCrypt.OrderedMonadAlgebra.μ_join]`
  - `wpE_indicator_eq_prEventComp` (line 407): `grind [wpE_eq_tsum, prEventComp, prEvent, tsum_congr]`
  - `wpE_indicator_eq_prTrue` (line 416): `simp_all [wpE_eq_tsum, ENNReal.tsum_prod', CatCrypt.Crypto.prTrue]`
  - `le_prEventComp_iff_le_wpE` (line 427): `simp_all [wpE_indicator_eq_prEventComp]`
- Closing steps replaced (4):
  - 296 (`sdistrExpect_bind_eq_tsum`): `simp` → `simp_all`
  - 314 (`wp_sdistr_eq_tsum`): `exact tsum_congr fun a => by rw [sdistrExpect_pure]` → `simp_all [sdistrExpect_pure]`
  - 460 (`wpE_sample`): `exact congrArg _ (funext hinner)` → `simp_all [congrArg]`
  - 464 (`wpE_sample`): `exact tsum_congr fun a => by rw [SDistr.uniform_apply_some]` → `simp_all [SDistr.uniform_apply_some]`
- Step suggestions not frozen: 461 `solve_by_elim [wp_sdistr_eq_tsum, sdistrExpect_bind_eq_tsum,` (without the import: rejected in the joint check).
- Golf (1): 310–311 `rw [sdistrExpect_bind_eq_tsum] / simp_all [sdistrExpect_pure]` → `simp_all [sdistrExpect_bind_eq_tsum, sdistrExpect_pure]`.
- Failures of `catcrypt_auto?`:
  - `sdistrExpect_bind_eq_tsum` (whole, line 273): other
  - `wp_sdistr_eq_tsum` (whole, line 310): other
  - `wpE_sample` (whole, line 440): other
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 456, 457, 459.

### Unary/ExpectedCost.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 8/21.
- Whole-proof attempts: 14 theorems; closed with the import: 6.
- Theorems closed whole by a frozen suggestion (6):
  - `wpE_add` (line 91): `simp_all [wpE_eq_tsum, mul_add, ENNReal.tsum_add]`
  - `wpE_const_mul` (line 97): `grind [wpE_eq_tsum, ENNReal.tsum_mul_left, tsum_congr]`
  - `wpE_zero` (line 103): `simp_all [wpE_eq_tsum]`
  - `wpE_congr` (line 108): `(unfold CatCrypt.Unary.wpE; simp_all)`
  - `wpE_const_of_lossless` (line 122): `simp_all [wpE_eq_tsum, ENNReal.tsum_mul_right, tsum_some_eq_mass, hc h, one_mul]`
  - `ecost_lift_of_lossless` (line 210): `simp_all [wpE_bind, wpE_pure, ecost, CostComp.lift, wpE_const_of_lossless]`
- Closing steps replaced (1):
  - 556 (`spcomp_pure_support`): `exact ⟨(Prod.ext_iff.mp hmem).1.symm, (Prod.ext_iff.mp hmem).2.symm⟩` → `simp_all`
- Golf (1): 179–180 `rw [wpE_pure] / simp` → `simp [wpE_pure]`.
- Failures of `catcrypt_auto?`:
  - `erase_pure` (whole, line 294): SPComp equality
  - `erase_fail` (whole, line 299): SPComp equality
  - `erase_bind` (whole, line 305): SPComp equality
  - `erase_lift` (whole, line 316): SPComp equality
  - `erase_bind_lift` (whole, line 328): SPComp equality
  - `ecost_of_spTreeQueryAdm` (whole, line 441): other
  - `ecost_of_costBounded` (whole, line 454): other
  - `spcomp_pure_support` (whole, line 553): other
  - 297 (`erase_pure`, `rw [SPComp.pure_bind]`): SPComp equality
  - 302 (`erase_fail`, `rw [SPComp.fail_bind]`): SPComp equality
  - 314 (`erase_bind`, `rw [SPComp.pure_bind]`): SPComp equality
  - 324 (`erase_lift`, `rw [heq, SPComp.bind_pure]`): SPComp equality
  - 336 (`erase_bind_lift`, `rw [SPComp.pure_bind]`): SPComp equality
  - 446 (`ecost_of_spTreeQueryAdm`, `refine ⟨fun a => compileCharged (s a), n`): other
  - 447 (`ecost_of_spTreeQueryAdm`, `rw [compileCharged_erase, hs a]`): SPComp equality
  - 458 (`ecost_of_costBounded`, `refine ⟨fun a => compileCharged (s a), f`): other
  - 459 (`ecost_of_costBounded`, `rw [compileCharged_erase, hs a]`): SPComp equality

### Unary/QueryBound.lean

- Temporary import: `CatCryptCore.Tactics.AutoBase`. Lines added/deleted: 10/16.
- Whole-proof attempts: 9 theorems; closed with the import: 3.
- Theorems closed whole by a frozen suggestion (2):
  - `prEventComp_pure` (line 269): `simp_all [SPComp.pure_def, prEventComp, prEvent_pure]`
  - `prEvent_bind_step_eq_tsum` (line 317): `simp_all [SPComp.bind_def, prEvent_bind_eq, prEventComp]`
- Closed with the import, not frozen: `sdistr_mass_le_one` (`(unfold CatCrypt.Prob.SDistr.mass; simp_all [tsub_le_self])`; without the import: simp_all made no progress).
- Closing steps replaced (7):
  - 258 (`prEvent_pure`): `simp [hb, SDistr.pure_apply_some]` → `simp_all [SDistr.pure_apply_some]`
  - 263 (`prEvent_pure`): `simp [hz]` → `simp_all`
  - 343 (`prEventComp_bind_step_le`): `_ = (m h₀) (some p) := mul_one _` → `_ = (m h₀) (some p) := by simp_all`
  - 386 (`prBad_induction`): `exact if_neg h_start` → `simp_all`
  - 394 (`prBad_induction`): `_ = ((q : ℝ≥0∞) + 1) * ε := by rw [add_mul, one_mul]` → `_ = ((q : ℝ≥0∞) + 1) * ε := by simp_all [add_mul, one_mul]`
  - 395 (`prBad_induction`): `_ = ((q + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring` → `_ = ((q + 1 : ℕ) : ℝ≥0∞) * ε := by simp_all`
  - 454 (`advantage_le_query_bound_derived`): `exact prBad_induction step Heap.empty bad ε h_start h_fresh q` → `simp_all [prBad_induction]`
- Step suggestions not frozen: 392 `solve_by_elim [prEventComp_bind_step_le, sdistr_mass_le_one,` (without the import: rejected in the joint check).
- Golf (3): 279–280 `rw [PMF.bind_apply, tsum_option_split] / simp only [SDistr.fail_apply_some, mul_` → `simp [PMF.bind_apply, tsum_option_split, SDistr.fail_apply_some, mul_zero, zero_`; 382–383 `rw [prEventComp_pure] / simp_all` → `simp_all [prEventComp_pure]`; 450–451 `rw [prEventComp_loopGame] / simp_all [prBad_induction]` → `simp_all [prEventComp_loopGame, prBad_induction]`.
- Failures of `catcrypt_auto?`:
  - `prEvent_pure` (whole, line 252): other
  - `prEvent_bind_eq` (whole, line 287): other
  - `prEventComp_bind_step_le` (whole, line 324): other
  - `prBad_induction` (whole, line 375): other
  - `prEventComp_loopGame` (whole, line 420): other
  - `advantage_le_query_bound_derived` (whole, line 440): other
  - 256 (`prEvent_pure`, `rw [tsum_eq_single (a, h)]`): other
  - 262 (`prEvent_pure`, `exact if_neg (fun heq => hp heq.symm)`): other
  - 342 (`prEventComp_bind_step_le`, `mul_le_mul' le_rfl ((prEvent_le_mass _ _`): distance inequality
  - 345 (`prEventComp_bind_step_le`, `exact mul_le_mul' le_rfl (h_fresh p.2 hb`): distance inequality
  - 356 (`prEventComp_bind_step_le`, `apply add_le_add`): monotonicity inequality
  - 357 (`prEventComp_bind_step_le`, `exact le_of_eq rfl`): other
  - 384 (`prBad_induction`, `simp only [repeatStep, Nat.cast_zero, ze`): other
  - 393 (`prBad_induction`, `add_le_add ihq le_rfl`): monotonicity inequality
- Candidate positions that were not tactic positions (the trial text did not parse or elaborate as a tactic there; not counted as attempts): 347.

### XDijkstra/Rel/XCombinedAutomation.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 4 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:
  - `prf_multi_query_via_advmvcgen_bang` (whole, line 194): elaboration error: no suggestion
  - `prf_multi_query_dep_via_advmvcgen_dep_bang` (whole, line 204): elaboration error: no suggestion
  - `prf_multi_query_from_single_via_advmvcgen_bang` (whole, line 215): elaboration error: no suggestion
  - `prf_multi_query_via_advmvcgen_bang_hook` (whole, line 232): elaboration error: no suggestion
  - 199 (`prf_multi_query_via_advmvcgen_bang`, `exact hstep          -- the only residua`): no message
  - 209 (`prf_multi_query_dep_via_advmvcgen_dep_bang`, `exact hstep          -- the only residua`): no message
  - 236 (`prf_multi_query_via_advmvcgen_bang_hook`, `advmvcgen!?`): no message

### XDijkstra/Rel/XHybridExample.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 0 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:

### XDijkstra/Rel/XRelMvcgenControl.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 2 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:
  - `relDemo_branch_sdistr` (whole, line 228): elaboration error: no suggestion
  - `relDemo_loop_sdistr` (whole, line 241): elaboration error: no suggestion
  - 234 (`relDemo_branch_sdistr`, `relmvcgen_ctl`): no message
  - 235 (`relDemo_branch_sdistr`, `exact ht`): no message
  - 246 (`relDemo_loop_sdistr`, `relmvcgen_ctl`): no message
  - 247 (`relDemo_loop_sdistr`, `exact hbase`): no message

### XDijkstra/Rel/XRelMvcgen.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 1 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:
  - `relDemo3_sdistr_tac` (whole, line 199): elaboration error: no suggestion
  - 209 (`relDemo3_sdistr_tac`, `relmvcgen`): no message
  - 210 (`relDemo3_sdistr_tac`, `exact h₁`): no message

### XDijkstra/Rel/XRelSpecMonad.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 0 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:

### XDijkstra/Rel/XSDistrSoundness.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 2 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:
  - `demo_sdistr_pure` (whole, line 129): elaboration error: no suggestion
  - `demo_sdistr_bind` (whole, line 140): elaboration error: no suggestion
  - 134 (`demo_sdistr_pure`, `exact ((SDistr.mem_support_pure_iff 3 a)`): no message
  - 147 (`demo_sdistr_bind`, `exact ((SDistr.mem_support_pure_iff 2 a)`): no message

### XDijkstra/XAdvantageHybrid.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 3 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:
  - `prf_multi_query_via_advmvcgen` (whole, line 176): elaboration error: no suggestion
  - `prf_multi_query_from_single` (whole, line 189): elaboration error: no suggestion
  - `prf_multi_query_dep_via_advmvcgen` (whole, line 203): elaboration error: no suggestion
  - 180 (`prf_multi_query_via_advmvcgen`, `advmvcgen`): no message
  - 181 (`prf_multi_query_via_advmvcgen`, `exact hstep      -- per-hop single-query`): no message
  - 195 (`prf_multi_query_from_single`, `advmvcgen`): no message
  - 197 (`prf_multi_query_from_single`, `exact le_rfl                            `): no message
  - 207 (`prf_multi_query_dep_via_advmvcgen`, `advmvcgen_dep`): no message
  - 208 (`prf_multi_query_dep_via_advmvcgen`, `exact hstep      -- per-hop leaf (pins ε`): no message

### XDijkstra/XMvcgenControl.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 0 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:

### XDijkstra/XMvcgen.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 0 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:

### XDijkstra/XMvcgenReg.lean

- Temporary import: `CatCryptCore.Tactics.AutoDispatch`. Lines added/deleted: 0/0.
- Whole-proof attempts: 0 theorems; closed with the import: 0.
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced: none.
- Failures of `catcrypt_auto?`:


# AUTO_CORPUS_6 report

Branch `work/auto-corpus-6`, created from `origin/work/auto-corpus` at 751637d. Proof-simplification pass with `catcrypt_auto?` (temporary import of `CatCryptCore.Tactics.AutoDispatchExt`), golf and deprecation replacement over the 24 files of the task list. All suggestions were read with `lean-query.py diag` on a trial copy of the file; every frozen suggestion was then checked without the temporary import, and each edited module was built with `lake build CatCryptCore.<Module>` (no new warnings in the edited file). A final joint build of the five edited modules and `CatCryptCore.Tactics.AutoDispatchExt` completed successfully (2755 jobs). Mathlib was replayed, not rebuilt.

No statement, definition, import, attribute or declaration name was changed; no declaration was added or deleted; no `sorry` or `native_decide` was introduced. `CatCryptCore.Tactics.AutoMetrics` was not imported in any file: no frozen suggestion uses `hop_chain`, `sum_atoms_le` or `gcongr_unfold`. No deprecation warning occurs in any of the 24 files, so step 3 made no change.

## Lines added/deleted (`git diff --numstat origin/work/auto-corpus`)

| File | added | deleted |
|---|---|---|
| CatCryptCore/Relational/Sync.lean | 2 | 14 |
| CatCryptCore/Unary/ExpectationVCGenExamples.lean | 9 | 13 |
| CatCryptCore/Unary/ExpectationVCGenLoops.lean | 6 | 7 |
| CatCryptCore/Unary/FailureEvent.lean | 16 | 21 |
| CatCryptCore/XDijkstra/Rel/XCoreProtocolReduction.lean | 4 | 6 |

The other 19 files are unchanged (see "Skipped files").

## Per-file results

Line numbers refer to the file at 751637d unless noted.

### Relational/Sync.lean

- Whole-proof attempts: 13 theorems (all state `rHoare`).
- Closed with the import, not frozen (6): `r_get_vs_get`, `r_get_vs_get_diff`, `r_put_vs_put`, `r_sample_vs_sample`, `r_sample_vs_sample_bij`, `r_swap`. Each suggestion is `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe …)`; without the import Lean reports "no such rule set: 'CatCryptRel'".
- Theorems closed whole by a frozen suggestion: none.
- Closing steps replaced (1): `r_frame`, `exact ⟨hΘ, hFrame a h₁' b h₂' hΘ⟩` → `grind`.
- Golf: three `simp only [SPComp.get_def]`/`[SPComp.set_def]` and one `simp only [SPComp.sample]` removed (the following `exact`/`apply` works up to definitional unfolding); in `r_sample_put_vs_sample_put` the two auxiliary `have heq₁/heq₂` and `simp only [heq₁, heq₂]` replaced by adding `SDistr.pure_bind` to the preceding `simp only`.
- Failures of `catcrypt_auto?`:
  - whole proofs of `r_get_vs_get'`, `r_put_vs_put_diff`, `r_put_vs_put_diff_loc`, `r_sample_vs_sample_coupling`, `r_get_put_vs_get_put`, `r_sample_put_vs_sample_put`, `r_frame`: shape "relational rHoare judgment", aesop (CatCryptRel), ssprove_crypto and ssprove_crypto_grind failed, also after the head-definition unfolding pass.
  - 55, 85, 95, 127, 147, 170 (`exact liftR_pure …`): shape "other", goal `liftR _ (SDistr.pure _) (SDistr.pure _)`; simp_all no progress, grind failed.

### Unary/ExpectationVCGenExamples.lean (I-ok; not a `module`, temporary import as plain `import`)

- Whole-proof attempts: 3 theorems (`prBad_induction_vcgen`, `prTrue_union_bound_vcgen`, `prTrue_double_sample_pure_bool_vcgen`); none closed.
- Closing steps replaced (9): 197 `simpa [hb, prEventComp] using h_fresh h hb` → `simp_all [prEventComp]`; 209 `simp` → `simp_all`; 224 `ring` → `grind`; 229 `simpa [h_start] using this` → `simp_all`; 309–310 `simp only […]` (2 lines) → `simp_all [wpE_pure, wpE_indicator_eq_prTrue, prTrue_isPure_eq hd₂]`; 312 `exact le_add_right (wpE_const_le _ _ _)` → `simp_all [le_add_right, wpE_const_le]`; 342–343 `simp only […]` (2 lines) → `simp_all [tsum_fintype, Finset.mul_sum, Nat.cast_sum, mul_assoc]`; 351 `exact harith.ge`, 361 `exact harith.le` → `simp_all`. Arguments that the unused-simp-argument linter flagged in the suggestions were dropped.
- Golf: 227–229 (`simp only [add_zero] at this`; `rw [wpE_indicator_eq_prEventComp] at this`; `simp_all`) → `simp_all [wpE_indicator_eq_prEventComp]`.
- Failures of `catcrypt_auto?`:
  - `prBad_induction_vcgen` (whole): shape "other", after unfolding `prEventComp`/`repeatStep` "distance inequality"; sum_atoms_le: atom `prEventComp (repeatStep step q) h₀ _` not bounded on the right; hop_chain: `prEvent` not a `@[hop_metric]` distance.
  - `prTrue_union_bound_vcgen` (whole): distance inequality `prTrue (bad₁ >>= …) _ ≤ prTrue bad₁ _ + prTrue bad₂ _`; hop_chain: `prTrue` not a `@[hop_metric]` distance; sum_atoms_le atom unbounded; gcongr no progress; bound failed.
  - `prTrue_double_sample_pure_bool_vcgen` (whole): shape "other" (`prTrue … = card / card ^ 2`); simp_all maximum recursion depth; grind failed.
  - 194–196 (`simpa … using …`, bad case): shape "other", `wpE`/`prEventComp` bound; sum_atoms_le atom unbounded, simp_all goals remain.
  - 225 (`exact key`): shape "other", `Triple (SPCompU.lift (repeatStep step (n+1))) …`; simp_all goals remain, grind failed.
  - 315 (`exact add_le_add le_rfl (wpE_const_le _ _ _)`): suggestion `(gcongr <;> catcrypt_grind [wpE_const_le])` closes with the import; `catcrypt_grind` is an unknown tactic without it; not frozen.
  - 316 (`exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht Heap.empty`): shape "other", `wpE … ≤ wpE … + wpE …`; sum_atoms_le atom unbounded; simp_all goals remain.
  - 362–363 (`exact le_antisymm …`): shape "other", equality of `wpE`/`prTrue`; simp_all goals remain.

### Unary/ExpectationVCGenLoops.lean (I-ok)

- Whole-proof attempts: 4 theorems (`repeatStep_succ_eq_bind`, `forIn_eq_repeatStep`, `prBad_induction_forIn_vcgen`, `forIn_retryStep_eq`); none closed.
- Closing steps replaced (5): 94, 95 `case vc1/vc2 => simp` → `simp_all`; 106 `simpa [hb, wpE_indicator_eq_prEventComp, prEventComp] using h_fresh s hb` → `simp_all [wpE_indicator_eq_prEventComp, prEventComp]`; 108 calc step `by ring` → `by grind`; 112 `simp [h_start]` → `simp_all`.
- Golf: 54–55 `rw [SPComp.pure_bind]`; `exact (SPComp.bind_pure step).symm` → `rw [SPComp.pure_bind, SPComp.bind_pure]`.
- Suggestions not frozen: 60 `simp only [ih]` → `catcrypt_grind`; 138 `rw [SPComp.pure_bind, add_zero]`, 144 and 145 `simp only […]` → `catcrypt_grind […]`. `catcrypt_grind` is an unknown tactic without the temporary import.
- Failures of `catcrypt_auto?`:
  - `repeatStep_succ_eq_bind`, `forIn_retryStep_eq` (whole): shape "SPComp equality"; catcrypt_grind failed, bind_vcgen goals remain; after the unfolding pass catcrypt_grind reached the 20000-heartbeat budget.
  - `forIn_eq_repeatStep` (whole): shape "other" (`forIn` in `SPCompU` = `repeatStep`); simp_all goals remain, grind failed.
  - `prBad_induction_forIn_vcgen` (whole): shape "other", after unfolding `prEventComp` "distance inequality"; sum_atoms_le atom unbounded; hop_chain: `prEvent` not registered.
  - 55 (`exact (SPComp.bind_pure step).symm`): shape "SPComp equality", `step = step.bind fun _ => pure ()`; catcrypt_grind failed, bind_vcgen goals remain.
  - 71 (`exact (repeatStep_succ_eq_bind step as.length).symm`): shape "other" (`SPCompU` do-block = `repeatStep step (a :: as).length`); simp_all goals remain.
  - 104–105 (`exact ((wpE_mono …).trans …).trans le_self_add`): shape "other", `wpE step (indicator) s ≤ 1 + ε`; sum_atoms_le atom unbounded; simp_all goals remain.

### Unary/FailureEvent.lean (not I-ok)

- Whole-proof attempts: 10 theorems.
- Theorems closed whole by one frozen suggestion (1): `prEvent_agree_of_no_bad`, five tactic lines → `grind [prEventComp, prEvent]`.
- Closing steps replaced (15): 86 `unfold Advantage; exact max_comm _ _` → `simp_all [Advantage, max_comm]`; 125 `exact h_agree b h' hbad.1 hbad.2` → `grind`; 212, 254 `simp [hE, hb, le_self_add]` → `simp_all`; 215, 257 calc step `ENNReal.tsum_add` → `by simp_all [ENNReal.tsum_add]`; 237, 411 calc step `tsum_some_eq_mass (G₁ h₀)` → `by simp_all [tsum_some_eq_mass]`; 238, 412 `unfold SDistr.mass; exact tsub_le_self` → `simp_all [SDistr.mass]`; 247, 422 `rwa [ENNReal.add_le_add_iff_right hN_ne_top] at hle` → `simp_all`; 261 `exact max_le (tsub_le_iff_left.mpr h1) (tsub_le_iff_left.mpr h2)` → `grind [max_le, tsub_le_iff_left]`; 438–439 and 440 `exact prBad_le_of_agree …` → `simp_all [prBad_le_of_agree]`.
- Golf: the two unused-simp-argument warnings (`le_self_add` at 212 and 254) disappear with the frozen `simp_all`.
- Suggestions not frozen: 148, 177 calc step `advantage_triangle …` → `catcrypt_grind [advantage_triangle]` (unknown tactic without the import); 260 `add_le_add le_rfl bad_G₁_le` → `gcongr_unfold` (file not I-ok); 230, 404 `by_cases hb … <;> simp [hb, h_agree p.1 p.2]`: the two branches received different suggestions (`simp_all [hb, h_agree]`, `grind`), so no single tactic replaces the step.
- Failures of `catcrypt_auto?`:
  - `advantage_le_prBad`, `advantage_le_prBad_right`, `advantage_le_prBad_union`, `advantage_le_two_bad`, `advantage_le_three_bad` (whole): distance inequality `Advantage G₀ G₁ ≤ prEventComp …` (or a sum of `prEventComp`); hop_chain: no hop facts found (the cited lemmas are ∀-quantified and are not instantiated); sum_atoms_le: `Advantage` atom unbounded; gcongr no progress; bound failed.
  - `advantageA_le_prBad` (whole): same, with `AdvantageA G₀ G₁ A`.
  - `prEvent_diff_le_prBad` (whole): shape "other", `max (prEventComp … - prEventComp …) (…) ≤ prEventComp …`; sum_atoms_le atom unbounded; simp_all goals remain.
  - `prBad_le_of_agree` (whole): shape "monotonicity inequality"; gcongr_unfold leaves `(if bad … then G₁ … else 0) ≤ (if bad … then G₀ … else 0)`.
  - `prBad_eq_of_agree` (whole): shape "other" (equality of two `prEventComp`); simp_all goals remain.
  - 88–90, 105–106 (`exact failure_event_lemma …`): distance inequality; hop_chain composes to `Advantage G₁ G₀` with the residual not closed, resp. no hop facts.
  - 126 (`exact hll₀`): shape "other" (losslessness goal); simp_all goals remain.
  - 152, 153, 182, 183 (`exact advantage_le_prBad …`, `exact advantage_le_two_bad …`): distance inequality; hop_chain: no hop facts.
  - 213, 255 (`simp [hE, hb, h_agree p.1 p.2 hb]` under `<;>`): one branch failed, shape "other", sum_atoms_le: atom `if E p.1 p.2 then G (some p) else 0` unbounded.

### XDijkstra/Rel/XCoreProtocolReduction.lean (I-ok)

- Whole-proof attempts: 3 SPComp equalities; all three closed with the import, none frozen: `sdistrToSPComp_uniform` → `bind_vcgen` (original proof `rfl`); `prfQueryRealSD_lift` → `unfold …; simp only [SPComp.monad_bind_eq]; catcrypt_grind […]`; `prfQueryIdealSD_lift` → `catcrypt_grind [prfQueryIdealSD, prf_query_ideal, sdistrToSPComp_uniform]`. `bind_vcgen` and `catcrypt_grind` are unknown tactics without the temporary import.
- The remaining theorems state `XRelTripleQ0` couplings or an `nsmul` identity and are outside the statement classes of step 1.
- Closing steps replaced: none.
- Golf: `prfQueryRealSD_lift` `rw [sdistrToSPComp_bind, sdistrToSPComp_uniform]`; `simp only [sdistrToSPComp_pure]` → one `simp only` with the three lemmas; `prfQueryIdealSD_lift` `unfold …`; `exact sdistrToSPComp_uniform V` → `exact sdistrToSPComp_uniform V`; three `intro a b hab; exact h a b hab` → `exact h`.

## Skipped files

Import cycle. For each of these 15 files, adding `public import CatCryptCore.Tactics.AutoDispatchExt` makes Lake report "build cycle detected" (`CatCryptCore.Tactics.AutoDispatchExt:exportInfo` → `<Module>:importInfo`), because the module lies in the import closure of `AutoDispatchExt` (through `AutoDispatch`/`AutoSets` or through `XCombinedAutomation`/`XMvcgenReg`). Step 1 is therefore impossible; step 2 was skipped as the task prescribes for this case; step 3 found no deprecation warning. Files not edited:

- Unary/Bridge.lean
- Unary/ExpectationVCGen.lean
- Unary/ExpectationWP.lean
- Unary/ExpectedCost.lean (imports are `public meta import`; the cycle was confirmed by inserting the import after them)
- Unary/QueryBound.lean
- XDijkstra/XAdvantageHybrid.lean
- XDijkstra/XMvcgenControl.lean
- XDijkstra/XMvcgen.lean
- XDijkstra/XMvcgenReg.lean
- XDijkstra/Rel/XCombinedAutomation.lean
- XDijkstra/Rel/XHybridExample.lean
- XDijkstra/Rel/XRelMvcgenControl.lean
- XDijkstra/Rel/XRelMvcgen.lean
- XDijkstra/Rel/XRelSpecMonad.lean
- XDijkstra/Rel/XSDistrSoundness.lean

No statement in step-1 scope and no golf applied. These files import `AutoDispatchExt` without a cycle, but no theorem states `rHoare`, `Advantage`/`AdvantageA`, `sdist`, `prTrue`/`prEvent`, `SPComp.IsPure`/`NoFail` or an SPComp equality. Their proofs are short (mostly `rfl`, `le_rfl` and one-line `rintro`/`exact`), no step had an evident shorter equivalent, and the build reports no linter warning in them. Files not edited:

- XDijkstra/Demo.lean
- XDijkstra/XCostMonad.lean
- XDijkstra/XDijkstraAll.lean (imports only)
- XDijkstra/XErrMonad.lean

## Vacuity-sweep files

None of the 24 files belongs to the vacuity-sweep set (Crypto/BadEvent.lean, Crypto/UCAdmClass*.lean, Examples/Cryptobox/**, Crypto/KeyAgreement/Curve25519.lean, Crypto/KeyAgreement/MontgomeryXOnly.lean), and none of those files was edited. CatCryptCore/Consensus/** was not touched.

## Interface queue

1. Rule set visibility. In Relational/Sync.lean six whole-proof suggestions close their goals but use the Aesop rule set `CatCryptRel`, which is not visible without importing `CatCryptCore.Tactics.AutoSets` (the set is declared in `AutoSetsDecl`, its rules are registered in `AutoSets`). By a static check of the import graph, `AutoSets` does not import Relational/Sync, so adding that import to Sync would not create a cycle. The import was not added, because imports are outside the edits this task permits.
2. Tactic visibility. `catcrypt_grind` (Tactics.AutoSets) and `bind_vcgen` (Tactics.BindVcgen) are unknown in ExpectationVCGenExamples, ExpectationVCGenLoops, FailureEvent and XCoreProtocolReduction without the temporary import. Ten suggestions that close their goals could not be frozen for this reason (FailureEvent 148, 177; ExpectationVCGenLoops 60, 138, 144, 145; ExpectationVCGenExamples 315; XCoreProtocolReduction whole proofs of `sdistrToSPComp_uniform`, `prfQueryRealSD_lift`, `prfQueryIdealSD_lift`). An import of `AutoSets`/`BindVcgen` in these modules would make them freezable. By the same static check, neither `AutoSets` nor `BindVcgen` imports any of the four modules, so such an import would not create a cycle.
3. Hop facts from lemmas. In FailureEvent all `Advantage … ≤ prEventComp …` goals fail in hop_chain with "no hop facts found". The facts are available only as ∀-quantified lemmas (`advantage_le_prBad`, `failure_event_lemma`) whose hypotheses are in context. hop_chain deliberately does not instantiate ∀-quantified facts, so these goals stay outside its reach unless instantiated facts are supplied.
4. Unregistered distances. `prTrue`, `prEvent` and `prEventComp` are not `@[hop_metric]` distances, so the distance-inequality arm rejects every bad-event bound in ExpectationVCGenExamples, ExpectationVCGenLoops and FailureEvent.
5. Missing arm for `liftR` leaves. The goal `liftR _ (SDistr.pure _) (SDistr.pure _)` (closed by `liftR_pure`) is classified as shape "other" and no arm closes it, even with `liftR_pure` passed as an argument (Relational/Sync, six positions).
6. Branch-dependent suggestions. Under `<;>`, `catcrypt_auto?` gives one suggestion per branch, and the suggestions can differ (FailureEvent 230, 404). There is no combined suggestion that could replace the step.
7. Observations in files that were not edited, recorded from build output and not acted on: Unary/Bridge.lean has an unused simp argument at 209:13 and unused variable names at 94:5, 96:5 and 104:5; Unary/QueryBound.lean has an unused variable name at 174:5; XDijkstra/XMvcgenControl.lean has an overlapping-instance-parameters warning at 121:4.

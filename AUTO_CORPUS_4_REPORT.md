# AUTO_CORPUS_4 report

Branch `work/auto-corpus-4`, created from `origin/work/auto-corpus` at 751637d. Each file was
processed in the listed order and committed separately. Line numbers below refer to the files as
they are on `origin/work/auto-corpus` (before this branch). A combined `lake build` of all 27
modules completed successfully after the last commit, with no warnings in the 27 files. No
Mathlib module was rebuilt. The diff adds no `sorry` and no `native_decide`, and changes no
statement, definition, attribute, declaration name or declaration count.

## Method

- Trials used the Lean server through a wrapper around `leanclient`, the library that
  `lean-query.py` uses. `lean-query.py multi` prints neither the "Try this" infos nor
  replacements of line ranges, so the wrapper adds both. The temporary
  `public import CatCryptCore.Tactics.AutoDispatchExt` was inserted in memory only and was
  never written to disk.
- Theorems were selected by a keyword match on the statement (rHoare, Advantage/AdvantageA,
  sdist, prTrue/prEvent, IsPure/NoFail, SPComp). Each selected theorem was tried in two forms:
  the whole proof replaced by `catcrypt_auto? [names cited by the old proof]`, and by bare
  `catcrypt_auto?`.
- When the whole proof stayed open, `catcrypt_auto?` was tried at closing steps: the last
  tactic of each branch, `calc` steps of the form `:= by tac`, and `simp_all`/`simp only`/
  `bind_align` lines.
- Each suggestion was re-elaborated without the temporary import before it was frozen.
- A suggestion that called `catcrypt_grind` (module `AutoSets`) was also tried with plain
  `grind` in place of `catcrypt_grind`. Every frozen `grind` call that came from a
  `catcrypt_grind` suggestion is that substitution.
- Suggestions using `hop_chain`/`sum_atoms_le` were verified with
  `CatCryptCore.Tactics.AutoMetrics` imported; this was done only for (I-ok) files.
- Closing-step suggestions were frozen only when not longer in lines. A closing step whose
  old text was already a single bare closer (`rfl`, `ring`, `simp`, `omega`, `linarith`,
  `simp_all`, `norm_num`, `decide`, `positivity`, `grind`, `le_rfl`) was not replaced.
- After freezing, the module was built. Linter warnings introduced by frozen text were removed
  by deleting the arguments the linter named, and in one case by replacing `<;>` with `;`:
  - unused `simp` arguments
  - `grind` parameters already annotated `@[grind]`
  - `<;>` where `;` suffices
- One whole-theorem suggestion was not kept: `hop1_equiv` in PRFMAC, where the suggestion
  `(simp only [CatCrypt.Core.SPComp.monad_bind_eq]; bind_vcgen)` would replace `rfl`.
- Golf (step 2) was mechanical and kept only when the module built:
  - `rw [..]` followed by `simp` merged into `simp [..]`
  - terminal `calc` blocks replaced by `grind`/`linarith`/`gcongr`
  - outer parentheses and fully qualified `unfold` names dropped in frozen suggestions
- Step 3: the baseline build showed no deprecation warnings in any of the 27 files, so no names
  were replaced.

## Per file

Columns of the numstat line: added, deleted (against `origin/work/auto-corpus`).
"Failures" lists the positions where `catcrypt_auto?` failed: the theorem, the line, the
attempt kind (whole or step), and the goal shape named by the error. A position where some
other attempt succeeded is omitted. "harness" marks a trial that the generator placed
incorrectly (a statement or step spanning lines it did not parse), so it gave no result.

### Examples/Cryptobox/GameHopping.lean (I-ok)

numstat: +15 -26

Theorems closed whole by one frozen suggestion: PKAE_cc_eq_PKEY_check, PKAE_eq_PKEY_nocheck, advantage_comm, cryptobox_security_with_nike_reduction, cryptobox_security_with_nike_reduction_no_gap, middle_step_triangle, pkae_pkey_step_rev.

Closing steps replaced: 8 (pkae_pkey_step L151; pkae_game_hopping L191; pkae_game_hopping L195; pkae_game_hopping L196; cryptobox_security_full L402; cryptobox_security_no_collision L422; cryptobox_security_collision_only L438; nikeStep_structure L657).

Golf: `(gcongr <;> grind [advantage_triangle])` written as `gcongr; grind`; `(unfold CatCrypt.Examples.Cryptobox.middleAdvantage; grind)` written as `unfold middleAdvantage; grind`.

Failures:

- pkae_game_hopping L182 (whole): distance inequality
- cryptobox_security_chain L219 (whole): other
- cryptobox_security_full L393 (whole): other
- cryptobox_security_no_collision L418 (whole): other
- cryptobox_security_collision_only L434 (whole): other
- GNIKE_R_NIKE_unfold L573 (whole): harness
- nikeStep_structure L646 (whole): distance inequality
- nikeStep_bounded L685 (whole): other

### Examples/Cryptobox/HYBRID.lean (I-ok)

numstat: +7 -8

Theorems closed whole by one frozen suggestion: aeHybridStepAdvantage_mem, aeHybrid_step_bound.

Closing steps replaced: 5 (aeHybrid_union_triangle L382; aeHybrid_union_triangle L419; aeHybrid_union_triangle L421; aeStep_bounded_by_sae_finset L522; aeStep_bounded_by_sae_finset L532).

Failures:

- aeHybrid_univ L202 (whole): SPComp equality
- aeHybrid_univ L210 (step): SPComp equality
- aeHybrid_union_triangle L371 (whole): distance inequality
- aeHybrid_union_triangle L386 (step): other
- aeStep_triangle L442 (whole): other
- aeStep_bounded_by_sae L473 (whole): other
- aeStep_bounded_by_sae_finset L511 (whole): other

### Examples/Cryptobox/KEY.lean (I-ok)

numstat: +0 -0 (unchanged)

No theorem or lemma in the file (definitions only); nothing to try.

### Examples/Cryptobox/NIKE.lean (I-ok)

numstat: +0 -0 (unchanged)

No theorem or lemma in the file (definitions only); nothing to try.

### Examples/Cryptobox/PKAE.lean (I-ok)

numstat: +0 -0 (unchanged)

No theorem or lemma in the file (definitions only); nothing to try.

### Examples/Cryptobox/PKEY.lean (I-ok)

numstat: +3 -4

Theorems closed whole by one frozen suggestion: spcomp_bind_congr_left.

Closing steps replaced: 2 (spcomp_fail_bind L423; collision_prob_single_query L532).

Failures:

- PKEY_eq_with_oracles L201 (whole): SPComp equality
- pkeyAdvantage_le_collision L265 (whole): other
- pkey_switching L282 (whole): other
- pkeyAdvantage_instr_le_collision L486 (whole): other
- collision_prob_single_query L526 (whole): distance inequality
- pkey_sdist L575 (whole): distance inequality

### Examples/Cryptobox/SAE.lean (I-ok)

numstat: +0 -0 (unchanged)

No theorem or lemma in the file (definitions only); nothing to try.

### Examples/CTRMode.lean (I-ok)

numstat: +0 -0 (unchanged)

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 0.

Failures:

- ctr_perfect_indcpa L139 (whole): other
- boolCTR_perfect_indcpa L163 (whole): other
- ctr_indcpa_bound L240 (whole): other

### Examples/CyclicGroupDDH.lean

numstat: +0 -0 (unchanged)

No theorem whose statement matches the selection; the temporary import loaded without a cycle. No change.

### Examples/DeepHybrid.lean (I-ok)

numstat: +3 -4

Theorems closed whole by one frozen suggestion: hybrid_step_zero_advantage.

Closing steps replaced: 2 (step_0_1_coupling L180; step_1_2_coupling L203).

Failures:

- single_oracle_coupling L113 (whole): relational rHoare judgment
- single_oracle_zero_advantage L119 (whole): other
- step_0_1_coupling L168 (step): other
- step_0_1_coupling L171 (step): other
- step_1_2_coupling L189 (whole): relational rHoare judgment
- step_1_2_coupling L191 (step): other
- step_1_2_coupling L194 (step): other
- three_instance_triangle L255 (whole): distance inequality
- threeHybrid_simpl L295 (whole): SPComp equality
- threeHybrid_simpl L296 (step): SPComp equality

### Examples/DetCPA.lean (I-ok)

numstat: +1 -2

Step 1 skipped: with the temporary import Lean reports 7 errors `... has already been declared`, i.e. the module is already in the import closure of `AutoDispatchExt` (through `CatCryptCore/Unary/ExpectationVCGen.lean`, which imports `CatCryptCore.Examples.DetCPA`). Golf: in `det_enc_xor_insecure`, `rw [same_msg_prTrue, diff_msg_prTrue]; simp` merged into `simp [same_msg_prTrue, diff_msg_prTrue]`.

### Examples/DiffieHellman.lean (I-ok)

numstat: +2 -3

Theorems closed whole by one frozen suggestion: ka_advantage_eq_ddh, ka_secure_under_ddh.

Closing steps replaced: 0.

Failures: none.

### Examples/ElGamalDDH.lean (I-ok)

numstat: +15 -22

Theorems closed whole by one frozen suggestion: reduction_real_eq_indcpa_real.

Closing steps replaced: 13 (keyGen_bind_eq L191; ElGamal_INDCPA_real_simplified L216; reduction_real_lhs_eq L234; reduction_ideal_indep_message L289; reduction_ideal_indep_message L292; reduction_ideal_indep_message L294; reduction_ideal_indep_message L298; reduction_ideal_indep_message L299; reduction_ideal_indep_message L300; reduction_ideal_indep_message L301; reduction_ideal_indep_message L317; elgamal_indcpa_security L363; elgamal_indcpa_security L368).

Golf: two terminal `calc` blocks (3 and 5 lines, the group-cancellation steps in `reduction_ideal_indep_message` and `elgamal_indcpa_security`) replaced by `grind`.

Failures:

- keyGen_bind_eq L183 (whole): SPComp equality
- keyGen_bind_eq L185 (step): SPComp equality
- ElGamal_INDCPA_real_simplified L207 (whole): SPComp equality
- ElGamal_INDCPA_real_simplified L209 (step): SPComp equality
- ElGamal_INDCPA_real_simplified L213 (step): SPComp equality
- reduction_real_lhs_eq L226 (step): SPComp equality
- reduction_real_rhs_eq L242 (whole): SPComp equality
- reduction_ideal_indep_message L261 (whole): SPComp equality
- reduction_ideal_indep_message L270 (step): SPComp equality
- reduction_ideal_indep_message L310 (step): other
- reduction_ideal_indep_message L319 (step): other

### Examples/ElGamal.lean (I-ok)

numstat: +2 -1

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 1 (elgamal_indcpa_le_ddh L255).

Keeps `public import CatCryptCore.Tactics.AutoMetrics` for a frozen `sum_atoms_le`.

Failures:

- elgamal_real₀_eq L187 (whole): SPComp equality
- elgamal_real₀_eq L188 (step): SPComp equality
- elgamal_real₁_eq L196 (whole): SPComp equality
- elgamal_real₁_eq L197 (step): SPComp equality
- mask_absorb L206 (whole): SPComp equality
- mask_absorb L207 (step): SPComp equality
- elgamal_indcpa_le_ddh L233 (whole): other
- elgamal_indcpa_le_ddh L238 (step): other
- elgamal_indcpa_le_ddh L239 (step): other
- elgamal_indcpa_le_ddh L243 (step): other
- elgamal_indcpa_le_ddh L245 (step): distance inequality
- elgamal_indcpa_le_ddh L252 (step): distance inequality
- elgamal_indcpa_eq_ddh L282 (whole): other
- elgamal_indcpa_eq_ddh L283 (step): other
- elgamal_indcpa_eq_ddh L284 (step): other

### Examples/ElGamalUCConcrete.lean (I-ok)

numstat: +0 -0 (unchanged)

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 0.

Failures:

- elgamalReal_isPure L60 (whole): IsPure/NoFail side condition
- elgamal_uc_concrete_apply L97 (whole): other

### Examples/EncryptThenMAC.lean (I-ok)

numstat: +0 -0 (unchanged)

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 0.

Failures:

- boolEtM_indcpa_game_eq L157 (whole): SPComp equality
- boolEtM_indcpa_game_eq L158 (step): SPComp equality
- boolEtM_indcpa_coupling L171 (whole): relational rHoare judgment
- boolEtM_indcpa_coupling L172 (step): relational rHoare judgment
- boolEtM_perfect_indcpa L181 (whole): other

### Examples/EtMCCA.lean (I-ok)

numstat: +0 -0 (unchanged)

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 0.

Failures:

- boolEtM_indcca_reduces L91 (whole): distance inequality

### Examples/HashedElGamal.lean (I-ok)

numstat: +5 -5

Theorems closed whole by one frozen suggestion: heg_real_eq_ddh_real.

Closing steps replaced: 4 (heg_real_bind_eq L163; ddh_real_bind_red_eq L178; heg_indcpa_le_ddh L226; heg_indcpa_le_ddh L228).

Failures:

- heg_real_bind_eq L156 (whole): SPComp equality
- heg_real_bind_eq L158 (step): SPComp equality
- heg_real_bind_eq L160 (step): SPComp equality
- ddh_real_bind_red_eq L171 (whole): SPComp equality
- ddh_real_bind_red_eq L173 (step): SPComp equality
- heg_ideal_mask_indep L243 (whole): SPComp equality
- heg_perfect_hash_security L266 (whole): other

### Examples/INDCPA.lean (I-ok)

numstat: +0 -0 (unchanged)

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 0.

Failures:

- perfect_indcpa_zero_advantage L94 (whole): other

### Examples/KEMDEM.lean (I-ok)

numstat: +11 -10

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 10 (pke_security L567; pke_real_eq_hybrid1 L613; pke_real_eq_hybrid1 L619; pke_real_eq_hybrid1 L620; hybrid1_eq_hybrid2 L648; hybrid1_eq_hybrid2 L657; hybrid1_eq_hybrid2 L661; hybrid2_eq_pke_ideal L690; hybrid2_eq_pke_ideal L697; hybrid2_eq_pke_ideal L698).

Keeps `public import CatCryptCore.Tactics.AutoMetrics` for a frozen `hop_chain`.

Failures:

- pke_real_eq_kem_real_bind L451 (whole): SPComp equality
- hybrid1_eq_dem_real_bind L468 (whole): SPComp equality
- hybrid1_eq_dem_real_bind L471 (step): other
- hybrid1_eq_dem_real_bind L480 (step): other
- hybrid1_eq_dem_real_bind L483 (step): harness
- hybrid1_eq_dem_real_bind L484 (step): other
- hybrid2_eq_dem_ideal_bind L489 (whole): SPComp equality
- hybrid2_eq_dem_ideal_bind L492 (step): other
- hybrid2_eq_dem_ideal_bind L501 (step): other
- hybrid2_eq_dem_ideal_bind L504 (step): harness
- hybrid2_eq_dem_ideal_bind L505 (step): other
- hybrid2_eq_kem_ideal_bind2 L510 (whole): SPComp equality
- pke_ideal_eq_kem_real_bind2 L517 (whole): SPComp equality
- pke_security L546 (whole): other
- pke_security L550 (step): other
- pke_security L554 (step): other
- pke_real_eq_hybrid1 L602 (whole): relational rHoare judgment
- pke_real_eq_hybrid1 L604 (step): other
- pke_real_eq_hybrid1 L611 (step): other
- pke_real_eq_hybrid1 L612 (step): other
- pke_real_eq_hybrid1 L617 (step): other
- pke_real_eq_hybrid1 L618 (step): other
- pke_real_eq_hybrid1 L623 (step): other
- hybrid1_eq_hybrid2 L635 (whole): relational rHoare judgment
- hybrid1_eq_hybrid2 L637 (step): other
- hybrid1_eq_hybrid2 L646 (step): other
- hybrid1_eq_hybrid2 L647 (step): other
- hybrid1_eq_hybrid2 L655 (step): other
- hybrid1_eq_hybrid2 L656 (step): other
- hybrid1_eq_hybrid2 L660 (step): other
- hybrid1_eq_hybrid2 L664 (step): other
- hybrid2_eq_pke_ideal L676 (whole): relational rHoare judgment
- hybrid2_eq_pke_ideal L678 (step): other
- hybrid2_eq_pke_ideal L682 (step): other
- hybrid2_eq_pke_ideal L688 (step): other
- hybrid2_eq_pke_ideal L689 (step): other
- hybrid2_eq_pke_ideal L695 (step): other
- hybrid2_eq_pke_ideal L696 (step): other
- hybrid2_eq_pke_ideal L701 (step): other
- xorHybrid_advantage_zero L774 (whole): other

### Examples/OneTimePad.lean

numstat: +1 -2

Theorems closed whole by one frozen suggestion: otpGameRaw_eval.

Closing steps replaced: 0.

Failures:

- otp_indcpa_coupling L109 (step): relational rHoare judgment
- otp_perfect_indcpa L116 (whole): other
- otpGameRaw_eval_eq L155 (whole): SPComp equality
- otpGameRaw_eval_eq L156 (step): SPComp equality
- otp_deepnom_zero L190 (whole): other
- otp_sdist_zero L205 (whole): other
- otp_uc L216 (whole): other
- otp_deepnom_forward_eq_indcpa L226 (whole): other

### Examples/OT.lean

numstat: +1 -1

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 1 (advantageA_sample_bind_le_of_eq_off L429).

Golf: `(gcongr; grind [mul_le_of_le_one_right'])` written without parentheses.

Failures:

- ot_real_isPure L225 (whole): IsPure/NoFail side condition
- ot_ideal_isPure L234 (whole): IsPure/NoFail side condition
- advantageA_sample_bind_le_of_eq_off L416 (whole): distance inequality
- advantageA_sample_bind_le_of_eq_off L418 (step): distance inequality
- ot_sender_secure L450 (whole): distance inequality
- ot_sender_secure L459 (step): SPComp equality
- ot_sender_secure L461 (step): SPComp equality
- reduction_real_eq_receiver L500 (whole): SPComp equality
- reduction_real_eq_receiver L502 (step): SPComp equality
- receiver_ideal_indep L507 (whole): SPComp equality
- receiver_ideal_indep L509 (step): SPComp equality
- receiver_security L520 (whole): distance inequality
- receiver_security L535 (step): other

### Examples/PKE/MultiInstance.lean (I-ok)

numstat: +4 -8

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 3 (MI_sampleN_isPure L172; MI_hybridLoop_decomp_ideal_gen L198; MI_step_eq L282).

Golf: the 5-line terminal `calc` in `Adv_MI_MT_CPA` replaced by `grind [MI_hybrid, MI_step_bound]`.

Failures:

- MI_sampleN_isPure L170 (whole): harness
- MI_sampleN_isPure L171 (step): SPComp equality
- MI_sampleN_isPure L175 (step): SPComp equality
- MI_hybridLoop_decomp_ideal_gen L196 (whole): harness
- MI_hybridLoop_decomp_ideal_gen L197 (step): SPComp equality
- MI_hybridLoop_decomp_ideal_gen L201 (step): SPComp equality
- MI_hybridLoop_decomp_real L214 (whole): SPComp equality
- MI_hybridLoop_decomp_real L215 (step): SPComp equality
- MI_hybridLoop_decomp_ideal L224 (whole): SPComp equality
- MI_hybridLoop_decomp_ideal L225 (step): SPComp equality
- MI_step_eq L244 (whole): other
- MI_step_eq L256 (step): SPComp equality
- MI_step_eq L272 (step): SPComp equality
- MI_step_bound L289 (whole): distance inequality
- Adv_MI_MT_CPA L300 (whole): other
- Adv_MI_direct L315 (whole): other
- Adv_MI_MT_CPA_nested L326 (whole): other

### Examples/PKE/OneToMany.lean (I-ok)

numstat: +3 -6

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 2 (dHybrid_step_eq L236; MT_CPA_perfect L298).

Golf: the 4-line terminal `calc` in `Adv_MT_CPA_OT` replaced by `grind [dHybrid_step_bound]`.

Failures:

- sampleN_isPure L158 (whole): harness
- sampleN_isPure L160 (step): SPComp equality
- hybridLoop_decomp_samp L179 (whole): harness
- hybridLoop_decomp_samp L181 (step): SPComp equality
- dHybrid_step_eq L219 (step): SPComp equality
- dHybrid_step_eq L229 (step): SPComp equality
- dHybrid_step_bound L244 (whole): distance inequality
- dHybrid_step_bound' L251 (whole): distance inequality
- Adv_MT_CPA_OT L265 (whole): other
- Adv_MT_CPA_direct L284 (whole): other
- MT_CPA_perfect L295 (whole): other

### Examples/PKE/Scheme.lean (I-ok)

numstat: +1 -1

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: 1 (MT_CPA_perfect L340).

Failures:

- MT_CPA_real_isPure L296 (whole): IsPure/NoFail side condition
- MT_CPA_bound L312 (whole): other
- MT_CPA_dep_bound L324 (whole): other
- MT_CPA_perfect L337 (whole): other

### Examples/PRF.lean (I-ok)

numstat: +4 -6

Theorems closed whole by one frozen suggestion: bijPRF_adv_zero_via_vcgen, cascade_prf_bound.

Closing steps replaced: 1 (cascade_prf_perfect L221).

Keeps `public import CatCryptCore.Tactics.AutoMetrics` for a frozen `hop_chain` (`cascade_prf_bound`).

Golf: `(unfold CatCrypt.Examples.PRF.birthdayTerm; simp_all)` written as `unfold birthdayTerm; simp_all`.

Failures:

- bijPRF_coupling L107 (whole): relational rHoare judgment
- bijPRF_coupling L108 (step): relational rHoare judgment
- bijPRF_perfect L115 (whole): other
- boolXorPRF_perfect L133 (whole): other
- cascade_prf_bound_of_assumption L206 (whole): distance inequality
- cascade_prf_perfect L220 (whole): other
- cascade_prf_perfect L222 (step): other

### Examples/PRFMAC.lean (I-ok)

numstat: +9 -9

Theorems closed whole by one frozen suggestion: none (the suggestion for `hop1_equiv` replaced `rfl` and was not kept).

Closing steps replaced: 9 (prf_uniform L276; forgery_diff_message_uniform L337; mac_same_message_coupling L396; macIdeal_diff_eq_pure_false L411; prTrue_pure_empty L421; prTrue_pure_empty L423; not_rHoare_macReal_macIdeal_of_ne L447; not_rHoare_macReal_macIdeal_of_ne L451; security_based_on_prf L527).

Golf trial stopped: the `grind` replacement of the 6-line `calc` in `not_rHoare_macReal_macIdeal_of_ne` hit the 200000-heartbeat limit and the next trial did not return within 30 min; the process was killed and no golf was applied to this file.

Failures:

- prf_uniform L263 (whole): relational rHoare judgment
- prf_uniform L265 (step): other
- prf_uniform L268 (step): other
- forgery_diff_message_uniform L312 (whole): relational rHoare judgment
- forgery_diff_message_uniform L314 (step): other
- forgery_diff_message_uniform L318 (step): other
- mac_same_message_coupling L388 (step): other
- mac_same_message_coupling L391 (step): other
- macIdeal_diff_eq_pure_false L405 (whole): SPComp equality
- macIdeal_diff_eq_pure_false L409 (step): other
- prTrue_pure_empty L415 (whole): other
- prTrue_pure_empty L417 (step): other
- not_rHoare_macReal_macIdeal_of_ne L431 (whole): other
- security_based_on_prf L517 (whole): other

## Files in the vacuity-sweep list

Examples/Cryptobox/** is on the vacuity-sweep list. Only proofs were edited in these files, and
no statement was changed:

- `Examples/Cryptobox/GameHopping.lean`
- `Examples/Cryptobox/HYBRID.lean`
- `Examples/Cryptobox/PKEY.lean`

The other Cryptobox files in scope (KEY, NIKE, PKAE, SAE) are unchanged. No file under
`Crypto/BadEvent.lean`, `Crypto/UCAdmClass*.lean`, `Crypto/KeyAgreement/**` or
`CatCryptCore/Consensus/**` was touched.

## Skipped

- `Examples/DetCPA.lean`: step 1 skipped. The module is in the import closure of
  `AutoDispatchExt`, so adding the import gives duplicate declarations.
- `Examples/Cryptobox/KEY.lean`, `NIKE.lean`, `PKAE.lean`, `SAE.lean`: no theorems.
- `Examples/CyclicGroupDDH.lean`: no theorem matching the selection.
- No change was found for these files: `Examples/CTRMode.lean`,
  `Examples/ElGamalUCConcrete.lean`, `Examples/EncryptThenMAC.lean`, `Examples/EtMCCA.lean`,
  `Examples/INDCPA.lean`.

## Interface queue

1. `CatCryptCore/Unary/ExpectationVCGen.lean` imports `CatCryptCore.Examples.DetCPA`.
   - Effect: a library module depends on an example, and `Examples/DetCPA.lean` cannot import
     the `AutoDispatchExt` chain.
   - Possible change: move what `ExpectationVCGen` uses from `DetCPA` into a non-example module.
2. Suggestions that close a goal with `catcrypt_grind` do not elaborate without `AutoSets`.
   - Workaround in this pass: plain `grind` with the same arguments was used where it closed the
     goal.
   - Where it did not close the goal, the suggestion could not be frozen.
3. Some suggestions are frozen with arguments that the linter then reports as unused or
   redundant. The arguments were taken from the old proof.
   - Example: `grind [advantage_triangle]`, where `advantage_triangle` is already `@[grind .]`.
   - Possible change: have `catcrypt_auto?` drop such arguments from the suggestion.
4. Some suggestions spell out fully qualified names inside `unfold`, or wrap a single sequence
   in parentheses. These were shortened by hand.
5. For a goal closed by `rfl`, the suggestion was `(simp only [SPComp.monad_bind_eq]; bind_vcgen)`
   (`hop1_equiv`, PRFMAC).
   - Possible change: the dispatcher could try `rfl` first on `SPComp equality` goals.
6. Most failures are of the shapes `SPComp equality` and `relational rHoare judgment`, and on
   `ℝ≥0∞` bounds that need instantiated hypotheses (`other`, `distance inequality`).
7. `lean-query.py multi` does not print info messages, so the "Try this" text is invisible to
   it. A `diag` call shows it, but each call elaborates the whole file again.

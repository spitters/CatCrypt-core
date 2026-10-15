# AUTO_CORPUS_5 report

Branch `work/auto-corpus-5`, created from `origin/work/auto-corpus` (751637d). Toolchain Lean 4.33.1, cache tag 725a07d3aa79; `cloud-setup.sh` exited 0 (it reported no prebuilt build for the `iris` package, which no module of this pass imports). No `lake build` printed `Built Mathlib.`.

## Method

- Candidates: theorems whose elaborated statement contains `rHoare`, `Advantage`, `AdvantageA`, `sdist`, `prTrue`, `prEvent`, `SPComp.IsPure`, `SPComp.NoFail` or an equality at type `SPComp _`, either directly or in the value of a CatCryptCore definition the statement mentions (one unfolding level). The classification ran in Lean on the elaborated declarations.
- Whole-proof trials: every candidate proof was replaced by `catcrypt_auto? [args]`, with `args` the lemmas, definitions and statement hypotheses that the old proof cites (for term proofs, every non-local identifier of the term), under the temporary import `CatCryptCore.Tactics.AutoDispatchExt`, all candidates of a file in one elaboration (`lake env lean --json`).
- Closing-step trials: for candidates not closed whole, the last tactic of each branch (top level, bullets, `case`/alternative blocks, nested `by` blocks) and each `calc` step proof were replaced by `catcrypt_auto? [args]`, with `args` the identifiers of the replaced step and, for `exact t`/`apply t`/`simpa using t`, the term `t` itself.
- Freezing: a suggestion was pasted when it closed the theorem (whole) or, for a step, when it had no more lines than the step it replaces, differs from it, and does not merely re-run the original step or term (for example `(unfold d; exact t)` or `grind [t]` for `exact t`). The file was then elaborated without the temporary import; any suggestion with an error or a new warning in its lines was reverted and the elaboration repeated. In files marked (I-ok), suggestions using `hop_chain`, `sum_atoms_le` or `gcongr_unfold` were kept with `public import CatCryptCore.Tactics.AutoMetrics`; in the other files they were not used.
- Golf: unused `simp` arguments flagged by the linter, `rw [..]` followed by a closing `simp [..]` (merged into one `simp [..]`), and `calc` blocks ending a branch (tried as `gcongr`, `linarith`, `grind`), each kept only if the file elaborates with no error or new warning. No site of these kinds survived in the processed files. Separately, a frozen suggestion whose only complaint was the unused-simp-argument linter was kept with the flagged arguments removed (NonUniform/Bernoulli 1, NonUniform/WhileRelationalLimit 1).
- Deprecations: no deprecation warning occurs in any of the 27 files.
- Each changed module was built with `lake build CatCryptCore.<Module>`; finally all 27 modules were built together (2813 jobs, success). The warnings of the 27 files are the same as on the base branch: Bernoulli 1, CenteredBinomial 1, CouplingRules 6 (unused variable names), Relational/Rules 5 (unused simp arguments); none is new.

Line numbers below refer to the files on `origin/work/auto-corpus`.

## Per file

### Examples/PRFPRG (I-ok)

- numstat: +7 -6
- declarations parsed: 18; candidates: 18; whole-proof suggestions: 8; closing-step targets: 13, with suggestion: 8
- keeps `public import CatCryptCore.Tactics.AutoMetrics` (frozen suggestion uses `hop_chain` or `sum_atoms_le`)
- theorems closed whole by one frozen suggestion: 5
  - `gen_hyb_zero_eq_real`: `bind_vcgen`
  - `gen_hyb_two_eq_ideal`: `bind_vcgen`
  - `gen_hyb_2_independent_of_F`: `bind_vcgen`
  - `gen_hyb_decomp_1_eq_hyb_1`: `bind_vcgen`
  - `gen_hyb_decomp_2_eq_hyb_2`: `bind_vcgen`
- closing steps replaced: 1
  - `prg_decomp_security_bound` line 715: `exact add_le_add h0 le_rfl` -> `sum_atoms_le`
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 5
  - `hyb_0_eq_real`: `catcrypt_grind [gen_hyb_zero_eq_real]` (unknown tactic)
  - `hyb_2_eq_ideal`: `catcrypt_grind [gen_hyb_two_eq_ideal]` (unknown tactic)
  - `gen_hyb_decomp_2_eq_ideal`: `catcrypt_grind [gen_hyb_decomp_2_eq_hyb_2, gen_hyb_two_eq_ideal]` (unknown tactic)
  - `decomp_hyb_adjacent_bound`: `catcrypt_grind [hyb2_eq_eval_ideal_wrap A, hyb2_eq_eval_ideal_wrap]` (unknown tactic)
  - `prg_decomp_security_bound`: `(gcongr <;> catcrypt_grind [add_le_add le_rfl h1, add_le_add])` (unknown tactic)

### Examples/PRG (I-ok)

- numstat: +12 -12
- declarations parsed: 12; candidates: 12; whole-proof suggestions: 7; closing-step targets: 3, with suggestion: 0
- keeps `public import CatCryptCore.Tactics.AutoMetrics` (frozen suggestion uses `hop_chain` or `sum_atoms_le`)
- theorems closed whole by one frozen suggestion: 7
  - `bijPRG_perfect`: `grind [PRG_Adv_zero_of_rHoare, bijPRG_coupling]`
  - `boolXorPRG_perfect`: `grind [bijPRG_perfect, boolXorPRG]`
  - `PRGAssumption.advantage_bound`: `grind [H.bound]`
  - `bijPRG_adv_zero_via_vcgen`: `simp_all [PRG_Adv, AdvantageA, bijPRG_game_eq, Advantage_self]`
  - `DoublePRG.hyb_2_ideal`: `(simp only [CatCrypt.Core.SPComp.monad_bind_eq]; bind_vcgen)`
  - `triple_prg_hybrid_bound`: `hop_chain`
  - `triple_prg_uniform_bound`: `hop_chain`
- closing steps replaced: 0

### Examples/SecretSharing (I-ok)

- numstat: +5 -7
- declarations parsed: 11; candidates: 9; whole-proof suggestions: 4; closing-step targets: 2, with suggestion: 0
- theorems closed whole by one frozen suggestion: 3
  - `ss_perfect_privacy`: `(unfold CatCrypt.Examples.SecretSharing.SS_Privacy_Adv; grind [advantage_zero_of_rHoare, ss_privacy_coupling])`
  - `ssGameRaw_eval_shallow`: `bind_vcgen`
  - `ss_deepnom_forward_eq_adv`: `grind [runPkg_link_forward, ssGameRaw, ssGameRaw_eval_shallow, SS_Privacy_Adv, AdvantageA_pure, DeepNomAdvantage, ssGameTrue, ssGameFalse]`
- closing steps replaced: 0
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 1
  - `ss_game_isPure`: `(unfold CatCrypt.Examples.SecretSharing.SS_Privacy_Game; simp only [CatCrypt.Core.SPComp.monad_bind_eq]; aesop` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)

### Examples/ShamirSecretSharing (I-ok)

- numstat: +3 -3
- declarations parsed: 22; candidates: 8; whole-proof suggestions: 3; closing-step targets: 2, with suggestion: 1
- theorems closed whole by one frozen suggestion: 2
  - `shamir_perfect_privacy`: `(unfold CatCrypt.Examples.ShamirSecretSharing.PrivAdv; grind [advantage_zero_of_rHoare, priv_coupling])`
  - `shamirGameRaw_eval_shallow`: `bind_vcgen`
- closing steps replaced: 0
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 1
  - `shamir_game_isPure`: `(unfold CatCrypt.Examples.ShamirSecretSharing.PrivGame; simp only [CatCrypt.Core.SPComp.monad_bind_eq]; aesop ` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)

### Examples/Sigma

- numstat: +0 -0
- declarations parsed: 8; candidates: 2; whole-proof suggestions: 0; closing-step targets: 2, with suggestion: 0
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### Examples/SigmaProtocol (I-ok)

- numstat: +0 -0
- declarations parsed: 8; candidates: 3; whole-proof suggestions: 0; closing-step targets: 1, with suggestion: 0
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### Examples/UniversalHash (I-ok)

- numstat: +0 -0
- declarations parsed: 10; candidates: 7; whole-proof suggestions: 2; closing-step targets: 2, with suggestion: 0
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 2
  - `uh_forge_real_isPure`: `(unfold CatCryptCore.Examples.UniversalHash.uh_forge_real; simp only [CatCrypt.Core.SPComp.monad_bind_eq]; aes` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)
  - `uh_forge_ideal_isPure`: `(unfold CatCryptCore.Examples.UniversalHash.uh_forge_ideal; aesop (rule_sets := [CatCryptRel]) (config := { te` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)

### Invariant/EqUpToInv

- numstat: +0 -0
- declarations parsed: 1; candidates: 1; whole-proof suggestions: 0; closing-step targets: 0, with suggestion: 0
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### Invariant

- numstat: +0 -0
- declarations parsed: 0; candidates: 0; whole-proof suggestions: 0; closing-step targets: 0, with suggestion: 0
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### NonUniform/Bernoulli (I-ok)

- numstat: +2 -3
- declarations parsed: 19; candidates: 5; whole-proof suggestions: 2; closing-step targets: 1, with suggestion: 1
- theorems closed whole by one frozen suggestion: 2
  - `prTrue_bernoulli_bind`: `simp_all [prTrue_bind_sampleFrom, tsum_fintype, bernoulli_apply_true, bernoulli_apply_false]` (unused simp argument of the suggestion removed)
  - `prTrue_bernoulli`: `simp_all [prTrue_sampleFrom, bernoulli_apply_true]`
- closing steps replaced: 0

### NonUniform/CenteredBinomial

- numstat: +2 -2
- declarations parsed: 17; candidates: 4; whole-proof suggestions: 2; closing-step targets: 0, with suggestion: 0
- theorems closed whole by one frozen suggestion: 1
  - `prTrue_cbd_bind`: `grind [prTrue_bind_sampleFrom, cbd]`
- closing steps replaced: 0
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 1
  - `rHoare_cbd_sign`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe rHoare_coupling_step, unsafe l` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)

### NonUniform/CouplingRules

- numstat: +0 -0
- declarations parsed: 11; candidates: 9; whole-proof suggestions: 1; closing-step targets: 2, with suggestion: 2
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 1
  - `rHoare_sampleFrom_same`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe hk, unsafe rHoare_coupling_ste` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)

### NonUniform (I-ok)

- numstat: +0 -0
- declarations parsed: 0; candidates: 0; whole-proof suggestions: 0; closing-step targets: 0, with suggestion: 0
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### NonUniform/Sample

- numstat: +1 -1
- declarations parsed: 19; candidates: 7; whole-proof suggestions: 2; closing-step targets: 1, with suggestion: 1
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 1
  - `sampleFrom_bind_sampleFrom` line 90: `simp only [sampleFrom_bind_apply, sampleFrom_apply, SDistr.bind_assoc]` -> `simp_all [sampleFrom_bind_apply, sampleFrom_apply, SDistr.bind_assoc]`
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 2
  - `sampleFrom_uniform`: `bind_vcgen` (unknown tactic)
  - `sampleFrom_eq_liftSDistr`: `bind_vcgen` (unknown tactic)

### NonUniform/WhileRelational (I-ok)

- numstat: +0 -0
- declarations parsed: 5; candidates: 5; whole-proof suggestions: 3; closing-step targets: 4, with suggestion: 2
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 3
  - `rHoare_fail_fail`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe liftR_fail)` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)
  - `rHoare_whileApprox_zero`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe rHoare_fail_fail)` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)
  - `rHoare_whileApprox_same`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe hguard, unsafe hbody, unsafe r` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)

### NonUniform/WhileRelationalLimit (I-ok)

- numstat: +8 -16
- declarations parsed: 16; candidates: 10; whole-proof suggestions: 4; closing-step targets: 17, with suggestion: 13
- theorems closed whole by one frozen suggestion: 3
  - `exists_loopJoint_ne_zero`: `simp_all [loopJointLim, mlim_apply_some]` (unused simp argument of the suggestion removed)
  - `loopJointLim_bind_fst`: `grind [loopJointLim, mlim_bind, mlim_apply_some, whileLoop_apply_some, loopJoint_bind_fst, iSup_congr]`
  - `loopJointLim_bind_snd`: `grind [loopJointLim, mlim_bind, mlim_apply_some, whileLoop_apply_some, loopJoint_bind_snd, iSup_congr]`
- closing steps replaced: 5
  - `loopJoint_bind_fst` line 201: `rw [← hguard h₁ h₂ hI]; exact hg₁` -> `grind`
  - `loopJoint_bind_snd` line 230: `rw [← hguard h₁ h₂ hI]; exact hg₁` -> `grind`
  - `loopJoint_bind_snd` line 235: `rw [← hguard h₁ h₂ hI]; exact hg₁` -> `grind`
  - `loopJoint_support` line 266: `rw [← hguard h₁ h₂ hI]; exact hg₁` -> `grind`
  - `loopJoint_support` line 276: `rw [← hguard h₁ h₂ hI]; exact hg₁` -> `grind`
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 1
  - `rHoare_whileLoop_same`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe hguard, unsafe hbody, unsafe r` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)

### Prob/BirthdayBound

- numstat: +0 -0
- declarations parsed: 10; candidates: 2; whole-proof suggestions: 0; closing-step targets: 1, with suggestion: 0
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### Prob/SchwartzZippel (I-ok)

- numstat: +2 -2
- declarations parsed: 2; candidates: 2; whole-proof suggestions: 0; closing-step targets: 5, with suggestion: 5
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 2
  - `poly_identity_test` line 116: `rw [sub_eq_add_neg]` -> `simp_all [sub_eq_add_neg]`
  - `poly_identity_test` line 118: `rw [natDegree_neg]` -> `simp_all [natDegree_neg]`

### Prob/XorBij

- numstat: +1 -1
- declarations parsed: 11; candidates: 5; whole-proof suggestions: 0; closing-step targets: 1, with suggestion: 1
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 1
  - `rHoare_sample_bij` line 121: `grind` -> `simp_all`

### Relational/Approx

- numstat: +0 -0
- Skipped steps 1 and 2: adding `public import CatCryptCore.Tactics.AutoDispatchExt` makes `lake build` report `build cycle detected` (the module is in the import closure of AutoDispatchExt). Step 3: no deprecation warnings. Module builds unchanged.

### Relational/ForLoop

- numstat: +0 -0
- declarations parsed: 7; candidates: 7; whole-proof suggestions: 0; closing-step targets: 12, with suggestion: 8
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### Relational/Frame

- numstat: +0 -0
- declarations parsed: 14; candidates: 3; whole-proof suggestions: 0; closing-step targets: 7, with suggestion: 6
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### Relational/Judgment

- numstat: +0 -0
- Skipped steps 1 and 2: adding `public import CatCryptCore.Tactics.AutoDispatchExt` makes `lake build` report `build cycle detected` (the module is in the import closure of AutoDispatchExt). Step 3: no deprecation warnings. Module builds unchanged.

### Relational/Reorder

- numstat: +0 -0
- declarations parsed: 6; candidates: 6; whole-proof suggestions: 0; closing-step targets: 6, with suggestion: 3
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0

### Relational/Rules

- numstat: +0 -0
- Skipped steps 1 and 2: adding `public import CatCryptCore.Tactics.AutoDispatchExt` makes `lake build` report `build cycle detected` (the module is in the import closure of AutoDispatchExt). Step 3: no deprecation warnings. Module builds unchanged.

### Relational/Separation (I-ok)

- numstat: +0 -0
- declarations parsed: 45; candidates: 7; whole-proof suggestions: 1; closing-step targets: 4, with suggestion: 3
- theorems closed whole by one frozen suggestion: 0
- closing steps replaced: 0
- suggestions not frozen (an error or a new warning in their lines without the temporary import): 1
  - `r_frame_set_sync_eqPre`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe r_frame_set_sync, unsafe l, un` (no such rule set: 'CatCryptRel' (Use 'declare_aesop_rule_set' to declare rule se)

### Relational/SpanLifting

- numstat: +0 -0
- Skipped steps 1 and 2: adding `public import CatCryptCore.Tactics.AutoDispatchExt` makes `lake build` report `build cycle detected` (the module is in the import closure of AutoDispatchExt). Step 3: no deprecation warnings. Module builds unchanged.

## Totals

- theorems closed whole by one frozen suggestion: 23
- closing steps replaced: 10
- positions where `catcrypt_auto?` failed: 125

## Positions where catcrypt_auto? failed

One line each: file, line, theorem, position, goal shape named by the error.

- Examples/PRFPRG:241 `xorPRF_eval_coupling` (whole proof): relational rHoare judgment
- Examples/PRFPRG:247 `xorPRF_zero_advantage` (whole proof): other
- Examples/PRFPRG:283 `xorPRF_hyb_1_coupling` (whole proof): relational rHoare judgment
- Examples/PRFPRG:323 `xorPRF_hyb_1_to_2_zero_advantage` (whole proof): other
- Examples/PRFPRG:405 `hyb1_eq_eval_real_wrap` (whole proof): SPComp equality
- Examples/PRFPRG:450 `hyb2_eq_eval_ideal_wrap` (whole proof): SPComp equality
- Examples/PRFPRG:578 `decomp_hyb0_eq_eval_real_wrap_fst` (whole proof): SPComp equality
- Examples/PRFPRG:591 `decomp_hyb1_eq_eval_ideal_wrap_fst` (whole proof): SPComp equality
- Examples/PRFPRG:620 `decomp_hyb_adjacent_bound` (whole proof): distance inequality
- Examples/PRFPRG:699 `prg_decomp_security_bound` (whole proof): distance inequality
- Examples/PRFPRG:243 `xorPRF_eval_coupling` (closing step): relational rHoare judgment
- Examples/PRFPRG:433 `hyb1_eq_eval_real_wrap` (closing step): other
- Examples/PRFPRG:468 `hyb2_eq_eval_ideal_wrap` (closing step): other
- Examples/PRFPRG:585 `decomp_hyb0_eq_eval_real_wrap_fst` (closing step): other
- Examples/PRFPRG:597 `decomp_hyb1_eq_eval_ideal_wrap_fst` (closing step): other
- Examples/PRG:114 `PRG_Adv_zero_of_rHoare` (whole proof): other
- Examples/PRG:155 `bijPRG_coupling` (whole proof): relational rHoare judgment
- Examples/PRG:227 `bijPRG_game_eq` (whole proof): SPComp equality
- Examples/PRG:372 `triple_prg_bound_of_assumption` (whole proof): distance inequality
- Examples/PRG:384 `triple_prg_perfect` (whole proof): other
- Examples/PRG:157 `bijPRG_coupling` (closing step): relational rHoare judgment
- Examples/PRG:230 `bijPRG_game_eq` (closing step): SPComp equality
- Examples/PRG:385 `triple_prg_perfect` (closing step): other
- Examples/SecretSharing:130 `ss_privacy_coupling` (whole proof): relational rHoare judgment
- Examples/SecretSharing:178 `ssGameRaw_eval_eq` (whole proof): SPComp equality
- Examples/SecretSharing:193 `ss_deepnom_zero` (whole proof): other
- Examples/SecretSharing:199 `ss_sdist_zero` (whole proof): other
- Examples/SecretSharing:215 `ss_uc` (whole proof): other
- Examples/SecretSharing:134 `ss_privacy_coupling` (closing step): other
- Examples/SecretSharing:180 `ssGameRaw_eval_eq` (closing step): SPComp equality
- Examples/ShamirSecretSharing:195 `priv_coupling` (whole proof): relational rHoare judgment
- Examples/ShamirSecretSharing:262 `shamirGameRaw_eval_eq` (whole proof): SPComp equality
- Examples/ShamirSecretSharing:278 `shamir_deepnom_zero` (whole proof): other
- Examples/ShamirSecretSharing:284 `shamir_sdist_zero` (whole proof): other
- Examples/ShamirSecretSharing:300 `shamir_uc` (whole proof): other
- Examples/ShamirSecretSharing:264 `shamirGameRaw_eval_eq` (closing step): SPComp equality
- Examples/Sigma:403 `simpleSigma_shvzk_given` (whole proof): other
- Examples/Sigma:418 `simpleSigma_shvzk` (whole proof): other
- Examples/Sigma:409 `simpleSigma_shvzk_given` (closing step): relational rHoare judgment
- Examples/Sigma:426 `simpleSigma_shvzk` (closing step): relational rHoare judgment
- Examples/SigmaProtocol:247 `simpleSigma_shvzk` (whole proof): other
- Examples/SigmaProtocol:256 `simpleSigma_shvzk_zero_adv` (whole proof): other
- Examples/SigmaProtocol:281 `simpleSigma_hiding` (whole proof): relational rHoare judgment
- Examples/SigmaProtocol:251 `simpleSigma_shvzk` (closing step): relational rHoare judgment
- Examples/UniversalHash:127 `forge_prTrue_eq` (whole proof): other
- Examples/UniversalHash:150 `boolHash_forge_advantage` (whole proof): other
- Examples/UniversalHash:159 `boolPairwiseHash_mac_security` (whole proof): other
- Examples/UniversalHash:178 `collision_prTrue_eq` (whole proof): other
- Examples/UniversalHash:198 `boolPairwiseHash_is_universal` (whole proof): other
- Examples/UniversalHash:153 `boolHash_forge_advantage` (closing step): distance inequality
- Examples/UniversalHash:202 `boolPairwiseHash_is_universal` (closing step): distance inequality
- Invariant/EqUpToInv:69 `simplify_eq_rel_intro` (whole proof): other
- NonUniform/Bernoulli:122 `rHoare_bernoulli_flip` (whole proof): relational rHoare judgment
- NonUniform/Bernoulli:130 `bernoulli_flip_program_eq` (whole proof): SPComp equality
- NonUniform/Bernoulli:153 `prTrue_bernoulli_not` (whole proof): other
- NonUniform/CenteredBinomial:172 `cbd_signed_eq` (whole proof): SPComp equality
- NonUniform/CenteredBinomial:180 `cbd_signed_indep` (whole proof): SPComp equality
- NonUniform/CouplingRules:108 `rHoare_coupling_step` (whole proof): relational rHoare judgment
- NonUniform/CouplingRules:118 `rHoare_coupling` (whole proof): relational rHoare judgment
- NonUniform/CouplingRules:142 `rHoare_bij_step_of_coupling` (whole proof): relational rHoare judgment
- NonUniform/CouplingRules:154 `rHoare_same_step_of_coupling` (whole proof): relational rHoare judgment
- NonUniform/CouplingRules:169 `r_sample_vs_sample_coupling_of_coupling` (whole proof): relational rHoare judgment
- NonUniform/CouplingRules:188 `rHoare_sampleFrom_l` (whole proof): relational rHoare judgment
- NonUniform/CouplingRules:198 `rHoare_sampleFrom_r` (whole proof): relational rHoare judgment
- NonUniform/CouplingRules:209 `eq_of_rHoare_eqPost` (whole proof): other
- NonUniform/Sample:78 `sampleFrom_pure` (whole proof): SPComp equality
- NonUniform/Sample:83 `sampleFrom_fail` (whole proof): SPComp equality
- NonUniform/Sample:88 `sampleFrom_bind_sampleFrom` (whole proof): SPComp equality
- NonUniform/Sample:93 `sampleFrom_isPure` (whole proof): IsPure/NoFail side condition
- NonUniform/Sample:139 `dead_sampleFrom` (whole proof): SPComp equality
- NonUniform/WhileRelational:79 `rHoare_whileApprox_step` (whole proof): relational rHoare judgment
- NonUniform/WhileRelational:99 `rHoare_whileApprox` (whole proof): relational rHoare judgment
- NonUniform/WhileRelational:108 `rHoare_whileApprox` (closing step): other
- NonUniform/WhileRelational:112 `rHoare_whileApprox` (closing step): other
- NonUniform/WhileRelationalLimit:150 `exists_bodyJoint` (whole proof): other
- NonUniform/WhileRelationalLimit:173 `bodyJoint_spec` (whole proof): other
- NonUniform/WhileRelationalLimit:186 `loopJoint_bind_fst` (whole proof): other
- NonUniform/WhileRelationalLimit:219 `loopJoint_bind_snd` (whole proof): other
- NonUniform/WhileRelationalLimit:255 `loopJoint_support` (whole proof): other
- NonUniform/WhileRelationalLimit:342 `rHoare_whileLoop` (whole proof): relational rHoare judgment
- NonUniform/WhileRelationalLimit:192 `loopJoint_bind_fst` (closing step): other
- NonUniform/WhileRelationalLimit:199 `loopJoint_bind_fst` (closing step): other
- NonUniform/WhileRelationalLimit:225 `loopJoint_bind_snd` (closing step): other
- NonUniform/WhileRelationalLimit:233 `loopJoint_bind_snd` (closing step): other
- Prob/BirthdayBound:124 `birthday_advantage` (whole proof): distance inequality
- Prob/BirthdayBound:137 `birthday_advantage_bound` (whole proof): distance inequality
- Prob/BirthdayBound:139 `birthday_advantage_bound` (closing step): distance inequality
- Prob/SchwartzZippel:62 `schwartz_zippel` (whole proof): distance inequality
- Prob/SchwartzZippel:101 `poly_identity_test` (whole proof): distance inequality
- Prob/XorBij:111 `rHoare_sample_bij` (whole proof): relational rHoare judgment
- Prob/XorBij:133 `rHoare_sample_xor` (whole proof): relational rHoare judgment
- Prob/XorBij:140 `rHoare_sample_prod_xor` (whole proof): relational rHoare judgment
- Prob/XorBij:150 `advantage_zero_of_bij` (whole proof): other
- Prob/XorBij:156 `advantage_zero_of_xor` (whole proof): other
- Relational/ForLoop:65 `mapM_isPure` (whole proof): IsPure/NoFail side condition
- Relational/ForLoop:77 `forM_isPure` (whole proof): IsPure/NoFail side condition
- Relational/ForLoop:88 `foldlM_isPure` (whole proof): IsPure/NoFail side condition
- Relational/ForLoop:116 `rHoare_forM` (whole proof): relational rHoare judgment
- Relational/ForLoop:129 `rHoare_forM_same` (whole proof): relational rHoare judgment
- Relational/ForLoop:150 `rHoare_foldlM` (whole proof): relational rHoare judgment
- Relational/ForLoop:168 `rHoare_foldlM_same` (whole proof): relational rHoare judgment
- Relational/ForLoop:70 `mapM_isPure` (closing step): IsPure/NoFail side condition
- Relational/ForLoop:81 `forM_isPure` (closing step): IsPure/NoFail side condition
- Relational/ForLoop:93 `foldlM_isPure` (closing step): IsPure/NoFail side condition
- Relational/ForLoop:156 `rHoare_foldlM` (closing step): relational rHoare judgment
- Relational/Frame:231 `r_frame_local` (whole proof): relational rHoare judgment
- Relational/Frame:287 `r_frame_of_preservesNothing` (whole proof): relational rHoare judgment
- Relational/Frame:314 `r_frame_agreeOff` (whole proof): relational rHoare judgment
- Relational/Frame:323 `r_frame_agreeOff` (closing step): other
- Relational/Reorder:51 `rHoare_reorder_pure_l` (whole proof): relational rHoare judgment
- Relational/Reorder:61 `rHoare_reorder_pure_r` (whole proof): relational rHoare judgment
- Relational/Reorder:87 `advantage_factorization_comm` (whole proof): other
- Relational/Reorder:114 `rHoare_sample_comm` (whole proof): relational rHoare judgment
- Relational/Reorder:148 `rHoare_sample_past_get_l` (whole proof): relational rHoare judgment
- Relational/Reorder:166 `rHoare_sample_past_set_l` (whole proof): relational rHoare judgment
- Relational/Reorder:131 `rHoare_sample_comm` (closing step): other
- Relational/Reorder:151 `rHoare_sample_past_get_l` (closing step): other
- Relational/Reorder:169 `rHoare_sample_past_set_l` (closing step): other
- Relational/Separation:338 `frameable_of_isPure` (whole proof): other
- Relational/Separation:443 `r_frame_sep` (whole proof): relational rHoare judgment
- Relational/Separation:470 `r_frame_sep_eqPre` (whole proof): relational rHoare judgment
- Relational/Separation:480 `r_frame_sep_agreeOff` (whole proof): relational rHoare judgment
- Relational/Separation:489 `rHoare_set_sync_owned` (whole proof): relational rHoare judgment
- Relational/Separation:497 `r_frame_set_sync` (whole proof): relational rHoare judgment
- Relational/Separation:492 `rHoare_set_sync_owned` (closing step): other

## Skipped files

- Relational/Approx, Relational/Judgment, Relational/Rules, Relational/SpanLifting: import cycle with `CatCryptCore.Tactics.AutoDispatchExt` (`lake build` reports `build cycle detected`); steps 1 and 2 skipped, step 3 found no deprecations; files unchanged.
- Files without changes after the pass (no suggestion survived the freezing rules, no golf site, no deprecation): Examples/Sigma, Examples/SigmaProtocol, Examples/UniversalHash, Invariant/EqUpToInv, Invariant, NonUniform/CouplingRules, NonUniform (no theorems), NonUniform/WhileRelational, Prob/BirthdayBound, Relational/ForLoop, Relational/Frame, Relational/Reorder, Relational/Separation. No commit was made for these.
- Vacuity-sweep files (Crypto/BadEvent.lean, Crypto/UCAdmClass*.lean, Examples/Cryptobox/**, Crypto/KeyAgreement/Curve25519.lean, Crypto/KeyAgreement/MontgomeryXOnly.lean): none is in this pass; none was edited. CatCryptCore/Consensus/** was not edited.

## Interface queue

- Imports that would help (not made; imports are fixed by the task). Suggestions that close the goal under the temporary import but fail without it because the tactic or the aesop rule set `CatCryptRel` is not imported by the module; the module that provides it is named:
  - Examples/PRFPRG `hyb_0_eq_real`: `catcrypt_grind [gen_hyb_zero_eq_real]` needs `CatCryptCore.Tactics.AutoSets`
  - Examples/PRFPRG `hyb_2_eq_ideal`: `catcrypt_grind [gen_hyb_two_eq_ideal]` needs `CatCryptCore.Tactics.AutoSets`
  - Examples/PRFPRG `gen_hyb_decomp_2_eq_ideal`: `catcrypt_grind [gen_hyb_decomp_2_eq_hyb_2, gen_hyb_two_eq_ideal]` needs `CatCryptCore.Tactics.AutoSets`
  - Examples/PRFPRG `decomp_hyb_adjacent_bound`: `catcrypt_grind [hyb2_eq_eval_ideal_wrap A, hyb2_eq_eval_ideal_wrap]` needs `CatCryptCore.Tactics.AutoSets`
  - Examples/PRFPRG `prg_decomp_security_bound`: `(gcongr <;> catcrypt_grind [add_le_add le_rfl h1, add_le_add])` needs `CatCryptCore.Tactics.AutoSets`
  - Examples/SecretSharing `ss_game_isPure`: `(unfold CatCrypt.Examples.SecretSharing.SS_Privacy_Game; simp only [CatCrypt.Core.SPComp.m` needs `CatCryptCore.Tactics.AutoSets`
  - Examples/ShamirSecretSharing `shamir_game_isPure`: `(unfold CatCrypt.Examples.ShamirSecretSharing.PrivGame; simp only [CatCrypt.Core.SPComp.mo` needs `CatCryptCore.Tactics.AutoSets`
  - Examples/UniversalHash `uh_forge_real_isPure`: `(unfold CatCryptCore.Examples.UniversalHash.uh_forge_real; simp only [CatCrypt.Core.SPComp` needs `CatCryptCore.Tactics.AutoSets`
  - Examples/UniversalHash `uh_forge_ideal_isPure`: `(unfold CatCryptCore.Examples.UniversalHash.uh_forge_ideal; aesop (rule_sets := [CatCryptR` needs `CatCryptCore.Tactics.AutoSets`
  - NonUniform/CenteredBinomial `rHoare_cbd_sign`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe rHoare_cou` needs `CatCryptCore.Tactics.AutoSets`
  - NonUniform/CouplingRules `rHoare_sampleFrom_same`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe hk, unsafe` needs `CatCryptCore.Tactics.AutoSets`
  - NonUniform/Sample `sampleFrom_uniform`: `bind_vcgen` needs `CatCryptCore.Tactics.BindVcgen`
  - NonUniform/Sample `sampleFrom_eq_liftSDistr`: `bind_vcgen` needs `CatCryptCore.Tactics.BindVcgen`
  - NonUniform/WhileRelational `rHoare_fail_fail`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe liftR_fail` needs `CatCryptCore.Tactics.AutoSets`
  - NonUniform/WhileRelational `rHoare_whileApprox_zero`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe rHoare_fai` needs `CatCryptCore.Tactics.AutoSets`
  - NonUniform/WhileRelational `rHoare_whileApprox_same`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe hguard, un` needs `CatCryptCore.Tactics.AutoSets`
  - NonUniform/WhileRelationalLimit `rHoare_whileLoop_same`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe hguard, un` needs `CatCryptCore.Tactics.AutoSets`
  - Relational/Separation `r_frame_set_sync_eqPre`: `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsafe r_frame_se` needs `CatCryptCore.Tactics.AutoSets`
- The cycle modules (Relational/Approx, Judgment, Rules, SpanLifting) cannot use `catcrypt_auto?` at all; trials there would need the dispatcher split from its relational dependencies or the trials run in a downstream scratch module.
- Relational/Rules.lean carries 5 linter warnings for unused simp arguments (lines 142, 146, 153, 462 twice). Step 2 was skipped for this file because of the import cycle, so they remain.
- Unused variable names flagged on the base branch remain: NonUniform/Bernoulli.lean:123, NonUniform/CenteredBinomial.lean:167, NonUniform/CouplingRules.lean:119, 126, 143. They were left as they are.
- The cited arguments change which arm closes a goal: in Examples/PRFPRG, `hyb_0_eq_real` and `hyb_2_eq_ideal` (term proofs citing `gen_hyb_zero_eq_real F`, `gen_hyb_two_eq_ideal F`) are closed by the first SPComp-equality arm `catcrypt_grind [...]` when the cited lemma is passed (not frozen, AutoSets missing), while a preliminary run that passed no arguments for term proofs got `bind_vcgen`, the second arm. A suggestion mode that prefers arms available without AutoSets, or reports every closing arm, would let more of these be frozen.
- Several frozen whole-proof suggestions replace a term proof or `rfl` by a tactic call (`bind_vcgen`, `grind [...]`, `hop_chain`); they are no shorter than the original. They are recorded above as frozen per the procedure.
- No statement looked vacuous and no lemma was found to be in the wrong module during this pass; this was not checked systematically.

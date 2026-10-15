# AUTO_CORPUS_2 report

Branch `work/auto-corpus-2`, created from `origin/work/auto-corpus` (751637d). Each modified module was
built with `lake build CatCryptCore.<Module>`; every build succeeded, no Mathlib module was rebuilt,
and no warning was reported in an edited file. Line numbers below refer to the files at
`origin/work/auto-corpus`, except the golf positions of a file that also received frozen suggestions,
which refer to the file after those were applied.

## Procedure

1. Theorem selection. A theorem was tried when its statement text mentions `rHoare`, `Advantage`,
   `AdvantageA`, `sdist`, `prTrue`, `prEvent`, `IsPure` or `NoFail`, or mentions `SPComp` and an
   equation. Statements that reach these notions only through a definition (e.g. `acceptProb`) were
   not selected.
2. Whole proofs. With `public import CatCryptCore.Tactics.AutoDispatchExt` added to a temporary copy,
   every selected proof was replaced at once by `catcrypt_auto? [..]` with the lemmas and the
   hypotheses (names starting with `h`) its old proof cites; terms reported as unknown were dropped
   and the trial repeated. Diagnostics were read with `lake env lean --json` on the copy (the
   language-server client of `lean-query.py` exited with a fatal error on these copies; the
   repository files were not modified by the trials).
3. Closing steps. For theorems not closed whole, the last tactic of each branch, each one-line
   `calc` step proof and each `simp_all`/`simp only`/`bind_align` call were replaced by
   `catcrypt_auto? [..]` (cited lemmas and `h`-hypotheses of the step). A step without diagnostics
   (not reached after an earlier failure in its block) was retried separately.
4. Freezing. A suggestion was frozen when it closed its goal, used none of `hop_chain`,
   `sum_atoms_le`, `gcongr_unfold` outside an I-ok file, and was not longer than what it replaced
   (fewer lines, or equal lines and no more characters). The same length rule was applied to whole
   proofs; this rejects for instance `rfl` → `simp_all`, which the task text would otherwise freeze.
   Frozen suggestions were elaborated without the temporary import; a suggestion whose only defect
   was an unused-simp-argument warning was pruned as the linter proposes, others with errors or
   warnings were dropped.
5. Golf, mechanical and checked by elaboration: runs of one-line `rw` merged; `rw [A]` followed by
   a closing `simp [B]` replaced by `simp [A, B]` (no unused-argument warning allowed); `calc` step
   proofs longer than the replacement replaced by `by gcongr`, `by linarith` or `by grind` (first
   that closes). In addition two unused `mapSum` simp arguments flagged by the linter in
   SizeBoundedUC were removed, and two overlong frozen lines were wrapped.
6. Deprecations. The baseline build reported no deprecation warning in any of the 27 files; no
   replacement was needed.

## Summary

- Theorems closed whole by one frozen suggestion: 9 (MLWE_PKE_Scheme 1, DualModeOT 1, QueryBoundedUC 2,
  SDistrLift 1, ShallowModule 1, SizeBoundedUC 1, UCAdmClass/SPCompInstance 2).
- Closing steps replaced by frozen suggestions: 5 (FIPS203Security 1, FOTransform 1, FOTransformU 2,
  SDistrLift 1).
- Failed positions recorded: 143 (shape `other` 94, `distance inequality` 35, `SPComp equality` 5,
  not well-formed trials 5, and four single cases).
- Files with commits: 17. Files without any change: KEM/Games, MultiQueryPRF, NomAdvantage, PKE/Games,
  PRPPRFSwitching, RCL3SPComp, SwitchingLemma, TV, UCAlg, UCComposition (no commit for these).
- No `AutoMetrics` import was kept: no I-ok file produced a frozen suggestion using `hop_chain`,
  `sum_atoms_le` or `gcongr_unfold`.
- No statement, definition, import, attribute or declaration name was changed; no declaration was
  added or deleted; no `sorry` or `native_decide` was introduced.

## Skipped

- catcrypt_auto? trials skipped for ForkingLemma, HybridArgument, MultiQueryPRF, NomAdvantage,
  NomPkgBridge and SDist: each is in the transitive import closure of
  `CatCryptCore.Tactics.AutoDispatchExt` (the copy with the import reported every declaration of
  the module as already declared). The parenthetical of the task ("skip step 2") was read as
  skipping the catcrypt_auto? trials of step 1; golf (step 2) and the deprecation check (step 3) were
  still done for these files. If step 2 was meant literally, the golf commits of ForkingLemma,
  HybridArgument, NomPkgBridge and SDist are the ones to drop.
- KEM/Games, RCL3, UCAlg: the extraction found no theorem of the selected class (RCL3 received a
  calc golf only).

## Vacuity-sweep files

Of the files named for the vacuity sweep, only `Crypto/UCAdmClass/SPCompInstance.lean` (taken as
covered by `Crypto/UCAdmClass*`) was edited: two proof-only replacements (`spcomp_distComp_comm`,
`spcomp_distComp_bind_right`), statements unchanged. BadEvent, the other UCAdmClass files,
Examples/Cryptobox, Curve25519 and MontgomeryXOnly were not in the file list and were not edited.
CatCryptCore/Consensus was not touched.

## Interface queue

- Import closure: `AutoDispatchExt` transitively imports ForkingLemma, HybridArgument,
  MultiQueryPRF, NomAdvantage, NomPkgBridge and SDist (these have 743 to 4988 importers), so
  `catcrypt_auto` cannot be used in them. A tactic entry module whose closure stops below
  `Crypto/SDist` would make it available there.
- Suggestions naming `catcrypt_grind` (RC `sdist_of_RC`, UCComposition `sdist_compile` twice,
  ShallowModule `hybrid_boundA₃`) do not elaborate without `CatCryptCore.Tactics.AutoSets`; they
  were dropped. Emitting the expansion (`grind` with the `CatCryptGrind` set spelled out) in the
  "Try this" text would make them freezable without an import.
- Suggestions using `hop_chain`/`gcongr_unfold` in non-I-ok files, not used: SwitchingLemma
  `prf_prp_composition`, `prf_prp_compositionA` (whole proof and closing step), PKE/Games
  `owcpa_le_indcpa` (calc step at line 366, `gcongr_unfold`).
- Definitions and non-lemma terms passed in the argument list reach `grind` and abort that arm
  ("invalid `grind` theorem, failed to find an usable pattern", e.g. `Heap.empty` in
  SwitchingLemma `switching_from_birthday`); filtering terms without a usable pattern before the
  `grind` arm would leave the other arms unaffected.
- On `rfl`-closed goals the dispatcher suggests `simp_all`, which is longer than the original; a
  `rfl` arm tried first would make these suggestions identities.
- No vacuous statement, misplaced lemma or hypothesis of the form `∀ A, Adv … ≤ ε` was identified;
  statements were not examined beyond what the trials required.

## Per file
### ForkingLemma

Lines added/deleted: 4/5.

catcrypt_auto? trials skipped: the module is in the transitive import closure of CatCryptCore.Tactics.AutoDispatchExt, so the temporary import would create an import cycle. Golf and the deprecation check were done.

Golf: calc step at line 167 closed by `by grind`; calc step at line 171 closed by `by grind`; calc step at line 176 closed by `by grind`; calc step at line 282 closed by `by grind`.

### HybridArgument

Lines added/deleted: 3/4.

catcrypt_auto? trials skipped: the module is in the transitive import closure of CatCryptCore.Tactics.AutoDispatchExt, so the temporary import would create an import cycle. Golf and the deprecation check were done.

Golf: calc step at line 88 closed by `by gcongr`; calc step at line 104 closed by `by gcongr`; calc step at line 101 closed by `by grind`.

### KEM/FIPS203Security

Lines added/deleted: 2/5.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced:
- `advantage_le_flag`, line 666 of the original: replaced by `grind [OracleAdv.run_apply_flag_false_eq, oFlag_apply_true_false, oFlag_apply_false_eq]`.

Suggestions not frozen:
- `advantage_le_flag@657`: `simp_all`; longer than the replaced step.
- `advantage_le_eager@2062`: `simp_all`; longer than the replaced step.

Positions where catcrypt_auto? failed:
- `advantage_le_flag` line 654 (whole proof): other
- `advantage_le_eager` line 2059 (whole proof): other
- `owpcaAdvantage_redFix` line 2108 (whole proof): other
- `cca_le_three_terms` line 2178 (whole proof): other
- `owpca_eq_redROM` line 2343 (whole proof): other
- `fips203_indcca` line 2385 (whole proof): other
- `advantage_le_flag` line 661 (closing step): other
- `advantage_le_flag` line 664 (closing step): other
- `advantage_le_flag` line 671 (closing step): distance inequality
- `advantage_le_flag` line 674 (closing step): other
- `advantage_le_flag` line 675 (closing step): other
- `owpcaAdvantage_redFix` line 2109 (closing step): other
- `owpcaAdvantage_redFix` line 2112 (closing step): other
- `owpcaAdvantage_redFix` line 2115 (closing step): other
- `cca_le_three_terms` line 2180 (closing step): other
- `cca_le_three_terms` line 2201 (closing step): other
- `cca_le_three_terms` line 2217 (closing step): other
- `owpca_eq_redROM` line 2344 (closing step): other
- `owpca_eq_redROM` line 2348 (closing step): other
- `fips203_indcca` line 2394 (closing step): other

Golf: rw+simp -> simp at line 1721.

### KEM/FOTransform

Lines added/deleted: 1/1.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced:
- `foNotBot_indcca`, line 719 of the original: replaced by `grind [tTransform_owpca_of_total]`.

Suggestions not frozen:
- `prTrue_pmfGame_true@400`: `simp_all [Set.indicator]`; longer than the replaced step.
- `foAdvantage_le@426`: `catcrypt_grind [advantage_bind_le]`; longer than the replaced step.
- `foNotBot_indcca_of_indcpa@742`: `simp_all [owcpa_le_indcpa]`; longer than the replaced step.
- `foNotBot_indcca_of_indcpa@743`: `simp_all [owcpa_le_indcpa]`; longer than the replaced step.

Positions where catcrypt_auto? failed:
- `prTrue_pmfGame_true` line 396 (whole proof): other
- `advantage_bind_le` line 407 (whole proof): distance inequality
- `foAdvantage_le` line 423 (whole proof): other
- `owpca_eq` line 672 (whole proof): other
- `foNotBot_indcca` line 703 (whole proof): other
- `foNotBot_indcca_of_indcpa` line 739 (whole proof): other
- `advantage_bind_le` line 408 (closing step): distance inequality
- `foAdvantage_le` line 425 (closing step): distance inequality
- `owpca_eq` line 673 (closing step): other
- `owpca_eq` line 677 (closing step): other
- `foNotBot_indcca` line 707 (closing step): trial not well-formed (the replacement broke the calc syntax); no result

Golf: none.

### KEM/FOTransformU

Lines added/deleted: 2/4.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced:
- `romINDCCAAdvantage_le_flag`, line 366 of the original: replaced by `grind [OracleAdv.run_apply_flag_false_eq, oFlag_apply_true_false, oFlag_apply_false_eq]`.
- `owpcaAdvantage_uReduction`, line 1019 of the original: replaced by `grind [uReduction_prob]`.

Suggestions not frozen:
- `romINDCCAAdvantage_le_flag@357`: `simp_all`; longer than the replaced step.
- `prTrue_pmfGame_eq@1006`: `simp_all [PMF.map_id, h]`; longer than the replaced step.
- `uNotBot_indcca@1095c`: `grind`; longer than the replaced step.

Positions where catcrypt_auto? failed:
- `romINDCCAAdvantage_le_flag` line 354 (whole proof): other
- `prTrue_pmfGame_eq` line 1004 (whole proof): other
- `owpcaAdvantage_uReduction` line 1014 (whole proof): other
- `uNotBot_indcca` line 1051 (whole proof): other
- `romINDCCAAdvantage_le_flag` line 361 (closing step): other
- `romINDCCAAdvantage_le_flag` line 364 (closing step): other
- `romINDCCAAdvantage_le_flag` line 371 (closing step): distance inequality
- `romINDCCAAdvantage_le_flag` line 374 (closing step): other
- `romINDCCAAdvantage_le_flag` line 375 (closing step): other
- `owpcaAdvantage_uReduction` line 1016 (closing step): other
- `uNotBot_indcca` line 1056 (closing step): trial not well-formed (the replacement broke the calc syntax); no result
- `uNotBot_indcca` line 1077 (closing step): other

Golf: none.

### KEM/Games

Lines added/deleted: 0/0.

Golf: none.

### MLKEM/MLWE_PKE_Scheme

Lines added/deleted: 1/5.

Theorems closed whole by one frozen suggestion: `prTrue_map_some` (`(unfold CatCrypt.Crypto.MLKEM.prTrue; simp_all [PMF.map_apply])`).

Closing steps replaced: none.

Suggestions not frozen:
- `advantage_pmfGame_eq_absDiff@140`: `(unfold CatCrypt.Crypto.MLKEM.absDiff; simp_all)`; longer than the replaced step.

Positions where catcrypt_auto? failed:
- `sdistr_bind_eq` line 118 (whole proof): other
- `sdistr_bind_map_some` line 122 (whole proof): other
- `advantage_pmfGame_eq_absDiff` line 138 (whole proof): other
- `indcpaAdvantage_eq_absDiff` line 207 (whole proof): other
- `indcpaAdvantage_eq_absDiff_prTrue` line 215 (whole proof): other
- `sdistr_bind_map_some` line 125 (closing step): other
- `advantage_pmfGame_eq_absDiff` line 139 (closing step): other
- `indcpaAdvantage_eq_absDiff_prTrue` line 216 (closing step): other

Golf: none.

### MultiQueryPRF

Lines added/deleted: 0/0.

catcrypt_auto? trials skipped: the module is in the transitive import closure of CatCryptCore.Tactics.AutoDispatchExt, so the temporary import would create an import cycle. Golf and the deprecation check were done.

Golf: none.

### NomAdvantage

Lines added/deleted: 0/0.

catcrypt_auto? trials skipped: the module is in the transitive import closure of CatCryptCore.Tactics.AutoDispatchExt, so the temporary import would create an import cycle. Golf and the deprecation check were done.

Golf: none.

### NomPkgBridge

Lines added/deleted: 4/6.

catcrypt_auto? trials skipped: the module is in the transitive import closure of CatCryptCore.Tactics.AutoDispatchExt, so the temporary import would create an import cycle. Golf and the deprecation check were done.

Golf: rw merge at line 80; rw+simp -> simp at line 143; calc step at line 175 closed by `by grind`; calc step at line 176 closed by `by grind`; calc step at line 177 closed by `by grind`.

### OT/DualModeOT

Lines added/deleted: 1/5. I-ok.

Theorems closed whole by one frozen suggestion: `sdist_dualEnc_uniform` (`simp_all [dualEnc_uniform, sdist_self]`).

Closing steps replaced: none.

Suggestions not frozen:
- `dualOT_reduction@300`: `catcrypt_grind [SPComp.bind_assoc, SPComp.pure_bind]`; longer than the replaced step.

Positions where catcrypt_auto? failed:
- `dualEnc_uniform` line 177 (whole proof): SPComp equality
- `dualOT_reduction` line 228 (whole proof): other
- `dualEnc_uniform` line 182 (closing step): SPComp equality
- `dualOT_reduction` line 231 (closing step): distance inequality
- `dualOT_reduction` line 251 (closing step): distance inequality
- `dualOT_reduction` line 302 (closing step): distance inequality
- `dualOT_reduction` line 327 (closing step): distance inequality

Golf: none.

### PKE/Games

Lines added/deleted: 0/0.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Suggestions not frozen:
- `owcpa_le_indcpa@291`: `simp_all [PMF.map_id, h]`; longer than the replaced step.
- `owcpa_le_indcpa@366c`: `gcongr_unfold`; uses hop_chain/sum_atoms_le/gcongr_unfold outside an I-ok file.

Positions where catcrypt_auto? failed:
- `owcpa_le_indcpa` line 287 (whole proof): other
- `owcpa_le_indcpa` line 293 (closing step): other
- `owcpa_le_indcpa` line 364 (closing step): trial not well-formed (the replacement broke the calc syntax); no result

Golf: none.

### PRPPRFSwitching

Lines added/deleted: 0/0.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Suggestions not frozen:
- `prEventComp_flagGame@366`: `grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.get_set_other]`; longer than the replaced step.
- `rfGame_eq@372`: `simp_all`; longer than the replaced step.
- `rpGame_eq@378`: `simp_all`; longer than the replaced step.
- `RF_RP_Advantage_le@406`: `grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.get_set_other, OracleAdv.run_apply_flag_false_eq, r`; longer than the replaced step.
- `RF_RP_Advantage_le@410`: `grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.get_set_other, Heap.get_set_same, Heap.get_set_othe`; longer than the replaced step.
- `RF_RP_Advantage_le@414`: `simp_all [CatCrypt.Prob.BirthdayBound.gauss_sum_nat]`; longer than the replaced step.

Positions where catcrypt_auto? failed:
- `prTrue_pmfGame_map` line 342 (whole proof): other
- `prTrue_flagGame` line 351 (whole proof): other
- `prEventComp_flagGame` line 361 (whole proof): other
- `rfGame_eq` line 369 (whole proof): other
- `rpGame_eq` line 375 (whole proof): other
- `RF_RP_Advantage_eq_flagGame` line 387 (whole proof): other
- `RF_RP_Advantage_le` line 396 (whole proof): other
- `PRF_q_Advantage_le` line 421 (whole proof): other
- `PRF_q_Advantage_of_isQueryBound_zero` line 439 (whole proof): other
- `PRP_q_Advantage_of_isQueryBound_zero` line 444 (whole proof): other
- `RF_RP_Advantage_of_isQueryBound_zero` line 450 (whole proof): other
- `prTrue_pmfGame_map` line 345 (closing step): other
- `RF_RP_Advantage_eq_flagGame` line 388 (closing step): other
- `RF_RP_Advantage_le` line 401 (closing step): other
- `RF_RP_Advantage_le` line 411 (closing step): heap read after write
- `PRF_q_Advantage_of_isQueryBound_zero` line 440 (closing step): other
- `PRP_q_Advantage_of_isQueryBound_zero` line 445 (closing step): other

Golf: none.

### QueryBoundedUC

Lines added/deleted: 7/14. I-ok.

Theorems closed whole by one frozen suggestion: `ex_queryBounded_no_separation` (`grind [le_antisymm, ucCdist_le_ucSdist, Example.F, ex_ucSdist_le_one, ex_queryBounded_ucCdist_ge_one]`), `ex_queryBounded_ucCdist_eq_one` (`grind [le_antisymm, ucCdist_le_ucSdist, Example.F, ex_ucSdist_le_one, ex_queryBounded_ucCdist_ge_one]`).

Closing steps replaced: none.

Suggestions not frozen:
- `exD_advantage_one@155`: `(unfold CatCrypt.Crypto.Example.π; unfold CatCrypt.Crypto.QueryBoundedUC.exD; catcrypt_grind [SPComp.pure_bind`; longer than the replaced step.
- `exD_advantage_one@157`: `(unfold CatCrypt.Crypto.Example.F; unfold CatCrypt.Crypto.QueryBoundedUC.exD; catcrypt_grind [Example.F, SPCom`; longer than the replaced step.
- `exD_advantage_one@159`: `(unfold CatCrypt.Crypto.absDiff; simp_all)`; longer than the replaced step.
- `queryBoundedCompDist_adm_eq`: `simp_all`; longer than the original proof.

Positions where catcrypt_auto? failed:
- `queryBoundedCompDist_adm_iff` line 78 (whole proof): other
- `adm_pure_predicate` line 137 (whole proof): other
- `exD_advantage_one` line 153 (whole proof): other

Golf: rw+simp -> simp at line 158.

### RCL3

Lines added/deleted: 1/2. I-ok.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

No theorem of the selected class (statement mentioning rHoare, Advantage/AdvantageA, sdist, prTrue/prEvent, IsPure/NoFail or an SPComp equality) was found by the extraction.

Golf: calc step at line 104 closed by `by gcongr`.

### RCL3SPComp

Lines added/deleted: 0/0. I-ok.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Positions where catcrypt_auto? failed:
- `ucSdist_eq_sdist` line 40 (whole proof): other

Golf: none.

### RC

Lines added/deleted: 2/2.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Suggestions not frozen:
- `sdist_of_RC@185`: `catcrypt_grind`; unknown tactic.
- `contextEquiv_iff_sdist`: `grind [sdist_of_contextEquiv, contextEquiv_of_sdist]`; longer than the original proof.
- `RC_iff_sdist`: `grind [sdist_of_RC, RC_of_sdist]`; longer than the original proof.

Positions where catcrypt_auto? failed:
- `contextEquiv_of_sdist` line 96 (whole proof): other
- `sdist_of_contextEquiv` line 106 (whole proof): distance inequality
- `RC_of_sdist` line 146 (whole proof): other
- `sdist_of_RC` line 163 (whole proof): distance inequality
- `sdist_implies_UCEmulates` line 203 (whole proof): other
- `sdist_mapSum_le` line 300 (whole proof): distance inequality
- `UCEmulates_mapSum_of_sdist` line 383 (whole proof): other
- `contextEquiv_of_sdist` line 98 (closing step): distance inequality
- `sdist_of_contextEquiv` line 128 (closing step): distance inequality
- `sdist_of_RC` line 175 (closing step): distance inequality
- `sdist_mapSum_le` line 306 (closing step): distance inequality
- `sdist_mapSum_le` line 318 (closing step): distance inequality
- `sdist_mapSum_le` line 322 (closing step): distance inequality
- `sdist_mapSum_le` line 333 (closing step): distance inequality
- `UCEmulates_mapSum_of_sdist` line 385 (closing step): distance inequality

Golf: calc step at line 320 closed by `by grind`; calc step at line 335 closed by `by grind`.

### SDist

Lines added/deleted: 3/5.

catcrypt_auto? trials skipped: the module is in the transitive import closure of CatCryptCore.Tactics.AutoDispatchExt, so the temporary import would create an import cycle. Golf and the deprecation check were done.

Golf: calc step at line 380 closed by `by gcongr`; calc step at line 165 closed by `by grind`; calc step at line 376 closed by `by grind`.

### SDistrLift

Lines added/deleted: 3/5.

Theorems closed whole by one frozen suggestion: `bind_sdistrToSPComp_eq` (`simp_all [SPComp.bind, SDistr.bind_assoc, SDistr.pure_bind]`).

Closing steps replaced:
- `sdistrToSPComp_bind`, line 62 of the original: replaced by `simp_all [SDistr.bind_assoc, SDistr.pure_bind]`.

Positions where catcrypt_auto? failed:
- `sdistrToSPComp_run` line 49 (whole proof): other
- `sdistrToSPComp_pure` line 53 (whole proof): SPComp equality
- `sdistrToSPComp_bind` line 59 (whole proof): SPComp equality
- `sdistrToSPComp_isPure` line 66 (whole proof): IsPure/NoFail side condition
- `sdistrToSPComp_pure` line 54 (closing step): SPComp equality

Golf: rw+simp -> simp at line 86.

### SecurityDefs

Lines added/deleted: 2/2.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Suggestions not frozen:
- `INDCCA_rejectGame_eq`: `(unfold CatCrypt.Crypto.SecurityDefs.INDCCA_rejectGame; unfold CatCrypt.Crypto.SecurityDefs.INDCPA_Game; simp `; longer than the original proof.

Positions where catcrypt_auto? failed:
- `PRF_Adv_zero_of_rHoare` line 221 (whole proof): other
- `INDCPA_Adv_zero_of_rHoare` line 227 (whole proof): other
- `INDCCA_Adv_zero_of_rHoare` line 238 (whole proof): other
- `INDCCA_reduces_to_INDCPA` line 259 (whole proof): distance inequality
- `INDCCA_Adv_zero_of_rHoare` line 240 (closing step): other
- `INDCCA_reduces_to_INDCPA` line 266 (closing step): trial not well-formed (the replacement broke the calc syntax); no result

Golf: calc step at line 268 closed by `by grind`.

### ShallowModule

Lines added/deleted: 4/4. I-ok.

Theorems closed whole by one frozen suggestion: `advantageA_absorb_left` (`simp_all [advantageA_absorb]`).

Closing steps replaced: none.

Suggestions not frozen:
- `hybrid_boundA₃`: `catcrypt_grind [hybrid_bound₃]`; unknown tactic.

Positions where catcrypt_auto? failed:
- `advantageA_absorb` line 60 (whole proof): other
- `OracleModule.toGame_ofGame` line 93 (whole proof): other
- `hybrid_bound₃` line 106 (whole proof): distance inequality
- `advantageA_absorb` line 61 (closing step): other

Golf: calc step at line 107 closed by `by grind`; calc step at line 110 closed by `by grind`.

### SizeBoundedUC

Lines added/deleted: 7/12. I-ok.

Theorems closed whole by one frozen suggestion: `ex_size_no_separation` (`grind [le_antisymm, ucCdist_le_ucSdist, Example.F, ex_size_ucSdist_le_one, ex_size_ucCdist_ge_one]`).

Closing steps replaced: none.

Suggestions not frozen:
- `exD_advantage_one@347`: `(unfold CatCrypt.Crypto.Example.π; unfold CatCrypt.Crypto.SizeBoundedUC.exD; catcrypt_grind [SPComp.pure_bind,`; longer than the replaced step.
- `exD_advantage_one@349`: `(unfold CatCrypt.Crypto.Example.F; unfold CatCrypt.Crypto.SizeBoundedUC.exD; catcrypt_grind [Example.F, SPComp`; longer than the replaced step.
- `exD_advantage_one@351`: `(unfold CatCrypt.Crypto.absDiff; simp_all)`; longer than the replaced step.
- `sizeCompDist_adm_eq`: `simp_all`; longer than the original proof.

Positions where catcrypt_auto? failed:
- `sizeCompDist_adm_iff` line 213 (whole proof): other
- `adm_pure_predicate_size` line 225 (whole proof): other
- `exD_advantage_one` line 345 (whole proof): other

Golf: rw+simp -> simp at line 350; calc step at line 97 closed by `by linarith`; calc step at line 105 closed by `by linarith`.

### SwitchingLemma

Lines added/deleted: 0/0.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Suggestions not frozen:
- `prf_prp_composition`: `hop_chain`; uses hop_chain/sum_atoms_le/gcongr_unfold outside an I-ok file.
- `prf_prp_compositionA`: `hop_chain`; uses hop_chain/sum_atoms_le/gcongr_unfold outside an I-ok file.
- `prf_prp_compositionA@124`: `hop_chain`; uses hop_chain/sum_atoms_le/gcongr_unfold outside an I-ok file.

Positions where catcrypt_auto? failed:
- `switching_from_birthday` line 82 (whole proof): distance inequality
- `switching_via_hybrid` line 95 (whole proof): distance inequality

Golf: none.

### TV

Lines added/deleted: 0/0. I-ok.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Suggestions not frozen:
- `prTrue_bind_as_weighted_sum@101`: `simp_all`; longer than the replaced step.

Positions where catcrypt_auto? failed:
- `prTrue_bind_as_weighted_sum` line 79 (whole proof): other
- `absDiff_prTrue_bind_le_tvDist` line 118 (whole proof): distance inequality
- `prTrue_bind_as_weighted_sum` line 82 (closing step): other
- `prTrue_bind_as_weighted_sum` line 85 (closing step): other
- `absDiff_prTrue_bind_le_tvDist` line 128 (closing step): No goals to be solved
- `absDiff_prTrue_bind_le_tvDist` line 130 (closing step): distance inequality

Golf: none.

### UCAdmClass/SPCompInstance

Lines added/deleted: 2/8. I-ok.

Theorems closed whole by one frozen suggestion: `spcomp_distComp_comm` (`simp_all [spcomp_distComp, absDiff_comm]`), `spcomp_distComp_bind_right` (`simp_all [spcomp_distComp, SPComp.bind_assoc]`).

Closing steps replaced: none.

Suggestions not frozen:
- `ucCdist_eq_ucSdist_trivial@179`: `simp_all [ucCdist_le_ucSdist]`; longer than the replaced step.
- `spcomp_distComp_self`: `simp_all [spcomp_distComp, absDiff_self]`; longer than the original proof.

Positions where catcrypt_auto? failed:
- `spcomp_sdist_eq_iSup` line 94 (whole proof): other
- `spcomp_distComp_bind_left` line 113 (whole proof): monotonicity inequality
- `spcomp_distComp_mapSum` line 135 (whole proof): other
- `ucCdist_eq_ucSdist_trivial` line 177 (whole proof): other
- `spcomp_sdist_eq_iSup` line 95 (closing step): other
- `spcomp_distComp_bind_left` line 124 (closing step): distance inequality
- `spcomp_distComp_bind_left` line 126 (closing step): distance inequality
- `spcomp_distComp_mapSum` line 140 (closing step): distance inequality
- `spcomp_distComp_mapSum` line 148 (closing step): distance inequality
- `spcomp_distComp_mapSum` line 150 (closing step): distance inequality
- `spcomp_distComp_mapSum` line 158 (closing step): distance inequality

Golf: none.

### UCAlg

Lines added/deleted: 0/0.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Positions where catcrypt_auto? failed:
- `UCEmulatesAlg_of_sdist` line 144 (whole proof): other

Golf: none.

### UCComposition

Lines added/deleted: 0/0.

Theorems closed whole by one frozen suggestion: none.

Closing steps replaced: none.

Suggestions not frozen:
- `sdist_compile@90`: `catcrypt_grind`; unknown tactic.
- `sdist_compile@92`: `catcrypt_grind [sdist_compile_same]`; unknown tactic.

Positions where catcrypt_auto? failed:
- `sdist_compile_same` line 54 (whole proof): distance inequality
- `sdist_compile` line 71 (whole proof): distance inequality
- `UCEmulates_compile` line 112 (whole proof): other
- `UCEmulates_compile_same_sub` line 122 (whole proof): other
- `UCEmulates_compile_perfect` line 132 (whole proof): other
- `UCEmulates_par` line 156 (whole proof): other
- `sdist_compile_same` line 57 (closing step): distance inequality
- `sdist_compile` line 74 (closing step): trial not well-formed (the replacement broke the calc syntax); no result

Golf: none.


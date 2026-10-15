# Auto-corpus pass 3: frozen `catcrypt_auto` suggestions and golf

Branch `work/auto-corpus-3`, created from `origin/work/auto-corpus` (751637d). One commit per
changed file; this report is the last commit. Every changed module was built with
`lake build CatCryptCore.<Module>` (Mathlib replayed, not rebuilt) and a final combined build of
all 27 modules succeeded (2804 jobs). No statement, definition, import, attribute or declaration
name was changed, no declaration was added or removed, and the changed files contain no `sorry`,
`native_decide` or temporary import. No deprecation warning occurred in any of the 27 files, so
step 3 made no change.

## Method

- Step 1 used the temporary `public import CatCryptCore.Tactics.AutoDispatchExt`. A theorem was
  attempted when its statement text contains `rHoare`, `Advantage`, `AdvantageA`, `sdist`,
  `prTrue`, `prEvent`, `IsPure`, `NoFail`, or an equation together with `SPComp`. Arguments of
  `catcrypt_auto? [..]` were the hypotheses and constants cited by the replaced proof text;
  arguments reported as unknown identifiers or as non-propositional locals were dropped and the
  attempt repeated.
- Trials ran through a leanclient-based driver (one server per file, the file on disk unchanged)
  instead of `lean-query.py multi`, because `multi` replaces a single line and does not print the
  "Try this" information messages; whole-proof replacement needs a line range. The driver waits
  until the diagnostics are stable; without that wait the first run returned stale diagnostics.
- A suggestion was frozen only after a second trial without the temporary import showed no error
  and no warning in the edited lines. Candidates were re-verified in rounds until stable, because
  an `unknown tactic` parse error in one candidate can hide the error of a later candidate in the
  same declaration (this occurred in CBCMode and CPAFromPRF). Each frozen file was then built.
- Closing steps: the last tactic of each branch, each `calc` step (tactic or term), match-arm
  bodies, `simp only`/`simp_all`/`bind_align` closers. The step finder was extended during the
  run (match-arm bodies, term `calc` steps, multi-line `exact`); a second steps pass with the final
  finder was run on all earlier files with matching theorems (results under "Second pass").
- Line numbers below are those of the file as it stood when the pass ran (for the first pass, the
  original file; for the second pass, the file after its first commit).

## Lines added and deleted (`git diff --numstat origin/work/auto-corpus`)

| File | + | - |
|---|---|---|
| Crypto/UCConcrete.lean | 6 | 15 |
| Crypto/UCDSL.lean | 9 | 18 |
| Crypto/UC.lean | 10 | 21 |
| Crypto/UCLevels.lean | 12 | 32 |
| Crypto/UCMonad.lean | 14 | 32 |
| Crypto/UCMonad/RoundMCompDist.lean | 7 | 41 |
| Crypto/UCMonad/RoundM.lean | 5 | 19 |
| Crypto/UCMonad/SDistrInstance.lean | 16 | 52 |
| Crypto/UCMonad/SPCompInstance.lean | 6 | 32 |
| Crypto/ZK/SigmaUCZK.lean | 7 | 17 |
| Deep/Bridge.lean | 3 | 7 |
| Deep/Eval.lean | 8 | 39 |
| Deep/OracleGamePackage.lean | 1 | 5 |
| Deep/PackageEquiv.lean | 5 | 26 |
| Deep/PureCode.lean | 0 | 0 |
| Deep/ReflectUCHelpers.lean | 6 | 9 |
| Deep/Strategy.lean | 0 | 0 |
| Examples/BasicHash.lean | 1 | 2 |
| Examples/CBCMode.lean | 6 | 8 |
| Examples/ChaumPedersen.lean | 3 | 10 |
| Examples/CoinToss.lean | 1 | 4 |
| Examples/Commitment.lean | 3 | 2 |
| Examples/Commitments/CommitmentScheme.lean | 0 | 0 |
| Examples/Commitments/Pedersen.lean | 4 | 6 |
| Examples/CPAFromPRF.lean | 11 | 28 |
| Examples/Cryptobox/AE.lean | 0 | 0 |
| Examples/Cryptobox/Cryptobox.lean | 2 | 7 |
| Total | 146 | 432 |

## Theorems closed whole by one frozen suggestion (9)

- Deep/ReflectUCHelpers: `AdvantageA_pure` -> `simp_all [AdvantageA, SPComp.bind_pure]`.
- Examples/CBCMode: `cbc_perfect_indcpa` -> `grind [INDCPA_Adv_zero_of_rHoare, cbc_indcpa_coupling]`;
  `boolCBC_perfect_indcpa` -> `grind [cbc_perfect_indcpa]`.
- Examples/Commitment: `maskComm_perfect_hiding` -> `unfold Hiding_Adv` and
  `simp_all [advantage_zero_of_rHoare, maskComm_hiding_coupling]` (one line longer than the term
  it replaces).
- Examples/Commitments/Pedersen: `pedersen_full_security` ->
  `simp_all [pedersen_perfect_hiding, pedersen_binding_le_dlog]`.
- Examples/CPAFromPRF: `bijCPA_prf_perfect` -> `grind [bijPRF_perfect]`; `bijCPA_perfect_indcpa` ->
  `grind [INDCPA_Adv_zero_of_rHoare, bijCPA_indcpa_coupling]`; `boolXorCPA_perfect_indcpa` ->
  `grind [bijCPA_perfect_indcpa]`; `PRFEncScheme.otp_advantage_zero` -> `simp_all` with the
  arguments of the former `simp only`.

Seven of the nine replace a one-line term proof by a one-line tactic proof; they do not shorten
the file.

## Closing steps replaced (15 frozen, 12 in the final files)

- Deep/ReflectUCHelpers: line 103 `exact liftR_eq_implies_eq hEq` -> `grind [liftR_eq_implies_eq]`;
  line 207 `funext A; exact runPkg_link_ofOracle_congr ..` -> `grind [runPkg_link_ofOracle_congr]`;
  second pass line 101 `simp_all [eqPost]` -> `simp_all`.
- Examples/CBCMode: line 225 `rfl` -> `grind`.
- Examples/ChaumPedersen: lines 268, 271 `rw [..]` -> `simp_all [..]` (same lemmas); lines 281, 282
  `exact commitment_recovery ..` -> `grind [commitment_recovery]`; line 283 `rfl` -> `simp_all`.
- Examples/Commitments/Pedersen: second pass line 251 `exact binding_extracts_dlog ..` ->
  `grind [binding_extracts_dlog, zpowZMod₁_g₁_injective]`.
- Examples/CPAFromPRF: line 213 `rw [B.xorOut_cancel]` -> `simp_all [B.xorOut_cancel]`; line 569
  `simp only [PRFEncScheme.otpGame, SPComp.monad_bind_eq]` -> `bind_vcgen`; calc steps 488, 489
  (`hswap` -> `by bound`, `H.bound x Ared` -> `by simp_all [H.bound]`), removed afterwards by the
  golf of `cpa_from_prf_bound`.
- Crypto/UCDSL: line 126 `unfold UCProtocol.ofGame; rw [h]` -> `simp_all [UCProtocol.ofGame, h]`
  was frozen, produced two unused-simp-argument warnings, and was removed by the golf of
  `UCEmulates_of_game_eq`.

No frozen suggestion uses `hop_chain`, `sum_atoms_le` or `gcongr_unfold`; no file received the
`AutoMetrics` import. Two such suggestions in I-ok files (CPAFromPRF step 476 `hop_chain`,
Cryptobox step 302 `gcongr_unfold`, the latter checked to elaborate with the `AutoMetrics` import)
sat in calcs that the golf replaced by a single term.

## Suggestions that closed but were not frozen

- `catcrypt_grind` is an unknown tactic without the temporary import in every file where it was
  suggested: UCConcrete 435 (whole, `ofGame_run_eq`) and 426 (second pass); UCDSL 102, 128;
  RoundMCompDist 242, 259 (second pass 211, 228); RoundM 171; SigmaUCZK 200; CBCMode 300, 328, 330,
  332; Pedersen `pedersen_binding_le_dlog` (whole, about 8 lines in place of 18); CPAFromPRF 481.
- `aesop (rule_sets := [CatCryptRel]) ..`: "no such rule set" without the import: Bridge
  `rHoare_of_code_eq`, `rHoare_of_eval_eq` (whole; second pass 97, 103); PackageEquiv 285; PureCode
  81-84; Commitment `mask_game_isPure` (whole; second pass 218); CPAFromPRF `bijCpa_game_isPure`.
- `bind_vcgen` unknown without the import: RoundM `RoundM.flattenAll_zero` (whole), second pass
  RoundM 168 and RoundMCompDist 74, 206.
- PackageEquiv 255: the suggestion itself calls `catcrypt_auto`
  (`first | exact advantage_zero_of_rHoare _ _ (by catcrypt_auto) _ | ..`).
- `hop_chain` in a file that is not I-ok: UCDSL `sdist_game_hop₂`, `sdist_game_hop₃`,
  `sdist_game_hop₄` (whole) and steps 170, 181.
- Unused-simp-argument warnings: ReflectUCHelpers 102, 106, 208 (second pass 205); ChaumPedersen
  284; CPAFromPRF 487 and `PRFEncScheme.slice_eq` (whole); Cryptobox 301.
- `rfl` proofs of `@[simp]` equation lemmas, not replaced although a suggestion closed them:
  RoundM `RoundM.flatten_zero`, `RoundM.flatten_succ` (`unfold RoundM.flatten; grind`, elaborates
  without the import), `RoundM.flattenAll_zero`; UCDSL `UCProtocol.ofGame_apply` (`bind_vcgen`).
  A tactic proof would be longer and the lemmas would stop being `rfl` lemmas for `dsimp`. This
  departs from the instruction to freeze every whole-proof suggestion.

## Positions where `catcrypt_auto?` failed (goal shape named by the error)

- Crypto/UCConcrete: `DistC_const_iff` whole: other; `DistC_of_isPure_advantageA` whole: other;
  `UCEmulatesCSim_of_isPure_advantageA` whole: other; steps 112, 116, 400, 455: distance
  inequality (`hop_chain`: left side `absDiff (prTrue ..) (prTrue ..)` not a registered distance);
  steps 393, 397: other.
- Crypto/UCDSL: `UCEmulates_of_isPure_advantage`, `UCEmulates_of_game_eq`,
  `UCEmulates_of_game_sdist`, `UCEmulates_of_isPure_advantageA`, `UCEmulates_game_hop₂`,
  `uc_alg_of_sdist` whole: other; step 140: distance inequality.
- Crypto/UCMonad/RoundMCompDist: `flattenAll_liftSPComp`, `flattenAll_done`,
  `roundm_flattenAll_mapSum_step` whole and steps 79, 82, 245: SPComp equality.
- Crypto/UCMonad/RoundM: `RoundM.bind'_zero`, `RoundM.bind'_succ`, `RoundM.hbind_succ` whole:
  other; `flattenAll_bind` whole: SPComp equality.
- Crypto/ZK/SigmaUCZK: `sigma_view_eq` whole and step 201: SPComp equality.
- Deep/Bridge: `DeepRHoare_iff` whole: other.
- Deep/OracleGamePackage: `oracleGame_advantage_eq_shallow` whole and step 184: other.
- Deep/PackageEquiv: `DeepPackage.link_evalWith_eq` whole and step 144: SPComp equality;
  `DeepPackage.BehavEquiv.advantage_link_congr` whole: other;
  `DeepPackage.BehavEquiv.rHoare_evalOp` whole: relational.
- Deep/PureCode: `eval_isPure_of_stateFree` whole: side condition (IsPure).
- Deep/ReflectUCHelpers: `spcomp_eq_of_isPure_coupling` whole and step 107: SPComp equality;
  `UCEmulates_of_boolGame_sdist`, `sdist_ofOracle_zero`, `uc_ofOracle` whole: other; step 130:
  distance inequality.
- Examples/BasicHash: `unlink_real_always_true` whole and step 215: SPComp equality.
- Examples/CBCMode: `cbc_game_eq`, `cbc_ideal_inner`, `cbc_ideal_game_uniform` whole and step 289:
  SPComp equality; `cbc_indcpa_coupling` whole: relational; `cbc_indcpa_bound` whole and step 206:
  other; step 326: distance inequality.
- Examples/ChaumPedersen: `chaumPedersen_SHVZK_visible` whole: other.
- Examples/CoinToss: `add_uniform_eq_uniform` whole and step 73: other; `inner_eq` whole and step
  81: SPComp equality.
- Examples/Commitment: `maskComm_hiding_coupling` whole and step 169: relational;
  `mask_sdist_zero`, `mask_deepnom_forward_eq_adv` whole and step 273: other.
- Examples/Commitments/Pedersen: `commit_game_eq` whole and step 144: SPComp equality.
- Examples/CPAFromPRF: `bijCPA_game_eq`, `PRFEncScheme.indcpa_game_eq` whole: SPComp equality;
  `bijCPA_indcpa_coupling` whole: relational; `bijCpa_sdist_zero`, `cpa_from_prf_bound` whole and
  steps 194, 535: other; `PRFEncScheme.indcpa_otp_hop` whole and step 571: distance inequality.
- Examples/Cryptobox/Cryptobox: `cryptobox_security` whole: other.

## Golf (step 2), by file

- Crypto/UCConcrete: `DistC.comp_right` (term `simpa`), `UCEmulatesC_iff_exists_sim`
  (`Classical.skolem`), `UCEmulatesC.mono` (`Exists.imp`).
- Crypto/UCDSL: five proofs to single `exact` terms; `UCEmulates_of_game_eq` via `subst h`.
- Crypto/UC: seven proofs (`cases <;> simp`, term-style `exact`).
- Crypto/UCLevels: nine proofs to term-style `exact`; a calc replaced by `le_trans`.
- Crypto/UCMonad: eleven proofs (`rw; simp` -> `simp [..]`, calc -> `le_trans`, term-style `exact`).
- Crypto/UCMonad/RoundMCompDist: `roundm_distComp_comm`, `roundm_distComp_triangle`,
  `roundm_distComp_bind_right` (two symmetric branches merged), `L2_iff_L1_RoundM`.
- Crypto/UCMonad/RoundM: `roundM_pure_bind`, `roundM_bind_done`, `mapSumRoundM_pure_pure`,
  `mapSumRoundM_pure_kleisli`.
- Crypto/UCMonad/SDistrInstance: eight proofs (calcs to `max_le`/`iSup₂_le`, have-equations to
  `rw [SDistr.bind_assoc]`).
- Crypto/UCMonad/SPCompInstance: `mapSumSP_pure_pure`, `sdist_mapSumSP_le`.
- Crypto/ZK/SigmaUCZK: `sigma_view_eq` (`simpa using`), `sigma_uc_zk_secure`.
- Deep/Bridge: four proofs. Deep/Eval: five structural inductions with `| _ => rfl`.
- Deep/OracleGamePackage: `runPkg_ofOracle_zero` (one `simp`).
- Deep/PackageEquiv: `link_congr_right` (an unused `have := Classical.dec ..` removed),
  `link_congr_left`, `advantage_link_congr`, `rHoare_evalOp`.
- Deep/ReflectUCHelpers: `spcomp_eq_of_isPure_coupling`.
- Examples: BasicHash `unlink_real_always_true`; CBCMode `cbc_indcpa_bound` (middle hop);
  ChaumPedersen `chaumPedersen_SHVZK_visible` (two `show` lines, a `have`, four bullets);
  CoinToss `add_uniform_eq_uniform`, `coinToss_eq`; Pedersen `pedersen_binding_le_dlog`;
  CPAFromPRF `cpa_from_prf_bound` (20-line calc -> 2 lines); Cryptobox `ae_hybrid_bound`,
  `cryptobox_security`.

Warnings in the changed files after the pass are the pre-existing ones only: Crypto/UC (universe
linter on `UCSpec`), Crypto/UCLevels (three overlapping-instance-parameter warnings on
signatures), Deep/Eval (nine unused binder names `op` in statements, the same nine as before),
Examples/Commitment (duplicated namespace in `CommScheme.Commitment`).

## Files without step 1, or unchanged

- Import cycle with the temporary import (step 1 skipped, golf only): Crypto/UC.lean,
  Crypto/UCMonad.lean, Crypto/UCMonad/SPCompInstance.lean, Deep/Eval.lean (`lake setup-file` reports
  a build cycle; e.g. Crypto/NomPkgBridge imports Crypto.UC and is in the closure of
  Tactics/AutoDispatchExt).
- No statement matches the filter: Crypto/UCLevels.lean, Crypto/UCMonad/SDistrInstance.lean (and
  Crypto/UCMonad.lean).
- Unchanged: Deep/PureCode.lean (no suggestion survived, no golf found), Deep/Strategy.lean
  (documentation only, no declarations), Examples/Commitments/CommitmentScheme.lean and
  Examples/Cryptobox/AE.lean (no theorems).

## Vacuity-sweep files

Of the listed vacuity-sweep files, only Examples/Cryptobox/** is in this task's list.
Examples/Cryptobox/Cryptobox.lean received proof-only edits (`ae_hybrid_bound`,
`cryptobox_security`), statements unchanged; Examples/Cryptobox/AE.lean is unchanged. No file under
CatCryptCore/Consensus/ was edited.

## Interface queue

1. `catcrypt_grind` (Tactics/AutoSets) is not in scope in any of the processed modules without
   `AutoDispatchExt`; it is the arm behind most surviving suggestions (16 positions above). Either
   the tactic needs a home low in the import graph, or the dispatcher could report `grind` with
   the same arguments when that also closes the goal.
2. The aesop rule set `CatCryptRel` is not visible without the import (12 positions); suggestions
   naming it cannot be frozen in these modules.
3. `bind_vcgen` is not in scope in Crypto/UCMonad/RoundM and RoundMCompDist (not tested in
   Crypto/UCDSL, where its only suggestion was on an `rfl` lemma).
4. The zero-advantage arm of `AutoDispatchExt` prints a suggestion that calls `catcrypt_auto`
   itself (PackageEquiv 255); the printed suggestion should contain the inner closing tactic.
5. Suggestions keep `simp_all` arguments that `simp_all` does not use; the unused-argument linter
   rejected 8 of them. Pruning unused arguments before printing would make them freezable.
6. Import cycles: Crypto/UC, Crypto/UCMonad, Crypto/UCMonad/SPCompInstance and Deep/Eval lie in the
   import closure of Tactics/AutoDispatchExt, so the dispatcher cannot run there.
7. `absDiff (prTrue ..) (prTrue ..) ≤ _` (the unfolded `Env.gap`/`DistC` goals of
   Crypto/UCConcrete) is not read as a registered distance; `sdistD`/`prTrueD` (SDistr) and
   `ucSdist`/`ucCdist` (UCMonadMetric) carry no `@[hop_metric]` registration either.
8. Equalities between advantages (`DeepNomAdvantage .. = Advantage ..`,
   `∀ A, AdvantageA .. = 0` in `DeepPackage.BehavEquiv.advantage_link_congr`) were classified as
   shape "other".
9. The procedure's whole-proof step should exclude `:= rfl` proofs of `@[simp]` lemmas (RoundM,
   UCDSL); replacing them changes their `dsimp` behaviour.
10. The statement filter matches no theorem in UCLevels, UCMonad and SDistrInstance, whose
    statements use `ucSdist`, `ucCdist` and `sdistD`; extending the filter to these heads would
    need the registrations of item 7 to be useful.

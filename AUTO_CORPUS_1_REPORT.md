# AUTO-C corpus pass, core batch 1

Branch `work/auto-corpus-1`, created from `origin/work/auto-corpus` (751637d). Files: the 27
modules of the task list, in the listed order, one commit per changed file. Toolchain Lean 4.33.1;
Mathlib was replayed from the cache and not rebuilt.

## Summary

- Files changed: 18 of 27; 48 lines added, 120 deleted (`git diff --shortstat origin/work/auto-corpus`).
- Theorems closed whole by one frozen `catcrypt_auto` suggestion: 2
  (`Core/StdDoBridge.bind_apply_some_ne_zero_iff`, `Crypto/Assumptions/tSDH.tSDH_Advantage_eq_ext`).
- Closing steps replaced by a frozen suggestion: 13.
- Golf edits kept: 26 recorded edits in 14 files, and 8 hunks in `Crypto/BadEvent.lean`.
- Positions where `catcrypt_auto?` failed with an error naming a goal shape or argument problem: 53
  (shapes: other 33, IsPure/NoFail side condition 8, SPComp equality 6, distance inequality 5,
  relational rHoare judgment 1).
- No frozen suggestion uses `hop_chain`, `sum_atoms_le` or `gcongr_unfold`; no file keeps
  `public import CatCryptCore.Tactics.AutoMetrics`. The temporary import of
  `CatCryptCore.Tactics.AutoDispatchExt` is removed from every file.
- No statement, definition, import, attribute or declaration name changed; no declaration was added
  or removed; no `sorry` or `native_decide` was introduced (`git diff` contains no changed line with
  `import`, `theorem`, `lemma`, `def`, `@[`, `sorry` or `native_decide`).
- No deprecation warning occurs in any of the 27 files, so step 3 made no change.
- `lake build` of the 27 modules succeeds (2776 jobs). Warnings per file equal those of the base
  branch: ProtBicat 21, StdDoBridge 3, CryptoWord 3, CR 2, DDH 1, PRP 1, all others 0.

## Method

Step 1 replaced, for every theorem whose statement mentions `rHoare`, `Advantage`, `AdvantageA`,
`sdist` (including `ucSdist`), `prTrue`, `prEvent`, `IsPure`, `NoFail` or `SPComp`, the whole tactic
proof by `catcrypt_auto? [cited]` (the hypotheses of the statement and the lemma names in the bracket
lists and `exact`/`apply` heads of the old proof; without arguments when an argument did not
elaborate). Where no suggestion closed the theorem, `catcrypt_auto?` was tried at each closing step:
the last tactic of each branch and each `calc` step, with the arguments of the replaced step.
Theorems with term-mode proofs were not tried whole.

Freezing rule applied to closing steps, in addition to "not longer in lines": a suggestion was not
frozen where the old step is a direct proof term (`exact`, `apply`, `rfl`, a `calc` step given by a
term), since the suggestion there only wraps the same term in heavier automation; nor where the
suggestion equals the old step. Suggestions using `catcrypt_grind`, the `CatCryptRel` rule set or
other arms of the leaf modules were not frozen, since they do not elaborate without the temporary
import. Unused simp arguments in frozen suggestions were removed as the linter reported them.

Step 2 tried to replace whole tactic proofs, branch bodies, `calc` blocks and two- or three-line
closing tails by one `simp`, `simp only`, `simp_all` or `grind` call with the lemmas the block cites,
or by `linarith`/`gcongr` for inequality `calc` blocks; a replacement was kept when its declaration
elaborated without error and without a new warning. Every kept edit was then checked by
`lake build` of the module.

Trials ran through the Lean server. Two properties of that setup were found during the run and
handled: diagnostics returned after 15 s without server activity were incomplete, and after an
in-place update of an open document the server reported no error for a proof that fails on a fresh
elaboration (observed on `RSA_Game_Real_isPure`). From `Crypto/Assumptions/RSA.lean` on, every trial
elaborated a fresh temporary copy of the file and waited for completion. Step 1 of the files before
RSA was repeated in that mode; the repetition found no further suggestion at an unedited position,
and its data are the ones reported below. The lake build was the acceptance test throughout; two
candidate edits accepted by the early trials (in `Crypto/Advantage.lean` and `RSA.lean`) failed it
and were dropped. For `Crypto/BadEvent.lean` two runs overlapped, so its per-edit record is
incomplete; its committed diff builds and is described by its hunks.

## Skipped steps

- Step 1 is skipped for `Core/Code.lean`, `Crypto/Advantage.lean` and `Crypto/BadEvent.lean`:
  `CatCryptCore.Tactics.AutoDispatchExt` imports each of them transitively, so the temporary import
  is circular (the server reports the declarations of the file as already declared). Steps 2 and 3
  were carried out.
- No file was skipped entirely. Nine files have no change: CoCDH, DDH, DLGroupParam, DL, GapDH,
  MAC, PRP, PedersenUC, CryptoWord (no frozen suggestion qualified and no golf candidate elaborated).

## Files of the vacuity-sweep findings

- `CatCryptCore/Crypto/BadEvent.lean`: proof-only edits (8 hunks), statements unchanged.

No other file of the batch belongs to that list. `CatCryptCore/Consensus/**` was not edited.

## Interface queue

1. `Crypto/Assumptions/CR.lean`, class `CRImpliesPre`: its field `bound` states
   `Pre_Advantage h A ≤ ε` for every adversary under the hypotheses `h_compress` and `hCR`, which its
   type does not use (unused-variable warnings at 278:17 and 279:5); `CRSecure_implies_PreSecure`
   only applies this field, so the theorem restates an assumed bound of the form `∀ A, Adv … ≤ ε`.
   The reduction (Katz-Lindell Prop. 8.4) needs a statement change or a proof of the class field.
2. `Category/ProtBicat.lean`: the section variables `[UCMonadBase T] [LawfulMonad T]` overlap (21
   warnings, "`[LawfulMonad T]` may be removed"). Removing the instance changes 21 statements.
3. `Crypto/Assumptions/DDH.lean:98`: the binder `b` of `let ⟨b, g_b⟩ ← D.keygen` in
   `DDH_Game_Real` is unused; renaming it to `_b` changes a definition body.
4. `Crypto/Assumptions/PRP.lean:88`: the argument `x` of `PRP_Ideal` is unused; removing it changes
   a definition signature.
5. `Crypto/CryptoWord.lean:54`: three class-typed definitions of `SampleableType` are
   semireducible (`@[instance_reducible]` suggested); this is an attribute change.
6. `Core/StdDoBridge.lean`: three uses of `mvcgen` produce the experimental-tactic warning.
7. `catcrypt_auto` cannot be used in `Core/Code.lean`, `Crypto/Advantage.lean` and
   `Crypto/BadEvent.lean` because `AutoDispatchExt` depends on them; their game lemmas could only be
   covered by moving the dispatcher below them or by a lighter dispatch module.
8. In the `Assumptions` files the `IsPure` goals of the game definitions are closed by
   `aesop (rule_sets := [CatCryptRel])` suggestions (DDH, GapDH, MAC, AEAD, OWF, PRP), which cannot
   be frozen without importing `AutoSets`; `simp_all [SPComp.bind_isPure, SPComp.pure_isPure]`
   closes the same goals in several files without it (CDH, ODH, OWF, qSDH, RSA). A plain-`simp`
   attribute set for these combinators would let the suggestion be frozen.

## Per file

### `CatCryptCore/Category/ProtBicat.lean`

Lines added/deleted: 3/3.
Theorems in scope of step 1: 1.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 3:
- `sdist_hcomp` (line 593): `| inl o => simp [wrap]` -> `| inl o => simp_all [wrap]`
- `sdist_hcomp` (line 594): `| inr j => simp [wrap]` -> `| inr j => simp_all [wrap]`
- `sdist_hcomp` (line 595): `| inr i => simp [K, UCMonadBase.ucMapSum_inr, pure_bind, wrap]` -> `| inr i => simp_all [K, UCMonadBase.ucMapSum_inr, pure_bind, wrap]`
Golf edits kept: 0.
Suggestions found but not frozen, by reason: term position: 2; uses sum_atoms_le in a file not marked I-ok: 1; suggestion equals the old step: 3.
- `sdist_hcomp` (line 605): `sum_atoms_le` (uses sum_atoms_le in a file not marked I-ok)
Positions where `catcrypt_auto?` failed: 1.
- `sdist_hcomp`, whole proof: other

### `CatCryptCore/Core/Code.lean`

Lines added/deleted: 4/9.
Step 1 skipped: the temporary import of `CatCryptCore.Tactics.AutoDispatchExt` is circular (that module imports this one transitively; with the import Lean reports the declarations of this file as already declared).
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 4:
- `bind_sample_bijection` (whole, lines 246-247, 2 lines): -> `simp [sample_bind_equiv]`
- `sample_prod_eq` (tail, lines 149-150, 2 lines): -> `simp only [SDistr.bind_assoc, SDistr.pure_bind, this.symm]`
- `bind_isPure` (tail, lines 277-279, 3 lines): -> `simp_all [SDistr.pure_bind]`
- `foldM_append` (tail, lines 350-351, 2 lines): -> `simp_all [SPComp.bind_assoc]`

### `CatCryptCore/Core/GenHeap.lean`

Lines added/deleted: 5/8.
Theorems in scope of step 1: 3.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 2:
- `preservesOutside_gget` (line 255): `rw [hne.1.2]` -> `simp_all [hne.1.2]`
- `incr_twice_empty` (line 290): `simp [incr, SPComp.bind, SPComp.gget, SPComp.gset, SPComp.pure, Cat...` -> `simp_all [incr, SPComp.bind, SPComp.gget, SPComp.gset, SPComp.pure, CatCrypt....`
Golf edits kept: 2:
- `preservesOutside_gset` (tail, lines 262-263, 2 lines): -> `simp_all [hne.1.2, Heap.gset_lookup_of_ne]`
- `gdecode_eq_decode` (branch, lines 86-88, 3 lines): -> `· grind [gdecode, Heap.decode]`
Suggestions found but not frozen, by reason: suggestion equals the old step: 2.
Positions where `catcrypt_auto?` failed: 1.
- `incr_twice_empty`, whole proof: other

### `CatCryptCore/Core/GenHeapRandomOracle.lean`

Lines added/deleted: 1/2.
Theorems in scope of step 1: 5.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 1:
- `query_consistent` (line 166): `rw [query_apply_cached D R id x h r hc, SDistr.pure_bind, SDistr.pu...` -> `simp_all [query_apply_cached D R id x h r hc, SDistr.pure_bind]`
Golf edits kept: 0.
Suggestions found but not frozen, by reason: needs a leaf module: 2; suggestion equals the old step: 2.
- `queryStep_of_cached` (line 93): `(unfold CatCrypt.Core.RandomOracle.queryStep; catcrypt_grind)` (needs a leaf module (catcrypt_grind))
- `queryStep_of_fresh` (line 99): `(unfold CatCrypt.Core.RandomOracle.queryStep; catcrypt_grind)` (needs a leaf module (catcrypt_grind))
Positions where `catcrypt_auto?` failed: 5.
- `query_consistent`, whole proof: SPComp equality
- `query_after_program`, whole proof: SPComp equality
- `rHoare_query_after_program`, whole proof: relational rHoare judgment
- `query_after_program`, line 185: other
- `query_consistent`, line 169: other

### `CatCryptCore/Core/StdDoBridge.lean`

Lines added/deleted: 4/19.
Theorems in scope of step 1: 13.
Theorems closed whole by one frozen suggestion: 1:
- `bind_apply_some_ne_zero_iff`: `grind [SPComp.bind_def, SDistr.bind_apply_some_ne_zero_iff]`
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 3:
- `bind_apply_none_ne_zero_iff` (whole, lines 127-134, 8 lines): -> `simp [SPComp.bind_def, SDistr.bind_apply_none_ne_zero_iff]`
- `_root_.CatCrypt.Prob.SDistr.bind_apply_none_ne_zero_iff` (branch, lines 101-103, 3 lines): -> `| none => grind`
- `fail` (branch, lines 352-353, 2 lines): -> `· grind`
Suggestions found but not frozen, by reason: old step is a direct proof term: 23; term position: 4.
Positions where `catcrypt_auto?` failed: 12.
- `wpProp_iff_forall_support`, whole proof: other
- `triple_of_forall`, whole proof: other
- `triple_mayThrow_iff`, whole proof: other
- `triple_noThrow_iff`, whole proof: other
- `triple_noThrow_true_iff_noFail`, whole proof: other
- `isPure_wpProp_iff`, whole proof: other
- `get`, whole proof: other
- `set`, whole proof: other
- `sample`, whole proof: other
- `fail`, whole proof: other
- `purePrim`, whole proof: other
- `triple_noThrow_iff`, line 245: other

### `CatCryptCore/Crypto/Advantage.lean`

Lines added/deleted: 3/8.
Step 1 skipped: the temporary import of `CatCryptCore.Tactics.AutoDispatchExt` is circular (that module imports this one transitively; with the import Lean reports the declarations of this file as already declared).
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 4:
- `prTrue_bind_sample_Bool` (tail, lines 219-220, 2 lines): -> `simp [add_comm]`
- `advantage_zero_of_inv` (tail, lines 170-171, 2 lines): -> `simp [hAeq, liftR_refl]`
- `weighted_sum_le` (calc, lines 291-292, 2 lines): -> `simp_all`
- `advantageA_isPure_bind` (tail, lines 379-381, 3 lines): -> `simp [ENNReal.tsum_comm, ENNReal.tsum_mul_left]`

### `CatCryptCore/Crypto/Assumptions/AEAD.lean`

Lines added/deleted: 2/10.
Theorems in scope of step 1: 7.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 2:
- `sample_bind_const` (whole, lines 186-193, 8 lines): -> `simp`
- `AEAD_CPA_le_CCA` (tail, lines 202-203, 2 lines): -> `simp only [SPComp.monad_bind_eq, SPComp.pure_bind, sample_bind_const, le_refl]`
Suggestions found but not frozen, by reason: needs a leaf module: 5; old step is a direct proof term: 2.
- `AEAD_Game_Real_isPure` (line 115): `(unfold CatCrypt.Crypto.Assumptions.AEAD_Game_Real; simp only [CatCrypt.Core....` (needs a leaf module (CatCryptRel))
- `AEAD_Game_Ideal_isPure` (line 122): `(unfold CatCrypt.Crypto.Assumptions.AEAD_Game_Ideal; simp only [CatCrypt.Core...` (needs a leaf module (CatCryptRel))
- `AEAD_CCA_Game_Real_isPure` (line 214): `(unfold CatCrypt.Crypto.Assumptions.AEAD_CCA_Game_Real; simp only [CatCrypt.C...` (needs a leaf module (CatCryptRel))
- `AEAD_CCA_Game_Ideal_isPure` (line 225): `(unfold CatCrypt.Crypto.Assumptions.AEAD_CCA_Game_Ideal; simp only [CatCrypt....` (needs a leaf module (CatCryptRel))
- `aead_keyed_real_isPure` (line 274): `(unfold CatCrypt.Crypto.Assumptions.aead_keyed_real; aesop (rule_sets := [Cat...` (needs a leaf module (CatCryptRel))
Positions where `catcrypt_auto?` failed: 3.
- `sample_bind_const`, whole proof: SPComp equality
- `AEAD_CPA_le_CCA`, whole proof: other
- `sample_bind_const`, line 186: SPComp equality

### `CatCryptCore/Crypto/Assumptions/CDH.lean`

Lines added/deleted: 2/3.
Theorems in scope of step 1: 3.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 1:
- `dl_le_cdh_ddh` (line 181): `simp only [ssprove_simpl]` -> `(simp only [CatCrypt.Core.SPComp.monad_bind_eq]; bind_vcgen)`
Golf edits kept: 1:
- `CDH_Game_isPure` (tail, lines 108-109, 2 lines): -> `simp_all [SPComp.bind_isPure, SPComp.pure_isPure]`
Suggestions found but not frozen, by reason: old step is a direct proof term: 1; term position: 1; needs a leaf module: 1.
- `dl_le_cdh_ddh` (line 183): `catcrypt_grind` (needs a leaf module (catcrypt_grind))
Positions where `catcrypt_auto?` failed: 3.
- `CDH_Game_isPure`, whole proof: IsPure/NoFail side condition
- `dl_le_cdh_ddh`, whole proof: other
- `cdh_secure_implies_dl_secure`, whole proof: other

### `CatCryptCore/Crypto/Assumptions/CoCDH.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 0.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.

### `CatCryptCore/Crypto/Assumptions/CR.lean`

Lines added/deleted: 2/4.
Theorems in scope of step 1: 1.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 2:
- `CRSecure_implies_TCRSecure` (line 260): `exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, Ne.symm h2⟩, fun ⟨h1, h2⟩ ...` -> `grind`
- `CRSecure_implies_TCRSecure` (line 264): `rw [hgame]` -> `simp_all`
Golf edits kept: 1:
- `CRSecure_implies_TCRSecure` (tail, lines 259-260, 2 lines): -> `grind`
Positions where `catcrypt_auto?` failed: 1.
- `CRSecure_implies_TCRSecure`, whole proof: SPComp equality

### `CatCryptCore/Crypto/Assumptions/DDH.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 2.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.
Suggestions found but not frozen, by reason: needs a leaf module: 2.
- `DDH_Game_Real_isPure` (line 121): `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsa...` (needs a leaf module (CatCryptRel))
- `DDH_Game_Ideal_isPure` (line 130): `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsa...` (needs a leaf module (CatCryptRel))
Positions where `catcrypt_auto?` failed: 2.
- `DDH_Game_Real_isPure`, whole proof: IsPure/NoFail side condition
- `DDH_Game_Ideal_isPure`, whole proof: IsPure/NoFail side condition

### `CatCryptCore/Crypto/Assumptions/DLGroupParam.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 0.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.

### `CatCryptCore/Crypto/Assumptions/DL.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 0.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.

### `CatCryptCore/Crypto/Assumptions/GapDH.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 2.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.
Suggestions found but not frozen, by reason: needs a leaf module: 2.
- `GapDH_Game_Real_isPure` (line 133): `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsa...` (needs a leaf module (CatCryptRel))
- `GapDH_Game_Ideal_isPure` (line 142): `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsa...` (needs a leaf module (CatCryptRel))
Positions where `catcrypt_auto?` failed: 2.
- `GapDH_Game_Real_isPure`, whole proof: IsPure/NoFail side condition
- `GapDH_Game_Ideal_isPure`, whole proof: IsPure/NoFail side condition

### `CatCryptCore/Crypto/Assumptions/MAC.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 3.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.
Suggestions found but not frozen, by reason: old step is a direct proof term: 2; needs a leaf module: 4.
- `MAC_Game_Ideal_isPure` (line 108): `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }) (add unsa...` (needs a leaf module (CatCryptRel))
- `MAC_Game_Real_isPure` (line 99): `(unfold CatCrypt.Crypto.Assumptions.MAC_Game_Real; simp only [CatCrypt.Core.S...` (needs a leaf module (CatCryptRel))
- `MAC_Game_Ideal_isPure` (line 106): `(unfold CatCrypt.Crypto.Assumptions.MAC_Game_Ideal; simp only [CatCrypt.Core....` (needs a leaf module (CatCryptRel))
- `mac_keyed_real_isPure` (line 143): `(unfold CatCrypt.Crypto.Assumptions.mac_keyed_real; aesop (rule_sets := [CatC...` (needs a leaf module (CatCryptRel))

### `CatCryptCore/Crypto/Assumptions/ODH.lean`

Lines added/deleted: 3/6.
Theorems in scope of step 1: 3.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 1:
- `odh_of_ddh_prf` (line 244): `rw [hreal, hideal]` -> `simp_all`
Golf edits kept: 2:
- `ODH_Game_Real_isPure` (tail, lines 153-155, 3 lines): -> `simp_all [SPComp.bind_isPure, SPComp.pure_isPure]`
- `ODH_Game_Ideal_isPure` (tail, lines 164-165, 2 lines): -> `simp_all [SPComp.bind_isPure, SPComp.pure_isPure]`
Suggestions found but not frozen, by reason: old step is a direct proof term: 2; term position: 2.
Positions where `catcrypt_auto?` failed: 4.
- `ODH_Game_Real_isPure`, whole proof: IsPure/NoFail side condition
- `ODH_Game_Ideal_isPure`, whole proof: IsPure/NoFail side condition
- `odh_of_ddh_prf`, whole proof: other
- `odh_of_ddh_prf`, line 242: other

### `CatCryptCore/Crypto/Assumptions/OWF.lean`

Lines added/deleted: 1/2.
Theorems in scope of step 1: 1.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 1:
- `OWF_Game_isPure` (tail, lines 107-108, 2 lines): -> `simp_all [SPComp.bind_isPure, SPComp.pure_isPure]`
Suggestions found but not frozen, by reason: needs a leaf module: 1.
- `OWF_Game_isPure` (line 105): `(unfold CatCrypt.Crypto.Assumptions.OWF_Game; simp only [CatCrypt.Core.SPComp...` (needs a leaf module (CatCryptRel))

### `CatCryptCore/Crypto/Assumptions/PRP.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 1.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.
Suggestions found but not frozen, by reason: needs a leaf module: 1.
- `PRP_Real_isPure` (line 188): `(unfold CatCrypt.Crypto.Assumptions.PRP_Real; simp only [CatCrypt.Core.SPComp...` (needs a leaf module (CatCryptRel))

### `CatCryptCore/Crypto/Assumptions/qSDH.lean`

Lines added/deleted: 1/2.
Theorems in scope of step 1: 1.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 1:
- `qSDH_Game_isPure` (tail, lines 153-154, 2 lines): -> `simp_all [SPComp.bind_isPure, SPComp.pure_isPure]`
Suggestions found but not frozen, by reason: old step is a direct proof term: 1.

### `CatCryptCore/Crypto/Assumptions/RSA.lean`

Lines added/deleted: 1/2.
Theorems in scope of step 1: 1.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 1:
- `RSA_Game_Real_isPure` (tail, lines 104-105, 2 lines): -> `simp_all [SPComp.bind_isPure, SPComp.pure_isPure]`
Suggestions found but not frozen, by reason: old step is a direct proof term: 1.
Positions where `catcrypt_auto?` failed: 1.
- `RSA_Game_Real_isPure`, whole proof: IsPure/NoFail side condition

### `CatCryptCore/Crypto/Assumptions/tSDH.lean`

Lines added/deleted: 1/1.
Theorems in scope of step 1: 1.
Theorems closed whole by one frozen suggestion: 1:
- `tSDH_Advantage_eq_ext`: `simp_all [tSDH_Advantage, tSDH_Advantage_ext, tSDH_Game, tSDH_Game_ext]`
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.

### `CatCryptCore/Crypto/BadEvent.lean`

Lines added/deleted: 9/31.
Step 1 skipped: the temporary import of `CatCryptCore.Tactics.AutoDispatchExt` is circular (that module imports this one transitively; with the import Lean reports the declarations of this file as already declared).
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 8 hunks of the commit diff (the per-edit record of this file is incomplete, see the method notes); every hunk replaces a block by one `simp`, `simp_all` or `grind` call.

### `CatCryptCore/Crypto/BLSSig/Security.lean`

Lines added/deleted: 1/2.
Theorems in scope of step 1: 2.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 1:
- `blsForgeGame_eq_cocdh` (tail, lines 191-192, 2 lines): -> `simp [zpowZMod₁_zpowZMod₁, mul_comm]`
Suggestions not frozen because they did not elaborate without the temporary import: 1.
- `blsForgeAdvantage_eq_cocdh` (line 203): `(unfold CatCryptCore.Crypto.BLSSig.blsForgeAdvantage; unfold CatCryptCore.Cry...`: unexpected identifier; expected ')'
Positions where `catcrypt_auto?` failed: 1.
- `bls_forge_reduces_to_cocdh`, whole proof: other

### `CatCryptCore/Crypto/Commitment/PedersenUC.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 1.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.
Positions where `catcrypt_auto?` failed: 1.
- `pedersen_view_eq`, whole proof: SPComp equality

### `CatCryptCore/Crypto/CryptoWord.lean`

Lines added/deleted: 0/0.
Theorems in scope of step 1: 0.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 0.
Golf edits kept: 0.

### `CatCryptCore/Crypto/DummyAdversary.lean`

Lines added/deleted: 2/4.
Theorems in scope of step 1: 8.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 1:
- `identity_sim_fails` (line 254): `simp [absDiff]` -> `(clear hD; simp_all [absDiff])`
Golf edits kept: 2:
- `specialized_iff_general` (branch, lines 203-204, 2 lines): -> `· simp_all [ucEmulates_of_general]`
- `identity_sim_fails` (tail, lines 253-254, 2 lines): -> `simp [h1, h2, ForkingLemma.prTrue_pure_bool, absDiff]`
Suggestions not frozen because they did not elaborate without the temporary import: 1.
- `mapSum_pure_comp_absorb` (line 101): `(unfold CatCrypt.Crypto.mapSum; grind [SPComp.map, SPComp.pure_bind, SPComp.b...`: warning: this parameter is redundant, environment already contains `CatCrypt.Core.SPCom...
Suggestions found but not frozen, by reason: needs a leaf module: 3; old step is a direct proof term: 3.
- `sdist_dummy_absorb` (line 123): `catcrypt_grind [mapSum_pure_comp_absorb S A, SPComp.bind_assoc]` (needs a leaf module (catcrypt_grind))
- `identity_sim_fails` (line 250): `catcrypt_grind [π, SPComp.pure_bind]` (needs a leaf module (catcrypt_grind))
- `identity_sim_fails` (line 252): `catcrypt_grind [F, SPComp.pure_bind]` (needs a leaf module (catcrypt_grind))
Positions where `catcrypt_auto?` failed: 10.
- `sdist_dummy_absorb`, whole proof: distance inequality
- `emulatesDummy_of_ucEmulates`, whole proof: other
- `dummy_completeness`, whole proof: other
- `ucEmulates_of_general`, whole proof: other
- `general_of_dummy`, whole proof: other
- `specialized_iff_general`, whole proof: other
- `identity_sim_fails`, whole proof: distance inequality
- `specialized_iff_general`, line 202: other
- `specialized_iff_general`, line 204: other
- `identity_sim_fails`, line 257: distance inequality

### `CatCryptCore/Crypto/EasyCryptBridge.lean`

Lines added/deleted: 3/4.
Theorems in scope of step 1: 7.
Theorems closed whole by one frozen suggestion: 0.
Closing steps replaced by frozen suggestions: 2:
- `sdist_zero_of_eq` (line 168): `rw [show f = g from funext h, sdist_self]` -> `simp_all [show f = g from funext h, sdist_self]`
- `module_hybrid_bound` (line 200): `_ = (↑n + 1) * ε := by rw [add_mul, one_mul]` -> `_ = (↑n + 1) * ε := by simp_all [add_mul, one_mul]`
Golf edits kept: 1:
- `pRHL_to_UCEmulates` (tail, lines 77-78, 2 lines): -> `simp [h_eq, UCEmulates_refl]`
Suggestions found but not frozen, by reason: needs a leaf module: 4; old step is a direct proof term: 1; term position: 2.
- `ModuleRefines_refl` (line 112): `(unfold CatCrypt.Crypto.EasyCryptBridge.ModuleRefines; catcrypt_grind [Module...` (needs a leaf module (catcrypt_grind))
- `ModuleRefines_sym` (line 116): `(unfold CatCrypt.Crypto.EasyCryptBridge.ModuleRefines; catcrypt_grind [Module...` (needs a leaf module (catcrypt_grind))
- `pRHL_to_ModuleRefines` (line 176): `catcrypt_grind [pRHL_eq_implies_prog_eq π F h, sdist_self]` (needs a leaf module (catcrypt_grind))
- `module_hybrid_bound` (line 188): `(unfold CatCrypt.Crypto.EasyCryptBridge.ModuleRefines; catcrypt_grind [Module...` (needs a leaf module (catcrypt_grind))
Positions where `catcrypt_auto?` failed: 6.
- `pRHL_eq_implies_prog_eq`, whole proof: other
- `pRHL_to_UCEmulates`, whole proof: other
- `sdist_zero_of_eq`, whole proof: other
- `pRHL_to_ModuleRefines`, whole proof: distance inequality
- `module_hybrid_bound`, whole proof: distance inequality
- `pRHL_to_UCEmulates`, line 78: other


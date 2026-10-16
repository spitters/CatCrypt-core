# Interface bundle report

Branch `work/interface-bundle`, created from `origin/work/auto-corpus` at `cf34750`.
Four items, one commit each, followed by this report. All four items were completed;
no commit was reverted.

## Build

| Build | Result | Jobs | Wall time |
|---|---|---|---|
| `lake build CatCryptCore`, started before the edits were complete (warms the package and library builds; mixed tree) | failed in two modules under edit | 3709 | 471 s |
| `lake build CatCryptCore`, all edits, first attempt | failed: `ExpectationVCGenCore` (see item 2) | — | 145 s |
| `lake build CatCryptCore`, all edits | succeeded | 3711 | 230 s (incremental) |
| `lake build CatCryptCore`, after silencing the `vcgen` warning | succeeded | 3711 | 186 s (incremental) |
| `lake build CatCryptCore` on the committed tree | succeeded, nothing to rebuild | 3711 | 5 s |

The setup script (`cloud-setup.sh`) supplied prebuilt builds of every package except
`iris`, which Lake built. No line `Built Mathlib.` appeared in any build log. The library
build runs with `-E hasSorry`. The changes add no `sorry`, no `native_decide` and no
axiom. The times above are incremental over the first build; no cold build of the whole
library from an empty `.lake/build` was timed.

## Item 1: helper lemmas moved to their defining modules

Commit `4f0cc7c`. Names, statements and proofs are unchanged; the attributes
(`aesop … CatCryptRel`, `@[bound]`, `@[hop_metric]`) stay in `Tactics/AutoSets.lean`
and `Tactics/AutoMetrics.lean`, which import the new locations.

| Declaration | From | To |
|---|---|---|
| `CatCrypt.Core.SPComp.bindOp_isPure` | `Tactics/AutoSets.lean` | `Core/Code.lean` (after `bind_isPure`) |
| `CatCrypt.Crypto.SPComp.bindOp_noFail` | `Tactics/AutoSets.lean` | `Crypto/NomPkgBridge.lean` (after `Assumptions.SPComp.bind_noFail`) |
| `CatCrypt.Crypto.SPComp.pureOp_noFail` | `Tactics/AutoSets.lean` | `Crypto/NomPkgBridge.lean` |
| `CatCrypt.Crypto.AdvantageA_sym` | `Tactics/AutoArms.lean` | `Crypto/Advantage.lean` (after `Advantage_self`) |
| `CatCrypt.Crypto.natCast_le_natCast_of_le` | `Tactics/AutoSets.lean` | `ForMathlib/ENNRealNatCast.lean` (new) |
| `CatCrypt.Crypto.le_natCast_mul_of_one_le` | `Tactics/AutoSets.lean` | `ForMathlib/ENNRealNatCast.lean` (new) |

`AutoPremises.lean` contained no such lemma. The two `ℝ≥0∞` lemmas mention only Mathlib
notions; they keep their `CatCrypt.Crypto` names, which departs from the Mathlib-style
naming of `ForMathlib/`. The docstring of the new module records this, and records that
Mathlib has the content as `Nat.cast_le` and `le_mul_of_one_le_left`. The new module is
not added to the aggregate `CatCryptCore/ForMathlib.lean`.

Imports changed: `Tactics/AutoSets.lean` (+ `CatCryptCore.ForMathlib.ENNRealNatCast`).
Interfaces changed: `Core/Code`, `Crypto/NomPkgBridge` and `Crypto/Advantage` gain one
or two declarations each.

## Item 2: `ExpectationVCGenCore` and three `vcgen` proofs

Commit `8359110`.

- New module `Unary/ExpectationVCGenCore.lean` holds everything of
  `Unary/ExpectationVCGen.lean` except the two examples: the `Lean.Order` instances on
  `ℝ≥0∞` and `ℝ≥0∞ᵒᵈ`, `wpEF` and its lemmas, `instWPMonadSPComp`, `SPCompU`,
  `instWPMonadSPCompU`, the readings `wp_eq_wpEF`, `wp_bot_eq_wpE`, `triple_iff_le_wpE`,
  `SPCompU.wp_eq`, `SPCompU.triple_iff_wpE_le`, `SPCompU.spec_wpE`, and all `@[spec]`
  triples. Its imports are `CatCryptCore.Unary.ExpectationWP`, `Std.Tactic.Do` and
  `Std.Internal.Do`. The third import departs from the specification: `Std.Tactic.Do`
  provides the `vcgen` syntax but not the class `Std.Internal.Do.WPMonad`, which the
  original module obtained through its other imports. `Std.Internal.Do` is a module of the
  Lean toolchain, not of CatCrypt or Mathlib.
- `Unary/ExpectationVCGen.lean` keeps `same_msg_prTrue_vcgen` and
  `prEventComp_bind_step_le_vcgen` and imports `ExpectationVCGenCore`, `ExpectedCost`,
  `Examples.DetCPA` and `Std.Tactic.Do`. It re-exports `ExpectationVCGenCore`, so its
  importers (`ExpectationVCGenExamples`, `ExpectationVCGenLoops`, `Tactics/AutoSets`) are
  unchanged.
- `wpEF_bind` (now in the new module) uses `wpE_add` and `wpE_const_mul`, which were in
  `Unary/ExpectedCost.lean`; `ExpectedCost` must import the new module, so these two lemmas
  moved to `Unary/ExpectationWP.lean` (beside `wpE_mono`), unchanged.
- `spec_wpE_lower` moved from `Unary/ExpectationVCGenExamples.lean` to the new module (it is
  used by the new proof of `ecost_bind`).
- Proofs replaced, statements unchanged:

  | Theorem | Old proof | New proof | Source |
  |---|---|---|---|
  | `CatCrypt.Unary.ecost_bind_le` | 21 lines | 13 lines | `ecost_bind_le_vcgen` |
  | `CatCrypt.Unary.ecost_bind` | 20 lines | 15 lines | `ecost_bind_vcgen` (with `ecost_bind_le` for the upper bound) |
  | `CatCrypt.Crypto.BadEvent.prTrue_union_bound` | 46 lines | 29 lines | `prTrue_union_bound_vcgen` |

  The proofs are taken from `CatCryptCore/Unary/ExpectationVCGenExamples.lean` on
  `origin/work/vcgen-conversions` (commit `6c8137b`), each under
  `set_option mvcgen.warning false in`. The binders of `prTrue_union_bound` that the new
  proof does not use are renamed `_hp₁`, `_hnf₁`, `_hnf₂` (the types are unchanged); its
  docstring now states that only the purity of `bad₂` is used. The other `_vcgen` theorems
  were not added; the existing ones in `ExpectationVCGenExamples.lean` are unchanged.
- Imports changed: `Unary/ExpectationVCGen.lean` (+ `ExpectationVCGenCore`, the rest
  unchanged), `Unary/ExpectedCost.lean` (+ `public meta import
  CatCryptCore.Unary.ExpectationVCGenCore`), `Crypto/BadEvent.lean` (+ private
  `import CatCryptCore.Unary.ExpectationVCGenCore` and `import
  CatCryptCore.Unary.ExpectedCost`; these are needed by the proof only and are not
  re-exported). `ExpectedCost` is needed in `BadEvent` for `wpE_const_le`.

## Item 3: `@[hop_metric]` registrations at definition sites

Commit `ad39492`. Each module imports `CatCryptCore.Tactics.AutoHopRegistry` (Lean only)
publicly and as `meta`.

| Distance | Module | Registered | Test (`Tactics/AutoArmsTest.lean`) |
|---|---|---|---|
| `UCMonad.ucCdist` | `Crypto/UCAdmClass.lean` | `ucCdist_triangle`, `ucCdist_sym` | three hops, one used backwards |
| `CatCrypt.Examples.DiffieHellman.KA_Advantage` | `Examples/DiffieHellman.lean` | the definition (unfolds to `Advantage (KA_Game_Real P D) (KA_Game_Ideal P D)`) | two hops through a middle game, one backwards |
| `CatCrypt.Crypto.KEM.Games.indcpaAdvantage` | `Crypto/KEM/Games.lean` | the definition (an `Advantage` between the games of the two challenge bits) | two hops through a middle game |
| `CatCrypt.Crypto.PKE.Games.indcpaAdvantage` | `Crypto/PKE/Games.lean` | the definition (same form) | two hops, one backwards |

Skipped: `PKE.Games.owcpaAdvantage` is `prTrue (pmfGame (owcpaGame P A)) Heap.empty`,
the success probability of one game, not a distance between two games.

`KA_Advantage` is registered by its definition, which unfolds to an `Advantage`; no
separate equation lemma was added. Imports changed: the four modules above (+
`AutoHopRegistry`), and `Tactics/AutoArmsTest.lean` (+ `Crypto.UCAdmClass`,
`Crypto.KEM.Games`, `Crypto.PKE.Games`, `Examples.DiffieHellman`). The `AGENTS.md`
statement that existing lemmas are tagged in `AutoSets` and not in their defining
module does not cover these registrations, which the task requires at the definition
sites; `AGENTS.md` is unchanged.

## Item 4: vacuous declarations

Commit `36fadba`.

- Deleted `lazyEval_fresh_equiv` (an instance of `rHoare_refl` that did not use its
  freshness hypothesis) and `lazyEval_fresh_pHoare` (a `pHoare` triple with postcondition
  `True`) from `Tactics/LazySampling.lean`. The docstring of `lazyEval_fresh_value_uniform`
  names it as the relational statement of a fresh query and records the two deletions.
- `UCEmulates_of_dummy` (`Crypto/UC.lean`) is now
  `@[deprecated UCEmulates_of_sdist (since := "2026-10-16")] alias UCEmulates_of_dummy :=
  UCEmulates_of_sdist`. Its docstring points to `dummy_completeness` in
  `CatCryptCore.Crypto.DummyAdversary` for dummy-adversary completeness. Its statement has
  changed: it was `∀ view A, ∃ S, sdist … ≤ ε`, and it is now that of `UCEmulates_of_sdist`.
- Deleted `INDCCA_Adv_zero_of_rHoare` (`Crypto/SecurityDefs.lean`), which had no users.
- `PRP_PRF_SwitchingBound` and `PRP_Full_Bound` (`Crypto/Assumptions/PRP.lean`) are
  connected to the adaptive switching game of `Crypto/PRPPRFSwitching.lean` by three
  new theorems:
  - `PRP_PRF_SwitchingBound_eq_div`: `PRP_PRF_SwitchingBound q N = ↑(q(q-1)/2) / ↑N`
    (`q(q-1)` is even);
  - `RF_RP_Advantage_le_PRP_PRF_SwitchingBound`: for a `q`-query adversary,
    `RF_RP_Advantage A ≤ PRP_PRF_SwitchingBound q |R|` (from `RF_RP_Advantage_le`);
  - `PRP_q_Advantage_le_PRP_Full_Bound`: for a `q`-query adversary,
    `PRP_q_Advantage P A ≤ PRP_Full_Bound (PRF_q_Advantage P A) q |R|` (triangle
    inequality through the random-function game).

  The docstrings of both definitions, the module table and `Assumptions/Catalog.lean` name
  these theorems. Imports changed: `Crypto/Assumptions/PRP.lean` (+
  `CatCryptCore.Crypto.PRPPRFSwitching`).

No user of a deleted declaration existed inside CatCrypt-core.

## Declarations that other repositories may use

Only CatCrypt-core was inspected; the other repositories that depend on it could not be
read from this session. Searching their sources for these names will show whether they
are affected.

- Removed: `CatCrypt.LazySampling.lazyEval_fresh_equiv`,
  `CatCrypt.LazySampling.lazyEval_fresh_pHoare` (in `Tactics/LazySampling.lean`), `CatCrypt.Crypto.SecurityDefs.INDCCA_Adv_zero_of_rHoare` (in
  `Crypto/SecurityDefs.lean`).
- Statement changed: `CatCrypt.Crypto.UCEmulates_of_dummy` (deprecated alias of
  `UCEmulates_of_sdist`; uses produce a deprecation warning and, where the old `∀ view`
  form was used, a type error).
- Binder names changed (types unchanged): `CatCrypt.Crypto.BadEvent.prTrue_union_bound`
  (`hp₁`, `hnf₁`, `hnf₂` → `_hp₁`, `_hnf₁`, `_hnf₂`; only calls with named arguments are
  affected).
- Moved, same names. Uses are affected only when the importing module no longer reaches
  the new location: `SPComp.bindOp_isPure`, `SPComp.bindOp_noFail`,
  `SPComp.pureOp_noFail`, `AdvantageA_sym`, `natCast_le_natCast_of_le`,
  `le_natCast_mul_of_one_le`, `wpE_add`, `wpE_const_mul`, `spec_wpE_lower`.
- Moved to `Unary/ExpectationVCGenCore` and re-exported by `Unary/ExpectationVCGen`: all
  declarations of the former `ExpectationVCGen` except the two examples. A module that
  imported `ExpectationVCGen` only for `ExpectedCost` or `Examples.DetCPA` still receives
  them.
- New: `CatCrypt.Crypto.Assumptions.PRP_PRF_SwitchingBound_eq_div`,
  `RF_RP_Advantage_le_PRP_PRF_SwitchingBound`, `PRP_q_Advantage_le_PRP_Full_Bound`; the
  module `CatCryptCore.ForMathlib.ENNRealNatCast`; the module
  `CatCryptCore.Unary.ExpectationVCGenCore`.
- New `@[hop_metric]` registrations (`ucCdist`, `KA_Advantage`, both `indcpaAdvantage`)
  change the behaviour of `hop_chain` and `catcrypt_auto` in importers. A goal that
  previously fell through to another arm may now close by `hop_chain`, and a `catcrypt_auto?`
  suggestion frozen in another repository may name a different arm.

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Aesop
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Bound
public import CatCryptCore.Tactics.AutoSetsDecl
public meta import CatCryptCore.Tactics.CryptoAuto
public import CatCryptCore.Tactics.CryptoAuto
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Unary.ExpectationVCGen
public import CatCryptCore.Unary.Event
public import CatCryptCore.Tactics.LazySampling
public import CatCryptCore.Crypto.NomPkgBridge
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CatCryptCore.Tactics.AutoDispatchCore
public import CatCryptCore.ForMathlib.ENNRealNatCast

/-!
# Automation sets for game proofs

Attribute registrations and closers for game-based proofs whose lemmas are stated in
modules above the theory modules `CatCryptCore.Core.Heap`, `CatCryptCore.Core.Code`,
`CatCryptCore.Relational.Rules` and `CatCryptCore.Crypto.Advantage`, which carry their own
registrations. The `>>=` forms of the `NoFail` combinators are stated beside the
combinators (`SPComp.bindOp_noFail` and `SPComp.pureOp_noFail` in
`CatCryptCore.Crypto.NomPkgBridge`), and the two `ℝ≥0∞` coefficient facts in
`CatCryptCore.ForMathlib.ENNRealNatCast`.

* The Aesop rule set `CatCryptRel` (declared in `CatCryptCore.Tactics.AutoSetsDecl`):
  the `NoFail` combinators for `pure`, `sample` and bind (in `SPComp.bind` and `>>=`
  form) as safe `apply` rules.
* `@[gcongr]` on the monotonicity of the expectation transformers `wpE` and `wpEF`
  in the postcondition and the error term, and of `prEvent` in the event.
* `@[bound]` on `ENNReal.div_le_div_right` and on the two `ℝ≥0∞` facts
  `natCast_le_natCast_of_le` (monotonicity of the cast from `ℕ`) and
  `le_natCast_mul_of_one_le` (`ε ≤ n * ε` for `1 ≤ n`).
* The scoped `grind` set of namespace `CatCryptGrind`:
  `Finset.sum_range_zero`/`Finset.sum_range_succ`, additive monotonicity `add_le_add`,
  and `lazyEval_fresh_eq_sample`. It is active where `CatCryptGrind` is open, and
  `catcrypt_grind` (`CatCryptCore.Tactics.AutoBase`) opens it.
* `ssprove_crypto_close`: closes a goal by `simp_all`, `catcrypt_grind` or
  `aesop` over `CatCryptRel`.
* `ssprove_crypto_grind`: `ssprove_crypto_close`, otherwise `ssprove_crypto`,
  otherwise the bounded rounds of `ssprove_auto_repeat` followed by
  `ssprove_crypto_close` on each remaining goal.
* Arms of `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`): `ssprove_crypto`
  and `ssprove_crypto_grind` on relational judgments, and `grind +suggestions` with the
  `CatCryptGrind` set after the `grind` arms of each shape.
-/

@[expose] public section

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto CatCrypt.Unary
open scoped ENNReal

/-! ## The Aesop rule set `CatCryptRel` -/

attribute [aesop safe apply (rule_sets := [CatCryptRel])]
  Assumptions.SPComp.bind_noFail SPComp.bindOp_noFail SPComp.pure_noFail
  SPComp.pureOp_noFail Assumptions.SPComp.sample_noFail

/-! ## `gcongr` and `bound` -/

attribute [gcongr] wpE_mono wpEF_mono prEvent_mono

attribute [bound] ENNReal.div_le_div_right natCast_le_natCast_of_le le_natCast_mul_of_one_le

/-! ## The scoped `grind` set `CatCryptGrind` -/

namespace CatCryptGrind

-- The `CatCryptGrind` lemma set.
attribute [scoped grind =]
  Finset.sum_range_zero Finset.sum_range_succ
  CatCrypt.LazySampling.lazyEval_fresh_eq_sample
attribute [scoped grind .] add_le_add
-- End of the `CatCryptGrind` lemma set.

end CatCryptGrind

/-! ## Closers -/

namespace CatCrypt.Tactics

meta section

/-- `ssprove_crypto_close` closes the main goal by the first of `simp_all`,
`catcrypt_grind` and `aesop` over the rule set `CatCryptRel` that closes it,
and fails otherwise. -/
macro "ssprove_crypto_close" : tactic => `(tactic| first
  | (simp_all; done)
  | catcrypt_grind
  | aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))

/-- `ssprove_crypto_grind` closes the goal by the first of
`ssprove_crypto_close`, `ssprove_crypto`, and the rounds of
`ssprove_auto_repeat` followed by `ssprove_crypto_close` on each remaining
goal. It fails when a goal stays open. -/
macro "ssprove_crypto_grind" : tactic => `(tactic| first
  | ssprove_crypto_close
  | ssprove_crypto
  | ((try ssprove_code_simpl)
     ssprove_auto_repeat
     all_goals ssprove_crypto_close))

end

end CatCrypt.Tactics

/-! ## Arms of `catcrypt_auto` -/

catcrypt_auto_arm "relational rHoare judgment" order 20 := "ssprove_crypto"
catcrypt_auto_arm "relational rHoare judgment" order 30 := "ssprove_crypto_grind"

/-! The arms below run `grind +suggestions` with the `CatCryptGrind` set active: `grind`
with the premises of the default library-suggestion selector added, which ranks the
theorems of every imported module. Each runs after the `catcrypt_grind` and `grind`
arms of its shape, under the per-arm budget `catcrypt_auto.maxHeartbeats` (default
20000). `simp? +suggestions` and `simp_all? +suggestions` are not arms. -/

catcrypt_auto_arm "IsPure/NoFail side condition" order 95 :=
  "(open CatCryptGrind in grind +suggestions%GRIND)"
catcrypt_auto_arm "distance inequality" order 45 :=
  "(open CatCryptGrind in grind +suggestions%GRIND)"
catcrypt_auto_arm "monotonicity inequality" order 65 :=
  "(open CatCryptGrind in grind +suggestions%GRIND)"
catcrypt_auto_arm "SPComp equality" order 15 :=
  "(open CatCryptGrind in grind +suggestions%GRIND)"
catcrypt_auto_arm "advantage equality" order 90 :=
  "(open CatCryptGrind in grind +suggestions%GRIND)"
catcrypt_auto_arm "other" order 40 := "(open CatCryptGrind in grind +suggestions%GRIND)"

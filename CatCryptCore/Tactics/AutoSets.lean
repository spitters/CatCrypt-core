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

Attribute registrations and closers for game-based proofs. Every attribute is
applied in this module, so the modules that state the lemmas are unchanged. The
`>>=` forms of the bind combinators are stated beside the combinators
(`SPComp.bindOp_isPure` in `CatCryptCore.Core.Code`, `SPComp.bindOp_noFail` and
`SPComp.pureOp_noFail` in `CatCryptCore.Crypto.NomPkgBridge`), and the two `ℝ≥0∞`
coefficient facts in `CatCryptCore.ForMathlib.ENNRealNatCast`.

* The Aesop rule set `CatCryptRel` (declared in `CatCryptCore.Tactics.AutoSetsDecl`):
  the relational rules registered under `@[rspec]` in `CatCryptCore.Tactics.Sim`,
  together with `rHoare_fail`, as unsafe `apply` rules; the `IsPure` and `NoFail`
  combinators for `pure`, `sample` and bind (in `SPComp.bind` and `>>=` form) as
  safe `apply` rules; and the `SPComp` monad laws as normalisation `simp` rules.
* `@[gcongr]` on the monotonicity of the expectation transformers `wpE` and `wpEF`
  in the postcondition and the error term, and of `prEvent` in the event.
* `@[bound]` on `prTrue_le_one`, on `ENNReal.div_le_div_right`, and on the two
  `ℝ≥0∞` facts `natCast_le_natCast_of_le` (monotonicity of the cast from `ℕ`) and
  `le_natCast_mul_of_one_le` (`ε ≤ n * ε` for `1 ≤ n`).
* The scoped `grind` set of namespace `CatCryptGrind`: heap read-after-write,
  `SPComp` monad laws, symmetry and reflexivity of `Advantage`, the unfolding of
  `AdvantageA`, `Finset.sum_range_zero`/`Finset.sum_range_succ`, additive
  monotonicity `add_le_add`, the relational facts `rHoare_refl` and
  `rHoare_sample_same`, and `lazyEval_fresh_eq_sample`. It is active where
  `CatCryptGrind` is open.
* `catcrypt_grind` and `catcrypt_grind [p₁, …]`: `grind`, with the given
  parameters, and the `CatCryptGrind` set active.
* `ssprove_crypto_close`: closes a goal by `simp_all`, `catcrypt_grind` or
  `aesop` over `CatCryptRel`.
* `ssprove_crypto_grind`: `ssprove_crypto_close`, otherwise `ssprove_crypto`,
  otherwise the bounded rounds of `ssprove_auto_repeat` followed by
  `ssprove_crypto_close` on each remaining goal.
* Arms of `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`): `aesop` over
  `CatCryptRel` on side conditions and relational judgments, `ssprove_crypto` and
  `ssprove_crypto_grind` on relational judgments, `catcrypt_grind` on distance
  inequalities and `SPComp` equalities, `gcongr <;> catcrypt_grind` on distance and
  monotonicity inequalities, `bound` on distance inequalities, and `apply t` with
  `assumption` or `catcrypt_grind` on the premises for each term argument `t`.
-/

@[expose] public section

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto CatCrypt.Unary
open scoped ENNReal

/-! ## The Aesop rule set `CatCryptRel` -/

attribute [aesop safe apply (rule_sets := [CatCryptRel])]
  SPComp.bind_isPure SPComp.bindOp_isPure SPComp.pure_isPure SPComp.sample_isPure
  Assumptions.SPComp.bind_noFail SPComp.bindOp_noFail SPComp.pure_noFail
  SPComp.pureOp_noFail Assumptions.SPComp.sample_noFail

attribute [aesop unsafe 70% apply (rule_sets := [CatCryptRel])]
  rHoare_ret_same rHoare_refl rHoare_sample_same rHoare_fail

attribute [aesop unsafe 50% apply (rule_sets := [CatCryptRel])]
  rHoare_get_sync rHoare_set_sync rHoare_get_l rHoare_get_r rHoare_put_l rHoare_put_r
  rHoare_ite rHoare_if

attribute [aesop norm simp (rule_sets := [CatCryptRel])]
  SPComp.pure_bind SPComp.bind_pure SPComp.bind_assoc SPComp.fail_bind
  SPComp.monad_bind_eq SPComp.monad_pure_eq

/-! ## `gcongr` and `bound` -/

attribute [gcongr] wpE_mono wpEF_mono prEvent_mono

attribute [bound] prTrue_le_one ENNReal.div_le_div_right natCast_le_natCast_of_le
  le_natCast_mul_of_one_le

/-! ## The scoped `grind` set `CatCryptGrind` -/

namespace CatCryptGrind

-- The `CatCryptGrind` lemma set.
attribute [scoped grind =]
  SPComp.pure_bind SPComp.bind_pure SPComp.bind_assoc SPComp.fail_bind
  Heap.get_set_same Heap.get_set_other Advantage_sym Advantage_self AdvantageA
  Finset.sum_range_zero Finset.sum_range_succ
  CatCrypt.LazySampling.lazyEval_fresh_eq_sample
attribute [scoped grind .] add_le_add rHoare_refl rHoare_sample_same
-- End of the `CatCryptGrind` lemma set.

end CatCryptGrind

/-! ## Closers -/

namespace CatCrypt.Tactics

meta section

/-- `catcrypt_grind` runs `grind` with the scoped lemma set of `CatCryptGrind`
active. -/
macro "catcrypt_grind" : tactic => `(tactic| open CatCryptGrind in grind)

/-- `catcrypt_grind [p₁, …, pₙ]` runs `grind [p₁, …, pₙ]` with the scoped lemma
set of `CatCryptGrind` active. -/
macro "catcrypt_grind" " [" ps:Lean.Parser.Tactic.grindParam,* "]" : tactic =>
  `(tactic| open CatCryptGrind in grind [$ps,*])

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

catcrypt_auto_arm "*" order 20 := "(apply %TERM <;> (first | assumption | catcrypt_grind))"

catcrypt_auto_arm "IsPure/NoFail side condition" order 10 :=
  "aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })%AESOP_ADD"

catcrypt_auto_arm "relational rHoare judgment" order 10 :=
  "aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })%AESOP_ADD"
catcrypt_auto_arm "relational rHoare judgment" order 20 := "ssprove_crypto"
catcrypt_auto_arm "relational rHoare judgment" order 30 := "ssprove_crypto_grind"

catcrypt_auto_arm "distance inequality" order 30 := "(gcongr <;> catcrypt_grind%GRIND)"
catcrypt_auto_arm "distance inequality" order 40 := "catcrypt_grind%GRIND"
catcrypt_auto_arm "distance inequality" order 50 skip_forall_ineq budget_div 4 := "bound"

catcrypt_auto_arm "monotonicity inequality" order 30 := "(gcongr <;> catcrypt_grind%GRIND)"

catcrypt_auto_arm "SPComp equality" order 10 := "catcrypt_grind%GRIND"

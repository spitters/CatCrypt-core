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

/-!
# Automation sets for game proofs

Attribute registrations and closers for game-based proofs. Every attribute is
applied here to a lemma proved elsewhere, so the modules that state the lemmas
are unchanged.

* The Aesop rule set `CatCryptRel` (declared in `CatCryptCore.Tactics.AutoSetsDecl`):
  the relational rules registered under `@[rspec]` in `CatCryptCore.Tactics.Sim`,
  together with `rHoare_fail`, as unsafe `apply` rules, and the `SPComp` monad laws
  as normalisation `simp` rules.
* `@[gcongr]` on the monotonicity of the expectation transformers `wpE` and `wpEF`
  in the postcondition and the error term, and of `prEvent` in the event.
* `@[bound]` on `prTrue_le_one`.
* The scoped `grind` set of namespace `CatCryptGrind`: heap get/set rewrites,
  `SPComp` monad laws, symmetry and reflexivity of `Advantage`. It is active
  where `CatCryptGrind` is open.
* `catcrypt_grind`: `grind` with the `CatCryptGrind` set active.
* `ssprove_crypto_close`: closes a goal by `simp_all`, `catcrypt_grind` or
  `aesop` over `CatCryptRel`.
* `ssprove_crypto_grind`: `ssprove_crypto_close`, and otherwise `ssprove_crypto`
  followed by `ssprove_crypto_close` on each remaining goal.
-/

@[expose] public section

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto CatCrypt.Unary

/-! ## The Aesop rule set `CatCryptRel` -/

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

attribute [bound] prTrue_le_one

/-! ## The scoped `grind` set `CatCryptGrind` -/

namespace CatCryptGrind

-- The `CatCryptGrind` lemma set.
attribute [scoped grind =]
  SPComp.pure_bind SPComp.bind_pure SPComp.bind_assoc SPComp.fail_bind
  Heap.get_set_same Heap.set_set_same Heap.get_empty
  Heap.get_set_other Advantage_sym Advantage_self
-- End of the `CatCryptGrind` lemma set.

end CatCryptGrind

/-! ## Closers -/

namespace CatCrypt.Tactics

meta section

/-- `catcrypt_grind` runs `grind` with the scoped lemma set of `CatCryptGrind`
active. -/
macro "catcrypt_grind" : tactic => `(tactic| open CatCryptGrind in grind)

/-- `ssprove_crypto_close` closes the main goal by the first of `simp_all`,
`catcrypt_grind` and `aesop` over the rule set `CatCryptRel` that closes it,
and fails otherwise. -/
macro "ssprove_crypto_close" : tactic => `(tactic| first
  | (simp_all; done)
  | catcrypt_grind
  | aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))

/-- `ssprove_crypto_grind` closes the goal by `ssprove_crypto_close`; when that
fails, it runs `ssprove_crypto` and closes each remaining goal by
`ssprove_crypto_close`. It fails when a goal stays open. -/
macro "ssprove_crypto_grind" : tactic => `(tactic| first
  | ssprove_crypto_close
  | (ssprove_crypto
     all_goals ssprove_crypto_close))

end

end CatCrypt.Tactics

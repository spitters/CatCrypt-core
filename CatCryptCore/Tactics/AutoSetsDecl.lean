/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Aesop

/-!
# The `CatCryptRel` Aesop rule set: declaration

Declares the Aesop rule set `CatCryptRel`. Aesop makes a rule set declared by
`declare_aesop_rule_sets` available only in modules that import the declaring
module, so the rules of the set live in modules that import this one: the `IsPure`
combinators and monad laws in `CatCryptCore.Core.Code`, the relational rules in
`CatCryptCore.Relational.Rules`, the `NoFail` combinators in
`CatCryptCore.Tactics.AutoSets` and `ssprove_nofail` in `CatCryptCore.Tactics.AutoRules`.
-/

@[expose] public section

declare_aesop_rule_sets [CatCryptRel]

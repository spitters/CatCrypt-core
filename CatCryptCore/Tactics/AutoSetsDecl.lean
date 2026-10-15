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
module, so the rules of the set and the tactics that call it live in
`CatCryptCore.Tactics.AutoSets`.
-/

@[expose] public section

declare_aesop_rule_sets [CatCryptRel]

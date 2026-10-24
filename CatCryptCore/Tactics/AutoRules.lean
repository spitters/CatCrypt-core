/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoSets
public import CatCryptCore.Tactics.VC
public meta import CatCryptCore.Tactics.VC

/-!
# Rule-step tactics in the Aesop rule set `CatCryptRel`

Registration in `CatCryptRel` (declared in `CatCryptCore.Tactics.AutoSetsDecl`) of
`ssprove_nofail` as an unsafe tactic rule: `NoFail` of a program built from `sample`,
`get`, `set` and `pure`, closed by `mvcgen`. The rule `rHoare_false` of
`ssprove_unreachable` is registered beside it in `CatCryptCore.Relational.Rules`.

The registration is active where this module is imported.
-/

public section

add_aesop_rules unsafe 60% tactic (by ssprove_nofail) (rule_sets := [CatCryptRel])

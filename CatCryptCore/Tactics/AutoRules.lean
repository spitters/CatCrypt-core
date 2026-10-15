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

Registrations in `CatCryptRel` (declared in `CatCryptCore.Tactics.AutoSetsDecl`)
of the rule steps whose goals the rules of `CatCryptCore.Tactics.AutoSets` do not
close:

* `rHoare_false` (the rule of `ssprove_unreachable`), as a safe `apply` rule: a
  relational judgment with precondition `fun _ _ => False` holds;
* `ssprove_nofail`, as an unsafe tactic rule: `NoFail` of a program built from
  `sample`, `get`, `set` and `pure`, closed by `mvcgen`.

The registrations are active where this module is imported.
-/

public section

open CatCrypt.Relational

add_aesop_rules safe apply rHoare_false (rule_sets := [CatCryptRel])

add_aesop_rules unsafe 60% tactic (by ssprove_nofail) (rule_sets := [CatCryptRel])

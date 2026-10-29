/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoRules

/-!
# Tests for the registrations of `AutoRules`

One goal per rule registered in `CatCryptCore.Tactics.AutoRules`, closed by
`aesop` over `CatCryptRel`. The rules of `CatCryptCore.Tactics.AutoSets` alone do
not close either goal.
-/

set_option autoImplicit false
set_option mvcgen.warning false

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto

namespace CatCrypt.Tactics.AutoRulesTest

/-- Demo location storing a `Bool`. -/
abbrev testLoc : Location := ⟨0, Bool⟩

/-- `rHoare_false`: a judgment with an unsatisfiable precondition. -/
example (c₁ c₂ : SPComp Bool) : rHoare (fun _ _ => False) c₁ c₂ eqPost := by
  aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })

/-- `ssprove_nofail`: `NoFail` through `sample`, `set`, `get` and `pure`. -/
example : SPComp.NoFail (do
    let b ← SPComp.sample Bool
    SPComp.set testLoc b
    let r ← SPComp.get testLoc
    pure (r == b)) := by
  aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })

end CatCrypt.Tactics.AutoRulesTest

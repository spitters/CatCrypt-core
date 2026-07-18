/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCryptCore.Relational.Judgment

/-!
# @[rspec] Attribute for Automatic Relational Spec Lookup

This file provides a `@[rspec]` attribute that registers rHoare lemmas in a
discrimination tree, keyed on the goal type. The `ssprove_sim` tactic queries
this tree when head-matching fails, enabling automatic spec application.

## Main definitions

* `rspecExt` - discrimination tree storing registered rspec lemmas
* `@[rspec]` - attribute to register a lemma for automatic lookup
* `rspecLookup` - query the tree for lemmas matching a goal
-/

namespace CatCrypt.Tactics

open Lean Meta

/-- Extension storing rspec lemmas indexed by goal pattern. -/
initialize rspecExt :
    SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

/-- Register a lemma in the rspec discrimination tree.
    Extracts the conclusion (an `rHoare` judgment) and indexes on it. -/
def addRSpecLemma (declName : Name) (kind : AttributeKind) : MetaM Unit := do
  let info ← getConstInfo declName
  let ty := info.type
  -- Use forallMetaTelescopeReducing to create metavars (not fvars)
  -- so they become wildcards in the DiscrTree key
  let (_, _, conclusion) ← withReducible <| forallMetaTelescopeReducing ty
  let key ← DiscrTree.mkPath conclusion
  rspecExt.add (declName, key) kind

/-- The `@[rspec]` attribute registers a relational spec for automatic lookup
    by `ssprove_sim`. -/
initialize registerBuiltinAttribute {
  name := `rspec
  descr := "Register a relational spec for automatic lookup by ssprove_sim"
  add := fun declName _stx attrKind => MetaM.run' do
    addRSpecLemma declName attrKind
  applicationTime := .afterTypeChecking
}

/-- Query the rspec tree for lemmas matching the current goal expression. -/
def rspecLookup (goal : Expr) : MetaM (Array Name) := do
  (rspecExt.getState (← getEnv)).getMatch goal

end CatCrypt.Tactics

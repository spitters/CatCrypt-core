/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# The `resp_b` registry

The attribute `@[resp_b]` and its registry of lemmas for the tactic `resp_b`
(`CatCryptCore.Complexity.D.RespB`), which proves that a term of D respects a base relation
(`Tm.RespB`). The module imports only `Lean`: a module registers its lemmas with `@[resp_b]` by
importing this module.

A registered lemma is used in two ways at an obligation that is not itself `Tm.RespB` or a
conjunction: every lemma is a rule of `solve_by_elim`, and a lemma whose conclusion is an
equation or an equivalence is also a rewrite rule of `simp_all`. Typical entries are a lemma
`Prim.RespB R p` for a primitive and a relation (with premises), a constructor of a predicate
such a lemma assumes, and an equivalence `R f a b ↔ a = b` that states where a base relation is
equality.

## Main definitions

* `respBExt` — the registry of `@[resp_b]` lemmas;
* `@[resp_b]` — the attribute.
-/

public section

meta section

namespace CatCrypt.Complexity.D.RespBTac

open Lean Meta

/-- The registry of `@[resp_b]` lemmas. -/
initialize respBExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension { addEntry := Array.push, initial := #[] }

/-- `@[resp_b]` registers a lemma for the tactic `resp_b`: a rule of `solve_by_elim` at each
obligation, and a rewrite rule of `simp_all` when its conclusion is an equation or an
equivalence. -/
initialize registerBuiltinAttribute {
  name := `resp_b
  descr := "Register a lemma for the tactic `resp_b` (respect of a base relation by a D term)"
  add := fun decl _ kind => do
    unless (← getEnv).contains decl do
      throwError "resp_b: unknown declaration `{decl}`"
    respBExt.add decl kind
  applicationTime := .afterTypeChecking
}

end CatCrypt.Complexity.D.RespBTac

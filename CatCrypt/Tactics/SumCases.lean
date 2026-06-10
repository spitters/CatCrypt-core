/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean

/-!
# `sum_cases` and `pkg_coherence_lite`

Cycle-free home for the exhaustive `Sum`-case-splitter (`sum_cases`) and a
lightweight SMC-coherence closer (`pkg_coherence_lite`) built from it.

This file depends **only** on Lean core metaprogramming — nothing from
`CatCrypt/Core`, `CatCrypt/Bridge`, or `CatCrypt/Category`.  That lets it be
imported by foundational files such as `Bridge/SemPkg.lean` and
`Category/Affine.lean`, which sit below `PkgCoherence` / `UCCoherence` in
the dependency DAG.

## Main contents

* `sumCasesCore` — recursively case-splits `Sum`-typed hypotheses,
  eliminating `Empty` branches via `cases`.
* `sum_cases` — elab wrapper.
* `pkg_coherence_lite` — `funext _; sum_cases; all_goals rfl`.
* Variants `funext _ _` / `funext _ _ _` for goals with deeper curry
  structure.

## When to use

Goals of shape `f = g` where both sides are handler-like functions built
from `Sum`-indexed data constructors, and the leaves are definitionally
equal.  Typical sites: `MonoidalCategoryStruct` field definitions
(`associator`, `unitors`, `braidings`, pentagon / hexagon coherence),
`TypedHandler.pair`/`fst`/`snd` laws, `Affine`-category coherence.

For richer closers that additionally normalize `SPComp` monad chains or
reach into the deep embedding, see `Tactics/SPNormalize.lean` and
`Tactics/PkgCoherenceBang.lean`.
-/

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta

/-- Recursively case-split all `Sum`-typed variables in the local context,
    eliminating `Empty` branches via `cases`.  Terminates because each
    recursive call strictly reduces the total `Sum` nesting depth. -/
partial def sumCasesCore (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let ty ← whnfD (← instantiateMVars decl.type)
      -- Empty has 0 constructors; `cases` closes the goal.
      if ty.isAppOfArity ``Empty 0 then
        try
          let subgoals ← goal.cases decl.fvarId
          return subgoals.toList.map (·.mvarId)
        catch _ => continue
      -- `Sum` splits into `inl` / `inr` subgoals.
      if ty.isAppOfArity ``Sum 2 then
        try
          let subgoals ← goal.cases decl.fvarId
          let mut results := #[]
          for cs in subgoals do
            results := results ++ (← sumCasesCore cs.mvarId).toArray
          return results.toList
        catch _ => continue
    return [goal]

/-- Exhaustive `Sum`-case split on the local context.  Recursively unpacks
    nested sums and eliminates `Empty` branches. -/
elab "sum_cases" : tactic => do
  replaceMainGoal (← sumCasesCore (← getMainGoal))

/-- Lightweight SMC-coherence closer for `Sum`-indexed handler equalities.

    Tries in order:
    1. `rfl`.
    2. `funext _; sum_cases; all_goals rfl`.
    3. `funext _ _; sum_cases; all_goals rfl` (deeper curry).
    4. `funext _ _ _; sum_cases; all_goals rfl`.

    Use for `MonoidalCategoryStruct` / `SymmetricCategory` field goals
    over `Sum`-indexed packaged-interface tensors, where the structure
    morphisms reduce by case-analysis plus definitional equality. -/
macro "pkg_coherence_lite" : tactic =>
  `(tactic| (
    first
    | rfl
    | (funext _ ; sum_cases ; all_goals rfl)
    | (funext _ _ ; sum_cases ; all_goals rfl)
    | (funext _ _ _ ; sum_cases ; all_goals rfl)))

end CatCrypt.Tactics

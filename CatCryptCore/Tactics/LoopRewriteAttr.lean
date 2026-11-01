/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# The simp set of loop rewriting

The simp set `loop_simps` collects the trace laws of a traced symmetric monoidal category and
the unfolding equations of feedback loops as directed rewrite steps; the tactic `loop_rw`
(`CatCryptCore.Tactics.LoopRewrite`) rewrites with it. An attribute made by
`register_simp_attr` is usable only in modules importing the one that declares it, so the
declaration is a module of its own.

## Main definitions

* `loop_simps`: the simp set of loop rewriting (trace laws, feedback unrolling).
-/

@[expose] public section

/-- `loop_simps` is the simp set of loop rewriting: the trace laws (tightening, sliding,
vanishing, superposing, yanking) and the unfolding of a feedback loop, each oriented so that a
loop shrinks or its pre- and post-processing moves outside it. -/
register_simp_attr loop_simps

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XMvcgen
public import CatCryptCore.XDijkstra.XMvcgenControl


@[expose] public section
set_option autoImplicit false

/-!
# `XMvcgenReg`: the registry-driven (`@[xspec]`-extensible) VC generator

`xmvcgen!` is the registry-driven verification-condition generator over the
extended-PostShape core, the general form of `xmvcgen`. Downstream files add
`@[xspec]` reductions and `xmvcgen!` uses them automatically, unlike `xmvcgen`'s
fixed explicit bundle. The bundle is a consequence of a `register_simp_attr`
constraint: an attribute created by `register_simp_attr` runs its `initialize`
block at import time, so inside `XMvcgen`'s own defining file the `xspec`
attribute is neither taggable nor referenceable, and that file drives
normalization with a hand-listed bundle equal to the `xspec` set.

This module lives **downstream** of `XMvcgen`, where the `xspec` attribute is
live: it is both taggable (`@[xspec]`) and referenceable (`simp only [xspec]`).
Two things follow.

1. **The `xspec` set is completed here.** The core reductions
   (`xpure_apply`, `xbind_apply`, `xseq_apply`, `xseq_grade`, `xprod_apply`,
   `xwp_graded_bind`, `xwp_self`, `frameSep_fst`) and the assertion-algebra
   unfoldings (`XPostCond.frameSep`, `XAssertion.sep`, `XAssertion.le`,
   `XExceptConds.le`) are declared in `XMvcgen`/`XPostShape` — its *own* files —
   so they could not be `@[xspec]`-tagged there. `attribute [xspec] …` here adds
   them, so `simp only [xspec]` alone now normalizes an XDijkstra WP. The
   control-flow reductions (`xite_*`, `xphi_*`) were already `@[xspec]`-tagged in
   `XMvcgenControl`, so they join the same set.

2. **`xmvcgen!` reads the registry, not a bundle.** It expands to
   `simp only [xspec, XTriple, XPT, XRelTriple, …]`: the open `xspec` set plus
   the triple-unfold wrappers plus optional extras. Every `@[xspec]`-tagged
   reduction — including ones a *later* module adds — is picked up with no change
   to the tactic. The two demos at the end witness both halves: (a) one of
   `XMvcgen`'s fused demos re-proved through the registry instead of the bundle,
   and (b) a fresh `@[xspec]` reduction declared here that `xmvcgen!` handles
   automatically. This is the stock-`mvcgen`-style `@[spec]`-registry behavior for
   XDijkstra.
-/

namespace CatCrypt.XDijkstra

/-! ## 1. Complete the `xspec` set downstream

`XMvcgen`'s explicit bundle exists only because these reductions are declared in
`XMvcgen`/`XPostShape`'s own files, where the freshly-`register_simp_attr`-ed
`xspec` attribute is not yet usable. Downstream, it *is* usable: tag the core
reductions and the assertion-algebra unfoldings into the open `xspec` set so
`simp only [xspec]` alone normalizes `(xwp⟦prog⟧).apply Q`. `attribute [xspec] Foo`
adds an already-declared lemma (or a `def`'s equation lemmas) to the simp set;
these are all also `@[simp]`, and the two attributes coexist.

Note `xseq_grade` (`(xseq x y).grade = x.grade + y.grade`) is deliberately **not**
tagged: it matches the same subterm as `xwp_graded_bind`
(`(xseq x y).grade.1 = x.grade.1 + y.grade.1`) but stops at the `Prod`-level `+`,
whose grade-`Add` instance simp does not unfold — leaving `((·,·) + (·,·)).1`.
`xwp_graded_bind` threads the grade to the numeric sum directly, so the bundle (and
this registry) use it alone. -/

attribute [xspec]
  xpure_apply xbind_apply xseq_apply xprod_apply
  xwp_graded_bind xwp_self frameSep_fst
  XPostCond.frameSep XAssertion.sep XAssertion.le XExceptConds.le

/-! ## 2. `xmvcgen!` — the registry-driven tactic

`xmvcgen!` normalizes a triple goal with `simp only [xspec, …]`: the open `xspec`
registry (every `@[xspec]`-tagged reduction, including downstream additions) plus
the triple-unfold wrappers `XTriple`/`XPT`/`XRelTriple` plus optional extras. It
maintains no bundle — a new operation's reduction enters the tactic the moment it
is tagged `@[xspec]`. -/

open Lean Parser.Tactic in
/-- Registry-driven verification-condition generator for the extended-PostShape
core. Expands to `simp only [xspec, XTriple, XPT, XRelTriple, …]`: it picks up
**every** `@[xspec]`-tagged reduction — core, control-flow, and any added by a
downstream module — with no bundle to maintain. `xmvcgen! [h, …]` adds extra simp
lemmas (e.g. concrete step definitions). -/
syntax (name := xmvcgenRegTac) "xmvcgen!" (" [" simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| xmvcgen!) =>
    `(tactic| simp only [xspec, XTriple, XPT, XRelTriple])
  | `(tactic| xmvcgen! [$xs,*]) =>
    `(tactic| simp only [xspec, XTriple, XPT, XRelTriple, $xs,*])

/-! ## 3. Extensibility demos — the registry payoff

### 3a. A fused `XMvcgen` demo, re-proved through the registry

`demo_graded_frame` (from `XMvcgen`) fuses the grade budget and the framed
entailment of a two-step sequenced program. Here it is re-proved verbatim with
`xmvcgen!` (the `xspec` registry) in place of `xmvcgen` (the explicit bundle):
the registry is a superset of the bundle, so the same residual VCs remain. -/

theorem demo_graded_frame_reg (R : Prop) :
    (xseq costStep costStep).grade.1 ≤ 2
    ∧ XPT (ps := .graded ℕ .pure) R
        (xseq costStep costStep)
        (XPostCond.frameSep (fun _ => True, ⟨⟩) R) := by
  refine ⟨?_, ?_⟩
  · -- GRADE axis: `xmvcgen!` threads the sum `1 + 1` via the registry; residual `≤ 2`.
    xmvcgen! [costStep]
    omega
  · -- FRAME axis: `xmvcgen!` normalizes the framed WP; residual entailment `R → True ∧ R`.
    xmvcgen! [costStep]
    exact fun hR => ⟨trivial, hR⟩

/-! ### 3b. A fresh `@[xspec]` reduction — picked up automatically

`xboost k` is a **new** operation declared *here*, downstream of the tactic: a
cost-`3·k` atom. Its `apply`/`grade` reductions are tagged `@[xspec]` in this
file. `xmvcgen!` handles it with no change to the tactic — the extensibility
the explicit-bundle `xmvcgen` lacks (its bundle does not list `xboost`). This is
the stock-`mvcgen`-style `@[spec]`-registry behavior. -/

/-- A fresh cost atom at shape `.graded ℕ .pure`, grade `(3·k, ⟨⟩)`, returning `()`.
Declared downstream of `xmvcgen!` to demonstrate registry pickup. -/
def xboost (k : ℕ) : XPredTrans (.graded ℕ .pure) Prop Unit where
  apply Q := Q.1 ()
  grade := (3 * k, ⟨⟩)
  mono h := h.1 ()

/-- The head grade of `xboost k` is `3·k` — a **new** `@[xspec]` reduction. -/
@[simp, xspec] theorem xboost_grade_fst (k : ℕ) : (xboost k).grade.1 = 3 * k := rfl

/-- The WP of `xboost k` returns `()` — a **new** `@[xspec]` reduction. -/
@[simp, xspec] theorem xboost_apply (k : ℕ)
    (Q : XPostCond Unit (.graded ℕ .pure) Prop) :
    (xboost k).apply Q = Q.1 () := rfl

/-- **Auto-pickup grade demo.** `xmvcgen!` reduces `(xboost 2).grade.1` to `3 · 2`
through the freshly-tagged `xboost_grade_fst`, with no change to the tactic;
`omega` closes the budget residual. -/
theorem demo_boost_auto (budget : ℕ) (h : 6 ≤ budget) :
    (xboost 2).grade.1 ≤ budget := by
  xmvcgen!
  omega

/-- **Auto-pickup triple demo.** `xmvcgen!` reduces the WP of `xboost 2` via the
freshly-tagged `xboost_apply`, leaving the trivial residual entailment. -/
theorem demo_boost_triple :
    XPT (ps := .graded ℕ .pure) True (xboost 2) (fun _ => True, ⟨⟩) := by
  xmvcgen!
  exact le_refl _

/-! ### 3c. The registry already covers control flow

The control-flow reductions of `XMvcgenControl` (`xite_grade_fst`, `xphi_*`) are
`@[xspec]`-tagged, so `xmvcgen!` handles a branch-grade goal too — a downstream
demonstration that the open set spans every module that has contributed to it. -/

/-- **Branch grade via the registry.** The same goal as `XMvcgenControl`'s
`demo_branch_ctl`, driven by `xmvcgen!`: it picks up `xite_grade_fst` (tagged
`@[xspec]` upstream) automatically, exposing the per-branch `bif`. -/
theorem demo_branch_reg (budget : ℕ) (h : 2 ≤ budget) (b : Bool) :
    (xite b (tick 1) (tick 2)).grade.1 ≤ budget := by
  xmvcgen! [tick_grade_fst]
  cases b <;> simp <;> omega

/-! ### 3d. A state layer and a postcondition written as a function

At the shape `.arg ℕ .pure` an assertion is a function of the state, and the
postcondition below is a pair of a `fun` and the unit. The reductions `xseq_apply`
and `stateStep_apply` quantify over `Q : XPostCond …`; they rewrite the pair because
`XPostCond` is reducible. -/

/-- One increment of a natural-number state, at the shape `.arg ℕ .pure`. -/
def stateStep : XPredTrans (.arg ℕ .pure) Prop Unit where
  apply Q := fun s => Q.1 () (s + 1)
  grade := ⟨⟩
  mono h := fun s => h.1 () (s + 1)

/-- The weakest precondition of `stateStep` evaluates the postcondition at the
incremented state. -/
@[simp, xspec] theorem stateStep_apply (Q : XPostCond Unit (.arg ℕ .pure) Prop) :
    stateStep.apply Q = fun s => Q.1 () (s + 1) := rfl

/-- Two increments take the state `n` to `n + 2`; `xmvcgen!` computes the weakest
precondition from the `xspec` set alone. -/
theorem demo_state_seq_reg (n : ℕ) :
    XPT (ps := .arg ℕ .pure) (fun s => s = n)
      (xseq stateStep stateStep) (fun _ s => s = n + 2, ⟨⟩) := by
  xmvcgen!
  rintro s rfl; rfl

end CatCrypt.XDijkstra

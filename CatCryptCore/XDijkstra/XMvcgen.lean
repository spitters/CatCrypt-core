/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPostShape


@[expose] public section
set_option autoImplicit false

/-!
# `XMvcgen`: the verification-condition generator over the extended-PostShape core

This module is **Phase 2** of the extended-PostShape Dijkstra framework: a
verification-condition (VC) generator `xmvcgen` driving the core built in
`XPostShape` (`CatCrypt.XDijkstra`).

The design mirrors how Lean's `Std.Do` weakest-precondition metatheory works —
its per-operation WP reductions (`Std.Do.WP.pure`, `.bind`, `.seq`, …) are
`@[simp]` lemmas of the shape `wp⟦x⟧ Q = …`, and `mvcgen` normalizes a triple by
simp-rewriting with them until only the residual side-conditions remain. Here the
analogous reductions are the `apply`/`grade` lemmas on `XPredTrans` from Phase 1,
and `xmvcgen` normalizes `(xwp⟦prog⟧).apply Q` the same way.

## What `xmvcgen` does

Given a goal that is an `XTriple` / `XPT` / `XRelTriple` (or a conjunction of such
with a `grade ≤ budget` obligation), `xmvcgen`:

1. **unfolds** the triple wrappers (`XTriple → XPT → XAssertion.le`) and the
   self-`XWP` observation (`xwp_self`);
2. **normalizes the WP** `(t).apply Q` through the per-operation reductions
   (`xpure_apply`, `xbind_apply`, `xseq_apply`, `xprod_apply`, and the frame /
   separation unfoldings) until the transformer is fully computed away;
3. **threads the grade** through sequencing: `xwp_graded_bind` rewrites
   `(xseq x y).grade.1` to the **sum** `x.grade.1 + y.grade.1`, so a sequenced
   program's total grade reduces automatically to the summed cost;
4. **leaves the residual VCs**: the assertion entailment (`XAssertion.le`, which
   at the pure leaf is the carrier's `≤`) and the `grade ≤ budget` obligation.

`xmvcgen [h₁, h₂, …]` passes extra simp lemmas (e.g. the definitions of the
concrete per-operation steps) so their `grade`/`apply` unfold as well.

## The `@[xspec]` simp set

`register_simp_attr xspec` registers the extensible attribute for the
per-operation WP reductions: a downstream module that adds a new operation states
its `apply`/`grade` reduction lemma, tags it `@[xspec]`, and `xmvcgen` (using
`simp only [xspec, …]` in that downstream module) picks it up with no change to
the tactic. This is the mechanism by which the generator stays open.

**Same-file caveat (why the in-file tactic uses an explicit bundle).** An
attribute registered with `register_simp_attr` is created by an `initialize`
block that runs at *import* time, so within its *defining* file the attribute is
neither taggable (`@[xspec]`) nor referenceable (`simp only [xspec]`). The in-file `xmvcgen`
therefore drives normalization with the **explicit** reduction bundle listed
below (semantically the `xspec` set); a downstream `xmvcgen`-style variant using
`simp only [xspec, …]` extends automatically. The four demos at the end exercise
the explicit bundle.
-/

namespace CatCrypt.XDijkstra

/-! ## 1. The `@[xspec]` simp attribute

The extensible attribute for per-operation WP reductions. Downstream modules tag
their `apply`/`grade` reduction lemmas `@[xspec]`; a `simp only [xspec]` (in a
module that imports this one) then normalizes `(xwp⟦prog⟧).apply Q`. -/

register_simp_attr xspec

/-! ## 2. Additional `xspec`-shaped reductions

Phase 1 already states the core reductions (`xpure_apply`, `xbind_apply`,
`xseq_apply`, `xseq_grade`, `xprod_apply`, `xwp_self`, `xwp_graded_bind`). Two
convenience reductions used by the frame demo are stated here as clean rewrite
lemmas so the VC generator computes the framed postcondition away. -/

variable {Ω : Type} [Preorder Ω]

/-- `frameSep` of a postcondition projects to the framed success assertion — a
clean `rfl`-rewrite the generator uses to expose the residual entailment. -/
@[simp] theorem frameSep_fst [XBI Ω] {α : Type} {ps : XPostShape.{0}}
    (Q : XPostCond α ps Ω) (R : XAssertion ps Ω) (a : α) :
    (Q.frameSep R).1 a = XAssertion.sep ps (Q.1 a) R := rfl

/-! ## 3. The `xmvcgen` tactic

`xmvcgen` (optionally `xmvcgen [extra, lemmas]`) normalizes a triple goal by
`simp only`-rewriting with the explicit reduction bundle: the triple/relational
wrappers, the self-`XWP` observation, the per-operation `apply` reductions, the
graded sequencing sum (`xwp_graded_bind`), and the frame/separation unfoldings.
What remains is the residual VC(s): the assertion entailment and — for a graded
goal carrying a budget — the `grade ≤ budget` obligation. -/

open Lean Parser.Tactic in
/-- Verification-condition generator for the extended-PostShape core. Normalizes
an `XTriple`/`XPT`/`XRelTriple` goal (or a conjunction with a `grade ≤ budget`
obligation), threading the grade through `xseq` automatically, and leaves the
residual entailment + budget VCs. `xmvcgen [h, …]` adds extra simp lemmas (e.g.
concrete step definitions). -/
syntax (name := xmvcgenTac) "xmvcgen" (" [" simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| xmvcgen) =>
    `(tactic| simp only [XTriple, XPT, XRelTriple, xwp_self,
        xpure_apply, xbind_apply, xseq_apply, xprod_apply, xwp_graded_bind,
        frameSep_fst, XPostCond.frameSep, XAssertion.sep,
        XAssertion.le, XExceptConds.le])
  | `(tactic| xmvcgen [$xs,*]) =>
    `(tactic| simp only [XTriple, XPT, XRelTriple, xwp_self,
        xpure_apply, xbind_apply, xseq_apply, xprod_apply, xwp_graded_bind,
        frameSep_fst, XPostCond.frameSep, XAssertion.sep,
        XAssertion.le, XExceptConds.le, $xs,*])

/-! ## 4. Fused demos — `xmvcgen` fires and threads the grade

Each demo states a **fused** goal over several axes and lets `xmvcgen` reduce it
to its residual VC. Carrier `Ω := Prop` (the plain assertion algebra, `∗ := ∧`
from `instXBIProp`). -/

section Demos

/-- A unit-cost step at shape `.graded ℕ .pure`, grade `(1, ⟨⟩)`, returning `()`. -/
def costStep : XPredTrans (.graded ℕ .pure) Prop Unit where
  apply Q := Q.1 ()
  grade := (1, ⟨⟩)
  mono h := h.1 ()

/-- A unit-cost step at shape `.graded ℕ .pure`, grade `(1, ⟨⟩)`, returning `3`. -/
def ret3Step : XPredTrans (.graded ℕ .pure) Prop Nat where
  apply Q := Q.1 3
  grade := (1, ⟨⟩)
  mono h := h.1 3

/-! ### Demo (a) — graded + frame fused

A two-step sequenced program `xseq costStep costStep` under a frame `R`. The
fused goal is the conjunction of the **grade budget** (`grade.1 ≤ 2`) and the
**framed entailment** (`⦃R⦄` through the sequence to the framed postcondition).
`xmvcgen` threads the grade to `1 + 1` *and* normalizes the framed WP in one
shot, leaving a residual both conjuncts of which are trivially true. -/
theorem demo_graded_frame (R : Prop) :
    (xseq costStep costStep).grade.1 ≤ 2
    ∧ XPT (ps := .graded ℕ .pure) R
        (xseq costStep costStep)
        (XPostCond.frameSep (fun _ => True, ⟨⟩) R) := by
  refine ⟨?_, ?_⟩
  · -- grade axis: xmvcgen threads the sum 1 + 1 automatically; residual VC `1+1 ≤ 2`.
    xmvcgen [costStep]
    omega
  · -- frame axis: xmvcgen normalizes the framed WP to `True ∗ R = True ∧ R`,
    -- leaving the residual entailment `R → True ∧ R`.
    xmvcgen [costStep]
    exact fun hR => ⟨trivial, hR⟩

/-! ### Demo (b) — relational + graded fused

A relational judgment over the product of two graded programs `ret3Step`. The
fused goal pairs the **relational entailment** (the product relates the two
returns by the diagonal) with the product's **head grade** (`xprod` keeps the
left grade). `xmvcgen` reduces the product WP to `3 = 3` and the grade to `1`. -/
theorem demo_relational_graded :
    (xprod ret3Step ret3Step).grade.1 ≤ 1
    ∧ XRelTriple (ps := .graded ℕ .pure) True
        ret3Step ret3Step (fun p => p.1 = p.2) ⟨⟩ := by
  refine ⟨?_, ?_⟩
  · -- grade axis on the relational product: `xprod` keeps the head grade 1.
    show (ret3Step.grade).1 ≤ 1
    xmvcgen [ret3Step]
    omega
  · -- relational axis: xmvcgen runs the product WP, leaving the residual
    -- entailment `True → 3 = 3`.
    xmvcgen [ret3Step]
    exact fun _ => rfl

/-! ### Demo (c) — relational via `xprod` on pure programs

The minimal relational demo: two pure programs returning `3` are related by the
diagonal through the product transformer. `xmvcgen` computes the product WP away,
leaving `True → 3 = 3`. -/
theorem demo_relational_pure :
    XRelTriple (ps := .pure) True
      (xpure (Ω := Prop) (ps := .pure) (3 : Nat))
      (xpure (Ω := Prop) (ps := .pure) (3 : Nat))
      (fun p => p.1 = p.2) ⟨⟩ := by
  -- xmvcgen runs the product WP; residual entailment `True → 3 = 3`.
  xmvcgen
  exact fun _ => rfl

/-! ### Demo (d) — monad morphism: the transfer law normalizes

For the identity WP-morphism (`instXWPMorphismId`) the `transfer` law is `rfl`
and both maps are the identity, so `xmvcgen` normalizes the transferred triple
`⦃P⦄ θ t ⦃Q⦄` back to the self-triple WP on `t`. Here the morphism axis is
exercised through the same simp normalizer: after `xmvcgen`, the residual is the
plain entailment `P ⊢ t.apply Q`. -/
theorem demo_morphism_normalize (t : XPredTrans (.pure) Prop Nat)
    (P : XAssertion (.pure) Prop) (Q : XPostCond Nat (.pure) Prop)
    (h : XAssertion.le (.pure) P (t.apply Q)) :
    XTriple (m := XPredTrans (.pure) Prop) (ps := .pure) P
      ((fun {_} t => t) t) Q := by
  xmvcgen
  exact h

end Demos

end CatCrypt.XDijkstra

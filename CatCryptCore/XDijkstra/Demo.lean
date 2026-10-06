/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.Do
public import Std.Tactic.Do
public import Mathlib.Order.SetNotation
public import CatCryptCore.XDijkstra.XMvcgenReg
public import CatCryptCore.XDijkstra.XHeapSoundness
public import CatCryptCore.XDijkstra.XMorphismInstance
public import CatCryptCore.XDijkstra.XRelatorPMF

@[expose] public section
set_option autoImplicit false

/-!
# A tutorial for the graded Dijkstra-monad kernel

The examples are written for a reader who knows `Std.Do` and `mvcgen`. One state
program is proved with a `Std.Do` triple and again with an `XTriple`; the later
sections add what `Std.Do` triples do not state: a grade, a framed assertion, a
relation between two runs, and transfer along a monad morphism. The last section
uses a rule stated over an arbitrary assertion type at two instances.

## Main definitions

* `addTwo`: a `StateM ℕ` program with two increments.
* `stepT`: the weakest-precondition transformer of one increment, at cost `1`.
* `readT`: the transformer that returns the state.
* `setStep`: a transformer over the assertion type `Set ℕ`, which is not computed
  from a shape.

## Main results

* `addTwo_std`, `addTwo_x`: one specification as a `Std.Do` triple and as an
  `XTriple`.
* `stepT_seq_budget`: the triple of two sequenced steps, with the grade within a
  budget.
* `pure_frame`, `stepT_framed`, `stepT_not_local`: the frame rule over an abstract
  separation carrier, a framed goal over `Prop`, and a transformer to which the
  frame rule does not apply.
* `readT_rel`, `map_coupled`: a relational triple of two runs, and a coupling of
  two probabilistic runs.
* `stepT_baseChange`: the triple of `stepT` transferred to a shape with an
  exception layer.
* `setStep_seq`, `stepT_seq_core`, `xseq_local`: `XCorePT.seq_triple` at `Set ℕ`
  and at a shape, and locality of `xseq` from `XCorePT.seq_local`.
-/

namespace CatCrypt.XDijkstra.Demo

/-! ## (a) One program, two triples

`mvcgen` works on `⦃P⦄ x ⦃Q⦄` (`Std.Do.Triple`), `xmvcgen!` on `XTriple P x Q`.
The notions correspond as follows.

* Shape: `PostShape.arg ℕ .pure` and `psState ℕ`, which is `XPostShape.arg ℕ .pure`.
* Observation: `wp⟦x⟧` and `XWP.xwp x`; for `StateM` the latter is `stateWP x`.
* Postcondition: `⇓ r s => …` and the pair `(fun r s => …, PUnit.unit)` of a success
  assertion and the exception postconditions.
* Assertion: `⌜p⌝` and `p`, since the carrier `Ω` is `Prop`.
* Residual goal: both tactics leave the entailment from the precondition to the
  computed weakest precondition. -/

/-- Two increments of a natural-number state. -/
def addTwo : StateM ℕ Unit := do
  modify (· + 1)
  modify (· + 1)

section StdDo

open Std.Do

set_option mvcgen.warning false in
/-- The `Std.Do` triple of `addTwo`, by `mvcgen`. -/
theorem addTwo_std (n : ℕ) :
    ⦃fun s => ⌜s = n⌝⦄ addTwo ⦃⇓ _ s => ⌜s = n + 2⌝⦄ := by
  mvcgen [addTwo]
  subst_vars; rfl

end StdDo

/-- The `XTriple` of `addTwo`, by `xmvcgen!`. The extra arguments unfold the
observation of `StateM`: the class projection `XWP.xwp` and its value `stateWP`. -/
theorem addTwo_x (n : ℕ) :
    XTriple (m := StateM ℕ) (ps := psState ℕ) (Ω := Prop)
      (fun s => s = n) addTwo (fun _ s => s = n + 2, PUnit.unit) := by
  xmvcgen! [XWP.xwp, stateWP]
  rintro s rfl; rfl

/-! ## (b) A grade

`StateM` carries no grade, so the cost is attached to the transformer: `stepT` is
the weakest precondition of one increment with grade `1`, at the shape
`.graded ℕ (.arg ℕ .pure)`. Sequencing with `xseq` adds grades, and `xmvcgen`
rewrites the grade of the sequence to the sum (`xwp_graded_bind`). A graded
specification is the conjunction of a bound on the grade and a triple. For the
triple, the definitions of the step and of `xseq` are passed to `xmvcgen`: at a
shape with a state layer the weakest precondition is computed by unfolding them. -/

/-- One increment of the state, at cost `1`. -/
def stepT : XPredTrans (.graded ℕ (.arg ℕ .pure)) Prop Unit where
  apply Q := fun s => Q.1 () (s + 1)
  grade := (1, ⟨⟩)
  mono h := fun s => h.1 () (s + 1)

/-- Two steps take the state `n` to `n + 2` at a cost within any budget `b ≥ 2`.
`xmvcgen` leaves the arithmetic goal `1 + 1 ≤ b` and the state entailment. -/
theorem stepT_seq_budget (n b : ℕ) (hb : 2 ≤ b) :
    (xseq stepT stepT).grade.1 ≤ b
    ∧ XPT (ps := .graded ℕ (.arg ℕ .pure)) (fun s => s = n)
        (xseq stepT stepT) (fun _ s => s = n + 2, ⟨⟩) := by
  refine ⟨?_, ?_⟩
  · xmvcgen [stepT]
    omega
  · xmvcgen [stepT, xseq]
    rintro s rfl; rfl

/-! ## (c) The frame rule

Over a carrier with a separating product (`XBI Ω`), `xframe` extends the triple of
a local transformer by a frame `R`. Return is local (`xpure_local`). Over `Prop`
the product is conjunction, lifted pointwise through a state layer; `stepT` is not
local for it, because a frame may mention the state, so a framed goal about
`stepT` is computed by `xmvcgen` and holds for a frame that ignores the state. -/

/-- The frame rule for return, over an arbitrary separation carrier. -/
theorem pure_frame {Ω : Type} [Preorder Ω] [XBI Ω] (a : ℕ) (P R : Ω) :
    XPT (ps := .pure) (XAssertion.sep .pure P R) (xpure (Ω := Ω) (ps := .pure) a)
      (XPostCond.frameSep (ps := .pure) (fun _ => P, ⟨⟩) R) :=
  xframe (xpure_local a) (XAssertion.le_refl .pure P)

/-- A framed triple of `stepT` with a frame that does not mention the state. -/
theorem stepT_framed (n : ℕ) (R : Prop) :
    XPT (ps := .graded ℕ (.arg ℕ .pure))
      (XAssertion.sep (.graded ℕ (.arg ℕ .pure)) (fun s => s = n) (fun _ => R)) stepT
      (XPostCond.frameSep (fun _ s => s = n + 1, ⟨⟩) (fun _ => R)) := by
  xmvcgen [stepT]
  rintro s ⟨rfl, hR⟩; exact ⟨rfl, hR⟩

/-- `stepT` is not local: the frame `s = 0` does not survive the increment. -/
theorem stepT_not_local : ¬ XLocal stepT := fun h =>
  absurd (h (fun _ _ => True, ⟨⟩) (fun s => s = 0) 0 ⟨trivial, rfl⟩).2 (by decide)

/-! ## (d) Two runs

`XRelTriple P t₁ t₂ Ψ E` is a triple over the product `xprod t₁ t₂`, which runs
`t₁`, then `t₂`, and pairs the results. For probabilistic programs the product is
the independent coupling; `Couples μ ν R` asks for a joint distribution with
marginals `μ` and `ν` supported on `R`, and `Couples_bind` composes couplings. -/

/-- The transformer that returns the state. -/
def readT : XPredTrans (.arg ℕ .pure) Prop ℕ where
  apply Q := fun s => Q.1 s s
  grade := ⟨⟩
  mono h := fun s => h.1 s s

/-- Two reads of the state return equal values. -/
theorem readT_rel :
    XRelTriple (ps := .arg ℕ .pure) (fun _ => True) readT readT
      (fun p _ => p.1 = p.2) ⟨⟩ := by
  xmvcgen [readT]
  exact fun _ _ => rfl

/-- Two runs that sample from the same distribution and then apply `f` and `g`
are coupled on `S` when `f` and `g` are pointwise related by `S`. -/
theorem map_coupled {α β : Type} (μ : PMF α) (f g : α → β) (S : β → β → Prop)
    (h : ∀ a, S (f a) (g a)) :
    Couples (μ.bind fun a => PMF.pure (f a)) (μ.bind fun a => PMF.pure (g a)) S :=
  Couples_bind (Couples_same μ) fun a _ hab => hab ▸ Couples_pure (h a)

/-! ## (e) Transfer along a monad morphism

`thetaX` sends a transformer over the shape `.graded G (.arg σ .pure)` to one over
the shape with an added exception layer, and `instXWPMorphismBaseChange` states its
action on postconditions: the exception postcondition is dropped. `xwp_morphism`
turns a triple about `stepT` into a triple about `thetaX stepT`; the hypothesis is
the triple of `stepT` at the pulled-back postcondition. -/

/-- The triple of one step, transferred to the shape with an exception layer. -/
theorem stepT_baseChange (n : ℕ) :
    XTriple (m := XPredTrans (.graded ℕ (.arg ℕ (.except PUnit .pure))) Prop)
      (ps := .graded ℕ (.arg ℕ (.except PUnit .pure))) (Ω := Prop)
      (fun s => s = n) (thetaX stepT) (fun _ s => s = n + 1, (fun _ => True, ⟨⟩)) :=
  xwp_morphism (Ω := Prop) (psm := .graded ℕ (.arg ℕ .pure))
    (psn := .graded ℕ (.arg ℕ (.except PUnit .pure)))
    (m := XPredTrans (.graded ℕ (.arg ℕ .pure)) Prop) (θ := fun {_} t => thetaX t)
    stepT (P₀ := fun s => s = n) (fun _ hs => congrArg (· + 1) hs)

/-! ## (f) The core without a shape

`XCorePT Pred EPred G α` takes the assertion type as a parameter. A rule proved
there applies to assertion types that no shape computes, and to every shape
through `XPredTrans.toCore`. The order and separation instances on
`XAssertion ps Ω` are definitions; a file that states a core rule at a shape makes
them local instances. -/

/-- One increment, as a transformer over sets of states. -/
def setStep : XCorePT (Set ℕ) PUnit ℕ Unit where
  apply post _ := {s | s + 1 ∈ post ()}
  grade := 1
  mono h _ := fun _ hs => h () hs

/-- `XCorePT.seq_triple` at the assertion type `Set ℕ`. -/
theorem setStep_seq (n : ℕ) :
    XCorePT.Triple {n} (setStep.seq setStep) (fun _ => {n + 2}) ⟨⟩
    ∧ (setStep.seq setStep).grade = 2 :=
  ⟨XCorePT.seq_triple (R := {n + 1}) (by rintro s rfl; rfl) (by rintro s rfl; rfl), rfl⟩

attribute [local instance] XAssertion.preorder XExceptConds.preorder XAssertion.coreSep

/-- `XCorePT.seq_triple` at the shape of `stepT`, through `xpt_iff_core`. -/
theorem stepT_seq_core (n : ℕ) :
    XPT (ps := .graded ℕ (.arg ℕ .pure)) (fun s => s = n)
      (xseq stepT stepT) (fun _ s => s = n + 2, ⟨⟩) :=
  (xpt_iff_core _ _ _).2 <|
    XCorePT.seq_triple (s := stepT.toCore) (t := stepT.toCore) (R := fun s => s = n + 1)
      (fun _ hs => congrArg (· + 1) hs) (fun _ hs => congrArg (· + 1) hs)

/-- Locality is closed under `xseq`: `XCorePT.seq_local` at a shape. -/
theorem xseq_local {ps : XPostShape.{0}} {Ω : Type} [Preorder Ω] [XBI Ω] [Add ps.Grade]
    {α β : Type} {x : XPredTrans ps Ω α} {y : XPredTrans ps Ω β}
    (hx : XLocal x) (hy : XLocal y) : XLocal (xseq x y) :=
  (xlocal_iff_core _).2 <|
    XCorePT.seq_local ((xlocal_iff_core x).1 hx) ((xlocal_iff_core y).1 hy)

end CatCrypt.XDijkstra.Demo

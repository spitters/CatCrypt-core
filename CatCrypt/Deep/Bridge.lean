/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Deep.Eval
import CatCrypt.Deep.Package
import CatCrypt.Tactics.SimpAttr
import CatCrypt.Relational.Rules

/-!
# Deep/Shallow Bridge Library

This file provides systematic support for moving between the deep embedding
(RawCode, DeepPackage) and the shallow embedding (SPComp).

## Main definitions

* `DeepPackage.evalOp` - Evaluate a single operation from a deep package
* `rHoare_of_code_eq` - Derive rHoare from code equality in deep embedding
* `rHoare_of_eval_eq` - Derive rHoare from evaluation equality

## Tactics

* `ssprove_deep_to_shallow` - Unfold DeepRHoare and simplify eval
* `ssprove_eval` - Simplify eval expressions using the ssprove_eval simp set

## Simp set

* `ssprove_eval` - Named simp set collecting all eval lemmas

## Design rationale

The bridge serves multiple purposes:

1. **Move to shallow for distribution reasoning**: After defining games in the
   deep embedding, use eval to move to SPComp for coupling proofs.

2. **Structural equality → rHoare**: When two deep programs are syntactically
   equal, this immediately gives an rHoare judgment after evaluation.

3. **Package-level evaluation**: Evaluate all implementations in a deep package
   to SPComp functions, enabling reasoning about whole packages.

## References

* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
* [Dupressoir et al., *How Hard Can It Be?*](https://eprint.iacr.org/2025/1569)
-/

namespace CatCrypt.Deep

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Relational

universe u

/-! ## Eval Simp Set

The `ssprove_eval` simp set collects all lemmas for evaluating
deep embedding code into the shallow embedding.
-/

-- RawCode eval lemmas
attribute [ssprove_eval] eval_ret eval_bind eval_sample eval_get eval_put eval_fail
  eval_oracleCall

-- SPComp normalization (for post-eval cleanup)
attribute [ssprove_eval] SPComp.pure_bind SPComp.bind_pure SPComp.bind_assoc SPComp.monad_bind_eq

/-! ## Package-Level Evaluation -/

/-- Evaluate a single operation from a deep package to an SPComp function.

Given a package `p` with an exported operation `(op, dom, codom)`,
this evaluates the implementation code to a shallow SPComp computation.
-/
noncomputable def DeepPackage.evalOp (p : DeepPackage.{u}) (op : ℕ) (dom codom : Type u)
    (h : (op, dom, codom) ∈ p.exports.ops) (x : dom) : SPComp codom :=
  (p.impl op dom codom h x).code.eval

/-! ## Code Equality → rHoare -/

/-- Code equality gives eqPost from eqPre.

This is the key bridge lemma: if two RawCode programs are syntactically equal,
their evaluations produce equal results from equal heaps.

For custom pre/post conditions, use `rHoare_conseq` after this lemma. -/
theorem rHoare_of_code_eq {α : Type*} (c₁ c₂ : RawCode α) (h : c₁ = c₂) :
    rHoare eqPre c₁.eval c₂.eval eqPost := by
  subst h
  exact rHoare_refl c₁.eval

/-- If two evaluations are equal as SPComp functions, rHoare holds. -/
theorem rHoare_of_eval_eq {α : Type*} (c₁ c₂ : RawCode α)
    (h : c₁.eval = c₂.eval) :
    rHoare eqPre c₁.eval c₂.eval eqPost := by
  rw [h]
  exact rHoare_refl c₂.eval

/-- Code equality lifts to eval equality. -/
@[simp, ssprove_eval]
theorem eval_congr {α : Type*} (c₁ c₂ : RawCode α) (h : c₁ = c₂) :
    c₁.eval = c₂.eval := by rw [h]

/-! ## Package Operation Evaluation Lemmas -/

/-- Evaluating an operation from a parallel composition (left component). -/
theorem evalOp_par_left (p₁ p₂ : DeepPackage.{u}) (h_sep : DeepPackage.sep p₁ p₂)
    (op : ℕ) (dom codom : Type u)
    (h₁ : (op, dom, codom) ∈ p₁.exports.ops) (x : dom) :
    (DeepPackage.par p₁ p₂ h_sep).evalOp op dom codom
      (List.mem_append.mpr (Or.inl h₁)) x =
    p₁.evalOp op dom codom h₁ x := by
  simp only [DeepPackage.evalOp, DeepPackage.par]
  simp only [dif_pos h₁]
  rfl

/-! ## Bridge Lemmas for Common Patterns -/

/-- DeepRHoare from code equality (the most common bridge pattern). -/
theorem DeepRHoare_of_eq {α : Type*} (c₁ c₂ : RawCode α) (h : c₁ = c₂) :
    DeepRHoare eqPre c₁ c₂ eqPost := by
  unfold DeepRHoare
  exact rHoare_of_code_eq c₁ c₂ h

/-- DeepRHoare unfolds to rHoare on eval. -/
theorem DeepRHoare_iff {α : Type*} (pre : RPre) (c₁ c₂ : RawCode α) (post : RPost α α) :
    DeepRHoare pre c₁ c₂ post ↔ rHoare pre c₁.eval c₂.eval post :=
  Iff.rfl

/-! ## Bridge Tactics -/

/-- `ssprove_deep_to_shallow` unfolds DeepRHoare to rHoare and simplifies eval.

This is the main entry point for moving from deep to shallow embedding.
After applying this tactic, the goal will be a standard rHoare judgment
on SPComp terms.

Example:
```lean
theorem example : DeepRHoare eqPre code₁ code₂ eqPost := by
  ssprove_deep_to_shallow
  -- Goal is now: rHoare eqPre (eval₁) (eval₂) eqPost
  -- where eval₁, eval₂ are simplified SPComp terms
```
-/
macro "ssprove_deep_to_shallow" : tactic =>
  `(tactic| (
    unfold DeepRHoare
    simp only [ssprove_eval]
  ))

/-- `ssprove_eval` simplifies eval expressions in the goal.

This applies all evaluation lemmas to normalize deep embedding terms
that have been evaluated into the shallow embedding.
-/
macro "ssprove_eval" : tactic =>
  `(tactic| simp only [ssprove_eval])

/-- `ssprove_code_eq` proves an rHoare goal from code equality.

When the deep code on both sides is syntactically equal (after unfolding),
this tactic closes the goal immediately.

Example:
```lean
theorem example : rHoare eqPre code.eval code.eval eqPost := by
  ssprove_code_eq
```
-/
macro "ssprove_code_eq" : tactic =>
  `(tactic| exact rHoare_refl _)

end CatCrypt.Deep

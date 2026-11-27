/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import PolyFun.PFunctor.Free.CodeRel

/-!
# Inversion of the heterogeneous relational lift

The heterogeneous lift `HFreeRel S R` of PolyFun relates two leaves exactly when their results
are related, two nodes exactly when their positions are related and their continuations are
related at related directions, and never a leaf and a node. These are the inversion lemmas of
`HFreeRel` at `pure` and `liftBind`, the heterogeneous forms of `freeRel_pure_iff` and
`freeRel_liftBind_iff`.

## Main results

* `hFreeRel_pure_iff`, `hFreeRel_liftBind_iff` — inversion at two leaves and at two nodes;
* `not_hFreeRel_pure_liftBind`, `not_hFreeRel_liftBind_pure` — a leaf and a node are unrelated.

Search words: heterogeneous relational lift, signature relation, free monad, inversion, leaf,
node.
-/

set_option autoImplicit false

@[expose] public section

universe u v u' v' w w'

namespace PFunctor

variable {P : PFunctor.{u, v}} {Q : PFunctor.{u', v'}} {S : SigRel P Q} {α : Type w}
  {β : Type w'}

/-- Leaves are related by the heterogeneous lift exactly when their results are. -/
theorem hFreeRel_pure_iff {R : α → β → Prop} {a : α} {b : β} :
    HFreeRel S R (.pure a : P.FreeM α) (.pure b : Q.FreeM β) ↔ R a b := by
  constructor
  · rintro ⟨h⟩; exact h
  · exact HFreeRel.pure

/-- Two nodes are related by the heterogeneous lift exactly when their positions are related and
their continuations are related at related directions. -/
theorem hFreeRel_liftBind_iff {R : α → β → Prop} {a : P.A} {a' : Q.A}
    {k : P.B a → P.FreeM α} {k' : Q.B a' → Q.FreeM β} :
    HFreeRel S R (.liftBind a k) (.liftBind a' k') ↔
      S.pos a a' ∧ ∀ d d', S.dir a a' d d' → HFreeRel S R (k d) (k' d') := by
  constructor
  · intro h
    cases h
    grind
  · exact fun h => HFreeRel.liftBind h.1 h.2

/-- A leaf and a node are not related by the heterogeneous lift. -/
theorem not_hFreeRel_pure_liftBind {R : α → β → Prop} {a : α} {a' : Q.A}
    {k' : Q.B a' → Q.FreeM β} : ¬ HFreeRel S R (.pure a : P.FreeM α) (.liftBind a' k') := by
  rintro ⟨⟩

/-- A node and a leaf are not related by the heterogeneous lift. -/
theorem not_hFreeRel_liftBind_pure {R : α → β → Prop} {a : P.A} {k : P.B a → P.FreeM α}
    {b : β} : ¬ HFreeRel S R (.liftBind a k) (.pure b : Q.FreeM β) := by
  rintro ⟨⟩

end PFunctor

end

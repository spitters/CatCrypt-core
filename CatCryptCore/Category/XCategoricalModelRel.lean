/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Category.XCategoricalModel
public import CatCryptCore.XDijkstra.Rel.XRelSpecMonad

@[expose] public section

set_option autoImplicit false

/-!
# `XCategoricalModelRel`: the relational axis of the XDijkstra categorical model

`XCategoricalModel` states the grade, separation and morphism axes of the
XDijkstra framework as categorical structures. This file states the fourth, the
relational axis, over the coupling-spec-monad `RelPT` of `XRelSpecMonad`: the
relational lifting is a monad on pairs whose `bind` (`relBind`) is the pRHL
coupling composition (`relational_axis_is_monad`), and the coupling error of a
`relBind` is the sum of the errors of its two parts (`relational_grade_adds`).

## Main results

* `relational_axis_is_monad`: the relational lifting is a monad on pairs whose bind is the
  coupling composition.
* `relational_grade_adds`: the coupling error of a composition is the sum of the errors.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal

/-! ### Axis III — relational ↔ the relational-lifting monad on pairs `RelPT` -/

/-- **Relational axis = a monad on pairs whose `bind` is the coupling composition.**
`relBind`'s specification is the pRHL coupling composition `RelQ0.liftR_bind`: from a
prefix coupling at `R` and a continuation coupling at `S`, the bound pair is coupled
at `S`. This is the relational lifting *as a monad* (Maillard et al., "The Next 700
Relational Program Logics") — the relational axis carrying the coupling relation, not
just its grade (contrast the blind product `xprod`/`xseq`). -/
theorem relational_axis_is_monad {T : Type → Type} [CatCrypt.RelQ0 T]
    {ε δ : ℝ≥0∞} {α β α' β' : Type}
    {R : α → β → Prop} {S : α' → β' → Prop}
    {m : RelPT (T := T) ε α β} {k₁ : α → T α'} {k₂ : β → T β'}
    (h : RelSpec m R)
    (hk : ∀ a b, R a b → RelSpecTriple δ S (k₁ a) (k₂ b)) :
    RelSpec (relBind (δ := δ) m k₁ k₂) S :=
  relBind_spec h hk

/-- **The relational monad adds grades.** The `relBind` of an `ε`-coupled prefix and
a `δ`-coupled continuation lands at grade `ε + δ` in the type index — coupling error
composes additively, in the object, alongside the relation `S`. -/
theorem relational_grade_adds {T : Type → Type} [CatCrypt.RelQ0 T]
    {ε δ : ℝ≥0∞} {α β α' β' : Type}
    (m : RelPT (T := T) ε α β) (k₁ : α → T α') (k₂ : β → T β') (S : α' → β' → Prop) :
    RelSpec (relBind (δ := δ) m k₁ k₂) S
      = RelQ0.liftR (ε + δ) S (RelQ0.bind' m.fst k₁) (RelQ0.bind' m.snd k₂) :=
  relBind_grade_add m k₁ k₂ S

end CatCrypt.XDijkstra

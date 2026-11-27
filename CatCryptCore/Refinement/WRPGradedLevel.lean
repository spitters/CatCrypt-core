/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Graded levels: squares of programs up to a graded error

A graded level has horizontal arrows `Hom a b` between objects (programs), grades in a type
`Grade` with an additive monoid and a preorder, and a square predicate `Sq g top bot` stating that
the program `bot` refines the program `top` up to the grade `g`, along identity vertical arrows.
Identity squares have grade `0`, squares are monotone in the grade, and vertical pasting adds
grades (`GradedLevel`). A graded level with horizontal composition (`GradedLevelH`) has a
composite of programs, a grade map `hgrade` for horizontal pasting, and the law that the composite
of the bottoms refines the composite of the tops at the mapped grade.

The square predicate is not required to be symmetric: refinement up to an error of quantum
channels is one-sided. The grades are not required to be `[0, ∞]`: realization of reactive systems
is graded by bounds that depend on the environment, under pointwise addition.

## Main definitions

* `GradedLevel`: horizontal arrows, grades, squares, with the laws `id`, `mono`, `vcomp`.
* `GradedLevelH`: a graded level with composition of programs and horizontal pasting `hcomp` at
  the grade map `hgrade`.

## Main results

* `GradedLevel.vchain`: a chain of hops `f 0, f 1, …, f n` pasted vertically is a square from
  `f 0` to `f n` whose grade is the sum of the grades of the hops (a list sum).
* `GradedLevel.vchain_finset`: the same with the sum over `Finset.range n`, for commutative
  grades.

## Search words

graded double category, graded level, approximate refinement, square up to an error, hybrid
argument, game hop chain, vertical pasting, horizontal pasting, sum of the errors
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace CatCrypt.Refinement.WRPGradedLevel

/-- A graded level: programs `Hom a b` between objects, grades in `Grade`, and squares
`Sq g top bot` (the program `bot` refines `top` up to the grade `g`). Identity squares have grade
`0`, squares are monotone in the grade, and vertical pasting adds grades. -/
structure GradedLevel {Obj : Type u} (Hom : Obj → Obj → Type v) (Grade : Type w)
    [AddMonoid Grade] [Preorder Grade] where
  /-- The square of grade `g` with the program `top` on top and the program `bot` at the
  bottom. -/
  Sq : {a b : Obj} → Grade → Hom a b → Hom a b → Prop
  /-- Identity squares have grade `0`. -/
  id : ∀ {a b : Obj} (f : Hom a b), Sq 0 f f
  /-- Squares are monotone in the grade. -/
  mono : ∀ {a b : Obj} {g g' : Grade} {top bot : Hom a b}, Sq g top bot → g ≤ g' →
    Sq g' top bot
  /-- Vertical pasting adds grades. -/
  vcomp : ∀ {a b : Obj} {g₁ g₂ : Grade} {f₁ f₂ f₃ : Hom a b}, Sq g₁ f₁ f₂ → Sq g₂ f₂ f₃ →
    Sq (g₁ + g₂) f₁ f₃

/-- A graded level with horizontal composition: the composite `comp f₁ f₂` of programs, a grade
map `hgrade` for horizontal pasting, and the law that the composite of the bottoms refines the
composite of the tops at the mapped grade. -/
structure GradedLevelH {Obj : Type u} (Hom : Obj → Obj → Type v) (Grade : Type w)
    [AddMonoid Grade] [Preorder Grade] extends GradedLevel Hom Grade where
  /-- The composite of two programs. -/
  comp : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c
  /-- The grade of a horizontal pasting. -/
  hgrade : Grade → Grade → Grade
  /-- Horizontal pasting: the composite of the bottoms refines the composite of the tops at the
  grade `hgrade g₁ g₂`. -/
  hcomp : ∀ {a b c : Obj} {g₁ g₂ : Grade} {top₁ bot₁ : Hom a b} {top₂ bot₂ : Hom b c},
    Sq g₁ top₁ bot₁ → Sq g₂ top₂ bot₂ → Sq (hgrade g₁ g₂) (comp top₁ top₂) (comp bot₁ bot₂)

namespace GradedLevel

variable {Obj : Type u} {Hom : Obj → Obj → Type v} {Grade : Type w}

/-- **Vertical chain.** Hops from `f i` down to `f (i + 1)` of grade `g i`, for `i < n`, paste
vertically to a square from `f 0` down to `f n` whose grade is the sum of the grades. -/
theorem vchain [AddMonoid Grade] [Preorder Grade] (L : GradedLevel Hom Grade) {a b : Obj}
    (f : ℕ → Hom a b) (g : ℕ → Grade) (n : ℕ)
    (h : ∀ i < n, L.Sq (g i) (f i) (f (i + 1))) :
    L.Sq ((List.range n).map g).sum (f 0) (f n) := by
  induction n with
  | zero => exact L.id (f 0)
  | succ n ih =>
    rw [List.sum_range_succ]
    exact L.vcomp (ih fun i hi => h i (by omega)) (h n (by omega))

/-- **Vertical chain, commutative grades.** Hops from `f i` down to `f (i + 1)` of grade `g i`,
for `i < n`, paste vertically to a square from `f 0` down to `f n` of grade
`∑ i ∈ Finset.range n, g i`. -/
theorem vchain_finset [AddCommMonoid Grade] [Preorder Grade] (L : GradedLevel Hom Grade)
    {a b : Obj} (f : ℕ → Hom a b) (g : ℕ → Grade) (n : ℕ)
    (h : ∀ i < n, L.Sq (g i) (f i) (f (i + 1))) :
    L.Sq (∑ i ∈ Finset.range n, g i) (f 0) (f n) := by
  induction n with
  | zero => exact L.id (f 0)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact L.vcomp (ih fun i hi => h i (by omega)) (h n (by omega))

end GradedLevel

end CatCrypt.Refinement.WRPGradedLevel

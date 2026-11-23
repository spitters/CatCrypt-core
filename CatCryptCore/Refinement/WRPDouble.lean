/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.WRPLevels
public import Mathlib.CategoryTheory.Category.KleisliCat

/-!
# The double category of refinement squares

Programs of several levels of abstraction, each level a monad with a weakest precondition
interpretation, form a thin double category. A monad level is a level `WRPLevels.CatLevel`
through its Kleisli category: its horizontal arrows are programs of one level, composed by
Kleisli composition, and the exactness of its weakest precondition makes the weakest
precondition strict. The objects, arrows, squares and the thin double category of this file
are those of `WRPLevels` at the family of Kleisli levels. Its vertical arrows are data
refinements between levels: a concretization of assertions, an exception map and a return
relation, composed by composing concretizations and relations; and its squares are the
refinements `RefinementWP.Refines` of the abstract program on top by the concrete program at
the bottom, under the left return relation as precondition and at the right return relation
as postcondition (`sq_iff_refines`).

At the trivial precondition a square is the inequality `γ ∘ wp u ⊑ wp w ∘ γ.post R` of data
refinement of predicate transformers (Gardiner and Morgan, "Data refinement of predicate
transformers", TCS 87, 1991), where the concretization `γ` of the vertical arrow is their
representation transformer. Vertical pasting composes
refinements along a chain of levels; horizontal pasting is sequencing.

## Main definitions

* `Level`: a monad with an assertion lattice, an exception postcondition type and an exact
  weakest precondition interpretation.
* `Level.lat`, `Level.wpTrans`: its lattice and the weakest precondition transformer of a
  program.
* `Level.toCatLevel`: the Kleisli level of a monad level.
* `Obj L`: a level index of the family `L` and a value type.
* `VHom L a c`: a data refinement from `a` (abstract) to `c` (concrete).
* `HHom L a b`: a program of one level from the values of `a` to those of `b`.
* `Sq L u f g w`: `w` refines `u` along `f` and `g`.

## Main results

* `sq_iff_refines`: a square is a family of refinements `RefinementWP.Refines`.
* `sq_iff_le_rightAdjoint`, `sq_iff_le_rightAdjoint_of_eq`: the decode/encode form of a square.
* The thin double category and the weakest precondition double functor are
  `WRPLevels.instThinDoubleCategoryObj` and `WRPLevels.wpDouble` at `levels L`.
-/

@[expose] public section

set_option autoImplicit false

open Std.WP Lean.Order

universe u v w w' t

namespace CatCrypt.Refinement.WRPDouble

open CategoryTheory RefinementWP

/-- A level of abstraction: a monad `m`, its assertion lattice `Pred` (a Heyting algebra), its
exception postcondition type `E`, and an exact weakest precondition interpretation of `m`. -/
structure Level where
  /-- The monad of the programs of the level. -/
  m : Type v → Type u
  /-- The assertions of the level. -/
  Pred : Type w
  /-- The exception postconditions of the level. -/
  E : Type w'
  [instMonad : Monad m]
  [instPred : Assertion Pred]
  [instHeyting : Heyting Pred]
  [instE : Assertion E]
  [instWP : WPMonad m Pred E]
  [instExact : WPMonadExact m (Pred := Pred) (EPosts := E)]

attribute [instance] Level.instMonad Level.instPred Level.instHeyting Level.instE Level.instWP
  Level.instExact

namespace Level

/-- The lattice of a level. -/
abbrev lat (ℓ : Level.{u, v, w, w'}) : WRPTransformers.Lat.{w, w'} where
  Pred := ℓ.Pred
  E := ℓ.E

/-- The weakest precondition transformer of a program of a level. -/
def wpTrans (ℓ : Level.{u, v, w, w'}) {X Y : Type v} (p : X → ℓ.m Y) :
    WRPTransformers.Trans ℓ.lat X Y where
  tr Q E x := wp (p x) Q E
  mono _ h _ := WP.wp_monotone_post h

/-- The Kleisli level of a monad level: the Kleisli category of `m`, whose objects are their
own value types, with the weakest precondition `wpTrans`, strict by exactness. -/
def toCatLevel (ℓ : Level.{u, v, w, w'}) : WRPLevels.CatLevel.{v + 1, max v u, v, w, w'} where
  Ob := KleisliCat ℓ.m
  carrier X := X
  lat := ℓ.lat
  wp p := ℓ.wpTrans p
  wp_id X := by
    ext Q E x
    exact WPMonadExact.wp_pure_eq x Q E
  wp_comp f g := by
    ext Q E x
    exact WPMonadExact.wp_bind_eq _ _ Q E

end Level

variable {I : Type t} (L : I → Level.{u, v, w, w'})

/-- The family of Kleisli levels of the monad levels `L`. -/
abbrev levels : I → WRPLevels.CatLevel.{v + 1, max v u, v, w, w'} := fun i => (L i).toCatLevel

/-- An object: a level index of the family `L` and a type of values of that level. -/
abbrev Obj := WRPLevels.Obj (levels L)

/-- A vertical arrow from `a` (abstract) to `c` (concrete): a concretization of the assertions
of `a` into those of `c` that preserves suprema, binary meets, `⊥` and `⊤`, an exception map,
and a return relation between concrete and abstract values. -/
abbrev VHom (a c : Obj L) := WRPLevels.VHom (levels L) a c

/-- A horizontal arrow: a program of one level from the values of its source to those of its
target, composed by Kleisli composition. -/
abbrev HHom (a b : Obj L) := WRPLevels.HHom (levels L) a b

/-- The square with top `u`, left `f`, right `g` and bottom `w`: `w` refines `u` along `f`
and `g` (`sq_iff_refines`). -/
abbrev Sq {a b c d : Obj L} (u : HHom L a b) (f : VHom L a c) (g : VHom L b d)
    (w : HHom L c d) : Prop :=
  WRPLevels.Sq (levels L) u f g w

/-- A square holds if and only if the two vertical arrows have the same concretization and
exception map, and `pw` refines `pu` under the relation `f.R` between the inputs and at the
relation `g.R` between the outputs. -/
theorem sq_iff_refines {i j : I} {X Y X' Y' : Type v} (pu : X → (L i).m Y)
    (f : VHom L ⟨i, X⟩ ⟨j, X'⟩) (g : VHom L ⟨i, Y⟩ ⟨j, Y'⟩) (pw : X' → (L j).m Y') :
    Sq L (.mk pu) f g (.mk pw) ↔
      f.γ = g.γ ∧ f.eps = g.eps ∧ ∀ xc xa, Refines (f.R xc xa) f.γ f.eps (pw xc) (pu xa) g.R := by
  refine and_congr_right fun h1 => and_congr_right fun h2 => Iff.symm ?_
  refine (WRPTransformers.refines_iff_post_le f.γ f.eps f.R g.R pu pw).trans ?_
  change (∀ Qa Ea, f.γ.post f.R (fun xa => wp (pu xa) Qa Ea) ⊑
      fun xc => wp (pw xc) (f.γ.post g.R Qa) (f.eps Ea)) ↔
    ∀ Q E, f.γ.post f.R (fun xa => wp (pu xa) Q E) ⊑
      fun xc => wp (pw xc) (g.γ.post g.R Q) (g.eps E)
  rw [h2, ← h1]
  exact Iff.rfl

/-- The decode/encode form of a refinement square: the weakest precondition of the abstract
program is below that of the concrete program conjugated by the conjoint `g*` of the right
arrow and the right adjoint `f*ʳ` of the conjoint of the left arrow. -/
theorem sq_iff_le_rightAdjoint {i j : I} {X Y X' Y' : Type v} (pu : X → (L i).m Y)
    (f : VHom L ⟨i, X⟩ ⟨j, X'⟩) (g : VHom L ⟨i, Y⟩ ⟨j, Y'⟩)
    (pw : X' → (L j).m Y') (hf : f.γ.SupPreserving.{_, max v w}) :
    Sq L (.mk pu) f g (.mk pw) ↔ f.γ = g.γ ∧ f.eps = g.eps ∧
      ∀ Q E, (fun xa => wp (pu xa) Q E) ⊑
        (f.γ.conjoint f.R).rightAdjoint
          (fun xc => wp (pw xc) ((g.γ.conjoint g.R).pred Q) (g.eps E)) :=
  WRPLevels.Sq.iff_le_rightAdjoint (L := levels L) pu f g pw hf

/-- The decode/encode form of a refinement square when assertions and values share a universe;
the supremum preservation of the vertical arrow suffices. -/
theorem sq_iff_le_rightAdjoint_of_eq {L : I → Level.{u, v, v, w'}} {i j : I}
    {X Y X' Y' : Type v} (pu : X → (L i).m Y) (f : VHom L ⟨i, X⟩ ⟨j, X'⟩)
    (g : VHom L ⟨i, Y⟩ ⟨j, Y'⟩) (pw : X' → (L j).m Y') :
    Sq L (.mk pu) f g (.mk pw) ↔ f.γ = g.γ ∧ f.eps = g.eps ∧
      ∀ Q E, (fun xa => wp (pu xa) Q E) ⊑
        (f.γ.conjoint f.R).rightAdjoint
          (fun xc => wp (pw xc) ((g.γ.conjoint g.R).pred Q) (g.eps E)) :=
  sq_iff_le_rightAdjoint L pu f g pw f.sup

-- The vertical identity square: every program refines itself along the identity.
example {i : I} {X Y : Type v} (pu : X → (L i).m Y) :
    Sq L (.mk pu) (WRPTransformers.VHom.id _) (WRPTransformers.VHom.id _) (.mk pu) :=
  WRPLevels.Sq.vid _

-- Horizontal composition of programs of a monad level is Kleisli composition.
example {i : I} {X Y Z : Type v} (p : X → (L i).m Y) (q : Y → (L i).m Z) :
    (.mk p : HHom L ⟨i, X⟩ ⟨i, Y⟩).comp (.mk q) = .mk fun x => p x >>= q := rfl

-- The horizontal identity of a monad level is `pure`.
example (a : Obj L) :
    (WRPLevels.HHom.id a : HHom L a a) = .mk (pure : a.ob → (L a.lvl).m a.ob) :=
  rfl

end CatCrypt.Refinement.WRPDouble

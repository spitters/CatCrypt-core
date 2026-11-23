/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.WRPTransformers

/-!
# Refinement squares over categories of programs

A level of abstraction is a category of programs together with a weakest precondition map into
the predicate transformers `WRPTransformers.Trans` of one assertion lattice, strict: it sends
identities to the identity transformer and composites to composite transformers. The objects
of a level carry value types, and the weakest precondition of a program from `X` to `Y` is a
transformer from postconditions on the values of `Y` to preconditions on the values of `X`.

Over a family of levels, the objects are a level index and an object of that level, the
horizontal arrows are programs of one level, the vertical arrows are the vertical arrows of
predicate transformers between the images of the objects, and a square is a square of
predicate transformers between the weakest preconditions of its horizontal sides. These form a
thin double category, and the weakest precondition is a thin double functor into predicate
transformers that is full on squares.

The monad levels of `WRPDouble` are the Kleisli instances of this construction; quantum
channels of one dimension form a level in `WRPLevelsQuantum`.

## Main definitions

* `CatLevel`: a category of programs with value types, an assertion lattice and a strict
  weakest precondition map.
* `Obj L`: a level index of the family `L` and an object of that level; `wpObj L a`, its
  object of predicate transformers.
* `VHom L a c`, `HHom L a b`, `Sq L u f g w`: the arrows and squares.
* `wpH L u`: the weakest precondition transformer of a horizontal arrow.
* `wpDouble L`: the weakest precondition `CategoryTheory.ThinDoubleFunctor` into
  `WRPTransformers.Obj`.

## Main results

* `wpH_id`, `wpH_comp`: the weakest precondition is strict on horizontal arrows.
* `instThinDoubleCategoryObj`: refinement squares over a family of levels form a thin double
  category.
* `wpDouble_sq_iff`: the weakest precondition double functor is full on squares.
* `Sq.iff_le_rightAdjoint`: the decode/encode form of a square.
-/

@[expose] public section

set_option autoImplicit false

open Lean.Order

universe o h v w w' t

namespace CatCrypt.Refinement.WRPLevels

open CategoryTheory

/-- A level of abstraction: a category of programs `Ob`, a value type `carrier X` of each
object, an assertion lattice `lat`, and a weakest precondition map `wp` from programs to
predicate transformers of `lat` that preserves identities and composites. -/
structure CatLevel where
  /-- The objects of the level. -/
  Ob : Type o
  /-- The category of programs. -/
  [cat : Category.{h} Ob]
  /-- The value type of an object. -/
  carrier : Ob → Type v
  /-- The assertion lattice. -/
  lat : WRPTransformers.Lat.{w, w'}
  /-- The weakest precondition transformer of a program. -/
  wp {X Y : Ob} : (X ⟶ Y) → WRPTransformers.Trans lat (carrier X) (carrier Y)
  /-- The weakest precondition of the identity program is the identity transformer. -/
  wp_id (X : Ob) : wp (𝟙 X) = WRPTransformers.Trans.id (carrier X)
  /-- The weakest precondition of a composite is the composite transformer. -/
  wp_comp {X Y Z : Ob} (f : X ⟶ Y) (g : Y ⟶ Z) : wp (f ≫ g) = (wp f).comp (wp g)

attribute [instance] CatLevel.cat

variable {I : Type t} (L : I → CatLevel.{o, h, v, w, w'})

/-- An object: a level index of the family `L` and an object of that level. -/
structure Obj (L : I → CatLevel.{o, h, v, w, w'}) where
  /-- The level index. -/
  lvl : I
  /-- The object of the level. -/
  ob : (L lvl).Ob

/-- The object of predicate transformers of an object: the lattice of its level and its value
type. -/
def wpObj (a : Obj L) : WRPTransformers.Obj.{v, w, w'} :=
  ⟨(L a.lvl).lat, (L a.lvl).carrier a.ob⟩

/-- A vertical arrow: a vertical arrow of predicate transformers between the images. -/
abbrev VHom (a c : Obj L) : Type _ :=
  WRPTransformers.VHom (wpObj L a) (wpObj L c)

/-- The vertical category: the vertical arrows of predicate transformers between the
images. -/
noncomputable instance instCategoryObj : Category (Obj L) where
  Hom a c := VHom L a c
  id a := WRPTransformers.VHom.id (wpObj L a)
  comp f g := WRPTransformers.VHom.comp f g
  id_comp f := Category.id_comp (obj := WRPTransformers.Obj) f
  comp_id f := Category.comp_id (obj := WRPTransformers.Obj) f
  assoc f g h := Category.assoc (obj := WRPTransformers.Obj) f g h

/-- A horizontal arrow: a program of one level. -/
inductive HHom : Obj L → Obj L → Type (max t o h)
  | mk {i : I} {X Y : (L i).Ob} (p : X ⟶ Y) : HHom ⟨i, X⟩ ⟨i, Y⟩

namespace HHom

variable {L}

/-- The identity program. -/
def id (a : Obj L) : HHom L a a :=
  HHom.mk (i := a.lvl) (X := a.ob) (𝟙 a.ob)

/-- Composition of programs of one level. -/
def comp : {a b c : Obj L} → HHom L a b → HHom L b c → HHom L a c
  | _, _, _, .mk p, .mk q => .mk (p ≫ q)

/-- The identity is a left unit. -/
theorem id_comp {a b : Obj L} (f : HHom L a b) : (HHom.id a).comp f = f := by
  cases f
  simp [HHom.comp, HHom.id]

/-- The identity is a right unit. -/
theorem comp_id {a b : Obj L} (f : HHom L a b) : f.comp (HHom.id b) = f := by
  cases f
  simp [HHom.comp, HHom.id]

/-- Composition is associative. -/
theorem comp_assoc {a b c d : Obj L} (f : HHom L a b) (g : HHom L b c) (h : HHom L c d) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  cases f
  cases g
  cases h
  simp [HHom.comp]

end HHom

/-- The horizontal category: programs of one level. -/
instance instCategoryHorObj : Category (Hor (Obj L)) where
  Hom a b := HHom L a b
  id a := HHom.id (L := L) a
  comp f g := HHom.comp f g
  id_comp f := HHom.id_comp f
  comp_id f := HHom.comp_id f
  assoc f g h := HHom.comp_assoc f g h

/-- The weakest precondition transformer of a horizontal arrow. -/
def wpH : {a b : Obj L} → HHom L a b → WRPTransformers.HHom (wpObj L a) (wpObj L b)
  | _, _, .mk p => .mk ((L _).wp p)

/-- `wpH` sends the identity program to the identity transformer. -/
theorem wpH_id (a : Obj L) : wpH L (HHom.id a) = WRPTransformers.HHom.id (wpObj L a) := by
  change WRPTransformers.HHom.mk ((L a.lvl).wp (𝟙 a.ob)) = WRPTransformers.HHom.mk _
  rw [CatLevel.wp_id]
  rfl

/-- `wpH` sends composites to composite transformers. -/
theorem wpH_comp {a b c : Obj L} (u : HHom L a b) (u' : HHom L b c) :
    wpH L (u.comp u') = (wpH L u).comp (wpH L u') := by
  cases u with
  | mk p =>
  cases u' with
  | mk q =>
  change WRPTransformers.HHom.mk ((L _).wp (p ≫ q)) = WRPTransformers.HHom.mk _
  rw [CatLevel.wp_comp]

/-- The square with top `u`, left `f`, right `g` and bottom `w`: the square of predicate
transformers between the weakest preconditions of `u` and `w`. -/
def Sq {a b c d : Obj L} (u : HHom L a b) (f : VHom L a c) (g : VHom L b d)
    (w : HHom L c d) : Prop :=
  WRPTransformers.Sq (wpH L u) f g (wpH L w)

variable {L}

/-- Vertical pasting of squares. -/
theorem Sq.vcomp {a b c d c' d' : Obj L} {u : HHom L a b} {f : VHom L a c}
    {g : VHom L b d} {w : HHom L c d} {f' : VHom L c c'} {g' : VHom L d d'} {z : HHom L c' d'}
    (s : Sq L u f g w) (t : Sq L w f' g' z) : Sq L u (f.comp f') (g.comp g') z :=
  WRPTransformers.Sq.vcomp s t

/-- Horizontal pasting of squares. -/
theorem Sq.hcomp {a b b' c d d' : Obj L} {u : HHom L a b} {f : VHom L a c}
    {g : VHom L b d} {w : HHom L c d} {u' : HHom L b b'} {k : VHom L b' d'}
    {w' : HHom L d d'} (s : Sq L u f g w) (s' : Sq L u' g k w') :
    Sq L (u.comp u') f k (w.comp w') := by
  unfold Sq
  rw [wpH_comp, wpH_comp]
  exact WRPTransformers.Sq.hcomp s s'

/-- The vertical identity square. -/
theorem Sq.vid {a b : Obj L} (u : HHom L a b) :
    Sq L u (WRPTransformers.VHom.id _) (WRPTransformers.VHom.id _) u :=
  WRPTransformers.Sq.vid _

/-- The horizontal identity square. -/
theorem Sq.hid {a c : Obj L} (f : VHom L a c) : Sq L (HHom.id a) f f (HHom.id c) := by
  unfold Sq
  rw [wpH_id, wpH_id]
  exact WRPTransformers.Sq.hid f

/-- Refinement squares over the family of levels `L` form a thin double category. -/
noncomputable instance instThinDoubleCategoryObj : ThinDoubleCategory (Obj L) where
  Sq u f g w := Sq L u f g w
  vcomp s t := Sq.vcomp s t
  hcomp s t := Sq.hcomp s t
  vid u := Sq.vid u
  hid f := Sq.hid f

variable (L)

/-- The weakest precondition thin double functor into predicate transformers: `wpObj` on
objects, the identity on vertical arrows and `wpH` on horizontal arrows. -/
noncomputable def wpDouble : ThinDoubleFunctor (Obj L) WRPTransformers.Obj.{v, w, w'} where
  obj := wpObj L
  mapV f := f
  mapH u := wpH L u
  mapV_id _ := rfl
  mapV_comp _ _ := rfl
  mapH_id a := wpH_id L a
  mapH_comp u u' := wpH_comp L u u'
  map_sq s := s

/-- The weakest precondition double functor is full on squares: a square holds if and only if
its image holds. -/
theorem wpDouble_sq_iff {a b c d : Obj L} (u : HHom L a b) (f : VHom L a c) (g : VHom L b d)
    (w : HHom L c d) :
    Sq L u f g w ↔
      ThinDoubleCategory.Sq ((wpDouble L).mapH u) ((wpDouble L).mapV f) ((wpDouble L).mapV g)
        ((wpDouble L).mapH w) :=
  Iff.rfl

/-- The decode/encode form of a square between programs `p` and `q`: the weakest
precondition of `p` is below that of `q` conjugated by the conjoint of the right arrow and the
right adjoint of the conjoint of the left arrow. -/
theorem Sq.iff_le_rightAdjoint {i j : I} {X Y : (L i).Ob} {X' Y' : (L j).Ob} (p : X ⟶ Y)
    (f : VHom L ⟨i, X⟩ ⟨j, X'⟩) (g : VHom L ⟨i, Y⟩ ⟨j, Y'⟩) (q : X' ⟶ Y')
    (hf : f.γ.SupPreserving.{_, max v w}) :
    Sq L (.mk p) f g (.mk q) ↔ f.γ = g.γ ∧ f.eps = g.eps ∧
      ∀ Q E, ((L i).wp p).tr Q E ⊑
        f.conj.rightAdjoint (((L j).wp q).tr (g.conj.pred Q) (g.eps E)) :=
  WRPTransformers.Sq.iff_le_rightAdjoint hf

end CatCrypt.Refinement.WRPLevels

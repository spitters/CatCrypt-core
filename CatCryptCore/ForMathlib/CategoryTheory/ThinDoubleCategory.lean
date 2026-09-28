/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Logic.Relation

/-!
# Thin double categories

A *double category* (Ehresmann) has objects, two classes of arrows between them — the
vertical and the horizontal arrows, each forming a category — and squares bounded by two
vertical and two horizontal arrows, which compose vertically and horizontally subject to
associativity, unit and interchange laws. A double category is *thin* when there is at most
one square with a given boundary; it is then determined by its two categories and the
predicate on boundaries saying which squares exist, and every coherence law holds
automatically.

This file defines thin double categories with the squares valued in `Prop`, proves the
associativity, unit and interchange laws (each by proof irrelevance), and gives two
families of examples:

* `CommSqDouble C`: for a category `C`, the thin double category whose vertical and
  horizontal categories are both `C` and whose squares are the commutative squares
  `CategoryTheory.CommSq` (the *double category of squares* of `C`);
* `ThinDoubleCategory.ofRelSemantics`: for a category of horizontal arrows interpreted as
  relations between carrier types, the thin double category whose vertical arrows are
  relations between the carriers and whose squares are the lax commutative squares
  `f ; w ⊆ u ; g` in the bicategory of relations, i.e. the forward simulations of the
  interpretation of `w` by the interpretation of `u`.

Mathlib candidate for a new file `Mathlib/CategoryTheory/DoubleCategory/Thin.lean`.
Mathlib has `CommSq`, the bicategory API and the category `RelCat`, but no double category.

## Implementation notes

The two categories share their objects. The vertical category is an instance on `C`; the
horizontal one is an instance on the type synonym `Hor C`, so that the two `Category`
instances do not conflict. `Hor.of a` is `a` viewed as an object of the horizontal
category. Following `CommSq f g h i`, a square is written `Sq u f g w` with `u` the top,
`f` the left, `g` the right and `w` the bottom side.

## References

* C. Ehresmann, *Catégories structurées*, Ann. Sci. École Norm. Sup. 80 (1963).
* M. Grandis, R. Paré, *Limits in double categories*, Cahiers Topologie Géom.
  Différentielle Catég. 40 (1999).
* R. Brown, C. B. Spencer, *Double groupoids and crossed modules*, Cahiers Topologie Géom.
  Différentielle Catég. 17 (1976) (the double category of commutative squares).
-/

@[expose] public section

set_option autoImplicit false

universe v w u u'

namespace CategoryTheory

/-- The objects of `C`, viewed as the objects of its horizontal category. A type synonym, so
that a horizontal `Category` instance on `Hor C` sits beside the vertical one on `C`. -/
def Hor (C : Type u) : Type u := C

/-- An object of `C`, viewed as an object of the horizontal category. -/
def Hor.of {C : Type u} (a : C) : Hor C := a

/-- The object of `C` underlying an object of the horizontal category. -/
def Hor.as {C : Type u} (a : Hor C) : C := a

@[simp] theorem Hor.as_of {C : Type u} (a : C) : (Hor.of a).as = a := rfl

@[simp] theorem Hor.of_as {C : Type u} (a : Hor C) : Hor.of a.as = a := rfl

/-- A **thin double category** on the objects `C`: a vertical category (the instance on `C`),
a horizontal category (the instance on `Hor C`), and for each boundary a proposition `Sq`
saying that a square with that boundary exists. Squares paste vertically and horizontally,
and the identity arrows in each direction carry identity squares. The coherence laws are the
theorems `ThinDoubleCategory.vcomp_assoc`, `ThinDoubleCategory.interchange` and their
siblings; they hold by proof irrelevance. -/
class ThinDoubleCategory (C : Type u) [Category.{v} C] [Category.{w} (Hor C)] where
  /-- A square with top `u`, left `f`, right `g` and bottom `w`. -/
  Sq {a b c d : C} (u : Hor.of a ⟶ Hor.of b) (f : a ⟶ c) (g : b ⟶ d)
    (w : Hor.of c ⟶ Hor.of d) : Prop
  /-- Vertical pasting: the bottom of the first square is the top of the second. -/
  vcomp {a b c d c' d' : C} {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} {f' : c ⟶ c'} {g' : d ⟶ d'} {z : Hor.of c' ⟶ Hor.of d'} :
    Sq u f g w → Sq w f' g' z → Sq u (f ≫ f') (g ≫ g') z
  /-- Horizontal pasting: the right side of the first square is the left side of the
  second. -/
  hcomp {a b b' c d d' : C} {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} {u' : Hor.of b ⟶ Hor.of b'} {k : b' ⟶ d'}
    {w' : Hor.of d ⟶ Hor.of d'} :
    Sq u f g w → Sq u' g k w' → Sq (u ≫ u') f k (w ≫ w')
  /-- The vertical identity square on a horizontal arrow. -/
  vid {a b : C} (u : Hor.of a ⟶ Hor.of b) : Sq u (𝟙 a) (𝟙 b) u
  /-- The horizontal identity square on a vertical arrow. -/
  hid {a c : C} (f : a ⟶ c) : Sq (𝟙 (Hor.of a)) f f (𝟙 (Hor.of c))

namespace ThinDoubleCategory

variable {C : Type u} [Category.{v} C] [Category.{w} (Hor C)] [ThinDoubleCategory C]

variable {a b c d : C}

/-- A square can be moved along equalities of its four sides. -/
theorem Sq.congr {u u' : Hor.of a ⟶ Hor.of b} {f f' : a ⟶ c} {g g' : b ⟶ d}
    {w w' : Hor.of c ⟶ Hor.of d} (s : Sq u f g w) (hu : u = u') (hf : f = f') (hg : g = g')
    (hw : w = w') : Sq u' f' g' w' := by
  subst hu hf hg hw; exact s

/-- **Interchange.** Pasting a two-by-two grid of squares row by row and then vertically is
pasting it column by column and then horizontally. Both sides prove the same proposition. -/
theorem interchange {b' c' d' e e' : C} {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} {f' : c ⟶ e} {g' : d ⟶ e'} {z : Hor.of e ⟶ Hor.of e'}
    {u' : Hor.of b ⟶ Hor.of b'} {k : b' ⟶ d'} {w' : Hor.of d ⟶ Hor.of d'} {k' : d' ⟶ c'}
    {z' : Hor.of e' ⟶ Hor.of c'}
    (s : Sq u f g w) (t : Sq w f' g' z) (s' : Sq u' g k w') (t' : Sq w' g' k' z') :
    hcomp (vcomp s t) (vcomp s' t') = vcomp (hcomp s s') (hcomp t t') :=
  rfl

/-- Vertical pasting is associative. The two composites have boundaries that agree up to
`Category.assoc`, so the law is a heterogeneous equality. -/
theorem vcomp_assoc {c' d' c'' d'' : C} {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} {f' : c ⟶ c'} {g' : d ⟶ d'} {z : Hor.of c' ⟶ Hor.of d'}
    {f'' : c' ⟶ c''} {g'' : d' ⟶ d''} {y : Hor.of c'' ⟶ Hor.of d''}
    (s : Sq u f g w) (t : Sq w f' g' z) (r : Sq z f'' g'' y) :
    vcomp (vcomp s t) r ≍ vcomp s (vcomp t r) :=
  proof_irrel_heq _ _

/-- Horizontal pasting is associative, up to the heterogeneous equality forced by
`Category.assoc` in the horizontal category. -/
theorem hcomp_assoc {b' d' b'' d'' : C} {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} {u' : Hor.of b ⟶ Hor.of b'} {k : b' ⟶ d'}
    {w' : Hor.of d ⟶ Hor.of d'} {u'' : Hor.of b' ⟶ Hor.of b''} {l : b'' ⟶ d''}
    {w'' : Hor.of d' ⟶ Hor.of d''}
    (s : Sq u f g w) (s' : Sq u' g k w') (s'' : Sq u'' k l w'') :
    hcomp (hcomp s s') s'' ≍ hcomp s (hcomp s' s'') :=
  proof_irrel_heq _ _

/-- The vertical identity square is a left unit for vertical pasting. -/
theorem vid_vcomp {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} (s : Sq u f g w) : vcomp (vid u) s ≍ s :=
  proof_irrel_heq _ _

/-- The vertical identity square is a right unit for vertical pasting. -/
theorem vcomp_vid {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} (s : Sq u f g w) : vcomp s (vid w) ≍ s :=
  proof_irrel_heq _ _

/-- The horizontal identity square is a left unit for horizontal pasting. -/
theorem hid_hcomp {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} (s : Sq u f g w) : hcomp (hid f) s ≍ s :=
  proof_irrel_heq _ _

/-- The horizontal identity square is a right unit for horizontal pasting. -/
theorem hcomp_hid {u : Hor.of a ⟶ Hor.of b} {f : a ⟶ c} {g : b ⟶ d}
    {w : Hor.of c ⟶ Hor.of d} (s : Sq u f g w) : hcomp s (hid g) ≍ s :=
  proof_irrel_heq _ _

/-- Horizontal identity squares paste vertically to the horizontal identity square on the
composite vertical arrow. -/
theorem vcomp_hid {c' : C} (f : a ⟶ c) (f' : c ⟶ c') :
    vcomp (hid (C := C) f) (hid f') = hid (f ≫ f') :=
  rfl

/-- Vertical identity squares paste horizontally to the vertical identity square on the
composite horizontal arrow. -/
theorem hcomp_vid {b' : C} (u : Hor.of a ⟶ Hor.of b) (u' : Hor.of b ⟶ Hor.of b') :
    hcomp (vid (C := C) u) (vid u') = vid (u ≫ u') :=
  rfl

/-- The two identity squares on an object coincide. -/
theorem vid_id_eq_hid_id (a : C) : vid (C := C) (𝟙 (Hor.of a)) = hid (𝟙 a) :=
  rfl

end ThinDoubleCategory

/-! ## The double category of commutative squares -/

/-- The objects of `C`, carrying the thin double category of commutative squares of `C`:
vertical and horizontal categories are both `C`, and the squares are the `CommSq`s. -/
def CommSqDouble (C : Type u) : Type u := C

namespace CommSqDouble

variable (C : Type u) [Category.{v} C]

instance : Category.{v} (CommSqDouble C) := inferInstanceAs (Category.{v} C)

instance : Category.{v} (Hor (CommSqDouble C)) := inferInstanceAs (Category.{v} C)

/-- The commutative squares of `C` form a thin double category. Pasting is
`CommSq.vert_comp` and `CommSq.horiz_comp`. -/
instance : ThinDoubleCategory (CommSqDouble C) where
  Sq {a b c d} u f g w := CommSq (C := C) (X := b) (Y := c) (Z := d) (W := a) u f g w
  vcomp s t := CommSq.vert_comp (C := C) s t
  hcomp s t := CommSq.horiz_comp (C := C) s t
  vid u := ⟨(Category.comp_id (obj := C) u).trans (Category.id_comp (obj := C) u).symm⟩
  hid f := ⟨(Category.id_comp (obj := C) f).trans (Category.comp_id (obj := C) f).symm⟩

/-- A square of `CommSqDouble C` is a commutative square of `C`. -/
theorem sq_iff {a b c d : C} (u : a ⟶ b) (f : a ⟶ c) (g : b ⟶ d) (w : c ⟶ d) :
    ThinDoubleCategory.Sq (C := CommSqDouble C) (a := a) (b := b) (c := c) (d := d) u f g w ↔
      CommSq u f g w :=
  Iff.rfl

end CommSqDouble

/-! ## Squares of relations over a relational semantics -/

namespace ThinDoubleCategory

variable {C : Type u} (X : C → Type u')

/-- The category of relations between the carriers `X a`: an arrow `a ⟶ c` is a relation
`X a → X c → Prop`, composition is `Relation.Comp` and the identity is equality. This is the
full subcategory of the category of relations spanned by the carriers. -/
abbrev relCategory : Category.{max u' 0} C where
  Hom a c := X a → X c → Prop
  id _ := (· = ·)
  comp r s := Relation.Comp r s
  id_comp r := by
    funext x y; apply propext
    exact ⟨fun ⟨_, h, hr⟩ => h ▸ hr, fun hr => ⟨x, rfl, hr⟩⟩
  comp_id r := by
    funext x y; apply propext
    exact ⟨fun ⟨_, hr, h⟩ => h ▸ hr, fun hr => ⟨y, hr, rfl⟩⟩
  assoc r s t := by
    funext x y; apply propext
    exact ⟨fun ⟨m, ⟨n, hr, hs⟩, ht⟩ => ⟨n, hr, m, hs, ht⟩,
      fun ⟨n, hr, m, hs, ht⟩ => ⟨m, ⟨n, hr, hs⟩, ht⟩⟩

variable [Category.{w} (Hor C)]

/-- A **relational semantics** of the horizontal category: every horizontal arrow
`a ⟶ b` denotes a relation `X a → X b → Prop`, functorially — the identity denotes equality
and a composite denotes the relational composite. Equivalently, a functor from `Hor C` to
the category of relations whose object map is `X`. -/
structure RelSemantics where
  /-- The relation a horizontal arrow denotes. -/
  sem {a b : C} : (Hor.of a ⟶ Hor.of b) → X a → X b → Prop
  /-- The identity denotes equality. -/
  sem_id (a : C) : sem (𝟙 (Hor.of a)) = (· = ·)
  /-- A composite denotes the relational composite. -/
  sem_comp {a b c : C} (u : Hor.of a ⟶ Hor.of b) (u' : Hor.of b ⟶ Hor.of c) :
    sem (u ≫ u') = Relation.Comp (sem u) (sem u')

variable {X}

/-- The **lax square** of relations over a semantics: `f ; ⟦w⟧ ⊆ ⟦u⟧ ; g`. Read as a
simulation: from `x` related to `y` by the left side and a step of the bottom arrow from
`y` to `y'`, the top arrow steps from `x` to some `x'` related to `y'` by the right side. -/
def RelSemantics.LaxSq (S : RelSemantics X) {a b c d : C} (u : Hor.of a ⟶ Hor.of b)
    (f : X a → X c → Prop) (g : X b → X d → Prop) (w : Hor.of c ⟶ Hor.of d) : Prop :=
  ∀ x y y', f x y → S.sem w y y' → ∃ x', S.sem u x x' ∧ g x' y'

/-- The thin double category of lax squares over a relational semantics: vertical arrows are
relations between carriers (`relCategory X`), horizontal arrows are those of `Hor C`, and
the squares are `RelSemantics.LaxSq`. -/
abbrev ofRelSemantics (S : RelSemantics X) :
    @ThinDoubleCategory C (relCategory X) _ :=
  letI := relCategory X
  { Sq := fun u f g w => S.LaxSq u f g w
    vcomp := by
      intro a b c d c' d' u f g w f' g' z s t x y y' ⟨m, hf, hf'⟩ hz
      obtain ⟨m', hw, hg'⟩ := t m y y' hf' hz
      obtain ⟨x', hu, hg⟩ := s x m m' hf hw
      exact ⟨x', hu, m', hg, hg'⟩
    hcomp := by
      intro a b b' c d d' u f g w u' k w' s s' x y y' hf hww
      rw [S.sem_comp] at hww
      obtain ⟨m, hw, hw'⟩ := hww
      obtain ⟨x₁, hu, hg⟩ := s x y m hf hw
      obtain ⟨x₂, hu', hk⟩ := s' x₁ m y' hg hw'
      exact ⟨x₂, by rw [S.sem_comp]; exact ⟨x₁, hu, hu'⟩, hk⟩
    vid := by
      intro a b u x y y' hxy hw
      exact ⟨y', hxy ▸ hw, rfl⟩
    hid := by
      intro a c f x y y' hf hid
      rw [S.sem_id] at hid
      exact ⟨x, by rw [S.sem_id], hid ▸ hf⟩ }

/-- In `ofRelSemantics S`, a square is a lax square of relations. -/
theorem ofRelSemantics_sq (S : RelSemantics X) {a b c d : C} (u : Hor.of a ⟶ Hor.of b)
    (f : X a → X c → Prop) (g : X b → X d → Prop) (w : Hor.of c ⟶ Hor.of d) :
    @Sq C (relCategory X) _ (ofRelSemantics S) a b c d u f g w ↔ S.LaxSq u f g w :=
  Iff.rfl

end ThinDoubleCategory

end CategoryTheory

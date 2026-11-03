/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Basic.ENNReal.Basic

/-!
# The symmetric monoidal category of Lawvere metric spaces

A Lawvere metric space is a type with a distance `ldist : X → X → ℝ≥0∞` satisfying
`ldist x x = 0` and the triangle inequality `ldist x z ≤ ldist x y + ldist y z`. The distance
need not be symmetric, and distance `0` need not imply equality; these are the categories
enriched in Lawvere's quantale `([0,∞], ≥, +, 0)`. Mathlib's `PseudoEMetricSpace` requires
symmetry, so it is the special case of a symmetric distance.

The morphisms of `LawvereMet` are the non-expansive maps, `ldist (f x) (f y) ≤ ldist x y`.
The tensor product is the cartesian product with the `ℓ¹` distance,
`ldist (x, y) (x', y') = ldist x x' + ldist y y'`, and the unit is the one-point space. The
associator, unitors and braiding are the evident bijections, which preserve the distance; all
coherence laws are equalities of underlying functions.

## Main definitions

* `LawvereMetricSpace`: a type with a distance in `ℝ≥0∞` that vanishes on the diagonal and
  satisfies the triangle inequality.
* `LawvereMetricSpace.prod`: the `ℓ¹` product of two Lawvere metric spaces.
* `LawvereMet`: the category of Lawvere metric spaces and non-expansive maps.
* `LawvereMet.monoidalCategory`, `LawvereMet.symmetricCategory`: the symmetric monoidal
  structure with the `ℓ¹` tensor product.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

universe u

/-- A Lawvere metric space: a distance in `ℝ≥0∞` that is `0` on the diagonal and satisfies the
triangle inequality, with no symmetry or separation condition. -/
class LawvereMetricSpace (X : Type u) where
  /-- The distance from `x` to `y`. -/
  ldist : X → X → ℝ≥0∞
  /-- The distance from a point to itself is `0`. -/
  ldist_self : ∀ x, ldist x x = 0
  /-- The triangle inequality. -/
  ldist_triangle : ∀ x y z, ldist x z ≤ ldist x y + ldist y z

export LawvereMetricSpace (ldist ldist_self ldist_triangle)

attribute [simp] ldist_self

namespace LawvereMetricSpace

/-- The `ℓ¹` product of two Lawvere metric spaces: the distance of pairs is the sum of the
distances of their components. -/
instance prod (X Y : Type u) [LawvereMetricSpace X] [LawvereMetricSpace Y] :
    LawvereMetricSpace (X × Y) where
  ldist p q := ldist p.1 q.1 + ldist p.2 q.2
  ldist_self p := by simp
  ldist_triangle p q r :=
    (add_le_add (ldist_triangle p.1 q.1 r.1) (ldist_triangle p.2 q.2 r.2)).trans_eq
      (add_add_add_comm _ _ _ _)

/-- Unfolding lemma of the `ℓ¹` product distance. -/
@[simp] theorem ldist_prod {X Y : Type u} [LawvereMetricSpace X] [LawvereMetricSpace Y]
    (p q : X × Y) : ldist p q = ldist p.1 q.1 + ldist p.2 q.2 := rfl

/-- The one-point Lawvere metric space. -/
instance punit : LawvereMetricSpace PUnit.{u + 1} where
  ldist _ _ := 0
  ldist_self _ := rfl
  ldist_triangle _ _ _ := by simp

/-- The distance of the one-point space is `0`. -/
@[simp] theorem ldist_punit (p q : PUnit.{u + 1}) : ldist p q = 0 := rfl

end LawvereMetricSpace

/-- The category of Lawvere metric spaces: a type with a `LawvereMetricSpace` structure. -/
structure LawvereMet : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  /-- The Lawvere metric. -/
  [str : LawvereMetricSpace carrier]

attribute [instance] LawvereMet.str

namespace LawvereMet

instance : CoeSort LawvereMet.{u} (Type u) := ⟨carrier⟩

/-- The object of `LawvereMet` of a Lawvere metric space. -/
abbrev of (X : Type u) [LawvereMetricSpace X] : LawvereMet.{u} := ⟨X⟩

/-- A non-expansive map between Lawvere metric spaces. -/
@[ext] structure Hom (X Y : LawvereMet.{u}) where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The map does not increase distances. -/
  ldist_le : ∀ x y, ldist (toFun x) (toFun y) ≤ ldist x y

/-- Lawvere metric spaces and non-expansive maps form a category. -/
instance category : CategoryTheory.Category LawvereMet.{u} where
  Hom := Hom
  id _ := ⟨id, fun _ _ => le_rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun x y => (g.ldist_le _ _).trans (f.ldist_le x y)⟩

open CategoryTheory MonoidalCategory

/-- Two non-expansive maps with the same underlying function are equal. -/
@[ext] theorem hom_ext {X Y : LawvereMet.{u}} {f g : X ⟶ Y}
    (h : ∀ x, Hom.toFun f x = Hom.toFun g x) : f = g :=
  Hom.ext (funext h)

/-- Unfolding lemma of the identity of `LawvereMet`. -/
@[simp] theorem id_toFun (X : LawvereMet.{u}) (x : X) : Hom.toFun (𝟙 X) x = x := rfl

/-- Unfolding lemma of the composition of `LawvereMet`. -/
@[simp] theorem comp_toFun {X Y Z : LawvereMet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    Hom.toFun (f ≫ g) x = Hom.toFun g (Hom.toFun f x) := rfl

/-- An isomorphism of `LawvereMet` from a distance-preserving bijection. -/
def isoMk {X Y : LawvereMet.{u}} (f : X → Y) (g : Y → X)
    (hf : ∀ x x', ldist (f x) (f x') = ldist x x') (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) : X ≅ Y where
  hom := ⟨f, fun x x' => (hf x x').le⟩
  inv := ⟨g, fun y y' => by
    rw [← hf, hfg, hfg]⟩
  hom_inv_id := by ext x; exact hgf x
  inv_hom_id := by ext y; exact hfg y

/-- The tensor product of morphisms of `LawvereMet`: `Prod.map` of non-expansive maps is
non-expansive for the `ℓ¹` distance. -/
def tensorHom' {X₁ Y₁ X₂ Y₂ : LawvereMet.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    of (X₁ × X₂) ⟶ of (Y₁ × Y₂) :=
  ⟨Prod.map (Hom.toFun f) (Hom.toFun g), fun p q =>
    add_le_add (Hom.ldist_le f p.1 q.1) (Hom.ldist_le g p.2 q.2)⟩

/-- The symmetric monoidal structure of `LawvereMet`: the tensor product is the cartesian
product with the `ℓ¹` distance and the unit is the one-point space. -/
instance monoidalCategory : MonoidalCategory LawvereMet.{u} where
  tensorObj X Y := of (X × Y)
  whiskerLeft X _ _ g := tensorHom' (𝟙 X) g
  whiskerRight f Y := tensorHom' f (𝟙 Y)
  tensorHom f g := tensorHom' f g
  tensorUnit := of PUnit
  associator X Y Z := isoMk (fun p => (p.1.1, (p.1.2, p.2))) (fun p => ((p.1, p.2.1), p.2.2))
    (fun _ _ => by simp [add_assoc]) (fun _ => rfl) (fun _ => rfl)
  leftUnitor X := isoMk (fun p => p.2) (fun x => (PUnit.unit, x))
    (fun _ _ => by simp) (fun _ => rfl) (fun _ => rfl)
  rightUnitor X := isoMk (fun p => p.1) (fun x => (x, PUnit.unit))
    (fun _ _ => by simp) (fun _ => rfl) (fun _ => rfl)
  tensorHom_def _ _ := rfl
  id_tensorHom_id _ _ := rfl
  tensorHom_comp_tensorHom _ _ _ _ := rfl
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality _ _ _ := rfl
  leftUnitor_naturality _ := rfl
  rightUnitor_naturality _ := rfl
  pentagon _ _ _ _ := rfl
  triangle _ _ := rfl

/-- The symmetric structure of `LawvereMet`: the braiding swaps the components. -/
instance symmetricCategory : SymmetricCategory LawvereMet.{u} where
  braiding _ _ := isoMk (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
    (fun _ _ => add_comm _ _) (fun _ => rfl) (fun _ => rfl)
  braiding_naturality_left _ _ := rfl
  braiding_naturality_right _ _ _ _ := rfl
  hexagon_forward _ _ _ := rfl
  hexagon_reverse _ _ _ := rfl
  symmetry _ _ := rfl

end LawvereMet

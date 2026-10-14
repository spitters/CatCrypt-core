/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.Category.KleisliCat
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The Kleisli category of `Option` is symmetric monoidal

The Kleisli category of the `Option` monad is the category of types and partial functions.
It carries a symmetric monoidal structure whose tensor is the product of partial functions,
`(f ⊗ g) (a, b) = (f a, g b)`, defined when both components are, with unit `PUnit`.
The associator, unitors and braiding are the images of the corresponding type isomorphisms
under `some`.

The product `X × Y` is not a categorical product in `KleisliCat Option`. The interchange law holds because `Option` is a commutative monad
(`Option.bind_comm`); this is the construction of a monoidal Kleisli category from a
commutative monad (Kock 1970; Power and Robinson 1997).

## Main results

* `MonoidalCategory (KleisliCat.{u, u} Option)`: tensor `×`, unit `PUnit`.
* `BraidedCategory (KleisliCat.{u, u} Option)`: the braiding swaps components.
* `SymmetricCategory (KleisliCat.{u, u} Option)`: the braiding is self-inverse.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CategoryTheory.KleisliOption

open MonoidalCategory

/-- The Kleisli category of `Option` at universe `u`. -/
abbrev KlOption : Type (u + 1) := KleisliCat.{u, u} Option

variable {α β γ : KlOption.{u}}

/-- Composition in `KleisliCat Option` applies the first morphism then binds the second. -/
@[simp]
theorem comp_apply (f : α ⟶ β) (g : β ⟶ γ) (x : α) :
    (f ≫ g) x = (f x).bind g := rfl

/-- The identity morphism in `KleisliCat Option` is `some`. -/
@[simp]
theorem id_apply (x : α) : (𝟙 α) x = some x := rfl

/-! ## Monoidal structure -/

/-- Left whiskering: the product of the identity on `X` with a partial map `f`. -/
def whiskerLeftOpt (X : KlOption.{u}) {Y₁ Y₂ : KlOption.{u}}
    (f : Y₁ ⟶ Y₂) : (show KlOption.{u} from X × Y₁) ⟶ (show KlOption.{u} from X × Y₂) :=
  fun ⟨x, y⟩ => (f y).bind (fun y' => some (x, y'))

/-- Right whiskering: the product of a partial map `f` with the identity on `Y`. -/
def whiskerRightOpt {X₁ X₂ : KlOption.{u}} (f : X₁ ⟶ X₂) (Y : KlOption.{u}) :
    (show KlOption.{u} from X₁ × Y) ⟶ (show KlOption.{u} from X₂ × Y) :=
  fun ⟨x, y⟩ => (f x).bind (fun x' => some (x', y))

/-- Forward component of the associator. -/
def assocHomOpt (X Y Z : KlOption.{u}) :
    (show KlOption.{u} from (X × Y) × Z) ⟶ (show KlOption.{u} from X × (Y × Z)) :=
  fun ⟨⟨x, y⟩, z⟩ => some (x, (y, z))

/-- Inverse component of the associator. -/
def assocInvOpt (X Y Z : KlOption.{u}) :
    (show KlOption.{u} from X × (Y × Z)) ⟶ (show KlOption.{u} from (X × Y) × Z) :=
  fun ⟨x, y, z⟩ => some ((x, y), z)

/-- Forward component of the braiding: swaps the two components. -/
def braidHomOpt (X Y : KlOption.{u}) :
    (show KlOption.{u} from X × Y) ⟶ (show KlOption.{u} from Y × X) :=
  fun ⟨x, y⟩ => some (y, x)

/-- Unfolds a pointwise equality of Kleisli morphisms of `Option` to an equation of
    `Option.bind` terms and closes it with the monad laws of `Option`. -/
local macro "klo_simp" : tactic =>
  `(tactic| (unfold KlOption KleisliCat at *
             simp +unfoldPartialApp [whiskerLeftOpt, whiskerRightOpt, assocHomOpt, assocInvOpt,
               braidHomOpt,
               CategoryStruct.comp, CategoryStruct.id, Bind.kleisliRight, Bind.bind, Pure.pure,
               MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorHom,
               MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight,
               MonoidalCategoryStruct.associator, MonoidalCategoryStruct.leftUnitor,
               MonoidalCategoryStruct.rightUnitor, BraidedCategory.braiding]))

/-- The associator of the product of partial maps. -/
def assocIsoOpt (X Y Z : KlOption.{u}) :
    (show KlOption.{u} from (X × Y) × Z) ≅ (show KlOption.{u} from X × (Y × Z)) where
  hom := assocHomOpt X Y Z
  inv := assocInvOpt X Y Z
  hom_inv_id := by funext ⟨⟨x, y⟩, z⟩; klo_simp
  inv_hom_id := by funext ⟨x, y, z⟩; klo_simp

/-- The left unitor `PUnit × X ≅ X`. -/
def leftUnitorOpt (X : KlOption.{u}) : (show KlOption.{u} from PUnit.{u + 1} × X) ≅ X where
  hom := fun ⟨_, x⟩ => some x
  inv := fun x => some (PUnit.unit, x)
  hom_inv_id := by funext ⟨⟨⟩, x⟩; klo_simp
  inv_hom_id := by funext x; klo_simp

/-- The right unitor `X × PUnit ≅ X`. -/
def rightUnitorOpt (X : KlOption.{u}) : (show KlOption.{u} from X × PUnit.{u + 1}) ≅ X where
  hom := fun ⟨x, _⟩ => some x
  inv := fun x => some (x, PUnit.unit)
  hom_inv_id := by funext ⟨x, ⟨⟩⟩; klo_simp
  inv_hom_id := by funext x; klo_simp

/-- The braiding `X × Y ≅ Y × X`. -/
def braidIsoOpt (X Y : KlOption.{u}) :
    (show KlOption.{u} from X × Y) ≅ (show KlOption.{u} from Y × X) where
  hom := braidHomOpt X Y
  inv := braidHomOpt Y X
  hom_inv_id := by funext ⟨x, y⟩; klo_simp
  inv_hom_id := by funext ⟨y, x⟩; klo_simp

/-- `klo_simp`, also unfolding the structure isomorphisms of the monoidal structure. -/
local macro "klo_simp_iso" : tactic =>
  `(tactic| (unfold KlOption KleisliCat at *
             simp +unfoldPartialApp [whiskerLeftOpt, whiskerRightOpt, assocHomOpt, assocInvOpt,
               braidHomOpt, assocIsoOpt, leftUnitorOpt, rightUnitorOpt, braidIsoOpt,
               Option.bind_assoc,
               CategoryStruct.comp, CategoryStruct.id, Bind.kleisliRight, Bind.bind, Pure.pure,
               MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorHom,
               MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight,
               MonoidalCategoryStruct.associator, MonoidalCategoryStruct.leftUnitor,
               MonoidalCategoryStruct.rightUnitor, BraidedCategory.braiding]))

instance : MonoidalCategoryStruct KlOption.{u} where
  tensorObj X Y := (show KlOption.{u} from X × Y)
  whiskerLeft := whiskerLeftOpt
  whiskerRight := whiskerRightOpt
  tensorUnit := (show KlOption.{u} from PUnit.{u + 1})
  associator := assocIsoOpt
  leftUnitor := leftUnitorOpt
  rightUnitor := rightUnitorOpt

/-! ## Simp lemmas -/

@[simp]
theorem whiskerLeft_def (X : KlOption.{u}) {Y₁ Y₂ : KlOption.{u}} (f : Y₁ ⟶ Y₂) :
    (X ◁ f) = whiskerLeftOpt X f := rfl

@[simp]
theorem whiskerRight_def {X₁ X₂ : KlOption.{u}} (f : X₁ ⟶ X₂) (Y : KlOption.{u}) :
    (f ▷ Y) = whiskerRightOpt f Y := rfl

@[simp]
theorem tensorHom_eq {X₁ Y₁ X₂ Y₂ : KlOption.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) = whiskerRightOpt f X₂ ≫ whiskerLeftOpt Y₁ g := rfl

/-- The tensor of two partial maps is their product: defined at `(a, b)` exactly when both
    components are. -/
theorem tensorHom_apply {X₁ Y₁ X₂ Y₂ : KlOption.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (a : X₁) (b : X₂) :
    (f ⊗ₘ g : (show KlOption.{u} from X₁ × X₂) ⟶ (show KlOption.{u} from Y₁ × Y₂)) (a, b) =
      (f a).bind fun a' => (g b).bind fun b' => some (a', b') := by
  klo_simp_iso

@[simp]
theorem associator_hom_eq (X Y Z : KlOption.{u}) :
    (α_ X Y Z).hom = assocHomOpt X Y Z := rfl

@[simp]
theorem associator_inv_eq (X Y Z : KlOption.{u}) :
    (α_ X Y Z).inv = assocInvOpt X Y Z := rfl

@[simp]
theorem leftUnitor_hom_eq (X : KlOption.{u}) :
    (λ_ X).hom = (leftUnitorOpt X).hom := rfl

@[simp]
theorem leftUnitor_inv_eq (X : KlOption.{u}) :
    (λ_ X).inv = (leftUnitorOpt X).inv := rfl

@[simp]
theorem rightUnitor_hom_eq (X : KlOption.{u}) :
    (ρ_ X).hom = (rightUnitorOpt X).hom := rfl

@[simp]
theorem rightUnitor_inv_eq (X : KlOption.{u}) :
    (ρ_ X).inv = (rightUnitorOpt X).inv := rfl

/-! ## MonoidalCategory -/

instance : MonoidalCategory KlOption.{u} where
  tensorHom_def _ _ := rfl
  id_tensorHom_id X₁ X₂ := by
    funext ⟨x, y⟩; klo_simp
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    funext ⟨x, y⟩; klo_simp_iso
    congr 1; funext a
    exact Option.bind_comm (f₂ y) (g₁ a)
  whiskerLeft_id X Y := by
    funext ⟨x, y⟩; klo_simp
  id_whiskerRight X Y := by
    funext ⟨x, y⟩; klo_simp
  associator_naturality f₁ f₂ f₃ := by
    funext ⟨⟨x₁, x₂⟩, x₃⟩; klo_simp_iso
  leftUnitor_naturality f := by
    funext ⟨⟨⟩, x⟩; klo_simp_iso
  rightUnitor_naturality f := by
    funext ⟨x, ⟨⟩⟩; klo_simp_iso
  pentagon W X Y Z := by
    funext ⟨⟨⟨w, x⟩, y⟩, z⟩; klo_simp_iso
  triangle X Y := by
    funext ⟨⟨x, ⟨⟩⟩, y⟩; klo_simp_iso

/-! ## BraidedCategory and SymmetricCategory -/

instance : BraidedCategory KlOption.{u} where
  braiding := braidIsoOpt
  braiding_naturality_right X {Y Z} f := by
    funext ⟨x, y⟩; klo_simp_iso
  braiding_naturality_left {X Y} f Z := by
    funext ⟨x, z⟩; klo_simp_iso
  hexagon_forward X Y Z := by
    funext ⟨⟨x, y⟩, z⟩; klo_simp_iso
  hexagon_reverse X Y Z := by
    funext ⟨x, y, z⟩; klo_simp_iso

@[simp]
theorem braiding_hom_eq (X Y : KlOption.{u}) :
    (β_ X Y).hom = braidHomOpt X Y := rfl

instance : SymmetricCategory KlOption.{u} where
  symmetry X Y := (braidIsoOpt X Y).hom_inv_id

example : SymmetricCategory (KleisliCat.{0, 0} Option) := inferInstance

end CategoryTheory.KleisliOption

end

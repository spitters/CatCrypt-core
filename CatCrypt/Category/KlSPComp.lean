/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Code
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Kleisli Category of SPComp as a Symmetric Monoidal Category

This file shows that the Kleisli category of `SPComp` (stateful probabilistic computations)
forms a symmetric monoidal category with `Sum` as tensor and `Empty` as unit.

## Main results

* `Category KlSPComp` — Kleisli category of SPComp
* `MonoidalCategory KlSPComp` — Sum tensor, Empty unit
* `BraidedCategory KlSPComp` — braiding swaps summands via `pure`
* `SymmetricCategory KlSPComp` — braiding is self-inverse
-/

namespace CatCrypt.Core

open CategoryTheory MonoidalCategory

/-- Objects of the Kleisli category of SPComp. Opaque wrapper around `Type` to avoid
    conflicting with Mathlib's `CategoryTheory.types : Category Type`. -/
def KlSPComp := Type

namespace KlSPComp

noncomputable instance : CategoryStruct KlSPComp where
  Hom α β := α → SPComp β
  id _ x := SPComp.pure x
  comp f g x := SPComp.bind (f x) g

noncomputable instance : Category KlSPComp where
  id_comp f := by funext x; exact SPComp.pure_bind x f
  comp_id f := by funext x; exact SPComp.bind_pure (f x)
  assoc f g h := by funext x; exact SPComp.bind_assoc (f x) g h

variable {α β γ : KlSPComp}

@[simp]
theorem comp_apply (f : α ⟶ β) (g : β ⟶ γ) (x : α) :
    (f ≫ g) x = SPComp.bind (f x) g := rfl

@[simp]
theorem id_apply (x : α) : (𝟙 α) x = SPComp.pure x := rfl

/-! ## Monoidal definitions

All structural morphisms use explicit pattern matching on `Sum` constructors
so their equations are directly available to `simp`. -/

noncomputable def wkL (X : KlSPComp) {Y₁ Y₂ : KlSPComp}
    (f : Y₁ ⟶ Y₂) : (show KlSPComp from X ⊕ Y₁) ⟶ (show KlSPComp from X ⊕ Y₂) :=
  fun | .inl a => SPComp.pure (Sum.inl a)
      | .inr c => SPComp.map Sum.inr (f c)

noncomputable def wkR {X₁ X₂ : KlSPComp} (f : X₁ ⟶ X₂)
    (Y : KlSPComp) : (show KlSPComp from X₁ ⊕ Y) ⟶ (show KlSPComp from X₂ ⊕ Y) :=
  fun | .inl a => SPComp.map Sum.inl (f a)
      | .inr c => SPComp.pure (Sum.inr c)

noncomputable def assocHom (X Y Z : KlSPComp) :
    (show KlSPComp from (X ⊕ Y) ⊕ Z) ⟶ (show KlSPComp from X ⊕ (Y ⊕ Z)) :=
  fun | .inl (.inl a) => SPComp.pure (Sum.inl a)
      | .inl (.inr b) => SPComp.pure (Sum.inr (Sum.inl b))
      | .inr c => SPComp.pure (Sum.inr (Sum.inr c))

noncomputable def assocInv (X Y Z : KlSPComp) :
    (show KlSPComp from X ⊕ (Y ⊕ Z)) ⟶ (show KlSPComp from (X ⊕ Y) ⊕ Z) :=
  fun | .inl a => SPComp.pure (Sum.inl (Sum.inl a))
      | .inr (.inl b) => SPComp.pure (Sum.inl (Sum.inr b))
      | .inr (.inr c) => SPComp.pure (Sum.inr c)

noncomputable def assocIso (X Y Z : KlSPComp) :
    (show KlSPComp from (X ⊕ Y) ⊕ Z) ≅ (show KlSPComp from X ⊕ (Y ⊕ Z)) where
  hom := assocHom X Y Z
  inv := assocInv X Y Z
  hom_inv_id := by funext x; rcases x with (a | b) | c <;> simp [assocHom, assocInv]
  inv_hom_id := by funext x; rcases x with a | (b | c) <;> simp [assocHom, assocInv]

noncomputable def lUnit (X : KlSPComp) :
    (show KlSPComp from Empty ⊕ X) ≅ X where
  hom := fun | .inr a => SPComp.pure a
  inv := fun a => SPComp.pure (Sum.inr a)
  hom_inv_id := by
    funext x; rcases x with _ | a
    · exact (Empty.elim ‹_›)
    · exact SPComp.pure_bind a _
  inv_hom_id := by funext a; exact SPComp.pure_bind (Sum.inr a) _

noncomputable def rUnit (X : KlSPComp) :
    (show KlSPComp from X ⊕ Empty) ≅ X where
  hom := fun | .inl a => SPComp.pure a
  inv := fun a => SPComp.pure (Sum.inl a)
  hom_inv_id := by
    funext x; rcases x with a | _
    · exact SPComp.pure_bind a _
    · exact (Empty.elim ‹_›)
  inv_hom_id := by funext a; exact SPComp.pure_bind (Sum.inl a) _

noncomputable def braidHom (X Y : KlSPComp) :
    (show KlSPComp from X ⊕ Y) ⟶ (show KlSPComp from Y ⊕ X) :=
  fun | .inl a => SPComp.pure (Sum.inr a)
      | .inr b => SPComp.pure (Sum.inl b)

noncomputable def braidIso (X Y : KlSPComp) :
    (show KlSPComp from X ⊕ Y) ≅ (show KlSPComp from Y ⊕ X) where
  hom := braidHom X Y
  inv := braidHom Y X
  hom_inv_id := by funext x; rcases x with a | b <;> simp [braidHom]
  inv_hom_id := by funext x; rcases x with b | a <;> simp [braidHom]

noncomputable instance : MonoidalCategoryStruct KlSPComp where
  tensorObj X Y := (show KlSPComp from X ⊕ Y)
  whiskerLeft := wkL
  whiskerRight := wkR
  tensorUnit := (show KlSPComp from Empty)
  associator := assocIso
  leftUnitor := lUnit
  rightUnitor := rUnit

/-! ## Simp lemmas for class projections

These bridge from Mathlib notation (`◁`, `▷`, `⊗ₘ`, `α_`, `λ_`, `ρ_`) to our
concrete definitions (`wkL`, `wkR`, `assocIso`, `lUnit`, `rUnit`). -/

@[simp] theorem whiskerLeft_def (X : KlSPComp) {Y₁ Y₂ : KlSPComp} (f : Y₁ ⟶ Y₂) :
    (X ◁ f) = wkL X f := rfl

@[simp] theorem whiskerRight_def {X₁ X₂ : KlSPComp} (f : X₁ ⟶ X₂) (Y : KlSPComp) :
    (f ▷ Y) = wkR f Y := rfl

@[simp] theorem tensorHom_eq {X₁ Y₁ X₂ Y₂ : KlSPComp}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) = wkR f X₂ ≫ wkL Y₁ g := rfl

@[simp] theorem associator_hom_eq (X Y Z : KlSPComp) :
    (α_ X Y Z).hom = assocHom X Y Z := rfl

@[simp] theorem associator_inv_eq (X Y Z : KlSPComp) :
    (α_ X Y Z).inv = assocInv X Y Z := rfl

@[simp] theorem leftUnitor_hom_eq (X : KlSPComp) :
    (λ_ X).hom = (lUnit X).hom := rfl

@[simp] theorem rightUnitor_hom_eq (X : KlSPComp) :
    (ρ_ X).hom = (rUnit X).hom := rfl

/-! ## MonoidalCategory -/

noncomputable instance : MonoidalCategory KlSPComp where
  tensorHom_def _ _ := rfl
  id_tensorHom_id X₁ X₂ := funext fun
    | .inl a => by simp [wkR, wkL, SPComp.map]
    | .inr c => by simp [wkR, wkL, SPComp.map]
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := funext fun
    | .inl a => by simp [wkR, wkL, SPComp.map, SPComp.bind_assoc]
    | .inr c => by simp [wkR, wkL, SPComp.map, SPComp.bind_assoc]
  whiskerLeft_id X Y := funext fun
    | .inl _ => rfl
    | .inr c => by simp [wkL, SPComp.map]
  id_whiskerRight X Y := funext fun
    | .inl a => by simp [wkR, SPComp.map]
    | .inr _ => rfl
  associator_naturality f₁ f₂ f₃ := funext fun
    | .inl (.inl a) => by
        simp [assocHom, wkL, wkR, SPComp.map, SPComp.bind_assoc]
    | .inl (.inr b) => by
        simp [assocHom, wkL, wkR, SPComp.map, SPComp.bind_assoc]
    | .inr c => by
        simp [assocHom, wkL, wkR, SPComp.map, SPComp.bind_assoc]
  leftUnitor_naturality f := funext fun
    | .inl e => (Empty.elim e)
    | .inr a => by simp [lUnit, wkL, SPComp.map, SPComp.bind_assoc]
  rightUnitor_naturality f := funext fun
    | .inl a => by simp [rUnit, wkR, SPComp.map, SPComp.bind_assoc]
    | .inr e => (Empty.elim e)
  pentagon W X Y Z := funext fun
    | .inl (.inl (.inl w)) => by
        simp [assocHom, wkL, wkR, SPComp.map]
    | .inl (.inl (.inr x)) => by
        simp [assocHom, wkL, wkR, SPComp.map]
    | .inl (.inr y) => by
        simp [assocHom, wkL, wkR, SPComp.map]
    | .inr z => by
        simp [assocHom, wkL, wkR, SPComp.map]
  triangle X Y := funext fun
    | .inl (.inl a) => by
        simp [assocHom, rUnit, lUnit, wkL, wkR, SPComp.map]
    | .inl (.inr e) => (Empty.elim e)
    | .inr b => by
        simp [assocHom, rUnit, lUnit, wkL, wkR, SPComp.map]

/-! ## BraidedCategory and SymmetricCategory -/

noncomputable instance : BraidedCategory KlSPComp where
  braiding := braidIso
  braiding_naturality_right X {Y Z} f := by
    change wkL X f ≫ braidHom X Z = braidHom X Y ≫ wkR f X
    funext x; rcases x with a | c
    · simp [braidHom, wkL, wkR]
    · simp [braidHom, wkL, wkR, SPComp.map, SPComp.bind_assoc]
  braiding_naturality_left {X Y} f Z := by
    change wkR f Z ≫ braidHom Y Z = braidHom X Z ≫ wkL Z f
    funext x; rcases x with a | c
    · simp [braidHom, wkL, wkR, SPComp.map, SPComp.bind_assoc]
    · simp [braidHom, wkL, wkR]
  hexagon_forward X Y Z := by
    change assocHom X Y Z ≫ braidHom X _ ≫ assocHom Y Z X =
      braidHom X Y ▷ Z ≫ assocHom Y X Z ≫ Y ◁ braidHom X Z
    simp only [whiskerLeft_def, whiskerRight_def]
    funext x; rcases x with (a | b) | c
    · simp [braidHom, assocHom, wkL, wkR, SPComp.map]
    · simp [braidHom, assocHom, wkL, wkR, SPComp.map]
    · simp [braidHom, assocHom, wkL, wkR, SPComp.map]
  hexagon_reverse X Y Z := by
    change assocInv X Y Z ≫ braidHom _ Z ≫ assocInv Z X Y =
      X ◁ braidHom Y Z ≫ assocInv X Z Y ≫ braidHom X Z ▷ Y
    simp only [whiskerLeft_def, whiskerRight_def]
    funext x; rcases x with a | (b | c)
    · simp [braidHom, assocInv, wkL, wkR, SPComp.map]
    · simp [braidHom, assocInv, wkL, wkR, SPComp.map]
    · simp [braidHom, assocInv, wkL, wkR, SPComp.map]

noncomputable instance : SymmetricCategory KlSPComp where
  symmetry X Y := by
    show (braidIso X Y).hom ≫ (braidIso Y X).hom = 𝟙 _
    exact (braidIso X Y).hom_inv_id

end KlSPComp

end CatCrypt.Core

/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Category.KlSPComp
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cocartesian Monoidal Categories

This file defines cocartesian monoidal categories (dual of cartesian monoidal) and proves
that `KlSPComp` is cocartesian with `Sum` as coproduct and `Empty` as initial object.

## Main definitions

* `SemiCocartesianMonoidalCategory` — monoidal category with initial tensor unit
* `CocartesianMonoidalCategory` — tensor is the categorical coproduct
* `KlSPComp` instance of `CocartesianMonoidalCategory`
-/

namespace CategoryTheory

open MonoidalCategory Limits

universe u v

variable (C : Type u) [Category.{v} C]

/-- A monoidal category is semicocartesian if the unit for the tensor product is
    an initial object. Dual of `SemiCartesianMonoidalCategory`. -/
class SemiCocartesianMonoidalCategory extends MonoidalCategory C where
  /-- The tensor unit is an initial object. -/
  isInitialTensorUnit : IsInitial (𝟙_ C)
  /-- The first coprojection into the coproduct. -/
  inl (X Y : C) : X ⟶ X ⊗ Y
  /-- The second coprojection into the coproduct. -/
  inr (X Y : C) : Y ⟶ X ⊗ Y
  inl_def (X Y : C) : inl X Y = (ρ_ X).inv ≫ X ◁ isInitialTensorUnit.to Y := by cat_disch
  inr_def (X Y : C) : inr X Y = (λ_ Y).inv ≫ isInitialTensorUnit.to X ▷ Y := by cat_disch

namespace SemiCocartesianMonoidalCategory

variable {C} [SemiCocartesianMonoidalCategory C]

/-- The unique morphism from the initial tensor unit to any object. -/
def fromUnit (X : C) : 𝟙_ C ⟶ X := isInitialTensorUnit.to X

@[reassoc (attr := simp)]
theorem fromUnit_comp {X Y : C} (f : X ⟶ Y) : fromUnit X ≫ f = fromUnit Y :=
  IsInitial.hom_ext isInitialTensorUnit _ _

@[simp] lemma fromUnit_unit : fromUnit (𝟙_ C) = 𝟙 (𝟙_ C) :=
  IsInitial.hom_ext isInitialTensorUnit _ _

/-- Bridge lemma: `isInitialTensorUnit.to X` is the same as `fromUnit X`. -/
@[simp] lemma isInitialTensorUnit_to (X : C) :
    isInitialTensorUnit.to X = fromUnit X := rfl

end SemiCocartesianMonoidalCategory

/-- A monoidal category is cocartesian if the tensor product is the categorical coproduct
    and the unit is initial. Dual of `CartesianMonoidalCategory`. -/
class CocartesianMonoidalCategory extends SemiCocartesianMonoidalCategory C where
  /-- The monoidal product is the categorical coproduct. -/
  tensorCoproductIsBinaryCoproduct (X Y : C) :
    IsColimit (BinaryCofan.mk (inl X Y) (inr X Y))

namespace CocartesianMonoidalCategory

variable {C} [CocartesianMonoidalCategory C]

/-- The copairing (universal map from coproduct). -/
def desc {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : X ⊗ Y ⟶ Z :=
  (tensorCoproductIsBinaryCoproduct X Y).desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]
theorem inl_desc {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    SemiCocartesianMonoidalCategory.inl X Y ≫ desc f g = f :=
  (tensorCoproductIsBinaryCoproduct X Y).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem inr_desc {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    SemiCocartesianMonoidalCategory.inr X Y ≫ desc f g = g :=
  (tensorCoproductIsBinaryCoproduct X Y).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

@[ext]
theorem hom_ext {X Y Z : C} {f g : X ⊗ Y ⟶ Z}
    (hl : SemiCocartesianMonoidalCategory.inl X Y ≫ f =
          SemiCocartesianMonoidalCategory.inl X Y ≫ g)
    (hr : SemiCocartesianMonoidalCategory.inr X Y ≫ f =
          SemiCocartesianMonoidalCategory.inr X Y ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (tensorCoproductIsBinaryCoproduct X Y) hl hr

theorem desc_unique {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : X ⊗ Y ⟶ Z}
    (hl : SemiCocartesianMonoidalCategory.inl X Y ≫ h = f)
    (hr : SemiCocartesianMonoidalCategory.inr X Y ≫ h = g) : h = desc f g :=
  hom_ext (hl.trans (inl_desc f g).symm) (hr.trans (inr_desc f g).symm)

/-! ### Simp library for CocartesianMonoidalCategory

Dual of Mathlib's `CartesianMonoidalCategory` simp library. -/

/-! #### Core desc identities -/

open SemiCocartesianMonoidalCategory in
@[simp]
theorem desc_inl_inr {X Y : C} : desc (inl X Y) (inr X Y) = 𝟙 (X ⊗ Y) := by
  ext <;> simp

open SemiCocartesianMonoidalCategory in
@[simp]
theorem desc_comp_inl_inr {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    desc (inl X Y ≫ f) (inr X Y ≫ f) = f := by
  ext <;> simp

open SemiCocartesianMonoidalCategory in
@[reassoc, simp]
theorem desc_comp {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ W) :
    desc f g ≫ h = desc (f ≫ h) (g ≫ h) := by
  ext <;> simp

/-! #### Coprojections and whiskering -/

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem inl_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    inl X Y ≫ X ◁ f = inl X Z := by
  simp only [inl_def, isInitialTensorUnit_to, Category.assoc,
    ← whiskerLeft_comp, fromUnit_comp]

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem inr_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    inr X Y ≫ X ◁ f = f ≫ inr X Z := by
  simp only [inr_def, isInitialTensorUnit_to, Category.assoc]
  rw [← whisker_exchange, leftUnitor_inv_naturality_assoc]

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem inl_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    inl X Z ≫ f ▷ Z = f ≫ inl Y Z := by
  simp only [inl_def, isInitialTensorUnit_to, Category.assoc]
  rw [whisker_exchange, rightUnitor_inv_naturality_assoc]

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem inr_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    inr X Z ≫ f ▷ Z = inr Y Z := by
  simp only [inr_def, isInitialTensorUnit_to, Category.assoc,
    ← comp_whiskerRight, fromUnit_comp]

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem inl_tensorHom {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    inl X₁ Y₁ ≫ (f ⊗ₘ g) = f ≫ inl X₂ Y₂ := by simp [tensorHom_def]

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem inr_tensorHom {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    inr X₁ Y₁ ≫ (f ⊗ₘ g) = g ≫ inr X₂ Y₂ := by simp [tensorHom_def]

/-! #### desc + tensor -/

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem map_desc {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : W ⟶ Z) (k : Y ⟶ Z) :
    (f ⊗ₘ g) ≫ desc h k = desc (f ≫ h) (g ≫ k) := by ext <;> simp

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem whiskerLeft_desc {X Y Z W : C} (f : X ⟶ W) (g : Y ⟶ Z) (h : Z ⟶ W) :
    X ◁ g ≫ desc f h = desc f (g ≫ h) := by ext <;> simp

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem whiskerRight_desc {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ W) (h : Z ⟶ W) :
    f ▷ Z ≫ desc g h = desc (f ≫ g) h := by ext <;> simp

open SemiCocartesianMonoidalCategory in
@[simp]
theorem desc_inl_comp_inr_comp {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    desc (f ≫ inl X Z) (g ≫ inr X Z) = f ⊗ₘ g := by ext <;> simp

/-! #### Unitor projections -/

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem inr_leftUnitor_hom (X : C) :
    inr (𝟙_ C) X ≫ (λ_ X).hom = 𝟙 X := by
  simp only [inr_def, isInitialTensorUnit_to, Category.assoc,
    fromUnit_unit, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

open SemiCocartesianMonoidalCategory in
@[reassoc (attr := simp)]
theorem inl_rightUnitor_hom (X : C) :
    inl X (𝟙_ C) ≫ (ρ_ X).hom = 𝟙 X := by
  simp only [inl_def, isInitialTensorUnit_to, Category.assoc,
    fromUnit_unit, whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

end CocartesianMonoidalCategory

end CategoryTheory

/-! ## Concrete instance: KlSPComp is cocartesian -/

namespace CatCrypt.Core

open CategoryTheory MonoidalCategory Limits
open SemiCocartesianMonoidalCategory CocartesianMonoidalCategory

namespace KlSPComp

/-! ### IsInitial for Empty -/

/-- `Empty` is initial in KlSPComp: there is a unique morphism from `Empty` to any type. -/
noncomputable def emptyIsInitial : IsInitial (show KlSPComp from Empty) :=
  IsInitial.ofUnique _ (h := fun _ => {
    default := fun e => Empty.elim e
    uniq := fun _ => funext fun e => Empty.elim e
  })

/-! ### Coprojections -/

/-- Left coprojection: embed into the left summand via pure. -/
noncomputable def klInl (α β : KlSPComp) : α ⟶ (show KlSPComp from α ⊕ β) :=
  fun a => SPComp.pure (Sum.inl a)

/-- Right coprojection: embed into the right summand via pure. -/
noncomputable def klInr (α β : KlSPComp) : β ⟶ (show KlSPComp from α ⊕ β) :=
  fun b => SPComp.pure (Sum.inr b)

/-! ### Copairing -/

/-- Copairing: given morphisms from each summand, produce a morphism from the coproduct. -/
noncomputable def klDesc {α β γ : KlSPComp} (f : α ⟶ γ) (g : β ⟶ γ) :
    (show KlSPComp from α ⊕ β) ⟶ γ :=
  fun | .inl a => f a | .inr b => g b

theorem klInl_klDesc {α β γ : KlSPComp} (f : α ⟶ γ) (g : β ⟶ γ) :
    klInl α β ≫ klDesc f g = f := by
  funext a; simp [klInl, klDesc]

theorem klInr_klDesc {α β γ : KlSPComp} (f : α ⟶ γ) (g : β ⟶ γ) :
    klInr α β ≫ klDesc f g = g := by
  funext b; simp [klInr, klDesc]

theorem klDesc_unique {α β γ : KlSPComp} {f : α ⟶ γ} {g : β ⟶ γ}
    {h : (show KlSPComp from α ⊕ β) ⟶ γ}
    (hl : klInl α β ≫ h = f) (hr : klInr α β ≫ h = g) :
    h = klDesc f g := by
  funext x; rcases x with a | b
  · have := congrFun hl a; simp [klInl] at this; simp [klDesc, this]
  · have := congrFun hr b; simp [klInr] at this; simp [klDesc, this]

/-! ### Coproduct is colimit -/

noncomputable def binaryCoproductIsColimit (α β : KlSPComp) :
    IsColimit (BinaryCofan.mk (klInl α β) (klInr α β)) :=
  BinaryCofan.isColimitMk
    (fun s => klDesc s.inl s.inr)
    (fun s => klInl_klDesc s.inl s.inr)
    (fun s => klInr_klDesc s.inl s.inr)
    (fun _ _ h₁ h₂ => klDesc_unique h₁ h₂)

/-! ### inl_def / inr_def compatibility -/

private theorem klInl_eq_rUnit_inv_wkL (α β : KlSPComp) :
    klInl α β = (ρ_ α).inv ≫ α ◁ emptyIsInitial.to β := by
  funext a
  simp only [comp_apply, whiskerLeft_def]
  show SPComp.pure (Sum.inl a) =
    SPComp.bind ((rUnit α).inv a) (wkL α (emptyIsInitial.to β))
  simp [rUnit, wkL]

private theorem klInr_eq_lUnit_inv_wkR (α β : KlSPComp) :
    klInr α β = (λ_ β).inv ≫ emptyIsInitial.to α ▷ β := by
  funext b
  simp only [comp_apply, whiskerRight_def]
  show SPComp.pure (Sum.inr b) =
    SPComp.bind ((lUnit β).inv b) (wkR (emptyIsInitial.to α) β)
  simp [lUnit, wkR]

/-! ### CocartesianMonoidalCategory instance -/

noncomputable instance : SemiCocartesianMonoidalCategory KlSPComp where
  isInitialTensorUnit := emptyIsInitial
  inl := klInl
  inr := klInr
  inl_def α β := klInl_eq_rUnit_inv_wkL α β
  inr_def α β := klInr_eq_lUnit_inv_wkR α β

noncomputable instance : CocartesianMonoidalCategory KlSPComp where
  tensorCoproductIsBinaryCoproduct := binaryCoproductIsColimit

end KlSPComp

end CatCrypt.Core

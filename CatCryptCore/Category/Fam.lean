/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Logic.Equiv.Sum

/-!
# Category of Families as a Symmetric Monoidal Category

For any category `C`, the category `Fam C` of families forms a symmetric monoidal
category with `Sum` as tensor and `Empty` as unit.

Objects are pairs `(ι : Type, objs : ι → C)`. Morphisms carry an equivalence
`σ : ι₁ ≃ ι₂` together with componentwise `C`-morphisms.

The tensor uses `Sum` on index types and `Sum.elim` on objects, giving
definitional reductions for all structural morphisms (associator, braiding, unitors).

## Main results

* `Category (FamObj C)` — componentwise category with Equiv permutations
* `MonoidalCategory (FamObj C)` — Sum tensor, Empty unit
* `BraidedCategory (FamObj C)` — braiding via `Sum.swap`
* `SymmetricCategory (FamObj C)` — braiding is self-inverse
-/

namespace CatCrypt.Category

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Objects of the family category: a type `ι` indexing objects of `C`. -/
structure FamObj (C : Type u) [Category.{v} C] where
  ι : Type
  objs : ι → C

namespace FamObj

/-- Morphisms in the family category: an equivalence on index types
    with componentwise C-morphisms. -/
structure Hom (X Y : FamObj C) where
  σ : X.ι ≃ Y.ι
  map : ∀ i : X.ι, X.objs i ⟶ Y.objs (σ i)

/-- Two morphisms are equal iff σ agrees and map agrees (up to HEq). -/
theorem fam_ext {X Y : FamObj C} {f g : Hom X Y}
    (hσ : f.σ = g.σ)
    (hmap : ∀ i, HEq (f.map i) (g.map i)) : f = g := by
  rcases f with ⟨fσ, fm⟩; rcases g with ⟨gσ, gm⟩
  subst hσ
  congr 1
  exact funext (fun i => eq_of_heq (hmap i))

noncomputable instance : CategoryStruct (FamObj C) where
  Hom := Hom
  id _ := ⟨Equiv.refl _, fun _ => 𝟙 _⟩
  comp f g := ⟨f.σ.trans g.σ, fun i => f.map i ≫ g.map (f.σ i)⟩

@[simp, grind =] theorem comp_σ {X Y Z : FamObj C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).σ = f.σ.trans g.σ := rfl

@[simp, grind =] theorem comp_map {X Y Z : FamObj C} (f : X ⟶ Y) (g : Y ⟶ Z) (i : X.ι) :
    (f ≫ g).map i = f.map i ≫ g.map (f.σ i) := rfl

@[simp, grind =] theorem id_σ (X : FamObj C) : (𝟙 X : X ⟶ X).σ = Equiv.refl _ := rfl

@[simp, grind =] theorem id_map (X : FamObj C) (i : X.ι) : (𝟙 X : X ⟶ X).map i = 𝟙 _ := rfl

noncomputable instance : Category (FamObj C) where
  id_comp f := by
    apply fam_ext
    · simp
    · intro i; exact heq_of_eq (Category.id_comp _)
  comp_id f := by
    apply fam_ext
    · simp
    · intro i; exact heq_of_eq (Category.comp_id _)
  assoc f g h := by
    apply fam_ext
    · simp [Equiv.trans_assoc]
    · intro i; exact heq_of_eq (Category.assoc _ _ _)

/-! ## Monoidal definitions -/

/-- Tensor product of families: Sum on index types, Sum.elim on objects. -/
def tensorObj (X Y : FamObj C) : FamObj C :=
  ⟨X.ι ⊕ Y.ι, Sum.elim X.objs Y.objs⟩

/-- Unit for tensor: empty family. -/
def unitObj : FamObj C := ⟨Empty, Empty.elim⟩

/-- Left whiskering: identity on the left component, f on the right. -/
noncomputable def wkL (X : FamObj C) {Y₁ Y₂ : FamObj C} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ where
  σ := (Equiv.refl X.ι).sumCongr f.σ
  map := fun | .inl _ => 𝟙 _ | .inr y => f.map y

/-- Right whiskering: f on the left component, identity on the right. -/
noncomputable def wkR {X₁ X₂ : FamObj C} (f : X₁ ⟶ X₂) (Y : FamObj C) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y where
  σ := f.σ.sumCongr (Equiv.refl Y.ι)
  map := fun | .inl x => f.map x | .inr _ => 𝟙 _

/-- Associator forward. -/
noncomputable def assocHom (X Y Z : FamObj C) :
    tensorObj (tensorObj X Y) Z ⟶ tensorObj X (tensorObj Y Z) where
  σ := Equiv.sumAssoc X.ι Y.ι Z.ι
  map := fun | .inl (.inl _) => 𝟙 _ | .inl (.inr _) => 𝟙 _ | .inr _ => 𝟙 _

/-- Associator backward. -/
noncomputable def assocInv (X Y Z : FamObj C) :
    tensorObj X (tensorObj Y Z) ⟶ tensorObj (tensorObj X Y) Z where
  σ := (Equiv.sumAssoc X.ι Y.ι Z.ι).symm
  map := fun | .inl _ => 𝟙 _ | .inr (.inl _) => 𝟙 _ | .inr (.inr _) => 𝟙 _

/-- Braiding. -/
noncomputable def braidHom (X Y : FamObj C) :
    tensorObj X Y ⟶ tensorObj Y X where
  σ := Equiv.sumComm X.ι Y.ι
  map := fun | .inl _ => 𝟙 _ | .inr _ => 𝟙 _

/-! ## Left and right unitors -/

noncomputable def lUnit (X : FamObj C) : tensorObj unitObj X ≅ X where
  hom := ⟨Equiv.emptySum Empty X.ι, fun | .inl e => nomatch e | .inr _ => 𝟙 _⟩
  inv := ⟨(Equiv.emptySum Empty X.ι).symm, fun _ => 𝟙 _⟩
  hom_inv_id := by
    apply fam_ext
    · ext i; rcases i with e | x
      · exact (Empty.elim e)
      · rfl
    · intro i; rcases i with e | x
      · exact (Empty.elim e)
      · exact heq_of_eq (Category.id_comp _)
  inv_hom_id := by
    apply fam_ext
    · ext i; rfl
    · intro i; exact heq_of_eq (Category.id_comp _)

noncomputable def rUnit (X : FamObj C) : tensorObj X unitObj ≅ X where
  hom := ⟨Equiv.sumEmpty X.ι Empty, fun | .inl _ => 𝟙 _ | .inr e => nomatch e⟩
  inv := ⟨(Equiv.sumEmpty X.ι Empty).symm, fun _ => 𝟙 _⟩
  hom_inv_id := by
    apply fam_ext
    · ext i; rcases i with x | e
      · rfl
      · exact (Empty.elim e)
    · intro i; rcases i with x | e
      · exact heq_of_eq (Category.id_comp _)
      · exact (Empty.elim e)
  inv_hom_id := by
    apply fam_ext
    · ext i; rfl
    · intro i; exact heq_of_eq (Category.id_comp _)

/-! ## Equiv application lemmas

Mathlib's `Equiv.sumCongr_apply` doesn't fire in `simp` through the
`FunLike.coe` discrimination tree. These specific lemmas bypass the issue
by stating applications directly. All proved by `rfl` (definitional). -/

@[simp] theorem sumCongr_refl_inl {α α' β : Type} (e : α ≃ α') (a : α) :
    (e.sumCongr (Equiv.refl β)) (Sum.inl a) = Sum.inl (e a) := rfl

@[simp] theorem sumCongr_refl_inr {α α' β : Type} (e : α ≃ α') (b : β) :
    (e.sumCongr (Equiv.refl β)) (Sum.inr b) = Sum.inr b := rfl

@[simp] theorem refl_sumCongr_inl {α β β' : Type} (e : β ≃ β') (a : α) :
    ((Equiv.refl α).sumCongr e) (Sum.inl a) = Sum.inl a := rfl

@[simp] theorem refl_sumCongr_inr {α β β' : Type} (e : β ≃ β') (b : β) :
    ((Equiv.refl α).sumCongr e) (Sum.inr b) = Sum.inr (e b) := rfl

@[simp] theorem sumAssoc_inl_inl {α β γ : Type} (a : α) :
    (Equiv.sumAssoc α β γ) (Sum.inl (Sum.inl a)) = Sum.inl a := rfl

@[simp] theorem sumAssoc_inl_inr {α β γ : Type} (b : β) :
    (Equiv.sumAssoc α β γ) (Sum.inl (Sum.inr b)) = Sum.inr (Sum.inl b) := rfl

@[simp] theorem sumAssoc_inr {α β γ : Type} (c : γ) :
    (Equiv.sumAssoc α β γ) (Sum.inr c) = Sum.inr (Sum.inr c) := rfl

@[simp] theorem sumAssoc_symm_inl {α β γ : Type} (a : α) :
    (Equiv.sumAssoc α β γ).symm (Sum.inl a) = Sum.inl (Sum.inl a) := rfl

@[simp] theorem sumAssoc_symm_inr_inl {α β γ : Type} (b : β) :
    (Equiv.sumAssoc α β γ).symm (Sum.inr (Sum.inl b)) = Sum.inl (Sum.inr b) := rfl

@[simp] theorem sumAssoc_symm_inr_inr {α β γ : Type} (c : γ) :
    (Equiv.sumAssoc α β γ).symm (Sum.inr (Sum.inr c)) = Sum.inr c := rfl

@[simp] theorem sumComm_inl {α β : Type} (a : α) :
    (Equiv.sumComm α β) (Sum.inl a) = Sum.inr a := rfl

@[simp] theorem sumComm_inr {α β : Type} (b : β) :
    (Equiv.sumComm α β) (Sum.inr b) = Sum.inl b := rfl

@[simp] theorem emptySum_inr {α : Type} (a : α) :
    (Equiv.emptySum Empty α) (Sum.inr a) = a := rfl

@[simp] theorem emptySum_symm_apply {α : Type} (a : α) :
    (Equiv.emptySum Empty α).symm a = Sum.inr a := rfl

@[simp] theorem sumEmpty_inl {α : Type} (a : α) :
    (Equiv.sumEmpty α Empty) (Sum.inl a) = a := rfl

@[simp] theorem sumEmpty_symm_apply {α : Type} (a : α) :
    (Equiv.sumEmpty α Empty).symm a = Sum.inl a := rfl

@[simp] theorem trans_apply' {α β γ : Type} (e₁ : α ≃ β) (e₂ : β ≃ γ) (a : α) :
    (e₁.trans e₂) a = e₂ (e₁ a) := rfl

/-! ## Equiv-level σ lemmas

These rewrite `Hom.σ` (a struct projection returning an `Equiv`) to the
concrete `Equiv` constructor. Since `Hom.σ` is a struct projection (not
going through `FunLike.coe`), these fire reliably in `simp`. -/

@[simp] theorem wkL_σ_eq (X : FamObj C) {Y₁ Y₂ : FamObj C} (f : Y₁ ⟶ Y₂) :
    (wkL X f).σ = (Equiv.refl X.ι).sumCongr f.σ := rfl

@[simp] theorem wkR_σ_eq {X₁ X₂ : FamObj C} (f : X₁ ⟶ X₂) (Y : FamObj C) :
    (wkR f Y).σ = f.σ.sumCongr (Equiv.refl Y.ι) := rfl

@[simp] theorem assocHom_σ_eq (X Y Z : FamObj C) :
    (assocHom X Y Z).σ = Equiv.sumAssoc X.ι Y.ι Z.ι := rfl

@[simp] theorem assocInv_σ_eq (X Y Z : FamObj C) :
    (assocInv X Y Z).σ = (Equiv.sumAssoc X.ι Y.ι Z.ι).symm := rfl

@[simp] theorem braidHom_σ_eq (X Y : FamObj C) :
    (braidHom X Y).σ = Equiv.sumComm X.ι Y.ι := rfl

@[simp] theorem lUnit_hom_σ_eq (X : FamObj C) :
    (lUnit X).hom.σ = Equiv.emptySum Empty X.ι := rfl

@[simp] theorem lUnit_inv_σ_eq (X : FamObj C) :
    (lUnit X).inv.σ = (Equiv.emptySum Empty X.ι).symm := rfl

@[simp] theorem rUnit_hom_σ_eq (X : FamObj C) :
    (rUnit X).hom.σ = Equiv.sumEmpty X.ι Empty := rfl

@[simp] theorem rUnit_inv_σ_eq (X : FamObj C) :
    (rUnit X).inv.σ = (Equiv.sumEmpty X.ι Empty).symm := rfl

/-! ## Per-constructor simp lemmas for map

These fire fine in `simp` because `Hom.map` is a direct struct projection
(no `FunLike.coe` coercion chain). -/

@[simp, grind =] theorem wkL_map_inl (X : FamObj C) {Y₁ Y₂ : FamObj C} (f : Y₁ ⟶ Y₂) (a : X.ι) :
    (wkL X f).map (.inl a) = 𝟙 _ := rfl

@[simp, grind =] theorem wkL_map_inr (X : FamObj C) {Y₁ Y₂ : FamObj C} (f : Y₁ ⟶ Y₂) (b : Y₁.ι) :
    (wkL X f).map (.inr b) = f.map b := rfl

@[simp, grind =] theorem wkR_map_inl {X₁ X₂ : FamObj C} (f : X₁ ⟶ X₂) (Y : FamObj C) (a : X₁.ι) :
    (wkR f Y).map (.inl a) = f.map a := rfl

@[simp, grind =] theorem wkR_map_inr {X₁ X₂ : FamObj C} (f : X₁ ⟶ X₂) (Y : FamObj C) (b : Y.ι) :
    (wkR f Y).map (.inr b) = 𝟙 _ := rfl

@[simp, grind =] theorem assocHom_map_inl_inl (X Y Z : FamObj C) (a : X.ι) :
    (assocHom X Y Z).map (.inl (.inl a)) = 𝟙 _ := rfl

@[simp, grind =] theorem assocHom_map_inl_inr (X Y Z : FamObj C) (b : Y.ι) :
    (assocHom X Y Z).map (.inl (.inr b)) = 𝟙 _ := rfl

@[simp, grind =] theorem assocHom_map_inr (X Y Z : FamObj C) (c : Z.ι) :
    (assocHom X Y Z).map (.inr c) = 𝟙 _ := rfl

@[simp, grind =] theorem assocInv_map_inl (X Y Z : FamObj C) (a : X.ι) :
    (assocInv X Y Z).map (.inl a) = 𝟙 _ := rfl

@[simp, grind =] theorem assocInv_map_inr_inl (X Y Z : FamObj C) (b : Y.ι) :
    (assocInv X Y Z).map (.inr (.inl b)) = 𝟙 _ := rfl

@[simp, grind =] theorem assocInv_map_inr_inr (X Y Z : FamObj C) (c : Z.ι) :
    (assocInv X Y Z).map (.inr (.inr c)) = 𝟙 _ := rfl

@[simp, grind =] theorem braidHom_map_inl (X Y : FamObj C) (a : X.ι) :
    (braidHom X Y).map (.inl a) = 𝟙 _ := rfl

@[simp, grind =] theorem braidHom_map_inr (X Y : FamObj C) (b : Y.ι) :
    (braidHom X Y).map (.inr b) = 𝟙 _ := rfl

@[simp, grind =] theorem lUnit_hom_map_inr (X : FamObj C) (a : X.ι) :
    (lUnit X).hom.map (.inr a) = 𝟙 _ := rfl

@[simp, grind =] theorem lUnit_inv_map (X : FamObj C) (a : X.ι) :
    (lUnit X).inv.map a = 𝟙 _ := rfl

@[simp, grind =] theorem rUnit_hom_map_inl (X : FamObj C) (a : X.ι) :
    (rUnit X).hom.map (.inl a) = 𝟙 _ := rfl

@[simp, grind =] theorem rUnit_inv_map (X : FamObj C) (a : X.ι) :
    (rUnit X).inv.map a = 𝟙 _ := rfl

/-! ## Small morphism-level lemmas

These operate at the level of whole morphisms (not components), allowing
MonoidalCategory axioms to be proved by rewriting rather than fam_ext. -/

@[simp] theorem wkL_id (X Y : FamObj C) : wkL X (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  apply fam_ext
  · ext i; rcases i with a | b <;> rfl
  · intro i; rcases i with a | b <;> exact heq_of_eq rfl

@[simp] theorem wkR_id (X Y : FamObj C) : wkR (𝟙 X) Y = 𝟙 (tensorObj X Y) := by
  apply fam_ext
  · ext i; rcases i with a | b <;> rfl
  · intro i; rcases i with a | b <;> exact heq_of_eq rfl

@[reassoc (attr := simp)] theorem wkL_comp (X : FamObj C) {Y₁ Y₂ Y₃ : FamObj C}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    wkL X f ≫ wkL X g = wkL X (f ≫ g) := by
  apply fam_ext
  · ext i; rcases i with a | b <;> rfl
  · intro i; rcases i with a | b
    · exact heq_of_eq (Category.id_comp _)
    · exact heq_of_eq rfl

@[reassoc (attr := simp)] theorem wkR_comp {X₁ X₂ X₃ : FamObj C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (Y : FamObj C) :
    wkR f Y ≫ wkR g Y = wkR (f ≫ g) Y := by
  apply fam_ext
  · ext i; rcases i with a | b <;> rfl
  · intro i; rcases i with a | b
    · exact heq_of_eq rfl
    · exact heq_of_eq (Category.id_comp _)

@[reassoc (attr := simp)] theorem wkR_wkL_comm {X₁ X₂ : FamObj C} (f : X₁ ⟶ X₂)
    {Y₁ Y₂ : FamObj C} (g : Y₁ ⟶ Y₂) :
    wkR f Y₁ ≫ wkL X₂ g = wkL X₁ g ≫ wkR f Y₂ := by
  apply fam_ext
  · ext i; rcases i with a | b <;> rfl
  · intro i; rcases i with a | b
    · apply heq_of_eq; show f.map a ≫ 𝟙 _ = 𝟙 _ ≫ f.map a; simp
    · apply heq_of_eq; show 𝟙 _ ≫ g.map b = g.map b ≫ 𝟙 _; simp

/-! ## Naturality lemmas for structural morphisms

These express naturality of `assocHom`, `braidHom`, and unitors with respect
to `wkR`/`wkL`. Proofs use `erw` which matches through dependent function
arguments via `isDefEq`, unlike `simp`/`dsimp` which use discrimination trees. -/

theorem assocHom_wkR {X₁ X₂ : FamObj C} (f : X₁ ⟶ X₂) (Y Z : FamObj C) :
    wkR (wkR f Y) Z ≫ assocHom X₂ Y Z = assocHom X₁ Y Z ≫ wkR f (tensorObj Y Z) := by
  apply fam_ext
  · ext i; rcases i with (a | b) | c <;> rfl
  · intro i; rcases i with (a | b) | c <;> apply heq_of_eq
    · erw [FamObj.comp_map, FamObj.comp_map]
      erw [wkR_map_inl]; erw [wkR_map_inl]
      erw [assocHom_map_inl_inl]; erw [assocHom_map_inl_inl]; erw [wkR_map_inl]
      erw [Category.id_comp, Category.comp_id]
    · erw [FamObj.comp_map]
    · erw [FamObj.comp_map]

theorem assocHom_wkL_mid (X : FamObj C) {Y₁ Y₂ : FamObj C} (g : Y₁ ⟶ Y₂)
    (Z : FamObj C) :
    wkR (wkL X g) Z ≫ assocHom X Y₂ Z = assocHom X Y₁ Z ≫ wkL X (wkR g Z) := by
  apply fam_ext
  · ext i; rcases i with (a | b) | c <;> rfl
  · intro i; rcases i with (a | b) | c <;> apply heq_of_eq
    · erw [FamObj.comp_map]
    · erw [FamObj.comp_map, FamObj.comp_map]
      erw [wkR_map_inl]; erw [wkL_map_inr]; erw [assocHom_map_inl_inr]
      erw [Category.id_comp, Category.comp_id]
    · erw [FamObj.comp_map]

theorem assocHom_wkL_right (X Y : FamObj C) {Z₁ Z₂ : FamObj C} (h : Z₁ ⟶ Z₂) :
    wkL (tensorObj X Y) h ≫ assocHom X Y Z₂ = assocHom X Y Z₁ ≫ wkL X (wkL Y h) := by
  apply fam_ext
  · ext i; rcases i with (a | b) | c <;> rfl
  · intro i; rcases i with (a | b) | c <;> apply heq_of_eq
    · erw [FamObj.comp_map]
    · erw [FamObj.comp_map]
    · erw [FamObj.comp_map, FamObj.comp_map]
      erw [wkL_map_inr]; erw [assocHom_map_inr]
      erw [assocHom_map_inr]; erw [wkL_map_inr]; erw [wkL_map_inr]
      erw [Category.id_comp, Category.comp_id]

theorem braidHom_wkR {X₁ X₂ : FamObj C} (f : X₁ ⟶ X₂) (Y : FamObj C) :
    wkR f Y ≫ braidHom X₂ Y = braidHom X₁ Y ≫ wkL Y f := by
  apply fam_ext
  · ext i; rcases i with a | b <;> rfl
  · intro i; rcases i with a | b <;> apply heq_of_eq
    · erw [FamObj.comp_map, FamObj.comp_map]
      erw [wkR_map_inl]; erw [braidHom_map_inl]
      erw [braidHom_map_inl]; erw [wkL_map_inr]
      erw [Category.id_comp, Category.comp_id]
    · erw [FamObj.comp_map]

theorem braidHom_wkL (X : FamObj C) {Y₁ Y₂ : FamObj C} (g : Y₁ ⟶ Y₂) :
    wkL X g ≫ braidHom X Y₂ = braidHom X Y₁ ≫ wkR g X := by
  apply fam_ext
  · ext i; rcases i with a | b <;> rfl
  · intro i; rcases i with a | b <;> apply heq_of_eq
    · erw [FamObj.comp_map]
    · erw [FamObj.comp_map, FamObj.comp_map]
      erw [wkL_map_inr]; erw [braidHom_map_inr]
      erw [braidHom_map_inr]; erw [wkR_map_inl]
      erw [Category.id_comp, Category.comp_id]

/-! ## Isomorphisms -/

noncomputable def assocIso (X Y Z : FamObj C) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom := assocHom X Y Z
  inv := assocInv X Y Z
  hom_inv_id := by
    apply fam_ext
    · ext i; rcases i with (a | b) | c <;> rfl
    · intro i; rcases i with (a | b) | c <;> exact heq_of_eq (Category.id_comp _)
  inv_hom_id := by
    apply fam_ext
    · ext i; rcases i with a | (b | c) <;> rfl
    · intro i; rcases i with a | (b | c) <;> exact heq_of_eq (Category.id_comp _)

noncomputable def braidIso (X Y : FamObj C) :
    tensorObj X Y ≅ tensorObj Y X where
  hom := braidHom X Y
  inv := braidHom Y X
  hom_inv_id := by
    apply fam_ext
    · ext i; rcases i with a | b <;> rfl
    · intro i; rcases i with a | b <;> exact heq_of_eq (Category.id_comp _)
  inv_hom_id := by
    apply fam_ext
    · ext i; rcases i with b | a <;> rfl
    · intro i; rcases i with b | a <;> exact heq_of_eq (Category.id_comp _)

theorem braidIso_hom (X Y : FamObj C) : (braidIso X Y).hom = braidHom X Y := rfl
theorem braidIso_inv (X Y : FamObj C) : (braidIso X Y).inv = braidHom Y X := rfl

noncomputable instance : MonoidalCategoryStruct (FamObj C) where
  tensorObj := tensorObj
  whiskerLeft := wkL
  whiskerRight := wkR
  tensorUnit := unitObj
  associator := assocIso
  leftUnitor := lUnit
  rightUnitor := rUnit

/-! ## Simp lemmas bridging class projections to concrete definitions -/

@[simp] theorem whiskerLeft_def (X : FamObj C) {Y₁ Y₂ : FamObj C} (f : Y₁ ⟶ Y₂) :
    (X ◁ f) = wkL X f := rfl

@[simp] theorem whiskerRight_def {X₁ X₂ : FamObj C} (f : X₁ ⟶ X₂) (Y : FamObj C) :
    (f ▷ Y) = wkR f Y := rfl

@[simp] theorem tensorHom_eq {X₁ Y₁ X₂ Y₂ : FamObj C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) = wkR f X₂ ≫ wkL Y₁ g := rfl

@[simp] theorem associator_hom_eq (X Y Z : FamObj C) :
    (α_ X Y Z).hom = assocHom X Y Z := rfl

@[simp] theorem associator_inv_eq (X Y Z : FamObj C) :
    (α_ X Y Z).inv = assocInv X Y Z := rfl

@[simp] theorem leftUnitor_hom_eq (X : FamObj C) :
    (λ_ X).hom = (lUnit X).hom := rfl

@[simp] theorem rightUnitor_hom_eq (X : FamObj C) :
    (ρ_ X).hom = (rUnit X).hom := rfl

/-! ## Tactic for map-field goals

For goals involving only structural morphisms (all `𝟙` map components),
`erw` with `isDefEq` matching can rewrite inside dependent function arguments
where `simp`/`dsimp` discrimination trees cannot. The pattern is:
1. `erw [FamObj.comp_map]` to expand compositions
2. `erw [specific_map_lemma]` to reduce individual `.map` calls
3. `erw [Category.id_comp]` to close residual `𝟙 ≫ 𝟙 = 𝟙` goals

For naturality axioms, we use morphism-level intermediate lemmas
(`assocHom_wkR`, `braidHom_wkR`, etc.) to avoid complex `erw` chains. -/

/-! ## MonoidalCategory -/

private theorem assocNat {X₁ Y₁ X₂ Y₂ X₃ Y₃ : FamObj C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
    (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  simp only [tensorHom_eq, associator_hom_eq]
  rw [← wkR_comp, Category.assoc, Category.assoc]
  erw [assocHom_wkL_right]
  rw [← Category.assoc (wkR (wkL _ _) _)]
  erw [assocHom_wkL_mid]
  rw [Category.assoc (assocHom _ _ _), wkL_comp, ← Category.assoc (wkR _ _)]
  erw [assocHom_wkR]
  rw [Category.assoc]
  congr 2

noncomputable instance : MonoidalCategory (FamObj C) where
  tensorHom_def _ _ := rfl
  id_tensorHom_id X₁ X₂ := by
    show wkR (𝟙 X₁) X₂ ≫ wkL X₁ (𝟙 X₂) = 𝟙 _
    simp [wkR_id, wkL_id]
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    show (wkR f₁ _ ≫ wkL _ f₂) ≫ (wkR g₁ _ ≫ wkL _ g₂) = wkR (f₁ ≫ g₁) _ ≫ wkL _ (f₂ ≫ g₂)
    rw [Category.assoc, ← Category.assoc (wkL _ f₂), (wkR_wkL_comm g₁ f₂).symm,
        Category.assoc (wkR g₁ _), wkL_comp, ← Category.assoc, wkR_comp]
  whiskerLeft_id X Y := wkL_id X Y
  id_whiskerRight X Y := wkR_id X Y
  associator_naturality f₁ f₂ f₃ := assocNat f₁ f₂ f₃
  leftUnitor_naturality f := by
    apply fam_ext
    · ext i; rcases i with e | a
      · exact (Empty.elim e)
      · rfl
    · intro i; rcases i with e | a
      · exact (Empty.elim e)
      · apply heq_of_eq
        erw [FamObj.comp_map, FamObj.comp_map]
        erw [wkL_map_inr]; erw [lUnit_hom_map_inr]
        erw [lUnit_hom_map_inr]; erw [wkL_map_inr]
        erw [Category.id_comp, Category.comp_id]
  rightUnitor_naturality f := by
    apply fam_ext
    · ext i; rcases i with a | e
      · rfl
      · exact (Empty.elim e)
    · intro i; rcases i with a | e
      · apply heq_of_eq
        erw [FamObj.comp_map, FamObj.comp_map]
        erw [wkR_map_inl]; erw [rUnit_hom_map_inl]
        erw [rUnit_hom_map_inl]; erw [wkR_map_inl]
        erw [Category.id_comp, Category.comp_id]
      · exact (Empty.elim e)
  pentagon W X Y Z := by
    apply fam_ext
    · ext i; rcases i with ((w | x) | y) | z <;> rfl
    · intro i; rcases i with ((w | x) | y) | z <;> apply heq_of_eq
      · simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq]
        erw [FamObj.comp_map, FamObj.comp_map]
        erw [wkR_map_inl]; erw [assocHom_map_inl_inl]
        erw [Category.id_comp]
      · simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq]
        erw [FamObj.comp_map, FamObj.comp_map]
        erw [wkR_map_inl]; erw [assocHom_map_inl_inr]
        erw [Category.id_comp]
      · simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq]
        erw [FamObj.comp_map, FamObj.comp_map]
        erw [wkR_map_inl]; erw [assocHom_map_inr]
        erw [Category.id_comp]
      · simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq]
        erw [FamObj.comp_map, FamObj.comp_map]
        erw [wkR_map_inr]
        erw [Category.id_comp]
  triangle X Y := by
    apply fam_ext
    · ext i; rcases i with (a | e) | b
      · rfl
      · exact (Empty.elim e)
      · rfl
    · intro i; rcases i with (a | e) | b
      · apply heq_of_eq
        simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq, rightUnitor_hom_eq]
        erw [FamObj.comp_map]
        erw [assocHom_map_inl_inl]
        erw [Category.id_comp]
      · exact (Empty.elim e)
      · apply heq_of_eq
        simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq, rightUnitor_hom_eq]
        erw [FamObj.comp_map]
        erw [assocHom_map_inr]
        erw [Category.id_comp]

/-! ## BraidedCategory and SymmetricCategory -/

noncomputable instance : BraidedCategory (FamObj C) where
  braiding := braidIso
  braiding_naturality_right X {Y Z} f := by
    simp only [whiskerLeft_def, whiskerRight_def, braidIso_hom]
    exact braidHom_wkL X f
  braiding_naturality_left {X Y} f Z := by
    simp only [whiskerLeft_def, whiskerRight_def, braidIso_hom]
    exact braidHom_wkR f Z
  hexagon_forward X Y Z := by
    apply fam_ext
    · ext i; rcases i with (a | b) | c <;> rfl
    · intro i; rcases i with (a | b) | c <;> apply heq_of_eq
      · simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq]
        rfl
      · simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq]
        rfl
      · simp only [whiskerRight_def, whiskerLeft_def, associator_hom_eq]
        rfl
  hexagon_reverse X Y Z := by
    apply fam_ext
    · ext i; rcases i with a | (b | c) <;> rfl
    · intro i; rcases i with a | (b | c) <;> apply heq_of_eq
      · simp only [whiskerRight_def, whiskerLeft_def, associator_inv_eq]
        rfl
      · simp only [whiskerRight_def, whiskerLeft_def, associator_inv_eq]
        rfl
      · simp only [whiskerRight_def, whiskerLeft_def, associator_inv_eq]
        rfl

noncomputable instance : SymmetricCategory (FamObj C) where
  symmetry X Y := by
    show (braidIso X Y).hom ≫ (braidIso Y X).hom = 𝟙 _
    exact (braidIso X Y).hom_inv_id

end FamObj

end CatCrypt.Category

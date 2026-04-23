/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.CategoryTheory.MarkovCategory.Basic
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Kleisli Category of PMF as a Markov Category

The Kleisli category of the `PMF` monad (probability mass functions), with `Prod`
as tensor and `PUnit` as unit, forms a Markov category — the first non-trivial
instance of `MarkovCategory`.

Full probability (`PMF`) rather than sub-probability (`PMF (Option α)`) is needed because
`discard_natural` (`f ≫ ε = ε`) requires mass preservation. The key lemma is
`PMF.bind_const : (p.bind fun _ => q) = q`, giving `discard_natural` for free.

## Main results

* `MonoidalCategory (KleisliCat PMF)` — `Prod` tensor, `PUnit` unit
* `BraidedCategory (KleisliCat PMF)` — braiding swaps components via `pure`
* `SymmetricCategory (KleisliCat PMF)` — braiding is self-inverse
* `CopyDiscardCategory (KleisliCat PMF)` — diagonal copy, terminal discard
* `MarkovCategory (KleisliCat PMF)` — `discard_natural` via `PMF.bind_const`
-/

namespace CategoryTheory.KleisliCat

open MonoidalCategory

variable {α β γ : KleisliCat PMF}

/-- Composition in `KleisliCat PMF` applies the first morphism then binds the second. -/
@[simp]
theorem comp_apply (f : α ⟶ β) (g : β ⟶ γ) (x : α) :
    (f ≫ g) x = (f x).bind g := rfl

/-- The identity morphism in `KleisliCat PMF` is `PMF.pure`. -/
@[simp]
theorem id_apply (x : α) : (𝟙 α) x = PMF.pure x := rfl

/-- Bridge between the generic `pure` and `PMF.pure`, needed because `KleisliCat.id_def`
    rewrites `𝟙 α` to the generic monad `pure`. -/
@[simp]
theorem pure_eq (a : α) : (pure a : PMF α) = PMF.pure a := rfl

/-! ## Monoidal structure -/

/-- Left whiskering: tensors the identity on `X` with a morphism `f` on the right. -/
noncomputable def whiskerLeftPMF (X : KleisliCat PMF) {Y₁ Y₂ : KleisliCat PMF}
    (f : Y₁ ⟶ Y₂) : (show KleisliCat PMF from X × Y₁) ⟶ (show KleisliCat PMF from X × Y₂) :=
  fun ⟨x, y⟩ => (f y).bind (fun y' => PMF.pure (x, y'))

/-- Right whiskering: tensors a morphism `f` on the left with the identity on `Y`. -/
noncomputable def whiskerRightPMF {X₁ X₂ : KleisliCat PMF} (f : X₁ ⟶ X₂)
    (Y : KleisliCat PMF) :
    (show KleisliCat PMF from X₁ × Y) ⟶ (show KleisliCat PMF from X₂ × Y) :=
  fun ⟨x, y⟩ => (f x).bind (fun x' => PMF.pure (x', y))

/-- Forward component of the associator. -/
noncomputable def assocHomPMF (X Y Z : KleisliCat PMF) :
    (show KleisliCat PMF from (X × Y) × Z) ⟶ (show KleisliCat PMF from X × (Y × Z)) :=
  fun ⟨⟨x, y⟩, z⟩ => PMF.pure (x, (y, z))

/-- Inverse component of the associator. -/
noncomputable def assocInvPMF (X Y Z : KleisliCat PMF) :
    (show KleisliCat PMF from X × (Y × Z)) ⟶ (show KleisliCat PMF from (X × Y) × Z) :=
  fun ⟨x, y, z⟩ => PMF.pure ((x, y), z)

/-- Associator isomorphism for the tensor product. -/
noncomputable def assocIsoPMF (X Y Z : KleisliCat PMF) :
    (show KleisliCat PMF from (X × Y) × Z) ≅ (show KleisliCat PMF from X × (Y × Z)) where
  hom := assocHomPMF X Y Z
  inv := assocInvPMF X Y Z
  hom_inv_id := by funext ⟨⟨x, y⟩, z⟩; simp [assocHomPMF, assocInvPMF]
  inv_hom_id := by funext ⟨x, y, z⟩; simp [assocHomPMF, assocInvPMF]

/-- Left unitor: `PUnit ⊗ X ≅ X`. -/
noncomputable def leftUnitorPMF (X : KleisliCat PMF) :
    (show KleisliCat PMF from PUnit × X) ≅ X where
  hom := fun ⟨_, x⟩ => PMF.pure x
  inv := fun x => PMF.pure (PUnit.unit, x)
  hom_inv_id := by funext ⟨⟨⟩, x⟩; simp
  inv_hom_id := by funext x; simp

/-- Right unitor: `X ⊗ PUnit ≅ X`. -/
noncomputable def rightUnitorPMF (X : KleisliCat PMF) :
    (show KleisliCat PMF from X × PUnit) ≅ X where
  hom := fun ⟨x, _⟩ => PMF.pure x
  inv := fun x => PMF.pure (x, PUnit.unit)
  hom_inv_id := by funext ⟨x, ⟨⟩⟩; simp
  inv_hom_id := by funext x; simp

/-- Forward component of the braiding: swaps the two components. -/
noncomputable def braidHomPMF (X Y : KleisliCat PMF) :
    (show KleisliCat PMF from X × Y) ⟶ (show KleisliCat PMF from Y × X) :=
  fun ⟨x, y⟩ => PMF.pure (y, x)

/-- Braiding isomorphism: swaps the two tensor factors. -/
noncomputable def braidIsoPMF (X Y : KleisliCat PMF) :
    (show KleisliCat PMF from X × Y) ≅ (show KleisliCat PMF from Y × X) where
  hom := braidHomPMF X Y
  inv := braidHomPMF Y X
  hom_inv_id := by funext ⟨x, y⟩; simp [braidHomPMF]
  inv_hom_id := by funext ⟨y, x⟩; simp [braidHomPMF]

noncomputable instance : MonoidalCategoryStruct (KleisliCat PMF) where
  tensorObj X Y := (show KleisliCat PMF from X × Y)
  whiskerLeft := whiskerLeftPMF
  whiskerRight := whiskerRightPMF
  tensorUnit := (show KleisliCat PMF from PUnit)
  associator := assocIsoPMF
  leftUnitor := leftUnitorPMF
  rightUnitor := rightUnitorPMF

/-! ## Simp lemmas -/

@[simp]
theorem whiskerLeft_def (X : KleisliCat PMF) {Y₁ Y₂ : KleisliCat PMF} (f : Y₁ ⟶ Y₂) :
    (X ◁ f) = whiskerLeftPMF X f := rfl

@[simp]
theorem whiskerRight_def {X₁ X₂ : KleisliCat PMF} (f : X₁ ⟶ X₂) (Y : KleisliCat PMF) :
    (f ▷ Y) = whiskerRightPMF f Y := rfl

@[simp]
theorem tensorHom_eq {X₁ Y₁ X₂ Y₂ : KleisliCat PMF} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) = whiskerRightPMF f X₂ ≫ whiskerLeftPMF Y₁ g := rfl

@[simp]
theorem associator_hom_eq (X Y Z : KleisliCat PMF) :
    (α_ X Y Z).hom = assocHomPMF X Y Z := rfl

@[simp]
theorem associator_inv_eq (X Y Z : KleisliCat PMF) :
    (α_ X Y Z).inv = assocInvPMF X Y Z := rfl

@[simp]
theorem leftUnitor_hom_eq (X : KleisliCat PMF) :
    (λ_ X).hom = (leftUnitorPMF X).hom := rfl

@[simp]
theorem leftUnitor_inv_eq (X : KleisliCat PMF) :
    (λ_ X).inv = (leftUnitorPMF X).inv := rfl

@[simp]
theorem rightUnitor_hom_eq (X : KleisliCat PMF) :
    (ρ_ X).hom = (rightUnitorPMF X).hom := rfl

@[simp]
theorem rightUnitor_inv_eq (X : KleisliCat PMF) :
    (ρ_ X).inv = (rightUnitorPMF X).inv := rfl

/-! ## MonoidalCategory -/

noncomputable instance : MonoidalCategory (KleisliCat PMF) where
  tensorHom_def _ _ := rfl
  id_tensorHom_id X₁ X₂ := by
    funext ⟨x, y⟩; simp [whiskerLeftPMF, whiskerRightPMF]
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    funext ⟨x, y⟩; simp [whiskerLeftPMF, whiskerRightPMF]
    congr 1; funext x'
    exact PMF.bind_comm (f₂ y) (g₁ x') _
  whiskerLeft_id X Y := by
    funext ⟨x, y⟩; simp [whiskerLeftPMF]
  id_whiskerRight X Y := by
    funext ⟨x, y⟩; simp [whiskerRightPMF]
  associator_naturality f₁ f₂ f₃ := by
    funext ⟨⟨x₁, x₂⟩, x₃⟩; simp [whiskerLeftPMF, whiskerRightPMF, assocHomPMF]
  leftUnitor_naturality f := by
    funext ⟨⟨⟩, x⟩; simp [whiskerLeftPMF, leftUnitorPMF]
  rightUnitor_naturality f := by
    funext ⟨x, ⟨⟩⟩; simp [whiskerRightPMF, rightUnitorPMF]
  pentagon W X Y Z := by
    funext ⟨⟨⟨w, x⟩, y⟩, z⟩; simp [whiskerLeftPMF, whiskerRightPMF, assocHomPMF]
  triangle X Y := by
    funext ⟨⟨x, ⟨⟩⟩, y⟩
    simp [whiskerLeftPMF, whiskerRightPMF, assocHomPMF, leftUnitorPMF, rightUnitorPMF]

/-! ## BraidedCategory and SymmetricCategory -/

noncomputable instance : BraidedCategory (KleisliCat PMF) where
  braiding := braidIsoPMF
  braiding_naturality_right X {Y Z} f := by
    funext ⟨x, y⟩; simp [whiskerLeftPMF, whiskerRightPMF, braidHomPMF, braidIsoPMF]
  braiding_naturality_left {X Y} f Z := by
    funext ⟨x, z⟩; simp [whiskerLeftPMF, whiskerRightPMF, braidHomPMF, braidIsoPMF]
  hexagon_forward X Y Z := by
    funext ⟨⟨x, y⟩, z⟩
    simp [whiskerLeftPMF, whiskerRightPMF, assocHomPMF, braidHomPMF, braidIsoPMF]
  hexagon_reverse X Y Z := by
    funext ⟨x, y, z⟩
    simp [whiskerLeftPMF, whiskerRightPMF, assocInvPMF, braidHomPMF, braidIsoPMF]

noncomputable instance : SymmetricCategory (KleisliCat PMF) where
  symmetry X Y := by
    show (braidIsoPMF X Y).hom ≫ (braidIsoPMF Y X).hom = 𝟙 _
    exact (braidIsoPMF X Y).hom_inv_id

/-! ## ComonObj (copy = diagonal, delete = terminal) -/

/-- Every type in `KleisliCat PMF` is a comonoid object:
    `comul` is the diagonal and `counit` is the terminal map. -/
noncomputable instance instComonObjPMF (X : KleisliCat PMF) : ComonObj X where
  comul := fun x => PMF.pure (x, x)
  counit := fun _ => PMF.pure PUnit.unit
  counit_comul := by
    funext x; simp [whiskerRightPMF, leftUnitorPMF]
  comul_counit := by
    funext x; simp [whiskerLeftPMF, rightUnitorPMF]
  comul_assoc := by
    funext x; simp [whiskerLeftPMF, whiskerRightPMF, assocHomPMF]

@[simp]
theorem braiding_hom_eq (X Y : KleisliCat PMF) :
    (β_ X Y).hom = braidHomPMF X Y := rfl

@[simp]
theorem braiding_inv_eq (X Y : KleisliCat PMF) :
    (β_ X Y).inv = braidHomPMF Y X := rfl

/-- Every type in `KleisliCat PMF` is a commutative comonoid object. -/
noncomputable instance instIsCommComonObjPMF (X : KleisliCat PMF) : IsCommComonObj X where
  comul_comm := by
    funext x
    simp only [comp_apply, instComonObjPMF, braiding_hom_eq, braidHomPMF, PMF.pure_bind]

/-! ## CopyDiscardCategory -/

/-- The tensor strength `tensorμ` acts as a pure reshuffling on product types. -/
theorem tensorμ_apply (X₁ X₂ Y₁ Y₂ : KleisliCat PMF)
    (x₁ : X₁) (x₂ : X₂) (y₁ : Y₁) (y₂ : Y₂) :
    tensorμ X₁ X₂ Y₁ Y₂ ((x₁, x₂), (y₁, y₂)) =
      PMF.pure ((x₁, y₁), (x₂, y₂)) := by
  simp only [tensorμ, braiding_hom_eq]
  simp [whiskerLeftPMF, whiskerRightPMF, assocHomPMF, assocInvPMF, braidHomPMF]

noncomputable instance : CopyDiscardCategory (KleisliCat PMF) where
  copy_tensor X Y := by
    funext ⟨x, y⟩
    simp only [comp_apply, instComonObjPMF, tensorHom_eq, whiskerRightPMF,
      whiskerLeftPMF, PMF.pure_bind]
    exact (tensorμ_apply X X Y Y x x y y).symm
  discard_tensor X Y := by
    funext ⟨x, y⟩
    simp only [comp_apply, instComonObjPMF, tensorHom_eq, whiskerRightPMF,
      whiskerLeftPMF, leftUnitor_hom_eq, leftUnitorPMF, PMF.pure_bind]
  copy_unit := by
    funext ⟨⟩
    simp only [instComonObjPMF, leftUnitor_inv_eq, leftUnitorPMF]
  discard_unit := by
    funext ⟨⟩
    simp only [instComonObjPMF, id_apply]

/-! ## MarkovCategory -/

/-- `KleisliCat PMF` is a Markov category:
    discarding after any stochastic map equals discarding directly. -/
noncomputable instance : MarkovCategory (KleisliCat PMF) where
  discard_natural f := by
    funext x; simp only [comp_apply]
    exact PMF.bind_const (f x) (PMF.pure PUnit.unit)

end CategoryTheory.KleisliCat

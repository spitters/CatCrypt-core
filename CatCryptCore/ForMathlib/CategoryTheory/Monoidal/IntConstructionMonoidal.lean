/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.IntConstruction

/-!
# The monoidal structure of the Int construction

For a traced symmetric monoidal category `C`, the Int construction `IntConstruction C` is a
monoidal category. The tensor product is componentwise, `X ⊗ Y = (X⁺ ⊗ Y⁺, X⁻ ⊗ Y⁻)`, and the
tensor product of `f : X₁ ⟶ Y₁` and `g : X₂ ⟶ Y₂` is the tensor product `f ⊗ g` in `C`,
conjugated by the symmetries `tensorμ` that regroup positive and negative components. The
associator, the unitors and the symmetry are those of `C` on the positive components and their
inverses on the negative components. The dual of `X` is `(X⁻, X⁺)`; the pairing of `X` with its
dual is the tensor product of the pairings of `(X⁺, 𝟙)` with `(𝟙, X⁺)` and of `(𝟙, X⁻)` with
`(X⁻, 𝟙)`, whose coevaluations and evaluations are unitors of `C`.

## Main definitions

* `CategoryTheory.IntConstruction.tensorHom`: the tensor product of morphisms.
* `CategoryTheory.IntConstruction.mkHom`: the morphism `X ⟶ Y` given by `X⁺ ⟶ Y⁺` and
  `Y⁻ ⟶ X⁻`.
* `CategoryTheory.IntConstruction.instMonoidalCategory`: the Int construction is monoidal.
* `CategoryTheory.IntConstruction.instSymmetricCategory`: the Int construction is symmetric.
* `CategoryTheory.IntConstruction.instRigidCategory`: the Int construction is rigid.
* `CategoryTheory.IntConstruction.inclusionCoreMonoidal`: the inclusion `C ⥤ IntConstruction C`
  is monoidal.

## Main results

* `CategoryTheory.IntConstruction.tensorHom_comp_tensorHom`: functoriality of the tensor
  product, from the trace of a tensor product of morphisms
  (`CategoryTheory.IntConstruction.trace_tensorμ_tensorHom_tensorμ`).
* `CategoryTheory.IntConstruction.posNegCoevaluation_evaluation` and
  `CategoryTheory.IntConstruction.posNegEvaluation_coevaluation`: the zig-zag laws for
  `(A, 𝟙)` and `(𝟙, A)`, by yanking.

## References

* A. Joyal, R. Street, D. Verity, *Traced monoidal categories*, Math. Proc. Cambridge Philos.
  Soc. 119 (1996).
* S. Abramsky, E. Haghverdi, P. Scott, *Geometry of interaction and linear combinatory
  algebras*, Math. Structures Comput. Sci. 12 (2002).
-/

set_option autoImplicit false

@[expose] public section

universe v u

namespace CategoryTheory

open Category MonoidalCategory BraidedCategory

namespace IntConstruction

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- In a symmetric category, `tensorμ` followed by `tensorμ` with the middle objects exchanged
is the identity. -/
@[reassoc (attr := simp)]
theorem tensorμ_tensorμ (X₁ X₂ Y₁ Y₂ : C) :
    tensorμ X₁ X₂ Y₁ Y₂ ≫ tensorμ X₁ Y₁ X₂ Y₂ = 𝟙 _ := by
  have h : tensorμ X₁ Y₁ X₂ Y₂ = tensorδ X₁ X₂ Y₁ Y₂ := by
    simp only [tensorμ, tensorδ, SymmetricCategory.braiding_swap_eq_inv_braiding]
  rw [h, tensorμ_tensorδ]

/-- The whiskered form of `tensorμ_tensorμ`. -/
@[reassoc (attr := simp)]
theorem whiskerRight_tensorμ_tensorμ (X₁ X₂ Y₁ Y₂ Z : C) :
    tensorμ X₁ X₂ Y₁ Y₂ ▷ Z ≫ tensorμ X₁ Y₁ X₂ Y₂ ▷ Z = 𝟙 _ := by
  rw [← comp_whiskerRight, tensorμ_tensorμ, id_whiskerRight]

/-- The symmetry of a tensor product of pairs is the tensor product of the symmetries,
conjugated by `tensorμ`. -/
@[reassoc]
theorem tensorμ_comp_braiding_tensorHom_braiding (U U' V V' : C) :
    tensorμ U U' V V' ≫ ((β_ U V).hom ⊗ₘ (β_ U' V').hom) =
      (β_ (U ⊗ U') (V ⊗ V')).hom ≫ tensorμ V V' U U' := by
  calc _ = 𝟙 _ ⊗≫ U ◁ (β_ U' V).hom ▷ V' ⊗≫
          ((β_ U V).hom ▷ (U' ⊗ V') ≫ (V ⊗ U) ◁ (β_ U' V').hom) ⊗≫ 𝟙 _ := by
        simp only [tensorμ, tensorHom_def]; monoidal
    _ = 𝟙 _ ⊗≫ U ◁ (β_ U' V).hom ▷ V' ⊗≫ (U ⊗ V) ◁ (β_ U' V').hom ⊗≫
          (β_ U V).hom ▷ (V' ⊗ U') ⊗≫ V ◁ ((β_ U V').hom ≫ (β_ V' U).hom) ▷ U' ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, SymmetricCategory.symmetry]; monoidal
    _ = _ := by
        rw [braiding_tensor_left_hom, braiding_tensor_right_hom, braiding_tensor_right_hom]
        simp only [tensorμ]; monoidal

/-- Regrouping `((X₁ ⊗ X₂) ⊗ (U₁ ⊗ U₂)) ⊗ (V₁ ⊗ V₂)` as
`((X₁ ⊗ U₁) ⊗ V₁) ⊗ ((X₂ ⊗ U₂) ⊗ V₂)`. -/
def tensorμ₃ (X₁ X₂ U₁ U₂ V₁ V₂ : C) :
    ((X₁ ⊗ X₂) ⊗ (U₁ ⊗ U₂)) ⊗ (V₁ ⊗ V₂) ⟶ ((X₁ ⊗ U₁) ⊗ V₁) ⊗ ((X₂ ⊗ U₂) ⊗ V₂) :=
  tensorμ X₁ X₂ U₁ U₂ ▷ (V₁ ⊗ V₂) ≫ tensorμ (X₁ ⊗ U₁) (X₂ ⊗ U₂) V₁ V₂

/-- Exchanging the last two factors of a tensor product of pairs is the tensor product of the
exchanges, conjugated by `tensorμ₃`. -/
@[reassoc]
theorem swapRight_tensorμ₃ (X₁ X₂ U₁ U₂ V₁ V₂ : C) :
    swapRight (X₁ ⊗ X₂) (U₁ ⊗ U₂) (V₁ ⊗ V₂) ≫ tensorμ₃ X₁ X₂ V₁ V₂ U₁ U₂ =
      tensorμ₃ X₁ X₂ U₁ U₂ V₁ V₂ ≫ (swapRight X₁ U₁ V₁ ⊗ₘ swapRight X₂ U₂ V₂) := by
  have e : tensorμ₃ X₁ X₂ V₁ V₂ U₁ U₂ = (α_ _ _ _).hom ≫
      (X₁ ⊗ X₂) ◁ tensorμ V₁ V₂ U₁ U₂ ≫ tensorμ X₁ X₂ (V₁ ⊗ U₁) (V₂ ⊗ U₂) ≫
        ((α_ X₁ V₁ U₁).inv ⊗ₘ (α_ X₂ V₂ U₂).inv) := by
    rw [← cancel_mono ((α_ X₁ V₁ U₁).hom ⊗ₘ (α_ X₂ V₂ U₂).hom)]
    simp only [tensorμ₃, assoc, tensor_associativity, tensorHom_comp_tensorHom,
      Iso.inv_hom_id, id_tensorHom_id, comp_id]
  calc _ = (α_ _ _ _).hom ≫ (X₁ ⊗ X₂) ◁ ((β_ (U₁ ⊗ U₂) (V₁ ⊗ V₂)).hom ≫
        tensorμ V₁ V₂ U₁ U₂) ≫ tensorμ X₁ X₂ (V₁ ⊗ U₁) (V₂ ⊗ U₂) ≫
        ((α_ X₁ V₁ U₁).inv ⊗ₘ (α_ X₂ V₂ U₂).inv) := by
        rw [e]; simp only [swapRight, assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]
    _ = (α_ _ _ _).hom ≫ (X₁ ⊗ X₂) ◁ tensorμ U₁ U₂ V₁ V₂ ≫ tensorμ X₁ X₂ (U₁ ⊗ V₁) (U₂ ⊗ V₂) ≫
        (X₁ ◁ (β_ U₁ V₁).hom ⊗ₘ X₂ ◁ (β_ U₂ V₂).hom) ≫
        ((α_ X₁ V₁ U₁).inv ⊗ₘ (α_ X₂ V₂ U₂).inv) := by
        rw [← tensorμ_comp_braiding_tensorHom_braiding, whiskerLeft_comp_assoc,
          tensorμ_natural_right_assoc]
    _ = _ := by
        simp only [tensorμ₃, swapRight, assoc, ← tensorHom_comp_tensorHom,
          tensor_associativity_assoc]

/-- Tensoring a morphism conjugated by `tensorμ` with an object pair, and regrouping by
`tensorμ₃`, is the tensor product of the whiskered morphisms. -/
@[reassoc]
theorem whiskerRight_tensorμ₃ {P₁ P₂ Q₁ Q₂ R₁ R₂ S₁ S₂ : C} (h₁ : P₁ ⊗ Q₁ ⟶ R₁ ⊗ S₁)
    (h₂ : P₂ ⊗ Q₂ ⟶ R₂ ⊗ S₂) (W₁ W₂ : C) :
    (tensorμ P₁ P₂ Q₁ Q₂ ≫ (h₁ ⊗ₘ h₂) ≫ tensorμ R₁ S₁ R₂ S₂) ▷ (W₁ ⊗ W₂) ≫
        tensorμ₃ R₁ R₂ S₁ S₂ W₁ W₂ =
      tensorμ₃ P₁ P₂ Q₁ Q₂ W₁ W₂ ≫ (h₁ ▷ W₁ ⊗ₘ h₂ ▷ W₂) := by
  simp only [tensorμ₃, comp_whiskerRight, assoc, whiskerRight_tensorμ_tensorμ_assoc,
    tensorμ_natural_left]

/-- The kernel of the composite of two tensor products is the tensor product of the kernels,
conjugated by `tensorμ₃`. -/
theorem swapRight_comp_tensorμ₃ {A₁ A₂ a₁ a₂ B₁ B₂ b₁ b₂ E₁ E₂ e₁ e₂ : C}
    (f₁ : A₁ ⊗ b₁ ⟶ B₁ ⊗ a₁) (f₂ : A₂ ⊗ b₂ ⟶ B₂ ⊗ a₂)
    (g₁ : B₁ ⊗ e₁ ⟶ E₁ ⊗ b₁) (g₂ : B₂ ⊗ e₂ ⟶ E₂ ⊗ b₂) :
    (swapRight (A₁ ⊗ A₂) (e₁ ⊗ e₂) (b₁ ⊗ b₂) ≫
        (tensorμ A₁ A₂ b₁ b₂ ≫ (f₁ ⊗ₘ f₂) ≫ tensorμ B₁ a₁ B₂ a₂) ▷ (e₁ ⊗ e₂) ≫
        swapRight (B₁ ⊗ B₂) (a₁ ⊗ a₂) (e₁ ⊗ e₂) ≫
        (tensorμ B₁ B₂ e₁ e₂ ≫ (g₁ ⊗ₘ g₂) ≫ tensorμ E₁ b₁ E₂ b₂) ▷ (a₁ ⊗ a₂) ≫
        swapRight (E₁ ⊗ E₂) (b₁ ⊗ b₂) (a₁ ⊗ a₂)) ≫ tensorμ₃ E₁ E₂ a₁ a₂ b₁ b₂ =
      tensorμ₃ A₁ A₂ e₁ e₂ b₁ b₂ ≫
        ((swapRight A₁ e₁ b₁ ≫ f₁ ▷ e₁ ≫ swapRight B₁ a₁ e₁ ≫ g₁ ▷ a₁ ≫ swapRight E₁ b₁ a₁) ⊗ₘ
          (swapRight A₂ e₂ b₂ ≫ f₂ ▷ e₂ ≫ swapRight B₂ a₂ e₂ ≫ g₂ ▷ a₂ ≫
            swapRight E₂ b₂ a₂)) := by
  simp only [assoc, swapRight_tensorμ₃, swapRight_tensorμ₃_assoc, whiskerRight_tensorμ₃_assoc,
    tensorHom_comp_tensorHom]

omit [SymmetricCategory C] in
/-- Tensoring a composite of three morphisms on the right by `f`. -/
theorem comp_comp_tensorHom {X X' Y Y' Z Z' : C} (x : X ⟶ X') (y : X' ⟶ Y') (z : Y' ⟶ Z)
    (f : Y ⟶ Z') : (x ≫ y ≫ z) ⊗ₘ f = x ▷ Y ≫ (y ⊗ₘ f) ≫ z ▷ Z' := by
  rw [← tensorHom_id, ← tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, id_comp, comp_id]

omit [SymmetricCategory C] in
/-- Tensoring a composite of three morphisms on the left by `f`. -/
theorem tensorHom_comp_comp {X X' Y Y' Z Z' : C} (f : Z ⟶ Z') (x : X ⟶ X') (y : X' ⟶ Y')
    (z : Y' ⟶ Y) : f ⊗ₘ (x ≫ y ≫ z) = Z ◁ x ≫ (f ⊗ₘ y) ≫ Z' ◁ z := by
  rw [← id_tensorHom, ← id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, id_comp, comp_id]

/-- The associativity of the tensor product of morphisms conjugated by `tensorμ`, up to the
associators of the positive components and the inverse associators of the negative
components. -/
theorem tensorμ_tensorHom_tensorμ_assoc_aux {A₁ A₂ A₃ a₁ a₂ a₃ B₁ B₂ B₃ b₁ b₂ b₃ : C}
    (f₁ : A₁ ⊗ b₁ ⟶ B₁ ⊗ a₁) (f₂ : A₂ ⊗ b₂ ⟶ B₂ ⊗ a₂) (f₃ : A₃ ⊗ b₃ ⟶ B₃ ⊗ a₃) :
    ((A₁ ⊗ A₂) ⊗ A₃) ◁ (α_ b₁ b₂ b₃).inv ≫
        (tensorμ (A₁ ⊗ A₂) A₃ (b₁ ⊗ b₂) b₃ ≫
          ((tensorμ A₁ A₂ b₁ b₂ ≫ (f₁ ⊗ₘ f₂) ≫ tensorμ B₁ a₁ B₂ a₂) ⊗ₘ f₃) ≫
          tensorμ (B₁ ⊗ B₂) (a₁ ⊗ a₂) B₃ a₃) ≫
        (α_ B₁ B₂ B₃).hom ▷ ((a₁ ⊗ a₂) ⊗ a₃) =
      (α_ A₁ A₂ A₃).hom ▷ (b₁ ⊗ (b₂ ⊗ b₃)) ≫
        (tensorμ A₁ (A₂ ⊗ A₃) b₁ (b₂ ⊗ b₃) ≫
          (f₁ ⊗ₘ (tensorμ A₂ A₃ b₂ b₃ ≫ (f₂ ⊗ₘ f₃) ≫ tensorμ B₂ a₂ B₃ a₃)) ≫
          tensorμ B₁ a₁ (B₂ ⊗ B₃) (a₂ ⊗ a₃)) ≫
        (B₁ ⊗ (B₂ ⊗ B₃)) ◁ (α_ a₁ a₂ a₃).inv := by
  have hμ : tensorμ (A₁ ⊗ A₂) A₃ (b₁ ⊗ b₂) b₃ ≫ tensorμ A₁ A₂ b₁ b₂ ▷ (A₃ ⊗ b₃) =
      ((α_ A₁ A₂ A₃).hom ⊗ₘ (α_ b₁ b₂ b₃).hom) ≫ tensorμ A₁ (A₂ ⊗ A₃) b₁ (b₂ ⊗ b₃) ≫
        (A₁ ⊗ b₁) ◁ tensorμ A₂ A₃ b₂ b₃ ≫ (α_ _ _ _).inv := by
    simp only [← assoc]
    rw [Iso.eq_comp_inv]
    simp only [assoc]
    exact associator_monoidal A₁ A₂ A₃ b₁ b₂ b₃
  have hδ : tensorμ B₁ a₁ B₂ a₂ ▷ (B₃ ⊗ a₃) ≫ tensorμ (B₁ ⊗ B₂) (a₁ ⊗ a₂) B₃ a₃ =
      (α_ _ _ _).hom ≫ (B₁ ⊗ a₁) ◁ tensorμ B₂ a₂ B₃ a₃ ≫
        tensorμ B₁ a₁ (B₂ ⊗ B₃) (a₂ ⊗ a₃) ≫ ((α_ B₁ B₂ B₃).inv ⊗ₘ (α_ a₁ a₂ a₃).inv) := by
    rw [← cancel_mono ((α_ B₁ B₂ B₃).hom ⊗ₘ (α_ a₁ a₂ a₃).hom)]
    simp only [assoc, MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id,
      id_tensorHom_id, comp_id]
    exact tensor_associativity B₁ a₁ B₂ a₂ B₃ a₃
  rw [comp_comp_tensorHom, tensorHom_comp_comp]
  simp only [assoc]
  rw [reassoc_of% hμ, reassoc_of% hδ, ← associator_inv_naturality_assoc, Iso.inv_hom_id_assoc]
  simp [tensorHom_def']

/-- The symmetry of the tensor product of morphisms conjugated by `tensorμ`, up to the
symmetries of the positive components and the inverse symmetries of the negative
components. -/
theorem tensorμ_tensorHom_tensorμ_braiding_aux {A₁ A₂ a₁ a₂ B₁ B₂ b₁ b₂ : C}
    (f : A₁ ⊗ b₁ ⟶ B₁ ⊗ a₁) (g : A₂ ⊗ b₂ ⟶ B₂ ⊗ a₂) :
    (A₁ ⊗ A₂) ◁ (β_ b₁ b₂).inv ≫ (tensorμ A₁ A₂ b₁ b₂ ≫ (f ⊗ₘ g) ≫ tensorμ B₁ a₁ B₂ a₂) ≫
        (β_ B₁ B₂).hom ▷ (a₁ ⊗ a₂) =
      (β_ A₁ A₂).hom ▷ (b₂ ⊗ b₁) ≫ (tensorμ A₂ A₁ b₂ b₁ ≫ (g ⊗ₘ f) ≫ tensorμ B₂ a₂ B₁ a₁) ≫
        (B₂ ⊗ B₁) ◁ (β_ a₁ a₂).inv := by
  have h₁ : (A₁ ⊗ A₂) ◁ (β_ b₁ b₂).inv ≫ tensorμ A₁ A₂ b₁ b₂ ≫
      (β_ (A₁ ⊗ b₁) (A₂ ⊗ b₂)).hom = (β_ A₁ A₂).hom ▷ (b₂ ⊗ b₁) ≫ tensorμ A₂ A₁ b₂ b₁ := by
    have hB := tensorμ_comp_braiding_tensorHom_braiding A₁ b₁ A₂ b₂ =≫ tensorμ A₂ A₁ b₂ b₁
    simp only [assoc, tensorμ_tensorμ, comp_id] at hB
    rw [← hB, tensorμ_tensorμ_assoc, tensorHom_def']
    simp
  have h₂ : (β_ (B₂ ⊗ a₂) (B₁ ⊗ a₁)).hom ≫ tensorμ B₁ a₁ B₂ a₂ ≫
      (β_ B₁ B₂).hom ▷ (a₁ ⊗ a₂) = tensorμ B₂ a₂ B₁ a₁ ≫ (B₂ ⊗ B₁) ◁ (β_ a₁ a₂).inv := by
    have hB := tensorμ_comp_braiding_tensorHom_braiding B₂ a₂ B₁ a₁ =≫ tensorμ B₁ B₂ a₁ a₂
    simp only [assoc, tensorμ_tensorμ, comp_id] at hB
    rw [← hB]
    simp only [assoc, tensorμ_tensorμ_assoc, tensorHom_def',
      ← SymmetricCategory.braiding_swap_eq_inv_braiding]
    rw [← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight, comp_id]
  have hfg : f ⊗ₘ g = (β_ (A₁ ⊗ b₁) (A₂ ⊗ b₂)).hom ≫ (g ⊗ₘ f) ≫
      (β_ (B₂ ⊗ a₂) (B₁ ⊗ a₁)).hom := by
    rw [← braiding_naturality_assoc, SymmetricCategory.symmetry, comp_id]
  rw [hfg]
  simp only [assoc]
  rw [reassoc_of% h₁, h₂]

/-- Exchanging the last two factors is natural in the third factor. -/
@[reassoc]
theorem swapRight_naturality_right (X U : C) {V V' : C} (h : V ⟶ V') :
    (X ⊗ U) ◁ h ≫ swapRight X U V' = swapRight X U V ≫ (X ◁ h) ▷ U := by
  simp only [swapRight, assoc, associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    braiding_naturality_right, whiskerLeft_comp, associator_inv_naturality_middle]

/-- Exchanging the last two factors is natural in the second factor. -/
@[reassoc]
theorem swapRight_naturality_middle (X : C) {U U' : C} (g : U ⟶ U') (V : C) :
    (X ◁ g) ▷ V ≫ swapRight X U' V = swapRight X U V ≫ (X ⊗ V) ◁ g := by
  simp only [swapRight, assoc, associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    braiding_naturality_left, whiskerLeft_comp, associator_inv_naturality_right]

/-- Exchanging the last two factors is natural in the first factor. -/
@[reassoc]
theorem swapRight_naturality_left {X X' : C} (f : X ⟶ X') (U V : C) :
    (f ▷ U) ▷ V ≫ swapRight X' U V = swapRight X U V ≫ (f ▷ V) ▷ U := by
  simp only [swapRight, assoc, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left]

end Symmetric

section Traced

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [TracedCategory C]

open TracedCategory

/-- The trace over `U ⊗ V` of a tensor product of morphisms, regrouped by `tensorμ`, is the
tensor product of the traces. -/
theorem trace_tensorμ_tensorHom_tensorμ (U V : C) {A A' B B' : C} (F : A ⊗ U ⟶ B ⊗ U)
    (G : A' ⊗ V ⟶ B' ⊗ V) :
    trace (U ⊗ V) (tensorμ A A' U V ≫ (F ⊗ₘ G) ≫ tensorμ B U B' V) =
      trace U F ⊗ₘ trace V G := by
  have h : (α_ (A ⊗ A') U V).hom ≫ (tensorμ A A' U V ≫ (F ⊗ₘ G) ≫ tensorμ B U B' V) ≫
      (α_ (B ⊗ B') U V).inv =
      (swapRight A A' U ≫ F ▷ A') ▷ V ≫
        ((α_ (B ⊗ U) A' V).hom ≫ (B ⊗ U) ◁ G ≫ (α_ (B ⊗ U) B' V).inv) ≫
        swapRight B U B' ▷ V := by
    simp only [tensorμ, swapRight, tensorHom_def]; monoidal
  rw [trace_tensor, h, trace_naturality, ← whiskerLeft_trace, tensorHom_def, whiskerRight_trace,
    ← trace_comp_whiskerRight, swapRight_naturality_right]
  simp only [assoc]

/-- The tensor product of objects of the Int construction, `(X⁺ ⊗ Y⁺, X⁻ ⊗ Y⁻)`. -/
abbrev tensorObj (X Y : IntConstruction C) : IntConstruction C :=
  ⟨X.pos ⊗ Y.pos, X.neg ⊗ Y.neg⟩

/-- The tensor product of morphisms of the Int construction: the tensor product in `C`,
conjugated by `tensorμ`. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : IntConstruction C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorμ X₁.pos X₂.pos Y₁.neg Y₂.neg ≫ (f.hom ⊗ₘ g.hom) ≫ tensorμ Y₁.pos X₁.neg Y₂.pos X₂.neg⟩

/-- Unfolding lemma for `tensorHom`. -/
theorem tensorHom_hom {X₁ Y₁ X₂ Y₂ : IntConstruction C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (tensorHom f g).hom =
      tensorμ X₁.pos X₂.pos Y₁.neg Y₂.neg ≫ (f.hom ⊗ₘ g.hom) ≫
        tensorμ Y₁.pos X₁.neg Y₂.pos X₂.neg :=
  rfl

/-- The tensor product of morphisms of the Int construction is functorial. -/
theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : IntConstruction C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  ext
  have e : compKernel (tensorHom f₁ f₂) (tensorHom g₁ g₂) =
      tensorμ X₁.pos X₂.pos Z₁.neg Z₂.neg ▷ (Y₁.neg ⊗ Y₂.neg) ≫
        (tensorμ (X₁.pos ⊗ Z₁.neg) (X₂.pos ⊗ Z₂.neg) Y₁.neg Y₂.neg ≫
          (compKernel f₁ g₁ ⊗ₘ compKernel f₂ g₂) ≫
          tensorμ (Z₁.pos ⊗ X₁.neg) Y₁.neg (Z₂.pos ⊗ X₂.neg) Y₂.neg) ≫
        tensorμ Z₁.pos X₁.neg Z₂.pos X₂.neg ▷ (Y₁.neg ⊗ Y₂.neg) := by
    have hK : compKernel (tensorHom f₁ f₂) (tensorHom g₁ g₂) ≫
        tensorμ₃ Z₁.pos Z₂.pos X₁.neg X₂.neg Y₁.neg Y₂.neg =
        tensorμ₃ X₁.pos X₂.pos Z₁.neg Z₂.neg Y₁.neg Y₂.neg ≫
          (compKernel f₁ g₁ ⊗ₘ compKernel f₂ g₂) :=
      swapRight_comp_tensorμ₃ f₁.hom f₂.hom g₁.hom g₂.hom
    calc _ = (compKernel (tensorHom f₁ f₂) (tensorHom g₁ g₂) ≫
          tensorμ₃ Z₁.pos Z₂.pos X₁.neg X₂.neg Y₁.neg Y₂.neg) ≫
          tensorμ (Z₁.pos ⊗ X₁.neg) Y₁.neg (Z₂.pos ⊗ X₂.neg) Y₂.neg ≫
          tensorμ Z₁.pos X₁.neg Z₂.pos X₂.neg ▷ (Y₁.neg ⊗ Y₂.neg) := by
          simp only [tensorμ₃, assoc, tensorμ_tensorμ_assoc, whiskerRight_tensorμ_tensorμ,
            comp_id]
      _ = _ := by rw [hK]; simp only [tensorμ₃, assoc]
  rw [comp_hom, e, trace_naturality, trace_tensorμ_tensorHom_tensorμ]
  rfl

/-- The morphism `X ⟶ Y` of the Int construction given by `u : X⁺ ⟶ Y⁺` and
`v : Y⁻ ⟶ X⁻`. -/
def mkHom {X Y : IntConstruction C} (u : X.pos ⟶ Y.pos) (v : Y.neg ⟶ X.neg) : X ⟶ Y :=
  ⟨u ⊗ₘ v⟩

/-- Unfolding lemma for `mkHom`. -/
@[simp]
theorem mkHom_hom {X Y : IntConstruction C} (u : X.pos ⟶ Y.pos) (v : Y.neg ⟶ X.neg) :
    (mkHom u v).hom = u ⊗ₘ v :=
  rfl

/-- Composing with `mkHom u v` on the left composes with `u` and `v` in `C`. -/
theorem mkHom_comp_hom {X Y Z : IntConstruction C} (u : X.pos ⟶ Y.pos) (v : Y.neg ⟶ X.neg)
    (g : Y ⟶ Z) : (mkHom u v ≫ g).hom = u ▷ Z.neg ≫ g.hom ≫ Z.pos ◁ v := by
  have e : compKernel (mkHom u v) g = (u ▷ Z.neg ≫ g.hom) ▷ Y.neg ≫
      swapRight Z.pos Y.neg Y.neg ≫ (Z.pos ◁ v) ▷ Y.neg := by
    simp only [compKernel, mkHom_hom, tensorHom_def, comp_whiskerRight, assoc]
    rw [← swapRight_naturality_left_assoc, swapRight_naturality_middle_assoc,
      swapRight_swapRight_assoc, whisker_exchange_assoc, swapRight_naturality_right]
  rw [comp_hom, e, trace_naturality, trace_swapRight, id_comp, assoc]

/-- Composing with `mkHom u v` on the right composes with `u` and `v` in `C`. -/
theorem comp_mkHom_hom {X Y Z : IntConstruction C} (f : X ⟶ Y) (u : Y.pos ⟶ Z.pos)
    (v : Z.neg ⟶ Y.neg) : (f ≫ mkHom u v).hom = X.pos ◁ v ≫ f.hom ≫ u ▷ X.neg := by
  have e : compKernel f (mkHom u v) = (X.pos ◁ v) ▷ Y.neg ≫
      swapRight X.pos Y.neg Y.neg ≫ (f.hom ≫ u ▷ X.neg) ▷ Y.neg := by
    simp only [compKernel, mkHom_hom, tensorHom_def', comp_whiskerRight, assoc]
    rw [swapRight_naturality_left, swapRight_naturality_middle_assoc,
      swapRight_swapRight_assoc, ← whisker_exchange_assoc, ← swapRight_naturality_middle_assoc]
  rw [comp_hom, e, trace_naturality, trace_swapRight, id_comp]

/-- The composite of two morphisms of the form `mkHom`. -/
@[simp]
theorem mkHom_comp_mkHom {X Y Z : IntConstruction C} (u : X.pos ⟶ Y.pos) (v : Y.neg ⟶ X.neg)
    (u' : Y.pos ⟶ Z.pos) (v' : Z.neg ⟶ Y.neg) :
    mkHom u v ≫ mkHom u' v' = mkHom (u ≫ u') (v' ≫ v) := by
  ext
  simp [mkHom_comp_hom, tensorHom_def]

/-- The identity is `mkHom` of identities. -/
theorem id_eq_mkHom (X : IntConstruction C) : 𝟙 X = mkHom (𝟙 X.pos) (𝟙 X.neg) := by
  ext
  simp

/-- The isomorphism `X ≅ Y` of the Int construction given by `X⁺ ≅ Y⁺` and `X⁻ ≅ Y⁻`. -/
def mkIso {X Y : IntConstruction C} (e : X.pos ≅ Y.pos) (e' : X.neg ≅ Y.neg) : X ≅ Y where
  hom := mkHom e.hom e'.inv
  inv := mkHom e.inv e'.hom
  hom_inv_id := by rw [mkHom_comp_mkHom, id_eq_mkHom]; simp
  inv_hom_id := by rw [mkHom_comp_mkHom, id_eq_mkHom]; simp

/-- Unfolding lemma for `mkIso`. -/
@[simp]
theorem mkIso_hom {X Y : IntConstruction C} (e : X.pos ≅ Y.pos) (e' : X.neg ≅ Y.neg) :
    (mkIso e e').hom = mkHom e.hom e'.inv :=
  rfl

/-- Unfolding lemma for `mkIso`. -/
@[simp]
theorem mkIso_inv {X Y : IntConstruction C} (e : X.pos ≅ Y.pos) (e' : X.neg ≅ Y.neg) :
    (mkIso e e').inv = mkHom e.inv e'.hom :=
  rfl

/-- The tensor product of two morphisms of the form `mkHom`. -/
theorem tensorHom_mkHom {X₁ Y₁ X₂ Y₂ : IntConstruction C} (u : X₁.pos ⟶ Y₁.pos)
    (v : Y₁.neg ⟶ X₁.neg) (u' : X₂.pos ⟶ Y₂.pos) (v' : Y₂.neg ⟶ X₂.neg) :
    tensorHom (mkHom u v) (mkHom u' v') =
      mkHom (X := tensorObj X₁ X₂) (Y := tensorObj Y₁ Y₂) (u ⊗ₘ u') (v ⊗ₘ v') := by
  ext
  simp only [tensorHom_hom, mkHom_hom]
  rw [tensorμ_natural, tensorμ_tensorμ_assoc]

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (IntConstruction C) where
  tensorObj := tensorObj
  whiskerLeft X _ _ g := tensorHom (𝟙 X) g
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := ⟨𝟙_ C, 𝟙_ C⟩
  associator X Y Z := mkIso (α_ X.pos Y.pos Z.pos) (α_ X.neg Y.neg Z.neg)
  leftUnitor X := mkIso (λ_ X.pos) (λ_ X.neg)
  rightUnitor X := mkIso (ρ_ X.pos) (ρ_ X.neg)

/-- Unfolding lemma: the positive component of the unit is the unit of `C`. -/
@[simp]
theorem tensorUnit_pos : (𝟙_ (IntConstruction C)).pos = 𝟙_ C :=
  rfl

/-- Unfolding lemma: the negative component of the unit is the unit of `C`. -/
@[simp]
theorem tensorUnit_neg : (𝟙_ (IntConstruction C)).neg = 𝟙_ C :=
  rfl

/-- The Int construction is a monoidal category. -/
instance instMonoidalCategory : MonoidalCategory (IntConstruction C) :=
  .ofTensorHom
    (id_tensorHom_id := fun X₁ X₂ => by
      ext
      change tensorμ _ _ _ _ ≫ (𝟙 _ ⊗ₘ 𝟙 _) ≫ tensorμ _ _ _ _ = 𝟙 _
      simp)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => tensorHom_comp_tensorHom f₁ f₂ g₁ g₂)
    (associator_naturality := fun f₁ f₂ f₃ => by
      ext
      change (tensorHom (tensorHom f₁ f₂) f₃ ≫ mkHom _ _).hom =
        (mkHom _ _ ≫ tensorHom f₁ (tensorHom f₂ f₃)).hom
      rw [comp_mkHom_hom, mkHom_comp_hom]
      exact tensorμ_tensorHom_tensorμ_assoc_aux f₁.hom f₂.hom f₃.hom)
    (leftUnitor_naturality := fun f => by
      ext
      change (tensorHom (𝟙 _) f ≫ mkHom _ _).hom = (mkHom _ _ ≫ f).hom
      rw [comp_mkHom_hom, mkHom_comp_hom]
      simp only [tensorHom_hom, id_hom, tensorμ, id_tensorHom]
      dsimp only [tensorUnit_pos, tensorUnit_neg]
      simp only [braiding_tensorUnit_left, braiding_tensorUnit_right]
      monoidal)
    (rightUnitor_naturality := fun f => by
      ext
      change (tensorHom f (𝟙 _) ≫ mkHom _ _).hom = (mkHom _ _ ≫ f).hom
      rw [comp_mkHom_hom, mkHom_comp_hom]
      simp only [tensorHom_hom, id_hom, tensorμ, tensorHom_id]
      dsimp only [tensorUnit_pos, tensorUnit_neg]
      simp only [braiding_tensorUnit_left, braiding_tensorUnit_right]
      monoidal)
    (pentagon := fun W X Y Z => by
      change tensorHom (mkHom _ _) (𝟙 Z) ≫ mkHom _ _ ≫ tensorHom (𝟙 W) (mkHom _ _) =
        mkHom _ _ ≫ mkHom _ _
      rw [id_eq_mkHom Z, id_eq_mkHom W, tensorHom_mkHom, tensorHom_mkHom, mkHom_comp_mkHom,
        mkHom_comp_mkHom, mkHom_comp_mkHom]
      congr 1 <;> monoidal)
    (triangle := fun X Y => by
      change mkHom _ _ ≫ tensorHom (𝟙 X) (mkHom _ _) = tensorHom (mkHom _ _) (𝟙 Y)
      rw [id_eq_mkHom X, id_eq_mkHom Y, tensorHom_mkHom, tensorHom_mkHom, mkHom_comp_mkHom]
      congr 1 <;> monoidal)

/-- Unfolding lemma: the positive component of a tensor product. -/
@[simp]
theorem tensor_pos (X Y : IntConstruction C) : (X ⊗ Y).pos = X.pos ⊗ Y.pos :=
  rfl

/-- Unfolding lemma: the negative component of a tensor product. -/
@[simp]
theorem tensor_neg (X Y : IntConstruction C) : (X ⊗ Y).neg = X.neg ⊗ Y.neg :=
  rfl

/-- Unfolding lemma for the associator. -/
theorem associator_hom (X Y Z : IntConstruction C) :
    (α_ X Y Z).hom = mkHom (α_ X.pos Y.pos Z.pos).hom (α_ X.neg Y.neg Z.neg).inv :=
  rfl

/-- Unfolding lemma for the inverse associator. -/
theorem associator_inv (X Y Z : IntConstruction C) :
    (α_ X Y Z).inv = mkHom (α_ X.pos Y.pos Z.pos).inv (α_ X.neg Y.neg Z.neg).hom :=
  rfl

/-- Unfolding lemma for the left unitor. -/
theorem leftUnitor_hom (X : IntConstruction C) :
    (λ_ X).hom = mkHom (λ_ X.pos).hom (λ_ X.neg).inv :=
  rfl

/-- Unfolding lemma for the inverse left unitor. -/
theorem leftUnitor_inv (X : IntConstruction C) :
    (λ_ X).inv = mkHom (λ_ X.pos).inv (λ_ X.neg).hom :=
  rfl

/-- Unfolding lemma for the right unitor. -/
theorem rightUnitor_hom (X : IntConstruction C) :
    (ρ_ X).hom = mkHom (ρ_ X.pos).hom (ρ_ X.neg).inv :=
  rfl

/-- Unfolding lemma for the inverse right unitor. -/
theorem rightUnitor_inv (X : IntConstruction C) :
    (ρ_ X).inv = mkHom (ρ_ X.pos).inv (ρ_ X.neg).hom :=
  rfl

/-- Whiskering `mkHom u v` on the right. -/
theorem mkHom_whiskerRight {X Y : IntConstruction C} (u : X.pos ⟶ Y.pos) (v : Y.neg ⟶ X.neg)
    (Z : IntConstruction C) :
    mkHom u v ▷ Z = mkHom (X := X ⊗ Z) (Y := Y ⊗ Z) (u ▷ Z.pos) (v ▷ Z.neg) := by
  change tensorHom (mkHom u v) (𝟙 Z) = _
  rw [id_eq_mkHom, tensorHom_mkHom]
  simp only [tensorHom_id]

/-- Whiskering `mkHom u v` on the left. -/
theorem whiskerLeft_mkHom (Z : IntConstruction C) {X Y : IntConstruction C}
    (u : X.pos ⟶ Y.pos) (v : Y.neg ⟶ X.neg) :
    Z ◁ mkHom u v = mkHom (X := Z ⊗ X) (Y := Z ⊗ Y) (Z.pos ◁ u) (Z.neg ◁ v) := by
  change tensorHom (𝟙 Z) (mkHom u v) = _
  rw [id_eq_mkHom, tensorHom_mkHom]
  simp only [id_tensorHom]

/-- Unfolding lemma: right whiskering is the tensor product with an identity. -/
theorem whiskerRight_hom' {X Y : IntConstruction C} (f : X ⟶ Y) (Z : IntConstruction C) :
    (f ▷ Z).hom = tensorμ X.pos Z.pos Y.neg Z.neg ≫ (f.hom ⊗ₘ 𝟙 _) ≫
      tensorμ Y.pos X.neg Z.pos Z.neg :=
  rfl

/-- Unfolding lemma: left whiskering is the tensor product with an identity. -/
theorem whiskerLeft_hom' (Z : IntConstruction C) {X Y : IntConstruction C} (f : X ⟶ Y) :
    (Z ◁ f).hom = tensorμ Z.pos X.pos Z.neg Y.neg ≫ (𝟙 _ ⊗ₘ f.hom) ≫
      tensorμ Z.pos Z.neg Y.pos X.neg :=
  rfl

/-- The symmetry of the Int construction: the symmetries of `C` on the positive components and
their inverses on the negative components. -/
abbrev braidingIso (X Y : IntConstruction C) : X ⊗ Y ≅ Y ⊗ X :=
  mkIso (β_ X.pos Y.pos) (β_ X.neg Y.neg)

/-- The symmetry of the Int construction is natural. -/
theorem tensorHom_comp_braidingIso {X₁ Y₁ X₂ Y₂ : IntConstruction C} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorHom f g ≫ (braidingIso Y₁ Y₂).hom = (braidingIso X₁ X₂).hom ≫ tensorHom g f := by
  ext
  change (tensorHom f g ≫ mkHom _ _).hom = (mkHom _ _ ≫ tensorHom g f).hom
  rw [comp_mkHom_hom, mkHom_comp_hom]
  exact tensorμ_tensorHom_tensorμ_braiding_aux f.hom g.hom

/-- The Int construction is a symmetric monoidal category. -/
instance instSymmetricCategory : SymmetricCategory (IntConstruction C) where
  braiding := braidingIso
  braiding_naturality_right X _ _ f := tensorHom_comp_braidingIso (𝟙 X) f
  braiding_naturality_left f Z := tensorHom_comp_braidingIso f (𝟙 Z)
  hexagon_forward X Y Z := by
    change mkHom _ _ ≫ mkHom _ _ ≫ mkHom _ _ =
      tensorHom (mkHom _ _) (𝟙 Z) ≫ mkHom _ _ ≫ tensorHom (𝟙 Y) (mkHom _ _)
    rw [id_eq_mkHom Z, id_eq_mkHom Y, tensorHom_mkHom, tensorHom_mkHom, mkHom_comp_mkHom,
      mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
    congr 1 <;> dsimp only [tensor_pos, tensor_neg] <;> simp
  hexagon_reverse X Y Z := by
    change mkHom _ _ ≫ mkHom _ _ ≫ mkHom _ _ =
      tensorHom (𝟙 X) (mkHom _ _) ≫ mkHom _ _ ≫ tensorHom (mkHom _ _) (𝟙 Y)
    rw [id_eq_mkHom X, id_eq_mkHom Y, tensorHom_mkHom, tensorHom_mkHom, mkHom_comp_mkHom,
      mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
    congr 1 <;> dsimp only [tensor_pos, tensor_neg] <;> simp
  symmetry X Y := by
    change mkHom _ _ ≫ mkHom _ _ = 𝟙 _
    rw [mkHom_comp_mkHom, id_eq_mkHom]
    simp [← SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- The image `⟨f ▷ 𝟙_ C⟩` of `f` under the inclusion is `mkHom f (𝟙 (𝟙_ C))`. -/
theorem mk_whiskerRight_tensorUnit {X Y : C} (f : X ⟶ Y) :
    (⟨f ▷ 𝟙_ C⟩ : (⟨X, 𝟙_ C⟩ : IntConstruction C) ⟶ ⟨Y, 𝟙_ C⟩) = mkHom f (𝟙 (𝟙_ C)) := by
  ext
  simp

/-- The monoidal structure of the inclusion `C ⥤ IntConstruction C`: the unit is preserved
on the nose, and `(X, 𝟙) ⊗ (Y, 𝟙) ≅ (X ⊗ Y, 𝟙)` is the left unitor of `𝟙_ C` on the negative
components. -/
def inclusionCoreMonoidal : (inclusion C).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := mkIso (X := (inclusion C).obj X ⊗ (inclusion C).obj Y)
    (Y := (inclusion C).obj (X ⊗ Y)) (Iso.refl _) (λ_ (𝟙_ C))
  μIso_hom_natural_left f X' := by
    dsimp only [inclusion]
    simp only [mk_whiskerRight_tensorUnit, mkIso_hom, mkHom_whiskerRight, mkHom_comp_mkHom,
      Iso.refl_hom]
    congr 1 <;> simp
  μIso_hom_natural_right X' f := by
    dsimp only [inclusion]
    simp only [mk_whiskerRight_tensorUnit, mkIso_hom, whiskerLeft_mkHom, mkHom_comp_mkHom,
      Iso.refl_hom]
    congr 1 <;> simp
  associativity X Y Z := by
    dsimp only [inclusion]
    simp only [mk_whiskerRight_tensorUnit, mkIso_hom, whiskerLeft_mkHom, mkHom_whiskerRight,
      mkHom_comp_mkHom, Iso.refl_hom, associator_hom]
    congr 1 <;> monoidal
  left_unitality X := by
    dsimp only [inclusion]
    simp only [mk_whiskerRight_tensorUnit, mkIso_hom, mkHom_whiskerRight, mkHom_comp_mkHom,
      Iso.refl_hom, leftUnitor_hom, id_eq_mkHom]
    congr 1 <;> simp
  right_unitality X := by
    dsimp only [inclusion]
    simp only [mk_whiskerRight_tensorUnit, mkIso_hom, whiskerLeft_mkHom, mkHom_comp_mkHom,
      Iso.refl_hom, rightUnitor_hom, id_eq_mkHom]
    congr 1 <;> monoidal

/-- The inclusion `C ⥤ IntConstruction C` is monoidal. -/
instance : (inclusion C).Monoidal :=
  (inclusionCoreMonoidal (C := C)).toMonoidal

/-- The coevaluation `𝟙 ⟶ (A, 𝟙) ⊗ (𝟙, A)`: the unitors of `C`. -/
def posNegCoevaluation (A : C) :
    𝟙_ (IntConstruction C) ⟶ (⟨A, 𝟙_ C⟩ ⊗ ⟨𝟙_ C, A⟩ : IntConstruction C) :=
  ⟨(λ_ _).hom ≫ (λ_ A).hom ≫ (ρ_ A).inv ≫ (ρ_ _).inv⟩

/-- The evaluation `(𝟙, A) ⊗ (A, 𝟙) ⟶ 𝟙`: the unitors of `C`. -/
def posNegEvaluation (A : C) :
    (⟨𝟙_ C, A⟩ ⊗ ⟨A, 𝟙_ C⟩ : IntConstruction C) ⟶ 𝟙_ (IntConstruction C) :=
  ⟨(ρ_ _).hom ≫ (λ_ A).hom ≫ (ρ_ A).inv ≫ (λ_ _).inv⟩

/-- The first zig-zag law for `(A, 𝟙)` and `(𝟙, A)`. -/
theorem posNegCoevaluation_evaluation (A : C) :
    posNegCoevaluation A ▷ (⟨A, 𝟙_ C⟩ : IntConstruction C) ≫ (α_ _ _ _).hom ≫
      (⟨A, 𝟙_ C⟩ : IntConstruction C) ◁ posNegEvaluation A =
      (λ_ _).hom ≫ (ρ_ _).inv := by
  ext
  rw [comp_hom]
  dsimp only [tensor_neg]
  rw [trace_eq_trace_conj ((λ_ A).symm ≪≫ (ρ_ _).symm)]
  simp only [leftUnitor_hom, rightUnitor_inv, mkHom_comp_mkHom, mkHom_hom, compKernel,
    associator_hom, mkHom_comp_hom]
  calc _ = trace A ((⊗𝟙.hom : (𝟙_ C ⊗ A) ⊗ (𝟙_ C ⊗ 𝟙_ C) ⟶ 𝟙_ C ⊗ A) ▷ A ≫
        swapRight (𝟙_ C) A A ≫
        (⊗𝟙.hom : 𝟙_ C ⊗ A ⟶ (A ⊗ 𝟙_ C) ⊗ (𝟙_ C ⊗ 𝟙_ C)) ▷ A) := by
        congr 1
        simp only [whiskerRight_hom', whiskerLeft_hom', posNegCoevaluation, posNegEvaluation,
          swapRight, tensorμ, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
        dsimp only [tensor_pos, tensor_neg, tensorUnit_pos, tensorUnit_neg]
        simp only [braiding_tensor_left_hom, braiding_tensor_right_hom,
          braiding_tensorUnit_left, braiding_tensorUnit_right, id_tensorHom, tensorHom_id]
        monoidal
    _ = _ := by
        rw [trace_naturality, trace_swapRight]
        monoidal

/-- The second zig-zag law for `(A, 𝟙)` and `(𝟙, A)`. -/
theorem posNegEvaluation_coevaluation (A : C) :
    (⟨𝟙_ C, A⟩ : IntConstruction C) ◁ posNegCoevaluation A ≫ (α_ _ _ _).inv ≫
      posNegEvaluation A ▷ (⟨𝟙_ C, A⟩ : IntConstruction C) =
      (ρ_ _).hom ≫ (λ_ _).inv := by
  ext
  rw [comp_hom]
  dsimp only [tensor_neg]
  rw [trace_eq_trace_conj (whiskerLeftIso A (λ_ A).symm), trace_tensor]
  simp only [leftUnitor_inv, rightUnitor_hom, mkHom_comp_mkHom, mkHom_hom, compKernel,
    associator_inv, mkHom_comp_hom]
  calc _ = trace A (trace A
        (((⊗𝟙.hom : ((𝟙_ C ⊗ 𝟙_ C) ⊗ (𝟙_ C ⊗ A)) ⊗ A ⟶ A ⊗ A) ≫ (β_ A A).hom) ▷ A ≫
          swapRight A A A ≫
          (⊗𝟙.hom : A ⊗ A ⟶ ((𝟙_ C ⊗ 𝟙_ C) ⊗ (A ⊗ 𝟙_ C)) ⊗ A) ▷ A)) := by
        congr 2
        refine Eq.trans (b := 𝟙 ((((𝟙_ C ⊗ 𝟙_ C) ⊗ (𝟙_ C ⊗ A)) ⊗ A) ⊗ A) ⊗≫
          (β_ A A).hom ▷ A ⊗≫ A ◁ (β_ A A).hom ⊗≫ (β_ A A).hom ▷ A ⊗≫
          A ◁ ((β_ A A).hom ≫ (β_ A A).hom) ⊗≫ (β_ A A).hom ▷ A ⊗≫
          𝟙 ((((𝟙_ C ⊗ 𝟙_ C) ⊗ (A ⊗ 𝟙_ C)) ⊗ A) ⊗ A)) ?_ ?_
        · simp only [whiskerRight_hom', whiskerLeft_hom', posNegCoevaluation,
            posNegEvaluation, swapRight, tensorμ, whiskerLeftIso_hom, whiskerLeftIso_inv,
            Iso.symm_hom, Iso.symm_inv]
          dsimp only [tensor_pos, tensor_neg, tensorUnit_pos, tensorUnit_neg]
          simp only [braiding_tensor_left_hom, braiding_tensor_right_hom,
            braiding_tensorUnit_left, braiding_tensorUnit_right, id_tensorHom, tensorHom_id]
          monoidal
        · rw [SymmetricCategory.symmetry]
          refine Eq.trans (b := 𝟙 ((((𝟙_ C ⊗ 𝟙_ C) ⊗ (𝟙_ C ⊗ A)) ⊗ A) ⊗ A) ⊗≫
            (β_ A A).hom ▷ A ⊗≫ A ◁ (β_ A A).hom ⊗≫ ((β_ A A).hom ≫ (β_ A A).hom) ▷ A ⊗≫
            𝟙 ((((𝟙_ C ⊗ 𝟙_ C) ⊗ (A ⊗ 𝟙_ C)) ⊗ A) ⊗ A)) (by monoidal) ?_
          rw [SymmetricCategory.symmetry]
          simp only [swapRight]
          monoidal
    _ = trace A ((⊗𝟙.hom : (𝟙_ C ⊗ 𝟙_ C) ⊗ (𝟙_ C ⊗ A) ⟶ 𝟙_ C ⊗ A) ▷ A ≫
        swapRight (𝟙_ C) A A ≫
        (⊗𝟙.hom : 𝟙_ C ⊗ A ⟶ (𝟙_ C ⊗ 𝟙_ C) ⊗ (A ⊗ 𝟙_ C)) ▷ A) := by
        rw [trace_naturality, trace_swapRight]
        congr 1
        simp only [swapRight]
        monoidal
    _ = _ := by
        rw [trace_naturality, trace_swapRight]
        monoidal

/-- The positive object `(A, 𝟙)` and the negative object `(𝟙, A)` form an exact pairing. -/
instance exactPairingPosNeg (A : C) :
    ExactPairing (⟨A, 𝟙_ C⟩ : IntConstruction C) ⟨𝟙_ C, A⟩ where
  coevaluation' := posNegCoevaluation A
  evaluation' := posNegEvaluation A
  coevaluation_evaluation' := posNegEvaluation_coevaluation A
  evaluation_coevaluation' := posNegCoevaluation_evaluation A

/-- The dual `(X⁻, X⁺)` of an object `X = (X⁺, X⁻)` of the Int construction. -/
def dual (X : IntConstruction C) : IntConstruction C :=
  ⟨X.neg, X.pos⟩

/-- An object `X` and its dual `(X⁻, X⁺)` form an exact pairing: `X ≅ (X⁺, 𝟙) ⊗ (𝟙, X⁻)`,
`(X⁻, X⁺) ≅ (X⁻, 𝟙) ⊗ (𝟙, X⁺)`, and the pairing is the tensor product of the pairings of
positive and negative objects. -/
instance exactPairingDual (X : IntConstruction C) : ExactPairing X (dual X) :=
  letI : ExactPairing (⟨𝟙_ C, X.neg⟩ : IntConstruction C) ⟨X.neg, 𝟙_ C⟩ :=
    exactPairing_swap _ _
  exactPairingCongr
    (X' := (⟨X.pos, 𝟙_ C⟩ : IntConstruction C) ⊗ ⟨𝟙_ C, X.neg⟩)
    (Y' := (⟨X.neg, 𝟙_ C⟩ : IntConstruction C) ⊗ ⟨𝟙_ C, X.pos⟩)
    (mkIso (ρ_ X.pos).symm (λ_ X.neg).symm) (mkIso (ρ_ X.neg).symm (λ_ X.pos).symm)

/-- Every object of the Int construction has a right dual. -/
instance (X : IntConstruction C) : HasRightDual X :=
  ⟨dual X⟩

/-- The Int construction is right rigid. -/
instance instRightRigidCategory : RightRigidCategory (IntConstruction C) where

/-- The Int construction is rigid. -/
instance instRigidCategory : RigidCategory (IntConstruction C) :=
  rigidCategoryOfRightRigidCategory

end Traced

end IntConstruction

end CategoryTheory

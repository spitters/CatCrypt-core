/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Traced symmetric monoidal categories

A trace on a symmetric monoidal category `C` assigns to every morphism `f : X ⊗ U ⟶ Y ⊗ U`
a morphism `trace U f : X ⟶ Y`, subject to the axioms of Joyal, Street and Verity in their
symmetric form: naturality in `X` and `Y` (tightening), dinaturality in `U` (sliding),
vanishing for the unit and for tensor products, superposing, and yanking.

Every right rigid braided category carries a partial trace: for an exact pairing of `U` with `D`,
the trace of `f` closes the `U` wire with the coevaluation and the braided evaluation of the
pairing. The partial trace does not depend on the chosen pairing, and in a symmetric category it
satisfies the axioms, so a right rigid symmetric category is traced.

## Main definitions

* `CategoryTheory.TracedCategory`: a trace on a symmetric monoidal category.
* `CategoryTheory.ExactPairing.partialTrace`: the partial trace along an exact pairing.
* `CategoryTheory.TracedCategory.ofRightRigidCategory`: the trace of a right rigid symmetric
  category.

## Main results

* `CategoryTheory.ExactPairing.partialTrace_whiskerLeft_comp`: sliding for the partial trace,
  along two possibly different exact pairings.
* `CategoryTheory.ExactPairing.partialTrace_congr`: the partial trace does not depend on the
  exact pairing.
* `CategoryTheory.ExactPairing.partialTrace_tensor`: vanishing for tensor products.

## References

* A. Joyal, R. Street, D. Verity, *Traced monoidal categories*, Math. Proc. Cambridge Philos.
  Soc. 119 (1996).
* M. Hasegawa, *Recursion from cyclic sharing: traced monoidal categories and models of cyclic
  lambda calculi*, TLCA 1997.
* P. Selinger, *A survey of graphical languages for monoidal categories*, in New Structures for
  Physics, Lecture Notes in Physics 813 (2011).
-/

set_option autoImplicit false

@[expose] public section

universe v u

namespace CategoryTheory

open Category MonoidalCategory BraidedCategory

/-- A trace on a symmetric monoidal category: an operation sending `f : X ⊗ U ⟶ Y ⊗ U` to
`trace U f : X ⟶ Y`, natural in `X` and `Y`, dinatural in `U`, compatible with the unit, the
tensor product and whiskering, and sending the symmetry `β_ U U` to the identity. -/
class TracedCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] where
  /-- The trace of `f : X ⊗ U ⟶ Y ⊗ U` over `U`. -/
  trace (U : C) {X Y : C} (f : X ⊗ U ⟶ Y ⊗ U) : X ⟶ Y
  /-- Naturality in the source (left tightening). -/
  trace_whiskerRight_comp (U : C) {X X' Y : C} (g : X' ⟶ X) (f : X ⊗ U ⟶ Y ⊗ U) :
    trace U (g ▷ U ≫ f) = g ≫ trace U f
  /-- Naturality in the target (right tightening). -/
  trace_comp_whiskerRight (U : C) {X Y Y' : C} (f : X ⊗ U ⟶ Y ⊗ U) (h : Y ⟶ Y') :
    trace U (f ≫ h ▷ U) = trace U f ≫ h
  /-- Dinaturality in the traced object (sliding). -/
  trace_whiskerLeft_comp {U U' X Y : C} (g : U ⟶ U') (f : X ⊗ U' ⟶ Y ⊗ U) :
    trace U (X ◁ g ≫ f) = trace U' (f ≫ Y ◁ g)
  /-- Vanishing for the unit object. -/
  trace_tensorUnit {X Y : C} (f : X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C) :
    trace (𝟙_ C) f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom
  /-- Vanishing for a tensor product: tracing over `U ⊗ V` traces over `V`, then over `U`. -/
  trace_tensor (U V : C) {X Y : C} (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :
    trace (U ⊗ V) f = trace U (trace V ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv))
  /-- Superposing: the trace commutes with whiskering on the left. -/
  whiskerLeft_trace (W U : C) {X Y : C} (f : X ⊗ U ⟶ Y ⊗ U) :
    W ◁ trace U f = trace U ((α_ W X U).hom ≫ W ◁ f ≫ (α_ W Y U).inv)
  /-- Yanking: the trace of the symmetry is the identity. -/
  trace_braiding (U : C) : trace U (β_ U U).hom = 𝟙 U

namespace TracedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [TracedCategory C]

attribute [reassoc] trace_whiskerRight_comp trace_comp_whiskerRight
attribute [simp] trace_tensorUnit trace_braiding

/-- Naturality in the source and the target at once (tightening). -/
@[reassoc]
theorem trace_naturality (U : C) {X X' Y Y' : C} (g : X' ⟶ X) (f : X ⊗ U ⟶ Y ⊗ U)
    (h : Y ⟶ Y') : trace U (g ▷ U ≫ f ≫ h ▷ U) = g ≫ trace U f ≫ h := by
  rw [trace_whiskerRight_comp, trace_comp_whiskerRight]

/-- Superposing with a tensor product of morphisms. -/
theorem tensorHom_trace (U : C) {W Z X Y : C} (g : W ⟶ Z) (f : X ⊗ U ⟶ Y ⊗ U) :
    g ⊗ₘ trace U f = trace U ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv) := by
  rw [tensorHom_def, tensorHom_def, whiskerLeft_trace, ← trace_whiskerRight_comp]
  simp only [assoc, associator_naturality_left_assoc]

/-- Yanking with the inverse symmetry. -/
@[simp]
theorem trace_braiding_inv (U : C) : trace U (β_ U U).inv = 𝟙 U := by
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding, trace_braiding]

end TracedCategory

namespace ExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {X X' Y Y' : C}

/-- The partial trace of `f : X ⊗ U ⟶ Y ⊗ U` along an exact pairing of `U` with `D`: open a
`U ⊗ D` pair with the coevaluation, apply `f`, and close the pair with the braiding followed by
the evaluation. -/
def partialTrace (U D : C) [ExactPairing U D] (f : X ⊗ U ⟶ Y ⊗ U) : X ⟶ Y :=
  (ρ_ X).inv ≫ X ◁ η_ U D ≫ (α_ X U D).inv ≫ f ▷ D ≫ (α_ Y U D).hom ≫
    Y ◁ ((β_ U D).hom ≫ ε_ U D) ≫ (ρ_ Y).hom

/-- The partial trace is natural in the source. -/
@[reassoc]
theorem partialTrace_whiskerRight_comp (U D : C) [ExactPairing U D] (g : X' ⟶ X)
    (f : X ⊗ U ⟶ Y ⊗ U) : partialTrace U D (g ▷ U ≫ f) = g ≫ partialTrace U D f := by
  simp only [partialTrace, comp_whiskerRight, assoc]
  rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]

/-- The partial trace is natural in the target. -/
@[reassoc]
theorem partialTrace_comp_whiskerRight (U D : C) [ExactPairing U D] (f : X ⊗ U ⟶ Y ⊗ U)
    (h : Y ⟶ Y') : partialTrace U D (f ≫ h ▷ U) = partialTrace U D f ≫ h := by
  simp only [partialTrace, comp_whiskerRight, assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]

/-- Sliding for the partial trace, along exact pairings `(U, D)` and `(U', D')`. -/
theorem partialTrace_whiskerLeft_comp {U U' D D' : C} [ExactPairing U D] [ExactPairing U' D']
    (g : U ⟶ U') (f : X ⊗ U' ⟶ Y ⊗ U) :
    partialTrace U D (X ◁ g ≫ f) = partialTrace U' D' (f ≫ Y ◁ g) := by
  obtain ⟨h, hη, hε⟩ : ∃ h : D' ⟶ D,
      η_ U D ≫ g ▷ D = η_ U' D' ≫ U' ◁ h ∧ h ▷ U ≫ ε_ U D = D' ◁ g ≫ ε_ U' D' := by
    let _ : HasRightDual U := ⟨D⟩
    let _ : HasRightDual U' := ⟨D'⟩
    exact ⟨gᘁ, (coevaluation_comp_rightAdjointMate g).symm, rightAdjointMate_comp_evaluation g⟩
  calc partialTrace U D (X ◁ g ≫ f)
      = (ρ_ X).inv ≫ X ◁ (η_ U D ≫ g ▷ D) ⊗≫ f ▷ D ⊗≫
          Y ◁ ((β_ U D).hom ≫ ε_ U D) ≫ (ρ_ Y).hom := by
        simp only [partialTrace]; monoidal
    _ = (ρ_ X).inv ≫ X ◁ η_ U' D' ⊗≫ ((X ⊗ U') ◁ h ≫ f ▷ D) ⊗≫
          Y ◁ ((β_ U D).hom ≫ ε_ U D) ≫ (ρ_ Y).hom := by
        rw [hη]; monoidal
    _ = (ρ_ X).inv ≫ X ◁ η_ U' D' ⊗≫ (f ▷ D' ≫ (Y ⊗ U) ◁ h) ⊗≫
          Y ◁ ((β_ U D).hom ≫ ε_ U D) ≫ (ρ_ Y).hom := by
        rw [whisker_exchange]
    _ = (ρ_ X).inv ≫ X ◁ η_ U' D' ⊗≫ f ▷ D' ⊗≫
          Y ◁ (U ◁ h ≫ (β_ U D).hom ≫ ε_ U D) ≫ (ρ_ Y).hom := by
        monoidal
    _ = (ρ_ X).inv ≫ X ◁ η_ U' D' ⊗≫ f ▷ D' ⊗≫
          Y ◁ ((β_ U D').hom ≫ D' ◁ g ≫ ε_ U' D') ≫ (ρ_ Y).hom := by
        rw [braiding_naturality_right_assoc, hε]
    _ = (ρ_ X).inv ≫ X ◁ η_ U' D' ⊗≫ f ▷ D' ⊗≫
          Y ◁ (g ▷ D' ≫ (β_ U' D').hom ≫ ε_ U' D') ≫ (ρ_ Y).hom := by
        rw [braiding_naturality_left_assoc]
    _ = partialTrace U' D' (f ≫ Y ◁ g) := by
        simp only [partialTrace]; monoidal

/-- The partial trace does not depend on the exact pairing. -/
theorem partialTrace_congr {U D D' : C} [ExactPairing U D] [ExactPairing U D']
    (f : X ⊗ U ⟶ Y ⊗ U) : partialTrace U D f = partialTrace U D' f := by
  simpa using partialTrace_whiskerLeft_comp (D := D) (D' := D') (𝟙 U) f

/-- Superposing for the partial trace. -/
theorem whiskerLeft_partialTrace (U D W : C) [ExactPairing U D] (f : X ⊗ U ⟶ Y ⊗ U) :
    W ◁ partialTrace U D f =
      partialTrace U D ((α_ W X U).hom ≫ W ◁ f ≫ (α_ W Y U).inv) := by
  simp only [partialTrace]; monoidal

/-- Vanishing for the unit object, along the exact pairing of the unit with itself. -/
theorem partialTrace_tensorUnit (f : X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C) :
    partialTrace (𝟙_ C) (𝟙_ C) f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom := by
  have h1 : η_ (𝟙_ C) (𝟙_ C) = (ρ_ _).inv := rfl
  have h2 : ε_ (𝟙_ C) (𝟙_ C) = (ρ_ _).hom := rfl
  simp only [partialTrace, h1, h2, braiding_tensorUnit_left]
  monoidal

/-- Yanking for the partial trace. -/
theorem partialTrace_braiding (U D : C) [ExactPairing U D] :
    partialTrace U D (β_ U U).hom = 𝟙 U := by
  calc partialTrace U D (β_ U U).hom
      = (ρ_ U).inv ≫ U ◁ η_ U D ≫ (β_ U (U ⊗ D)).hom ≫ (α_ U D U).hom ≫ U ◁ ε_ U D ≫
          (ρ_ U).hom := by
        simp [partialTrace]
    _ = (ρ_ U).inv ≫ (β_ U (𝟙_ C)).hom ≫ η_ U D ▷ U ≫ (α_ U D U).hom ≫ U ◁ ε_ U D ≫
          (ρ_ U).hom := by
        rw [braiding_naturality_right_assoc]
    _ = 𝟙 U := by
        simp [braiding_tensorUnit_right]

/-- The braided evaluation of a tensor product of exact pairings closes the inner pair first,
then the outer pair. -/
theorem braiding_comp_tensor_evaluation {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] (U V D E : C) [ExactPairing U D] [ExactPairing V E] :
    (β_ (U ⊗ V) (E ⊗ D)).hom ≫ ε_ (U ⊗ V) (E ⊗ D) =
      𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ≫ ε_ V E) ▷ D ⊗≫ (β_ U D).hom ≫ ε_ U D := by
  have hC : U ◁ (β_ V D).hom = (α_ U V D).inv ≫ (β_ V U).inv ▷ D ≫ (α_ V U D).hom ≫
      (β_ V (U ⊗ D)).hom ≫ (α_ U D V).hom := by
    rw [braiding_tensor_right_hom]; simp
  calc (β_ (U ⊗ V) (E ⊗ D)).hom ≫ ε_ (U ⊗ V) (E ⊗ D)
      = 𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ▷ D) ⊗≫ ((U ⊗ E) ◁ (β_ V D).hom ≫
          (β_ U E).hom ▷ (D ⊗ V)) ⊗≫ E ◁ (((β_ U D).hom ≫ ε_ U D) ▷ V) ⊗≫ ε_ V E := by
        rw [braiding_tensor_left_hom, braiding_tensor_right_hom, braiding_tensor_right_hom,
          tensor_evaluation]
        monoidal
    _ = 𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ▷ D) ⊗≫ (β_ U E).hom ▷ (V ⊗ D) ⊗≫
          E ◁ ((U ◁ (β_ V D).hom) ⊗≫ ((β_ U D).hom ≫ ε_ U D) ▷ V) ⊗≫ ε_ V E := by
        rw [whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ▷ D) ⊗≫ (β_ U E).hom ▷ (V ⊗ D) ⊗≫
          E ◁ ((β_ V U).inv ▷ D) ⊗≫
          E ◁ ((β_ V (U ⊗ D)).hom ≫ ((β_ U D).hom ≫ ε_ U D) ▷ V) ⊗≫ ε_ V E := by
        rw [hC]; monoidal
    _ = 𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ▷ D) ⊗≫ (β_ U E).hom ▷ (V ⊗ D) ⊗≫
          E ◁ ((β_ V U).inv ▷ D) ⊗≫
          E ◁ (V ◁ ((β_ U D).hom ≫ ε_ U D) ≫ (β_ V (𝟙_ C)).hom) ⊗≫ ε_ V E := by
        rw [braiding_naturality_right]
    _ = 𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ▷ D) ⊗≫ (β_ U E).hom ▷ (V ⊗ D) ⊗≫
          E ◁ ((β_ V U).inv ▷ D) ⊗≫
          ((E ⊗ V) ◁ ((β_ U D).hom ≫ ε_ U D) ≫ ε_ V E ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
        rw [braiding_tensorUnit_right]; monoidal
    _ = 𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ▷ D) ⊗≫ (β_ U E).hom ▷ (V ⊗ D) ⊗≫
          E ◁ ((β_ V U).inv ▷ D) ⊗≫
          (ε_ V E ▷ (U ⊗ D) ≫ 𝟙_ C ◁ ((β_ U D).hom ≫ ε_ U D)) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ▷ D) ⊗≫
          ((β_ U (E ⊗ V)).hom ≫ ε_ V E ▷ U) ▷ D ⊗≫ (β_ U D).hom ≫ ε_ U D := by
        rw [braiding_tensor_right_hom, ← SymmetricCategory.braiding_swap_eq_inv_braiding]
        monoidal
    _ = 𝟙 _ ⊗≫ U ◁ ((β_ V E).hom ▷ D) ⊗≫
          (U ◁ ε_ V E ≫ (β_ U (𝟙_ C)).hom) ▷ D ⊗≫ (β_ U D).hom ≫ ε_ U D := by
        rw [braiding_naturality_right]
    _ = _ := by
        rw [braiding_tensorUnit_right]; monoidal

/-- Vanishing for a tensor product, along the tensor product of exact pairings. -/
theorem partialTrace_tensor {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] (U V D E : C) [ExactPairing U D] [ExactPairing V E] {X Y : C}
    (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :
    partialTrace (U ⊗ V) (E ⊗ D) f =
      partialTrace U D (partialTrace V E ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv)) := by
  calc partialTrace (U ⊗ V) (E ⊗ D) f
      = (ρ_ X).inv ≫ X ◁ η_ (U ⊗ V) (E ⊗ D) ⊗≫ f ▷ (E ⊗ D) ⊗≫
          Y ◁ ((β_ (U ⊗ V) (E ⊗ D)).hom ≫ ε_ (U ⊗ V) (E ⊗ D)) ≫ (ρ_ Y).hom := by
        simp only [partialTrace]; monoidal
    _ = _ := by
        rw [braiding_comp_tensor_evaluation, tensor_coevaluation]
        simp only [partialTrace]
        monoidal

end ExactPairing

namespace TracedCategory

open ExactPairing

/-- A right rigid symmetric category is traced by the partial trace along the right duals. -/
@[instance_reducible]
def ofRightRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] [RightRigidCategory C] : TracedCategory C where
  trace U _ _ f := partialTrace U Uᘁ f
  trace_whiskerRight_comp U _ _ _ g f := partialTrace_whiskerRight_comp U Uᘁ g f
  trace_comp_whiskerRight U _ _ _ f h := partialTrace_comp_whiskerRight U Uᘁ f h
  trace_whiskerLeft_comp g f := partialTrace_whiskerLeft_comp g f
  trace_tensorUnit f := by
    rw [partialTrace_congr (D' := 𝟙_ C)]
    exact partialTrace_tensorUnit f
  trace_tensor U V _ _ f := by
    rw [partialTrace_congr (D' := Vᘁ ⊗ Uᘁ)]
    exact partialTrace_tensor U V Uᘁ Vᘁ f
  whiskerLeft_trace W U _ _ f := whiskerLeft_partialTrace U Uᘁ W f
  trace_braiding U := partialTrace_braiding U Uᘁ

end TracedCategory

end CategoryTheory

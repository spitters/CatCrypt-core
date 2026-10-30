/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.Traced

/-!
# The Int construction

For a traced symmetric monoidal category `C`, the Int construction of Joyal, Street and Verity
is the category `IntConstruction C` whose objects are pairs `(X⁺, X⁻)` of objects of `C` and
whose morphisms `(X⁺, X⁻) ⟶ (Y⁺, Y⁻)` are morphisms `X⁺ ⊗ Y⁻ ⟶ Y⁺ ⊗ X⁻` of `C`. The identity
of `(X⁺, X⁻)` is the identity of `X⁺ ⊗ X⁻`, and the composite of `f` and `g` is the trace over
`Y⁻` of `f` and `g` placed in sequence.

The functor `C ⥤ IntConstruction C` sending `X` to `(X, 𝟙_ C)` is fully faithful.

## Main definitions

* `CategoryTheory.IntConstruction`: the objects of the Int construction.
* `CategoryTheory.IntConstruction.inclusion`: the functor `X ↦ (X, 𝟙_ C)`.

## Main results

* `CategoryTheory.IntConstruction.instCategory`: the Int construction is a category.
* `CategoryTheory.IntConstruction.inclusionFullyFaithful`: the inclusion is fully faithful.

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

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The symmetry exchanging the last two factors of `(X ⊗ U) ⊗ V`. -/
def swapRight (X U V : C) : (X ⊗ U) ⊗ V ⟶ (X ⊗ V) ⊗ U :=
  (α_ X U V).hom ≫ X ◁ (β_ U V).hom ≫ (α_ X V U).inv

/-- Exchanging the last two factors twice is the identity. -/
@[reassoc (attr := simp)]
theorem swapRight_swapRight (X U V : C) : swapRight X U V ≫ swapRight X V U = 𝟙 _ := by
  simp only [swapRight, assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry]
  simp

/-- Whiskering on the right by `x ⊗ y` is conjugate, by the symmetry, to whiskering by
`y ⊗ x`. -/
theorem whiskerRight_tensor_eq {P Q : C} (k : P ⟶ Q) (x y : C) :
    k ▷ (x ⊗ y) = P ◁ (β_ x y).hom ≫ k ▷ (y ⊗ x) ≫ Q ◁ (β_ y x).hom := by
  rw [whisker_exchange_assoc, ← whiskerLeft_comp, SymmetricCategory.symmetry, whiskerLeft_id,
    comp_id]

/-- The Yang–Baxter composite on `p ⊗ (q ⊗ r)` followed by the symmetry of `q` and `p`. -/
theorem yangBaxter_comp_braiding (p q r : C) :
    (α_ p q r).inv ≫ (β_ p q).hom ▷ r ≫ (α_ q p r).hom ≫ q ◁ (β_ p r).hom ≫
      (α_ q r p).inv ≫ (β_ q r).hom ▷ p ≫ (α_ r q p).hom ≫ r ◁ (β_ q p).hom =
    p ◁ (β_ q r).hom ≫ (α_ p r q).inv ≫ (β_ p r).hom ▷ q ≫ (α_ r p q).hom := by
  rw [yang_baxter_assoc]
  simp only [← whiskerLeft_comp, SymmetricCategory.symmetry, whiskerLeft_id, comp_id]

/-- The Yang–Baxter composite on `p ⊗ (q ⊗ r)`, conjugated by symmetries. -/
theorem braiding_comp_yangBaxter_comp_braiding (p q r : C) :
    p ◁ (β_ r q).hom ≫ (α_ p q r).inv ≫ (β_ p q).hom ▷ r ≫ (α_ q p r).hom ≫
      q ◁ (β_ p r).hom ≫ (α_ q r p).inv ≫ (β_ q r).hom ▷ p ≫ (α_ r q p).hom ≫
        r ◁ (β_ q p).hom =
    (α_ p r q).inv ≫ (β_ p r).hom ▷ q ≫ (α_ r p q).hom := by
  rw [yangBaxter_comp_braiding, ← whiskerLeft_comp_assoc, SymmetricCategory.symmetry,
    whiskerLeft_id, id_comp]

end IntConstruction

namespace TracedCategory

open IntConstruction (swapRight)

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [TracedCategory C]

/-- The trace over `U'` is the trace over `U` conjugated by an isomorphism `U ≅ U'`. -/
theorem trace_eq_trace_conj {U U' X Y : C} (e : U ≅ U') (f : X ⊗ U' ⟶ Y ⊗ U') :
    trace U' f = trace U (X ◁ e.hom ≫ f ≫ Y ◁ e.inv) := by
  rw [trace_whiskerLeft_comp]
  simp

/-- Tracing over `V` and then over `U` is tracing over `U ⊗ V`. -/
theorem trace_trace (U V : C) {X Y : C} (f : (X ⊗ U) ⊗ V ⟶ (Y ⊗ U) ⊗ V) :
    trace U (trace V f) = trace (U ⊗ V) ((α_ X U V).inv ≫ f ≫ (α_ Y U V).hom) := by
  rw [trace_tensor]
  simp

/-- Whiskering a trace on the right moves the whiskered object past the traced one. -/
theorem whiskerRight_trace (U W : C) {X Y : C} (f : X ⊗ U ⟶ Y ⊗ U) :
    trace U f ▷ W = trace U (swapRight X W U ≫ f ▷ W ≫ swapRight Y U W) := by
  have h : trace U f ▷ W = (β_ X W).hom ≫ W ◁ trace U f ≫ (β_ W Y).hom := by
    rw [← braiding_naturality_left_assoc, SymmetricCategory.symmetry, comp_id]
  rw [h, whiskerLeft_trace, ← trace_comp_whiskerRight, ← trace_whiskerRight_comp]
  congr 1
  have hf : W ◁ f = (β_ W (X ⊗ U)).hom ≫ f ▷ W ≫ (β_ (Y ⊗ U) W).hom := by
    rw [← braiding_naturality_right_assoc, SymmetricCategory.symmetry, comp_id]
  have hL : (β_ X W).hom ▷ U ≫ (α_ W X U).hom ≫ (β_ W (X ⊗ U)).hom = swapRight X W U := by
    rw [braiding_tensor_right_hom]
    simp only [swapRight, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight, id_comp]
  have hR : (β_ (Y ⊗ U) W).hom ≫ (α_ W Y U).inv ≫ (β_ W Y).hom ▷ U = swapRight Y U W := by
    rw [braiding_tensor_left_hom]
    simp only [swapRight, assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight, comp_id]
  rw [hf, ← hL, ← hR]
  simp only [assoc]

end TracedCategory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [TracedCategory C]

/-- The objects of the Int construction on `C`: pairs of a positive and a negative object. -/
structure IntConstruction where
  /-- The positive component. -/
  pos : C
  /-- The negative component. -/
  neg : C

namespace IntConstruction

open TracedCategory

variable {C}

/-- The morphisms `X ⟶ Y` of the Int construction: morphisms `X⁺ ⊗ Y⁻ ⟶ Y⁺ ⊗ X⁻` of `C`. -/
@[ext]
structure Hom (X Y : IntConstruction C) where
  /-- The underlying morphism of `C`. -/
  hom : X.pos ⊗ Y.neg ⟶ Y.pos ⊗ X.neg

/-- The trace of `swapRight X U U` over `U` is the identity. -/
@[simp]
theorem trace_swapRight (X U : C) : trace U (swapRight X U U) = 𝟙 (X ⊗ U) := by
  rw [swapRight, ← whiskerLeft_trace, trace_braiding, whiskerLeft_id]

/-- The morphism traced over `Y⁻` in the composite of `f : X ⟶ Y` and `g : Y ⟶ Z`. -/
def compKernel {X Y Z : IntConstruction C} (f : Hom X Y) (g : Hom Y Z) :
    (X.pos ⊗ Z.neg) ⊗ Y.neg ⟶ (Z.pos ⊗ X.neg) ⊗ Y.neg :=
  swapRight X.pos Z.neg Y.neg ≫ f.hom ▷ Z.neg ≫ swapRight Y.pos X.neg Z.neg ≫
    g.hom ▷ X.neg ≫ swapRight Z.pos Y.neg X.neg

instance : CategoryStruct (IntConstruction C) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨trace _ (compKernel f g)⟩

/-- Morphisms of the Int construction are equal when their underlying morphisms are. -/
@[ext]
theorem hom_ext {X Y : IntConstruction C} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- Unfolding lemma: the identity of `X` is the identity of `X⁺ ⊗ X⁻`. -/
@[simp]
theorem id_hom (X : IntConstruction C) : (𝟙 X : X ⟶ X).hom = 𝟙 _ := rfl

/-- Unfolding lemma: the composite is the trace over `Y⁻` of `compKernel`. -/
theorem comp_hom {X Y Z : IntConstruction C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = trace Y.neg (compKernel f g) := rfl

/-- The identity is a left unit for composition (by yanking). -/
theorem id_comp' {X Y : IntConstruction C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by
  ext
  simp only [comp_hom, compKernel, id_hom, id_whiskerRight, id_comp, swapRight_swapRight_assoc]
  rw [trace_whiskerRight_comp, trace_swapRight, comp_id]

/-- The identity is a right unit for composition (by yanking). -/
theorem comp_id' {X Y : IntConstruction C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by
  ext
  simp only [comp_hom, compKernel, id_hom, id_whiskerRight, id_comp, swapRight_swapRight,
    comp_id]
  rw [trace_comp_whiskerRight, trace_swapRight, id_comp]

/-- Associativity of composition in the Int construction, on underlying morphisms of `C`. -/
theorem assoc_aux {A a B b E c D d : C} (f : A ⊗ b ⟶ B ⊗ a) (g : B ⊗ c ⟶ E ⊗ b)
    (h : E ⊗ d ⟶ D ⊗ c) :
    trace c (swapRight A d c ≫
      trace b (swapRight A c b ≫ f ▷ c ≫ swapRight B a c ≫ g ▷ a ≫ swapRight E b a) ▷ d ≫
        swapRight E a d ≫ h ▷ a ≫ swapRight D c a) =
    trace b (swapRight A d b ≫ f ▷ d ≫ swapRight B a d ≫
      trace c (swapRight B d c ≫ g ▷ d ≫ swapRight E b d ≫ h ▷ b ≫ swapRight D c b) ▷ a ≫
        swapRight D b a) := by
  rw [whiskerRight_trace, whiskerRight_trace]
  simp only [← trace_whiskerRight_comp, ← trace_comp_whiskerRight]
  rw [trace_trace, trace_trace, trace_eq_trace_conj (β_ c b)]
  congr 1
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  calc _ = 𝟙 ((A ⊗ d) ⊗ (c ⊗ b)) ⊗≫
          A ◁ ((α_ d c b).inv ≫ (β_ d c).hom ▷ b ≫ (α_ c d b).hom ≫
            c ◁ (β_ d b).hom ≫ (α_ c b d).inv ≫ (β_ c b).hom ▷ d ≫ (α_ b c d).hom) ⊗≫
          f ▷ (c ⊗ d) ⊗≫ B ◁ ((β_ a c).hom ▷ d) ⊗≫ g ▷ (a ⊗ d) ⊗≫
          E ◁ ((α_ b a d).inv ≫ (β_ b a).hom ▷ d ≫ (α_ a b d).hom ≫ a ◁ (β_ b d).hom ≫
            (α_ a d b).inv ≫ (β_ a d).hom ▷ b ≫ (α_ d a b).hom) ⊗≫
          h ▷ (a ⊗ b) ⊗≫ D ◁ ((β_ c a).hom ▷ b) ⊗≫ 𝟙 ((D ⊗ a) ⊗ (c ⊗ b)) := by
        simp only [swapRight]; monoidal
    _ = 𝟙 ((A ⊗ d) ⊗ (c ⊗ b)) ⊗≫
          A ◁ ((α_ d c b).inv ≫ (β_ d c).hom ▷ b ≫ (α_ c d b).hom ≫
            c ◁ (β_ d b).hom ≫ (α_ c b d).inv ≫ (β_ c b).hom ▷ d ≫ (α_ b c d).hom ≫
            b ◁ (β_ c d).hom) ⊗≫
          f ▷ (d ⊗ c) ⊗≫
          B ◁ (a ◁ (β_ d c).hom ≫ (α_ a c d).inv ≫ (β_ a c).hom ▷ d ≫ (α_ c a d).hom ≫
            c ◁ (β_ a d).hom) ⊗≫
          g ▷ (d ⊗ a) ⊗≫
          E ◁ (b ◁ (β_ d a).hom ≫ (α_ b a d).inv ≫ (β_ b a).hom ▷ d ≫ (α_ a b d).hom ≫
            a ◁ (β_ b d).hom ≫ (α_ a d b).inv ≫ (β_ a d).hom ▷ b ≫ (α_ d a b).hom ≫
            d ◁ (β_ a b).hom) ⊗≫
          h ▷ (b ⊗ a) ⊗≫
          D ◁ (c ◁ (β_ b a).hom ≫ (α_ c a b).inv ≫ (β_ c a).hom ▷ b ≫ (α_ a c b).hom) ⊗≫
          𝟙 ((D ⊗ a) ⊗ (c ⊗ b)) := by
        rw [whiskerRight_tensor_eq f c d, whiskerRight_tensor_eq g a d,
          whiskerRight_tensor_eq h a b]
        monoidal
    _ = 𝟙 ((A ⊗ d) ⊗ (c ⊗ b)) ⊗≫
          A ◁ (d ◁ (β_ c b).hom ≫ (α_ d b c).inv ≫ (β_ d b).hom ▷ c ≫ (α_ b d c).hom) ⊗≫
          f ▷ (d ⊗ c) ⊗≫
          B ◁ ((α_ a d c).inv ≫ (β_ a d).hom ▷ c ≫ (α_ d a c).hom ≫ d ◁ (β_ a c).hom ≫
            (α_ d c a).inv ≫ (β_ d c).hom ▷ a ≫ (α_ c d a).hom) ⊗≫
          g ▷ (d ⊗ a) ⊗≫
          E ◁ ((α_ b d a).inv ≫ (β_ b d).hom ▷ a ≫ (α_ d b a).hom) ⊗≫
          h ▷ (b ⊗ a) ⊗≫
          D ◁ ((α_ c b a).inv ≫ (β_ c b).hom ▷ a ≫ (α_ b c a).hom ≫ b ◁ (β_ c a).hom ≫
            (α_ b a c).inv ≫ (β_ b a).hom ▷ c ≫ (α_ a b c).hom ≫ a ◁ (β_ b c).hom) ⊗≫
          𝟙 ((D ⊗ a) ⊗ (c ⊗ b)) := by
        rw [yangBaxter_comp_braiding d c b, ← yang_baxter a d c,
          braiding_comp_yangBaxter_comp_braiding b a d, ← yangBaxter_comp_braiding c b a]
    _ = _ := by
        simp only [swapRight]; monoidal

/-- Composition in the Int construction is associative. -/
theorem assoc' {W X Y Z : IntConstruction C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := by
  ext
  exact assoc_aux f.hom g.hom h.hom

instance instCategory : Category (IntConstruction C) where
  id_comp := id_comp'
  comp_id := comp_id'
  assoc := assoc'

variable (C)

/-- The inclusion of `C` in its Int construction, `X ↦ (X, 𝟙_ C)`. -/
def inclusion : C ⥤ IntConstruction C where
  obj X := ⟨X, 𝟙_ C⟩
  map f := ⟨f ▷ 𝟙_ C⟩
  map_id X := by ext; simp
  map_comp f g := by
    ext
    simp only [comp_hom, compKernel, trace_tensorUnit, swapRight, braiding_tensorUnit_left]
    monoidal

/-- The inclusion of `C` in its Int construction is fully faithful. -/
def inclusionFullyFaithful : (inclusion C).FullyFaithful where
  preimage {X Y} f := (ρ_ X).inv ≫ (f.hom : X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C) ≫ (ρ_ Y).hom
  map_preimage {X Y} f := by
    ext
    change ((ρ_ X).inv ≫ (f.hom : X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C) ≫ (ρ_ Y).hom) ▷ 𝟙_ C = f.hom
    simp only [whiskerRight_id, assoc, Iso.hom_inv_id_assoc]
    erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  preimage_map f := by simp [inclusion]

instance : (inclusion C).Full := (inclusionFullyFaithful C).full

instance : (inclusion C).Faithful := (inclusionFullyFaithful C).faithful

end IntConstruction

end CategoryTheory

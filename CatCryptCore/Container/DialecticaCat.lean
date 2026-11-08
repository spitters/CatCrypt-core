/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNBang
public import CatCryptCore.Container.CwFPi
public import PolyFun.PFunctor.InternalHom
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monad.Basic

/-!
# The Dialectica category of dependent lenses

The parallel product `⊗` of polynomial functors is closed: the internal hom `ihom q r` has the
lenses `q ⇆ r` as shapes (Niu–Spivak, Ex. 4.78), and `Lens.curryEquiv` is the adjunction. This
module makes `TensorCat.{u, u}` a monoidal closed category with it.

An object of the Dialectica category `DialObj` is a polynomial functor with a predicate on its
positions, and a morphism is a lens satisfying de Paiva's condition `LensSound`: a position of the
target that holds at the image shape is pulled back to a position of the source that holds
(de Paiva, *A Dialectica-like model of linear logic*, CTCS 1989; *The Dialectica categories*,
Tech. Rep. UCAM-CL-TR-213, 1991), here on dependent lenses. The tensor has the conjunction as its
predicate and the internal hom has the Gödel clause of implication; the category is symmetric
monoidal closed, and the forgetful functor to `TensorCat` has the right adjoint that gives every
position the true predicate.

The multiset exponential `bang` lifts to `DialObj.bang`, whose predicate holds at a multiset when
it holds at every element; it is a comonad on `DialObj`. A Diller–Nahm morphism satisfying
equation (9) of Moss and von Glehn (`DNSound`) is a morphism of `DialObj` out of `DialObj.bang`
(`dnSound_iff_lensSound`, `DialObj.dnHomEquiv`), so the Diller–Nahm category with predicates is
the co-Kleisli category of `DialObj.bang` (Hofstra, *The Dialectica monad and its cousins*, CRM
Proc. Lecture Notes 53, 2011). The Seely isomorphism `DialObj.seely` and the closed structure give
the cartesian closure of the Diller–Nahm category, `dnCurry`, with `[!Y, Z]` as exponential.

## Main definitions

* `TensorCat.instMonoidalClosed` — the monoidal closed structure of the parallel product;
* `LensSound`, `DialObj`, `DialHom` — de Paiva's condition, objects and morphisms;
* `DialObj.tensor`, `DialObj.unit`, `DialObj.ihom` — tensor, unit and internal hom;
* `DialObj.curryRight` — `(X ⊗ Y ⟶ Z) ≃ (X ⟶ DialObj.ihom Y Z)`;
* `DialObj.forget`, `DialObj.forgetMonoidal`, `DialObj.top`, `DialObj.forgetTopAdj` — the
  forgetful functor, strict monoidal, and its right adjoint;
* `DialObj.bang`, `DialObj.bangComonad` — the exponential on predicates and its comonad;
* `DialObj.dnHomEquiv` — sound Diller–Nahm morphisms as morphisms out of the exponential;
* `DialObj.prod`, `DialObj.seely` — the product with predicates and the Seely isomorphism;
* `DialObj.arrow`, `dnCurry` — the exponential of the Diller–Nahm category and its currying
  bijection.

## Main results

* the instances `MonoidalCategory`, `SymmetricCategory`, `MonoidalClosed` on `DialObj`;
* `dnSound_iff_lensSound` — equation (9) is de Paiva's condition on the co-Kleisli lens.

## References

* V. de Paiva, *A Dialectica-like model of linear logic*, CTCS 1989, LNCS 389, 341–356.
* V. de Paiva, *The Dialectica categories*, Tech. Rep. UCAM-CL-TR-213, Cambridge, 1991.
* P. Hofstra, *The Dialectica monad and its cousins*, CRM Proc. Lecture Notes 53, 2011.
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018, §8.
* N. Niu, D. Spivak, *Polynomial functors: a mathematical theory of interaction*, Ex. 4.78.

Search words: Dialectica category, de Paiva, Gödel clause, linear logic, symmetric monoidal
closed, internal hom, parallel product, tensor, exponential, of-course modality, comonad,
co-Kleisli, Diller–Nahm, Seely isomorphism, cartesian closed, currying, lens, predicate,
polynomial functor.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container

open PFunctor CategoryTheory MonoidalCategory
open CwF (Pred DNSound)

/-! ## The monoidal closed structure of the parallel product -/

namespace TensorCat

/-- Currying on the right in `TensorCat`: `(P ⊗ Q ⟶ R) ≃ (P ⟶ ihom Q R)`. -/
def curryRight (P Q R : PFunctor.TensorCat.{u, u}) :
    (P ⊗ Q ⟶ R) ≃ (P ⟶ TensorCat.of (ihom Q.toPFunctor R.toPFunctor)) :=
  Lens.curryEquiv

/-- The hom-set bijection of the tensor–hom adjunction for `tensorLeft P`. -/
def curryLeft (P Q R : PFunctor.TensorCat.{u, u}) :
    (P ⊗ Q ⟶ R) ≃ (Q ⟶ TensorCat.of (ihom P.toPFunctor R.toPFunctor)) :=
  ((β_ P Q).homCongr (Iso.refl R)).trans (curryRight Q P R)

/-- The parallel product of polynomial functors is monoidal closed, with `ihom` as internal hom. -/
instance instMonoidalClosed : MonoidalClosed PFunctor.TensorCat.{u, u} where
  closed P :=
    { rightAdj := Adjunction.rightAdjointOfEquiv (G_obj := fun R =>
          TensorCat.of (ihom P.toPFunctor R.toPFunctor)) (curryLeft P) (fun _ _ _ _ _ => rfl)
      adj := Adjunction.adjunctionOfEquivRight _ _ }

end TensorCat

/-! ## Objects and morphisms -/

/-- de Paiva's condition on a lens: a position of the target that satisfies `β` at the image shape
is pulled back to a position of the source that satisfies `α`. -/
def LensSound {P Q : PFunctor.{u, u}} (α : Pred P) (β : Pred Q) (l : Lens P Q) : Prop :=
  ∀ a y, α a (l.toFunB a y) → β (l.toFunA a) y

/-- An object of the Dialectica category of lenses: a polynomial functor with a predicate on its
positions. -/
structure DialObj : Type (u + 1) where
  /-- The polynomial functor. -/
  P : PFunctor.{u, u}
  /-- The predicate on its positions. -/
  rel : Pred P

/-- A morphism of the Dialectica category: a lens satisfying de Paiva's condition. -/
@[ext]
structure DialHom (X Y : DialObj.{u}) where
  /-- The underlying lens. -/
  lens : Lens X.P Y.P
  /-- de Paiva's condition. -/
  sound : LensSound X.rel Y.rel lens

namespace DialObj

instance instCategory : Category DialObj.{u} where
  Hom := DialHom
  id X := ⟨Lens.id X.P, fun _ _ h => h⟩
  comp f g := ⟨Lens.comp g.lens f.lens, fun a z h => g.sound _ z (f.sound a _ h)⟩

/-- Morphisms of `DialObj` with equal lenses are equal. -/
@[ext]
theorem hom_ext {X Y : DialObj.{u}} {f g : X ⟶ Y} (h : f.lens = g.lens) : f = g :=
  DialHom.ext h

/-- The lens of an identity. -/
@[simp]
theorem id_lens (X : DialObj.{u}) : DialHom.lens (𝟙 X) = Lens.id X.P := rfl

/-- The lens of a composite. -/
@[simp]
theorem comp_lens {X Y Z : DialObj.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    DialHom.lens (f ≫ g) = Lens.comp g.lens f.lens := rfl

/-! ## The symmetric monoidal structure -/

/-- The tensor: the parallel product with the conjunction of the predicates. -/
def tensor (X Y : DialObj.{u}) : DialObj.{u} :=
  ⟨X.P ⊗ Y.P, fun ab xy => X.rel ab.1 xy.1 ∧ Y.rel ab.2 xy.2⟩

/-- The unit: `y` with the true predicate. -/
def unit : DialObj.{u} := ⟨y, fun _ _ => True⟩

/-- The tensor of two morphisms. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : DialObj.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensor X₁ X₂ ⟶ tensor Y₁ Y₂ :=
  ⟨f.lens ⊗ₗ g.lens, fun _ _ h => ⟨f.sound _ _ h.1, g.sound _ _ h.2⟩⟩

/-- The associator. -/
def associator (X Y Z : DialObj.{u}) : tensor (tensor X Y) Z ≅ tensor X (tensor Y Z) where
  hom := ⟨Lens.Equiv.tensorAssoc.toLens, fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩⟩
  inv := ⟨Lens.Equiv.tensorAssoc.invLens, fun _ _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- The left unitor. -/
def leftUnitor (X : DialObj.{u}) : tensor unit X ≅ X where
  hom := ⟨Lens.Equiv.yTensor.toLens, fun _ _ h => h.2⟩
  inv := ⟨Lens.Equiv.yTensor.invLens, fun _ _ h => ⟨trivial, h⟩⟩

/-- The right unitor. -/
def rightUnitor (X : DialObj.{u}) : tensor X unit ≅ X where
  hom := ⟨Lens.Equiv.tensorY.toLens, fun _ _ h => h.1⟩
  inv := ⟨Lens.Equiv.tensorY.invLens, fun _ _ h => ⟨h, trivial⟩⟩

instance instMonoidalCategoryStruct : MonoidalCategoryStruct DialObj.{u} where
  tensorObj := tensor
  whiskerLeft X _ _ g := tensorHom (𝟙 X) g
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := unit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/-- The Dialectica category is monoidal for the tensor. -/
instance instMonoidalCategory : MonoidalCategory DialObj.{u} :=
  .ofTensorHom
    (id_tensorHom_id := fun _ _ => hom_ext rfl)
    (id_tensorHom := fun _ _ _ _ => hom_ext rfl)
    (tensorHom_id := fun _ _ => hom_ext rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => hom_ext rfl)
    (associator_naturality := fun _ _ _ => hom_ext rfl)
    (leftUnitor_naturality := fun _ => hom_ext rfl)
    (rightUnitor_naturality := fun _ => hom_ext rfl)
    (pentagon := fun _ _ _ _ => hom_ext rfl)
    (triangle := fun _ _ => hom_ext rfl)

/-- The braiding. -/
def braiding (X Y : DialObj.{u}) : X ⊗ Y ≅ Y ⊗ X where
  hom := ⟨(Lens.Equiv.tensorComm X.P Y.P).toLens, fun _ _ h => ⟨h.2, h.1⟩⟩
  inv := ⟨(Lens.Equiv.tensorComm Y.P X.P).toLens, fun _ _ h => ⟨h.2, h.1⟩⟩

/-- The Dialectica category is symmetric monoidal. -/
instance instSymmetricCategory : SymmetricCategory DialObj.{u} where
  braiding := braiding
  braiding_naturality_right _ _ _ _ := hom_ext rfl
  braiding_naturality_left _ _ := hom_ext rfl
  hexagon_forward _ _ _ := hom_ext rfl
  hexagon_reverse _ _ _ := hom_ext rfl
  symmetry _ _ := hom_ext rfl

/-! ## The internal hom -/

/-- The internal hom: the lenses `X.P ⇆ Y.P` as shapes, with the Gödel clause of implication as
predicate at a lens `l` and a position `⟨j, z⟩`. -/
def ihom (X Y : DialObj.{u}) : DialObj.{u} :=
  ⟨PFunctor.ihom X.P Y.P, fun l jz => X.rel jz.1 (l.toFunB jz.1 jz.2) → Y.rel (l.toFunA jz.1) jz.2⟩

/-- Currying on the right: `(X ⊗ Y ⟶ Z) ≃ (X ⟶ ihom Y Z)`. -/
def curryRight (X Y Z : DialObj.{u}) : (X ⊗ Y ⟶ Z) ≃ (X ⟶ ihom Y Z) where
  toFun φ := ⟨Lens.curry φ.lens, fun _ _ hx hy => φ.sound _ _ ⟨hx, hy⟩⟩
  invFun ψ := ⟨Lens.uncurry ψ.lens, fun _ _ h => ψ.sound _ _ h.1 h.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The hom-set bijection of the tensor–hom adjunction for `tensorLeft X`. -/
def curryLeft (X Y Z : DialObj.{u}) : (X ⊗ Y ⟶ Z) ≃ (Y ⟶ ihom X Z) :=
  ((β_ X Y).homCongr (Iso.refl Z)).trans (curryRight Y X Z)

/-- The Dialectica category is monoidal closed, with `DialObj.ihom` as internal hom. -/
instance instMonoidalClosed : MonoidalClosed DialObj.{u} where
  closed X :=
    { rightAdj := Adjunction.rightAdjointOfEquiv (G_obj := ihom X) (curryLeft X)
          (fun _ _ _ _ _ => hom_ext rfl)
      adj := Adjunction.adjunctionOfEquivRight _ _ }

/-! ## The forgetful functor and the true predicate -/

/-- The forgetful functor to lenses. -/
def forget : DialObj.{u} ⥤ PFunctor.TensorCat.{u, u} where
  obj X := TensorCat.of X.P
  map f := f.lens

/-- The forgetful functor is strict monoidal: its structure isomorphisms are identities. -/
def forgetCoreMonoidal : forget.{u}.CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left _ _ := rfl
  μIso_hom_natural_right _ _ := rfl
  associativity _ _ _ := rfl
  left_unitality _ := rfl
  right_unitality _ := rfl

/-- The forgetful functor as a monoidal functor. -/
instance forgetMonoidal : forget.{u}.Monoidal := forgetCoreMonoidal.toMonoidal

/-- A polynomial functor with the true predicate. -/
def top : PFunctor.TensorCat.{u, u} ⥤ DialObj.{u} where
  obj P := ⟨P.toPFunctor, fun _ _ => True⟩
  map l := ⟨l, fun _ _ _ => trivial⟩

/-- The forgetful functor is left adjoint to the true predicate: every lens into a polynomial
functor with the true predicate is sound. -/
def forgetTopAdj : forget.{u} ⊣ top.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X P :=
        { toFun f := ⟨f, fun _ _ _ => trivial⟩
          invFun g := g.lens
          left_inv _ := rfl
          right_inv _ := rfl } }

/-! ## The exponential -/

/-- The exponential on predicates: a multiset of positions holds when every element holds
(Diller–Nahm). -/
def bang (X : DialObj.{u}) : DialObj.{u} := ⟨Container.bang X.P, fun a m => ∀ x ∈ m, X.rel a x⟩

/-- The exponential as an endofunctor of the Dialectica category. -/
def bangFunctor : DialObj.{u} ⥤ DialObj.{u} where
  obj := bang
  map f := ⟨bangMap f.lens, fun a _ h y hy =>
    f.sound a y (h _ (Multiset.mem_map_of_mem _ hy))⟩
  map_id _ := hom_ext bangMap_id
  map_comp f g := hom_ext (bangMap_comp g.lens f.lens)

/-- The exponential as a comonad on the Dialectica category. -/
def bangComonad : Comonad DialObj.{u} where
  toFunctor := bangFunctor
  ε := { app X := ⟨bangCounit X.P, fun _ y h => h y (Multiset.mem_singleton_self y)⟩
         naturality _ _ f := hom_ext (bangCounit_natural f.lens) }
  δ := { app X := ⟨bangComult X.P, fun _ _ h s hs x hx => h x (Multiset.mem_join.2 ⟨s, hs, hx⟩)⟩
         naturality _ _ f := hom_ext (bangComult_natural f.lens) }
  coassoc X := hom_ext (bangComult_coassoc X.P).symm
  left_counit X := hom_ext (bangCounit_comult X.P)
  right_counit X := hom_ext (bangMap_counit_comult X.P)

end DialObj

/-- **Equation (9) of Moss and von Glehn is de Paiva's condition on the co-Kleisli lens.** -/
theorem dnSound_iff_lensSound {P Q : PFunctor.{u, u}} {α : Pred P} {β : Pred Q}
    (g : DNLens P Q) : DNSound α β g ↔ LensSound (DialObj.bang ⟨P, α⟩).rel β g.toBangLens :=
  Iff.rfl

namespace DialObj

/-- The sound Diller–Nahm morphisms `X → Z` are the morphisms `bang X ⟶ Z` of the Dialectica
category: the hom-sets of its co-Kleisli category. -/
def dnHomEquiv (X Z : DialObj.{u}) :
    {g : DNLens X.P Z.P // DNSound X.rel Z.rel g} ≃ (bang X ⟶ Z) where
  toFun g := ⟨g.1.toBangLens, (dnSound_iff_lensSound g.1).1 g.2⟩
  invFun f := ⟨DNLens.ofBangLens f.lens, f.sound⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The product with predicates: positions are a sum, and the predicate is the case split. -/
def prod (X Y : DialObj.{u}) : DialObj.{u} :=
  ⟨X.P.prod Y.P, fun ab => Sum.elim (X.rel ab.1) (Y.rel ab.2)⟩

/-- **The Seely isomorphism with predicates**: the exponential of a product is the tensor of the
exponentials. -/
def seely (X Y : DialObj.{u}) : bang (prod X Y) ≅ bang X ⊗ bang Y where
  hom := ⟨(Container.seely X.P Y.P).toLens, fun _ _ h =>
    ⟨fun x hx => h (Sum.inl x) (Multiset.inl_mem_disjSum.2 hx),
      fun x hx => h (Sum.inr x) (Multiset.inr_mem_disjSum.2 hx)⟩⟩
  inv := ⟨(Container.seely X.P Y.P).invLens, fun _ _ h s hs => by
    cases s with
    | inl x => exact h.1 x ((Multiset.mem_filterMap _ _).2 ⟨Sum.inl x, hs, rfl⟩)
    | inr x => exact h.2 x ((Multiset.mem_filterMap _ _).2 ⟨Sum.inr x, hs, rfl⟩)⟩
  hom_inv_id := hom_ext (Container.seely X.P Y.P).left_inv
  inv_hom_id := hom_ext (Container.seely X.P Y.P).right_inv

/-- The exponential object of the Diller–Nahm category: `[!X, Y]`. -/
def arrow (X Y : DialObj.{u}) : DialObj.{u} := ihom (bang X) Y

end DialObj

/-- **The Diller–Nahm category is cartesian closed**: a sound Diller–Nahm morphism out of a product
is a sound Diller–Nahm morphism into the exponential `DialObj.arrow`. -/
def dnCurry (X Y Z : DialObj.{u}) :
    {g : DNLens (X.prod Y).P Z.P // DNSound (X.prod Y).rel Z.rel g} ≃
      {g : DNLens X.P (DialObj.arrow Y Z).P // DNSound X.rel (DialObj.arrow Y Z).rel g} :=
  (DialObj.dnHomEquiv (X.prod Y) Z).trans <|
    ((DialObj.seely X Y).homCongr (Iso.refl Z)).trans <|
      (DialObj.curryRight (DialObj.bang X) (DialObj.bang Y) Z).trans
        (DialObj.dnHomEquiv X (DialObj.arrow Y Z)).symm

end CatCrypt.Container

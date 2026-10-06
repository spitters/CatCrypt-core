/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# The covariant Grothendieck construction gives a cofibered category

For a functor `F : C ⥤ Cat`, the forgetful functor `Grothendieck.forget F : Grothendieck F ⥤ C`
is a Grothendieck opfibration: for `x : Grothendieck F` and `t : x.base ⟶ c`, the morphism
`x.toTransport t : x ⟶ x.transport t`, whose base component is `t` and whose fibre component is
the identity, is strongly co-Cartesian over `t`.

This is the covariant twin of the statement that the contravariant Grothendieck construction of
a pseudofunctor is a fibered category, `CategoryTheory.Pseudofunctor.CoGrothendieck.forget`
in `Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean`.

## Main definitions

- `Functor.IsPreCofibered p`: every morphism in the base whose source has a lift has a
  co-Cartesian lift. It mirrors `Functor.IsPreFibered`.
- `Functor.IsCofibered p`: `p` is precofibered and co-Cartesian morphisms are closed under
  composition. It mirrors `Functor.IsFibered`.
- `Grothendieck.transportDesc`: the morphism `x.transport t ⟶ z` over `g` induced by a
  morphism `φ : x ⟶ z` over `t ≫ g`.

## Main statements

- `Functor.IsCofibered.of_exists_isStronglyCocartesian`: a functor that admits strongly
  co-Cartesian lifts is cofibered.
- `Grothendieck.isStronglyCocartesian_toTransport`: `x.toTransport t` is strongly co-Cartesian
  over `t` for `Grothendieck.forget F`.
- `Grothendieck.forget F` is cofibered.

## Mathlib placement

The classes `Functor.IsPreCofibered` and `Functor.IsCofibered` and the constructor
`Functor.IsCofibered.of_exists_isStronglyCocartesian` belong in a new file
`Mathlib/CategoryTheory/FiberedCategory/Cofibered.lean`, adapted from
`Mathlib/CategoryTheory/FiberedCategory/Fibered.lean`. The statements about `Grothendieck F`
belong beside `Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean`, which treats the
contravariant construction.
-/

@[expose] public section

set_option autoImplicit false

universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory.Functor Category IsHomLift

section Cofibered

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- A functor `p : 𝒳 ⥤ 𝒮` is precofibered if every morphism `f : p.obj a ⟶ S` in the base has a
co-Cartesian lift with domain `a`. -/
class Functor.IsPreCofibered (p : 𝒳 ⥤ 𝒮) : Prop where
  exists_isCocartesian' {a : 𝒳} {S : 𝒮} (f : p.obj a ⟶ S) :
    ∃ (b : 𝒳) (φ : a ⟶ b), IsCocartesian p f φ

protected lemma IsPreCofibered.exists_isCocartesian (p : 𝒳 ⥤ 𝒮) [p.IsPreCofibered] {a : 𝒳}
    {R S : 𝒮} (ha : p.obj a = R) (f : R ⟶ S) : ∃ (b : 𝒳) (φ : a ⟶ b), IsCocartesian p f φ := by
  subst ha; exact IsPreCofibered.exists_isCocartesian' f

/-- A functor `p : 𝒳 ⥤ 𝒮` is cofibered (a Grothendieck opfibration) if it is precofibered and
the composition of any two co-Cartesian morphisms is co-Cartesian. -/
class Functor.IsCofibered (p : 𝒳 ⥤ 𝒮) : Prop extends IsPreCofibered p where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCocartesian p f φ] [IsCocartesian p g ψ] : IsCocartesian p (f ≫ g) (φ ≫ ψ)

instance (p : 𝒳 ⥤ 𝒮) [p.IsCofibered] {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳}
    (φ : a ⟶ b) (ψ : b ⟶ c) [IsCocartesian p f φ] [IsCocartesian p g ψ] :
    IsCocartesian p (f ≫ g) (φ ≫ ψ) :=
  IsCofibered.comp f g φ ψ

namespace Functor.IsCofibered

/-- In a category which admits strongly co-Cartesian lifts, any co-Cartesian morphism is
strongly co-Cartesian. -/
lemma isStronglyCocartesian_of_exists_isCocartesian (p : 𝒳 ⥤ 𝒮) (h : ∀ (a : 𝒳) (S : 𝒮)
    (f : p.obj a ⟶ S), ∃ (b : 𝒳) (φ : a ⟶ b), IsStronglyCocartesian p f φ) {R S : 𝒮} (f : R ⟶ S)
    {a b : 𝒳} (φ : a ⟶ b) [p.IsCocartesian f φ] : p.IsStronglyCocartesian f φ := by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  -- Let `ψ` be a strongly co-Cartesian arrow lying over `p.map φ`
  obtain ⟨b', ψ, hψ⟩ := h _ _ (p.map φ)
  -- Let `τ' : b' ⟶ c` be the map induced by the universal property of `ψ`
  let τ' := IsStronglyCocartesian.map p (p.map φ) ψ (f' := p.map φ ≫ g) rfl φ'
  -- Let `σ` and `σ'` be the mutually inverse comparison maps between the codomains of `φ`, `ψ`
  let σ := IsCocartesian.map p (p.map φ) φ ψ
  let σ' := IsCocartesian.map p (p.map φ) ψ φ
  have hσ : σ ≫ σ' = 𝟙 _ := (IsCocartesian.codomainUniqueUpToIso p (p.map φ) φ ψ).hom_inv_id
  refine ⟨σ ≫ τ', ⟨inferInstance, ?_⟩, ?_⟩
  · simp [σ, τ', IsCocartesian.fac_assoc, IsStronglyCocartesian.fac]
  -- Uniqueness follows from the universal property of `ψ`
  intro π ⟨hπ, hπ_comp⟩
  have : σ' ≫ π = τ' := by
    apply IsStronglyCocartesian.map_uniq p (p.map φ) ψ rfl φ'
    simp [σ', IsCocartesian.fac_assoc, hπ_comp]
  rw [← this, ← assoc, hσ, id_comp]

/-- Alternate constructor for `IsCofibered`: a functor `p : 𝒳 ⥤ 𝒮` is cofibered if any diagram
of the form
```
 a
 -
 |
 v
p(a) --f--> S
```
admits a strongly co-Cartesian lift `a ⟶ b` of `f`. -/
lemma of_exists_isStronglyCocartesian {p : 𝒳 ⥤ 𝒮}
    (h : ∀ (a : 𝒳) (S : 𝒮) (f : p.obj a ⟶ S),
      ∃ (b : 𝒳) (φ : a ⟶ b), IsStronglyCocartesian p f φ) :
    IsCofibered p where
  exists_isCocartesian' := by
    intro a S f
    obtain ⟨b, φ, hφ⟩ := h a S f
    exact ⟨b, φ, inferInstance⟩
  comp := fun R S T f g {a b c} φ ψ _ _ =>
    have : p.IsStronglyCocartesian f φ := isStronglyCocartesian_of_exists_isCocartesian p h _ _
    have : p.IsStronglyCocartesian g ψ := isStronglyCocartesian_of_exists_isCocartesian p h _ _
    inferInstance

end Functor.IsCofibered

end Cofibered

namespace Grothendieck

variable {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Cat.{w, w'}}

section

variable (x : Grothendieck F) {c : C} (t : x.base ⟶ c)

instance isHomLift_toTransport : IsHomLift (forget F) t (x.toTransport t) :=
  IsHomLift.map (forget F) (x.toTransport t)

variable {z : Grothendieck F} (g : c ⟶ z.base) (φ : x ⟶ z) (h : φ.base = t ≫ g)

/-- Given a morphism `φ : x ⟶ z` whose base component factors as `t ≫ g`, the morphism
`x.transport t ⟶ z` with base component `g` and fibre component `φ.fiber`, transported along
`F.map (t ≫ g) = F.map t ≫ F.map g`. -/
def transportDesc : x.transport t ⟶ z where
  base := g
  fiber := eqToHom (by rw [h, F.map_comp]; rfl) ≫ φ.fiber

@[simp]
lemma transportDesc_base : (x.transportDesc t g φ h).base = g := rfl

instance isHomLift_transportDesc : IsHomLift (forget F) g (x.transportDesc t g φ h) :=
  IsHomLift.map (forget F) (x.transportDesc t g φ h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toTransport_comp_transportDesc : x.toTransport t ≫ x.transportDesc t g φ h = φ :=
  Grothendieck.ext _ _ (by simp [h]) (by simp [transportDesc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism out of `x.transport t` is determined by its base component and its composition
with `x.toTransport t`. -/
lemma transportDesc_toTransport_comp (χ : x.transport t ⟶ z) :
    x.transportDesc t χ.base (x.toTransport t ≫ χ) rfl = χ :=
  Grothendieck.ext _ _ rfl (by simp [transportDesc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism `x.toTransport t`, with base component `t` and identity fibre component, is
strongly co-Cartesian over `t`. -/
instance isStronglyCocartesian_toTransport :
    IsStronglyCocartesian (forget F) t (x.toTransport t) where
  universal_property' {z} g φ' _ := by
    have hφ' : φ'.base = t ≫ g := by simpa using IsHomLift.fac' (forget F) (t ≫ g) φ'
    refine ⟨x.transportDesc t g φ' hφ', ⟨inferInstance, by simp⟩, ?_⟩
    rintro χ ⟨hχ, rfl⟩
    obtain rfl : g = χ.base := by simpa using IsHomLift.fac (forget F) g χ
    exact (x.transportDesc_toTransport_comp t χ).symm

/-- The morphism `x.toTransport t` is co-Cartesian over `t`. -/
lemma isCocartesian_toTransport : IsCocartesian (forget F) t (x.toTransport t) :=
  inferInstance

end

/-- `forget F : Grothendieck F ⥤ C` is a cofibered category. -/
instance : IsCofibered (forget F) :=
  IsCofibered.of_exists_isStronglyCocartesian fun a _ f ↦
    ⟨a.transport f, a.toTransport f, isStronglyCocartesian_toTransport a f⟩

end Grothendieck

end CategoryTheory

/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Category.Cocartesian

/-!
# Affine Monoidal Categories

An affine monoidal category has a natural "discard" morphism `del X : X ⟶ 𝟙_ C`
for every object, satisfying naturality (`f ≫ del Y = del X`). This is the dual
notion to having a "copy" morphism; in a cocartesian setting it means every
computation can be discarded.

## Main definitions

* `AffineMonoidalCategory` — abstract class with `del` morphism
* `KlSPComp` instance — discard by mapping to `SDistr.fail`

## Duality

* Every `SemiCartesianMonoidalCategory` is affine (via `toUnit`)
* Every `SemiCocartesianMonoidalCategory` has a dual "co-affine" structure (`fromUnit`)
-/

namespace CategoryTheory

open MonoidalCategory

universe u v

variable (C : Type u) [Category.{v} C]

/-- An affine monoidal category has a natural discard morphism `del X : X ⟶ 𝟙_ C`
    for every object. Naturality means `f ≫ del Y = del X`. -/
class AffineMonoidalCategory [MonoidalCategory C] where
  /-- The discard morphism. -/
  del (X : C) : X ⟶ 𝟙_ C
  /-- Discarding the unit is the identity. -/
  del_unit : del (𝟙_ C) = 𝟙 (𝟙_ C)
  /-- Discard is natural: composing with any morphism then discarding equals discarding directly. -/
  del_naturality : ∀ {X Y : C} (f : X ⟶ Y), f ≫ del Y = del X

namespace AffineMonoidalCategory

variable {C} [MonoidalCategory C] [AffineMonoidalCategory C]

@[reassoc (attr := simp)]
theorem del_comp {X Y : C} (f : X ⟶ Y) : f ≫ del Y = del X := del_naturality f

@[simp]
theorem del_unit' : del (𝟙_ C) = 𝟙 (𝟙_ C) := del_unit

end AffineMonoidalCategory

/-! ## Duality: SemiCartesian → Affine -/

/-- Every semicartesian monoidal category is affine (del = toUnit). -/
noncomputable instance AffineMonoidalCategory.ofSemiCartesian
    [SemiCartesianMonoidalCategory C] : AffineMonoidalCategory C where
  del := SemiCartesianMonoidalCategory.toUnit
  del_unit := SemiCartesianMonoidalCategory.toUnit_unit
  del_naturality := fun f => SemiCartesianMonoidalCategory.comp_toUnit f

end CategoryTheory

/-! ## Concrete instance: KlSPComp is affine -/

namespace CatCrypt.Core

open CategoryTheory MonoidalCategory
open CatCrypt.Prob

namespace KlSPComp

/-- Discard morphism: maps any value to the failing computation on Empty. -/
noncomputable def klDel (α : KlSPComp) : α ⟶ (show KlSPComp from Empty) :=
  fun _ => SPComp.fail

private theorem klDel_unit : klDel (show KlSPComp from Empty) = 𝟙 _ := by
  funext e; exact Empty.elim e

private theorem bind_fail_right {α β : Type*} (c : SPComp α) :
    SPComp.bind c (fun _ => (SPComp.fail : SPComp β)) = SPComp.fail := by
  funext h
  simp only [SPComp.bind_def, SPComp.fail]
  show SDistr.bind (c h) (fun _ => SDistr.fail) = SDistr.fail
  simp only [SDistr.bind, SDistr.fail]
  -- Goal: PMF.bind (c h) (fun oa => match oa ...) = PMF.pure none
  calc PMF.bind (c h) _ = PMF.bind (c h) (fun _ => PMF.pure (none : Option (β × Heap))) := by
        congr 1; funext oa; cases oa <;> rfl
    _ = PMF.pure none := PMF.bind_const _ _

private theorem klDel_naturality {α β : KlSPComp} (f : α ⟶ β) :
    f ≫ klDel β = klDel α := by
  funext a
  show SPComp.bind (f a) (klDel β) = klDel α a
  show SPComp.bind (f a) (fun _ => SPComp.fail) = SPComp.fail
  exact bind_fail_right (f a)

noncomputable instance : AffineMonoidalCategory KlSPComp where
  del := klDel
  del_unit := klDel_unit
  del_naturality := fun f => klDel_naturality f

end KlSPComp

end CatCrypt.Core

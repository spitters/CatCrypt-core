/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Package.RawPackage
import CatCrypt.Package.Locations

/-!
# Valid Packages

This file defines valid packages - raw packages with proofs that they correctly
implement their interface and only access declared locations.

## Main definitions

* `ValidCode` - A computation that only accesses locations in L and imports from I
* `ValidPackage` - A package that correctly implements interface E using imports from I
* `fseparate` - Two packages have disjoint locations

## References

* [Benton et al., *Nominal SSProve*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Package

open CatCrypt.Core
open CatCrypt.Prob

/-- Specification of location access in code.
    For a full implementation, we would need to track this syntactically.
    For now, we use a semantic characterization. -/
structure LocAccess where
  /-- Locations that may be read -/
  reads : Locations
  /-- Locations that may be written -/
  writes : Locations

/-- Code validity: only accesses locations in L and imports from I.
    This is a predicate on computations asserting they respect the declared
    locations and import interface.

    Note: A full implementation would require tracking access syntactically
    or using a free monad representation. For now, we use a Prop-level assertion.

    The `reads_in_L` condition says the return-value distribution is unchanged
    when an out-of-scope location is overwritten — the code doesn't read it. -/
class ValidCode (L : Locations) (I : Interface) (α : Type*) (c : SPComp α) : Prop where
  /-- The code's return-value distribution does not depend on locations outside L -/
  reads_in_L : ∀ l v h, l ∉ L →
    (c h).bind (fun (a, _) => SDistr.pure a) =
    (c (Heap.set h l v)).bind (fun (a, _) => SDistr.pure a)
  /-- The code only writes to locations in L -/
  writes_in_L : ∀ l h, l ∉ L →
    (c h).bind (fun (a, h₁) => SDistr.pure (a, h₁.get l)) =
    (c h).bind (fun (a, _) => SDistr.pure (a, h.get l))

/-- A valid package correctly implements an export interface using an import interface.
    - L: the locations the package may access
    - I: the interface the package may import
    - E: the interface the package exports -/
structure ValidPackage (L : Locations) (I E : Interface) (P : RawPackage) : Prop where
  /-- The package implements all operations in E -/
  exports_complete : ∀ id S T, E.has id S T → P.has id S T
  /-- The package only implements operations in E -/
  exports_only : ∀ id S T, P.has id S T → E.has id S T
  /-- All implementations are valid code -/
  valid_impl : ∀ e ∈ P.entries, ∀ x : e.fun_.src,
                 ValidCode L I e.fun_.tgt (e.fun_.impl x)

/-- Two packages have separate (disjoint) locations -/
def fseparate (L₁ L₂ : Locations) : Prop :=
  Locations.Separate L₁ L₂

namespace ValidPackage

/-- Valid code for a smaller location set is valid for a larger one.
    This is mathematically sound: if code only accesses L₁, and L₁ ⊆ L₂,
    then the code trivially satisfies validity for L₂. -/
theorem validCode_weaken {L₁ L₂ : Locations} {I₁ I₂ : Interface} {α : Type*} {c : SPComp α}
    (hL : L₁ ⊆ L₂)
    (hv : ValidCode L₁ I₁ α c) :
    ValidCode L₂ I₂ α c where
  reads_in_L := fun l v h hl =>
    -- If l ∉ L₂ and L₁ ⊆ L₂, then l ∉ L₁
    have hl₁ : l ∉ L₁ := fun h => hl (hL h)
    hv.reads_in_L l v h hl₁
  writes_in_L := fun l h hl =>
    have hl₁ : l ∉ L₁ := fun h => hl (hL h)
    hv.writes_in_L l h hl₁

/-- Empty package is valid for empty interface -/
theorem empty_valid (I : Interface) : ValidPackage ∅ I ∅ (∅ : RawPackage) where
  exports_complete := fun id S T h => (Interface.empty_not_has id S T h).elim
  exports_only := fun id S T h => (RawPackage.empty_not_has id S T h).elim
  valid_impl := fun e h => (Finset.notMem_empty _ h).elim

/-- Parallel composition of valid packages -/
theorem par_valid {L₁ L₂ : Locations} {I₁ I₂ E₁ E₂ : Interface}
    {P₁ P₂ : RawPackage}
    (h₁ : ValidPackage L₁ I₁ E₁ P₁) (h₂ : ValidPackage L₂ I₂ E₂ P₂)
    (hL : Locations.Separate L₁ L₂)
    (hI : Interface.Disjoint I₁ I₂)
    (hP : RawPackage.Disjoint P₁ P₂)
    (hE : Interface.Disjoint E₁ E₂) :
    ValidPackage (Locations.union L₁ L₂ hL) (Interface.union I₁ I₂ hI)
                 (Interface.union E₁ E₂ hE) (RawPackage.par P₁ P₂ hP) := by
  constructor
  · intro id S T hE'
    simp only [Interface.union, Interface.has, Finset.mem_union] at hE'
    obtain ⟨e, he, hid, hsig⟩ := hE'
    cases he with
    | inl he₁ =>
      obtain ⟨pe, hpe, hpid, hpS, hpT⟩ := h₁.exports_complete id S T ⟨e, he₁, hid, hsig⟩
      simp only [RawPackage.par, RawPackage.has, Finset.mem_union] at *
      exact ⟨pe, Or.inl hpe, hpid, hpS, hpT⟩
    | inr he₂ =>
      obtain ⟨pe, hpe, hpid, hpS, hpT⟩ := h₂.exports_complete id S T ⟨e, he₂, hid, hsig⟩
      simp only [RawPackage.par, RawPackage.has, Finset.mem_union] at *
      exact ⟨pe, Or.inr hpe, hpid, hpS, hpT⟩
  · intro id S T hP'
    simp only [RawPackage.par, RawPackage.has, Finset.mem_union] at hP'
    obtain ⟨pe, hpe, hpid, hpS, hpT⟩ := hP'
    cases hpe with
    | inl hpe₁ => exact Interface.union_has_left hE id S T (h₁.exports_only id S T ⟨pe, hpe₁, hpid, hpS, hpT⟩)
    | inr hpe₂ => exact Interface.union_has_right hE id S T (h₂.exports_only id S T ⟨pe, hpe₂, hpid, hpS, hpT⟩)
  · -- valid_impl
    intro e he x
    simp only [RawPackage.par, Finset.mem_union] at he
    cases he with
    | inl he₁ => exact validCode_weaken (fun id hid => by
        rw [Locations.union_ids]; exact Finset.mem_union_left _ hid) (h₁.valid_impl e he₁ x)
    | inr he₂ => exact validCode_weaken (fun id hid => by
        rw [Locations.union_ids]; exact Finset.mem_union_right _ hid) (h₂.valid_impl e he₂ x)

/-- Location tracking: get the locations from a ValidPackage -/
def locs (L : Locations) (_I _E : Interface) (_P : RawPackage)
    (_ : ValidPackage L _I _E _P) : Locations := L

end ValidPackage

/-- The game import interface (empty for basic games) -/
def Game_import : Interface := Interface.empty

/-- The adversary export interface (empty for basic adversaries) -/
def A_export : Interface := Interface.empty

end CatCrypt.Package

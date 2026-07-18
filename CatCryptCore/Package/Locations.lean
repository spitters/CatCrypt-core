/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Location
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Enhanced Location Tracking

This file defines a structured collection of memory locations for package validity tracking.
Locations are tracked as a finite set with type information.

## Main definitions

* `Locations` - A finite collection of typed memory locations
* `Locations.empty` - Empty location set
* `Locations.Separate` - Two location sets with disjoint ids
* `Locations.mem` - Location membership

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Package

open CatCrypt.Core

/-- Locations: a finite set of location ids with their type information.
    We track locations by their ids since type information is bundled in Location. -/
structure Locations where
  /-- The set of location identifiers -/
  ids : Finset ℕ
  /-- Function mapping ids to their locations (partial) -/
  toLocation : (id : ℕ) → id ∈ ids → Location
  /-- Locations have consistent ids -/
  id_consistent : ∀ id (h : id ∈ ids), (toLocation id h).id = id

namespace Locations

/-- Empty location set -/
def empty : Locations :=
  ⟨∅, fun _ h => (Finset.notMem_empty _ h).elim, fun _ h => (Finset.notMem_empty _ h).elim⟩

instance : EmptyCollection Locations := ⟨empty⟩

/-- A location is in the set if its id is in the id set -/
instance : Membership Location Locations where
  mem := fun (L : Locations) (l : Location) => l.id ∈ L.ids

theorem mem_iff (L : Locations) (l : Location) : l ∈ L ↔ l.id ∈ L.ids := Iff.rfl

/-- Singleton location set -/
def singleton (l : Location) : Locations :=
  ⟨{l.id}, fun id _ => l, fun id h => by simp only [Finset.mem_singleton] at h; exact h.symm⟩

instance : Singleton Location Locations := ⟨singleton⟩

theorem mem_singleton (l l' : Location) : l' ∈ ({l} : Locations) ↔ l'.id = l.id :=
  Finset.mem_singleton

/-- Two location sets are separate (disjoint ids) -/
def Separate (L₁ L₂ : Locations) : Prop :=
  Disjoint L₁.ids L₂.ids

theorem separate_symm {L₁ L₂ : Locations} (h : Separate L₁ L₂) : Separate L₂ L₁ :=
  Disjoint.symm h

theorem separate_empty_left (L : Locations) : Separate empty L := by
  simp only [Separate, empty, Finset.disjoint_empty_left]

theorem separate_empty_right (L : Locations) : Separate L empty := by
  simp only [Separate, empty, Finset.disjoint_empty_right]

/-- Union of location sets (partial - should only be used with disjoint locations
    for well-definedness of the location mapping) -/
noncomputable def union (L₁ L₂ : Locations) (h : Separate L₁ L₂) : Locations :=
  ⟨L₁.ids ∪ L₂.ids,
   fun id hid =>
     if h₁ : id ∈ L₁.ids then
       L₁.toLocation id h₁
     else
       have h₂ : id ∈ L₂.ids := by
         rw [Finset.mem_union] at hid
         cases hid with
         | inl h => exact (h₁ h).elim
         | inr h => exact h
       L₂.toLocation id h₂,
   fun id hid => by
     simp only
     split_ifs with h₁
     · exact L₁.id_consistent id h₁
     · have h₂ : id ∈ L₂.ids := by
         rw [Finset.mem_union] at hid
         cases hid with
         | inl h => exact (h₁ h).elim
         | inr h => exact h
       exact L₂.id_consistent id h₂⟩

theorem union_ids {L₁ L₂ : Locations} (h : Separate L₁ L₂) :
    (union L₁ L₂ h).ids = L₁.ids ∪ L₂.ids := rfl

theorem mem_union_left {L₁ L₂ : Locations} (h : Separate L₁ L₂) (l : Location) :
    l ∈ L₁ → l ∈ union L₁ L₂ h := by simp only [mem_iff, union_ids, Finset.mem_union]; exact Or.inl

theorem mem_union_right {L₁ L₂ : Locations} (h : Separate L₁ L₂) (l : Location) :
    l ∈ L₂ → l ∈ union L₁ L₂ h := by simp only [mem_iff, union_ids, Finset.mem_union]; exact Or.inr

/-- Subset relation on locations -/
def Subset (L₁ L₂ : Locations) : Prop := L₁.ids ⊆ L₂.ids

instance : HasSubset Locations := ⟨Subset⟩

theorem empty_subset (L : Locations) : (∅ : Locations) ⊆ L :=
  Finset.empty_subset _

/-- Difference of location sets -/
def diff (L₁ L₂ : Locations) : Locations :=
  ⟨L₁.ids \ L₂.ids,
   fun id hid =>
     have h : id ∈ L₁.ids := Finset.mem_sdiff.mp hid |>.1
     L₁.toLocation id h,
   fun id hid =>
     have h : id ∈ L₁.ids := Finset.mem_sdiff.mp hid |>.1
     L₁.id_consistent id h⟩

theorem diff_ids (L₁ L₂ : Locations) : (diff L₁ L₂).ids = L₁.ids \ L₂.ids := rfl

/-- Card of a location set -/
def card (L : Locations) : ℕ := L.ids.card

theorem empty_card : (∅ : Locations).card = 0 := Finset.card_empty

theorem singleton_card (l : Location) : ({l} : Locations).card = 1 := Finset.card_singleton _

end Locations

end CatCrypt.Package

/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
# Operation Signatures and Interfaces

This file defines operation signatures and interfaces for the CatCrypt package system.
An interface is a finite collection of operation signatures indexed by identifiers.

## Main definitions

* `OpSig` - Operation signature: specifies input and output types
* `Interface` - Collection of operation signatures indexed by natural numbers
* `Interface.empty` - Empty interface
* `Interface.has` - Check if interface contains an operation

## References

* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Package

/-- Operation signature: specifies the input type (src) and output type (tgt) -/
structure OpSig where
  src : Type*
  tgt : Type*

/-- Two operation signatures are equal if their types are the same.
    Note: This uses heterogeneous equality for Type universes. -/
noncomputable instance : DecidableEq OpSig := Classical.decEq OpSig

/-- An interface entry: an operation id with its signature -/
structure InterfaceEntry where
  id : ℕ
  sig : OpSig

/-- DecidableEq for InterfaceEntry (needed for Finset operations) -/
noncomputable instance : DecidableEq InterfaceEntry := Classical.decEq InterfaceEntry

/-- Interface: a finite collection of operation signatures indexed by identifiers.
    We represent this as a finite set of entries with unique ids. -/
structure Interface where
  entries : Finset InterfaceEntry
  unique_ids : ∀ e₁ e₂ : InterfaceEntry, e₁ ∈ entries → e₂ ∈ entries →
                e₁.id = e₂.id → e₁ = e₂

namespace Interface

/-- Empty interface -/
def empty : Interface := ⟨∅, fun _ _ h => (Finset.notMem_empty _ h).elim⟩

instance : EmptyCollection Interface := ⟨empty⟩

/-- Check if an interface declares an operation with given id and signature -/
def has (I : Interface) (id : ℕ) (S T : Type*) : Prop :=
  ∃ e ∈ I.entries, e.id = id ∧ e.sig = ⟨S, T⟩

/-- The set of operation ids in the interface -/
noncomputable def ids (I : Interface) : Finset ℕ :=
  I.entries.image (·.id)

/-- Lookup a signature by id (noncomputable since types aren't decidable) -/
noncomputable def lookup (I : Interface) (id : ℕ) : Option OpSig :=
  if h : ∃ e ∈ I.entries, e.id = id then
    some (Classical.choose h).sig
  else
    none

/-- Two interfaces are disjoint if they share no operation ids -/
def Disjoint (I₁ I₂ : Interface) : Prop :=
  _root_.Disjoint I₁.ids I₂.ids

/-- A single operation interface -/
noncomputable def singleton (id : ℕ) (S T : Type*) : Interface :=
  ⟨{⟨id, ⟨S, T⟩⟩}, fun e₁ e₂ h₁ h₂ _ => by
    simp only [Finset.mem_singleton] at h₁ h₂
    rw [h₁, h₂]⟩

theorem singleton_has (id : ℕ) (S T : Type*) :
    (singleton id S T).has id S T := by
  simp only [singleton, has]
  exact ⟨⟨id, ⟨S, T⟩⟩, Finset.mem_singleton_self _, rfl, rfl⟩

/-- Empty interface has no operations -/
theorem empty_not_has (id : ℕ) (S T : Type*) : ¬(empty.has id S T) := by
  simp only [empty, has]
  intro ⟨e, he, _, _⟩
  exact Finset.notMem_empty _ he

/-- Union of interfaces (requires disjoint ids for uniqueness) -/
noncomputable def union (I₁ I₂ : Interface) (h : Disjoint I₁ I₂) : Interface :=
  ⟨I₁.entries ∪ I₂.entries, fun e₁ e₂ h₁ h₂ hid => by
    rw [Finset.mem_union] at h₁ h₂
    cases h₁ with
    | inl h₁ =>
      cases h₂ with
      | inl h₂ => exact I₁.unique_ids e₁ e₂ h₁ h₂ hid
      | inr h₂ =>
        -- e₁ from I₁, e₂ from I₂ with same id - contradicts disjointness
        exfalso
        simp only [Disjoint, ids, Finset.disjoint_iff_ne] at h
        have h₁' : e₁.id ∈ I₁.ids := Finset.mem_image_of_mem _ h₁
        have h₂' : e₂.id ∈ I₂.ids := Finset.mem_image_of_mem _ h₂
        exact h _ h₁' _ h₂' hid
    | inr h₁ =>
      cases h₂ with
      | inl h₂ =>
        exfalso
        simp only [Disjoint, ids, Finset.disjoint_iff_ne] at h
        have h₂' : e₂.id ∈ I₁.ids := Finset.mem_image_of_mem _ h₂
        have h₁' : e₁.id ∈ I₂.ids := Finset.mem_image_of_mem _ h₁
        exact h _ h₂' _ h₁' hid.symm
      | inr h₂ => exact I₂.unique_ids e₁ e₂ h₁ h₂ hid⟩

/-- Union contains operations from both interfaces -/
theorem union_has_left {I₁ I₂ : Interface} (h : Disjoint I₁ I₂)
    (id : ℕ) (S T : Type*) (hI₁ : I₁.has id S T) :
    (union I₁ I₂ h).has id S T := by
  obtain ⟨e, he, hid, hsig⟩ := hI₁; simp only [union, has]
  exact ⟨e, Finset.mem_union_left _ he, hid, hsig⟩

theorem union_has_right {I₁ I₂ : Interface} (h : Disjoint I₁ I₂)
    (id : ℕ) (S T : Type*) (hI₂ : I₂.has id S T) :
    (union I₁ I₂ h).has id S T := by
  obtain ⟨e, he, hid, hsig⟩ := hI₂; simp only [union, has]
  exact ⟨e, Finset.mem_union_right _ he, hid, hsig⟩

end Interface

end CatCrypt.Package

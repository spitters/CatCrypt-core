/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Nominal.Nominal
import CatCrypt.Nominal.Fresh
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Basic

open scoped Classical

/-!
# Locations and Heaps for Deep Embedding

This file defines locations and heaps for the deep embedding of CatCrypt computations.

## Main definitions

* `Location` - A location pairs an atom (name) with a type
* `DeepHeap` - A heap mapping locations to values
* `DeepHeap.empty` - The empty heap
* `DeepHeap.get` - Get value from a location
* `DeepHeap.set` - Set value at a location

## Nominal Structure

Locations are equipped with a nominal structure:
* Permutations act on the atom while preserving the type: `π • ℓ = ⟨π • ℓ.name, ℓ.ty⟩`
* The support of a location is the singleton of its atom: `supp ℓ = {ℓ.name}`

**Design decision**: Two locations with the same name but different types are
considered *different* locations. This is the mathematically consistent approach:
Location equality is structural equality of the pair (name, ty). The heap stores
values indexed by the full location (including type), so there's no inconsistency.

This means you cannot have two locations with the same name but different types
"collide" in a heap - they simply occupy different slots.

## References

* CatCrypt `theories/Crypt/rhl_semantics/free_prot/free_code.v`
* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Deep

open CatCrypt.Nominal

/-- A location pairs an atom (name) with a type.
    This represents a typed memory location in the deep embedding.

    Two locations are equal iff both name AND ty are equal.
    This is standard structural equality - no axioms needed. -/
structure Location where
  /-- The name of the location -/
  name : Atom
  /-- The type of values stored at this location -/
  ty : Type*

namespace Location

/-- Decidable equality on the name component only.
    Note: This is weaker than structural equality since it ignores types. -/
def beqName (ℓ₁ ℓ₂ : Location) : Bool :=
  ℓ₁.name == ℓ₂.name

/-- Two locations are equal iff they have the same name and type.
    This follows from the structure definition. -/
theorem ext_iff {ℓ₁ ℓ₂ : Location} : ℓ₁ = ℓ₂ ↔ ℓ₁.name = ℓ₂.name ∧ ℓ₁.ty = ℓ₂.ty := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩
  · intro ⟨hn, ht⟩
    cases ℓ₁
    cases ℓ₂
    simp only [mk.injEq]
    exact ⟨hn, ht⟩

@[ext]
theorem ext {ℓ₁ ℓ₂ : Location} (hn : ℓ₁.name = ℓ₂.name) (ht : ℓ₁.ty = ℓ₂.ty) : ℓ₁ = ℓ₂ :=
  ext_iff.mpr ⟨hn, ht⟩

theorem name_eq_of_eq {ℓ₁ ℓ₂ : Location} (h : ℓ₁ = ℓ₂) : ℓ₁.name = ℓ₂.name := by
  rw [h]

theorem ty_eq_of_eq {ℓ₁ ℓ₂ : Location} (h : ℓ₁ = ℓ₂) : ℓ₁.ty = ℓ₂.ty := by
  rw [h]

/-- Apply a permutation to a location by permuting its atom name.
    The type is preserved: `(π • ℓ).ty = ℓ.ty`. -/
def perm (π : FinPerm) (ℓ : Location) : Location :=
  ⟨π ℓ.name, ℓ.ty⟩

@[simp]
theorem perm_name (π : FinPerm) (ℓ : Location) : (perm π ℓ).name = π ℓ.name := rfl

@[simp]
theorem perm_ty (π : FinPerm) (ℓ : Location) : (perm π ℓ).ty = ℓ.ty := rfl

@[simp]
theorem perm_one (ℓ : Location) : perm 1 ℓ = ℓ := by
  simp only [perm, FinPerm.one_apply]

theorem perm_mul (π₁ π₂ : FinPerm) (ℓ : Location) :
    perm (π₁ * π₂) ℓ = perm π₁ (perm π₂ ℓ) := by
  simp only [perm, FinPerm.mul_apply]

end Location

/-! ## Nominal Instances for Location

Locations form a nominal set where:
- Permutations act on the atom, preserving the type
- The support is the singleton of the atom -/

/-- Nominal action on locations: permute the atom, preserve the type -/
instance : MulAction FinPerm Location where
  smul := Location.perm
  one_smul := Location.perm_one
  mul_smul := Location.perm_mul

/-- Locations form a nominal set with singleton support -/
instance : NomSet Location where
  supp := fun ℓ => {ℓ.name}
  supp_supports := fun ℓ π h => by
    have hname := h ℓ.name (Finset.mem_singleton_self ℓ.name)
    simp only [HSMul.hSMul, SMul.smul, Location.perm, hname]
  supp_equivariant := fun ℓ π => by
    simp only [HSMul.hSMul, SMul.smul, Location.perm, Finset.image_singleton]

/-- The atom of a location -/
abbrev Location.atom (ℓ : Location) : Atom := ℓ.name

/-- The support of a location is its atom -/
@[simp]
theorem Location.supp_eq (ℓ : Location) : NomSet.supp ℓ = {ℓ.name} := rfl

/-- Two locations are disjoint if they have different atoms -/
def Location.disj (ℓ₁ ℓ₂ : Location) : Prop := ℓ₁.name ≠ ℓ₂.name

theorem Location.disj_comm (ℓ₁ ℓ₂ : Location) : ℓ₁.disj ℓ₂ ↔ ℓ₂.disj ℓ₁ :=
  ne_comm

theorem Location.disj_of_ne_name {ℓ₁ ℓ₂ : Location} (h : ℓ₁.name ≠ ℓ₂.name) :
    ℓ₁.disj ℓ₂ := h

/-- A finite set of locations -/
abbrev LocAtomSet := Finset Atom

/-- Get the atoms from a finite set of locations.
    Note: We can't use Finset Location directly since Location contains types,
    so we work with atoms and store locations in a separate structure. -/
def locsToAtoms (locs : List Location) : LocAtomSet :=
  locs.foldl (fun s ℓ => s ∪ {ℓ.name}) ∅

/-- A heap is a mapping from locations to optional values.
    Each location can either be uninitialized (None) or contain a value
    of the appropriate type. -/
structure DeepHeap where
  /-- The underlying data: for each location, an optional value of the right type -/
  data : ∀ (ℓ : Location), Option ℓ.ty

namespace DeepHeap

/-- The empty heap where all locations are uninitialized -/
def empty : DeepHeap :=
  ⟨fun _ => none⟩

/-- Get the value at a location -/
def get (h : DeepHeap) (ℓ : Location) : Option ℓ.ty :=
  h.data ℓ

/-- Set the value at a location.

    This updates the heap so that location `ℓ` contains value `v`.
    For any other location `ℓ'`, the value is unchanged.

    Two locations are considered the same iff both name AND type match.
    If `ℓ'` has the same name but different type, it is a different location
    and is not affected by this update.

    This is noncomputable because we use classical decidability for type equality. -/
noncomputable def set (h : DeepHeap) (ℓ : Location) (v : ℓ.ty) : DeepHeap :=
  ⟨fun ℓ' =>
    -- Check if both name and type match
    if _hName : ℓ'.name = ℓ.name then
      -- Names match, now check types
      if hTy : ℓ'.ty = ℓ.ty then
        -- Both match: this is the same location, return the new value
        -- We need to cast v from ℓ.ty to ℓ'.ty using hTy
        some (cast hTy.symm v)
      else
        -- Same name, different type: different location, keep old value
        h.data ℓ'
    else
      -- Different name: different location, keep old value
      h.data ℓ'⟩

/-- Getting from the empty heap returns None -/
@[simp]
theorem get_empty (ℓ : Location) : get empty ℓ = none := rfl

/-- Getting from a heap after setting the same location returns the value -/
theorem get_set_same (h : DeepHeap) (ℓ : Location) (v : ℓ.ty) :
    get (set h ℓ v) ℓ = some v := by
  simp only [get, set, dif_pos, cast_eq]

/-- Getting from a heap after setting a different location returns the original value.
    Note: This now requires that the locations are different (either by name or by type). -/
theorem get_set_other (h : DeepHeap) (ℓ₁ ℓ₂ : Location) (v : ℓ₁.ty)
    (hne : ℓ₁ ≠ ℓ₂) :
    get (set h ℓ₁ v) ℓ₂ = get h ℓ₂ := by
  simp only [get, set]
  split_ifs with hName hTy
  · -- Both name and type match - contradiction with hne
    exfalso
    apply hne
    exact Location.ext hName.symm hTy.symm
  · -- Name matches, type doesn't - keep old value
    rfl
  · -- Name doesn't match - keep old value
    rfl

/-- Getting from a heap after setting a location with different name returns the original value.
    This is a convenience lemma when we know the names differ. -/
theorem get_set_other_name (h : DeepHeap) (ℓ₁ ℓ₂ : Location) (v : ℓ₁.ty)
    (hne : ℓ₁.name ≠ ℓ₂.name) :
    get (set h ℓ₁ v) ℓ₂ = get h ℓ₂ := by
  apply get_set_other
  intro heq
  apply hne
  rw [heq]

/-- Extensionality for heaps: heaps are equal if they agree on all locations -/
@[ext]
theorem ext {h₁ h₂ : DeepHeap} (hext : ∀ ℓ, h₁.get ℓ = h₂.get ℓ) : h₁ = h₂ := by
  cases h₁; cases h₂
  simp only [get] at hext
  congr
  funext ℓ
  exact hext ℓ

/-- Setting the same location twice keeps only the last value -/
theorem set_set_same (h : DeepHeap) (ℓ : Location) (v₁ v₂ : ℓ.ty) :
    set (set h ℓ v₁) ℓ v₂ = set h ℓ v₂ := by
  apply ext
  intro ℓ'
  simp only [get, set]
  split_ifs <;> rfl

/-- Setting different locations commutes.
    Note: Now requires that the locations are different (either by name or type). -/
theorem set_set_comm (h : DeepHeap) (ℓ₁ ℓ₂ : Location)
    (v₁ : ℓ₁.ty) (v₂ : ℓ₂.ty) (hne : ℓ₁ ≠ ℓ₂) :
    set (set h ℓ₁ v₁) ℓ₂ v₂ = set (set h ℓ₂ v₂) ℓ₁ v₁ := by
  apply ext
  intro ℓ
  simp only [get, set]
  split_ifs <;> try rfl
  -- Case: both name and type match for both ℓ₁ and ℓ₂ → contradiction
  rename_i hName1 hTy1 hName2 hTy2
  exfalso
  apply hne
  have hname : ℓ₁.name = ℓ₂.name := hName2.symm.trans hName1
  have htype : ℓ₁.ty = ℓ₂.ty := hTy2.symm.trans hTy1
  exact Location.ext hname htype

/-- Setting different locations (by name) commutes.
    This is a convenience lemma when we know the names differ. -/
theorem set_set_comm_name (h : DeepHeap) (ℓ₁ ℓ₂ : Location)
    (v₁ : ℓ₁.ty) (v₂ : ℓ₂.ty) (hne : ℓ₁.name ≠ ℓ₂.name) :
    set (set h ℓ₁ v₁) ℓ₂ v₂ = set (set h ℓ₂ v₂) ℓ₁ v₁ := by
  apply set_set_comm
  intro heq
  apply hne
  rw [heq]

end DeepHeap

end CatCrypt.Deep

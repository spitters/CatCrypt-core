/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Location
import Mathlib.Data.Finmap
import Mathlib.Data.Fintype.EquivFin

/-!
# Heap Model

This file defines the heap model for stateful computations.

## Design

Following the Rocq SSProve design, values are stored using their Fintype encoding
as natural numbers in a **partial finite map** (`Finmap`) from location ids to
encoded values. Unaccessed locations map to `none`; `get` returns `default` for
such locations.

This is the Lean 4 analogue of Rocq SSProve's `{fmap nat → nat}`.

## Key Properties

* `get_set_same`: Getting after setting returns the stored value
* `get_set_other`: Setting at one location doesn't affect other locations
* `set_set_same`: Double write contracts to a single write
* `set_set_comm`: Writes to different locations commute
-/

open scoped Classical

namespace CatCrypt.Core

/-- Heap: partial finite map from location ids to encoded values.
    Values are encoded using their Fintype encoding as natural numbers.
    Unaccessed locations are absent from the map; `get` returns `default`
    for absent locations. -/
structure Heap where
  /-- Partial map from location id to encoded value (natural number) -/
  data : Finmap (fun _ : Nat => Nat)
  deriving Inhabited

namespace Heap

/-- Extensionality for heaps -/
@[ext]
theorem ext {h₁ h₂ : Heap} (hdata : h₁.data = h₂.data) : h₁ = h₂ := by
  cases h₁; cases h₂; simp only [Heap.mk.injEq]; exact hdata

/-- Extensionality for heaps via lookup -/
theorem ext_lookup {h₁ h₂ : Heap}
    (hlookup : ∀ id, h₁.data.lookup id = h₂.data.lookup id) : h₁ = h₂ :=
  ext (Finmap.ext_lookup hlookup)

/-- Empty heap: no locations are initialized -/
def empty : Heap := ⟨∅⟩

/-- Encode a value using its Fintype equivalence -/
noncomputable def encode {α : Type} [Fintype α] (v : α) : Nat :=
  (Fintype.equivFin α v).val

/-- Decode a natural number to a value.
    If the number is out of range, returns default. -/
noncomputable def decode (α : Type) [Fintype α] [Inhabited α] (n : Nat) : α :=
  if h : n < Fintype.card α then
    (Fintype.equivFin α).symm ⟨n, h⟩
  else
    default

/-- Encoding then decoding returns the original value -/
theorem decode_encode {α : Type} [Fintype α] [Inhabited α] (v : α) :
    decode α (encode v) = v := by
  unfold encode decode
  have hlt := (Fintype.equivFin α v).isLt
  simp only [hlt, ↓reduceDIte]
  exact Equiv.symm_apply_apply _ _

/-- Get a value from the heap at a location.
    Returns `default` if the location has never been written. -/
noncomputable def get (h : Heap) (l : Location) : l.ty :=
  match h.data.lookup l.id with
  | some n => decode l.ty n
  | none => default

/-- Set a value in the heap at a location -/
noncomputable def set (h : Heap) (l : Location) (v : l.ty) : Heap :=
  ⟨h.data.insert l.id (encode v)⟩

/-- Two heaps agree on a set of location ids -/
def agreeOn (h1 h2 : Heap) (locs : LocSet) : Prop :=
  ∀ id ∈ locs, h1.data.lookup id = h2.data.lookup id

/-- Heap equality is not decidable in general, but we can use classical logic -/
noncomputable instance : DecidableEq Heap := Classical.decEq Heap

/-- Getting after setting the same location returns the stored value -/
@[simp]
theorem get_set_same (h : Heap) (l : Location) (v : l.ty) :
    (h.set l v).get l = v := by
  simp only [get, set, Finmap.lookup_insert, decode_encode]

/-- Setting at one location doesn't affect getting from another location -/
@[simp]
theorem get_set_other (h : Heap) (l l' : Location) (v : l.ty) (hne : l.id ≠ l'.id) :
    (h.set l v).get l' = h.get l' := by
  unfold get set
  have hne' : l'.id ≠ l.id := hne.symm
  simp [hne']

/-- Setting the same location twice: the second write wins -/
@[simp]
theorem set_set_same (h : Heap) (l : Location) (v₁ v₂ : l.ty) :
    (h.set l v₁).set l v₂ = h.set l v₂ := by
  apply ext
  simp only [set, Finmap.insert_insert]

/-- Setting different locations commutes -/
theorem set_set_comm (h : Heap) (l₁ l₂ : Location) (v₁ : l₁.ty) (v₂ : l₂.ty)
    (hne : l₁.id ≠ l₂.id) :
    (h.set l₁ v₁).set l₂ v₂ = (h.set l₂ v₂).set l₁ v₁ := by
  apply ext
  simp only [set]
  exact Finmap.insert_insert_of_ne _ hne

/-- Looking up a location in the empty heap returns none -/
@[simp]
theorem get_empty (l : Location) : empty.get l = default := by
  simp only [get, empty, Finmap.lookup_empty]

end Heap

end CatCrypt.Core

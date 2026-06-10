/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Invariant.Coupling

/-!
# Semi-Invariants for Relational Reasoning

This file defines semi-invariants - partial invariants that conclude about
specific locations rather than whole heaps. Semi-invariants can be combined
with proper invariants using `⋊` conjunction.

## Main definitions

* `SemiInvariant` - A predicate that is location-local
* `IsInvariant_inv_conj` - Combining invariants with semi-invariants

## Usage

Semi-invariants are used for:
1. Tracking remembered values (`rem_lhs`, `rem_rhs`)
2. Location synchronization (`syncsAt`)
3. Location-specific couplings (`couple_cross`)

## References

* [Benton et al., *Nominal SSProve*](https://eprint.iacr.org/2025/598)
* SSProve: theories/Crypt/package/pkg_heap_comp.v
-/

namespace CatCrypt.Invariant

open CatCrypt.Core
open CatCrypt.Relational
open CatCrypt.Package

/-! ## Semi-Invariant Class -/

/-- A semi-invariant is a predicate that depends only on specific locations.
    Unlike a full invariant, it doesn't need to be preserved by arbitrary writes,
    but it is local to the locations it mentions. -/
class SemiInvariant (L₀ L₁ : Locations) (sinv : RPre) : Prop where
  /-- The semi-invariant only reads from locations in L₀ on the left -/
  left_reads : ∀ h₀ h₀' h₁, (∀ l ∈ L₀, h₀.get l = h₀'.get l) → sinv h₀ h₁ → sinv h₀' h₁
  /-- The semi-invariant only reads from locations in L₁ on the right -/
  right_reads : ∀ h₀ h₁ h₁', (∀ l ∈ L₁, h₁.get l = h₁'.get l) → sinv h₀ h₁ → sinv h₀ h₁'

/-! ## Basic Semi-Invariant Instances -/

/-- True is always a semi-invariant -/
instance truePre_SemiInvariant (L₀ L₁ : Locations) : SemiInvariant L₀ L₁ truePre where
  left_reads := fun _ _ _ _ _ => trivial
  right_reads := fun _ _ _ _ _ => trivial

/-- Synchronization at a location is a semi-invariant if both sides have the location.

    **Mathematical argument:**
    - `hsync : h₀.get l = h₁.get l`
    - `hloc : ∀ l' ∈ L₀, h₀.get l' = h₀'.get l'`
    - Since `l ∈ L₀`, we have `h₀.get l = h₀'.get l` (by hloc)
    - Therefore `h₀'.get l = h₀.get l = h₁.get l`

    Note: Earlier versions of this codebase had universe polymorphism issues here.
    These were resolved by fixing Location.ty to Type (Type 0) in Core/Location.lean. -/
theorem syncsAt_SemiInvariant (l : Location)
    (L₀ L₁ : Locations) (hl₀ : l ∈ L₀) (hl₁ : l ∈ L₁) :
    SemiInvariant L₀ L₁ (syncsAt l) where
  left_reads := fun h₀ h₀' h₁ hloc hsync => by
    -- hsync : h₀.get l = h₁.get l
    -- hloc : ∀ l' ∈ L₀, h₀.get l' = h₀'.get l'
    -- Need: h₀'.get l = h₁.get l
    simp only [syncsAt] at hsync ⊢
    have heq : h₀.get l = h₀'.get l := hloc l hl₀
    rw [← heq, hsync]
  right_reads := fun h₀ h₁ h₁' hloc hsync => by
    -- hsync : h₀.get l = h₁.get l
    -- hloc : ∀ l' ∈ L₁, h₁.get l' = h₁'.get l'
    -- Need: h₀.get l = h₁'.get l
    simp only [syncsAt] at hsync ⊢
    have heq : h₁.get l = h₁'.get l := hloc l hl₁
    rw [hsync, heq]

/-- Remembered value on left is a semi-invariant.

    **Mathematical argument:**
    - `hrem : h₀.get l = v`
    - `hloc : ∀ l' ∈ L₀, h₀.get l' = h₀'.get l'`
    - Since `l ∈ L₀`, we have `h₀.get l = h₀'.get l`
    - Therefore `h₀'.get l = h₀.get l = v`

    Note: Earlier versions of this codebase had universe polymorphism issues here.
    These were resolved by fixing Location.ty to Type (Type 0) in Core/Location.lean. -/
theorem rem_lhs_SemiInvariant (l : Location) (v : l.ty)
    (L₀ L₁ : Locations) (hl : l ∈ L₀) :
    SemiInvariant L₀ L₁ (rem_lhs l v) where
  left_reads := fun h₀ h₀' _ hloc hrem => by
    -- hrem : h₀.get l = v
    -- hloc : ∀ l' ∈ L₀, h₀.get l' = h₀'.get l'
    -- Need: h₀'.get l = v
    simp only [rem_lhs] at hrem ⊢
    have heq : h₀.get l = h₀'.get l := hloc l hl
    rw [← heq, hrem]
  right_reads := fun _ _ _ _ hrem => hrem

/-- Remembered value on right is a semi-invariant.

    **Mathematical argument:**
    - `hrem : h₁.get l = v`
    - `hloc : ∀ l' ∈ L₁, h₁.get l' = h₁'.get l'`
    - Since `l ∈ L₁`, we have `h₁.get l = h₁'.get l`
    - Therefore `h₁'.get l = h₁.get l = v`

    Note: Earlier versions of this codebase had universe polymorphism issues here.
    These were resolved by fixing Location.ty to Type (Type 0) in Core/Location.lean. -/
theorem rem_rhs_SemiInvariant (l : Location) (v : l.ty)
    (L₀ L₁ : Locations) (hl : l ∈ L₁) :
    SemiInvariant L₀ L₁ (rem_rhs l v) where
  left_reads := fun _ _ _ _ hrem => hrem
  right_reads := fun _ h₁ h₁' hloc hrem => by
    -- hrem : h₁.get l = v
    -- hloc : ∀ l' ∈ L₁, h₁.get l' = h₁'.get l'
    -- Need: h₁'.get l = v
    simp only [rem_rhs] at hrem ⊢
    have heq : h₁.get l = h₁'.get l := hloc l hl
    rw [← heq, hrem]

/-! ## Combining Invariants with Semi-Invariants -/

/-- An invariant combined with a semi-invariant is still an invariant.

    **Mathematical argument:**
    - Both inv and sinv only depend on locations in L₀ (for left heap)
    - If heaps agree on L₀, both inv and sinv transfer to the new heap
    - Therefore their conjunction transfers as well

    Note: Earlier versions of this codebase had universe polymorphism issues here.
    These were resolved by fixing Location.ty to Type (Type 0) in Core/Location.lean. -/
theorem IsInvariant_inv_conj {L₀ L₁ : Locations} {inv sinv : RPre}
    [hInv : IsInvariant L₀ L₁ inv] [hSInv : SemiInvariant L₀ L₁ sinv] :
    IsInvariant L₀ L₁ (inv ⋊ sinv) where
  left_local := fun h₀ h₀' h₁ hloc ⟨hinv, hsinv⟩ =>
    ⟨hInv.left_local h₀ h₀' h₁ hloc hinv, hSInv.left_reads h₀ h₀' h₁ hloc hsinv⟩
  right_local := fun h₀ h₁ h₁' hloc ⟨hinv, hsinv⟩ =>
    ⟨hInv.right_local h₀ h₁ h₁' hloc hinv, hSInv.right_reads h₀ h₁ h₁' hloc hsinv⟩

/-! ## Additional Location Couplings -/

/-- Predicate about a single location on the left heap -/
def single_lhs' (l : Location) (P : l.ty → Prop) : RPre :=
  fun h₀ _ => P (h₀.get l)

/-- Predicate about a single location on the right heap -/
def single_rhs' (l : Location) (P : l.ty → Prop) : RPre :=
  fun _ h₁ => P (h₁.get l)

/-- Cross-heap coupling: relate values at locations across heaps.
    Unlike `couple_cross` in Coupling.lean, this version doesn't require type equality. -/
def couple_cross' (l₀ l₁ : Location) (R : l₀.ty → l₁.ty → Prop) : RPre :=
  fun h₀ h₁ => R (h₀.get l₀) (h₁.get l₁)

/-- Synchronized location: same value on both sides.
    Deprecated alias for `syncsAt`. -/
@[deprecated syncsAt (since := "2026-02-13")]
abbrev syncs' (l : Location) : RPre := syncsAt l

/-! ## Semi-Invariant Instances for Additional Couplings -/

/-- single_lhs' is a semi-invariant for L₀ containing l -/
theorem single_lhs'_SemiInvariant (l : Location) (P : l.ty → Prop)
    (L₀ L₁ : Locations) (hl : l ∈ L₀) :
    SemiInvariant L₀ L₁ (single_lhs' l P) where
  left_reads := fun h₀ h₀' _ hloc hp => by
    simp only [single_lhs'] at hp ⊢; rw [← hloc l hl]; exact hp
  right_reads := fun _ _ _ _ hp => hp

/-- single_rhs' is a semi-invariant for L₁ containing l -/
theorem single_rhs'_SemiInvariant (l : Location) (P : l.ty → Prop)
    (L₀ L₁ : Locations) (hl : l ∈ L₁) :
    SemiInvariant L₀ L₁ (single_rhs' l P) where
  left_reads := fun _ _ _ _ hp => hp
  right_reads := fun _ h₁ h₁' hloc hp => by
    simp only [single_rhs'] at hp ⊢; rw [← hloc l hl]; exact hp

/-- couple_cross' is a semi-invariant when both locations are in respective sets -/
theorem couple_cross'_SemiInvariant (l₀ l₁ : Location)
    (R : l₀.ty → l₁.ty → Prop) (L₀ L₁ : Locations)
    (hl₀ : l₀ ∈ L₀) (hl₁ : l₁ ∈ L₁) :
    SemiInvariant L₀ L₁ (couple_cross' l₀ l₁ R) where
  left_reads := fun h₀ h₀' h₁ hloc hR => by
    simp only [couple_cross'] at hR ⊢; rw [← hloc l₀ hl₀]; exact hR
  right_reads := fun h₀ h₁ h₁' hloc hR => by
    simp only [couple_cross'] at hR ⊢; rw [← hloc l₁ hl₁]; exact hR

/-! ## Heap Agreement Invariants -/

/-- Heap ignore: heaps are equal except on specified locations.
    This is useful when protocols use private state that differs between
    the left and right executions.

    **Important Design Note:**
    This definition talks about locations OUTSIDE L (requiring equality for l ∉ L),
    which is fundamentally incompatible with the `IsInvariant L₀ L₁` framework:
    - `IsInvariant` requires that if heaps agree on L₀/L₁, the invariant transfers
    - `heap_ignore L` reads from ALL locations outside L
    - When l ∉ L and l ∉ L₀, we have no information about h₀'.get l

    For this reason, `heap_ignore` cannot be made into a sound `IsInvariant` instance.
    Use `heap_agree` (below) instead, which uses a positive formulation that works
    correctly with the `IsInvariant` framework. -/
def heap_ignore (L : Locations) : RPre :=
  fun h₀ h₁ => ∀ l, l ∉ L → h₀.get l = h₁.get l

/-! ## Positive Agreement Invariant -/

/-- Heaps agree on a specific set of locations (positive formulation) -/
def heap_agree (L : Locations) : RPre :=
  fun h₀ h₁ => ∀ l ∈ L, h₀.get l = h₁.get l

/-- heap_agree L is an invariant for (L, L) -/
instance heap_agree_IsInvariant (L : Locations) : IsInvariant L L (heap_agree L) where
  left_local := fun h₀ h₀' h₁ hloc hagree => by
    intro l hl
    have heq₁ : h₀.get l = h₁.get l := hagree l hl
    have heq₀ : h₀.get l = h₀'.get l := hloc l hl
    rw [← heq₀, heq₁]
  right_local := fun h₀ h₁ h₁' hloc hagree => by
    intro l hl
    have heq₁ : h₀.get l = h₁.get l := hagree l hl
    have heq₀ : h₁.get l = h₁'.get l := hloc l hl
    rw [heq₁, heq₀]

/-! ## Get/Put Preservation -/

/-- Getting a value preserves semi-invariants -/
theorem get_preserves_semi {L₀ L₁ : Locations} {sinv : RPre}
    [SemiInvariant L₀ L₁ sinv] (l : Location) (h₀ h₁ : Heap)
    (hsinv : sinv h₀ h₁) : sinv h₀ h₁ := hsinv

/-- Putting a value on both sides preserves syncsAt if values are equal -/
theorem put_both_preserves_syncsAt (l : Location) (v : l.ty)
    (h₀ h₁ : Heap) : syncsAt l (h₀.set l v) (h₁.set l v) :=
  syncsAt_set_both l v h₀ h₁

/-- Putting a value on left updates rem_lhs -/
theorem put_lhs_updates_rem (l : Location) (v : l.ty)
    (h₀ h₁ : Heap) : rem_lhs l v (h₀.set l v) h₁ := by
  simp only [rem_lhs, Heap.get_set_same]

/-- Putting a value on right updates rem_rhs -/
theorem put_rhs_updates_rem (l : Location) (v : l.ty)
    (h₀ h₁ : Heap) : rem_rhs l v h₀ (h₁.set l v) := by
  simp only [rem_rhs, Heap.get_set_same]

/-! ## Restoring Invariants After Writes -/

/-- After writing equal values to both sides, sync is restored -/
theorem restore_sync_after_write (l : Location) (v : l.ty)
    (h₀ h₁ : Heap) : syncsAt l (h₀.set l v) (h₁.set l v) :=
  syncsAt_set_both l v h₀ h₁

/-- Writing on one side and syncing restores remembered values -/
theorem restore_rem_from_sync {l : Location} {v : l.ty}
    {h₀ h₁ : Heap} (hsync : syncsAt l h₀ h₁) (hrem_l : rem_lhs l v h₀ h₁) :
    rem_rhs l v h₀ h₁ := by
  simp only [rem_rhs, rem_lhs, syncsAt] at *
  rw [← hsync, hrem_l]

end CatCrypt.Invariant

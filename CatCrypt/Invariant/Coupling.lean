/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Invariant.Basic

/-!
# Location Couplings for Relational Reasoning

This file defines location-specific couplings - relations between specific
locations across the left and right heaps. These are used as semi-invariants
that hold for specific locations.

## Main definitions

* `syncs` - Two locations are synchronized (have equal values)
* `rem_lhs` / `rem_rhs` - Remembered values on left/right side
* `single_lhs` / `single_rhs` - Predicate about single location
* `couple_cross` - Relation across left and right locations

## Usage

Location couplings are composed with invariants using `⋊` to build
more precise relational specifications. The `ssprove_sync` and
`ssprove_restore` tactics manipulate these couplings.

## References

* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
* CatCrypt: theories/Crypt/package/pkg_heap_comp.v
-/

namespace CatCrypt.Invariant

open CatCrypt.Core
open CatCrypt.Relational
open CatCrypt.Package

/-! ## Synchronization -/

/-- Two locations are synchronized: they have equal values -/
def syncs (l₀ l₁ : Location) (hty : l₀.ty = l₁.ty) : RPre := fun h₀ h₁ =>
  h₀.get l₀ = cast (by rw [hty]) (h₁.get l₁)

/-- Same location synchronized on both sides -/
def syncsAt (l : Location) : RPre := fun h₀ h₁ => h₀.get l = h₁.get l

theorem syncsAt_def (l : Location) (h₀ h₁ : Heap) :
    syncsAt l h₀ h₁ ↔ h₀.get l = h₁.get l := Iff.rfl

/-! ## Remembered Values -/

/-- Remembered value on the left: the left heap has value v at location l -/
def rem_lhs (l : Location) (v : l.ty) : RPre := fun h₀ _ => h₀.get l = v

/-- Remembered value on the right: the right heap has value v at location l -/
def rem_rhs (l : Location) (v : l.ty) : RPre := fun _ h₁ => h₁.get l = v

/-- Remembered value in a specific invariant (left or right) -/
inductive Side | left | right

def rem_inv (s : Side) (l : Location) (v : l.ty) : RPre :=
  match s with
  | Side.left => rem_lhs l v
  | Side.right => rem_rhs l v

/-- Get the other side -/
def Side.other : Side → Side
  | left => right
  | right => left

/-! ## Single-Location Predicates -/

/-- Predicate about a single location on the left -/
def single_lhs (l : Location) (P : l.ty → Prop) : RPre := fun h₀ _ => P (h₀.get l)

/-- Predicate about a single location on the right -/
def single_rhs (l : Location) (P : l.ty → Prop) : RPre := fun _ h₁ => P (h₁.get l)

/-! ## Location Couplings -/

/-- Relation between two locations on the left heap -/
def couple_lhs (l₀ l₁ : Location) (R : l₀.ty → l₁.ty → Prop) : RPre :=
  fun h₀ _ => R (h₀.get l₀) (h₀.get l₁)

/-- Relation between two locations on the right heap -/
def couple_rhs (l₀ l₁ : Location) (R : l₀.ty → l₁.ty → Prop) : RPre :=
  fun _ h₁ => R (h₁.get l₀) (h₁.get l₁)

/-- Relation between a location on left and a location on right -/
def couple_cross (l₀ l₁ : Location) (hty : l₀.ty = l₁.ty)
    (R : l₀.ty → l₁.ty → Prop) : RPre :=
  fun h₀ h₁ => R (h₀.get l₀) (h₁.get l₁)

/-- Equality coupling across sides (same as syncs) -/
def eqCross (l₀ l₁ : Location) (hty : l₀.ty = l₁.ty) : RPre :=
  couple_cross l₀ l₁ hty (fun v₀ v₁ => v₀ = cast (by rw [hty]) v₁)

/-! ## Triple Couplings -/

/-- Relation between three locations on the left -/
def triple_lhs (l₀ l₁ l₂ : Location) (R : l₀.ty → l₁.ty → l₂.ty → Prop) : RPre :=
  fun h₀ _ => R (h₀.get l₀) (h₀.get l₁) (h₀.get l₂)

/-- Relation between three locations on the right -/
def triple_rhs (l₀ l₁ l₂ : Location) (R : l₀.ty → l₁.ty → l₂.ty → Prop) : RPre :=
  fun _ h₁ => R (h₁.get l₀) (h₁.get l₁) (h₁.get l₂)

/-! ## Set Predicates (for writes) -/

/-- Setting a value on the left, used in put rules -/
def set_lhs (l : Location) (v : l.ty) (P : RPre) : RPre :=
  fun h₀ h₁ => P (h₀.set l v) h₁

/-- Setting a value on the right, used in put rules -/
def set_rhs (l : Location) (v : l.ty) (P : RPre) : RPre :=
  fun h₀ h₁ => P h₀ (h₁.set l v)

/-! ## Lemmas -/

theorem syncsAt_set_both (l : Location) (v : l.ty) (h₀ h₁ : Heap) :
    syncsAt l (h₀.set l v) (h₁.set l v) := by simp only [syncsAt, Heap.get_set_same]

theorem rem_lhs_intro (l : Location) (h₀ h₁ : Heap) :
    rem_lhs l (h₀.get l) h₀ h₁ := rfl

theorem rem_rhs_intro (l : Location) (h₀ h₁ : Heap) :
    rem_rhs l (h₁.get l) h₀ h₁ := rfl

/-- If locations are synced and we remember on one side, we can remember the same on the other -/
theorem rem_sync {l : Location} {v : l.ty} {s : Side} {h₀ h₁ : Heap}
    (hrem : rem_inv s l v h₀ h₁) (hsync : syncsAt l h₀ h₁) :
    rem_inv s.other l v h₀ h₁ := by
  cases s <;> simp only [rem_inv, rem_lhs, rem_rhs, Side.other] at *
  · exact hsync.symm.trans hrem
  · exact hsync.trans hrem

/-! ## Proof helpers -/

/-- Mark that a location coupling is proven by the precondition -/
class ProvenBy (coupling : RPre) (pre : RPre) : Prop where
  holds : ∀ h₀ h₁, pre h₀ h₁ → coupling h₀ h₁

/-- If coupling is part of the precondition conjunction, it's proven -/
instance ProvenBy_left (coupling inv : RPre) : ProvenBy coupling (coupling ⋊ inv) where
  holds := fun _ _ ⟨hc, _⟩ => hc

instance ProvenBy_right (coupling other inv : RPre) [ProvenBy coupling inv] :
    ProvenBy coupling (other ⋊ inv) where
  holds := fun h₀ h₁ ⟨_, hinv⟩ => ProvenBy.holds h₀ h₁ hinv

/-- Helper to extract proven coupling -/
theorem coupling_from_pre {coupling pre : RPre} [ProvenBy coupling pre]
    {h₀ h₁ : Heap} (hpre : pre h₀ h₁) : coupling h₀ h₁ :=
  ProvenBy.holds h₀ h₁ hpre

end CatCrypt.Invariant

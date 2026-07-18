/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Relational.Basic
import CatCryptCore.Package.Locations

/-!
# Invariants for Relational Reasoning

This file defines invariants - predicates on heap pairs that are preserved
by package operations. Invariants are central to proving perfect indistinguishability.

## Main definitions

* `IsInvariant` - A class for valid invariants on location pairs
* `heapEq` - The simplest invariant: heap equality
* `trueInv` - The trivial invariant that always holds

## Usage

When relating two packages up to an invariant, we choose an invariant and prove
that all operations preserve it while establishing equal behavior.

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
* SSProve: theories/Crypt/package/pkg_invariants.v
-/

namespace CatCrypt.Invariant

open CatCrypt.Core
open CatCrypt.Relational
open CatCrypt.Package

/-! ## Invariant Class -/

/-- An invariant is a precondition that is well-formed with respect to location sets.
    It only talks about locations in L₀ (for the left heap) and L₁ (for the right heap).

    The key property is that the invariant should be:
    1. Preserved by operations that only access the declared locations
    2. Restorable after writes to declared locations -/
class IsInvariant (L₀ L₁ : Locations) (inv : RPre) : Prop where
  /-- The invariant only depends on locations in L₀ for the left heap -/
  left_local : ∀ h₀ h₀' h₁, (∀ l ∈ L₀, h₀.get l = h₀'.get l) → inv h₀ h₁ → inv h₀' h₁
  /-- The invariant only depends on locations in L₁ for the right heap -/
  right_local : ∀ h₀ h₁ h₁', (∀ l ∈ L₁, h₁.get l = h₁'.get l) → inv h₀ h₁ → inv h₀ h₁'

/-! ## Standard Invariants -/

/-- Heap equality invariant: the heaps are equal -/
def heapEq : RPre := eqPre

/-!
### Note on heapEq and IsInvariant

Heap equality (`heapEq`) is **not** a proper invariant for the locality framework.

The `IsInvariant` class requires that if heaps agree on L₀/L₁, then the
invariant is preserved. But `heapEq` requires complete heap equality,
not just equality on specific locations.

For empty location sets, the locality hypothesis `∀ l ∈ ∅, ...` is vacuously
true, giving us no information about the relationship between h₀ and h₀'.
We cannot prove h₀' = h₀ from this.

**Design Decision:** We intentionally do NOT provide an `IsInvariant` instance
for `heapEq` with empty location sets. Users should use:
- `trueInv` for cases where no invariant is needed
- Location-specific invariants like `syncsAt` for tracking equality at specific locations

In the original CatCrypt/Rocq, the heap-equality case is handled specially,
outside the locality framework.
For Lean 4, we follow the same pattern: use `rHoare_eq` (defined in Rules.lean) for
the heap equality case directly, bypassing the `IsInvariant` machinery.
-/

/-- True invariant: always holds (used when location sets are empty) -/
def trueInv : RPre := truePre

instance trueInv_IsInvariant (L₀ L₁ : Locations) : IsInvariant L₀ L₁ trueInv where
  left_local := fun _ _ _ _ _ => trivial
  right_local := fun _ _ _ _ _ => trivial

/-! ## Invariant Combinators -/

/-- Conjunction of invariants -/
def andInv (inv₁ inv₂ : RPre) : RPre := andPre inv₁ inv₂

/-- Conjunction of invariants is an invariant.

    The mathematical proof is straightforward: if `hloc : ∀ l ∈ L₀, h₀.get l = h₀'.get l`
    and both inv₁ and inv₂ are invariants for L₀, L₁, then both `left_local` properties
    apply with the same `hloc`.

    Note: Earlier versions of this codebase had universe polymorphism issues here.
    These were resolved by fixing Location.ty to Type (Type 0) in Core/Location.lean. -/
instance andInv_IsInvariant {L₀ L₁ : Locations} {inv₁ inv₂ : RPre}
    [hi₁ : IsInvariant L₀ L₁ inv₁] [hi₂ : IsInvariant L₀ L₁ inv₂] :
    IsInvariant L₀ L₁ (andInv inv₁ inv₂) where
  left_local := fun h₀ h₀' h₁ hloc ⟨hinv₁, hinv₂⟩ =>
    ⟨hi₁.left_local h₀ h₀' h₁ hloc hinv₁, hi₂.left_local h₀ h₀' h₁ hloc hinv₂⟩
  right_local := fun h₀ h₁ h₁' hloc ⟨hinv₁, hinv₂⟩ =>
    ⟨hi₁.right_local h₀ h₁ h₁' hloc hinv₁, hi₂.right_local h₀ h₁ h₁' hloc hinv₂⟩

infixl:65 " ⋊ " => andInv

/-! ## Invariant Operations -/

/-- Setting a location on both sides preserves the invariant
    when the location is outside both L₀ and L₁.

    This is because the invariant only depends on locations in L₀/L₁,
    so writes outside these sets don't affect the invariant.

    **Mathematical proof:**
    1. For any `l' ∈ L₀`, we have `l'.id ≠ l.id` (since `l ∉ L₀` means `l.id ∉ L₀.ids`)
    2. Therefore `(h₀.set l v).get l' = h₀.get l'` (by `get_set_other`)
    3. Apply `left_local` with this agreement to get `inv (h₀.set l v) h₁`
    4. Similarly, apply `right_local` to get `inv (h₀.set l v) (h₁.set l v)`

    Note: Earlier versions of this codebase had universe polymorphism issues here.
    These were resolved by fixing Location.ty to Type (Type 0) in Core/Location.lean. -/
theorem set_preserves_outside {L₀ L₁ : Locations} {inv : RPre} [hInv : IsInvariant L₀ L₁ inv]
    (l : Location) (v : l.ty) (h₀ h₁ : Heap) (hinv : inv h₀ h₁)
    (hl₀ : l ∉ L₀) (hl₁ : l ∉ L₁) : inv (h₀.set l v) (h₁.set l v) := by
  -- l ∉ L₀ means l.id ∉ L₀.ids (by definition of Membership)
  -- Rewrite using mem_iff to work with ids
  rw [Locations.mem_iff] at hl₀ hl₁
  -- First, use left_local to show inv (h₀.set l v) h₁
  have hloc₀ : ∀ l' ∈ L₀, h₀.get l' = (h₀.set l v).get l' := fun l' hl' => by
    -- hl' : l' ∈ L₀ means l'.id ∈ L₀.ids
    rw [Locations.mem_iff] at hl'
    -- hl' : l'.id ∈ L₀.ids, hl₀ : l.id ∉ L₀.ids
    -- So l.id ≠ l'.id
    have hne : l.id ≠ l'.id := fun heq => hl₀ (heq ▸ hl')
    exact (Heap.get_set_other h₀ l l' v hne).symm
  have hinv' : inv (h₀.set l v) h₁ := hInv.left_local h₀ (h₀.set l v) h₁ hloc₀ hinv
  -- Then, use right_local to show inv (h₀.set l v) (h₁.set l v)
  have hloc₁ : ∀ l' ∈ L₁, h₁.get l' = (h₁.set l v).get l' := fun l' hl' => by
    rw [Locations.mem_iff] at hl'
    have hne : l.id ≠ l'.id := fun heq => hl₁ (heq ▸ hl')
    exact (Heap.get_set_other h₁ l l' v hne).symm
  exact hInv.right_local (h₀.set l v) h₁ (h₁.set l v) hloc₁ hinv'

/-! ## Special Invariants for Games -/

/-- Invariant for equal initial state: heaps are equal -/
def eqInit : RPre := eqPre

end CatCrypt.Invariant

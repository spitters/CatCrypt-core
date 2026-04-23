/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Invariant
import CatCrypt.Relational.Rules

/-!
# Invariant Tactics

This file provides tactics for working with invariants in relational proofs,
including proving invariant preservation and extracting relation hypotheses.

## Main tactics

* `ssprove_invariant` - prove IsInvariant goals using common patterns
* `ssprove_invariant_step` - discharge per-operation invariant preservation goals
* `ssprove_rem_rel` - extract hypotheses from remembered/synchronized values
* `ssprove_restore` - restore invariant after writes

## Heap agreement modulo location sets

* `heap_agree_except` - heaps agree except on a set of locations (useful for
  proving that operations on private state don't affect the invariant)
* Preservation rules for sample, get, set operations

## Implementation Notes

### ssprove_invariant

The `ssprove_invariant` tactic tries the following strategies in order:
1. `trueInv_IsInvariant` - trivial invariant that always holds
2. `heap_agree_IsInvariant` - heap agreement on specified locations
3. `IsInvariant_inv_conj` - conjunction of invariant with semi-invariant
4. `andInv_IsInvariant` - conjunction of two invariants
5. User-provided assumptions

### ssprove_rem_rel

The `ssprove_rem_rel` tactic extracts information from location couplings:
- `rem_lhs l v` - the left heap has value v at location l
- `rem_rhs l v` - the right heap has value v at location l
- `syncsAt l` - both heaps have the same value at location l

When both `rem_lhs l v` and `syncsAt l` hold, we can derive `rem_rhs l v`.

## References

* CatCrypt: theories/Crypt/package/pkg_user_util.v
* CatCrypt: theories/Crypt/package/pkg_invariants.v
* EasyCrypt: `auto`/`sp`/`wp` for invariant preservation
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob CatCrypt.Invariant

/-! ## Heap Agreement Modulo Locations

These definitions and lemmas support proving that operations on private
state don't break an invariant on shared state. This is the key pattern
for crypto proofs where packages have disjoint state. -/

/-- Heap equivalence modulo a set of location IDs.
    Two heaps agree except possibly at locations in L.

    This is the "frame" invariant: L represents the "private" locations
    that may differ, and everything else must be equal. -/
def heap_agree_except (L : Finset Nat) : RPre :=
  fun h₁ h₂ => ∀ ℓ : Location, ℓ.id ∉ L → h₁.get ℓ = h₂.get ℓ

/-! ### Preservation rules for heap_agree_except -/

/-- Sampling preserves heap_agree_except (sampling doesn't touch the heap). -/
theorem heap_agree_except_sample (L : Finset Nat) (α : Type*) [Fintype α] [Nonempty α] :
    rHoare (heap_agree_except L) (SPComp.sample α) (SPComp.sample α)
      (fun a₁ h₁ a₂ h₂ => heap_agree_except L h₁ h₂ ∧ a₁ = a₂) := by
  apply rHoare_sample_same

/-- Getting from a location not in L gives equal values. -/
theorem heap_agree_except_get (L : Finset Nat) (ℓ : Location) (hℓ : ℓ.id ∉ L) :
    rHoare (heap_agree_except L) (SPComp.get ℓ) (SPComp.get ℓ)
      (fun a₁ h₁ a₂ h₂ => heap_agree_except L h₁ h₂ ∧ a₁ = a₂) := by
  apply rHoare_get_sync
  intro h₁ h₂ hagree
  exact hagree ℓ hℓ

/-- Setting a location IN L (private state) with arbitrary values preserves the invariant. -/
theorem heap_agree_except_set_in (L : Finset Nat) (ℓ : Location) (hℓ : ℓ.id ∈ L)
    (v₁ v₂ : ℓ.ty) :
    rHoare (heap_agree_except L) (SPComp.set ℓ v₁) (SPComp.set ℓ v₂)
      (fun _ h₁ _ h₂ => heap_agree_except L h₁ h₂) := by
  intro h₁ h₂ hagree
  simp only [SPComp.set_def]
  apply liftR_pure
  intro ℓ' hℓ'
  simp only [Heap.get_set_other h₁ ℓ ℓ' v₁ (fun heq => hℓ' (heq ▸ hℓ)),
             Heap.get_set_other h₂ ℓ ℓ' v₂ (fun heq => hℓ' (heq ▸ hℓ))]
  exact hagree ℓ' hℓ'

/-- Setting the same value on both sides preserves the invariant (for any location). -/
theorem heap_agree_except_set_same (L : Finset Nat) (ℓ : Location) (v : ℓ.ty) :
    rHoare (heap_agree_except L) (SPComp.set ℓ v) (SPComp.set ℓ v)
      (fun _ h₁ _ h₂ => heap_agree_except L h₁ h₂) := by
  intro h₁ h₂ hagree
  simp only [SPComp.set_def]
  apply liftR_pure
  intro ℓ' hℓ'
  by_cases heq : ℓ.id = ℓ'.id
  · -- Same id: both sides get the newly written (encoded) value
    unfold Heap.get Heap.set
    rw [show ℓ'.id = ℓ.id from heq.symm]
    simp [Finmap.lookup_insert]
  · -- Different id: write doesn't affect this location
    rw [Heap.get_set_other h₁ ℓ ℓ' v heq, Heap.get_set_other h₂ ℓ ℓ' v heq]
    exact hagree ℓ' hℓ'

/-- Getting from any location preserves the invariant. -/
theorem heap_agree_except_get_any (L : Finset Nat) (ℓ : Location) :
    rHoare (heap_agree_except L) (SPComp.get ℓ) (SPComp.get ℓ)
      (fun _ h₁ _ h₂ => heap_agree_except L h₁ h₂) := by
  intro h₁ h₂ hagree
  simp only [SPComp.get_def]
  apply liftR_pure
  exact hagree

/-- Pure/return preserves the invariant. -/
theorem heap_agree_except_ret {α : Type*} (L : Finset Nat) (a : α) :
    rHoare (heap_agree_except L) (pure a : SPComp α) (pure a : SPComp α)
      (fun _ h₁ _ h₂ => heap_agree_except L h₁ h₂) := by
  apply rHoare_ret
  intro _ _ h; exact h

end CatCrypt.Relational

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Invariant
open CatCrypt.Relational
open CatCrypt.Core

/-! ## ssprove_invariant Tactic -/

/-- `ssprove_invariant` is a tactic for proving `IsInvariant` goals.

The tactic attempts to prove that a predicate is a valid invariant by trying:
1. `trueInv_IsInvariant` - the trivial invariant
2. `heap_agree_IsInvariant` - heap agreement invariants
3. `IsInvariant_inv_conj` - conjunction with semi-invariants (recursive)
4. `andInv_IsInvariant` - conjunction of invariants
5. Type class inference
6. Direct assumptions

Example:
```lean
-- Proving that trueInv is an invariant
example : IsInvariant L₀ L₁ trueInv := by ssprove_invariant

-- Proving that heap_agree is an invariant
example : IsInvariant L L (heap_agree L) := by ssprove_invariant

-- Proving conjunction invariants
example [IsInvariant L₀ L₁ inv] [SemiInvariant L₀ L₁ sinv] :
    IsInvariant L₀ L₁ (inv ⋊ sinv) := by ssprove_invariant
```
-/
macro "ssprove_invariant" : tactic => `(tactic| (
  first
  -- Try direct instances
  | exact trueInv_IsInvariant _ _
  | exact heap_agree_IsInvariant _
  -- Try type class inference
  | infer_instance
  -- Try assumption
  | assumption
))

/-- `ssprove_invariant!` is a more aggressive version that uses `decide` for decidable goals. -/
macro "ssprove_invariant!" : tactic => `(tactic| (
  first
  | exact trueInv_IsInvariant _ _
  | exact heap_agree_IsInvariant _
  | infer_instance
  | assumption
  | decide
))

/-- `ssprove_invariant_step` discharges per-operation invariant preservation goals
for `heap_agree_except`.

This tactic tries all preservation rules for `heap_agree_except`:
- Sample (always preserves)
- Get (always preserves)
- Set on private location (arbitrary values)
- Set on shared location (same value)
- Sync and ret rules

Example:
```lean
-- Given goal: rHoare (heap_agree_except L) (SPComp.sample α) (SPComp.sample α) Ψ
ssprove_invariant_step
```
-/
macro "ssprove_invariant_step" : tactic => `(tactic| (
  first
  | apply heap_agree_except_sample
  | apply heap_agree_except_get <;> decide
  | apply heap_agree_except_set_in <;> decide
  | apply heap_agree_except_set_same
  | apply heap_agree_except_get_any
  | apply heap_agree_except_ret
  | apply rHoare_sample_same
  | apply rHoare_ret_same
))

/-! ## ssprove_rem_rel Tactic -/

/-- `ssprove_rem_rel` extracts relation hypotheses from remembered values and syncs.

Given hypotheses about `rem_lhs`, `rem_rhs`, and `syncsAt`, this tactic
derives additional hypotheses about the relationship between heap values.

**Key derivations:**
- From `rem_lhs l v` and `syncsAt l`, derive `h₀.get l = h₁.get l` and `h₁.get l = v`
- From `rem_rhs l v` and `syncsAt l`, derive `h₀.get l = h₁.get l` and `h₀.get l = v`
- From `rem_lhs l v` alone, derive `h₀.get l = v`
- From `rem_rhs l v` alone, derive `h₁.get l = v`
- From `syncsAt l` alone, derive `h₀.get l = h₁.get l`

Example:
```lean
example (hrem : rem_lhs l v h₀ h₁) (hsync : syncsAt l h₀ h₁) : h₁.get l = v := by
  ssprove_rem_rel
```
-/
elab "ssprove_rem_rel" : tactic => do
  evalTactic (← `(tactic|
    -- Unfold the coupling definitions and simplify
    simp only [
      rem_lhs, rem_rhs, syncsAt, syncs, Side.other, rem_inv,
      single_lhs, single_rhs, couple_cross, couple_cross', couple_lhs, couple_rhs,
      heap_agree, heap_ignore, set_lhs, set_rhs,
      andInv, andPre, truePre, eqPre
    ] at *
    -- Try various finishing tactics
    <;> first
    | exact Eq.symm (by assumption)
    | exact Eq.trans (by assumption) (by assumption)
    | exact Eq.trans (Eq.symm (by assumption)) (by assumption)
    | assumption
    | rfl
  ))

/-- `ssprove_rem_rel_intro` introduces and names the extracted relations.

This variant names the derived hypotheses for later use.
-/
macro "ssprove_rem_rel_intro" : tactic => `(tactic| (
  simp only [
    rem_lhs, rem_rhs, syncsAt, syncs, rem_inv, Side.other,
    single_lhs, single_rhs, couple_cross, couple_cross', couple_lhs, couple_rhs,
    heap_agree, heap_ignore, set_lhs, set_rhs,
    andInv, andPre, truePre, eqPre
  ] at *
))

/-! ## ssprove_restore Tactic -/

/-- `ssprove_restore` is a tactic for restoring an invariant after writes.

After a sequence of writes that may have temporarily broken the invariant,
this tactic attempts to show that the final state satisfies the invariant.

Common patterns:
1. Writes that "undo" previous changes
2. Writes that establish a synchronized state
3. Combining partial invariants

Example:
```lean
-- After setting the same value on both sides, syncsAt is restored
example : syncsAt l (h₀.set l v) (h₁.set l v) := by ssprove_restore

-- After writes that maintain invariant structure
example (hinv : inv h₀ h₁) : inv (h₀.set l v) (h₁.set l v) := by
  ssprove_restore
```
-/
macro "ssprove_restore" : tactic => `(tactic| (
  first
  | trivial
  | assumption
  -- For syncsAt after setting same value on both sides
  | exact syncsAt_set_both _ _ _ _
  -- For rem_lhs/rem_rhs after setting
  | exact put_lhs_updates_rem _ _ _ _
  | exact put_rhs_updates_rem _ _ _ _
  -- Unfold and simplify
  | simp only [
      heapEq, eqPre, trueInv, truePre, andInv, andPre,
      syncsAt, rem_lhs, rem_rhs, heap_agree,
      Heap.get_set_same, Heap.get_set_other
    ] at * <;> first
    | trivial
    | assumption
    | rfl
    | constructor <;> (first | trivial | assumption | rfl)
))

/-! ## ssprove_invariant_intro Tactic -/

/-- `ssprove_invariant_intro` introduces invariant hypotheses into context.

This is useful at the start of a relational proof to set up the
invariant assumptions. It introduces the heap pair and the invariant hypothesis.

Example:
```lean
theorem example : rHoare inv c₁ c₂ post := by
  ssprove_invariant_intro
  -- Now have: h₀ h₁ : Heap, hinv : inv h₀ h₁
```
-/
macro "ssprove_invariant_intro" : tactic => `(tactic| (
  intro _ _ _
))

/-- `ssprove_invariant_intro_named h₀ h₁ hinv` introduces with specific names. -/
macro "ssprove_invariant_intro_named" h₀:ident h₁:ident hinv:ident : tactic =>
  `(tactic| intro $h₀ $h₁ $hinv)

/-! ## Helper Tactics -/

/-- `ssprove_split_inv` splits a conjunction invariant into its components. -/
macro "ssprove_split_inv" : tactic => `(tactic| (
  simp only [andInv, andPre] at *
  <;> (try constructor)
  <;> assumption
))

/-- `ssprove_extract_sync l` extracts synchronization information for location l. -/
macro "ssprove_extract_sync" : tactic => `(tactic| (
  simp only [syncsAt, rem_lhs, rem_rhs] at *
))

/-! ## Configuration -/

/-- Configuration for invariant tactics -/
structure InvariantConfig where
  /-- Whether to automatically apply locality -/
  autoLocality : Bool := true
  /-- Whether to split conjunction invariants -/
  splitAnd : Bool := true
  /-- Maximum depth for recursive tactics -/
  maxDepth : Nat := 10
  /-- Whether to unfold definitions aggressively -/
  unfoldDefs : Bool := false

/-! ## Simp Lemmas for Invariant Reasoning -/

-- Register lemmas for the simp set used by invariant tactics
attribute [simp] syncsAt_set_both
attribute [simp] rem_lhs_intro
attribute [simp] rem_rhs_intro

end CatCrypt.Tactics

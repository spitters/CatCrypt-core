/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Countable.Defs

/-!
# Atoms for Nominal Sets

This file defines atoms, which are abstract names used in nominal set theory.
Atoms are represented as wrapped natural numbers, providing a countably infinite
supply of distinguishable names.

## Main definitions

* `Atom` - The type of atoms (wrapped naturals)
* `Atom.fresh` - Generate a fresh atom not in a given finite set
* `Atom.freshN` - Generate n fresh atoms

## References

* [Pitts, *Nominal Sets*]
* [SSProve Nominal Package](https://github.com/SSProve/ssprove)
-/

namespace CatCrypt.Nominal

/-- Atoms are abstract names, represented as wrapped natural numbers.
    This provides a countably infinite supply of distinguishable names. -/
structure Atom where
  val : ℕ
  deriving DecidableEq, Hashable, Repr, Ord

namespace Atom

@[ext]
theorem ext {a b : Atom} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact h

instance : Inhabited Atom := ⟨⟨0⟩⟩

/-- Coercion to natural numbers -/
instance : Coe Atom ℕ := ⟨Atom.val⟩

/-- Linear order on atoms inherited from naturals -/
instance : LinearOrder Atom :=
  LinearOrder.lift' Atom.val (fun _ _ h => Atom.ext h)

instance : OrderBot Atom where
  bot := ⟨0⟩
  bot_le a := Nat.zero_le a.val

/-- Atoms are countable -/
instance : Countable Atom := ⟨⟨Atom.val, fun _ _ h => Atom.ext h⟩⟩

/-- Constructor from natural number -/
def ofNat (n : ℕ) : Atom := ⟨n⟩

@[simp]
theorem ofNat_val (n : ℕ) : (ofNat n).val = n := rfl

@[simp]
theorem val_ofNat (a : Atom) : ofNat a.val = a := rfl

/-- Offset: one plus the maximum in a set, used for fresh generation -/
noncomputable def offset (s : Finset Atom) : ℕ :=
  if h : s.Nonempty then s.sup' h Atom.val + 1 else 0

theorem offset_pos_of_nonempty {s : Finset Atom} (h : s.Nonempty) :
    0 < offset s := by
  simp only [offset, h, ↓reduceDIte]
  omega

/-- Fresh atom: the smallest atom not in the given set -/
noncomputable def fresh (s : Finset Atom) : Atom :=
  ⟨offset s⟩

/-- The fresh atom is not in the original set -/
theorem fresh_not_mem (s : Finset Atom) : fresh s ∉ s := by
  intro h
  simp only [fresh, offset] at h
  split_ifs at h with hne
  · have hle := Finset.le_sup' Atom.val h
    simp only at hle
    exact Nat.not_succ_le_self _ hle
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h
    exact Finset.notMem_empty _ h

/-- Fresh atom has value greater than all atoms in the set -/
theorem fresh_val_gt {s : Finset Atom} {a : Atom} (ha : a ∈ s) :
    a.val < (fresh s).val := by
  simp only [fresh, offset]
  have hne : s.Nonempty := ⟨a, ha⟩
  simp only [hne, ↓reduceDIte]
  have hle := Finset.le_sup' Atom.val ha
  omega

/-- Generate n fresh atoms not in the given set -/
noncomputable def freshN (s : Finset Atom) (n : ℕ) : Finset Atom :=
  Finset.image (fun i => ⟨offset s + i⟩) (Finset.range n)

theorem freshN_card (s : Finset Atom) (n : ℕ) : (freshN s n).card = n := by
  simp only [freshN]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range n
  · intro i j h
    simp only [mk.injEq] at h
    omega

theorem freshN_disjoint (s : Finset Atom) (n : ℕ) :
    Disjoint s (freshN s n) := by
  rw [Finset.disjoint_left]
  intro a ha hfresh
  simp only [freshN, Finset.mem_image, Finset.mem_range] at hfresh
  obtain ⟨i, _, rfl⟩ := hfresh
  have hlt := fresh_val_gt ha
  simp only [fresh] at hlt
  omega

/-- Two distinct atoms -/
def a₀ : Atom := ⟨0⟩
def a₁ : Atom := ⟨1⟩

theorem a₀_ne_a₁ : a₀ ≠ a₁ := by decide

end Atom

end CatCrypt.Nominal

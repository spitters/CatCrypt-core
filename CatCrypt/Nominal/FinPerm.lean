/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Nominal.Atom
import Mathlib.GroupTheory.Perm.Basic

/-!
# Finite Permutations

This file defines finite permutations of atoms - permutations that only move
finitely many atoms. This is the key structure for nominal set theory.

## Main definitions

* `FinPerm` - Finite permutations (bijections on atoms with finite support)
* `FinPerm.swap` - Transposition of two atoms

## Implementation notes

Since `Atom` is infinite (not `Fintype`), we cannot use Mathlib's `Perm.support`
directly (which requires `Fintype`). Instead, we define a predicate
`IsFinitelySupported` that states a permutation has finite support, and define
`FinPerm` as the subtype of permutations satisfying this predicate.

Key insight: in nominal set theory, we only work with *finitely-supported*
permutations, even though the set of atoms is infinite.

## References

* [Pitts, *Nominal Sets*], Chapter 2
* SSProve `theories/Crypt/nominal/Nominal.v`
-/

namespace CatCrypt.Nominal

open Equiv

/-- A permutation is finitely supported if there exists a finite set outside
    of which it acts as the identity. -/
def IsFinitelySupported (π : Perm Atom) : Prop :=
  ∃ s : Finset Atom, ∀ a, a ∉ s → π a = a

/-- The type of finitely-supported permutations of atoms. -/
def FinPerm := { π : Perm Atom // IsFinitelySupported π }

namespace FinPerm

/-- Coercion to underlying permutation -/
instance : CoeOut FinPerm (Perm Atom) := ⟨Subtype.val⟩

/-- Apply permutation to an atom -/
def apply (π : FinPerm) (a : Atom) : Atom := π.val a

instance : CoeFun FinPerm (fun _ => Atom → Atom) := ⟨apply⟩

@[simp]
theorem apply_def (π : FinPerm) (a : Atom) : π a = π.val a := rfl

theorem val_injective : Function.Injective (Subtype.val : FinPerm → Perm Atom) :=
  Subtype.val_injective

@[ext]
theorem ext {π₁ π₂ : FinPerm} (h : ∀ a, π₁ a = π₂ a) : π₁ = π₂ := by
  apply val_injective
  apply Perm.ext
  intro a
  have := h a
  simp only [apply_def] at this
  exact this

/-- A witness of finite support for a permutation -/
noncomputable def suppWitness (π : FinPerm) : Finset Atom :=
  Classical.choose π.prop

theorem suppWitness_spec (π : FinPerm) : ∀ a, a ∉ π.suppWitness → π a = a :=
  Classical.choose_spec π.prop

/-- Identity permutation -/
def one : FinPerm :=
  ⟨1, ∅, by simp⟩

instance : One FinPerm := ⟨one⟩

@[simp]
theorem one_apply (a : Atom) : (1 : FinPerm) a = a := rfl

@[simp]
theorem one_val : (1 : FinPerm).val = 1 := rfl

/-- Composition of finite permutations -/
def mul (π₁ π₂ : FinPerm) : FinPerm :=
  ⟨π₁.val * π₂.val,
   π₁.suppWitness ∪ π₂.suppWitness, by
     intro a ha
     simp only [Finset.mem_union, not_or] at ha
     simp only [Perm.coe_mul, Function.comp_apply]
     have h2 := π₂.suppWitness_spec a ha.2
     have h1 := π₁.suppWitness_spec a ha.1
     simp only [apply_def] at h2 h1
     rw [h2, h1]⟩

instance : Mul FinPerm := ⟨mul⟩

@[simp]
theorem mul_apply (π₁ π₂ : FinPerm) (a : Atom) : (π₁ * π₂) a = π₁ (π₂ a) := rfl

@[simp]
theorem mul_val (π₁ π₂ : FinPerm) : (π₁ * π₂).val = π₁.val * π₂.val := rfl

/-- Inverse of a finite permutation -/
def inv (π : FinPerm) : FinPerm :=
  ⟨π.val⁻¹, π.suppWitness, by
     intro a ha
     have h := π.suppWitness_spec a ha
     simp only [apply_def] at h
     simp only [Perm.inv_eq_iff_eq]
     exact h.symm⟩

instance : Inv FinPerm := ⟨inv⟩

@[simp]
theorem inv_apply (π : FinPerm) (a : Atom) : π⁻¹ a = π.val.symm a := rfl

@[simp]
theorem inv_val (π : FinPerm) : π⁻¹.val = π.val⁻¹ := rfl

/-- Finite permutations form a group -/
instance : Group FinPerm where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc π₁ π₂ π₃ := by ext a; simp [mul_assoc]
  one_mul π := by ext a; simp
  mul_one π := by ext a; simp
  inv_mul_cancel π := by ext a; simp

/-- Transposition: swap two atoms -/
noncomputable def swap (a b : Atom) : FinPerm :=
  ⟨Equiv.swap a b, if a = b then ∅ else {a, b}, by
     intro c hc
     by_cases hab : a = b
     · simp [hab, Equiv.swap_self]
     · simp only [hab, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
       exact Equiv.swap_apply_of_ne_of_ne hc.1 hc.2⟩

@[simp]
theorem swap_apply_left (a b : Atom) : swap a b a = b := Equiv.swap_apply_left a b

@[simp]
theorem swap_apply_right (a b : Atom) : swap a b b = a := Equiv.swap_apply_right a b

@[simp]
theorem swap_apply_of_ne_of_ne {a b c : Atom} (hca : c ≠ a) (hcb : c ≠ b) :
    swap a b c = c := Equiv.swap_apply_of_ne_of_ne hca hcb

@[simp]
theorem swap_val (a b : Atom) : (swap a b).val = Equiv.swap a b := rfl

@[simp]
theorem swap_self (a : Atom) : swap a a = 1 := by
  ext c; simp [Equiv.swap_self]

theorem swap_comm (a b : Atom) : swap a b = swap b a := by
  ext c; simp [Equiv.swap_comm]

theorem swap_swap (a b : Atom) : swap a b * swap a b = 1 := by
  apply val_injective
  apply Perm.ext
  intro c
  simp only [mul_val, one_val, Perm.coe_mul, Function.comp_apply, swap_val]
  exact Equiv.swap_apply_self a b c

@[simp]
theorem swap_inv (a b : Atom) : (swap a b)⁻¹ = swap a b := by
  have h := swap_swap a b
  calc (swap a b)⁻¹ = (swap a b)⁻¹ * 1 := by rw [mul_one]
    _ = (swap a b)⁻¹ * (swap a b * swap a b) := by rw [h]
    _ = ((swap a b)⁻¹ * swap a b) * swap a b := by rw [mul_assoc]
    _ = 1 * swap a b := by rw [inv_mul_cancel]
    _ = swap a b := by rw [one_mul]

end FinPerm

end CatCrypt.Nominal

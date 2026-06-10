/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Nominal.FinPerm

/-!
# Nominal Sets

This file defines the typeclass for nominal sets - sets equipped with a
permutation action and finite support.

## Main definitions

* `NomSet` - A typeclass for nominal sets (with finite support)

The permutation action uses Mathlib's `MulAction FinPerm α`, giving access to
`π • x` notation, `one_smul`, `mul_smul`, `inv_smul_smul`, `smul_inv_smul`,
orbit/stabilizer theory, etc.

## References

* [Pitts, *Nominal Sets*], Chapters 2-3
* SSProve `theories/Crypt/nominal/Nominal.v`
-/

namespace CatCrypt.Nominal

/-! ## Backward-Compatible Aliases

These aliases provide backward compatibility for code that used the old
`NominalAction` API. They are definitionally equal to the Mathlib equivalents. -/

namespace NominalAction

variable {α : Type*} [MulAction FinPerm α]

/-- Backward-compatible alias for `π • x`. -/
abbrev act (π : FinPerm) (x : α) : α := π • x

@[simp] theorem one_act (x : α) : act (1 : FinPerm) x = x := one_smul FinPerm x

theorem mul_act (π₁ π₂ : FinPerm) (x : α) : act (π₁ * π₂) x = act π₁ (act π₂ x) :=
  mul_smul π₁ π₂ x

@[simp] theorem inv_act_act (π : FinPerm) (x : α) : act π⁻¹ (act π x) = x :=
  inv_smul_smul π x

@[simp] theorem act_inv_act (π : FinPerm) (x : α) : act π (act π⁻¹ x) = x :=
  smul_inv_smul π x

/-- Backward-compatible alias: `act_one` = `one_smul`. -/
theorem act_one (x : α) : act 1 x = x := one_smul FinPerm x

/-- Backward-compatible alias: `act_mul` = `mul_smul`. -/
theorem act_mul (π₁ π₂ : FinPerm) (x : α) : act (π₁ * π₂) x = act π₁ (act π₂ x) :=
  mul_smul π₁ π₂ x

end NominalAction

/-- A set S supports an element x if every permutation fixing S pointwise
    also fixes x. -/
def Supports {α : Type*} [MulAction FinPerm α] (s : Finset Atom) (x : α) : Prop :=
  ∀ π : FinPerm, (∀ a ∈ s, π a = a) → π • x = x

/-- An element is finitely supported if some finite set supports it. -/
def HasFinSupp {α : Type*} [MulAction FinPerm α] (x : α) : Prop :=
  ∃ s : Finset Atom, Supports s x

/-- Typeclass for nominal sets - types where every element has finite support
    and support transforms equivariantly under permutations.

    The equivariance property `supp_equivariant` is essential for reasoning about
    how supports transform under permutation actions, particularly for the move
    operation in nominal CatCrypt. -/
class NomSet (α : Type*) extends MulAction FinPerm α where
  /-- The support of an element -/
  supp : α → Finset Atom
  /-- The support supports the element -/
  supp_supports : ∀ x, Supports (supp x) x
  /-- Support transforms equivariantly: supp(π • x) = π '' (supp x) -/
  supp_equivariant : ∀ x (π : FinPerm), supp (π • x) = (supp x).image (π ·)

namespace NomSet

variable {α : Type*} [NomSet α]

theorem supp_supports' (x : α) : Supports (NomSet.supp x) x :=
  NomSet.supp_supports x

/-- If all atoms in the support are fixed, the element is fixed -/
theorem act_eq_of_supp_fixed (x : α) (π : FinPerm)
    (h : ∀ a ∈ NomSet.supp x, π a = a) : π • x = x :=
  supp_supports' x π h

/-- Support transforms equivariantly -/
theorem supp_act_eq_image (x : α) (π : FinPerm) :
    NomSet.supp (π • x) = (NomSet.supp x).image (π ·) :=
  NomSet.supp_equivariant x π

end NomSet

/-! ## Instances -/

/-- Atoms form a nominal set with the natural action -/
instance : MulAction FinPerm Atom where
  smul := fun π a => π a
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

instance : NomSet Atom where
  supp := fun a => {a}
  supp_supports := fun a _ h => h a (Finset.mem_singleton_self a)
  supp_equivariant := fun a π => by simp only [Finset.image_singleton, HSMul.hSMul, SMul.smul]

/-- Products of MulAction instances are MulAction instances -/
instance {α β : Type*} [MulAction FinPerm α] [MulAction FinPerm β] :
    MulAction FinPerm (α × β) where
  smul := fun π p => (π • p.1, π • p.2)
  one_smul := fun p => Prod.ext (one_smul FinPerm p.1) (one_smul FinPerm p.2)
  mul_smul := fun π₁ π₂ p => Prod.ext (mul_smul π₁ π₂ p.1) (mul_smul π₁ π₂ p.2)

instance {α β : Type*} [NomSet α] [NomSet β] : NomSet (α × β) where
  supp := fun p => NomSet.supp p.1 ∪ NomSet.supp p.2
  supp_supports := fun p π h => by
    simp only [Finset.mem_union] at h
    apply Prod.ext
    · apply NomSet.act_eq_of_supp_fixed
      intro a ha; exact h a (Or.inl ha)
    · apply NomSet.act_eq_of_supp_fixed
      intro a ha; exact h a (Or.inr ha)
  supp_equivariant := fun p π => by
    show NomSet.supp (π • p.1) ∪ NomSet.supp (π • p.2) = _
    rw [NomSet.supp_act_eq_image, NomSet.supp_act_eq_image, Finset.image_union]

end CatCrypt.Nominal

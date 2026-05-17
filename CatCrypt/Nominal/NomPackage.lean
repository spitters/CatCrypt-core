/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Nominal.Support
import CatCrypt.Nominal.Fresh
import CatCrypt.Package

/-!
# Nominal Packages

This file defines nominal packages - packages equipped with nominal structure
(atom support) enabling separated composition.

## Main definitions

* `NomPackage` - A package wrapped with support information
* `NomPackage.sep` - Separated composition (packages with disjoint supports)

## Overview

In nominal CatCrypt, packages are given a nominal structure where atoms represent
abstract memory locations. The key insight is that:

1. Each package has a finite support (the atoms/locations it uses)
2. Packages with disjoint supports can be composed without interference
3. The "move" operation can rename atoms to achieve disjoint supports

## References

* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
* [Pitts, *Nominal Sets*], Chapter 6
-/

namespace CatCrypt.Nominal

open CatCrypt.Package
open CatCrypt.Core
open CatCrypt.Prob

/-- A nominal package: a raw package together with its atom support.
    The support represents the abstract locations/names the package uses. -/
structure NomPackage where
  /-- The underlying raw package -/
  raw : RawPackage
  /-- The support: atoms that matter for this package -/
  support : Finset Atom

namespace NomPackage

@[ext]
theorem ext {P₁ P₂ : NomPackage} (hRaw : P₁.raw = P₂.raw) (hSupp : P₁.support = P₂.support) :
    P₁ = P₂ := by
  cases P₁; cases P₂; simp only [mk.injEq]; exact ⟨hRaw, hSupp⟩

/-- Empty nominal package with empty support -/
def empty : NomPackage := ⟨RawPackage.empty, ∅⟩

instance : EmptyCollection NomPackage := ⟨empty⟩

instance : Inhabited NomPackage := ⟨empty⟩

/-- Get the support of a nominal package -/
def getSupport (P : NomPackage) : Finset Atom := P.support

@[simp]
theorem getSupport_eq (P : NomPackage) : P.getSupport = P.support := rfl

/-- An atom is fresh for a package if it's not in the support -/
def Fresh (a : Atom) (P : NomPackage) : Prop := a ∉ P.support

/-- Two nominal packages are disjoint if their supports are disjoint -/
def Disjoint (P₁ P₂ : NomPackage) : Prop :=
  _root_.Disjoint P₁.support P₂.support

theorem disjoint_comm (P₁ P₂ : NomPackage) : Disjoint P₁ P₂ ↔ Disjoint P₂ P₁ := by
  simp only [Disjoint, _root_.disjoint_comm]

/-- Separated composition: compose two packages with disjoint supports.
    This is the key operation for nominal reasoning - packages that use
    different atoms can be composed without interference. -/
noncomputable def sep (P₁ P₂ : NomPackage) (_hDisj : Disjoint P₁ P₂)
    (hIds : RawPackage.Disjoint P₁.raw P₂.raw) : NomPackage :=
  ⟨RawPackage.par P₁.raw P₂.raw hIds, P₁.support ∪ P₂.support⟩

theorem sep_support (P₁ P₂ : NomPackage) (hDisj : Disjoint P₁ P₂)
    (hIds : RawPackage.Disjoint P₁.raw P₂.raw) :
    (sep P₁ P₂ hDisj hIds).support = P₁.support ∪ P₂.support := rfl

/-- Parallel composition without disjointness proof (using trivially empty supports).
    This is a fallback when support information isn't needed. -/
noncomputable def par (P₁ P₂ : NomPackage)
    (hIds : RawPackage.Disjoint P₁.raw P₂.raw) : NomPackage :=
  ⟨RawPackage.par P₁.raw P₂.raw hIds, P₁.support ∪ P₂.support⟩

/-- Sequential composition (linking) of nominal packages -/
noncomputable def link (P₁ P₂ : NomPackage) : NomPackage :=
  ⟨RawPackage.link P₁.raw P₂.raw, P₁.support ∪ P₂.support⟩

/-- Create a singleton nominal package with given support.
    `S` and `T` are restricted to `Type` (not `Type*`) to match the
    underlying `RawPackage.singleton` constraint. -/
noncomputable def singleton (id : ℕ) (S T : Type) (f : S → SPComp T)
    (support : Finset Atom := ∅) : NomPackage :=
  ⟨RawPackage.singleton id S T f, support⟩

/-- Rename atoms in a package using a finite permutation.
    This changes the support according to the permutation.

    **WARNING: This only renames the support, NOT the underlying code.**
    The `RawPackage` stores `S → SPComp T` functions that have no notion of
    atom/location identity, so there is nothing to rename inside the code.

    For actual code renaming, use the deep embedding layer where `RawCode`
    has explicit location references that can be permuted via
    `RawCode.renameLocations`. -/
noncomputable def rename (P : NomPackage) (π : FinPerm) : NomPackage :=
  ⟨P.raw, P.support.image (π ·)⟩

theorem rename_support (P : NomPackage) (π : FinPerm) :
    (rename P π).support = P.support.image (π ·) := rfl

/-! ## Separated composition properties -/

/-- Separated composition is commutative (up to raw package commutativity) -/
theorem sep_comm (P₁ P₂ : NomPackage) (hDisj : Disjoint P₁ P₂)
    (hIds : RawPackage.Disjoint P₁.raw P₂.raw)
    (hIds' : RawPackage.Disjoint P₂.raw P₁.raw) :
    (sep P₁ P₂ hDisj hIds).support = (sep P₂ P₁ (disjoint_comm P₁ P₂ |>.mp hDisj) hIds').support := by
  simp only [sep_support, Finset.union_comm]

/-- Fresh atoms don't affect packages under renaming -/
theorem rename_fresh (P : NomPackage) (a b : Atom)
    (ha : Fresh a P) (hb : Fresh b P) :
    rename P (FinPerm.swap a b) = P := by
  apply NomPackage.ext
  · rfl
  · simp only [rename_support]
    apply Finset.ext
    intro c
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have hda : d ≠ a := fun h => ha (h ▸ hd)
      have hdb : d ≠ b := fun h => hb (h ▸ hd)
      simp only [FinPerm.apply_def, FinPerm.swap_val, Equiv.swap_apply_of_ne_of_ne hda hdb]
      exact hd
    · intro hc
      use c, hc
      have hca : c ≠ a := fun h => ha (h ▸ hc)
      have hcb : c ≠ b := fun h => hb (h ▸ hc)
      simp only [FinPerm.apply_def, FinPerm.swap_val, Equiv.swap_apply_of_ne_of_ne hca hcb]

/-! ## NominalAction and NomSet instances -/

/-- NomPackage has a nominal action: permutations act on the support -/
noncomputable instance : MulAction FinPerm NomPackage where
  smul := fun π P => rename P π
  one_smul := fun P => by
    apply NomPackage.ext
    · rfl
    · show (rename P 1).support = P.support
      simp only [rename_support]
      apply Finset.ext
      intro a
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨b, hb, rfl⟩; simp [hb]
      · intro ha; exact ⟨a, ha, rfl⟩
  mul_smul := fun π₁ π₂ P => by
    apply NomPackage.ext
    · rfl
    · show (rename P (π₁ * π₂)).support = (rename (rename P π₂) π₁).support
      simp only [rename_support, Finset.image_image]
      rfl

/-- NomPackage is a nominal set -/
noncomputable instance : NomSet NomPackage where
  supp := fun P => P.support
  supp_supports := fun P π h => by
    apply NomPackage.ext
    · rfl
    · show (rename P π).support = P.support
      simp only [rename_support]
      apply Finset.ext
      intro a
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨b, hb, rfl⟩
        have hπb := h b hb
        simp only [FinPerm.apply_def] at hπb ⊢
        rw [hπb]
        exact hb
      · intro ha
        use a, ha
        exact h a ha
  supp_equivariant := fun P π => by
    show (rename P π).support = P.support.image (π ·)
    simp only [rename_support]

/-! ## Alpha-equivalence for packages -/

/-- Alpha-equivalence for NomPackage: two packages are equivalent if
    they differ only by a permutation -/
def AlphaEquiv (P₁ P₂ : NomPackage) : Prop :=
  CatCrypt.Nominal.AlphaEquiv P₁ P₂

notation:50 P₁ " ≡αP " P₂ => AlphaEquiv P₁ P₂

/-- Alpha-equivalence is reflexive -/
theorem AlphaEquiv.refl (P : NomPackage) : P ≡αP P :=
  CatCrypt.Nominal.AlphaEquiv.refl P

/-- Alpha-equivalence is symmetric -/
theorem AlphaEquiv.symm {P₁ P₂ : NomPackage} (h : P₁ ≡αP P₂) : P₂ ≡αP P₁ :=
  CatCrypt.Nominal.AlphaEquiv.symm h

/-- Alpha-equivalence is transitive -/
theorem AlphaEquiv.trans {P₁ P₂ P₃ : NomPackage} (h₁₂ : P₁ ≡αP P₂) (h₂₃ : P₂ ≡αP P₃) :
    P₁ ≡αP P₃ :=
  CatCrypt.Nominal.AlphaEquiv.trans h₁₂ h₂₃

/-! ## Package algebra laws -/

/-- Raw package parallel composition is commutative up to alpha-equivalence.

    This theorem states that the underlying raw packages have the same entries
    (though possibly in different order in the union). -/
theorem RawPackage.par_comm (P₁ P₂ : RawPackage)
    (hIds : RawPackage.Disjoint P₁ P₂)
    (hIds' : RawPackage.Disjoint P₂ P₁) :
    (RawPackage.par P₁ P₂ hIds).entries = (RawPackage.par P₂ P₁ hIds').entries := by
  simp only [RawPackage.par, Finset.union_comm]

/-- Commutativity of separated composition for NomPackage.

    When two packages have disjoint supports, their separated composition
    is equal (not just alpha-equivalent) because:
    - The raw packages combine with union (which is commutative)
    - The supports combine with union (which is commutative) -/
theorem sep_comm_eq (P₁ P₂ : NomPackage) (hDisj : Disjoint P₁ P₂)
    (hIds : RawPackage.Disjoint P₁.raw P₂.raw)
    (hIds' : RawPackage.Disjoint P₂.raw P₁.raw) :
    sep P₁ P₂ hDisj hIds = sep P₂ P₁ (disjoint_comm P₁ P₂ |>.mp hDisj) hIds' := by
  apply NomPackage.ext
  · -- Raw packages are equal (union is commutative)
    simp only [sep, RawPackage.par]
    congr 1
    exact Finset.union_comm _ _
  · -- Supports are equal (union is commutative)
    simp only [sep_support, Finset.union_comm]

/-- Commutativity of separated composition up to alpha-equivalence -/
theorem sep_comm_alpha (P₁ P₂ : NomPackage) (hDisj : Disjoint P₁ P₂)
    (hIds : RawPackage.Disjoint P₁.raw P₂.raw)
    (hIds' : RawPackage.Disjoint P₂.raw P₁.raw) :
    sep P₁ P₂ hDisj hIds ≡αP sep P₂ P₁ (disjoint_comm P₁ P₂ |>.mp hDisj) hIds' := by
  rw [sep_comm_eq P₁ P₂ hDisj hIds hIds']
  exact AlphaEquiv.refl _

/-- Associativity of separated composition (equality version).

    For three packages with mutually disjoint supports, separated composition
    is associative. -/
theorem sep_assoc_eq (P₁ P₂ P₃ : NomPackage)
    (hDisj₁₂ : Disjoint P₁ P₂)
    (hDisj₂₃ : Disjoint P₂ P₃)
    (hDisj₁₃ : Disjoint P₁ P₃)
    (hIds₁₂ : RawPackage.Disjoint P₁.raw P₂.raw)
    (hIds₂₃ : RawPackage.Disjoint P₂.raw P₃.raw)
    (hIds₁₃ : RawPackage.Disjoint P₁.raw P₃.raw)
    (hIds₁₂₃_left : RawPackage.Disjoint (RawPackage.par P₁.raw P₂.raw hIds₁₂) P₃.raw)
    (hIds₁₂₃_right : RawPackage.Disjoint P₁.raw (RawPackage.par P₂.raw P₃.raw hIds₂₃))
    (hDisj₁₂_₃ : Disjoint (sep P₁ P₂ hDisj₁₂ hIds₁₂) P₃)
    (hDisj₁_₂₃ : Disjoint P₁ (sep P₂ P₃ hDisj₂₃ hIds₂₃)) :
    sep (sep P₁ P₂ hDisj₁₂ hIds₁₂) P₃ hDisj₁₂_₃ hIds₁₂₃_left =
    sep P₁ (sep P₂ P₃ hDisj₂₃ hIds₂₃) hDisj₁_₂₃ hIds₁₂₃_right := by
  apply NomPackage.ext
  · -- Raw packages: (P₁ ∪ P₂) ∪ P₃ = P₁ ∪ (P₂ ∪ P₃)
    simp only [sep, RawPackage.par]
    congr 1
    exact Finset.union_assoc _ _ _
  · -- Supports: (S₁ ∪ S₂) ∪ S₃ = S₁ ∪ (S₂ ∪ S₃)
    simp only [sep_support]
    exact Finset.union_assoc _ _ _

/-- Associativity of separated composition up to alpha-equivalence -/
theorem sep_assoc_alpha (P₁ P₂ P₃ : NomPackage)
    (hDisj₁₂ : Disjoint P₁ P₂)
    (hDisj₂₃ : Disjoint P₂ P₃)
    (hDisj₁₃ : Disjoint P₁ P₃)
    (hIds₁₂ : RawPackage.Disjoint P₁.raw P₂.raw)
    (hIds₂₃ : RawPackage.Disjoint P₂.raw P₃.raw)
    (hIds₁₃ : RawPackage.Disjoint P₁.raw P₃.raw)
    (hIds₁₂₃_left : RawPackage.Disjoint (RawPackage.par P₁.raw P₂.raw hIds₁₂) P₃.raw)
    (hIds₁₂₃_right : RawPackage.Disjoint P₁.raw (RawPackage.par P₂.raw P₃.raw hIds₂₃))
    (hDisj₁₂_₃ : Disjoint (sep P₁ P₂ hDisj₁₂ hIds₁₂) P₃)
    (hDisj₁_₂₃ : Disjoint P₁ (sep P₂ P₃ hDisj₂₃ hIds₂₃)) :
    sep (sep P₁ P₂ hDisj₁₂ hIds₁₂) P₃ hDisj₁₂_₃ hIds₁₂₃_left ≡αP
    sep P₁ (sep P₂ P₃ hDisj₂₃ hIds₂₃) hDisj₁_₂₃ hIds₁₂₃_right := by
  rw [sep_assoc_eq P₁ P₂ P₃ hDisj₁₂ hDisj₂₃ hDisj₁₃ hIds₁₂ hIds₂₃ hIds₁₃
      hIds₁₂₃_left hIds₁₂₃_right hDisj₁₂_₃ hDisj₁_₂₃]
  exact AlphaEquiv.refl _

/-! ## Simplified versions with automatic disjointness -/

/-- Disjointness of sep's support with a third package -/
theorem sep_disjoint_right (P₁ P₂ P₃ : NomPackage)
    (hDisj₁₂ : Disjoint P₁ P₂)
    (hIds₁₂ : RawPackage.Disjoint P₁.raw P₂.raw)
    (hDisj₁₃ : Disjoint P₁ P₃)
    (hDisj₂₃ : Disjoint P₂ P₃) :
    Disjoint (sep P₁ P₂ hDisj₁₂ hIds₁₂) P₃ := by
  simp only [Disjoint, sep_support]
  rw [Finset.disjoint_union_left]
  constructor
  · exact hDisj₁₃
  · exact hDisj₂₃

/-- Disjointness of a package with sep's support -/
theorem disjoint_sep_left (P₁ P₂ P₃ : NomPackage)
    (hDisj₂₃ : Disjoint P₂ P₃)
    (hIds₂₃ : RawPackage.Disjoint P₂.raw P₃.raw)
    (hDisj₁₂ : Disjoint P₁ P₂)
    (hDisj₁₃ : Disjoint P₁ P₃) :
    Disjoint P₁ (sep P₂ P₃ hDisj₂₃ hIds₂₃) := by
  simp only [Disjoint, sep_support]
  rw [Finset.disjoint_union_right]
  constructor
  · exact hDisj₁₂
  · exact hDisj₁₃

end NomPackage

end CatCrypt.Nominal

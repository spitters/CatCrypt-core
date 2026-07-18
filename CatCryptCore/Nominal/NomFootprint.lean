/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Nominal.NomPackage

/-!
# Generic Nominal Footprint

`NomPackage` (see `CatCryptCore.Nominal.NomPackage`) is *shallow* nominal SSProve:
a `RawPackage` paired with a declared `Finset Atom` support, composed on disjoint
supports, with a rename that acts only on the support metadata (not on the code).

This file abstracts that construction away from `RawPackage`: the footprint
(support, disjointness, freshness, rename) is orthogonal to the carrier `C`, so it
works over an arbitrary carrier — hence generically over the underlying effect /
Q₀-monad the carrier is built from.

## Main definitions

* `NomOver C` — a carrier `C` paired with a `Finset Atom` support.
* `NomOver.Disjoint`, `NomOver.Fresh` — the footprint predicates.
* `NomOver.rename` — permutation acting on the support only.
* `NomOver.sepWith comb` — separated composition, parameterized by a carrier
  combination `comb : C → C → C` (so no `RawPackage.par` is needed here).

## Recovery

`NomPackage` is the `C := RawPackage` instance: `equivNomOver` is the data-level
bijection `NomPackage ≃ NomOver RawPackage`, and the `to_*` lemmas show it carries
`NomPackage.rename` / `support` / `Disjoint` / `Fresh` to the generic operations.

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
-/

set_option autoImplicit false

namespace CatCrypt.Nominal

open CatCrypt.Package

universe u

/-- A carrier `C` equipped with a nominal footprint: a declared atom support.
    This is `NomPackage` with `RawPackage` abstracted to an arbitrary `C`; nothing
    is required of `C`, since the footprint is orthogonal to the carrier. -/
structure NomOver (C : Type u) where
  /-- The underlying carrier value -/
  carrier : C
  /-- The support: atoms that matter for this value -/
  support : Finset Atom

namespace NomOver

variable {C : Type u}

@[ext]
theorem ext {P₁ P₂ : NomOver C} (hCarrier : P₁.carrier = P₂.carrier)
    (hSupp : P₁.support = P₂.support) : P₁ = P₂ := by
  cases P₁; cases P₂; simp only [mk.injEq]; exact ⟨hCarrier, hSupp⟩

/-- An atom is fresh for a value if it is not in the support. -/
def Fresh (a : Atom) (P : NomOver C) : Prop := a ∉ P.support

/-- Two values are disjoint if their supports are disjoint. -/
def Disjoint (P₁ P₂ : NomOver C) : Prop :=
  _root_.Disjoint P₁.support P₂.support

theorem disjoint_comm (P₁ P₂ : NomOver C) : Disjoint P₁ P₂ ↔ Disjoint P₂ P₁ := by
  simp only [Disjoint, _root_.disjoint_comm]

/-! ## Rename: a permutation acts on the support only -/

/-- Rename atoms in the footprint using a finite permutation.
    Like `NomPackage.rename`, this only relabels the support; the carrier is
    untouched (a shallow, metadata-level rename). -/
def rename (P : NomOver C) (π : FinPerm) : NomOver C :=
  ⟨P.carrier, P.support.image (π ·)⟩

@[simp]
theorem rename_carrier (P : NomOver C) (π : FinPerm) :
    (rename P π).carrier = P.carrier := rfl

@[simp]
theorem rename_support (P : NomOver C) (π : FinPerm) :
    (rename P π).support = P.support.image (π ·) := rfl

/-- Renaming by the identity permutation is the identity. -/
@[simp]
theorem rename_one (P : NomOver C) : rename P 1 = P := by
  apply NomOver.ext
  · rfl
  · simp only [rename_support]
    apply Finset.ext
    intro a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩; simpa using hb
    · intro ha; exact ⟨a, ha, by simp⟩

/-- Rename composes: `rename (π * σ) = rename π ∘ rename σ`. -/
theorem rename_mul (P : NomOver C) (π σ : FinPerm) :
    rename P (π * σ) = rename (rename P σ) π := by
  apply NomOver.ext
  · rfl
  · simp only [rename_support, Finset.image_image]
    rfl

/-- Freshness is transported along a rename: `a` is fresh for `P` iff `π a` is
    fresh for `rename P π` (the permutation is injective on atoms). -/
theorem fresh_rename (P : NomOver C) (a : Atom) (π : FinPerm) :
    Fresh a P ↔ Fresh (π a) (rename P π) := by
  simp only [Fresh, rename_support, Finset.mem_image, not_exists, not_and]
  constructor
  · intro h b hb hEq
    apply h
    have hba : b = a := by
      have := π.val.injective (a₁ := b) (a₂ := a) (by simpa only [FinPerm.apply_def] using hEq)
      exact this
    rwa [hba] at hb
  · intro h ha
    exact h a ha rfl

/-! ## Separated composition, parameterized by a carrier combination -/

/-- Separated composition of footprints, with the carrier combined by `comb`.
    Taking `comb` as a parameter avoids committing to `RawPackage.par`: the
    support law and the algebraic laws that do not mention `comb` hold for any
    `comb`, and commutativity / associativity are recovered from the
    corresponding law on `comb`. -/
def sepWith (comb : C → C → C) (P₁ P₂ : NomOver C) : NomOver C :=
  ⟨comb P₁.carrier P₂.carrier, P₁.support ∪ P₂.support⟩

@[simp]
theorem sepWith_carrier (comb : C → C → C) (P₁ P₂ : NomOver C) :
    (sepWith comb P₁ P₂).carrier = comb P₁.carrier P₂.carrier := rfl

@[simp]
theorem sepWith_support (comb : C → C → C) (P₁ P₂ : NomOver C) :
    (sepWith comb P₁ P₂).support = P₁.support ∪ P₂.support := rfl

/-- The support law is symmetric regardless of `comb`. -/
theorem sepWith_support_comm (comb : C → C → C) (P₁ P₂ : NomOver C) :
    (sepWith comb P₁ P₂).support = (sepWith comb P₂ P₁).support := by
  simp only [sepWith_support, Finset.union_comm]

/-- Disjointness of a separated composition with a third value. -/
theorem sepWith_disjoint_right (comb : C → C → C) (P₁ P₂ P₃ : NomOver C)
    (hDisj₁₃ : Disjoint P₁ P₃) (hDisj₂₃ : Disjoint P₂ P₃) :
    Disjoint (sepWith comb P₁ P₂) P₃ := by
  simp only [Disjoint, sepWith_support, Finset.disjoint_union_left]
  exact ⟨hDisj₁₃, hDisj₂₃⟩

/-- Disjointness of a value with a separated composition. -/
theorem disjoint_sepWith_left (comb : C → C → C) (P₁ P₂ P₃ : NomOver C)
    (hDisj₁₂ : Disjoint P₁ P₂) (hDisj₁₃ : Disjoint P₁ P₃) :
    Disjoint P₁ (sepWith comb P₂ P₃) := by
  simp only [Disjoint, sepWith_support, Finset.disjoint_union_right]
  exact ⟨hDisj₁₂, hDisj₁₃⟩

/-- If `comb` is commutative, so is `sepWith comb` (equality of full footprints). -/
theorem sepWith_comm (comb : C → C → C)
    (hComb : ∀ a b, comb a b = comb b a) (P₁ P₂ : NomOver C) :
    sepWith comb P₁ P₂ = sepWith comb P₂ P₁ := by
  apply NomOver.ext
  · simp only [sepWith_carrier]; exact hComb _ _
  · simp only [sepWith_support, Finset.union_comm]

/-- If `comb` is associative, so is `sepWith comb`. -/
theorem sepWith_assoc (comb : C → C → C)
    (hComb : ∀ a b c, comb (comb a b) c = comb a (comb b c))
    (P₁ P₂ P₃ : NomOver C) :
    sepWith comb (sepWith comb P₁ P₂) P₃ = sepWith comb P₁ (sepWith comb P₂ P₃) := by
  apply NomOver.ext
  · simp only [sepWith_carrier]; exact hComb _ _ _
  · simp only [sepWith_support, Finset.union_assoc]

/-! ## `NomOver` is a nominal footprint: the rename action -/

/-- The shallow rename is a `MulAction` of `FinPerm` on any footprint carrier. -/
instance : MulAction FinPerm (NomOver C) where
  smul := fun π P => rename P π
  one_smul := fun P => rename_one P
  mul_smul := fun π σ P => rename_mul P π σ

@[simp]
theorem smul_eq_rename (π : FinPerm) (P : NomOver C) : π • P = rename P π := rfl

end NomOver

/-! ## Recovery: nominal SSProve is the `RawPackage` instance -/

namespace NomPackage

/-- Forget the `RawPackage`-specific packaging: view a `NomPackage` as a generic
    footprint over the carrier `RawPackage`. -/
def toNomOver (P : NomPackage) : NomOver RawPackage := ⟨P.raw, P.support⟩

/-- Rebuild a `NomPackage` from a generic footprint over `RawPackage`. -/
def ofNomOver (P : NomOver RawPackage) : NomPackage := ⟨P.carrier, P.support⟩

/-- `NomPackage` and `NomOver RawPackage` are the same data: the footprint
    construction over `RawPackage` recovers nominal SSProve. -/
def equivNomOver : NomPackage ≃ NomOver RawPackage where
  toFun := toNomOver
  invFun := ofNomOver
  left_inv := fun P => by cases P; rfl
  right_inv := fun P => by cases P; rfl

@[simp]
theorem toNomOver_carrier (P : NomPackage) : (toNomOver P).carrier = P.raw := rfl

@[simp]
theorem toNomOver_support (P : NomPackage) : (toNomOver P).support = P.support := rfl

/-- The bijection carries `NomPackage.rename` to `NomOver.rename`. -/
theorem toNomOver_rename (P : NomPackage) (π : FinPerm) :
    toNomOver (rename P π) = NomOver.rename (toNomOver P) π := rfl

/-- The bijection carries `NomPackage.Disjoint` to `NomOver.Disjoint`. -/
theorem toNomOver_disjoint (P₁ P₂ : NomPackage) :
    Disjoint P₁ P₂ ↔ NomOver.Disjoint (toNomOver P₁) (toNomOver P₂) := Iff.rfl

/-- The bijection carries `NomPackage.Fresh` to `NomOver.Fresh`. -/
theorem toNomOver_fresh (a : Atom) (P : NomPackage) :
    Fresh a P ↔ NomOver.Fresh a (toNomOver P) := Iff.rfl

/-- The support of a separated composition matches `sepWith`'s support law for any
    carrier combination. -/
theorem toNomOver_sep_support (P₁ P₂ : NomPackage) (hDisj : Disjoint P₁ P₂)
    (hIds : RawPackage.Disjoint P₁.raw P₂.raw) (comb : RawPackage → RawPackage → RawPackage) :
    (toNomOver (sep P₁ P₂ hDisj hIds)).support
      = (NomOver.sepWith comb (toNomOver P₁) (toNomOver P₂)).support := rfl

/-- The carrier of a separated composition is the concrete `RawPackage.par`.
    (A *total* `comb : RawPackage → RawPackage → RawPackage` cannot be `RawPackage.par`,
    which needs the id-disjointness proof `hIds`; this is why `sepWith` takes `comb`
    as a parameter and why the `sep` correspondence is stated on carrier/support
    separately rather than as a single `sepWith` equation.) -/
theorem toNomOver_sep_carrier (P₁ P₂ : NomPackage) (hDisj : Disjoint P₁ P₂)
    (hIds : RawPackage.Disjoint P₁.raw P₂.raw) :
    (toNomOver (sep P₁ P₂ hDisj hIds)).carrier = RawPackage.par P₁.raw P₂.raw hIds := rfl

end NomPackage

end CatCrypt.Nominal

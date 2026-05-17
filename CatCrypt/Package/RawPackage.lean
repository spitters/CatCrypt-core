/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Package.Interface
import CatCrypt.Core.Code
import Mathlib.Data.Finset.Image

/-!
# Raw Packages

This file defines raw packages - collections of typed function implementations.
A raw package maps operation identifiers to their implementations.

## Main definitions

* `TypedFun` - A typed function implementation (input type, output type, implementation)
* `RawPackage` - A collection of typed function implementations
* `RawPackage.link` - Sequential composition (linking)
* `RawPackage.par` - Parallel composition
* `RawPackage.id` - Identity package

## References

* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Package

open CatCrypt.Core
open CatCrypt.Prob

/-- A typed function: source type, target type, and implementation -/
structure TypedFun where
  /-- Input type -/
  src : Type
  /-- Output type -/
  tgt : Type
  /-- Implementation: src → SPComp tgt -/
  impl : src → SPComp tgt

/-- DecidableEq for TypedFun -/
noncomputable instance : DecidableEq TypedFun := Classical.decEq TypedFun

/-- Package entry: operation id with its typed implementation -/
structure PackageEntry where
  id : ℕ
  fun_ : TypedFun

/-- DecidableEq for PackageEntry (needed for Finset operations) -/
noncomputable instance : DecidableEq PackageEntry := Classical.decEq PackageEntry

/-- Raw package: a finite collection of typed function implementations.
    Each entry maps an operation id to its implementation. -/
structure RawPackage where
  entries : Finset PackageEntry
  unique_ids : ∀ e₁ e₂ : PackageEntry, e₁ ∈ entries → e₂ ∈ entries →
                e₁.id = e₂.id → e₁ = e₂

namespace RawPackage

/-- Empty package -/
def empty : RawPackage := ⟨∅, fun _ _ h => (Finset.notMem_empty _ h).elim⟩

instance : EmptyCollection RawPackage := ⟨empty⟩

/-- The set of operation ids implemented by the package -/
noncomputable def ids (P : RawPackage) : Finset ℕ :=
  P.entries.image (·.id)

/-- Check if a package implements an operation with given id and types -/
def has (P : RawPackage) (id : ℕ) (S T : Type) : Prop :=
  ∃ e ∈ P.entries, e.id = id ∧ e.fun_.src = S ∧ e.fun_.tgt = T

/-- Lookup an implementation by id (noncomputable) -/
noncomputable def lookup (P : RawPackage) (id : ℕ) : Option TypedFun :=
  if h : ∃ e ∈ P.entries, e.id = id then
    some (Classical.choose h).fun_
  else
    none

/-- Single function package -/
noncomputable def singleton (id : ℕ) (S T : Type) (f : S → SPComp T) : RawPackage :=
  ⟨{⟨id, ⟨S, T, f⟩⟩}, fun e₁ e₂ h₁ h₂ _ => by
    simp only [Finset.mem_singleton] at h₁ h₂
    rw [h₁, h₂]⟩

/-- Two packages are disjoint if they share no operation ids -/
def Disjoint (P₁ P₂ : RawPackage) : Prop :=
  _root_.Disjoint P₁.ids P₂.ids

/-- Parallel composition: combine two packages with disjoint ids -/
noncomputable def par (P₁ P₂ : RawPackage) (h : Disjoint P₁ P₂) : RawPackage :=
  ⟨P₁.entries ∪ P₂.entries, fun e₁ e₂ h₁ h₂ hid => by
    rw [Finset.mem_union] at h₁ h₂
    cases h₁ with
    | inl h₁ =>
      cases h₂ with
      | inl h₂ => exact P₁.unique_ids e₁ e₂ h₁ h₂ hid
      | inr h₂ =>
        exfalso
        simp only [Disjoint, ids, Finset.disjoint_iff_ne] at h
        have h₁' : e₁.id ∈ P₁.ids := Finset.mem_image_of_mem _ h₁
        have h₂' : e₂.id ∈ P₂.ids := Finset.mem_image_of_mem _ h₂
        exact h _ h₁' _ h₂' hid
    | inr h₁ =>
      cases h₂ with
      | inl h₂ =>
        exfalso
        simp only [Disjoint, ids, Finset.disjoint_iff_ne] at h
        have h₂' : e₂.id ∈ P₁.ids := Finset.mem_image_of_mem _ h₂
        have h₁' : e₁.id ∈ P₂.ids := Finset.mem_image_of_mem _ h₁
        exact h _ h₂' _ h₁' hid.symm
      | inr h₂ => exact P₂.unique_ids e₁ e₂ h₁ h₂ hid⟩

theorem par_ids {P₁ P₂ : RawPackage} (h : Disjoint P₁ P₂) :
    (par P₁ P₂ h).ids = P₁.ids ∪ P₂.ids := by
  simp only [par, ids, Finset.image_union]

/-- Resolve: find the implementation for an operation id and call it.
    Returns `fail` if the operation is not implemented. -/
noncomputable def resolve (P : RawPackage) (id : ℕ) {S T : Type}
    (x : S) : SPComp T :=
  match lookup P id with
  | some f =>
    -- Use classical decidability for type equality
    haveI : Decidable (f.src = S) := Classical.dec _
    haveI : Decidable (f.tgt = T) := Classical.dec _
    if hS : f.src = S then
      if hT : f.tgt = T then
        cast (by rw [hT]) (f.impl (cast (by rw [hS]) x))
      else
        SPComp.fail
    else
      SPComp.fail
  | none => SPComp.fail

/-- Sequential composition (linking): P₁ imports from P₂.

    **WARNING: This is a stub that returns `P₁` unchanged.**
    The shallow `RawPackage` representation stores typed functions
    (`S → SPComp T`) that have no notion of oracle calls, so there
    is nothing to substitute. This makes `link` a no-op.

    **For real package linking, use the deep embedding layer:**
    - `DeepPackage.link` in `CatCrypt.Deep.Package` performs actual
      oracle substitution via `RawCode.substOracle`
    - `runPkg_link` in `CatCrypt.Crypto.NomAdvantage` proves correctness
    - `runPkg_link_assoc` proves associativity at the evaluation level -/
noncomputable def link (P₁ _P₂ : RawPackage) : RawPackage :=
  P₁

/-- Identity package: implements an interface by just forwarding -/
-- Note: Full identity would need import capability
noncomputable def idPkg (I : Interface) : RawPackage := empty

theorem empty_ids : (∅ : RawPackage).ids = ∅ := Finset.image_empty _

theorem empty_not_has (id : ℕ) (S T : Type) : ¬(empty.has id S T) := by
  simp only [empty, has]
  intro ⟨e, he, _, _, _⟩
  exact Finset.notMem_empty _ he

end RawPackage

end CatCrypt.Package

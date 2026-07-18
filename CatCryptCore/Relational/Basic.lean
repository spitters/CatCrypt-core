/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Heap

/-!
# Relational Assertions

This file defines relational preconditions and postconditions for pRHL.

## Main definitions

* `RPre` - Relational precondition (predicate on heap pairs)
* `RPost α β` - Relational postcondition (predicate on (result, heap) pairs)
* `eqPre` - Equality precondition
* `eqPost` - Equality postcondition

## Notation

* `⟨1⟩` - Access left component
* `⟨2⟩` - Access right component
-/

namespace CatCrypt.Relational

open CatCrypt.Core

/-! ## Basic types -/

/-- Relational precondition: predicate on pairs of heaps -/
abbrev RPre := Heap → Heap → Prop

/-- Relational postcondition: predicate on pairs of (result, heap) -/
abbrev RPost (α β : Type*) := α → Heap → β → Heap → Prop

/-- Relational specification -/
structure RSpec (α β : Type*) where
  pre : RPre
  post : RPost α β

/-! ## Standard preconditions -/

/-- Equality precondition: heaps must be equal -/
def eqPre : RPre := fun h₁ h₂ => h₁ = h₂

/-- Grind normalization for eqPre -/
@[grind =] theorem eqPre_eq (h₁ h₂ : Heap) : eqPre h₁ h₂ = (h₁ = h₂) := rfl

/-- True precondition: always holds -/
def truePre : RPre := fun _ _ => True

@[grind =] theorem truePre_eq (h₁ h₂ : Heap) : truePre h₁ h₂ = True := rfl

/-- False precondition: never holds -/
def falsePre : RPre := fun _ _ => False

@[grind =] theorem falsePre_eq (h₁ h₂ : Heap) : falsePre h₁ h₂ = False := rfl

/-! ## Standard postconditions -/

variable {α β γ : Type*}

/-- Equality postcondition: results and heaps must be equal -/
def eqPost : RPost α α := fun a₁ h₁ a₂ h₂ => a₁ = a₂ ∧ h₁ = h₂

/-- Grind normalization for eqPost -/
@[grind =] theorem eqPost_eq (a₁ a₂ : α) (h₁ h₂ : Heap) :
    eqPost a₁ h₁ a₂ h₂ = (a₁ = a₂ ∧ h₁ = h₂) := rfl

/-- True postcondition: always holds -/
def truePost : RPost α β := fun _ _ _ _ => True

@[grind =] theorem truePost_eq (a₁ : α) (h₁ : Heap) (a₂ : β) (h₂ : Heap) :
    truePost a₁ h₁ a₂ h₂ = True := rfl

/-! ## Combinators -/

/-- Conjunction of preconditions -/
def andPre (P Q : RPre) : RPre := fun h₁ h₂ => P h₁ h₂ ∧ Q h₁ h₂

infixl:65 " ⋀ " => andPre

/-- Disjunction of preconditions -/
def orPre (P Q : RPre) : RPre := fun h₁ h₂ => P h₁ h₂ ∨ Q h₁ h₂

infixl:60 " ⋁ " => orPre

/-- Implication of preconditions -/
def implPre (P Q : RPre) : RPre := fun h₁ h₂ => P h₁ h₂ → Q h₁ h₂

infixr:55 " ⟹ " => implPre

/-- Conjunction of postconditions -/
def andPost (P Q : RPost α β) : RPost α β :=
  fun a₁ h₁ a₂ h₂ => P a₁ h₁ a₂ h₂ ∧ Q a₁ h₁ a₂ h₂

/-! ## EasyCrypt-style ⟨1⟩/⟨2⟩ accessors -/

/-- Access left heap in relational assertion -/
def lhs (f : Heap → γ) : Heap → Heap → γ := fun h₁ _ => f h₁

/-- Access right heap in relational assertion -/
def rhs (f : Heap → γ) : Heap → Heap → γ := fun _ h₂ => f h₂

notation:max f "⟨1⟩" => lhs f
notation:max f "⟨2⟩" => rhs f

/-! ## Location-based assertions -/

/-- Left heap has value v at location l -/
def leftHas (l : Location) (v : l.ty) : RPre := fun h₁ _ => h₁.get l = v

@[grind =] theorem leftHas_eq (l : Location) (v : l.ty) (h₁ h₂ : Heap) :
    leftHas l v h₁ h₂ = (h₁.get l = v) := rfl

/-- Right heap has value v at location l -/
def rightHas (l : Location) (v : l.ty) : RPre := fun _ h₂ => h₂.get l = v

@[grind =] theorem rightHas_eq (l : Location) (v : l.ty) (h₁ h₂ : Heap) :
    rightHas l v h₁ h₂ = (h₂.get l = v) := rfl

/-! ## Lemmas -/

@[simp]
theorem eqPre_iff (h₁ h₂ : Heap) : eqPre h₁ h₂ ↔ h₁ = h₂ := Iff.rfl

@[simp]
theorem truePre_iff (h₁ h₂ : Heap) : truePre h₁ h₂ ↔ True := Iff.rfl

@[simp]
theorem eqPost_iff (a₁ : α) (h₁ : Heap) (a₂ : α) (h₂ : Heap) :
    eqPost a₁ h₁ a₂ h₂ ↔ a₁ = a₂ ∧ h₁ = h₂ := Iff.rfl

theorem andPre_iff (P Q : RPre) (h₁ h₂ : Heap) :
    (P ⋀ Q) h₁ h₂ ↔ P h₁ h₂ ∧ Q h₁ h₂ := Iff.rfl

end CatCrypt.Relational

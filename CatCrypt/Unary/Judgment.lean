/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Code
import CatCrypt.Prob.SDistr

/-!
# Unary Probabilistic Hoare Logic - Judgment

This file defines the unary probabilistic Hoare logic judgment for CatCrypt.
It is analogous to EasyCrypt's pHL but for our `SPComp` monad.

## Main definitions

* `UPre` - Unary precondition (predicate on initial heap)
* `UPost α` - Unary postcondition (predicate on result and final heap)
* `pHoare P c Q` - The pHL judgment: for all heaps satisfying `P`,
  every outcome in the support of `c h` satisfies `Q`

## References

* EasyCrypt pHL (unary probabilistic Hoare logic)
* CatCrypt Relational.Judgment (the relational counterpart)
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob

variable {α β : Type*}

/-! ## Unary assertion types -/

/-- Unary precondition: predicate on initial heap -/
abbrev UPre := Heap → Prop

/-- Unary postcondition: predicate on result and final heap -/
abbrev UPost (α : Type*) := α → Heap → Prop

/-! ## Standard preconditions -/

/-- True precondition: always holds -/
def truePre : UPre := fun _ => True

/-- False precondition: never holds -/
def falsePre : UPre := fun _ => False

/-! ## The pHL Judgment -/

/-- The probabilistic Hoare logic judgment (pHL).

`pHoare P c Q` means: for all initial heaps `h` satisfying `P h`,
every outcome `(a, h')` in the support of `c h` satisfies `Q a h'`.

An outcome `(a, h')` is in the support when `(c h) (some (a, h')) ≠ 0`,
i.e., it has nonzero probability. -/
def pHoare (P : UPre) (c : SPComp α) (Q : UPost α) : Prop :=
  ∀ h, P h → ∀ a h', (c h) (some (a, h')) ≠ 0 → Q a h'

/-! ## Basic properties -/

/-- pHoare is monotone in the postcondition -/
theorem pHoare_mono_post {P : UPre} {Q Q' : UPost α} {c : SPComp α}
    (h : pHoare P c Q) (hQ : ∀ a h, Q a h → Q' a h) :
    pHoare P c Q' := by
  intro h₀ hP a h' hsupp
  exact hQ a h' (h h₀ hP a h' hsupp)

/-- pHoare is antimonotone in the precondition -/
theorem pHoare_mono_pre {P P' : UPre} {Q : UPost α} {c : SPComp α}
    (h : pHoare P c Q) (hP : ∀ h, P' h → P h) :
    pHoare P' c Q := by
  intro h₀ hP' a h' hsupp
  exact h h₀ (hP h₀ hP') a h' hsupp

/-- Consequence rule: strengthen precondition, weaken postcondition -/
theorem pHoare_conseq {P P' : UPre} {Q Q' : UPost α} {c : SPComp α}
    (hPre : ∀ h, P' h → P h) (hPost : ∀ a h, Q a h → Q' a h)
    (h : pHoare P c Q) :
    pHoare P' c Q' :=
  pHoare_mono_post (pHoare_mono_pre h hPre) hPost

/-- Conjunction of postconditions -/
theorem pHoare_and {P : UPre} {Q₁ Q₂ : UPost α} {c : SPComp α}
    (h₁ : pHoare P c Q₁) (h₂ : pHoare P c Q₂) :
    pHoare P c (fun a h => Q₁ a h ∧ Q₂ a h) := by
  intro h₀ hP a h' hsupp
  exact ⟨h₁ h₀ hP a h' hsupp, h₂ h₀ hP a h' hsupp⟩

/-- Disjunction of preconditions -/
theorem pHoare_or_pre {P₁ P₂ : UPre} {Q : UPost α} {c : SPComp α}
    (h₁ : pHoare P₁ c Q) (h₂ : pHoare P₂ c Q) :
    pHoare (fun h => P₁ h ∨ P₂ h) c Q := by
  intro h₀ hP a h' hsupp
  cases hP with
  | inl hp₁ => exact h₁ h₀ hp₁ a h' hsupp
  | inr hp₂ => exact h₂ h₀ hp₂ a h' hsupp

/-- True precondition implies any precondition suffices -/
theorem pHoare_true_pre {P : UPre} {Q : UPost α} {c : SPComp α}
    (h : pHoare truePre c Q) :
    pHoare P c Q :=
  pHoare_mono_pre h (fun _ _ => trivial)

/-- False precondition makes any judgment trivially true -/
theorem pHoare_false_pre {Q : UPost α} {c : SPComp α} :
    pHoare falsePre c Q := by
  intro _ hP
  exact absurd hP id

end CatCrypt.Unary

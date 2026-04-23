/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Code
import CatCrypt.Prob.Coupling
import CatCrypt.Relational.Basic

/-!
# Probabilistic Relational Hoare Logic - Judgment

This file defines the fundamental pRHL judgment.

## Main definitions

* `rHoare Φ c₁ c₂ Ψ` - The pRHL judgment

## Notation

* `⊨ ⦃Φ⦄ c₁ ~ c₂ ⦃Ψ⦄` - pRHL judgment
* `c₁ ~ c₂ : Φ ==> Ψ` - EasyCrypt-style notation

## References

* CatCrypt: theories/Crypt/package/pkg_rhl.v
* EasyCrypt pRHL
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β : Type*}

/-! ## The pRHL Judgment -/

/--
The fundamental pRHL judgment.

`rHoare Φ c₁ c₂ Ψ` (written `⊨ ⦃Φ⦄ c₁ ~ c₂ ⦃Ψ⦄`) means:

For all pairs of heaps (h₁, h₂) satisfying precondition Φ,
there exists a coupling of the output distributions (c₁ h₁) and (c₂ h₂)
such that all coupled pairs of outputs satisfy postcondition Ψ.

This is the semantic definition based on probabilistic couplings.
-/
def rHoare (Φ : RPre) (c₁ : SPComp α) (c₂ : SPComp β) (Ψ : RPost α β) : Prop :=
  ∀ h₁ h₂, Φ h₁ h₂ →
    liftR (fun (p₁ : α × Heap) (p₂ : β × Heap) => Ψ p₁.1 p₁.2 p₂.1 p₂.2)
          (c₁ h₁) (c₂ h₂)

/-! ## Basic properties -/

/-- rHoare is monotone in the postcondition -/
theorem rHoare_mono_post {Φ : RPre} {Ψ Ψ' : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (h : rHoare Φ c₁ c₂ Ψ)
    (hΨ : ∀ a₁ h₁ a₂ h₂, Ψ a₁ h₁ a₂ h₂ → Ψ' a₁ h₁ a₂ h₂) :
    rHoare Φ c₁ c₂ Ψ' := by
  intro h₁ h₂ hΦ
  have hh := h h₁ h₂ hΦ
  exact liftR_mono (fun p₁ p₂ hp => hΨ p₁.1 p₁.2 p₂.1 p₂.2 hp) hh

/-- rHoare is antimonotone in the precondition -/
theorem rHoare_mono_pre {Φ Φ' : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (h : rHoare Φ c₁ c₂ Ψ)
    (hΦ : ∀ h₁ h₂, Φ' h₁ h₂ → Φ h₁ h₂) :
    rHoare Φ' c₁ c₂ Ψ := by
  intro h₁ h₂ hΦ'
  exact h h₁ h₂ (hΦ h₁ h₂ hΦ')

end CatCrypt.Relational

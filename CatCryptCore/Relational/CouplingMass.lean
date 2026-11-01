/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.Judgment
public import CatCryptCore.Prob.Support

/-!
# Couplings preserve total mass

A coupling of two sub-distributions has the two sub-distributions as its marginals on the
successful outcomes, so both marginals carry the total mass of the joint sub-distribution: the
total mass of `d₁` equals that of `d₂`, and so does the failure mass at `none`. A relational
Hoare triple `rHoare Φ c c' Q` provides such a coupling at every pair of heaps related by `Φ`,
so `c` and `c'` have equal total mass there; under `eqPre` the two computations fail at the
same heaps, and `c` has no failure exactly when `c'` has no failure. This holds for every
postcondition `Q`.

No failure is stated as `∀ h, (c h) none = 0`, the unfolding of `SPComp.NoFail`.

## Main results

* `CatCrypt.Prob.Coupling.mass_eq` — the two marginals of a coupling have equal total mass
* `CatCrypt.Prob.Coupling.none_eq` — the two marginals of a coupling have equal failure mass
* `CatCrypt.Prob.liftR_mass_eq`, `CatCrypt.Prob.liftR_none_eq` — the same for a lifted relation
* `CatCrypt.Relational.rHoare_mass_eq`, `CatCrypt.Relational.rHoare_none_eq` — coupled
  computations have equal total mass and equal failure mass at related heaps
* `CatCrypt.Relational.rHoare_noFail_iff` — under `eqPre`, no failure of `c` is no failure
  of `c'`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Prob

variable {α β : Type*} {d₁ : SDistr α} {d₂ : SDistr β}

namespace Coupling

/-- The two marginals of a coupling have equal total mass. -/
theorem mass_eq (c : Coupling d₁ d₂) : SDistr.mass d₁ = SDistr.mass d₂ := by
  rw [← tsum_some_eq_mass, ← tsum_some_eq_mass]
  calc ∑' a, d₁ (some a) = ∑' a, ∑' b, c.joint (some (a, b)) := by
        simp only [c.left_marginal_sum]
    _ = ∑' b, ∑' a, c.joint (some (a, b)) := ENNReal.tsum_comm
    _ = ∑' b, d₂ (some b) := by simp only [c.right_marginal_sum]

/-- The two marginals of a coupling have equal failure mass. -/
theorem none_eq (c : Coupling d₁ d₂) : d₁ none = d₂ none := by
  have h1 := PMF.tsum_coe d₁
  have h2 := PMF.tsum_coe d₂
  rw [SDistr.tsum_option_eq_add, tsum_some_eq_mass, c.mass_eq] at h1
  rw [SDistr.tsum_option_eq_add, tsum_some_eq_mass] at h2
  have hm : SDistr.mass d₂ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  exact (ENNReal.add_left_inj hm).1 (h1.trans h2.symm)

end Coupling

/-- Two sub-distributions related by a lifted relation have equal total mass. -/
theorem liftR_mass_eq {R : α → β → Prop} (h : liftR R d₁ d₂) :
    SDistr.mass d₁ = SDistr.mass d₂ := by
  obtain ⟨c, -⟩ := h
  exact c.mass_eq

/-- Two sub-distributions related by a lifted relation have equal failure mass. -/
theorem liftR_none_eq {R : α → β → Prop} (h : liftR R d₁ d₂) : d₁ none = d₂ none := by
  obtain ⟨c, -⟩ := h
  exact c.none_eq

end CatCrypt.Prob

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β : Type*}

/-- Coupled computations have equal total mass at heaps related by the precondition. -/
theorem rHoare_mass_eq {Φ : RPre} {c : SPComp α} {c' : SPComp β} {Q : RPost α β}
    (h : rHoare Φ c c' Q) {h₁ h₂ : Heap} (hΦ : Φ h₁ h₂) :
    SDistr.mass (c h₁) = SDistr.mass (c' h₂) :=
  liftR_mass_eq (h h₁ h₂ hΦ)

/-- Coupled computations have equal failure mass at heaps related by the precondition. -/
theorem rHoare_none_eq {Φ : RPre} {c : SPComp α} {c' : SPComp β} {Q : RPost α β}
    (h : rHoare Φ c c' Q) {h₁ h₂ : Heap} (hΦ : Φ h₁ h₂) : (c h₁) none = (c' h₂) none :=
  liftR_none_eq (h h₁ h₂ hΦ)

/-- No failure transfers from left to right along a triple whose precondition relates some
heap to every right heap. -/
theorem rHoare_noFail_right {Φ : RPre} {c : SPComp α} {c' : SPComp β} {Q : RPost α β}
    (h : rHoare Φ c c' Q) (hΦ : ∀ h₂, ∃ h₁, Φ h₁ h₂) (hc : ∀ h₁, (c h₁) none = 0) :
    ∀ h₂, (c' h₂) none = 0 := by
  intro h₂
  obtain ⟨h₁, hh⟩ := hΦ h₂
  rw [← rHoare_none_eq h hh]
  exact hc h₁

/-- No failure transfers from right to left along a triple whose precondition relates every
left heap to some heap. -/
theorem rHoare_noFail_left {Φ : RPre} {c : SPComp α} {c' : SPComp β} {Q : RPost α β}
    (h : rHoare Φ c c' Q) (hΦ : ∀ h₁, ∃ h₂, Φ h₁ h₂) (hc' : ∀ h₂, (c' h₂) none = 0) :
    ∀ h₁, (c h₁) none = 0 := by
  intro h₁
  obtain ⟨h₂, hh⟩ := hΦ h₁
  rw [rHoare_none_eq h hh]
  exact hc' h₂

/-- Under `eqPre`, a computation has no failure exactly when its coupled partner has none,
for every postcondition. -/
theorem rHoare_noFail_iff {c : SPComp α} {c' : SPComp β} {Q : RPost α β}
    (h : rHoare eqPre c c' Q) : (∀ h₁, (c h₁) none = 0) ↔ ∀ h₂, (c' h₂) none = 0 :=
  ⟨rHoare_noFail_right h fun h₂ => ⟨h₂, rfl⟩, rHoare_noFail_left h fun h₁ => ⟨h₁, rfl⟩⟩

end CatCrypt.Relational

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.Judgment

/-!
# Span Liftings of Sub-Distributions

This file packages the relational lifting of `SDistr` in *span* form and proves
that it coincides with the coupling-based lifting `liftR` used by the exact
pRHL judgment `rHoare`.

A span over a relation `R : α → β → Prop` is the subtype
`{p : α × β // R p.1 p.2}` together with its two projections. Its lifting
through the sub-distribution monad relates `d₁ : SDistr α` and `d₂ : SDistr β`
when there is a witness distribution on the subtype whose projections are
exactly `d₁` and `d₂`. This is the monadic-relational-lifting view of
couplings: a coupling whose support respects `R` is the same data as a
distribution on the span carrier.

## Main definitions

* `SpanLift R d₁ d₂` — span lifting: a witness `w : SDistr {p // R p.1 p.2}`
  whose two projections are `d₁` and `d₂`

## Main results

* `spanLift_iff_liftR` — span lifting coincides with the coupling lifting
  (couplings = span lifting, exact case)
* `rHoare_iff_spanLift` — the exact pRHL judgment holds iff the span lifting
  holds pointwise at every pair of `Φ`-related initial heaps

## References

* T. Sato, *Approximate Span Liftings*, LICS 2019 — graded relational
  liftings of probability monads via spans (this file is the exact, grade-0
  layer; the graded layer is `CatCrypt.Relational.Approx`).
* S. Katsumata, T. Sato, *Codensity Liftings of Monads*, CALCO 2015 —
  relational liftings of monads; couplings as liftings of the (sub-)Giry
  monad.
* SSProve: theories/Crypt/rhl_semantics/only_prob/Couplings.v
-/

@[expose] public section

namespace CatCrypt.Prob

open scoped ENNReal

variable {α β : Type*}

/-! ## A computation lemma for `bind` -/

/-- Pointwise formula for `SDistr.bind` at a `some` value:
    the `none` branch of the underlying `PMF.bind` contributes nothing. -/
theorem SDistr.bind_apply_some {α β : Type*} (d : SDistr α) (g : α → SDistr β) (x : β) :
    (d.bind g) (some x) = ∑' a, d (some a) * (g a) (some x) := by
  show (PMF.bind d _) (some x) = _
  rw [PMF.bind_apply, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail_apply_some, mul_zero, zero_add]

/-! ## Span lifting -/

/-- **Span lifting** of a relation `R` through the sub-distribution monad.

    `SpanLift R d₁ d₂` holds when there is a witness distribution `w` on the
    span carrier `{p : α × β // R p.1 p.2}` whose two projections are exactly
    `d₁` and `d₂`. The support condition of couplings is internalized in the
    type of the witness: every point of the carrier satisfies `R` by
    construction. -/
def SpanLift (R : α → β → Prop) (d₁ : SDistr α) (d₂ : SDistr β) : Prop :=
  ∃ w : SDistr {p : α × β // R p.1 p.2},
    (w.bind fun s => SDistr.pure s.val.1) = d₁ ∧
    (w.bind fun s => SDistr.pure s.val.2) = d₂

/-- Span lifting implies the coupling lifting: push the witness forward along
    the span's mediating map into `α × β`; the marginal conditions follow by
    the monad laws, and the support condition holds because every point in the
    image carries a proof of `R`. -/
theorem liftR_of_spanLift {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    (h : SpanLift R d₁ d₂) : d₁ ⟨R⟩# d₂ := by
  classical
  obtain ⟨w, hw₁, hw₂⟩ := h
  refine ⟨{ joint := w.bind fun s => SDistr.pure s.val
            left_marginal := fun a => ?_
            right_marginal := fun b => ?_ }, ?_⟩
  · rw [SDistr.bind_assoc]
    simp only [SDistr.pure_bind]
    rw [hw₁]
  · rw [SDistr.bind_assoc]
    simp only [SDistr.pure_bind]
    rw [hw₂]
  · intro a b hab
    rw [SDistr.bind_apply_some] at hab
    obtain ⟨s, hs⟩ : ∃ s, w (some s) * (SDistr.pure s.val) (some (a, b)) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hab (ENNReal.tsum_eq_zero.mpr hc)
    have hval : s.val = (a, b) := by
      by_contra hne
      rw [SDistr.pure_apply_some, if_neg hne, mul_zero] at hs
      exact hs rfl
    have hR := s.property
    rw [hval] at hR
    exact hR

/-- The coupling lifting implies span lifting: restrict the joint distribution
    to the span carrier. On the support of the joint, `R` holds (by the
    coupling's support condition), so the restriction loses no mass and the
    projections recover the marginals. -/
theorem spanLift_of_liftR {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    (h : d₁ ⟨R⟩# d₂) : SpanLift R d₁ d₂ := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨c.joint.bind fun p =>
      if hp : R p.1 p.2 then SDistr.pure (⟨p, hp⟩ : {p : α × β // R p.1 p.2})
      else SDistr.fail, ?_, ?_⟩
  · rw [SDistr.bind_assoc]
    have heq : c.joint.bind (fun p =>
        (if hp : R p.1 p.2 then SDistr.pure (⟨p, hp⟩ : {p : α × β // R p.1 p.2})
         else SDistr.fail).bind fun s => SDistr.pure s.val.1)
        = c.joint.bind (fun p => SDistr.pure p.1) := by
      apply SDistr.bind_congr_support
      intro p hp0
      have hR : R p.1 p.2 := hc p.1 p.2 hp0
      rw [dif_pos hR, SDistr.pure_bind]
    rw [heq]
    exact SDistr.eq_of_some_eq c.left_marginal
  · rw [SDistr.bind_assoc]
    have heq : c.joint.bind (fun p =>
        (if hp : R p.1 p.2 then SDistr.pure (⟨p, hp⟩ : {p : α × β // R p.1 p.2})
         else SDistr.fail).bind fun s => SDistr.pure s.val.2)
        = c.joint.bind (fun p => SDistr.pure p.2) := by
      apply SDistr.bind_congr_support
      intro p hp0
      have hR : R p.1 p.2 := hc p.1 p.2 hp0
      rw [dif_pos hR, SDistr.pure_bind]
    rw [heq]
    exact SDistr.eq_of_some_eq c.right_marginal

/-- **Couplings = span lifting, exact case**: the coupling-based lifting of a
    relation through `SDistr` coincides with its span lifting. -/
theorem spanLift_iff_liftR {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β} :
    SpanLift R d₁ d₂ ↔ (d₁ ⟨R⟩# d₂) :=
  ⟨liftR_of_spanLift, spanLift_of_liftR⟩

end CatCrypt.Prob

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β : Type*}

/-- **The exact pRHL judgment is the pointwise span lifting**: `rHoare Φ c₁ c₂ Ψ`
    holds iff, at every pair of `Φ`-related initial heaps, the output
    sub-distributions are related by the span lifting of the (paired)
    postcondition. This identifies the coupling-based judgment of
    `CatCrypt.Relational.Judgment` with the relational-lifting view of
    Katsumata–Sato (CALCO 2015). -/
theorem rHoare_iff_spanLift {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β} :
    rHoare Φ c₁ c₂ Ψ ↔
      ∀ h₁ h₂, Φ h₁ h₂ →
        SpanLift (fun (p₁ : α × Heap) (p₂ : β × Heap) => Ψ p₁.1 p₁.2 p₂.1 p₂.2)
          (c₁ h₁) (c₂ h₂) := by
  constructor
  · intro h h₁ h₂ hΦ
    exact spanLift_of_liftR (h h₁ h₂ hΦ)
  · intro h h₁ h₂ hΦ
    exact liftR_of_spanLift (h h₁ h₂ hΦ)

end CatCrypt.Relational

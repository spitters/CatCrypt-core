/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Order.Basic

set_option autoImplicit false

/-! # Effectus Theory

An effectus (Cho-Jacobs 2015) is a category with coproducts and a terminal
object satisfying axioms about pullbacks along coproduct injections.
We define the key properties needed for Kantorovich UCMonads.

## Mathematical context

In the effectus framework, a **predicate** on an object X is a morphism
`p : X → 1 + 1` in the Kleisli category. The two injections `κ₁, κ₂ : 1 → 1 + 1`
represent "true" and "false". The **predicate transformer** `wp(f, p)` is
defined by post-composition: `wp(f, p) = p ∘ f`.

The effectus axioms (E1-E3) ensure that predicates form an effect module:
* (E1) Finite coproducts exist and are disjoint
* (E2) Partial addition of predicates: `p ⊕ q` is defined when `p + q ≤ 1`
* (E3) **Positive cancellation**: `p ⊕ q = 0 ⟹ p = 0 ∧ q = 0`

Axiom (E3) is the key one for cryptographic applications. In the Kleisli
category of a probability monad, it says: if a sum of non-negative quantities
is zero, each quantity is zero. This is the property that makes game-hopping
arguments valid — if an adversary has zero advantage, no sub-computation
can have negative advantage "cancelling out" a positive one.

## Relation to UCMonadPosCancel

The `UCMonadPosCancel` class in `CatCrypt.Crypto.KantorovichUCMonad` is the
metric-enriched version of (E3): instead of "sum = 0 implies each = 0" for
predicates, it states "sum of distances = 0 implies each distance = 0" for
Kleisli morphisms. This file provides the categorical/predicate-level
framing that motivates the metric version.

## Main definitions

* `EffectusPred` — a predicate in the Kleisli category (map to `Bool`)
* `wpTransformer` — the weakest-precondition predicate transformer
* `EffectusPositiveCancel` — the positive cancellation axiom (E3) for a monad

## References

* Cho, K. & Jacobs, B. (2015). An introduction to effectus theory.
* Cho, K. & Jacobs, B. (2019). Disintegration and Bayesian inversion via
  string diagrams. MSCS 29(7).
-/

namespace CatCrypt.Category.Effectus

/-! ## Predicates in the Kleisli Category -/

/-- An **effectus predicate** on type `α` in the Kleisli category of `T` is
    a Kleisli morphism `α → T Bool`. The value `true` represents "accept"
    and `false` represents "reject".

    This is equivalent to the standard effectus formulation using `1 + 1`,
    since `Bool ≅ Unit ⊕ Unit`, but avoids universe issues.

    For `T = SPComp` (sub-distribution monad), this is an event: a function
    that maps each state to a distribution over {true, false, ⊥}.

    For `T = QComp d` (quantum monad), this is a binary-outcome instrument:
    a POVM with two elements (accept/reject). -/
structure EffectusPred (T : Type → Type) (α : Type) where
  /-- The underlying Kleisli morphism -/
  pred : α → T Bool

@[ext]
theorem EffectusPred.ext {T : Type → Type} {α : Type}
    {p q : EffectusPred T α} (h : p.pred = q.pred) : p = q := by
  cases p; cases q; congr

/-- The **one predicate** always accepts (maps to `true`). -/
def EffectusPred.one (T : Type → Type) [Monad T] (α : Type) :
    EffectusPred T α :=
  ⟨fun _ => pure true⟩

/-- The **zero predicate** always rejects (maps to `false`). -/
def EffectusPred.falseP (T : Type → Type) [Monad T] (α : Type) :
    EffectusPred T α :=
  ⟨fun _ => pure false⟩

/-! ## Predicate Transformer (Weakest Precondition) -/

/-- The **predicate transformer** `wp(f, p)` for a Kleisli morphism `f : α → T β`
    and predicate `p : EffectusPred T β` is defined by Kleisli composition:
    `wp(f, p)(a) = f(a) >>= p.pred`. This is the "weakest precondition"
    transformer in the effectus framework.

    In probabilistic terms: `wp(f, p)(a)` gives the probability that running
    `f` on input `a` and then testing with `p` yields "accept". -/
def wpTransformer {T : Type → Type} [Monad T] {α β : Type}
    (f : α → T β) (p : EffectusPred T β) : EffectusPred T α :=
  ⟨fun a => f a >>= p.pred⟩

/-- Predicate transformer is functorial: `wp(pure, p) = p`. -/
theorem wpTransformer_pure {T : Type → Type} [Monad T] [LawfulMonad T]
    {α : Type} (p : EffectusPred T α) :
    wpTransformer (pure : α → T α) p = p := by
  ext; simp [wpTransformer, pure_bind]

/-- Predicate transformer composes: `wp(f ∘ₖ g, p) = wp(f, wp(g, p))`. -/
theorem wpTransformer_comp {T : Type → Type} [Monad T] [LawfulMonad T]
    {α β γ : Type} (f : α → T β) (g : β → T γ) (p : EffectusPred T γ) :
    wpTransformer (fun a => f a >>= g) p =
    wpTransformer f (wpTransformer g p) := by
  ext; simp [wpTransformer, bind_assoc]

/-! ## Positive Cancellation (Effectus Axiom E3) -/

/-- **Positive cancellation** for the Kleisli category of `T`.

    This is axiom (E3) from Cho-Jacobs (2015): if the "sum" of two predicates
    equals the zero predicate, then each predicate is individually zero.

    We state this in a monad-agnostic way: post-composing two Kleisli morphisms
    with any test predicate and getting the same result implies the morphisms
    are equal. This is the "separation by tests" property.

    For classical probability (`SPComp`), this says:
    if `∀ D : β → SPComp Bool, Pr[f₁;D] = Pr[f₂;D]`, then `f₁ = f₂`
    (as sub-distributions).

    For quantum (`QComp d`), this says:
    if two instruments give the same measurement statistics for all binary
    measurements, they are equal.

    This class captures the **qualitative** (non-metric) version. The metric
    version is `UCMonadPosCancel` in `KantorovichUCMonad.lean`. -/
class EffectusPositiveCancel (T : Type → Type) [Monad T] where
  /-- If post-composing `f₁` and `f₂` with every test yields the same
      result, then `f₁ = f₂`. This is the "separation by tests" property. -/
  posCancel {α β : Type} (f₁ f₂ : α → T β) :
    (∀ (p : EffectusPred T β), wpTransformer f₁ p = wpTransformer f₂ p) →
    f₁ = f₂

/-- Positive cancellation implies that the predicate transformer is faithful:
    `wp(f₁, −) = wp(f₂, −)` implies `f₁ = f₂`. -/
theorem wpTransformer_faithful {T : Type → Type} [Monad T]
    [EffectusPositiveCancel T]
    {α β : Type} (f₁ f₂ : α → T β)
    (h : ∀ p, wpTransformer f₁ p = wpTransformer f₂ p) :
    f₁ = f₂ :=
  EffectusPositiveCancel.posCancel f₁ f₂ h

/-- Positive cancellation is preserved by Kleisli composition on the left:
    if `g₁ = g₂` (established via tests), then `f >>= g₁ = f >>= g₂`. -/
theorem posCancel_comp_left {T : Type → Type} [Monad T] [LawfulMonad T]
    [EffectusPositiveCancel T]
    {α β γ : Type} (f : α → T β) (g₁ g₂ : β → T γ)
    (h : ∀ p, wpTransformer g₁ p = wpTransformer g₂ p) :
    (fun a => f a >>= g₁) = (fun a => f a >>= g₂) := by
  have heq := EffectusPositiveCancel.posCancel g₁ g₂ h
  rw [heq]

/-! ## Stronger Separation: Arbitrary Codomain Tests

The effectus axiom (E3) traditionally uses Boolean tests (predicates to
`1 + 1`). A stronger version uses tests to arbitrary types — this is
what `UCMonadPosCancel` does in the metric setting. We show that with
`LawfulMonad`, the stronger version follows from the Boolean version
by taking `k = pure`. -/

/-- Strong positive cancellation: separation by **all** Kleisli morphisms
    (not just Boolean tests). This matches `UCMonadPosCancel`. -/
class EffectusStrongPosCancel (T : Type → Type) [Monad T] where
  /-- If post-composing `f₁` and `f₂` with every Kleisli morphism yields
      the same result, then `f₁ = f₂`. -/
  strongPosCancel {α β : Type} (f₁ f₂ : α → T β) :
    (∀ (γ : Type) (k : β → T γ),
      (fun a => f₁ a >>= k) = (fun a => f₂ a >>= k)) →
    f₁ = f₂

/-- `EffectusPositiveCancel` (Boolean tests suffice) implies
    `EffectusStrongPosCancel` (all tests suffice), since the all-tests
    hypothesis is strictly stronger than the Boolean-tests hypothesis.
    With `LawfulMonad`, the all-k hypothesis with `k = pure` already
    gives `f₁ = f₂` via `bind_pure`. -/
instance (T : Type → Type) [Monad T] [LawfulMonad T]
    [EffectusPositiveCancel T] : EffectusStrongPosCancel T where
  strongPosCancel {α β} f₁ f₂ h := by
    -- From all-k agreement, specialise to k = pure to get f₁ = f₂
    have hpure := h β pure
    simp only [bind_pure] at hpure
    exact hpure

/-- With `LawfulMonad`, strong positive cancellation follows from taking
    `k = pure` in the "all morphisms" quantifier. -/
theorem strongPosCancel_of_pure {T : Type → Type} [Monad T] [LawfulMonad T]
    {α β : Type} (f₁ f₂ : α → T β)
    (h : (fun a => f₁ a >>= (pure : β → T β)) =
         (fun a => f₂ a >>= (pure : β → T β))) :
    f₁ = f₂ := by
  simp [bind_pure] at h
  exact h

/-! ## Connection to Metric Enrichment

The effectus axiom (E3) is the qualitative backbone of the metric-enriched
positive cancellation in `UCMonadPosCancel`. The relationship is:

* `EffectusPositiveCancel` says: **equality** of all test outcomes implies
  **equality** of morphisms.
* `UCMonadPosCancel` says: **zero distance** in all post-processings implies
  **zero distance** of morphisms.

When the monad's pseudometric is faithful (`ucSdist f g = 0 → f = g`),
the metric version implies the qualitative version. In general, the metric
version is stated up to the equivalence relation induced by the pseudometric.
-/

end CatCrypt.Category.Effectus

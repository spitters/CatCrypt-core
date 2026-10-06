/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.Approx

/-!
# Relational Q₀-monads: the coupling structure for a generic approximate relational logic

The Approxis reconstruction (`ApproxisRelational.lean`) fixes the effect to `SDistr`.
This file abstracts the structure that reconstruction actually consumes — a monad with
a **graded approximate relational lifting** and its four laws (pure, grade-additive
bind, relation- and grade-monotonicity) — into a typeclass `RelQ0`. It is the first
step of extending the reconstruction from the classical effect to every
coupling-equipped Q₀-monad: `SDistr` is the classical instance here, `QComp` (quantum
couplings, `Quantum/ApproxRelational.lean`) is the intended second.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt

open scoped ENNReal
open CatCrypt.Prob CatCrypt.Relational

/-- A **relational Q₀-monad**: a probabilistic effect `T` with monad operations and a
graded approximate relational lifting `liftR ε R m₁ m₂` — couple `m₁, m₂` up to error
`ε` with support in `R` — satisfying the coupling laws an approximate relational
program logic needs. -/
class RelQ0 (T : Type → Type) where
  pure' : {α : Type} → α → T α
  bind' : {α β : Type} → T α → (α → T β) → T β
  liftR : {α β : Type} → ℝ≥0∞ → (α → β → Prop) → T α → T β → Prop
  liftR_pure : ∀ {α β : Type} {a : α} {b : β} {R : α → β → Prop},
    R a b → liftR 0 R (pure' a) (pure' b)
  liftR_bind : ∀ {α β α' β' : Type} {ε δ : ℝ≥0∞} {R : α → β → Prop} {S : α' → β' → Prop}
    {m₁ : T α} {m₂ : T β} {k₁ : α → T α'} {k₂ : β → T β'},
    liftR ε R m₁ m₂ → (∀ a b, R a b → liftR δ S (k₁ a) (k₂ b)) →
    liftR (ε + δ) S (bind' m₁ k₁) (bind' m₂ k₂)
  liftR_mono_rel : ∀ {α β : Type} {ε : ℝ≥0∞} {R S : α → β → Prop} {m₁ : T α} {m₂ : T β},
    (∀ a b, R a b → S a b) → liftR ε R m₁ m₂ → liftR ε S m₁ m₂
  liftR_mono_eps : ∀ {α β : Type} {ε ε' : ℝ≥0∞} {R : α → β → Prop} {m₁ : T α} {m₂ : T β},
    ε ≤ ε' → liftR ε R m₁ m₂ → liftR ε' R m₁ m₂

/-- The classical instance: `SDistr` with the sub-coupling lifting `liftRApprox`. -/
noncomputable instance instRelQ0SDistr : RelQ0 SDistr where
  pure' := SDistr.pure
  bind' := SDistr.bind
  liftR := liftRApprox
  liftR_pure h := liftRApprox_of_liftR (liftR_pure h)
  liftR_bind h hf := liftRApprox_bind h hf
  liftR_mono_rel hRS h := liftRApprox_mono_rel hRS h
  liftR_mono_eps hε h := liftRApprox_mono_eps hε h

/-! ## Higher-order layer: arrow-type relational lifting

The first-order judgment `RelQ0.liftR` relates values. The extension to *function*
types — the arrow-type case the first-order judgment cannot express — is definable
over any `RelQ0` and its compatibility rules are derivable from the four
first-order laws, so it holds for every coupling-equipped Q₀-monad at once. -/

/-- Higher-order (arrow-type) relational lifting: Kleisli arrows `f, g` are related
at `R ⇒ S` and grade `ε` when they send `R`-related arguments to `liftR ε S`-related
results. -/
def liftRArr {T : Type → Type} [RelQ0 T] {α α' β β' : Type}
    (ε : ℝ≥0∞) (R : α → α' → Prop) (S : β → β' → Prop)
    (f : α → T β) (g : α' → T β') : Prop :=
  ∀ a a', R a a' → RelQ0.liftR ε S (f a) (g a')

/-- Arrow elimination (application): an `R ⇒ S`-related function pair, applied to
`R`-related arguments, yields `liftR ε S`-related results. -/
theorem liftRArr_app {T : Type → Type} [RelQ0 T] {α α' β β' : Type}
    {ε : ℝ≥0∞} {R : α → α' → Prop} {S : β → β' → Prop}
    {f : α → T β} {g : α' → T β'} {a : α} {a' : α'}
    (hfg : liftRArr ε R S f g) (ha : R a a') : RelQ0.liftR ε S (f a) (g a') :=
  hfg a a' ha

/-- Kleisli composition of arrow-related pairs, grade-additive — the higher-order
form of the first-order bind rule, over any coupling-equipped Q₀-monad. -/
theorem liftRArr_kleisli {T : Type → Type} [RelQ0 T] {α α' β β' γ γ' : Type}
    {ε δ : ℝ≥0∞} {R : α → α' → Prop} {S : β → β' → Prop} {U : γ → γ' → Prop}
    {f : α → T β} {g : α' → T β'} {k : β → T γ} {k' : β' → T γ'}
    (hfg : liftRArr ε R S f g) (hkk' : liftRArr δ S U k k') :
    liftRArr (ε + δ) R U (fun a => RelQ0.bind' (f a) k)
      (fun a' => RelQ0.bind' (g a') k') :=
  fun a a' ha => RelQ0.liftR_bind (hfg a a' ha) (fun b b' hb => hkk' b b' hb)

/-- Grade monotonicity lifts to arrows. -/
theorem liftRArr_mono_eps {T : Type → Type} [RelQ0 T] {α α' β β' : Type}
    {ε ε' : ℝ≥0∞} {R : α → α' → Prop} {S : β → β' → Prop}
    {f : α → T β} {g : α' → T β'} (hε : ε ≤ ε') (h : liftRArr ε R S f g) :
    liftRArr ε' R S f g :=
  fun a a' ha => RelQ0.liftR_mono_eps hε (h a a' ha)

/- The guarded (step-indexed) higher-order layer lives in `RelationalQ0Guarded.lean`,
built on iris-lean's `SiProp` (the topos of trees) — the same step-indexed
propositions `refines` uses — rather than a hand-rolled copy. -/

end CatCrypt

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCPullbackSemantics

/-!
# Metric advantage theories and the denotation of systems

An advantage theory `T` is *metric* (`AdvTheory.Metric`) when its advantage vanishes on the
diagonal, is symmetric and satisfies the triangle inequality at every test. The systems of a
metric theory form a symmetric category enriched in the grades `T.Test → ℝ≥0∞`, and realization
(`AdvTheory.Realizes`) is the graded relation of that enrichment: it is reflexive at bound `0`,
symmetric, transitive with added bounds and monotone in the bound.

`Denotes α E O` assigns to each object of `α` a reactive system with interface `(E, O)`, its
denotation `⟦x⟧`; statements about a game language read `Realizes ⟦G⟧ ⟦G'⟧ ε`.

## Main definitions

* `AdvTheory.Metric`: the metric laws of an advantage theory.
* `Denotes`, with the scoped notation `⟦x⟧` for `Denotes.den x`.

## Main results

* `AdvTheory.Realizes.refl`, `.symm`, `.trans`, `.mono`: the laws of the graded relation.
* `envTheory_metric`, `gameTheory_metric`: the environment theory and the oracle-game theory
  are metric.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

universe u v

/-- An advantage theory is metric: the advantage of every test vanishes between a system and
itself, is symmetric in the two systems and satisfies the triangle inequality. -/
class AdvTheory.Metric (T : AdvTheory.{u, v}) : Prop where
  /-- The advantage between a system and itself is `0`. -/
  adv_self : ∀ x t, T.adv x x t = 0
  /-- The advantage is symmetric in the two systems. -/
  adv_symm : ∀ x y t, T.adv x y t = T.adv y x t
  /-- The triangle inequality. -/
  adv_triangle : ∀ x y z t, T.adv x z t ≤ T.adv x y t + T.adv y z t

namespace AdvTheory.Realizes

variable {T : AdvTheory.{u, v}} {x y z : T.System} {b c : T.Test → ℝ≥0∞}

/-- In a metric theory every system realizes itself with bound `0`. -/
theorem refl [T.Metric] (x : T.System) : T.Realizes x x 0 := fun t => by
  simp [AdvTheory.Metric.adv_self x t]

/-- In a metric theory realization is symmetric. -/
theorem symm [T.Metric] (h : T.Realizes x y b) : T.Realizes y x b := fun t => by
  grind [AdvTheory.Metric.adv_symm, AdvTheory.Realizes]

/-- In a metric theory realization is transitive, with the bounds added. -/
theorem trans [T.Metric] (h₁ : T.Realizes x y b) (h₂ : T.Realizes y z c) :
    T.Realizes x z (b + c) := fun t =>
  (AdvTheory.Metric.adv_triangle x y z t).trans (add_le_add (h₁ t) (h₂ t))

/-- Realization is monotone in the bound. -/
theorem mono (h : T.Realizes x y b) (hle : b ≤ c) : T.Realizes x y c := fun t =>
  (h t).trans (hle t)

end AdvTheory.Realizes

/-- A bound of realization of reactive systems can be raised. -/
theorem Realizes.mono {τ υ E O : Type} {R : Sys τ E O} {I : Sys υ E O}
    {b b' : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes R I b)
    (hb : ∀ ζ Z, b ζ Z ≤ b' ζ Z) : Realizes R I b' :=
  fun ζ => (h ζ).mono (hb ζ)

/-- The environment theory is metric. -/
instance envTheory_metric (E O : Type) : (envTheory E O).Metric where
  adv_self X Z := by
    simp [envTheory, adv, Env.gap, absDiff]
  adv_symm X Y Z := by
    simp only [envTheory, adv, Env.gap]
    exact absDiff_comm _ _
  adv_triangle X Y W Z := by
    simp only [envTheory, adv, Env.gap]
    exact absDiff_triangle _ _ _

/-- The oracle-game theory is metric. -/
instance gameTheory_metric (Q A : Type) : (gameTheory Q A).Metric where
  adv_self G B := by
    simp [gameTheory, KeyedGame.advantage, absDiff]
  adv_symm G G' B := by
    simp only [gameTheory, KeyedGame.advantage]
    exact absDiff_comm _ _
  adv_triangle G G' G'' B := by
    simp only [gameTheory, KeyedGame.advantage]
    exact absDiff_triangle _ _ _

/-- A denotation of the objects of `α` as reactive systems with interface `(E, O)`: each `x`
has a state type `St x` and a system `den x`. -/
class Denotes (α : Type*) (E O : outParam Type) where
  /-- The state type of the denotation of `x`. -/
  St : α → Type
  /-- The denotation of `x` as a reactive system. -/
  den : (x : α) → Sys (St x) E O

/-- `⟦x⟧` is the denotation of `x` as a reactive system. -/
scoped notation "⟦" x "⟧" => Denotes.den x

example {α E O : Type} [Denotes α E O] (x y : α) (b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (h : Realizes ⟦x⟧ ⟦y⟧ b) : Realizes (Denotes.den x) (Denotes.den y) b := h

end CatCrypt.Crypto.UCTransparent

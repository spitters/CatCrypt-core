/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.Code

@[expose] public section
set_option autoImplicit false

/-!
# Sequencing a `Fin n`-indexed family of computations

`SPComp.seqFin n β g` runs `g 0, g 1, …, g (n - 1)` in this order and returns
the dependent tuple of their results. `SPComp.seqVec` is its specialisation to a
constant result type.

## Main definitions

* `SPComp.seqFin` - dependent sequencing of `g : (j : Fin n) → SPComp (β j)`
* `SPComp.seqVec` - non-dependent sequencing of `f : Fin n → SPComp α`

## Main results

* `SPComp.seqFin_isPure`, `SPComp.seqVec_isPure` - a sequence of pure
  computations is pure
* `SPComp.seqFin_split` - a pure coordinate can be run first and its result
  substituted into its position
* `SPComp.seqFin_congr`, `SPComp.seqVec_congr` - pointwise equal families give
  equal sequences
* `SPComp.seqVec_bind_pure` - sequencing commutes with a pointwise
  deterministic post-processing
* `SPComp.seqVec_discard` - a sequence of computations that are discardable
  (their result dropped, they equal `pure k`) is discardable
-/

namespace CatCrypt.Core

namespace SPComp

/-- Runs the computations `g 0, …, g (n - 1)` in order and returns their results
as a dependent tuple. -/
noncomputable def seqFin : (n : ℕ) → (β : Fin n → Type) → ((j : Fin n) → SPComp (β j)) →
    SPComp ((j : Fin n) → β j)
  | 0, _, _ => SPComp.pure fun j => j.elim0
  | n + 1, _, g =>
    (g 0).bind fun x => (seqFin n _ fun j => g j.succ).bind fun xs =>
      SPComp.pure (Fin.cons x xs)

/-- Runs the computations `f 0, …, f (n - 1)` in order and returns the vector of
their results. -/
noncomputable def seqVec {α : Type} (n : ℕ) (f : Fin n → SPComp α) : SPComp (Fin n → α) :=
  seqFin n (fun _ => α) f

/-- The empty sequence returns the empty tuple. -/
theorem seqFin_zero (β : Fin 0 → Type) (g : (j : Fin 0) → SPComp (β j)) :
    seqFin 0 β g = SPComp.pure fun j => j.elim0 := rfl

/-- A sequence of length `n + 1` runs `g 0`, then the sequence of the tail family. -/
theorem seqFin_succ (n : ℕ) (β : Fin (n + 1) → Type) (g : (j : Fin (n + 1)) → SPComp (β j)) :
    seqFin (n + 1) β g =
      (g 0).bind fun x => (seqFin n (fun j => β j.succ) fun j => g j.succ).bind fun xs =>
        SPComp.pure (Fin.cons x xs) := rfl

/-- The empty sequence returns the empty vector. -/
theorem seqVec_zero {α : Type} (f : Fin 0 → SPComp α) :
    seqVec 0 f = SPComp.pure Fin.elim0 := rfl

/-- The unfolding of `seqVec` at a successor, stated in `do` form with the
head index `⟨0, _⟩` and the tail family `fun i => f ⟨i.val + 1, _⟩`. -/
theorem seqVec_succ {α : Type} (n : ℕ) (f : Fin (n + 1) → SPComp α) :
    seqVec (n + 1) f = (do
      let head ← f ⟨0, Nat.zero_lt_succ n⟩
      let tail ← seqVec n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      SPComp.pure (Fin.cons head tail)) := rfl

/-- A sequence of pure computations is pure. -/
theorem seqFin_isPure : ∀ (n : ℕ) (β : Fin n → Type) (g : (j : Fin n) → SPComp (β j)),
    (∀ j, IsPure (g j)) → IsPure (seqFin n β g)
  | 0, _, _, _ => pure_isPure _
  | n + 1, β, g, h => bind_isPure (h 0) fun _ =>
      bind_isPure (seqFin_isPure n (fun j => β j.succ) (fun j => g j.succ) fun j => h j.succ)
        fun _ => pure_isPure _

/-- A sequence of pure computations is pure. -/
theorem seqVec_isPure {α : Type} (n : ℕ) (f : Fin n → SPComp α) (h : ∀ i, IsPure (f i)) :
    IsPure (seqVec n f) :=
  seqFin_isPure n _ f h

/-- A pure coordinate of `seqFin` can be run first, its result substituted
into its position. -/
theorem seqFin_split : ∀ (n : ℕ) (β : Fin n → Type) (g : (j : Fin n) → SPComp (β j))
    (t : Fin n), IsPure (g t) →
    seqFin n β g = (g t).bind fun x => seqFin n β (Function.update g t (SPComp.pure x))
  | 0, _, _, t, _ => t.elim0
  | n + 1, β, g, t, h => by
    cases t using Fin.cases with
    | zero =>
      simp only [seqFin, Function.update_self, pure_bind, ne_eq, Fin.succ_ne_zero,
        not_false_eq_true, Function.update_of_ne]
    | succ s =>
      have ih := seqFin_split n (fun j => β j.succ) (fun j => g j.succ) s h
      simp only [seqFin, ih, bind_assoc]
      rw [← isPure_bind_comm_left (g s.succ) (g 0) _ h]
      congr 1; funext x
      rw [Function.update_of_ne (Fin.succ_ne_zero s).symm,
        Function.update_comp_eq_of_injective' g (Fin.succ_injective n) s (SPComp.pure x)]

/-- Pointwise equal families give equal sequences. -/
theorem seqFin_congr {n : ℕ} {β : Fin n → Type} {g₁ g₂ : (j : Fin n) → SPComp (β j)}
    (h : ∀ j, g₁ j = g₂ j) : seqFin n β g₁ = seqFin n β g₂ := by
  rw [funext h]

/-- Pointwise equal families give equal sequences. -/
theorem seqVec_congr {α : Type} {n : ℕ} {f₁ f₂ : Fin n → SPComp α} (h : ∀ i, f₁ i = f₂ i) :
    seqVec n f₁ = seqVec n f₂ := by
  rw [funext h]

/-- Sequencing the computations `bind (h i) (pure ∘ ψ i)` equals sequencing the
`h i` and applying `ψ` pointwise afterwards. -/
theorem seqVec_bind_pure {α γ : Type} :
    ∀ {n : ℕ} (h : Fin n → SPComp α) (ψ : Fin n → α → γ),
      seqVec n (fun i => SPComp.bind (h i) (fun a => SPComp.pure (ψ i a))) =
        SPComp.bind (seqVec n h) (fun R => SPComp.pure (fun i => ψ i (R i)))
  | 0, h, ψ => by
    simp only [seqVec_zero, pure_bind]
    congr 1; funext i; exact i.elim0
  | n + 1, h, ψ => by
    have ih := seqVec_bind_pure (fun i => h i.succ) (fun i => ψ i.succ)
    simp only [seqVec, seqFin_succ] at ih ⊢
    rw [ih]
    simp only [bind_assoc, pure_bind]
    congr 1; funext a
    congr 1; funext R
    congr 1; funext i
    cases i using Fin.cases <;> rfl

/-- A sequence of computations each of which, with its result discarded, equals
`pure k`, also equals `pure k` with its result discarded. -/
theorem seqVec_discard {α X : Type} (k : X) :
    ∀ {n : ℕ} (g : Fin n → SPComp α)
      (_hg : ∀ i, SPComp.bind (g i) (fun _ => SPComp.pure k) = SPComp.pure k),
      SPComp.bind (seqVec n g) (fun _ => SPComp.pure k) = SPComp.pure k
  | 0, _, _ => by simp only [seqVec_zero, pure_bind]
  | n + 1, g, hg => by
    have ih := seqVec_discard k (fun i => g i.succ) fun i => hg i.succ
    simp only [seqVec, seqFin_succ] at ih ⊢
    simp only [bind_assoc, pure_bind, ih]
    exact hg 0

end SPComp

end CatCrypt.Core

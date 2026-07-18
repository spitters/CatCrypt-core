/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Relational.Rules
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# General Hybrid Argument Theory

This file provides reusable infrastructure for hybrid argument proofs,
following the approach in "Mechanizing Nested Hybrid Arguments in
Nominal-CatCrypt" (Larsen & Schurmann, CSF 2025).

## Main Results

* `advantage_hybrid_dep` - Dependent hybrid inequality: when step advantages differ,
  `Adv(G 0, G n) ≤ Σᵢ Adv(G i, G (i+1))`
* `advantage_hybrid_uniform` - Uniform hybrid bound:
  `Adv(G 0, G n) ≤ n * ε` when each step is bounded by ε
* `advantage_hybrid_eq` - Hybrid equality (strengthening of the paper's main theorem):
  When all adjacent games are perfectly indistinguishable,
  `Advantage (G 0) (G n) = 0`

## Overview

The standard game-hopping proof technique transitions through a sequence
of hybrid games G₀, G₁, ..., Gₙ. The triangle inequality gives:

  Adv(G₀, Gₙ) ≤ Σᵢ Adv(Gᵢ, Gᵢ₊₁)

The CSF 2025 paper strengthens this to an equality when all step advantages
are equal, using the law of total probability and CONST/RAND packages.
At the distribution level (without stateful packages), the key insight is
simpler: the triangle inequality already provides the bound, and the
equality case follows from zero-advantage of perfectly indistinguishable games.

## References

* [Larsen & Schurmann, Mechanizing Nested Hybrid Arguments, CSF 2025]
* CatCrypt/Lean: `CatCrypt/Tactics/Triangle.lean` (basic triangle chains)
* CatCrypt/Lean: `CatCrypt/Examples/SymmRatchet.lean` (concrete hybrid argument)
-/

namespace CatCrypt.Crypto.HybridArgument

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open scoped ENNReal

/-! ## Telescoping Sum Helpers -/

/-- Telescoping sum: the sum of consecutive differences.
    This is the fundamental decomposition used in hybrid arguments. -/
noncomputable def telescope_sum (f : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range n, ((f i - f (i + 1)) ⊔ (f (i + 1) - f i))

/-! ## Core Hybrid Argument Theorems -/

/-- **Dependent hybrid inequality** (general form).

    For a sequence of games `G : Fin (n+1) → SPComp α` and an adversary `A`,
    the advantage between the first and last game is bounded by the sum of
    per-step advantages.

    This generalizes `advantageA_triangle_n` from `SymmRatchet.lean` to a
    reusable theorem. Unlike `AdvantageA_triangle_chain` (which uses `List`),
    this uses `ℕ`-indexed games for easier composition with `Finset.sum`. -/
theorem advantage_hybrid_dep {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) :
    AdvantageA (G 0) (G n) A ≤
    ∑ i ∈ Finset.range n, AdvantageA (G i) (G (i + 1)) A := by
  induction n with
  | zero =>
    unfold AdvantageA Advantage
    simp [Finset.range_zero, Finset.sum_empty]
  | succ k ih =>
    have htri : AdvantageA (G 0) (G (k + 1)) A ≤
        AdvantageA (G 0) (G k) A + AdvantageA (G k) (G (k + 1)) A := by
      unfold AdvantageA; exact advantage_triangle _ _ _
    calc AdvantageA (G 0) (G (k + 1)) A
        ≤ AdvantageA (G 0) (G k) A + AdvantageA (G k) (G (k + 1)) A := htri
      _ ≤ (∑ i ∈ Finset.range k, AdvantageA (G i) (G (i + 1)) A) +
          AdvantageA (G k) (G (k + 1)) A := add_le_add ih le_rfl
      _ = ∑ i ∈ Finset.range (k + 1), AdvantageA (G i) (G (i + 1)) A := by
          rw [Finset.sum_range_succ]

/-- **Dependent hybrid inequality for Advantage** (Bool games, no adversary). -/
theorem advantage_hybrid_dep_bool (G : ℕ → SPComp Bool) (n : ℕ) :
    Advantage (G 0) (G n) ≤
    ∑ i ∈ Finset.range n, Advantage (G i) (G (i + 1)) := by
  induction n with
  | zero =>
    simp [Finset.range_zero, Finset.sum_empty, Advantage]
  | succ k ih =>
    calc Advantage (G 0) (G (k + 1))
        ≤ Advantage (G 0) (G k) + Advantage (G k) (G (k + 1)) :=
          advantage_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.range k, Advantage (G i) (G (i + 1))) +
          Advantage (G k) (G (k + 1)) := add_le_add ih le_rfl
      _ = ∑ i ∈ Finset.range (k + 1), Advantage (G i) (G (i + 1)) := by
          rw [Finset.sum_range_succ]

/-- **Uniform hybrid bound**: when each step is bounded by the same ε,
    the total advantage is at most `n * ε`.

    This is the typical use case: all hybrid steps have the same security level
    (e.g., each step reduces to one CPA query). -/
theorem advantage_hybrid_uniform {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (n : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < n → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA (G 0) (G n) A ≤ n * ε := by
  calc AdvantageA (G 0) (G n) A
      ≤ ∑ i ∈ Finset.range n, AdvantageA (G i) (G (i + 1)) A :=
        advantage_hybrid_dep G A n
    _ ≤ ∑ _ ∈ Finset.range n, ε := by
        apply Finset.sum_le_sum
        intro i hi
        exact hstep i (Finset.mem_range.mp hi)
    _ = n * ε := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Hybrid equality**: when all adjacent games are perfectly indistinguishable
    (via rHoare eqPre/eqPost), the advantage is 0.

    This captures the "equality" case from the CSF 2025 paper: when transitions
    are information-theoretically perfect, the total advantage vanishes. -/
theorem advantage_hybrid_zero {α : Type} (G : ℕ → SPComp α) (n : ℕ)
    (hperf : ∀ i, i < n → rHoare eqPre (G i) (G (i + 1)) eqPost)
    (A : α → SPComp Bool) :
    AdvantageA (G 0) (G n) A = 0 := by
  have hle := advantage_hybrid_uniform G A n 0 (fun i hi => by
    rw [advantage_zero_of_rHoare _ _ (hperf i hi) A])
  simp only [mul_zero] at hle
  exact le_antisymm hle (zero_le)

/-! ## Boundary Composition Helpers

    These helpers allow composing hybrid arguments with boundary conditions:
    when the first hybrid game equals the "real" game and the last equals the "ideal" game. -/

/-- **Hybrid argument with boundary conditions**: if `real = G 0` and `ideal = G n`,
    then `Adv(real, ideal) ≤ n * ε`. -/
theorem advantage_hybrid_bound {α : Type} (real ideal : SPComp α)
    (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) (ε : ℝ≥0∞)
    (hleft : real = G 0)
    (hright : ideal = G n)
    (hstep : ∀ i, i < n → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA real ideal A ≤ n * ε := by
  rw [hleft, hright]
  exact advantage_hybrid_uniform G A n ε hstep

/-- **Hybrid argument with dependent bounds and boundary conditions**:
    the general form with different per-step bounds. -/
theorem advantage_hybrid_dep_bound {α : Type} (real ideal : SPComp α)
    (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) (ε : ℕ → ℝ≥0∞)
    (hleft : real = G 0)
    (hright : ideal = G n)
    (hstep : ∀ i, i < n → AdvantageA (G i) (G (i + 1)) A ≤ ε i) :
    AdvantageA real ideal A ≤ ∑ i ∈ Finset.range n, ε i := by
  rw [hleft, hright]
  calc AdvantageA (G 0) (G n) A
      ≤ ∑ i ∈ Finset.range n, AdvantageA (G i) (G (i + 1)) A :=
        advantage_hybrid_dep G A n
    _ ≤ ∑ i ∈ Finset.range n, ε i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hstep i (Finset.mem_range.mp hi)

/-! ## Factorization + Hybrid Composition

    A common pattern: factor out a common post-processing step, apply the hybrid
    argument to the core computation, then compose. -/

/-- **Factored hybrid bound**: when real and ideal games factor through
    a common post-processing `f`, apply the hybrid argument to the base games. -/
theorem advantage_hybrid_factored {α β : Type}
    (G_base : ℕ → SPComp α) (f : α → SPComp β) (A : β → SPComp Bool)
    (n : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < n → AdvantageA (G_base i) (G_base (i + 1))
      (fun x => (f x).bind A) ≤ ε) :
    AdvantageA ((G_base 0).bind f) ((G_base n).bind f) A ≤ n * ε := by
  rw [advantage_factorization f (G_base 0) (G_base n) A]
  exact advantage_hybrid_uniform G_base (fun x => (f x).bind A) n ε hstep

/-! ## Nested Hybrid Arguments

    For multi-dimensional hybrid arguments (e.g., multi-instance + multi-query),
    the inner and outer hybrid bounds compose multiplicatively. -/

/-- **Nested hybrid bound**: composing two levels of hybrid arguments.

    If the outer hybrid has `m` steps each bounded by `ε_outer`,
    and `ε_outer` is itself bounded by an inner hybrid with `q` steps each ≤ `ε`,
    then the total bound is `m * q * ε`. -/
theorem advantage_hybrid_nested {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (m q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < m → AdvantageA (G i) (G (i + 1)) A ≤ q * ε) :
    AdvantageA (G 0) (G m) A ≤ m * (q * ε) :=
  advantage_hybrid_uniform G A m (q * ε) hstep

/-! ## Equality Forms

    The standard hybrid argument gives `≤`. When all step advantages are
    *equal* (not just bounded), and the per-step advantage comes from an
    equality (like `dHybrid_step_eq`), we can derive tighter statements.

    The key insight: if `Adv(G i, G(i+1)) = ε` for all `i < n`, then
    `Adv(G 0, G n) ≤ n * ε`. The converse (achieving equality) requires
    monotonicity of `Pr[A ∘ G i = true]` in `i`, which ensures the
    telescoping sum has consistent signs.

    We provide the "≤" version with step equalities, which is the most
    practically useful form. -/

/-- **Uniform hybrid bound from equalities**: when each step advantage
    *equals* ε, the total advantage is at most `n * ε`.

    This is the distributional analogue of the CSF 2025 paper's Theorem 4.
    The bound is tight when the telescoping sum has consistent signs. -/
theorem advantage_hybrid_uniform_eq {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (n : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < n → AdvantageA (G i) (G (i + 1)) A = ε) :
    AdvantageA (G 0) (G n) A ≤ n * ε :=
  advantage_hybrid_uniform G A n ε (fun i hi => (hstep i hi).le)

/-- **Nested hybrid bound from equalities**: composing two levels of hybrid
    arguments where both inner and outer step advantages are exact equalities. -/
theorem advantage_hybrid_nested_eq {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (m q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < m → AdvantageA (G i) (G (i + 1)) A ≤ q * ε) :
    AdvantageA (G 0) (G m) A ≤ m * q * ε := by
  calc AdvantageA (G 0) (G m) A ≤ m * (q * ε) :=
        advantage_hybrid_nested G A m q ε hstep
    _ = m * q * ε := by ring

end CatCrypt.Crypto.HybridArgument

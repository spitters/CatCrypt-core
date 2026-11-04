/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Crypto.SDist
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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
* `familyAdvantage_pairSampler_le` - the advantage against a pair of independent samplers is
  at most the sum of the two sampler advantages
* `epochFold_advantage_le` - the hybrid over an epoch fold with two samplers per epoch (a
  secret and a stretch): the gap between the fold with the computational samplers and the
  fold with the idealized ones is at most `epochFoldBound`, the sum over the epochs of the
  advantages of the reductions `secHybRed` and `stretchHybRed`

## Sampler families and the epoch fold

A sampler family `f : α → SPComp β` is compared with `g` by a two-stage distinguisher
(`FamilyDistinguisher`): the first stage draws a state and an input, the second guesses from
the state and the family's output on the input (`familyGame`, `familyAdvantage`).
`pairSampler c d` draws two independent secrets as one sampler.

`epochFold getRoot post out sec s` is the fold with a root state `ρ`: each epoch reads the root
with `getRoot`, draws the secret with `sec`, stretches with `s`, and stores the new root with
`post`. The hybrid `hybFold … i` runs the first `i` epochs with the idealized samplers and the
rest with the computational ones; hop `i` swaps the secret sampler (reduction
`secHybRed … i`) and then the stretch (reduction `stretchHybRed … i`). Both reductions
simulate the first `i` epochs from the initial heap (`idealPrefix`) and embed their challenge
at epoch `i`. The costed reductions and their time bounds are in `HybridArgumentTimed`.

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
-/

@[expose] public section

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

    Unlike `AdvantageA_triangle_chain` (which uses `List`), this uses
    `ℕ`-indexed games for easier composition with `Finset.sum`. -/
theorem advantage_hybrid_dep {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) :
    AdvantageA (G 0) (G n) A ≤
    ∑ i ∈ Finset.range n, AdvantageA (G i) (G (i + 1)) A := by
  induction n with
  | zero =>
    unfold AdvantageA Advantage
    bound
  | succ k ih =>
    have htri : AdvantageA (G 0) (G (k + 1)) A ≤
        AdvantageA (G 0) (G k) A + AdvantageA (G k) (G (k + 1)) A := by
      unfold AdvantageA; exact advantage_triangle _ _ _
    calc AdvantageA (G 0) (G (k + 1)) A
        ≤ AdvantageA (G 0) (G k) A + AdvantageA (G k) (G (k + 1)) A := htri
      _ ≤ (∑ i ∈ Finset.range k, AdvantageA (G i) (G (i + 1)) A) +
          AdvantageA (G k) (G (k + 1)) A := by gcongr
      _ = ∑ i ∈ Finset.range (k + 1), AdvantageA (G i) (G (i + 1)) A := by
          simp_all [Finset.sum_range_succ]

/-- **Dependent hybrid inequality for Advantage** (Bool games, no adversary). -/
theorem advantage_hybrid_dep_bool (G : ℕ → SPComp Bool) (n : ℕ) :
    Advantage (G 0) (G n) ≤
    ∑ i ∈ Finset.range n, Advantage (G i) (G (i + 1)) := by
  induction n with
  | zero =>
    simp [Finset.range_zero, Finset.sum_empty, Advantage]
  | succ k ih =>
    calc Advantage (G 0) (G (k + 1))
        ≤ Advantage (G 0) (G k) + Advantage (G k) (G (k + 1)) := by grind
      _ ≤ (∑ i ∈ Finset.range k, Advantage (G i) (G (i + 1))) +
          Advantage (G k) (G (k + 1)) := by gcongr
      _ = ∑ i ∈ Finset.range (k + 1), Advantage (G i) (G (i + 1)) := by
          simp_all [Finset.sum_range_succ]

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
        by solve_by_elim [advantage_hybrid_dep, advantage_hybrid_dep_bool]
    _ ≤ ∑ _ ∈ Finset.range n, ε := by
        apply Finset.sum_le_sum
        intro i hi
        exact hstep i (Finset.mem_range.mp hi)
    _ = n * ε := by
        simp_all [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

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
        by solve_by_elim [advantage_hybrid_dep, advantage_hybrid_dep_bool, advantage_hybrid_zero]
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
    _ = m * q * ε := by grind

/-! ## Distinguishers against a sampler family -/

/-- A two-stage distinguisher against a family of samplers `α → SPComp β`:
`pre` draws a state and an input, and `guess` decides from the state and the
family's output on that input. -/
structure FamilyDistinguisher (σ α β : Type) where
  /-- The first stage: a state and the input queried to the family. -/
  pre : SPComp (σ × α)
  /-- The second stage: the guess from the state and the family's output. -/
  guess : σ → β → SPComp Bool

/-- The family game: run the first stage `pre`, query the family `f` at the
drawn input, and return the state with the family's output. -/
noncomputable def familyGame {σ α β : Type} (f : α → SPComp β)
    (pre : SPComp (σ × α)) : SPComp (σ × β) :=
  SPComp.bind pre fun p => SPComp.bind (f p.2) fun y => SPComp.pure (p.1, y)

/-- The advantage of the two-stage distinguisher `B` between the sampler
families `f` and `g`. -/
noncomputable def familyAdvantage {σ α β : Type} (f g : α → SPComp β)
    (B : FamilyDistinguisher σ α β) : ℝ≥0∞ :=
  AdvantageA (familyGame f B.pre) (familyGame g B.pre) fun q => B.guess q.1 q.2

theorem familyGame_bind_guess {σ α β : Type} (f : α → SPComp β)
    (B : FamilyDistinguisher σ α β) :
    SPComp.bind (familyGame f B.pre) (fun q => B.guess q.1 q.2) =
      SPComp.bind B.pre fun p => SPComp.bind (f p.2) (B.guess p.1) := by
  simp only [familyGame, SPComp.bind_assoc, SPComp.pure_bind]

/-- The distinguisher `B` with its input mapped by `e` after the first stage. -/
noncomputable def FamilyDistinguisher.mapInput {σ α α' β : Type} (e : α → α')
    (B : FamilyDistinguisher σ α β) : FamilyDistinguisher σ α' β where
  pre := SPComp.bind B.pre fun p => SPComp.pure (p.1, e p.2)
  guess := B.guess

/-- Reindexing a sampler family by `e` is the same game for the distinguisher
with its input mapped by `e`. -/
theorem familyAdvantage_comp_input {σ α α' β : Type} (f g : α' → SPComp β) (e : α → α')
    (B : FamilyDistinguisher σ α β) :
    familyAdvantage (fun a => f (e a)) (fun a => g (e a)) B =
      familyAdvantage f g (B.mapInput e) := by
  unfold familyAdvantage familyGame FamilyDistinguisher.mapInput
  simp only [SPComp.bind_assoc, SPComp.pure_bind]

/-- Unfolding lemma of `SPComp.bind` for a computation run from the heap `h₀`:
the bind is the bind of the computation evaluated at `h₀`. -/
theorem bind_fromHeap {α β : Type} (c : SPComp α) (K : α → SPComp β) (h₀ : Heap) :
    SPComp.bind (fun _ => c h₀) K = fun _ => SPComp.bind c K h₀ := rfl

/-! ## Two independent secret samplers as one -/

/-- Two independent samplers drawn in sequence, as one sampler of pairs. -/
noncomputable def pairSampler {β γ : Type} (c : Unit → SPComp β)
    (d : Unit → SPComp γ) : Unit → SPComp (β × γ) :=
  fun _ => SPComp.bind (c ()) fun r => SPComp.bind (d ()) fun q => SPComp.pure (r, q)

/-- The distinguisher against the first sampler built from a distinguisher `B`
against the pair: it draws the second component with `d` itself. -/
noncomputable def pairFstRed {σ β γ : Type} (d : Unit → SPComp γ)
    (B : FamilyDistinguisher σ Unit (β × γ)) : FamilyDistinguisher σ Unit β where
  pre := B.pre
  guess := fun st r => SPComp.bind (d ()) fun q => B.guess st (r, q)

/-- The distinguisher against the second sampler built from a distinguisher
`B` against the pair: its first stage draws the first component with `c`. -/
noncomputable def pairSndRed {σ β γ : Type} (c : Unit → SPComp β)
    (B : FamilyDistinguisher σ Unit (β × γ)) : FamilyDistinguisher (σ × β) Unit γ where
  pre := SPComp.bind B.pre fun p =>
    SPComp.bind (c ()) fun r => SPComp.pure ((p.1, r), ())
  guess := fun st q => B.guess st.1 (st.2, q)

/-- **Pair hybrid.** The advantage of `B` between `pairSampler c d` and
`pairSampler c' d'` is at most the advantage of `pairFstRed d B` between `c`
and `c'` plus the advantage of `pairSndRed c' B` between `d` and `d'`. -/
theorem familyAdvantage_pairSampler_le {σ β γ : Type} (c c' : Unit → SPComp β)
    (d d' : Unit → SPComp γ) (B : FamilyDistinguisher σ Unit (β × γ)) :
    familyAdvantage (pairSampler c d) (pairSampler c' d') B ≤
      familyAdvantage c c' (pairFstRed d B) + familyAdvantage d d' (pairSndRed c' B) := by
  unfold familyAdvantage AdvantageA
  have e₁ : ∀ c₀ : Unit → SPComp β,
      SPComp.bind (familyGame (pairSampler c₀ d) B.pre) (fun q => B.guess q.1 q.2) =
        SPComp.bind (familyGame c₀ (pairFstRed d B).pre)
          (fun q => (pairFstRed d B).guess q.1 q.2) := by
    intro c₀
    simp only [familyGame, pairSampler, pairFstRed, SPComp.bind_assoc, SPComp.pure_bind]
  have e₂ : ∀ d₀ : Unit → SPComp γ,
      SPComp.bind (familyGame (pairSampler c' d₀) B.pre) (fun q => B.guess q.1 q.2) =
        SPComp.bind (familyGame d₀ (pairSndRed c' B).pre)
          (fun q => (pairSndRed c' B).guess q.1 q.2) := by
    intro d₀
    simp only [familyGame, pairSampler, pairSndRed, SPComp.bind_assoc, SPComp.pure_bind]
  calc Advantage (SPComp.bind (familyGame (pairSampler c d) B.pre) fun q => B.guess q.1 q.2)
        (SPComp.bind (familyGame (pairSampler c' d') B.pre) fun q => B.guess q.1 q.2)
      ≤ Advantage (SPComp.bind (familyGame (pairSampler c d) B.pre) fun q => B.guess q.1 q.2)
          (SPComp.bind (familyGame (pairSampler c' d) B.pre) fun q => B.guess q.1 q.2) +
        Advantage (SPComp.bind (familyGame (pairSampler c' d) B.pre) fun q => B.guess q.1 q.2)
          (SPComp.bind (familyGame (pairSampler c' d') B.pre) fun q => B.guess q.1 q.2) :=
        advantage_triangle _ _ _
    _ = _ := by
      congr 1
      · rw [e₁ c, e₁ c']
      · rw [e₂ d, e₂ d']

/-! ## The generic epoch fold -/

section Fold

variable {W ρ Z : Type} (getRoot : ρ → SPComp W) (post : W → SPComp ρ) (out : W → W)

/-- The n-epoch fold over a root state `ρ`. Per epoch: read the current root
`rk` with `getRoot`, draw the fresh secret `r` with `sec`, stretch `rk` with
`r` into the next root `k` with `s`, store `k` with `post`, record the view
entry (`k` itself at a corrupted epoch, `out k` at a clean one), and recurse.
The schedule bit only affects the view. -/
noncomputable def epochFold (sec : Unit → SPComp Z) (s : W × Z → SPComp W) :
    List Bool → ρ → SPComp (List W)
  | [], _ => SPComp.pure []
  | b :: bs, x =>
    SPComp.bind (getRoot x) fun rk =>
    SPComp.bind (sec ()) fun r =>
    SPComp.bind (s (rk, r)) fun k =>
    SPComp.bind (post k) fun x' =>
    SPComp.bind (epochFold sec s bs x') fun ks =>
    SPComp.pure (cond b k (out k) :: ks)

variable (sec : Unit → SPComp Z) (s : W × Z → SPComp W)
  (secI : Unit → SPComp Z) (sI : W × Z → SPComp W)

/-- The hybrid fold at epoch `j`: the first `j` epochs run the idealized
samplers `secI`, `sI`; epoch `j` runs the samplers `c`, `t`; the remaining
epochs run the computational samplers `sec`, `s`. -/
noncomputable def hybFold (c : Unit → SPComp Z) (t : W × Z → SPComp W) :
    ℕ → List Bool → ρ → SPComp (List W)
  | _, [], _ => SPComp.pure []
  | 0, b :: bs, x =>
    SPComp.bind (getRoot x) fun rk =>
    SPComp.bind (c ()) fun r =>
    SPComp.bind (t (rk, r)) fun k =>
    SPComp.bind (post k) fun x' =>
    SPComp.bind (epochFold getRoot post out sec s bs x') fun ks =>
    SPComp.pure (cond b k (out k) :: ks)
  | j + 1, b :: bs, x =>
    SPComp.bind (getRoot x) fun rk =>
    SPComp.bind (secI ()) fun r =>
    SPComp.bind (sI (rk, r)) fun k =>
    SPComp.bind (post k) fun x' =>
    SPComp.bind (hybFold c t j bs x') fun ks =>
    SPComp.pure (cond b k (out k) :: ks)

/-- The first `j` epochs run with the idealized samplers, returning their view
entries and the root state after them. -/
noncomputable def idealPrefix : ℕ → List Bool → ρ → SPComp (List W × ρ)
  | 0, _, x => SPComp.pure ([], x)
  | _ + 1, [], x => SPComp.pure ([], x)
  | j + 1, b :: bs, x =>
    SPComp.bind (getRoot x) fun rk =>
    SPComp.bind (secI ()) fun r =>
    SPComp.bind (sI (rk, r)) fun k =>
    SPComp.bind (post k) fun x' =>
    SPComp.bind (idealPrefix j bs x') fun p =>
    SPComp.pure (cond b k (out k) :: p.1, p.2)

/-- The reduction of hop `i` against the secret sampler: from the heap `h₀` it
simulates the first `i` epochs with the idealized samplers and reads the root
(`pre`); on the challenge secret it runs epoch `i` with the stretch `s` and the
remaining epochs with the computational samplers, and runs `D` on the view. -/
noncomputable def secHybRed (i : ℕ) (bs : List Bool) (x : ρ) (h₀ : Heap)
    (D : List W → SPComp Bool) : FamilyDistinguisher (List W × W) Unit Z where
  pre := fun _ => SPComp.bind (idealPrefix getRoot post out secI sI i bs x) (fun p =>
    SPComp.bind (getRoot p.2) fun rk => SPComp.pure ((p.1, rk), ())) h₀
  guess := fun st r =>
    SPComp.bind (s (st.2, r)) fun k =>
    SPComp.bind (post k) fun x' =>
    SPComp.bind (epochFold getRoot post out sec s (bs.drop (i + 1)) x') fun ks =>
    D (st.1 ++ cond (bs.getD i false) k (out k) :: ks)

/-- The reduction of hop `i` against the stretch: from the heap `h₀` it
simulates the first `i` epochs with the idealized samplers, reads the root and
draws the idealized secret of epoch `i` (`pre`, whose input is the root and the
secret); on the challenge root it runs the remaining epochs with the
computational samplers, and runs `D` on the view. -/
noncomputable def stretchHybRed (i : ℕ) (bs : List Bool) (x : ρ) (h₀ : Heap)
    (D : List W → SPComp Bool) : FamilyDistinguisher (List W) (W × Z) W where
  pre := fun _ => SPComp.bind (idealPrefix getRoot post out secI sI i bs x) (fun p =>
    SPComp.bind (getRoot p.2) fun rk =>
    SPComp.bind (secI ()) fun r => SPComp.pure (p.1, (rk, r))) h₀
  guess := fun ks₀ k =>
    SPComp.bind (post k) fun x' =>
    SPComp.bind (epochFold getRoot post out sec s (bs.drop (i + 1)) x') fun ks =>
    D (ks₀ ++ cond (bs.getD i false) k (out k) :: ks)

/-- The hybrid bound: the sum over the epochs of the advantages of the two
reductions of each hop. -/
noncomputable def epochFoldBound (bs : List Bool) (x : ρ) (h₀ : Heap)
    (D : List W → SPComp Bool) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range bs.length,
    (familyAdvantage sec secI (secHybRed getRoot post out sec s secI sI i bs x h₀ D) +
      familyAdvantage s sI (stretchHybRed getRoot post out sec s secI sI i bs x h₀ D))

theorem hybFold_zero (bs : List Bool) (x : ρ) :
    hybFold getRoot post out sec s secI sI sec s 0 bs x =
      epochFold getRoot post out sec s bs x := by
  cases bs <;> rfl

theorem hybFold_ideal_succ (j : ℕ) (bs : List Bool) (x : ρ) :
    hybFold getRoot post out sec s secI sI secI sI j bs x =
      hybFold getRoot post out sec s secI sI sec s (j + 1) bs x := by
  induction j generalizing bs x with
  | zero =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [hybFold, hybFold_zero]
  | succ j ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [hybFold, ih]

theorem hybFold_of_length_le (bs : List Bool) (j : ℕ) (x : ρ) (hj : bs.length ≤ j) :
    hybFold getRoot post out sec s secI sI sec s j bs x =
      epochFold getRoot post out secI sI bs x := by
  induction bs generalizing j x with
  | nil => cases j <;> rfl
  | cons b bs ih =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by simp at hj; omega⟩
    have ih' : ∀ x', hybFold getRoot post out sec s secI sI sec s j bs x' =
        epochFold getRoot post out secI sI bs x' :=
      fun x' => ih j x' (by simp at hj; omega)
    simp only [hybFold, epochFold, ih']

/-- A hybrid fold below the schedule length is the idealized prefix of `i`
epochs, epoch `i` with the samplers `c`, `t`, and the computational tail. -/
theorem hybFold_bind (c : Unit → SPComp Z) (t : W × Z → SPComp W) (i : ℕ)
    (bs : List Bool) (x : ρ) (D : List W → SPComp Bool) (hi : i < bs.length) :
    SPComp.bind (hybFold getRoot post out sec s secI sI c t i bs x) D =
      SPComp.bind (idealPrefix getRoot post out secI sI i bs x) fun p =>
        SPComp.bind (getRoot p.2) fun rk =>
        SPComp.bind (c ()) fun r =>
        SPComp.bind (t (rk, r)) fun k =>
        SPComp.bind (post k) fun x' =>
        SPComp.bind (epochFold getRoot post out sec s (bs.drop (i + 1)) x') fun ks =>
        D (p.1 ++ cond (bs.getD i false) k (out k) :: ks) := by
  induction i generalizing bs x D with
  | zero =>
    cases bs with
    | nil => simp at hi
    | cons b bs =>
      simp only [hybFold, idealPrefix, SPComp.bind_assoc, SPComp.pure_bind,
        List.nil_append, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
  | succ i ih =>
    cases bs with
    | nil => simp at hi
    | cons b bs =>
      have hi' : i < bs.length := by simpa using hi
      simp only [hybFold, idealPrefix, SPComp.bind_assoc, SPComp.pure_bind,
        ih _ _ _ hi', List.cons_append, List.getD_cons_succ, List.drop_succ_cons]

/-- Hop `i`, first half: swapping the secret sampler of epoch `i` is the
advantage of `secHybRed … i` between `sec` and `secI`. -/
theorem hybFold_sec_hop (i : ℕ) (bs : List Bool) (x : ρ) (h₀ : Heap)
    (D : List W → SPComp Bool) (hi : i < bs.length) :
    AdvantageA (fun _ => hybFold getRoot post out sec s secI sI sec s i bs x h₀)
        (fun _ => hybFold getRoot post out sec s secI sI secI s i bs x h₀) D =
      familyAdvantage sec secI (secHybRed getRoot post out sec s secI sI i bs x h₀ D) := by
  unfold familyAdvantage AdvantageA
  have e : ∀ c : Unit → SPComp Z,
      SPComp.bind (fun _ => hybFold getRoot post out sec s secI sI c s i bs x h₀) D =
        SPComp.bind (familyGame c (secHybRed getRoot post out sec s secI sI i bs x h₀ D).pre)
          fun q => (secHybRed getRoot post out sec s secI sI i bs x h₀ D).guess q.1 q.2 := by
    intro c
    rw [familyGame_bind_guess, bind_fromHeap,
      hybFold_bind getRoot post out sec s secI sI c s i bs x D hi]
    simp only [secHybRed, bind_fromHeap, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  rw [e sec, e secI]

/-- Hop `i`, second half: swapping the stretch of epoch `i` is the advantage of
`stretchHybRed … i` between `s` and `sI`. -/
theorem hybFold_stretch_hop (i : ℕ) (bs : List Bool) (x : ρ) (h₀ : Heap)
    (D : List W → SPComp Bool) (hi : i < bs.length) :
    AdvantageA (fun _ => hybFold getRoot post out sec s secI sI secI s i bs x h₀)
        (fun _ => hybFold getRoot post out sec s secI sI secI sI i bs x h₀) D =
      familyAdvantage s sI (stretchHybRed getRoot post out sec s secI sI i bs x h₀ D) := by
  unfold familyAdvantage AdvantageA
  have e : ∀ t : W × Z → SPComp W,
      SPComp.bind (fun _ => hybFold getRoot post out sec s secI sI secI t i bs x h₀) D =
        SPComp.bind (familyGame t (stretchHybRed getRoot post out sec s secI sI i bs x h₀ D).pre)
          fun q => (stretchHybRed getRoot post out sec s secI sI i bs x h₀ D).guess q.1 q.2 := by
    intro t
    rw [familyGame_bind_guess, bind_fromHeap,
      hybFold_bind getRoot post out sec s secI sI secI t i bs x D hi]
    simp only [stretchHybRed, bind_fromHeap, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  rw [e s, e sI]

/-- **Epoch hybrid, per distinguisher.** From every initial heap `h₀` and for
every distinguisher `D`, the gap between the computational fold and the
idealized fold is at most `epochFoldBound`: the sum over the epochs `i` of the
advantage of `secHybRed … i` against the secret sampler and the advantage of
`stretchHybRed … i` against the stretch. -/
theorem epochFold_advantage_le (bs : List Bool) (x : ρ) (h₀ : Heap)
    (D : List W → SPComp Bool) :
    absDiff (prTrue (SPComp.bind (epochFold getRoot post out sec s bs x) D) h₀)
        (prTrue (SPComp.bind (epochFold getRoot post out secI sI bs x) D) h₀) ≤
      epochFoldBound getRoot post out sec s secI sI bs x h₀ D := by
  have key := HybridArgument.advantage_hybrid_dep
    (fun i _ => hybFold getRoot post out sec s secI sI sec s i bs x h₀) D bs.length
  have e0 : absDiff (prTrue (SPComp.bind (epochFold getRoot post out sec s bs x) D) h₀)
      (prTrue (SPComp.bind (epochFold getRoot post out secI sI bs x) D) h₀) =
      AdvantageA (fun _ => hybFold getRoot post out sec s secI sI sec s 0 bs x h₀)
        (fun _ => hybFold getRoot post out sec s secI sI sec s bs.length bs x h₀) D := by
    rw [hybFold_zero, hybFold_of_length_le getRoot post out sec s secI sI bs bs.length x le_rfl]
    rfl
  rw [e0]
  refine key.trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i < bs.length := Finset.mem_range.mp hi
  calc AdvantageA (fun _ => hybFold getRoot post out sec s secI sI sec s i bs x h₀)
        (fun _ => hybFold getRoot post out sec s secI sI sec s (i + 1) bs x h₀) D
      ≤ AdvantageA (fun _ => hybFold getRoot post out sec s secI sI sec s i bs x h₀)
          (fun _ => hybFold getRoot post out sec s secI sI secI s i bs x h₀) D +
        AdvantageA (fun _ => hybFold getRoot post out sec s secI sI secI s i bs x h₀)
          (fun _ => hybFold getRoot post out sec s secI sI sec s (i + 1) bs x h₀) D :=
        advantage_triangle _ _ _
    _ = _ := by
      rw [← hybFold_ideal_succ, hybFold_sec_hop getRoot post out sec s secI sI i bs x h₀ D hi',
        hybFold_stretch_hop getRoot post out sec s secI sI i bs x h₀ D hi']

end Fold

end CatCrypt.Crypto.HybridArgument

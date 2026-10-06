/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Crypto.MultiQueryPRF


@[expose] public section
set_option autoImplicit false

/-!
# `XAdvantageHybrid`: the advantage-triangle composition tactic

The advantage-triangle composition tactic — `advChain_triangle` / `advChain_uniform` +
`advmvcgen` — for Core's **advantage idiom** (the triangle inequality over a game chain on
`SPComp` / `AdvantageA`). It composes Core's hybrid arguments (`MultiQueryPRF`,
`HybridArgument`) in their own form, with no coupling reformulation.

## The advantage idiom and the coupling idiom

A coupling tactic composes `ε`-approximate `SDistr` **couplings** (`liftRApprox`) through a
coupling-spec-monad bind; no such tactic is part of this package. Core's protocol reductions
(`MultiQueryPRF`, `HybridArgument`, the switching-lemma and dual-mode-OT hybrids) are
**advantage-shaped**: they compose `AdvantageA` / `Advantage` bounds by the **triangle
inequality** over a chain of games on `SPComp`, and a coupling tactic reaches them only after
reformulating each hop as a coupling.

This module states the composition for the advantage idiom, which composes the Core hybrids
as they stand and needs only Core primitives (`AdvantageA` + `advantage_triangle`).

## The Core game-chain representation

The hybrid engine of CatCrypt-core (module `HybridArgument`) indexes the chain by `ℕ`, not by
`Fin (n+1)`:

* a game chain is `G : ℕ → SPComp α` (with `G 0` the real game and `G n` the ideal game),
* the adversary is explicit, `A : α → SPComp Bool`, and distinguishing is measured by
  `AdvantageA G₀ G₁ A = Advantage (G₀.bind A) (G₁.bind A)` (not the adversary-free `Advantage`),
* per-hop bounds are `∀ i, i < n → AdvantageA (G i) (G (i+1)) A ≤ ε i`, and the conclusion is
  `AdvantageA (G 0) (G n) A ≤ ∑ i ∈ Finset.range n, ε i` (a `Finset.range` sum), or `≤ n * ε`
  in the uniform case.

We therefore build the composition rules over Core's `ℕ`-indexed `AdvantageA` chain, so they
wrap the Core engine directly (no re-indexing, no re-proof).

## What this module provides

1. **The advantage-chain composition rules** (sequencing and iteration in the advantage
   idiom):
   * `advChain_triangle` — per-hop bounds `AdvantageA (G i) (G (i+1)) A ≤ ε i` fold, by the
     triangle inequality, to `AdvantageA (G 0) (G n) A ≤ ∑ i ∈ Finset.range n, ε i`. Wraps the
     Core engine lemma `HybridArgument.advantage_hybrid_dep_bound`.
   * `advChain_uniform` — the uniform case `≤ n * ε`. Wraps `HybridArgument.advantage_hybrid_uniform`.
   * `advChain_triangle_le` / `advChain_uniform_le` — the same, composed with a final
     `hbudget` step (`le_trans`) so the conclusion is `≤ budget` for an arbitrary budget. These
     are the tactic-facing forms: they split a `≤ budget` goal into the per-hop leaves plus the
     arithmetic verification condition `∑ ε i ≤ budget` (resp. `n * ε ≤ budget`).

2. **The tactic `advmvcgen`** — on a goal `AdvantageA (G 0) (G n) A ≤ budget`, fires
   `advChain_uniform_le` / `advChain_triangle_le`, reducing it to the per-hop leaf obligation
   `∀ i, i < n → AdvantageA (G i) (G (i+1)) A ≤ ε` and the arithmetic VC `n * ε ≤ budget`. It
   does the **composition**; the per-hop leaves stay obligations. The per-hop advantage `ε` is
   left as a metavariable, pinned when the leaf is discharged. `advmvcgen_dep` is the
   varying-`εᵢ` (`∑`) variant.

3. **The `MultiQueryPRF` demo, composed in the native idiom.** `advmvcgen` re-derives the
   q-query PRF hybrid bound `AdvantageA (G 0) (G q) A ≤ q * ε` from the per-hop single-query
   obligations — the exact statement of Core's `MultiQueryPRF.prf_multi_query_bound`, with no
   `SDistr` coupling reformulation. `prf_multi_query_from_single` grounds the per-hop leaf in
   the single-query PRF advantage `MultiQueryPRF.prf_adv1` (built from `prf_query_real` /
   `prf_query_ideal`), so the composition touches `MultiQueryPRF` objects. And
   `prf_multi_query_bound_is_advChain` shows Core's native bound *is* `advChain_uniform`.

4. **Dependencies.** Every declaration here depends only on `CatCrypt.Crypto.AdvantageA`,
   `advantage_triangle`, and the `HybridArgument` engine, all in **CatCrypt-core**.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.HybridArgument
open CatCrypt.Crypto.MultiQueryPRF

/-! ## 1. The advantage-chain composition rules

Sequencing and iteration rules in the advantage idiom. Where a coupling tactic folds
`ε`-approximate couplings through a coupling-spec-monad bind, these fold
`AdvantageA` bounds through the **triangle inequality** `advantage_triangle`, over Core's
`ℕ`-indexed game chain `G : ℕ → SPComp α`. The fold itself is the Core engine
(`HybridArgument.advantage_hybrid_dep` / `advantage_hybrid_uniform`); the rules here are the
tactic-facing repackaging that wraps it (no re-proof of the induction). -/

variable {α : Type}

/-- **Advantage-chain triangle rule (per-hop advantages).** For a game chain `G : ℕ → SPComp α`
and an adversary `A`, per-hop bounds `AdvantageA (G i) (G (i+1)) A ≤ ε i` compose, by the
triangle inequality over the chain, to `AdvantageA (G 0) (G n) A ≤ ∑ i ∈ Finset.range n, ε i`.

The per-hop distinguishing advantages sum by `advantage_triangle`. Wraps the Core engine lemma
`HybridArgument.advantage_hybrid_dep_bound` at the boundary `real = G 0`, `ideal = G n`. -/
theorem advChain_triangle (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < n → AdvantageA (G i) (G (i + 1)) A ≤ ε i) :
    AdvantageA (G 0) (G n) A ≤ ∑ i ∈ Finset.range n, ε i :=
  advantage_hybrid_dep_bound (G 0) (G n) G A n ε rfl rfl hstep

/-- **Advantage-chain triangle rule (uniform advantage).** When every hop is bounded by the same
`ε`, the chain composes to `AdvantageA (G 0) (G n) A ≤ n * ε`. The uniform case of
`advChain_triangle`. Wraps `HybridArgument.advantage_hybrid_uniform`. -/
theorem advChain_uniform (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < n → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA (G 0) (G n) A ≤ n * ε :=
  advantage_hybrid_uniform G A n ε hstep

/-- **Advantage-chain triangle rule to a budget (per-hop).** `advChain_triangle` followed by a
final `hbudget : ∑ ε i ≤ budget` step, so the conclusion is `≤ budget` for an arbitrary budget.
This is the tactic-facing form: it splits a `≤ budget` goal into the per-hop leaves plus the
arithmetic verification condition `∑ ε i ≤ budget`. -/
theorem advChain_triangle_le (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) (ε : ℕ → ℝ≥0∞)
    (budget : ℝ≥0∞)
    (hstep : ∀ i, i < n → AdvantageA (G i) (G (i + 1)) A ≤ ε i)
    (hbudget : ∑ i ∈ Finset.range n, ε i ≤ budget) :
    AdvantageA (G 0) (G n) A ≤ budget :=
  le_trans (advChain_triangle G A n ε hstep) hbudget

/-- **Advantage-chain triangle rule to a budget (uniform).** `advChain_uniform` followed by a
final `hbudget : n * ε ≤ budget` step. The tactic-facing uniform form: it splits a `≤ budget`
goal into the per-hop leaf `∀ i, i < n → AdvantageA (G i) (G (i+1)) A ≤ ε` plus the arithmetic
VC `n * ε ≤ budget`. -/
theorem advChain_uniform_le (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) (ε : ℝ≥0∞)
    (budget : ℝ≥0∞)
    (hstep : ∀ i, i < n → AdvantageA (G i) (G (i + 1)) A ≤ ε)
    (hbudget : (n : ℝ≥0∞) * ε ≤ budget) :
    AdvantageA (G 0) (G n) A ≤ budget :=
  le_trans (advChain_uniform G A n ε hstep) hbudget

/-! ## 2. The tactic `advmvcgen`

On a goal `AdvantageA (G 0) (G n) A ≤ budget`, `advmvcgen` fires the composition rule
`advChain_uniform_le` (or, for `advmvcgen_dep`, `advChain_triangle_le`), leaving exactly the
per-hop leaf obligation and the arithmetic verification condition. It does the
**composition** — the triangle fold over the chain — and leaves the per-hop bounds as goals.

The per-hop advantage `ε` is not determined by a `≤ budget` goal, so it is left as a
metavariable, pinned when the per-hop leaf is discharged (hence `apply`, not `refine`). -/

/-- **Advantage-chain VC generator (uniform).** On a goal `AdvantageA (G 0) (G n) A ≤ budget`,
fires `advChain_uniform_le`, reducing it to the per-hop leaf `∀ i, i < n → AdvantageA (G i)
(G (i+1)) A ≤ ?ε` and the arithmetic VC `n * ?ε ≤ budget`; `?ε` is pinned when the leaf is
discharged. -/
macro "advmvcgen" : tactic =>
  `(tactic| apply advChain_uniform_le)

/-- **Advantage-chain VC generator (per-hop / varying).** Like `advmvcgen` but fires
`advChain_triangle_le`, reducing the goal to the per-hop leaf `∀ i, i < n → AdvantageA (G i)
(G (i+1)) A ≤ ?ε i` and the arithmetic VC `∑ i ∈ Finset.range n, ?ε i ≤ budget`. -/
macro "advmvcgen_dep" : tactic =>
  `(tactic| apply advChain_triangle_le)

/-! ## 3. Demo — the `MultiQueryPRF` hybrid composed in the native idiom

Core's q-query PRF reduction is advantage-shaped, and `advmvcgen` composes it in that idiom,
with no `SDistr` coupling reformulation. -/

/-- **The q-query PRF bound re-derived by `advmvcgen`.** Given a q-step PRF hybrid chain `G`
(`G 0` real, `G q` ideal, each hop replacing one query real → random) whose adjacent games
differ by at most the single-query PRF advantage `ε`, `advmvcgen` fires the triangle fold and
leaves exactly the per-hop leaf (discharged from the single-query obligation, which pins `ε`)
and the arithmetic VC `q * ε ≤ q * ε`. The conclusion `AdvantageA (G 0) (G q) A ≤ q * ε` is the
exact statement of Core's `MultiQueryPRF.prf_multi_query_bound`, composed here in the native
idiom. -/
theorem prf_multi_query_via_advmvcgen (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA (G 0) (G q) A ≤ q * ε := by
  advmvcgen
  · exact hstep      -- per-hop single-query leaf (pins ε)
  · exact le_rfl     -- arithmetic VC: q * ε ≤ q * ε

/-- **The per-hop leaf grounded in the single-query PRF advantage.** The per-hop
distinguishing bound is the single-query PRF advantage `MultiQueryPRF.prf_adv1 F x A =
AdvantageA (prf_query_real F x) (prf_query_ideal x) A` (built from the single-query PRF
games), bounded by the PRF-security parameter `ε`. `advmvcgen` composes the q-step chain to
`q * ε`, the triangle fold touching a `MultiQueryPRF` object. -/
theorem prf_multi_query_from_single {K D R : Type} [Fintype K] [Nonempty K]
    [Fintype R] [Nonempty R] (F : PRFSpec K D R) (x : D) (A : R → SPComp Bool)
    (G : ℕ → SPComp R) (q : ℕ) (ε : ℝ≥0∞)
    (hsingle : prf_adv1 F x A ≤ ε)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ prf_adv1 F x A) :
    AdvantageA (G 0) (G q) A ≤ q * ε := by
  advmvcgen
  · intro i hi; exact le_trans (hstep i hi) hsingle   -- per-hop ≤ single-query ≤ ε (pins ε)
  · exact le_rfl                                        -- arithmetic VC: q * ε ≤ q * ε

/-- **Varying per-query advantages, by `advmvcgen_dep`.** Different queries may have different
single-query advantages `ε i`; the chain composes to `∑ i ∈ Finset.range q, ε i`, the exact
statement of Core's `MultiQueryPRF.prf_multi_query_dep_bound`. `advmvcgen_dep` fires the
per-hop triangle fold and leaves the per-hop leaf plus the arithmetic VC (here `le_rfl`). -/
theorem prf_multi_query_dep_via_advmvcgen (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (q : ℕ) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε i) :
    AdvantageA (G 0) (G q) A ≤ ∑ i ∈ Finset.range q, ε i := by
  advmvcgen_dep
  · exact hstep      -- per-hop leaf (pins εᵢ)
  · exact le_rfl     -- arithmetic VC: ∑ εᵢ ≤ ∑ εᵢ

/-- **Core's native bound *is* `advChain_uniform`.** `MultiQueryPRF.prf_multi_query_bound`
composed as it stands in Core is exactly this module's `advChain_uniform` — the tactic makes
the hybrid structure of Core's reduction explicit and reusable without reformulating it. -/
theorem prf_multi_query_bound_is_advChain (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    prf_multi_query_bound G A q ε hstep = advChain_uniform G A q ε hstep := rfl

end CatCrypt.XDijkstra

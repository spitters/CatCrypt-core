/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.HybridArgument
import CatCryptCore.Relational.Rules

/-!
# Multi-Query PRF Security via Hybrid Argument

This file provides the standard **q-fold hybrid argument** for bounding
the advantage of a q-query PRF adversary:

    `Adv_q(F) ≤ q · Adv_1(F)`

## Overview

Given a PRF `F : K → D → R`, the q-query PRF game answers q queries.
The hybrid argument interpolates between real and ideal:
- Hybrid 0: All queries answered by `F(k, ·)` (real)
- Hybrid i: First i queries answered by random function, rest by `F(k, ·)`
- Hybrid q: All queries answered by random function (ideal)

Each adjacent pair of hybrids differs by exactly one query, and the
advantage of distinguishing them is bounded by the single-query PRF
advantage. The total advantage is then at most `q · ε₁`.

## Key Theorems

* `prf_multi_query_bound` — `Adv(hyb 0, hyb q) ≤ q · ε` via `advantage_hybrid_uniform`
* `prf_multi_query_perfect` — Zero advantage when each step is perfectly secure
* `prf_multi_query_nested` — Nested hybrid: `Adv ≤ m · q · ε`

## References

* [Bellare & Rogaway, Introduction to Modern Cryptography]
* [Rosulek, The Joy of Cryptography, Claim 6.1]
-/

namespace CatCrypt.Crypto.MultiQueryPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.HybridArgument

open scoped ENNReal

/-! ## Abstract PRF Specification -/

/-- Abstract PRF specification parameterized by key, domain, and range types. -/
structure PRFSpec (K D R : Type) [Fintype K] [Nonempty K]
    [Fintype R] [Nonempty R] where
  /-- The PRF evaluation function -/
  eval : K → D → R

/-! ## Single-Query PRF Games -/

variable {K D R : Type} [Fintype K] [Nonempty K]
  [Fintype R] [Nonempty R]

/-- Single-query real PRF game: sample key, return F(k, x) -/
noncomputable def prf_query_real (F : PRFSpec K D R) (x : D) : SPComp R := do
  let k ← SPComp.sample K
  SPComp.pure (F.eval k x)

/-- Single-query ideal PRF game: return random R -/
noncomputable def prf_query_ideal (_x : D) : SPComp R :=
  SPComp.sample R

/-- Single-query PRF advantage for query x -/
noncomputable def prf_adv1 (F : PRFSpec K D R) (x : D) (A : R → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (prf_query_real F x) (prf_query_ideal x) A

/-! ## Multi-Query Hybrid Games

    The q-query hybrid game is parameterized by a natural number i.
    We use an **abstract** hybrid sequence indexed by ℕ, where:
    - G 0 = all-real game
    - G q = all-ideal game
    - G i differs from G (i+1) in exactly one query position

    The concrete construction of these hybrids depends on the query model.
    Here we provide the general-purpose bound that works for any such sequence.
-/

/-- **Multi-query PRF security bound**: the q-query advantage is at most q · ε.

    Given a sequence of q hybrid games `G` where each adjacent pair
    differs by at most ε, the total advantage is at most q · ε.

    In the PRF setting:
    - `G 0` = real game (all queries answered by PRF)
    - `G q` = ideal game (all queries answered randomly)
    - Each `G i → G (i+1)` changes one query from real to random -/
theorem prf_multi_query_bound {α : Type} (G : ℕ → SPComp α)
    (A : α → SPComp Bool) (q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA (G 0) (G q) A ≤ q * ε :=
  advantage_hybrid_uniform G A q ε hstep

/-- **Multi-query PRF with dependent step bounds**: different queries may
    have different single-query advantages. -/
theorem prf_multi_query_dep_bound {α : Type}
    (real ideal : SPComp α) (G : ℕ → SPComp α)
    (A : α → SPComp Bool) (q : ℕ) (ε : ℕ → ℝ≥0∞)
    (hleft : real = G 0) (hright : ideal = G q)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε i) :
    AdvantageA real ideal A ≤ ∑ i ∈ Finset.range q, ε i :=
  advantage_hybrid_dep_bound real ideal G A q ε hleft hright hstep

/-- **Perfect multi-query PRF**: when all steps are perfectly indistinguishable,
    the multi-query advantage is 0. -/
theorem prf_multi_query_perfect {α : Type} (G : ℕ → SPComp α) (q : ℕ)
    (hperf : ∀ i, i < q → rHoare eqPre (G i) (G (i + 1)) eqPost) :
    ∀ A, AdvantageA (G 0) (G q) A = 0 := fun A =>
  advantage_hybrid_zero G q hperf A

/-- **Nested multi-query bound**: for a two-level hybrid argument
    (e.g., multi-instance × multi-query), the total advantage is m · q · ε. -/
theorem prf_multi_query_nested {α : Type} (G : ℕ → SPComp α)
    (A : α → SPComp Bool) (m q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < m → AdvantageA (G i) (G (i + 1)) A ≤ q * ε) :
    AdvantageA (G 0) (G m) A ≤ m * q * ε :=
  advantage_hybrid_nested_eq G A m q ε hstep

end CatCrypt.Crypto.MultiQueryPRF

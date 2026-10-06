/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MultiQueryPRF
public import CatCryptCore.Crypto.SDistrLift
public import CatCryptCore.XDijkstra.Rel.XRelMvcgen
public import CatCryptCore.XDijkstra.Rel.XRelMvcgenControl
public import CatCryptCore.XDijkstra.Rel.XRelQ0


@[expose] public section
set_option autoImplicit false

/-!
# `relmvcgen` / `relSpec_forN` applied to a catcrypt-core protocol from dev

`relmvcgen` (`XRelMvcgen.lean`) and its control-flow superset `relmvcgen_ctl`
(`XRelMvcgenControl.lean`, firing `relSpec_forN`) are the XDijkstra relational
coupling tactics; they live in the **dev** repo. `CatCryptCore.Crypto.MultiQueryPRF`
is the **catcrypt-core** (published) q-query PRF hybrid reduction
`Adv_q(F) ≤ q · Adv_1(F)`. This file expresses that Core multi-hop reduction as
an XDijkstra `SDistr` coupling and lets the dev tactic do the composition —
demonstrating, from dev (which imports both), that the tactic reaches a Core
protocol even though the tactic itself lives in dev.

## What is tied to the Core defs

The per-query leaf programs are the Core PRF games:

* `prfQueryRealSD F x` is the `SDistr` distribution underlying the Core
  `MultiQueryPRF.prf_query_real F x` — `prfQueryRealSD_lift` proves
  `sdistrToSPComp (prfQueryRealSD F x) = prf_query_real F x`, i.e. it is the
  Core real single-query game lifted to `SPComp` by the canonical stateless
  embedding.
* `prfQueryIdealSD x` likewise underlies the Core `prf_query_ideal x`
  (`prfQueryIdealSD_lift`).

Both are built directly from the Core `PRFSpec.eval` and `SDistr.uniform`.

## What the tactic composes

* `prf_multi_query_coupling` — the **q-query hybrid as a coupled loop**. A round
  reads the next query index from the loop state `ℕ × List V`, answers it (real
  vs ideal), prepends the response, advances the counter — so the `n`-round
  uniform loop processes the distinct queries `xs 0, …, xs (n-1)`.
  `relmvcgen_ctl` fires `relSpec_forN`, composing the base coupling and the
  single per-round leaf into the end-to-end coupling at grade `ε₀ + n • ε`.
  `prf_multi_query_coupling_grade` records `n • ε = ↑n * ε`, so the coupling
  grade is the coupling-level analogue of the Core headline bound
  `prf_multi_query_bound`'s `q * ε`.
* `prf_three_query_coupling` — the straight-line variant: a fixed 3-query
  transcript, real vs ideal, composed by `relmvcgen` (the bind-chain tactic)
  into grade `(ε₁ + ε₂) + ε₃`, the coupling-level analogue of the Core
  `prf_multi_query_dep_bound`'s `∑ᵢ εᵢ` at `n = 3`.

## Scope — covered vs reformulation

The Core `MultiQueryPRF` reduction is **advantage/triangle-shaped**: it composes
per-hop `AdvantageA (G i) (G (i+1)) A ≤ ε` bounds by the triangle inequality
(`HybridArgument.advantage_hybrid_uniform`), on the stateful `SPComp`. It is
**not natively an `SDistr` coupling**. So this is a reformulation: the
same q-query hybrid structure, re-expressed as an `ε`-approximate `SDistr`
coupling (`XRelTripleQ0`, `liftRApprox`), where the tactic composes the per-round
leaves. Covered here is the composition — the grade-additive assembly of the
`n`-round hybrid — tied to the Core query games. The per-round coupling
leaf (`hstep`, the single-query PRF advantage as an `SDistr` coupling) is left as
a hypothesis: the tactic does composition, not leaves.

To use these tactics **inside** core (published), they would move down the stack
(dev → core): `relmvcgen` / `relSpec_forN` need only `SDistr` and the `RelQ0`
coupling structure, both already present in core (`SDist.lean`,
`instRelQ0SDistr`). Nothing about the tactic is dev-specific; it lives in dev
only by current publication status.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.MultiQueryPRF
open CatCrypt.Crypto.SDistrLift

variable {K D V : Type} [Fintype K] [Nonempty K] [Fintype V] [Nonempty V]

/-! ## 1. The single-query PRF games on `SDistr`, tied to the Core `SPComp` games -/

/-- Real single-query PRF game on `SDistr`: sample a key uniformly, evaluate the
    Core `PRFSpec.eval` at `x`. This is the `SDistr` distribution underlying the
    Core `MultiQueryPRF.prf_query_real`. -/
noncomputable def prfQueryRealSD (F : PRFSpec K D V) (x : D) : SDistr V :=
  SDistr.bind (SDistr.uniform K) (fun k => SDistr.pure (F.eval k x))

/-- Ideal single-query PRF game on `SDistr`: uniform range element. Underlies the
    Core `MultiQueryPRF.prf_query_ideal`. -/
noncomputable def prfQueryIdealSD (_x : D) : SDistr V :=
  SDistr.uniform V

/-- The stateless embedding of `SDistr.uniform` is `SPComp.sample`. -/
theorem sdistrToSPComp_uniform (α : Type) [Fintype α] [Nonempty α] :
    sdistrToSPComp (SDistr.uniform α) = SPComp.sample α := rfl

/-- **Tie to the Core def:** the `SDistr` real single-query game embeds to the
    Core `MultiQueryPRF.prf_query_real`. -/
theorem prfQueryRealSD_lift (F : PRFSpec K D V) (x : D) :
    sdistrToSPComp (prfQueryRealSD F x) = prf_query_real F x := by
  unfold prfQueryRealSD prf_query_real
  rw [sdistrToSPComp_bind, sdistrToSPComp_uniform]
  simp only [sdistrToSPComp_pure]
  rfl

/-- **Tie to the Core def:** the `SDistr` ideal single-query game embeds to the
    Core `MultiQueryPRF.prf_query_ideal`. -/
theorem prfQueryIdealSD_lift (x : D) :
    sdistrToSPComp (prfQueryIdealSD (V := V) x) = prf_query_ideal (R := V) x := by
  unfold prfQueryIdealSD prf_query_ideal
  exact sdistrToSPComp_uniform V

/-! ## 2. The q-query hybrid as a coupled loop -/

/-- Loop state: `(next query index, accumulated response transcript)`. -/
abbrev HybState (V : Type) : Type := ℕ × List V

/-- One real round of the q-query game: answer query `xs s.1` with the real PRF
    game `prfQueryRealSD`, prepend the response, advance the query counter. -/
noncomputable def prfRoundReal (F : PRFSpec K D V) (xs : ℕ → D) (s : HybState V) :
    SDistr (HybState V) :=
  SDistr.bind (prfQueryRealSD F (xs s.1)) (fun r => SDistr.pure (s.1 + 1, r :: s.2))

/-- One ideal round: answer query `xs s.1` with the ideal game `prfQueryIdealSD`. -/
noncomputable def prfRoundIdeal (xs : ℕ → D) (s : HybState V) : SDistr (HybState V) :=
  SDistr.bind (prfQueryIdealSD (V := V) (xs s.1)) (fun r => SDistr.pure (s.1 + 1, r :: s.2))

/-- **The q-query PRF hybrid composed by `relmvcgen_ctl`.**

    A base coupling of the initial loop states at `ε₀`, and a single per-round
    coupling leaf at `(ε, Rinv)` — each round maps `Rinv`-related states to
    `Rinv`-related states, coupling one real query with one ideal query at grade
    `ε` (the single-query PRF advantage as an `SDistr` coupling) — compose to the
    end-to-end coupling of the `n`-round real vs ideal hybrid at grade
    `ε₀ + n • ε`. `relmvcgen_ctl` fires `relSpec_forN` to do the composition; the
    grade accumulates in the type index (no unrolling), for general `n`.

    This is the coupling-level form of the Core `prf_multi_query_bound`'s
    `Adv(G 0, G q) ≤ q · ε`, with the per-round leaf tied to the Core PRF
    query games (`prfRoundReal`/`prfRoundIdeal` built from `PRFSpec.eval`). -/
theorem prf_multi_query_coupling
    (F : PRFSpec K D V) (xs : ℕ → D)
    (Rinv : HybState V → HybState V → Prop) (ε₀ ε : ℝ≥0∞)
    (init₁ init₂ : SDistr (HybState V))
    (hbase : XRelTripleQ0 (T := SDistr) ε₀ Rinv init₁ init₂)
    (hstep : ∀ s s', Rinv s s' →
      XRelTripleQ0 (T := SDistr) ε Rinv (prfRoundReal F xs s) (prfRoundIdeal xs s'))
    (n : ℕ) :
    XRelTripleQ0 (T := SDistr) (ε₀ + n • ε) Rinv
      (relForN (prfRoundReal F xs) init₁ n) (relForN (prfRoundIdeal xs) init₂ n) := by
  relmvcgen_ctl
  · exact hbase                          -- base coupling of the initial loop states
  · intro a b hab; exact hstep a b hab   -- per-round PRF query coupling leaf

/-- The loop grade `n • ε` is `↑n * ε`: the coupling grade of `prf_multi_query_coupling`
    has exactly the shape of the Core `prf_multi_query_bound`'s advantage bound
    `q * ε`, at the coupling level. -/
theorem prf_multi_query_coupling_grade (n : ℕ) (ε : ℝ≥0∞) : n • ε = (n : ℝ≥0∞) * ε :=
  nsmul_eq_mul n ε

/-! ## 3. The straight-line variant — a fixed 3-query transcript by `relmvcgen` -/

/-- **A fixed 3-query PRF sequence coupled by `relmvcgen`.**

    Three real queries `x₁, x₂, x₃` answered in sequence, coupled with the
    corresponding three ideal queries. `relmvcgen` fires `relSpec_seq` twice,
    leaving exactly the three per-query coupling leaves; the grade
    `(ε₁ + ε₂) + ε₃` is read off the type index. This is the coupling-level form
    of the Core `prf_multi_query_dep_bound`'s `∑ᵢ εᵢ` at `n = 3`, with each leaf a
    single-query PRF coupling on the Core games (`prfQueryRealSD` /
    `prfQueryIdealSD`, built from `PRFSpec.eval`). -/
theorem prf_three_query_coupling
    (F : PRFSpec K D V) (x₁ x₂ x₃ : D)
    {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ R₁ R₂ : V → V → Prop}
    (h₁ : XRelTripleQ0 (T := SDistr) ε₁ R₀
      (prfQueryRealSD F x₁) (prfQueryIdealSD (V := V) x₁))
    (h₂ : ∀ a b, R₀ a b → XRelTripleQ0 (T := SDistr) ε₂ R₁
      (prfQueryRealSD F x₂) (prfQueryIdealSD (V := V) x₂))
    (h₃ : ∀ a b, R₁ a b → XRelTripleQ0 (T := SDistr) ε₃ R₂
      (prfQueryRealSD F x₃) (prfQueryIdealSD (V := V) x₃)) :
    XRelTripleQ0 (T := SDistr) ((ε₁ + ε₂) + ε₃) R₂
      (RelQ0.bind' (RelQ0.bind' (prfQueryRealSD F x₁)
        (fun _ => prfQueryRealSD F x₂)) (fun _ => prfQueryRealSD F x₃))
      (RelQ0.bind' (RelQ0.bind' (prfQueryIdealSD (V := V) x₁)
        (fun _ => prfQueryIdealSD (V := V) x₂)) (fun _ => prfQueryIdealSD (V := V) x₃)) := by
  relmvcgen
  · exact h₁
  · intro a b hab; exact h₂ a b hab
  · intro a b hab; exact h₃ a b hab

end CatCrypt.XDijkstra

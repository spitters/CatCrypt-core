/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XAdvantageHybrid
public import CatCryptCore.XDijkstra.Rel.XRelMvcgen
public import CatCryptCore.XDijkstra.Rel.XRelMvcgenControl
public import CatCryptCore.XDijkstra.Rel.XLargeReduction


@[expose] public section
set_option autoImplicit false

/-!
# `XCombinedAutomation`: `advmvcgen!` / `relmvcgen!` — composition + VC-discharge

`advmvcgen!` / `relmvcgen!` are the XDijkstra composition tactics **chained with
arithmetic-VC discharge** (`le_rfl` / `gcongr` / `norm_num`) and trivial-base
discharge (`xrelQ0_pure`), so that firing one tactic leaves **only the cryptographic
leaves** — blind arithmetic automation first, crypto leaves last.

## The design — two residual goal types, one auto-dischargeable

The bare composition tactics of this frontier reduce a bound to **two** residual goal
shapes:

* **(a) the arithmetic verification condition** — `n * ε ≤ budget` / `∑ ε i ≤ budget`
  for the advantage axis (`advmvcgen`/`advmvcgen_dep`), or the grade weakening
  `ε ≤ budget` for the coupling axis; and
* **(b) the per-hop cryptographic leaves** — the per-hop `AdvantageA` bounds
  (advantage axis) or the per-hop `ε`-approximate couplings (coupling axis);
* **(b′) a trivial grade-0 base** — for a coupled loop (`relSpec_forN`), the base coupling
  of the initial states, at grade `0`, `R`-related points lifting to the zero-error triple
  (`xrelQ0_pure`).

Goal type (a) is a pure arithmetic obligation and (b′) is structural — both are
**mechanically dischargeable**. Only the (b) leaves carry cryptographic content (the actual
advantage / coupling assumptions). The `!` tactics fire the composition and then run a
discharge cascade on the residuals, closing (a) and (b′) and leaving exactly the (b)
cryptographic leaves: blind arithmetic automation first, crypto leaves last.

## What each `!` tactic closes vs. leaves

| Tactic | Fires | Auto-closes | Leaves |
|--------|-------|-------------|--------|
| `advmvcgen!` | `advChain_uniform_le` | VC `n * ε ≤ budget` | per-hop `AdvantageA` leaf |
| `advmvcgen_dep!` | `advChain_triangle_le` | VC `∑ ε i ≤ budget` | per-hop `AdvantageA` leaf |
| `relmvcgen!` | `relSpec_seq` / `relSpec_forN` / … | grade-0 base (`xrelQ0_pure`) + arith VC | per-hop coupling leaf |
| `advmvcgen!?` | `advChain_uniform_le` | VC **and** hypothesis-fed leaves (`assumption`) | (nothing, if leaves are in context) |
| `relmvcgen!?` | `relSpec_seq` / … | base **and** hypothesis-fed coupling leaves | (nothing, if leaves are in context) |

The **VC-discharge cascade** is `first | exact le_rfl | gcongr | norm_num`, applied under
`try` to every residual. `le_rfl` closes the **tight** budget shapes (`n * ε ≤ n * ε`,
`∑ ε i ≤ ∑ ε i`) that a `≤ budget` goal collapses to when the budget is the composed bound
itself; `gcongr` / `norm_num` handle looser monotone shapes (`n * ε ≤ n * ε'` with
`ε ≤ ε'`, numeric budgets). The cascade is deliberately **arithmetic-only** in the base `!`
variants — it never touches a `∀ … → AdvantageA …` / `∀ a b, R a b → …` leaf, because those
are not `≤`/`<`/numeric goals, so `try` leaves them untouched. The **grade-0 base** is closed
by `apply xrelQ0_pure <;> assumption` (the `R a b`-related initial points).

`omega` is **deliberately excluded**: on the residual leaf `∀ i, i < n → AdvantageA … ≤ ?ε`,
with `?ε` still an unpinned metavariable, `omega` closes the goal by assigning the metavariable
(it fails on the same leaf once `?ε` is concrete). That is a leaf-eating side effect, not a VC
discharge — and the VC lives in `ℝ≥0∞`, which `omega` cannot address anyway — so the cascade
uses `le_rfl` / `gcongr` / `norm_num` for the VC.

`grind` and `assumption` are held back to the `!?` **leaf-hook** variants (with `assumption`
placed **first** in the cascade, ahead of `gcongr` / `norm_num`, which can *succeed with no
progress* and short-circuit a trailing `assumption`): they close the cryptographic leaves when
the per-hop bound is itself a hypothesis in context (a fully hypothesis-fed reduction then
closes **entirely**). They are excluded from the base `!` variants precisely because they
*would* reach into a leaf via its per-hop hypothesis, which is the leaf-hook behavior, not the
"leave only the crypto leaves" behavior.

## Goal-count comparison (see the demos below)

| Goal | bare tactic | `!` tactic | `!?` tactic |
|------|-------------|-----------|-------------|
| `MultiQueryPRF` uniform (`AdvantageA (G 0) (G q) A ≤ q * ε`) | 2 (leaf + VC) | **1** (leaf) | **0** |
| `MultiQueryPRF` dep (`… ≤ ∑ ε i`) | 2 (leaf + VC) | **1** (leaf) | **0** |
| large-reduction loop (`… (0 + n • ε)`) | 2 (base + per-round) | **1** (per-round) | **0** |
| straight-line 3-hop coupling | 3 (leaves) | 3 (leaves) | **0** |

The straight-line coupling has no VC and no trivial base, so `relmvcgen!` leaves the same 3
crypto leaves as `relmvcgen` (nothing to auto-discharge) — the reduction is on the axes that
produce an arithmetic VC or a trivial base. The `!?` leaf-hook closes all four entirely when
the per-hop bounds are hypotheses.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.HybridArgument
open CatCrypt.Crypto.MultiQueryPRF

/-! ## 1. The combined tactics

Each `!` tactic runs a composition tactic and then the discharge cascade under `<;> try (…)`,
so the cascade is attempted on every residual goal and (via `try`) leaves the goals it cannot
close. The arithmetic-only cascade closes the VC / grade-0 base and leaves the cryptographic
leaves; the `!?` leaf-hook cascade additionally tries `assumption` / `grind`, closing
hypothesis-fed leaves. -/

/-- **`advmvcgen!` — advantage composition + arithmetic-VC discharge (uniform).** Fires
`advChain_uniform_le` (via `advmvcgen`) on a goal `AdvantageA (G 0) (G n) A ≤ budget`, then
discharges the arithmetic VC `n * ε ≤ budget` with `first | exact le_rfl | gcongr |
norm_num`, leaving exactly the per-hop cryptographic leaf `∀ i, i < n → AdvantageA (G i)
(G (i+1)) A ≤ ε`. The metavariable `?ε` is pinned by the tight VC (`le_rfl` unifies it), so
the residual leaf is fully concrete. -/
macro "advmvcgen!" : tactic =>
  `(tactic| (advmvcgen <;> (try (first | exact le_rfl | gcongr | norm_num))))

/-- **`advmvcgen! [budget]` — with an explicit budget bound.** Like `advmvcgen!` but discharges
the arithmetic VC with the supplied bound `hbudget : n * ε ≤ budget` first (for a loose budget
that `le_rfl` cannot collapse), falling back to the arithmetic cascade. Leaves the per-hop
crypto leaf. -/
macro "advmvcgen!" "[" h:term "]" : tactic =>
  `(tactic| (advmvcgen <;> (try (first | exact $h | exact le_rfl | gcongr | norm_num))))

/-- **`advmvcgen_dep!` — advantage composition + VC discharge (per-hop / varying).** Fires
`advChain_triangle_le` (via `advmvcgen_dep`), then discharges the arithmetic VC
`∑ i ∈ Finset.range n, ε i ≤ budget`, leaving the per-hop crypto leaf. -/
macro "advmvcgen_dep!" : tactic =>
  `(tactic| (advmvcgen_dep <;> (try (first | exact le_rfl | gcongr | norm_num))))

/-- **`advmvcgen_dep! [budget]`** — the varying form with an explicit budget bound. -/
macro "advmvcgen_dep!" "[" h:term "]" : tactic =>
  `(tactic| (advmvcgen_dep <;> (try (first | exact $h | exact le_rfl | gcongr | norm_num))))

/-- **`relmvcgen!` — coupling composition + trivial-base + grade-VC discharge.** Fires the
coupling-composition rules (via `relmvcgen_ctl`: `relSpec_seq` for bind-chains, `relSpec_forN`
for coupled loops, `relSpec_ite` for shared-condition branches), then discharges (i) the
trivial grade-0 base coupling `XRelTripleQ0 0 R (pure a) (pure a)` with
`apply xrelQ0_pure <;> assumption` (the `R a b`-related initial points), and (ii) any
arithmetic grade VC with `first | exact le_rfl | gcongr | norm_num`. Leaves exactly the
per-hop cryptographic coupling leaves. The arithmetic-only cascade never touches a
`∀ a b, R a b → …` leaf. -/
macro "relmvcgen!" : tactic =>
  `(tactic| (relmvcgen_ctl <;>
     (try (first
       | exact le_rfl
       | (apply xrelQ0_pure <;> assumption)
       | gcongr
       | norm_num))))

/-! ### The leaf-hook variants (`!?`)

`advmvcgen!?` / `relmvcgen!?` extend the base `!` cascade with `assumption` (and `grind`),
which close a cryptographic leaf **when the per-hop bound is a hypothesis in context**. A
fully hypothesis-fed reduction then closes entirely — no residual goals. `assumption` matching
a hypothesis of the leaf's exact shape simultaneously pins the deferred per-hop metavariable
(`?ε` on the advantage axis, the intermediate relation `?R` on the coupling axis), exactly as a
hand `exact hᵢ` would. These are held out of the base `!` variants because they would reach
into a leaf, which is the opposite of the "leave only the crypto leaves" contract. -/

/-- **`advmvcgen!?` — `advmvcgen!` plus a leaf-hook.** As `advmvcgen!`, but the cascade also
tries `assumption` (then `grind`) on the residuals, closing the per-hop `AdvantageA` leaf when
it is a hypothesis. A hypothesis-fed uniform hybrid closes with no residual goals. -/
macro "advmvcgen!?" : tactic =>
  `(tactic| (advmvcgen <;>
     (try (first | assumption | exact le_rfl | gcongr | norm_num | grind))))

/-- **`relmvcgen!?` — `relmvcgen!` plus a leaf-hook.** As `relmvcgen!`, but the cascade also
tries `assumption` (then `grind`) on the residuals, closing a per-hop coupling leaf when it is
a hypothesis. A hypothesis-fed coupling chain closes with no residual goals; `assumption` pins
each intermediate relation metavariable as it discharges the matching leaf. -/
macro "relmvcgen!?" : tactic =>
  `(tactic| (relmvcgen_ctl <;>
     (try (first
       | assumption
       | exact le_rfl
       | (apply xrelQ0_pure <;> assumption)
       | gcongr
       | norm_num
       | grind))))

/-! ## 2. Advantage-axis demos — `advmvcgen!` closes the VC, leaving only the leaf

The bare `advmvcgen` leaves **2** goals on the `MultiQueryPRF` uniform hybrid: the per-hop
single-query leaf and the arithmetic VC `q * ε ≤ q * ε`. `advmvcgen!` closes the VC with
`le_rfl`, leaving **1** goal — the crypto leaf. -/

variable {α : Type}

/-- **The q-query PRF bound with `advmvcgen!` — 1 residual goal (the leaf).** Compare
`XAdvantageHybrid.prf_multi_query_via_advmvcgen`, which after `advmvcgen` has **two** bullet
goals (`exact hstep`; `exact le_rfl`). Here `advmvcgen!` fires the triangle fold *and* closes
the arithmetic VC `q * ε ≤ q * ε` (`le_rfl`), so **only the single-query crypto leaf remains**
— discharged by the single bullet, which also pins `ε`. -/
theorem prf_multi_query_via_advmvcgen_bang (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA (G 0) (G q) A ≤ q * ε := by
  advmvcgen!
  exact hstep          -- the only residual goal: the per-hop single-query crypto leaf

/-- **Varying per-query advantages with `advmvcgen_dep!` — 1 residual goal.** The dep chain
composes to `∑ i ∈ Finset.range q, ε i`; `advmvcgen_dep!` fires the triangle fold and closes
the arithmetic VC `∑ ε i ≤ ∑ ε i` (`le_rfl`), leaving only the per-hop leaf. -/
theorem prf_multi_query_dep_via_advmvcgen_dep_bang (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (q : ℕ) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε i) :
    AdvantageA (G 0) (G q) A ≤ ∑ i ∈ Finset.range q, ε i := by
  advmvcgen_dep!
  exact hstep          -- the only residual goal: the per-hop leaf

/-- **The single-query PRF advantage as the leaf, with `advmvcgen!`.** As
`XAdvantageHybrid.prf_multi_query_from_single`, but `advmvcgen!` closes the arithmetic VC, so
only the crypto leaf (grounded in the single-query PRF advantage
`MultiQueryPRF.prf_adv1`) remains. -/
theorem prf_multi_query_from_single_via_advmvcgen_bang {K D R : Type} [Fintype K] [Nonempty K]
    [Fintype R] [Nonempty R] (F : PRFSpec K D R) (x : D) (A : R → SPComp Bool)
    (G : ℕ → SPComp R) (q : ℕ) (ε : ℝ≥0∞)
    (hsingle : prf_adv1 F x A ≤ ε)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ prf_adv1 F x A) :
    AdvantageA (G 0) (G q) A ≤ q * ε := by
  advmvcgen!
  intro i hi; exact le_trans (hstep i hi) hsingle   -- the only residual goal: the crypto leaf

/-! ### The advantage leaf-hook — `advmvcgen!?` closes the hypothesis-fed hybrid entirely

When the per-hop leaf is exactly a hypothesis (`hstep`), `advmvcgen!?` closes **both** the VC
and the leaf: **0** residual goals. -/

/-- **The q-query PRF bound with `advmvcgen!?` — 0 residual goals.** The per-hop bound `hstep`
is a hypothesis of the leaf's exact shape, so the leaf-hook's `assumption` discharges the leaf
(pinning `ε`) and `le_rfl` closes the VC — the whole hybrid closes with no bullets. -/
theorem prf_multi_query_via_advmvcgen_bang_hook (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA (G 0) (G q) A ≤ q * ε := by
  advmvcgen!?

/-! ## 3. Coupling-axis demo — `relmvcgen!` closes the grade-0 base, leaving the per-round leaf

The bare `relmvcgen_ctl` leaves **2** goals on an `n`-round coupled loop with a grade-0 base:
the base coupling `XRelTripleQ0 0 R (pure rk₀) (pure rk₀)` and the per-round leaf.
`relmvcgen!` closes the grade-0 base with `xrelQ0_pure`, leaving **1** goal — the per-round
crypto coupling leaf. This is the loop shape of a multi-round reduction (the base is the
trivial initial-state coupling). -/

section LoopDemo
variable {W : Type}

/-- **`n`-round coupled loop with `relmvcgen!` — 1 residual goal (the per-round leaf).**
Compare `XRelMvcgenControl.relDemo_loop_tac`,
which after `relmvcgen_ctl` has **two** bullet goals (`exact xrelQ0_pure hR₀`; the per-round
leaf). Here `relmvcgen!` fires `relSpec_forN` *and* closes the grade-0 base
`XRelTripleQ0 0 R (pure rk₀) (pure rk₀)` (`apply xrelQ0_pure <;> assumption`, using `hR₀`), so
**only the per-round coupling leaf remains** — the large-reduction loop shape with the summed
grade `0 + n • ε` in the index. -/
theorem loop_coupling_via_relmvcgen_bang {R : W → W → Prop}
    {k₁ k₂ : W → SDistr W}
    {ε : ℝ≥0∞} (rk₀ : W) (n : ℕ) (hR₀ : R rk₀ rk₀)
    (hstep : ∀ a b, R a b → XRelTripleQ0 (T := SDistr) ε R (k₁ a) (k₂ b)) :
    XRelTripleQ0 (T := SDistr) (0 + n • ε) R
      (relForN k₁ (SDistr.pure rk₀) n) (relForN k₂ (SDistr.pure rk₀) n) := by
  relmvcgen!
  intro a b hab; exact hstep a b hab   -- the only residual goal: the per-round crypto leaf

/-- **The same loop with `relmvcgen!?` — 0 residual goals.** The per-round leaf `hstep` is a
hypothesis, so the leaf-hook's `assumption` discharges it (pinning the invariant relation) and
`xrelQ0_pure` closes the base — the whole loop coupling closes with no bullets. -/
theorem loop_coupling_via_relmvcgen_bang_hook {R : W → W → Prop}
    {k₁ k₂ : W → SDistr W}
    {ε : ℝ≥0∞} (rk₀ : W) (n : ℕ) (hR₀ : R rk₀ rk₀)
    (hstep : ∀ a b, R a b → XRelTripleQ0 (T := SDistr) ε R (k₁ a) (k₂ b)) :
    XRelTripleQ0 (T := SDistr) (0 + n • ε) R
      (relForN k₁ (SDistr.pure rk₀) n) (relForN k₂ (SDistr.pure rk₀) n) := by
  relmvcgen!?

end LoopDemo

/-! ## 4. Straight-line coupling — no VC, no base, so `!` leaves the same crypto leaves

A straight-line 3-hop coupling has neither an arithmetic VC nor a trivial base, so `relmvcgen!`
leaves the same **3** crypto leaves as `relmvcgen` (the cascade finds nothing to auto-close).
The `!?` leaf-hook closes all three when they are hypotheses. This bounds the automation: the
`!` reduction is exactly the VC + trivial-base discharge; the crypto leaves are never
auto-discharged. -/

section StraightLine
variable {T : Type → Type} [RelQ0 T]
variable {α₀ β₀ α₁ β₁ α₂ β₂ : Type}

/-- **3-hop coupling with `relmvcgen!?` — 0 residual goals.** The three per-hop couplings
`h₁ h₂ h₃` are hypotheses, so the leaf-hook closes the whole chain; `assumption` pins each
intermediate relation metavariable as it discharges the matching leaf (`?R` shared between a
prefix leaf and its continuation). -/
theorem relDemo3_via_relmvcgen_bang_hook {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : T α₀} {m₂ : T β₀}
    {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b)) :
    RelSpecTriple ((ε₁ + ε₂) + ε₃) R₂
      (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) := by
  relmvcgen!?

end StraightLine

end CatCrypt.XDijkstra

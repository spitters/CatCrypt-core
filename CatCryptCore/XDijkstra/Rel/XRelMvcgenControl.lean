/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.Rel.XRelMvcgen
public import CatCryptCore.XDijkstra.Rel.XRelSpecMonad
public import CatCryptCore.XDijkstra.Rel.XLargeReduction


@[expose] public section
set_option autoImplicit false

/-!
# `XRelMvcgenControl`: relational control flow for the coupling tactic

Relational control flow for the coupling tactic — branch (`relSpec_ite`) and bounded loop
(`relSpec_forN`), so `relmvcgen` / `relmvcgen_ctl` reduces coupling goals with branching and
loops to per-branch / per-round leaves; the coupling-axis counterpart of `XMvcgenControl`.

`relmvcgen` (`XRelMvcgen.lean`) reduces a **straight-line** coupling bind-chain to its per-hop
leaves by firing `relBind_spec` / `relSpec_seq` at every `bind` node. A cryptographic
reduction is not straight-line: it **branches** (couple two conditionals) and runs **bounded
hybrid loops** (an `n`-round coupled hybrid). This module supplies the two relational
composition rules those forms need and extends the tactic to fire them, exactly mirroring what
`XMvcgenControl.lean` (`xite_triple`, `xfor_triple`) does on the unary WP/grade axis.

## What this module provides

1. **Relational branch — `relSpec_ite`.** Two conditionals over a **shared condition** `c`,
   `bif c then t₁ else e₁` / `bif c then t₂ else e₂`. If the `then`-legs couple at `(ε_t, R)`
   and the `else`-legs at `(ε_e, R)`, the conditionals couple at grade `ε_t ⊔ ε_e`, carrying
   `R`. The proof cases on the shared boolean; each branch is a leaf coupling weakened to the
   `sup` grade via `RelQ0.liftR_mono_eps`. This is the coupling-axis analogue of
   `XMvcgenControl.xite_triple`. `relSpec_ite'` gives the per-branch-grade (no `sup`) form.

   The *differing-condition* case (`bif c … / bif c' …` with `c ≠ c'`) is **not** deliverable
   from same-relation branch couplings alone — see §1 for the obstacle.

2. **Relational bounded loop — `relSpec_forN`.** `n` coupled rounds — a base coupling at `ε₀`
   and a per-round leaf coupling at `(ε, R → R)` — compose to `RelSpecTriple (ε₀ + n • ε) R
   (relForN k₁ m₁ n) (relForN k₂ m₂ n)` by induction over `relSpec_seq`. It packages
   `XLargeReduction.largeN_reduction_uniform` (over the left-nested Kleisli iterate `iterK`) as
   a reusable loop rule; `relSpec_forN_varying` is the per-round-advantage `∑` variant.

3. **The extended tactic — `relmvcgen_ctl`.** A superset of `relmvcgen` that also fires
   `relSpec_ite` / `relSpec_forN`, reducing a coupling goal that contains a branch or a bounded
   loop to the per-branch / per-round leaves; the grade (`ε_t ⊔ ε_e` for a branch, `ε₀ + n • ε`
   for a loop) is threaded automatically in the type index. Demos: (a) a coupled conditional
   reduced to its two branch leaves; (b) an `n`-round coupled loop reduced to the base + the
   per-round leaf, the `n • ε` grade carried in the index.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob

variable {T : Type → Type} [RelQ0 T]

/-! ## 1. Relational branch — `relSpec_ite` (shared condition)

`relSpec_ite` couples two conditionals over the **same** boolean `c`. The couplings agree on
the branch: the `then`-legs are coupled at `(ε_t, R)`, the `else`-legs at `(ε_e, R)` — the
*same* post-relation `R` on both legs (the branches reconverge). Casing on `c` selects one
leg pair; weakening its grade to the `sup ε_t ⊔ ε_e` (via `RelQ0.liftR_mono_eps`) gives a
single grade covering both arms. This is the coupling-axis counterpart of
`XMvcgenControl.xite_triple`.

**Obstacle — differing conditions.** For `bif c then t₁ else e₁` vs `bif c' then t₂ else e₂`
with `c ≠ c'`, casing produces the *cross* pairs `(t₁, e₂)` and `(e₁, t₂)`, which the
hypotheses (couplings of `t₁` with `t₂` and `e₁` with `e₂`) do **not** cover. A coupling of
the two conditionals then requires either (i) the two booleans themselves to be coupled — the
coupling relation must track the branch value, i.e. the conditionals must be phrased
`bind (sample c) (fun b => bif b …)` and handled by the *bind* rule, not a branch rule — or
(ii) cross-couplings `t₁ ~ e₂`, `e₁ ~ t₂` supplied as extra hypotheses. Neither is derivable
from the two same-relation branch couplings, so no rule of `relSpec_ite`'s signature exists
for the differing-condition case; it is the bind rule's job once the branch value is
sampled. This module delivers the shared-condition rule. -/

/-- **Relational conditional (shared condition), `sup` grade.** Couple `bif c then t₁ else e₁`
with `bif c then t₂ else e₂` over a shared boolean `c`: from a `then`-coupling at `(ε_t, R)`
and an `else`-coupling at `(ε_e, R)`, the conditionals couple at grade `ε_t ⊔ ε_e`, carrying
`R`. Cases on the shared `c`; each arm is the corresponding branch leaf weakened to the `sup`
grade. The coupling-axis analogue of `XMvcgenControl.xite_triple`. -/
theorem relSpec_ite {ε_t ε_e : ℝ≥0∞} {α β : Type} {R : α → β → Prop}
    (c : Bool) {t₁ e₁ : T α} {t₂ e₂ : T β}
    (ht : RelSpecTriple ε_t R t₁ t₂)
    (he : RelSpecTriple ε_e R e₁ e₂) :
    RelSpecTriple (ε_t ⊔ ε_e) R (bif c then t₁ else e₁) (bif c then t₂ else e₂) := by
  cases c
  · exact RelQ0.liftR_mono_eps le_sup_right he
  · exact RelQ0.liftR_mono_eps le_sup_left ht

/-- **Relational conditional (shared condition), per-branch grade.** The exact-grade form: the
result grade is the *selected* branch's grade `bif c then ε_t else ε_e`, with no `sup`
weakening. Useful when the concrete `c` is known. Cases on `c`. -/
theorem relSpec_ite' {ε_t ε_e : ℝ≥0∞} {α β : Type} {R : α → β → Prop}
    (c : Bool) {t₁ e₁ : T α} {t₂ e₂ : T β}
    (ht : RelSpecTriple ε_t R t₁ t₂)
    (he : RelSpecTriple ε_e R e₁ e₂) :
    RelSpecTriple (bif c then ε_t else ε_e) R
      (bif c then t₁ else e₁) (bif c then t₂ else e₂) := by
  cases c
  · exact he
  · exact ht

/-! ## 2. Relational bounded loop — `relSpec_forN`

`relForN k m n` is the `n`-fold left-nested Kleisli iterate `XLargeReduction.iterK` (append
one step on the outside). `relSpec_forN` packages `largeN_reduction_uniform` as a loop rule: a
base coupling at `ε₀` plus a per-round coupling leaf at `(ε, R → R)` (each round preserves the
invariant relation `R`) compose to a coupling of the `n`-fold iterate at grade `ε₀ + n • ε`.
The whole arbitrary-length composition is one `induction` over `relSpec_seq` — the loop-axis
counterpart of `XMvcgenControl.xfor_triple`. -/

section Loop
variable {α : Type}

/-- **The relational bounded-loop combinator.** `relForN k m n` folds the coupled round `k`
`n` times from the base `m`, left-nested (`XLargeReduction.iterK`). -/
def relForN (k : α → T α) (m : T α) (n : ℕ) : T α := iterK k m n

@[simp] theorem relForN_zero (k : α → T α) (m : T α) : relForN k m 0 = m := rfl

@[simp] theorem relForN_succ (k : α → T α) (m : T α) (n : ℕ) :
    relForN k m (n + 1) = RelQ0.bind' (relForN k m n) k := rfl

/-- **Relational bounded-loop rule (uniform per-round advantage).** From a base coupling at
`ε₀` and a per-round coupling leaf at `(ε, R → R)` — every round preserves the invariant
relation `R` — the `n`-round loop `relForN` is coupled at grade `ε₀ + n • ε`, carrying `R`.
Packages `XLargeReduction.largeN_reduction_uniform`; the grade `n • ε` accumulates in the type
index by the one induction over `relSpec_seq`. The coupling-axis counterpart of
`XMvcgenControl.xfor_triple` (there an invariant through `n` iterations; here an invariant
*coupling* through `n` rounds, with the advantage summing). -/
theorem relSpec_forN {ε₀ ε : ℝ≥0∞} {R : α → α → Prop}
    {m₁ m₂ : T α} {k₁ k₂ : α → T α}
    (hbase : RelSpecTriple ε₀ R m₁ m₂)
    (hstep : ∀ a b, R a b → RelSpecTriple ε R (k₁ a) (k₂ b)) (n : ℕ) :
    RelSpecTriple (T := T) (ε₀ + n • ε) R (relForN k₁ m₁ n) (relForN k₂ m₂ n) :=
  largeN_reduction_uniform hbase hstep n

/-- **Relational bounded-loop rule (per-round advantages).** Each round `i` has its own
advantage `ε i` (and its own coupled step `k · i`), preserving `R`; the `n`-round loop over
the varying iterate `iterKV` is coupled at grade `ε₀ + ∑_{i<n} ε i`, carrying `R`. Packages
`XLargeReduction.largeN_reduction_varying` — the varying-`εᵢ` loop is no harder than the
uniform one. -/
theorem relSpec_forN_varying {ε₀ : ℝ≥0∞} {ε : ℕ → ℝ≥0∞} {R : α → α → Prop}
    {m₁ m₂ : T α} {k₁ k₂ : ℕ → α → T α}
    (hbase : RelSpecTriple ε₀ R m₁ m₂)
    (hstep : ∀ i a b, R a b → RelSpecTriple (ε i) R (k₁ i a) (k₂ i b)) (n : ℕ) :
    RelSpecTriple (T := T) (ε₀ + ∑ i ∈ Finset.range n, ε i) R
      (iterKV k₁ m₁ n) (iterKV k₂ m₂ n) :=
  largeN_reduction_varying hbase hstep n

end Loop

/-! ## 3. The extended tactic — `relmvcgen_ctl`

`relmvcgen_ctl` is a superset of `relmvcgen`: it repeatedly fires, at the main goal,
`relBind_spec` / `relSpec_seq` (the straight-line bind rules) **and** `relSpec_ite` /
`relSpec_forN` (the control-flow rules). On a coupling goal that contains a branch or a bounded
loop it splits off the per-branch / per-round leaves, with the grade — `ε_t ⊔ ε_e` for a
branch, `ε₀ + n • ε` for a loop — threaded automatically in the type index. The intermediate
per-hop / per-round relation is left as a metavariable, pinned when each leaf is discharged,
exactly as for `relmvcgen` (see `XRelMvcgen`'s calling convention). `apply`, not `refine`, for
the same metavariable-deferral reason. -/

/-- **Relational control-flow VC generator.** Extends `relmvcgen` with the two relational
control-flow rules: on a coupling goal with a shared-condition branch (`bif c …`) or a bounded
loop (`relForN`), fires `relSpec_ite` / `relSpec_forN` (alongside the bind rules
`relBind_spec` / `relSpec_seq`), reducing the goal to the per-branch / per-round coupling
leaves; the grade is threaded in the type index. Discharge each residual leaf with its coupling
hypothesis. -/
macro "relmvcgen_ctl" : tactic =>
  `(tactic| repeat first
    | apply relBind_spec
    | apply relSpec_seq
    | apply relSpec_ite
    | apply relSpec_forN)

/-! ## 4. Demos — the extended tactic fires on branch and loop -/

section Demo
variable {α₀ β₀ α : Type}

/-- **(a) Coupled conditional reduced to its two branch leaves.** The two conditionals over a
shared `b`, `bif b then t₁ else e₁` / `bif b then t₂ else e₂`, couple at grade `ε_t ⊔ ε_e`.
`relmvcgen_ctl` fires `relSpec_ite`, leaving exactly the `then`-leaf and the `else`-leaf, each
discharged from its coupling hypothesis. -/
theorem relDemo_branch_tac {ε_t ε_e : ℝ≥0∞} {R : α₀ → β₀ → Prop} (b : Bool)
    {t₁ e₁ : T α₀} {t₂ e₂ : T β₀}
    (ht : RelSpecTriple ε_t R t₁ t₂)
    (he : RelSpecTriple ε_e R e₁ e₂) :
    RelSpecTriple (ε_t ⊔ ε_e) R (bif b then t₁ else e₁) (bif b then t₂ else e₂) := by
  relmvcgen_ctl
  · exact ht   -- then-leg leaf
  · exact he   -- else-leg leaf

/-- **(b) `n`-round coupled loop reduced to the per-round leaf + the `n • ε` grade.** The
`n`-round coupled hybrid `relForN` couples at grade `ε₀ + n • ε`, for **general `n`**.
`relmvcgen_ctl` fires `relSpec_forN`, leaving the base coupling and the single per-round leaf;
the `n • ε` grade is carried in the type index (no unrolling). -/
theorem relDemo_loop_tac {ε₀ ε : ℝ≥0∞} {R : α → α → Prop} (n : ℕ)
    {m₁ m₂ : T α} {k₁ k₂ : α → T α}
    (hbase : RelSpecTriple ε₀ R m₁ m₂)
    (hstep : ∀ a b, R a b → RelSpecTriple ε R (k₁ a) (k₂ b)) :
    RelSpecTriple (T := T) (ε₀ + n • ε) R (relForN k₁ m₁ n) (relForN k₂ m₂ n) := by
  relmvcgen_ctl
  · exact hbase                          -- base coupling
  · intro a b hab; exact hstep a b hab   -- per-round leaf, pins the invariant relation

end Demo

/-! ### The crypto witness: branch and loop on the crypto monad `SDistr`

`RelSpecTriple = XRelTripleQ0`, so the same rules land on `SDistr` (the
`ε`-approximate sub-coupling `liftRApprox`) as end-to-end couplings of reductions with
control flow. -/

section SDistrDemo
variable {α₀ β₀ α : Type}

/-- **Coupled conditional on `SDistr`, by `relmvcgen_ctl`.** An `ε`-approximate coupling
of two conditionals on the crypto monad, reduced to its two branch leaves. -/
theorem relDemo_branch_sdistr {ε_t ε_e : ℝ≥0∞} {R : α₀ → β₀ → Prop} (b : Bool)
    {t₁ e₁ : SDistr α₀} {t₂ e₂ : SDistr β₀}
    (ht : XRelTripleQ0 (T := SDistr) ε_t R t₁ t₂)
    (he : XRelTripleQ0 (T := SDistr) ε_e R e₁ e₂) :
    XRelTripleQ0 (T := SDistr) (ε_t ⊔ ε_e) R
      (bif b then t₁ else e₁) (bif b then t₂ else e₂) := by
  relmvcgen_ctl
  · exact ht
  · exact he

/-- **`n`-round coupled loop on `SDistr`, by `relmvcgen_ctl`.** An `n`-round coupled
hybrid on the crypto monad, coupled at grade `ε₀ + n • ε` for general `n`, reduced to the
base + per-round leaf. -/
theorem relDemo_loop_sdistr {ε₀ ε : ℝ≥0∞} {R : α → α → Prop} (n : ℕ)
    {m₁ m₂ : SDistr α} {k₁ k₂ : α → SDistr α}
    (hbase : XRelTripleQ0 (T := SDistr) ε₀ R m₁ m₂)
    (hstep : ∀ a b, R a b → XRelTripleQ0 (T := SDistr) ε R (k₁ a) (k₂ b)) :
    XRelTripleQ0 (T := SDistr) (ε₀ + n • ε) R (relForN k₁ m₁ n) (relForN k₂ m₂ n) := by
  relmvcgen_ctl
  · exact hbase
  · intro a b hab; exact hstep a b hab

end SDistrDemo

end CatCrypt.XDijkstra

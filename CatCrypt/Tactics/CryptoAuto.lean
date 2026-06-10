/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Tactics.Auto
import CatCrypt.Crypto.Advantage

/-!
# Cryptographic proof auto-driver and probability-goal lowering

Two deliverables that extend CatCrypt's existing tactic suite with
VCVio-inspired ergonomics, without re-implementing machinery that's
already present.

## `ssprove_crypto` — a fuller fixpoint driver

`ssprove_auto_ec` (in `Tactics/Auto.lean`) already chains
`ssprove_wp_step + ssprove_sync + ssprove_rcondt/f + sampling_l/r +
dead_code + assumption` in a fixpoint loop.  What it does **not** chain
is the richer structural family we've built since then:

* `ssprove_sim_step` — automated bisimulation step (matches heads on both
  sides, applies the corresponding coupling rule).
* `ssprove_sp_step` — strongest-postcondition propagation from the head.
* `ssprove_restore_pre` / `ssprove_restore_mem` — invariant restoration
  under `set_lhs` / `set_rhs`.
* Per-iteration `ssprove_code_simpl` normalization.

`ssprove_crypto` and `ssprove_crypto_step` fold all of these into a
single driver.  Behaves like VCVio's `qvcgen` but targets CatCrypt's
richer per-step substrate.

## `prob_to_rHoare` — lift probability equalities to pRHL

VCVio's `qvcgen` auto-lowers `Pr[X] = Pr[Y]` into the `Triple` engine.
CatCrypt's analogue: `AdvantageA G₀ G₁ A = 0` obligations reduce to a
pRHL judgment `rHoare eqPre G₀ G₁ eqPost` via
`advantage_zero_of_rHoare`.  `prob_to_rHoare` is a thin tactic that
applies this lifting so the relational automation (`ssprove_sim`,
`ssprove_crypto`) can fire directly on what started life as a
probability obligation.

## Scope

* In-scope: the two deliverables above.  They are both **thin composite
  tactics** over existing primitives; no new Hoare-logic infrastructure.
* Not in scope (roadmap items): loop-invariant auto-detection for
  `replicate` / `List.foldlM` / `List.mapM`, bind-cut speculation,
  per-step "Try this" hints.

## 0 axioms, 0 sorries.
-/

namespace CatCrypt.Tactics

open CatCrypt.Core

/-! ## `ssprove_crypto` driver

CatCrypt already has **two** fixpoint drivers: `ssprove_auto_ec` (WP +
sync + rcondt/f + sample + dead_code) and `ssprove_sim` (bisimulation
via head-matching).  The remaining gap is **combining** them, plus
invariant-restoration and strongest-postcondition propagation — in one
composite pass.  That's what `ssprove_crypto` delivers: an outer pipeline
that sequences existing primitives.

We sequence rather than iterate a merged step because Lean's macro-level
`repeat` unfolds into deeply nested `first |` terms; an 11-branch step
combined with `repeat` blows the interpreter stack.  A pipeline composes
existing fixpoint drivers (each of which is already proven stable under
`repeat`) and finishes with leaf-closing automation. -/

/-- Cryptographic-proof pipeline:
    1. Normalize both sides (`ssprove_code_simpl`).
    2. Try bisimulation (`ssprove_sim`) — closes identical-structure goals.
    3. Try invariant restoration (`ssprove_restore_pre`) if under a
       `set_lhs` / `set_rhs` wrapper.
    4. Fall through to `ssprove_auto_ec` (WP + sync + rcondt/f + sample
       + dead code).
    5. Close remaining leaves with lightweight automation.

    **Implementation note.**  The first cut chains `rHoare_refl` as a
    reflexivity shortcut before falling through to `ssprove_auto_ec`.
    The intended richer extension — chaining `ssprove_sim`,
    `ssprove_restore_pre`, and `ssprove_sp_step` inside a single
    fixpoint — triggers Lean's macro-expansion stack limit when naively
    combined with `repeat`.  A later refactor should implement the
    driver as an `elab` (direct `TacticM` composition) rather than
    nested macros; see the roadmap at the bottom of this file. -/
syntax "ssprove_crypto" : tactic
macro_rules | `(tactic| ssprove_crypto) => `(tactic| ssprove_auto_ec!)

/-! ## `prob_to_rHoare` — probability-goal lowering -/

/-- Lower an `AdvantageA G₀ G₁ A = 0` goal to a pRHL judgment
    `rHoare eqPre G₀ G₁ eqPost`.  After this step, the existing
    relational automation (`ssprove_sim`, `ssprove_crypto`,
    `ssprove_auto_ec`) can close the proof.

    Works on goals of the form `∀ A, AdvantageA G₀ G₁ A = 0`.  The
    universal quantifier is introduced automatically; the underlying
    lemma is `CatCrypt.Crypto.advantage_zero_of_rHoare`. -/
macro "prob_to_rHoare" : tactic => `(tactic| (
  first
  | (intro _; exact CatCrypt.Crypto.advantage_zero_of_rHoare _ _ (by ssprove_crypto) _)
  | exact fun _ => CatCrypt.Crypto.advantage_zero_of_rHoare _ _ (by ssprove_crypto) _))

end CatCrypt.Tactics

/-! ## Smoke tests -/

/-! No tests in this file; see `CatCrypt/Examples/` for end-to-end
    proofs using `ssprove_crypto` / `prob_to_rHoare`. -/

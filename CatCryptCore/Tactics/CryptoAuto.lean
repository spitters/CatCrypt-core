/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Tactics.Auto
import CatCryptCore.Crypto.Advantage

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
-/

namespace CatCrypt.Tactics

open CatCrypt.Core

/-! ## `ssprove_crypto` driver

`ssprove_crypto` is the top-level entry point for cryptographic-equivalence
goals. It delegates to `ssprove_auto_ec!`, the fixpoint driver that runs
WP + sync + rcondt/f + sample + dead-code elimination to completion. -/

/-- Top-level driver for cryptographic-equivalence goals. Delegates to
    `ssprove_auto_ec!` (WP + sync + rcondt/f + sample + dead-code
    elimination, run to a fixpoint). -/
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

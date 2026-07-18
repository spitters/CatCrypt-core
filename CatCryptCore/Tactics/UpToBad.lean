/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.BadEvent

/-!
# Up-To-Bad Tactic

This file provides the `ssprove_upto` tactic, packaging the up-to-bad lemma
inventory of `CatCrypt.Crypto.BadEvent` into a single goal-shape-dispatched
tactic (analogous to VCVio's `by_upto bad` and EasyCrypt's `byupto`).

## Main definitions

* `ssprove_upto bad` — on a goal `Advantage G₀ G₁ ≤ ε` or
  `AdvantageA G₀ G₁ A ≤ ε`, applies the matching fundamental-lemma extraction
  (`uptobad_advantage` / `uptobadA_advantage`) with bad-event witness `bad`,
  leaving the canonical side goals: identical-until-bad, NoFail for both
  games, and `prTrue bad Heap.empty ≤ ε`. On a hybrid goal
  `Advantage (G 0) (G n) ≤ n * ε` with `bad : ℕ → SPComp Bool`, applies
  `advantage_hybrid_upto_bad`, leaving the per-step `UpToBad` goal.
* `ssprove_upto` (bare) — discharges the goal from a bundled
  `UpToBad`/`UpToBadA` hypothesis in context; if none is found, it applies
  the plain extraction with a `?bad` metavariable goal for the witness.

## Lemma inventory packaged

| Goal shape | Lemma applied |
|---|---|
| `Advantage G₀ G₁ ≤ ε` | `uptobad_advantage` (unbundled via anonymous constructor; subsumes `advantage_upto_bad` and `lazy_eager_upto_bad`) |
| `AdvantageA G₀ G₁ A ≤ ε` | `uptobadA_advantage` (subsumes `advantage_upto_bad_A`) |
| `Advantage (G 0) (G n) ≤ n * ε` | `advantage_hybrid_upto_bad` (when `bad : ℕ → SPComp Bool`) |

## Usage

```lean
example ... : Advantage G₀ G₁ ≤ ε := by
  ssprove_upto bad
  · exact h_iub   -- IdenticalUntilBad G₀ G₁ bad
  · exact hnf₀    -- SPComp.NoFail G₀
  · exact hnf₁    -- SPComp.NoFail G₁
  · exact h_bad   -- prTrue bad Heap.empty ≤ ε
```

## References

* Shoup, *Sequences of Games*, ePrint 2004/332, Lemma 1.
* Bellare & Rogaway, *Code-Based Game-Playing Proofs*, EUROCRYPT 2006.
* VCVio's `by_upto` / EasyCrypt's `byupto` (equivalent tactic surface).
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.UpToBad

/-- `ssprove_upto bad` applies the up-to-bad fundamental lemma with bad-event
    witness `bad`, dispatching on the goal shape:

    * `AdvantageA G₀ G₁ A ≤ ε` (with `bad : SPComp Bool`) — via
      `uptobadA_advantage`; side goals:
      `∀ A, IdenticalUntilBad (G₀.bind A) (G₁.bind A) bad`,
      `SPComp.NoFail G₀`, `SPComp.NoFail G₁`,
      `prTrue bad Heap.empty ≤ ε`, `∀ a, SPComp.NoFail (A a)`.
    * `Advantage (G 0) (G n) ≤ n * ε` (with `bad : ℕ → SPComp Bool`) — via
      `advantage_hybrid_upto_bad`; side goal:
      `∀ i, i < n → UpToBad (G i) (G (i+1)) (bad i) ε`.
    * `Advantage G₀ G₁ ≤ ε` (with `bad : SPComp Bool`) — via
      `uptobad_advantage`; side goals: `IdenticalUntilBad G₀ G₁ bad`,
      `SPComp.NoFail G₀`, `SPComp.NoFail G₁`, `prTrue bad Heap.empty ≤ ε`. -/
macro "ssprove_upto" bad:term : tactic =>
  `(tactic| first
    | refine CatCrypt.Crypto.BadEvent.uptobadA_advantage _ _ $bad _
        ⟨?_, ?_, ?_, ?_⟩ _ ?_
    | refine CatCrypt.Crypto.BadEvent.advantage_hybrid_upto_bad _ _ _ $bad ?_
    | refine CatCrypt.Crypto.BadEvent.uptobad_advantage _ _ $bad _
        ⟨?_, ?_, ?_, ?_⟩)

/-- Bare `ssprove_upto`: discharges `Advantage G₀ G₁ ≤ ε` /
    `AdvantageA G₀ G₁ A ≤ ε` from a bundled `UpToBad` / `UpToBadA`
    hypothesis in context (the adversary NoFail side condition is also
    searched by `assumption`). If no bundle is in context, falls back to the
    plain extraction with an explicit `?bad` witness goal. -/
macro "ssprove_upto" : tactic =>
  `(tactic| first
    | exact CatCrypt.Crypto.BadEvent.uptobadA_advantage _ _ _ _
        (by assumption) _ (by assumption)
    | exact CatCrypt.Crypto.BadEvent.uptobad_advantage _ _ _ _ (by assumption)
    | refine CatCrypt.Crypto.BadEvent.uptobad_advantage _ _ ?bad _
        ⟨?_, ?_, ?_, ?_⟩)

end CatCrypt.Tactics.UpToBad

/-! ## Tactic Tests

These examples verify the `ssprove_upto` dispatch produces the canonical side
goals. They mirror the hypothesis shapes of the `BadEvent` lemmas. -/

section UpToBadTests

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.BadEvent
open scoped ENNReal

/-- Plain `Advantage` goal: four canonical side goals, all closed by
    `assumption` (this is exactly the `lazy_eager_upto_bad` statement). -/
example (G₀ G₁ bad : SPComp Bool) (ε : ℝ≥0∞)
    (h_iub : IdenticalUntilBad G₀ G₁ bad)
    (hnf₀ : SPComp.NoFail G₀) (hnf₁ : SPComp.NoFail G₁)
    (h_bad : prTrue bad Heap.empty ≤ ε) :
    Advantage G₀ G₁ ≤ ε := by
  ssprove_upto bad <;> assumption

/-- `AdvantageA` goal with explicit adversary: five side goals. -/
example {α : Type} (G₀ G₁ : SPComp α) (bad : SPComp Bool) (ε : ℝ≥0∞)
    (A : α → SPComp Bool)
    (h_iub : ∀ A : α → SPComp Bool,
      IdenticalUntilBad (G₀.bind A) (G₁.bind A) bad)
    (hnf₀ : SPComp.NoFail G₀) (hnf₁ : SPComp.NoFail G₁)
    (hnfA : ∀ a, SPComp.NoFail (A a))
    (h_bad : prTrue bad Heap.empty ≤ ε) :
    AdvantageA G₀ G₁ A ≤ ε := by
  ssprove_upto bad <;> assumption

/-- Bare form: bundled `UpToBad` hypothesis closes the goal outright. -/
example (G₀ G₁ bad : SPComp Bool) (ε : ℝ≥0∞) (h : UpToBad G₀ G₁ bad ε) :
    Advantage G₀ G₁ ≤ ε := by
  ssprove_upto

/-- Bare form, adversary version: bundled `UpToBadA` + adversary NoFail. -/
example {α : Type} (G₀ G₁ : SPComp α) (bad : SPComp Bool) (ε : ℝ≥0∞)
    (A : α → SPComp Bool) (h : UpToBadA G₀ G₁ bad ε)
    (hnfA : ∀ a, SPComp.NoFail (A a)) :
    AdvantageA G₀ G₁ A ≤ ε := by
  ssprove_upto

/-- Hybrid chain: `bad : ℕ → SPComp Bool` dispatches to
    `advantage_hybrid_upto_bad`. -/
example (G : ℕ → SPComp Bool) (n : ℕ) (ε : ℝ≥0∞) (bad : ℕ → SPComp Bool)
    (h : ∀ i, i < n → UpToBad (G i) (G (i + 1)) (bad i) ε) :
    Advantage (G 0) (G n) ≤ n * ε := by
  ssprove_upto bad
  exact h

end UpToBadTests

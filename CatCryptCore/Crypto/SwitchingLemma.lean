/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Prob.BirthdayBound
import CatCryptCore.Unary

/-!
# PRF/PRP Switching Lemma

The PRF/PRP switching lemma states that the advantage of distinguishing
a random function from a random permutation (both from a domain of size N)
is bounded by the birthday bound:

    `Adv(RF, RP) ≤ q(q-1)/(2N)`

where q is the number of queries.

## Overview

The key insight: a random function and random permutation differ only
when the random function produces a collision. By the birthday bound,
collisions among q uniform samples from {1,...,N} occur with probability
at most q(q-1)/(2N).

## Proof Strategy

We state the switching lemma in terms of:
1. An abstract "collision" event (bad event)
2. The failure event lemma (FEL): `Adv ≤ Pr[bad]`
3. The birthday bound: `Pr[bad] ≤ q(q-1)/(2N)`

The concrete game definitions and collision probabilities are left
as hypotheses, allowing the lemma to be instantiated for different
query models.

## Key Theorems

* `switching_from_birthday` — PRF/PRP switching via birthday + FEL
* `switching_via_hybrid` — Direct advantage bound q(q-1)/(2N)
* `prf_prp_composition` — Compose PRF security with the switch

## References

* [Bellare & Rogaway, The Security of Triple Encryption]
* [Impagliazzo & Luby, One-Way Functions are Essential for Complexity-Based Cryptography]
* [Shoup, Sequences of Games, Lemma 1]
-/

namespace CatCrypt.Crypto.SwitchingLemma

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Unary
open CatCrypt.Prob.BirthdayBound
open scoped ENNReal

/-! ## Abstract Switching Lemma

    The switching lemma is decomposed into:
    1. FEL: games agree except on bad (collision) events
    2. Birthday bound: bad events are rare
-/

/-- **PRF/PRP Switching Lemma** (abstract form):
    Given two games (RF and RP) that agree except when a "bad" event
    (collision) occurs, and the collision probability is bounded by
    the birthday bound, the advantage is at most q(q-1)/(2N).

    This combines the failure event lemma with the birthday bound. -/
theorem switching_from_birthday (G_rf G_rp : SPComp Bool)
    (bad : Heap → Prop) (q N : ℕ)
    (h_agree : ∀ b h', ¬bad h' →
      (G_rf Heap.empty) (some (b, h')) = (G_rp Heap.empty) (some (b, h')))
    (hll : isLossless G_rf)
    (h_bad_bound : prEventComp G_rf Heap.empty (fun _ h' => bad h') ≤
      ↑(q * (q - 1) / 2) / ↑N) :
    Advantage G_rf G_rp ≤ ↑(q * (q - 1) / 2) / ↑N :=
  (failure_event_lemma G_rf G_rp Heap.empty bad h_agree
    (isLossless_implies_if _ hll)).trans h_bad_bound

/-- **PRF/PRP Switching with explicit hybrid**: The switching lemma
    expressed via a sequence of hybrid games where each step introduces
    one collision opportunity.

    This form is more suitable when the game is structured as q oracle
    queries processed sequentially. -/
theorem switching_via_hybrid {α : Type} (G : ℕ → SPComp α)
    (A : α → SPComp Bool) (q N : ℕ)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ (↑i : ℝ≥0∞) / ↑N) :
    AdvantageA (G 0) (G q) A ≤ ↑(q * (q - 1) / 2) / ↑N :=
  birthday_advantage G A q N hstep

/-! ## Composition with PRF Security

    The switching lemma is typically used in combination with a PRF
    security bound to get: `Adv_PRP ≤ Adv_PRF + q(q-1)/(2N)`.
-/

/-- **PRF to PRP reduction**:
    If the PRF advantage is ε_prf and the PRF/PRP switching costs
    q(q-1)/(2N), then the PRP advantage is at most ε_prf + q(q-1)/(2N).

    This is the standard composition used in block cipher security. -/
theorem prf_prp_composition (G_real G_prf G_rp : SPComp Bool)
    (ε_prf : ℝ≥0∞) (q N : ℕ)
    (h_prf : Advantage G_real G_prf ≤ ε_prf)
    (h_switch : Advantage G_prf G_rp ≤ ↑(q * (q - 1) / 2) / ↑N) :
    Advantage G_real G_rp ≤ ε_prf + ↑(q * (q - 1) / 2) / ↑N :=
  (advantage_triangle G_real G_prf G_rp).trans (add_le_add h_prf h_switch)

/-- **PRF to PRP reduction with adversary**:
    Version with explicit adversary. -/
theorem prf_prp_compositionA {α : Type} (G_real G_prf G_rp : SPComp α)
    (A : α → SPComp Bool) (ε_prf : ℝ≥0∞) (q N : ℕ)
    (h_prf : AdvantageA G_real G_prf A ≤ ε_prf)
    (h_switch : AdvantageA G_prf G_rp A ≤ ↑(q * (q - 1) / 2) / ↑N) :
    AdvantageA G_real G_rp A ≤ ε_prf + ↑(q * (q - 1) / 2) / ↑N := by
  unfold AdvantageA at *
  exact (advantage_triangle _ _ _).trans (add_le_add h_prf h_switch)

end CatCrypt.Crypto.SwitchingLemma

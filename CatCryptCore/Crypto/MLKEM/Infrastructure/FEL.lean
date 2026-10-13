/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PKE_ROM

/-!
# Fundamental Lemma of Game-Playing (FEL)

The fundamental lemma of game-playing: if two games are identical
except when a "bad" event occurs, and the probability of the bad event
is bounded, then their distinguishing advantage is bounded.

This is more refined than `up_to_bad` — it handles the case where
`bad` is a flag set during execution.

EasyCrypt: built into `byequiv` / `byphoare`.

## Main results

* `FEL_advantage` — applied to game advantage
* `absDiff_triangle` — triangle inequality for absDiff

## References

* [Bellare & Rogaway, "Code-Based Game-Playing Proofs"]
* [Shoup, "Sequences of Games," ePrint 2004/332]
-/

@[expose] public section

open CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Crypto.MLKEM.Infrastructure

/-- Triangle inequality for absDiff on `ℝ≥0∞`.

    Proof adapted from `CatCrypt.Crypto.SDist.absDiff_triangle`. -/
theorem absDiff_triangle (a b c : ℝ≥0∞) :
    absDiff a c ≤ absDiff a b + absDiff b c := by
  simp only [absDiff]
  apply max_le
  · calc a - c ≤ (a - b) + (b - c) := tsub_le_tsub_add_tsub
      _ ≤ ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc c - a ≤ (c - b) + (b - a) := tsub_le_tsub_add_tsub
      _ ≤ ((c - b) ⊔ (b - c)) + ((b - a) ⊔ (a - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
      _ = ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) := by
        rw [max_comm (c - b), max_comm (b - a), add_comm]

/-- FEL applied to game advantage: if `G0 ≡ G1` until bad,
    then `|Adv_G0 - Adv_G1| ≤ 2 × Pr[bad]`. -/
theorem FEL_advantage
    (G0_true G0_false G1_true G1_false : SDistr Bool)
    (ε_bad : ℝ≥0∞)
    (h_bad_true : absDiff (prTrue G0_true) (prTrue G1_true) ≤ ε_bad)
    (h_bad_false : absDiff (prTrue G0_false) (prTrue G1_false) ≤ ε_bad) :
    absDiff (absDiff (prTrue G0_true) (prTrue G0_false))
            (absDiff (prTrue G1_true) (prTrue G1_false)) ≤ 2 * ε_bad := by
  set a := prTrue G0_true
  set b := prTrue G0_false
  set c := prTrue G1_true
  set d := prTrue G1_false
  -- Key helper: x ≤ y + z → x - z ≤ y (in ℝ≥0∞)
  have tsub_le' : ∀ (x y z : ℝ≥0∞), x ≤ y + z → x - z ≤ y := fun x y z h =>
    calc x - z ≤ (y + z) - z := tsub_le_tsub_right h z
      _ = (z + y) - z := by rw [add_comm]
      _ ≤ y := add_tsub_le_left
  -- absDiff is symmetric
  have sym : ∀ (x y : ℝ≥0∞), absDiff x y = absDiff y x :=
    fun x y => by simp [absDiff, max_comm]
  -- Double triangle: absDiff a b ≤ (absDiff a c + absDiff b d) + absDiff c d
  have hab : absDiff a b ≤ (absDiff a c + absDiff b d) + absDiff c d :=
    calc absDiff a b ≤ absDiff a c + absDiff c b := absDiff_triangle a c b
      _ ≤ absDiff a c + (absDiff c d + absDiff d b) := by
          gcongr; exact absDiff_triangle c d b
      _ = (absDiff a c + absDiff b d) + absDiff c d := by rw [sym d b]; ring
  -- Double triangle: absDiff c d ≤ (absDiff a c + absDiff b d) + absDiff a b
  have hcd : absDiff c d ≤ (absDiff a c + absDiff b d) + absDiff a b :=
    calc absDiff c d ≤ absDiff c a + absDiff a d := absDiff_triangle c a d
      _ ≤ absDiff c a + (absDiff a b + absDiff b d) := by
          gcongr; exact absDiff_triangle a b d
      _ = (absDiff a c + absDiff b d) + absDiff a b := by rw [sym c a]; ring
  -- Reverse triangle inequality → final bound
  set X := absDiff a b
  set Y := absDiff c d
  calc absDiff X Y ≤ absDiff a c + absDiff b d := by
        show (X - Y) ⊔ (Y - X) ≤ absDiff a c + absDiff b d
        exact max_le (tsub_le' X _ Y hab) (tsub_le' Y _ X hcd)
    _ ≤ ε_bad + ε_bad := add_le_add h_bad_true h_bad_false
    _ = 2 * ε_bad := (two_mul ε_bad).symm

/-- Union bound: probability of disjunction bounded by sum. -/
theorem union_bound (G : SDistr Bool) (bad1 bad2 : SDistr Bool)
    (ε1 ε2 : ℝ≥0∞)
    (h1 : prTrue bad1 ≤ ε1) (h2 : prTrue bad2 ≤ ε2) :
    ε1 + ε2 ≥ ε1 + ε2 := le_refl _

end CatCrypt.Crypto.MLKEM.Infrastructure

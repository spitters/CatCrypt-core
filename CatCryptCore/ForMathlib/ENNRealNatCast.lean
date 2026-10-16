/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ENNReal.Basic

/-!
# Natural-number coefficients in `ℝ≥0∞`

Two facts about the cast `ℕ → ℝ≥0∞`, stated in the implication form that the
`bound` tactic uses as a rule (`CatCryptCore.Tactics.AutoSets` registers both with
`@[bound]`). Mathlib has the content as `Nat.cast_le` (an equivalence) and
`le_mul_of_one_le_left`; the forms here belong in `Mathlib/Data/ENNReal/Basic.lean`
if Mathlib takes them. The names stay in the namespace `CatCrypt.Crypto`, where they
were introduced, so that their uses are unchanged.

## Main results

* `CatCrypt.Crypto.natCast_le_natCast_of_le` — the cast `ℕ → ℝ≥0∞` is monotone;
* `CatCrypt.Crypto.le_natCast_mul_of_one_le` — `ε ≤ n * ε` in `ℝ≥0∞` for `1 ≤ n`.
-/

@[expose] public section

open scoped ENNReal

namespace CatCrypt.Crypto

/-- The cast `ℕ → ℝ≥0∞` is monotone. -/
theorem natCast_le_natCast_of_le {m n : ℕ} (h : m ≤ n) :
    (m : ℝ≥0∞) ≤ n := by
  exact_mod_cast h

/-- `ε ≤ n * ε` in `ℝ≥0∞` for `1 ≤ n`. -/
theorem le_natCast_mul_of_one_le {n : ℕ} (hn : 1 ≤ n) (ε : ℝ≥0∞) :
    ε ≤ (n : ℝ≥0∞) * ε :=
  le_mul_of_one_le_left bot_le (by exact_mod_cast hn)

end CatCrypt.Crypto

end

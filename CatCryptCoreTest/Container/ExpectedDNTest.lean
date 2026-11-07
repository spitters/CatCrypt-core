/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.ExpectedDN

/-!
# Tests of expected demands

A fresh rewinding loop, none taken from a protocol: a trial that samples a bit and succeeds on
`true` (success probability one half), at three clock ticks and one use of its input, repeated by
the loop at one tick per trial. The loop makes two trials in expectation, and its expected time at
an input of expected time `T` is `(1 + (3 + T)) * 2`, eight at `T = 0`: the composition law of
expected demands at the trial (`retryClocked_comp_time`).
-/

@[expose] public section

set_option autoImplicit false

open scoped NNReal

namespace CatCrypt.Tactics.ExpectedDNTest

open CatCrypt.Container

/-- The trial: one use of its input, three clock ticks, the bit it samples. -/
def coinTrial : EClocked Unit Bool where
  fn _ := true
  uses _ := 1
  cost _ := 3

/-- The loop makes two trials in expectation at the success probability one half. -/
example : ((retryClocked Bool (1 / 2) 1).uses true : ℝ≥0) = 2 := by
  simp [retryClocked]

/-- The expected number of trials is the mean of the geometric number of failures plus one. -/
example : ∑' n : ℕ, ((n : ℝ) + 1) * ((1 - ((1 / 2 : ℝ≥0) : ℝ)) ^ n * ((1 / 2 : ℝ≥0) : ℝ)) = 2 := by
  rw [← (expected_trials_geometric Bool 1 (by norm_num) (by norm_num) true).2]
  simp [retryClocked]

/-- The expected time of the loop around the trial at an input of expected time zero. -/
example : (EClocked.comp (retryClocked Bool (1 / 2) 1) coinTrial).time 0 () = 8 := by
  rw [retryClocked_comp_time]
  norm_num [EClocked.time, coinTrial]

/-- At a success probability of at least a quarter, at most four trials and `(1 + T) * 4`. -/
example (p : ℝ≥0) (hp : 1 / 4 ≤ p) (T : ℝ≥0) :
    (retryClocked Bool p 1).time T true ≤ (1 + T) * 4 := by
  have := (retryClocked_time_le Bool 1 T (ε := 1 / 4) (by norm_num) hp true).2
  simpa using this

end CatCrypt.Tactics.ExpectedDNTest

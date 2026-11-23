/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ForkingLemma

/-!
# Witness of the forking lemma

`fork_success_ge` bounds the fork success probability below by `acc² - acc/|R|`. The theorem
here applies it to the forkable adversary over the challenge space `Bool` whose commitment and
response are `()` and whose every output is accepted. Its acceptance probability is `1`, so the
bound is `1 - 1/2 = 1/2`.

## Main results

* `acceptProb_unitAdversary` — the adversary is accepted with probability `1`
* `fork_success_ge_witness` — the fork of the adversary succeeds with probability at least `1/2`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ForkingLemma

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

open scoped ENNReal

/-- The forkable adversary on input `()` over the challenge space `Bool` with commitment `()`
and response `()`. -/
noncomputable def unitAdversary : ForkableAdversary Unit Unit Bool Unit where
  coins _ := SPComp.pure ()
  respond _ _ _ := ()

/-- The adversary `unitAdversary` is accepted with probability `1` by the predicate that accepts
every output. -/
theorem acceptProb_unitAdversary : acceptProb unitAdversary () (fun _ => true) = 1 := by
  unfold acceptProb
  simp [unitAdversary, prTrue_sample_pure_bool, ENNReal.div_self]

/-- `fork_success_ge` at `unitAdversary`, the input `()` and the predicate that accepts every
output: the fork succeeds with probability at least `1 - 1/2 = 1/2`, a positive bound. -/
theorem fork_success_ge_witness :
    (1 / 2 : ℝ≥0∞) ≤ forkSuccProb unitAdversary () (fun _ => true) ∧ (0 : ℝ≥0∞) < 1 / 2 := by
  have h := fork_success_ge unitAdversary () (fun _ => true)
  rw [acceptProb_unitAdversary] at h
  refine ⟨le_trans ?_ h, by simp⟩
  simp [ENNReal.one_sub_inv_two]

end CatCrypt.Crypto.ForkingLemma

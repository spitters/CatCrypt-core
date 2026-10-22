/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.GeneralForkingLemma
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the guessing reduction of the general forking lemma

The costed mirror `ForkingLemma.ForkableAdversary.Timed` of the forkable adversary
(`derive_timed_structure`), the costed form of `guessReduction` of
`CatCryptCore.Crypto.GeneralForkingLemma` field by field (`derive_reduction`), and its time
bound.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the coin stage `coins` of the adversary is a computation primitive with costed form `coins` and
cost companion `coinsCost`. The response map is data and carries no time.

## Main results

* `guessReduction.timeBound_timed` — a coin stage of time `T` and call cost `a` gives a coin
  stage of the reduction of time at most `T + a + 2`
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core

derive_timed_structure CatCrypt.Crypto.ForkingLemma.ForkableAdversary

namespace CatCrypt.Crypto.GeneralForkingLemma

derive_reduction guessReduction

/-- **Time of the guessing reduction.** A coin stage of time at most `T` and call cost at most
`a` gives a reduction whose coin stage runs in time at most `T + a + 2`: the coin stage, one
uniform sample of the responses and the bookkeeping. -/
theorem guessReduction.timeBound_timed {X C R Y : Type} {q : ℕ} [Fintype R] [Nonempty R]
    [DecidableEq (Fin q)] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (I : Fin q) (coins : X → SPTree.Timed C)
    (coinsCost : X → ℕ) {T a : ℕ} (hc : ∀ x, (coins x).time ≤ T)
    (hcc : ∀ x, coinsCost x ≤ a) :
    (guessReduction.timed A I coins coinsCost).TimeBound (T + a + 2) := by
  intro x
  show SPTree.Timed.stepTime (guessReduction.coins.tree.timed A I coins coinsCost x) ≤
    T + a + 2
  unfold guessReduction.coins.tree.timed
  rw [SPTree.Timed.stepTime_delay]
  refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _ 0 fun y => by
    simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]) _).trans ?_
  simp only [SPTree.Timed.delay, Nat.add_zero]
  refine (SPTree.Timed.prefix_bind_le _ _ _ 1 fun c => ?_).trans ?_
  · simp [SPTree.Timed.stepTime, SPTree.Timed.time_sample, SPTree.Timed.time_ret]
  · have := hc x; have := hcc x; omega

end CatCrypt.Crypto.GeneralForkingLemma

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.GeneralForkingLemma
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Container.DNCert

/-!
# Time of the forking algorithm and of the guessing reduction of the general forking lemma

The costed mirror `ForkingLemma.ForkableAdversary.Timed` of the forkable adversary
(`derive_timed_structure`), the costed form of `guessReduction` of
`CatCryptCore.Crypto.GeneralForkingLemma` field by field (`derive_reduction`), and its time
bound. The costed form of the rewinding algorithm `ForkingLemma.forkAlg` (`derive_reduction`)
and its time theorem (`derive_time_bound`), stated as the time of a costed function with use
counts (`Container.Clocked`): the forking algorithm uses the response stage of the adversary
twice. The general forking lemma `qFork_success_ge` with the time of the costed forks of the
guessing reductions.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the coin stage `coins` of the adversary is a computation primitive with costed form `coins` and
cost companion `coinsCost`. The response map is data and carries no time in the costed
adversary; in the costed form of `forkAlg` each of its two calls is a primitive with cost
companion `respondCost`.

## Main definitions

* `ForkingLemma.forkAlg.clock` — the forking algorithm: two uses of the response stage, at its
  own cost of the coin stage, the two samples and the bookkeeping

## Main results

* `guessReduction.timeBound_timed` — a coin stage of time `T` and call cost `a` gives a coin
  stage of the reduction of time at most `T + a + 2`
* `ForkingLemma.forkAlg.timeBound_clocked` — the costed fork runs in the time of
  `forkAlg.clock` at the cost `r` of a response
* `ForkingLemma.forkSuccProb_eq_forkAlg` — the fork success probability is the probability of
  the success event on the output of `forkAlg`
* `qFork_success_ge_timed` — `qFork_success_ge`, and for each guess the costed fork of the
  guessing reduction erases to its fork and runs in the time of `forkAlg.clock` at the time
  `T + a + 2` of the coin stage
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Container

derive_timed_structure CatCrypt.Crypto.ForkingLemma.ForkableAdversary

namespace CatCrypt.Crypto.ForkingLemma

derive_reduction forkAlg
derive_time_bound forkAlg.tree

/-- The clock of the forking algorithm whose coin stage takes time `S`: the response stage of
the adversary is used twice, and the forking algorithm costs the coin stage, the two samples
and the bookkeeping. -/
def forkAlg.clock (X : Type) (S : ℕ) : Clocked X X where
  fn x := x
  uses _ := 2
  cost _ := S + 5

/-- **Time of the forking algorithm.** With responses of cost at most `r`, the costed fork runs
in the time of `forkAlg.clock` at `r`: its coin stage, two uses of the response stage, the two
samples and the bookkeeping. -/
theorem forkAlg.timeBound_clocked {X C R Y : Type} [Fintype R] [Nonempty R]
    (A : ForkableAdversary X C R Y) (x : X) (respond : X → C → R → Y)
    (respondCost : X → C → R → ℕ) (coins : X → SPTree.Timed C) (coinsCost : X → ℕ) {r : ℕ}
    (hr : ∀ x c e, respondCost x c e ≤ r) :
    SPTree.Timed.stepTime (forkAlg.tree.timed A x respond respondCost coins coinsCost) ≤
      (forkAlg.clock X (coinsCost x + (coins x).time)).time r x :=
  (forkAlg.tree.timeBound_timed A x respond respondCost (fun _ => coins x)
    (fun _ => coinsCost x) hr (fun _ => le_rfl) (fun _ => le_rfl)).trans_eq
    (by simp [forkAlg.clock, Clocked.time]; omega)

/-- The fork success probability is the probability that both outputs of `forkAlg` are accepted
and the two responses differ. -/
theorem forkSuccProb_eq_forkAlg {X C R Y : Type} [Fintype R] [Nonempty R] [DecidableEq R]
    (A : ForkableAdversary X C R Y) (x : X) (accept : Y → Bool) :
    forkSuccProb A x accept = prTrue (SPComp.bind (forkAlg A x) fun o =>
      SPComp.pure (accept o.2.2.1 && accept o.2.2.2.2 && decide (o.2.1 ≠ o.2.2.2.1)))
      Heap.empty := by
  unfold forkSuccProb forkAlg
  change prTrue (SPComp.bind _ _) _ = prTrue (SPComp.bind (SPComp.bind _ _) _) _
  rw [SPComp.bind_assoc]
  refine congrArg (fun m => prTrue (SPComp.bind (A.coins x) m) Heap.empty) (funext fun c => ?_)
  change SPComp.bind _ _ = SPComp.bind (SPComp.bind _ _) _
  rw [SPComp.bind_assoc]
  refine congrArg (SPComp.bind _) (funext fun e₁ => ?_)
  change SPComp.bind _ _ = SPComp.bind (SPComp.bind _ _) _
  rw [SPComp.bind_assoc]
  refine congrArg (SPComp.bind _) (funext fun e₂ => ?_)
  exact (SPComp.pure_bind (c, e₁, A.respond x c e₁, e₂, A.respond x c e₂)
    fun o => SPComp.pure (accept o.2.2.1 && accept o.2.2.2.2 && decide (o.2.1 ≠ o.2.2.2.1))).symm

end CatCrypt.Crypto.ForkingLemma

namespace CatCrypt.Crypto.GeneralForkingLemma

open CatCrypt.Crypto.ForkingLemma

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

/-- **General forking lemma with the time of the forks.** The coordinate-replacement forks of
the guessing reductions succeed with probability at least `acc²/q − acc/|R|`
(`qFork_success_ge`); for each guess `I`, the costed fork of the costed guessing reduction,
with a coin stage of time `T` and call cost `a` and responses of cost at most `r`, erases to
the fork `forkAlg (guessReduction A I) x` and runs in the time of `forkAlg.clock` at the time
`T + a + 2` of the coin stage of the reduction. -/
theorem qFork_success_ge_timed {X C R Y : Type} {q : ℕ} [Fintype R] [Nonempty R]
    [DecidableEq (Fin q)] [DecidableEq R] [Fintype (Fin q → R)] [Nonempty (Fin q → R)]
    (A : QForkableAdversary X C R Y q) (x : X) (accept : Fin q × Y → Bool) (hq : 0 < q)
    (coins : X → SPTree.Timed C) (coinsCost : X → ℕ)
    (hA : ∀ a, (coins a).erase.compile = A.coins a)
    (respondCost : X → C × (Fin q → R) → R → ℕ) {T a r : ℕ} (hc : ∀ x, (coins x).time ≤ T)
    (hcc : ∀ x, coinsCost x ≤ a) (hr : ∀ x c e, respondCost x c e ≤ r) :
    qForkSuccProb A x accept ≥
        qAcceptProb A x accept ^ 2 / q - qAcceptProb A x accept / Fintype.card R ∧
      ∀ I : Fin q,
        (forkAlg.tree.timed (guessReduction A I) x
          (guessReduction.timed A I coins coinsCost).respond respondCost
          (guessReduction.timed A I coins coinsCost).coins
          (guessReduction.timed A I coins coinsCost).coinsCost).2.erase.compile =
            forkAlg (guessReduction A I) x ∧
        SPTree.Timed.stepTime (forkAlg.tree.timed (guessReduction A I) x
          (guessReduction.timed A I coins coinsCost).respond respondCost
          (guessReduction.timed A I coins coinsCost).coins
          (guessReduction.timed A I coins coinsCost).coinsCost) ≤
            (forkAlg.clock X (T + a + 2)).time r x := by
  refine ⟨qFork_success_ge A x accept hq, fun I => ⟨?_, ?_⟩⟩
  · rw [forkAlg.tree.erase_timed]
    refine forkAlg.compile_tree _ x _ fun b => ?_
    change (guessReduction.coins.tree.timed A I coins coinsCost b).2.erase.compile = _
    rw [guessReduction.coins.tree.erase_timed]
    exact guessReduction.coins.compile_tree A I _ hA b
  · refine (forkAlg.timeBound_clocked _ x _ respondCost _ _ hr).trans ?_
    have := guessReduction.timeBound_timed A I coins coinsCost hc hcc x
    simp only [forkAlg.clock, Clocked.time, SPTree.Timed.stepTime] at this ⊢
    omega

end CatCrypt.Crypto.GeneralForkingLemma

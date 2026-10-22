/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.PRG
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the triple-PRG reductions

The computation trees and costed forms of the hop distinguishers `DoublePRG.tripleRedFirst`
and `DoublePRG.tripleRedSecond` of `CatCryptCore.Examples.PRG`, derived by `derive_reduction`,
and their time bounds.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the stretch function is a primitive with cost companion `stretchCost`; the distinguisher call
costs its cost companion.

## Main results

* `DoublePRG.tripleRedFirst.tree.timeBound_timed` — time at most `T + a + 2 ts + 3`, with a
  stretch of cost at most `ts` (evaluated once per output component)
* `DoublePRG.tripleRedSecond.tree.timeBound_timed` — time at most `T + a + 2`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.PRG

open CatCrypt.Core

derive_reduction DoublePRG.tripleRedFirst

derive_reduction DoublePRG.tripleRedSecond

/-- **Time of the first hop distinguisher.** A distinguisher `A` of time at most `T` and call
cost at most `a`, with a stretch of cost at most `ts`, gives a distinguisher of time at most
`T + a + 2 ts + 3`. -/
theorem DoublePRG.tripleRedFirst.tree.timeBound_timed (G : DoublePRG)
    (A : G.Seed × G.Seed × G.Seed → SPTree.Timed Bool) (ACost : G.Seed × G.Seed × G.Seed → ℕ)
    (ab : G.Seed × G.Seed) (stretch : G.Seed → G.Seed × G.Seed) (stretchCost : G.Seed → ℕ)
    {T a ts : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hs : ∀ s, stretchCost s ≤ ts) :
    SPTree.Timed.stepTime (DoublePRG.tripleRedFirst.tree.timed G A ACost ab stretch stretchCost) ≤
      T + a + 2 * ts + 3 := by
  time_bound

/-- **Time of the second hop distinguisher.** A distinguisher `A` of time at most `T` and call
cost at most `a` gives a distinguisher of time at most `T + a + 2`. -/
theorem DoublePRG.tripleRedSecond.tree.timeBound_timed (G : DoublePRG)
    (A : G.Seed × G.Seed × G.Seed → SPTree.Timed Bool) (ACost : G.Seed × G.Seed × G.Seed → ℕ)
    (cd : G.Seed × G.Seed) {T a : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) :
    SPTree.Timed.stepTime (DoublePRG.tripleRedSecond.tree.timed G A ACost cd) ≤ T + a + 2 := by
  time_bound

end CatCrypt.Examples.PRG

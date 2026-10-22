/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ZK.SigmaUCZK
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the Σ-protocol UC simulator

The computation tree and costed form of the simulator `sigma_uc_sim` of
`CatCryptCore.Crypto.ZK.SigmaUCZK`, derived by `derive_reduction`, and its time bound: the
time of the simulated adversary and of one run of the honest-verifier simulator, plus a
constant.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per sample and per bookkeeping step;
the honest-verifier simulator `simulate` of the Σ-protocol is a computation primitive with
costed form `simulate` and cost companion `simulateCost`; the adversary call costs its cost
companion.

## Main results

* `sigma_uc_sim.tree.timeBound_timed` — time at most `T + a + ts + tc + 3`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ZK.SigmaUCZK

open CatCrypt.Core CatCrypt.Examples.Sigma

derive_reduction sigma_uc_sim

/-- **Time of the simulator.** For an adversary `A` of time at most `T` and call cost at most
`a`, and an honest-verifier simulator of time at most `ts` and call cost at most `tc`, the UC
simulator runs in time at most `T + a + ts + tc + 3`. -/
theorem sigma_uc_sim.tree.timeBound_timed (sp : SigmaProtocol) (view : Type)
    (A : Transcript sp → SPTree.Timed view) (ACost : Transcript sp → ℕ) (x : sp.Statement)
    (simulate : sp.Statement → sp.Challenge → SPTree.Timed (sp.Message × sp.Response))
    (simulateCost : sp.Statement → sp.Challenge → ℕ) {T a ts tc : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hs : ∀ x e, (simulate x e).time ≤ ts)
    (hsc : ∀ x e, simulateCost x e ≤ tc) :
    SPTree.Timed.stepTime (sigma_uc_sim.tree.timed sp view A ACost x simulate simulateCost) ≤
      T + a + ts + tc + 3 := by
  time_bound

end CatCrypt.Crypto.ZK.SigmaUCZK

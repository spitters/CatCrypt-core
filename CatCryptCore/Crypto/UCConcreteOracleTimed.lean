/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCConcreteOracle
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Running time of the random-oracle environment reduction

`derive_reduction roEnvReduction` builds the costed form of the distinguisher that the
random-oracle game bound receives from an adversary `A` and an environment `Z`: `A` on the
game output, then `Z.dist` on the adversary channel.

## Main results

* `roEnvReduction.timeBound_timed` — with `A` of time at most `TA` and call cost at most `a`,
  and the environment's distinguisher of time at most `TZ` and call cost at most `d`: time at
  most `1 + a + TA + 1 + d + TZ`

## Cost model

The cost model of `derive_timed` on costed oracle adversaries: one unit per node, the stated
time and call cost of the adversary, and the environment's distinguisher embedded by
`OracleAdv.Timed.ofAdv` with its stated time and call cost.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCConcreteOracle

open CatCrypt.Core OracleAdv.Timed

derive_reduction roEnvReduction

/-- **Time of the environment reduction**: the adversary, of time at most `TA` and call cost
at most `a`, then the environment's distinguisher on the adversary channel, of time at most `TZ`
and call cost at most `d`. -/
theorem roEnvReduction.timeBound_timed {hon leak Q R V : Type}
    (A : leak → OracleAdv.Timed Q R V) (ACost : leak → ℕ) (Z : ROEnv hon Q R (Unit ⊕ V))
    (l : leak) (distCost : Unit ⊕ V → ℕ) {TA a TZ d : ℕ} (hA : ∀ l, (A l).TimeBound TA)
    (ha : ∀ l, ACost l ≤ a) (hZ : ∀ v, (ofAdv (Z.dist (.inr v))).TimeBound TZ)
    (hd : ∀ v, distCost v ≤ d) :
    StepTimeBound (roEnvReduction.timed A ACost Z l distCost) (1 + a + (TA + (1 + d + TZ))) := by
  time_bound

end CatCrypt.Crypto.UCConcreteOracle

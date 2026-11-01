/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.ALSZ
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Crypto.UCChannelLiftTimed
public import CatCryptCore.Crypto.OTExtension.IKNPPVWTimed

/-!
# Time of the PRG reduction and of the simulators of ALSZ

`derive_reduction` builds the costed forms of the hop reduction `prgHybRed` of the PRG hybrids,
over its distinguisher `D`, and of the reduction of ALSZ to the PRG `alszRed`, over the keyed
world `W` of the environment (`alszPrgRed G i Z` is `alszRed G i` over the world of `Z`), with
their erasure theorems; `time_bound` gives their times: the time of `D` (of `W`) plus its call
cost plus a constant. The simulator `simA` of one base OT is certified by `derive_reduction`,
`derive_time_bound` and `derive_hybrid_time`, and the simulator `simALSZ` of ALSZ over the seed
OTs by `derive_simulator`. No module imports this file.

## Main results

* `prgHybRed.tree.timed`, `prgHybRed.tree.erase_timed`, `prgHybRed.tree.timeBound_timed`.
* `alszRed.tree.timed`, `alszRed.tree.erase_timed`, `alszRed.tree.timeBound_timed`.
* `simA.timed`, `simA.erase_timed`, `simA.timeBound_timed`.
* `simALSZ.timed`, `simALSZ.erase_timed`, `simALSZ.timeBound_timed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.ALSZ

open CatCrypt.Core

derive_reduction prgHybRed

derive_reduction alszRed

/-- **Time of the reduction of ALSZ to the PRG.** With a keyed world of time at most `t` and call
cost at most `c`, the reduction runs in time at most `t + c + 4`. -/
theorem alszRed.tree.timeBound_timed {κ m : ℕ} {Seed : Type}
    (G : Assumptions.PRGDef Seed (Fin m → Bool)) [Fintype Seed] [Inhabited Seed] (i : Fin κ)
    (W : IKNPSquare.IKNPKey κ m → SPTree.Timed Bool) (WCost : IKNPSquare.IKNPKey κ m → ℕ)
    (y : Fin m → Bool) (yCost : Fin m → ℕ) {t c : ℕ} (hW : ∀ k, (W k).time ≤ t)
    (hc : ∀ k, WCost k ≤ c) :
    SPTree.Timed.stepTime (alszRed.tree.timed G i W WCost y yCost) ≤ t + c + 4 := by
  time_bound

/-- **Time of the hop reduction.** With a distinguisher of time at most `t` and call cost at most
`c`, the hop reduction of the PRG hybrids runs in time at most `t + c + 3`. -/
theorem prgHybRed.tree.timeBound_timed {κ : ℕ} {Seed Out : Type} [Fintype Seed]
    [Nonempty Seed] [Fintype Out] [Nonempty Out] (G : Assumptions.PRGDef Seed Out)
    (D : (Fin κ → Out) → SPTree.Timed Bool) (DCost : (Fin κ → Out) → ℕ) (i : Fin κ) (y : Out)
    {t c : ℕ} (hD : ∀ x, (D x).time ≤ t) (hc : ∀ x, DCost x ≤ c) :
    SPTree.Timed.stepTime (prgHybRed.tree.timed G D DCost i y) ≤ t + c + 3 := by
  time_bound

end CatCrypt.Crypto.OT.ALSZ

derive_reduction CatCrypt.Crypto.OT.ALSZ.simA
derive_time_bound CatCrypt.Crypto.OT.ALSZ.simA.start.tree
derive_time_bound CatCrypt.Crypto.OT.ALSZ.simA.resume.tree
derive_time_bound CatCrypt.Crypto.OT.ALSZ.simA.finish.tree
derive_hybrid_time CatCrypt.Crypto.OT.ALSZ.simA
derive_simulator CatCrypt.Crypto.OT.ALSZ.simALSZ

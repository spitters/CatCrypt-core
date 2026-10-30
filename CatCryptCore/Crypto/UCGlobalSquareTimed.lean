/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCGlobalSquare
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the router over a global functionality

The costed form of the router `gRouter` of `UCGlobalSquare.lean`, derived by
`derive_reduction`, and the time theorems of its three steps, derived by `derive_time_bound`;
the costed forms of the bundled simulators `gSim` and `gSimB`, derived by `derive_simulator`;
the costed form of the multi-call simulator `gSimHybrid`, the time theorems of its three steps
and its time theorem, derived by `derive_hybrid_time`. No module imports this file.

## Main results

* `gRouter.timed`, `gRouter.erase_timed`: the costed router and its erasure.
* `gRouter.start.tree.timeBound_timed`, `gRouter.resume.tree.timeBound_timed`,
  `gRouter.finish.tree.timeBound_timed`: the time bounds of the three costed steps.
* `gSim.timeBound_timed`: the costed `gSim` over a costed simulator with step bounds
  `a`, `b`, `c` takes the time `max (a + 14) (max (b + 14) (c + 6))`.
* `gSimB.timeBound_timed`: the costed `gSimB` takes that time plus `4`.
* `gSimHybrid.timed`, `gSimHybrid.erase_timed`: the costed simulator and its erasure.
* `gSimHybrid.start.tree.timeBound_timed`, `gSimHybrid.resume.tree.timeBound_timed`,
  `gSimHybrid.finish.tree.timeBound_timed`: the time bounds of the three costed steps.
* `gSimHybrid.timeBound_timed`: the costed `gSimHybrid` has these three step bounds.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.gRouter
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.finish.tree
derive_simulator CatCrypt.Crypto.UCTransparent.gSim
derive_simulator CatCrypt.Crypto.UCTransparent.gSimB
derive_reduction CatCrypt.Crypto.UCTransparent.gSimHybrid
derive_time_bound CatCrypt.Crypto.UCTransparent.gSimHybrid.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.gSimHybrid.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.gSimHybrid.finish.tree
derive_hybrid_time CatCrypt.Crypto.UCTransparent.gSimHybrid

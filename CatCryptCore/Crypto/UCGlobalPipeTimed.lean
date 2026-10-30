/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCGlobalPipe
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the post-processing simulator

`derive_reduction`, `derive_time_bound` and `derive_hybrid_time` build the costed form of the
pure post-processing simulator `MultiHybrid.postSim` of `UCGlobalPipe.lean` and the time
theorems of its three steps, over the post-processing `f` with its cost companion. No module
imports this file.

## Main results

* `MultiHybrid.postSim.timed`, `MultiHybrid.postSim.erase_timed`: the costed form and its
  erasure.
* `MultiHybrid.postSim.timeBound_timed`: `start` costs `0`; `resume` and `finish` cost the
  bound of the costed post-processing plus its step cost plus `1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

derive_reduction postSim
derive_time_bound postSim.start.tree
derive_time_bound postSim.resume.tree
derive_time_bound postSim.finish.tree
derive_hybrid_time postSim

end CatCrypt.Crypto.UCTransparent.MultiHybrid

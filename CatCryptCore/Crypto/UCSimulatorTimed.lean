/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the forwarding simulator

The costed form of the forwarding simulator `MultiHybrid.idSim` of `UCSimulator.lean`, derived
by `derive_reduction`, and the time theorems of its three steps, derived by
`derive_time_bound`: each step costs `0`. No module imports this file.

## Main results

* `MultiHybrid.idSim.timed`, `MultiHybrid.idSim.erase_timed`: the costed form and its erasure.
* `MultiHybrid.idSim.timeBound_timed`: every step of the costed form costs `0`.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.MultiHybrid.idSim
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.idSim.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.idSim.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.idSim.finish.tree

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

/-- **Running time of the forwarding simulator**: `start`, `resume` and `finish` of the costed
form each cost `0`. -/
theorem idSim.timeBound_timed (E O : Type) : (idSim.timed E O).TimeBound 0 0 0 :=
  ⟨fun s e => idSim.start.tree.timeBound_timed E O s e,
    fun s o => idSim.resume.tree.timeBound_timed E O s o,
    fun s o => idSim.finish.tree.timeBound_timed E O s o⟩

end CatCrypt.Crypto.UCTransparent.MultiHybrid

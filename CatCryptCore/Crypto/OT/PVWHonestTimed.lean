/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.PVWHonest
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the simulator of the PVW OT with both parties honest

`derive_simulator` builds the costed form, the erasure theorem and the time theorem of
`pvwSimH`, the simulator of `PVWHonest.lean` with both parties honest; it derives on the way
the costed form `simH.timed` of the multi-call simulator `simH` and the time theorems of its
three steps, from which `derive_hybrid_time` proves the time theorem of `simH.timed`.
No module imports this file.

## Main results

* `simH.timed`, `simH.erase_timed`, `simH.timeBound_timed`: the costed multi-call simulator,
  its erasure and its time.
* `pvwSimH.timed`, `pvwSimH.erase_timed`, `pvwSimH.timeBound_timed`: the costed simulator, its
  erasure and its time.
-/

@[expose] public section

set_option autoImplicit false

derive_simulator CatCrypt.Crypto.OT.PVWHonest.pvwSimH
derive_hybrid_time CatCrypt.Crypto.OT.PVWHonest.simH

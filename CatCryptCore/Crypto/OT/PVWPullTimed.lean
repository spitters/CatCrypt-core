/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.PVWPull
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the adversary-port simulator of the PVW OT

`derive_reduction` builds the costed form of the multi-call simulator `simP` of
`PVWPull.lean`, `derive_time_bound` the time theorems of its three steps and
`derive_hybrid_time` the time theorem of the costed form. No module imports this file.

## Main results

* `simP.timed`, `simP.erase_timed`: the costed multi-call simulator and its erasure.
* `simP.timeBound_timed`: its time.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.OT.PVWPull.simP
derive_time_bound CatCrypt.Crypto.OT.PVWPull.simP.start.tree
derive_time_bound CatCrypt.Crypto.OT.PVWPull.simP.resume.tree
derive_time_bound CatCrypt.Crypto.OT.PVWPull.simP.finish.tree
derive_hybrid_time CatCrypt.Crypto.OT.PVWPull.simP

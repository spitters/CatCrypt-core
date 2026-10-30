/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.ChannelSquare
public import CatCryptCore.Crypto.UCOracleGameTimed
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the channel adversary and the channel simulator

`derive_reduction` builds the costed form of the channel adversary `chanAdv` of
`ChannelSquare.lean`: the reduction of an environment against the channel protocol with a
given transcript, asking the AEAD calls of the protocol as oracle queries.

`derive_reduction`, `derive_time_bound` and `derive_hybrid_time` build the costed form of the
adversary-port simulator `secSimA` and the time theorems of its three steps, whose draw of the
transcript is a `sampleDist` node; `derive_simulator` builds the costed form of the bundled
simulator `secSim`, whose steps cost at most `20`.

## Main definitions

* `chanAdv.timed` — the costed channel adversary
* `secSimA.timed`, `secSim.timed` — the costed simulators

## Main results

* `chanAdv.erase_timed` — the costed channel adversary erases to `chanAdv N ad Zv pk c t`
* `secSimA.erase_timed`, `secSimA.timeBound_timed` — erasure and step bounds of `secSimA`
* `secSim.erase_timed`, `secSim.timeBound_timed` — erasure and the bound `20` of `secSim`

No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.ChannelSquare

open CatCrypt.Core

derive_reduction chanAdv

derive_reduction secSimA
derive_time_bound secSimA.start.tree
derive_time_bound secSimA.resume.tree
derive_time_bound secSimA.finish.tree
derive_hybrid_time secSimA
derive_simulator secSim

end CatCrypt.Crypto.AKE.ChannelSquare

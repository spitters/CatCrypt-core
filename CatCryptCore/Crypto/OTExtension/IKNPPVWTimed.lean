/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNPPVW
public import CatCryptCore.Crypto.OTExtension.IKNPWakeTimed
public import CatCryptCore.Crypto.OT.PVWPullTimed
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Costed forms of the simulators of IKNP over the PVW base OTs

`derive_simulator` gives the costed forms of the simulators `simU` and `simC` of
`IKNPPVW.lean`, their erasure theorems and their time theorems. `simU` is the IKNP simulator
`simW` on relabelled ports; its time is that of `simW` on the states of its invariant
(`simW.timeBoundInv_timed` of `IKNPWakeTimed.lean`). `simC` composes the forwarding of the
parties' port beside the indexed copies of the PVW simulator `simP` and the forwarding of the
channel's adversary port with `simU`, on relabelled ports; its time is the sum of the times of
its parts. No module imports this file.

## Main results

* `simU.timed`, `simU.erase_timed`, `simU.timeBound_timed`.
* `simC.timed`, `simC.erase_timed`, `simC.timeBound_timed`.
-/

@[expose] public section

set_option autoImplicit false

derive_simulator CatCrypt.Crypto.OT.IKNPPVW.simU
derive_simulator CatCrypt.Crypto.OT.IKNPPVW.simC

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.PVWOTSquare
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the simulator of the dual-mode OT against a corrupt sender

`derive_simulator` builds the costed form, the erasure theorem and the time theorem of
`pvwSimSend`, the simulator of `PVWOTSquare.lean` against a corrupt sender, with a cost for
`decode`.

No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

derive_simulator CatCrypt.Crypto.OT.PVW.pvwSimSend

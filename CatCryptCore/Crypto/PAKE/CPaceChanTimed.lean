/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceChan
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Crypto.UCWakeTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the bridging simulator of CPace over a channel

`derive_simulator` builds the costed form, the erasure theorem and the time theorem of
`bridgeSim`, the single-call relabelling simulator of `CPaceChan.lean` that maps the woken party's
output to the answer of `send`.

No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceChan

open CatCrypt.Core

derive_simulator bridgeSim

end CatCrypt.Crypto.PAKE.CPaceChan

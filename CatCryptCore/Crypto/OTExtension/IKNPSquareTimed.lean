/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNPSquare
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the IKNP simulators

`derive_simulator` builds the costed forms, erasure theorems and time theorems of the two
simulators of `IKNPSquare.lean`, `iknpSimRecv` against a corrupt receiver and `iknpSimSend`
against a corrupt sender, together with those of the adversary-port simulator `postSim`; the
answer map of each simulator is a costed binder. `derive_reduction` and `derive_time_bound`
build the costed form and the time theorem of the answer map `simSPost` of `iknpSimSend`.

No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.IKNPSquare

open CatCrypt.Core

derive_simulator iknpSimRecv
derive_simulator iknpSimSend
derive_reduction simSPost
derive_time_bound simSPost.tree

end CatCrypt.Crypto.OT.IKNPSquare

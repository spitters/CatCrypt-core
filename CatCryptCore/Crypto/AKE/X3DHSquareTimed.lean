/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquare
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the X3DH simulator

`derive_reduction` builds the costed form `simProt.timed` of the multi-call simulator `simProt`
of `X3DHSquare.lean` and its erasure theorem. The start step `simStart` is read as a computation
tree: each draw of a long-term pair, of a session secret and of a key-derivation value is a
`sample` node, and the record updates, the derivation inputs `aliceInp` and `bobInp`, the group
operations and the decisions are priced by the cost model of `derive_timed`. A lookup in the
key-derivation table costs in the length of the table.

No module imports this file.

## Main results

* `simProt.timed`, `simProt.erase_timed`: the costed multi-call simulator and its erasure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core

set_option maxHeartbeats 400000 in
-- The start step reflects ten event cases with nested record updates.
derive_reduction simProt

end CatCrypt.Crypto.AKE.X3DHSquare

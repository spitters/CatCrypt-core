/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceSquare
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Running time of the CPace simulator

`derive_reduction` builds the costed form of the multi-call simulator `simProt G` of
`CPaceSquare.lean`, whose state holds the table of `H1` (a function of the passwords, sampled at
the first activation), the tables of the sessions and the lists of candidates and programmed
inputs, at the costed state in which each stored function carries a cost companion.
`derive_simulator` builds the costed form of the bundled simulator `cpaceSim G` from it. The
lists of the state grow with the activations, so that the cost of a step is not bounded
uniformly: the time theorem of `cpaceSim` takes a time bound of `simProt.timed` on the states
of an invariant as its hypothesis.

No module imports this file.

## Main results

* `simProt.timed`, `simProt.erase_timed`: the costed multi-call simulator and its erasure.
* `cpaceSim.timed`, `cpaceSim.erase_timed`, `cpaceSim.timeBound_timed`: the costed bundled
  simulator, its erasure, and its time from a time bound of `simProt.timed` on the states of an
  invariant.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceSquare

set_option maxHeartbeats 1000000 in
-- The derivation prices and erases the nested matches of `simStart` and `simCore` over a state
-- of eight fields, five of them holding functions; it exceeds the default budget of the
-- command (it needs between 400000 and 1000000 heartbeats).
derive_reduction simProt

derive_simulator cpaceSim

end CatCrypt.Crypto.PAKE.CPaceSquare

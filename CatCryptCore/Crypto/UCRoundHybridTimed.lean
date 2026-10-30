/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCRoundHybrid
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the session reductions

`derive_reduction sessRed` builds the costed form of the session reduction
`KeyedGame.sessRed`, the multi-session adversary with every session other than `i` simulated
and session `i` forwarded to the oracle, and of the hop reduction `KeyedGame.sessReduction`,
`sessRed` over the session oracles of the hybrid world `i`.

No module imports this file.

## Main definitions

* `KeyedGame.sessRed.timed` — the costed reduction, over the session oracles `orc` with their
  cost companion `orcCost` and the costed adversary `B`
* `KeyedGame.sessReduction.timed` — the costed hop reduction, over the costs of the oracles of
  `G₀` and `G₁` and the costed adversary `B`

## Main results

* `KeyedGame.sessRed.erase_timed` — the costed reduction erases to `sessRed orc i s₀ B.erase`
* `KeyedGame.sessReduction.erase_timed` — the costed hop reduction erases to
  `sessReduction G₀ G₁ i B.erase`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.KeyedGame

open CatCrypt.Core OracleAdv.Timed

derive_reduction sessRed
derive_reduction sessReduction


end CatCrypt.Crypto.UCTransparent.KeyedGame

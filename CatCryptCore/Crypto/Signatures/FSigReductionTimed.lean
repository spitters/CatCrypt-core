/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.FSigReduction
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the forger of the signature functionality

`derive_reduction` builds the costed forms of the simulated signer `forgeAct`, of the forger
loop `forgeReduce` over an environment strategy, and of the forger `forger` of an environment.

No module imports this file.

## Main definitions

* `forgeAct.timed`, `forgeReduce.timed`, `forger.timed` — the costed forms

## Main results

* `forgeAct.erase_timed`, `forgeReduce.erase_timed`, `forger.erase_timed` — their erasure
  theorems
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signatures.FSigSys

open CatCrypt.Core OracleAdv.Timed

derive_reduction forgeAct
derive_reduction forgeReduce
derive_reduction forger

end CatCrypt.Crypto.Signatures.FSigSys

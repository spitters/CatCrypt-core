/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the environment reduction of an oracle protocol

`derive_reduction` builds the costed forms of `OProt.reduce`, the environment `Z` with its
distinguisher run against the program of an oracle protocol `P` as an oracle adversary, and of
`OProt.reduction`, `reduce` from the initial states of `Z` and `P`.

No module imports this file.

## Main definitions

* `OProt.reduce.timed`, `OProt.reduction.timed` — the costed reductions

## Main results

* `OProt.reduce.erase_timed`, `OProt.reduction.erase_timed` — their erasure theorems
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.OProt

open CatCrypt.Core OracleAdv.Timed

derive_reduction reduce
derive_reduction reduction

end CatCrypt.Crypto.UCTransparent.OProt

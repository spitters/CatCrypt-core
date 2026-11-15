/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.WeakPRF
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.ForMathlib.ListLength
public import CatCryptCore.Tactics.StdCosts
import CatCryptCore.Tactics.AutoTime

/-!
# Time certificate of the DDH reduction of the weak-PRF hybrid

`derive_reduction` gives the costed form of `wprfHybRed` of `WeakPRF.lean` over a costed
distinguisher, with its erasure theorem.

## Main results

* `wprfHybRed.tree.timed`, `wprfHybRed.tree.erase_timed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions.WeakPRF

open CatCrypt.Core

derive_reduction wprfHybRed

end CatCrypt.Crypto.Assumptions.WeakPRF

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.Games
public import CatCryptCore.Tactics.DeriveTimedStructure

/-!
# The costed OT adversary

The costed mirror `OTAdversary.Timed` of the semi-honest OT adversary `OTAdversary` of
`CatCryptCore.Crypto.OT.Games`, derived by `derive_timed_structure`: the input choice `choose`
becomes a costed tree, and the distinguisher `guess` a costed tree with its cost companion. A
reduction that maps an OT adversary to an OT adversary (the base-OT reductions of the IKNP
extension, the OT reductions of COPE) gets its costed form of this type from
`derive_reduction`, field by field.

## Main results

* `OTAdversary.Timed` — the costed mirror, with the erasure relation `OTAdversary.Timed.Erases`
  and the time bound `OTAdversary.Timed.TimeBound`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT

derive_timed_structure OTAdversary

end CatCrypt.Crypto.OT

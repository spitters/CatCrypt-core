/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSemiHonest
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the semi-honest simulator

`derive_simulator` builds the costed form of the simulator `semiHonestSim` of
`UCSemiHonest.lean`, the corrupt-party wrapper composed with the simulator of the subroutine,
each extended by forwarding on the honest port, over costed forms of the wrapper and of the
subroutine's simulator. No module imports this file.

## Main results

* `semiHonestSim.timed`, `semiHonestSim.erase_timed`: the costed form and its erasure.
* `semiHonestSim.timeBound_timed`: over costed forms of the wrapper and of the subroutine's
  simulator with step bounds `(a, b, c)` and `(a', b', c')`, the costed form is bounded by
  `max (a + 7) (max (b + 7) (c + 3)) + max (a' + 7) (max (b' + 7) (c' + 3))`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

derive_simulator semiHonestSim

end CatCrypt.Crypto.UCTransparent

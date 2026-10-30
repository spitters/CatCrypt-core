/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.FSigSys
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Running time of the simulator for `F_SIG`

The costed form of the bundled simulator `fsigSim` of `FSigSys.lean`, its erasure theorem and
its time theorem, derived by `derive_simulator`. The costed simulator takes a costed key
generation; over one whose time is at most `G_keygen` it takes the time `G_keygen + 3`. No
module imports this file.

## Main results

* `fsigSim.timed`, `fsigSim.erase_timed`, `fsigSim.timeBound_timed`: the costed simulator,
  its erasure and its time bound.
-/

@[expose] public section

set_option autoImplicit false

derive_simulator CatCrypt.Crypto.Signatures.FSigSys.fsigSim

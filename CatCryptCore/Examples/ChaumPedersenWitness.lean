/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.ChaumPedersen
public import CatCryptCore.Examples.Schnorr
public import CatCryptCore.Examples.ToyPairingGroup

/-!
# Witness of special soundness of Chaum-Pedersen identification

`chaumPedersen_special_soundness` quantifies over the group parameters `GroupParam`. The
theorem here applies it at the group `G₁` of the pairing group of `ZMod 2`, presented as
`GroupParam` by `Schnorr.g₁GroupParam`, which discharges every field of the record.

## Main results

* `chaumPedersen_special_soundness_witness` — special soundness at these group parameters
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.ChaumPedersen

open CatCrypt.Examples.Sigma

/-- `chaumPedersen_special_soundness` at the group parameters of the pairing group of
`ZMod 2`. -/
theorem chaumPedersen_special_soundness_witness :
    SpecialSoundness (chaumPedersenSigma (Schnorr.g₁GroupParam (zmodPairingGroup 2))) :=
  chaumPedersen_special_soundness (Schnorr.g₁GroupParam (zmodPairingGroup 2))

end CatCrypt.Examples.ChaumPedersen

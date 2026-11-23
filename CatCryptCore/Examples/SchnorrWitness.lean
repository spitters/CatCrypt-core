/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.Schnorr
public import CatCryptCore.Examples.ToyPairingGroup

/-!
# Witness of special soundness of Schnorr identification

`schnorr_special_soundness` takes two accepting transcripts with a shared commitment and
distinct challenges. The theorem here applies it in the pairing group of `ZMod 2` at the public
key `g₁`, the commitment `1` and the transcripts `(0, 0)` and `(1, 1)` of challenge and response,
both accepting, with the challenges `0 ≠ 1`.

## Main results

* `schnorr_special_soundness_witness` — the extracted exponent `(0 - 1) * (0 - 1)⁻¹` gives `g₁`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.Schnorr

open CatCrypt.Crypto CatCrypt.Crypto.PairingGroup

/-- `schnorr_special_soundness` in the pairing group of `ZMod 2` at the public key `g₁`, the
commitment `1` and the challenge-response pairs `(0, 0)` and `(1, 1)`. -/
theorem schnorr_special_soundness_witness :
    (zmodPairingGroup 2).g₁ =
      (zmodPairingGroup 2).g₁ ^ᵍ (((0 : ZMod 2) - 1) * ((0 : ZMod 2) - 1)⁻¹) :=
  schnorr_special_soundness (P := zmodPairingGroup 2) (zmodPairingGroup 2).g₁ 1 0 1 0 1
    (by simp [schnorrAccepts, zpowZMod₁])
    (by simp [schnorrAccepts, zpowZMod₁])
    (by decide)

end CatCrypt.Examples.Schnorr

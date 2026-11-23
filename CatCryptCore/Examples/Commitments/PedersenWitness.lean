/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.Commitments.Pedersen
public import CatCryptCore.Examples.ToyPairingGroup

/-!
# Witnesses of the Pedersen hiding theorems

`pedersen_perfect_hiding` and `pedersen_hiding_uc` quantify over the parameter record
`PedersenParams`. The record `zmodPedersenParams` takes the pairing group of `ZMod 2` and the
exponent `β = 1`, whose hypothesis `β ≠ 0` holds in `ZMod 2`. The theorems here apply both
headlines at these parameters, the first at the adversary that chooses the messages `0` and `1`
and outputs `true`, the second at the environment output type `Unit`.

## Main results

* `pedersen_perfect_hiding_witness` — the hiding advantage of that adversary is `0`
* `pedersen_hiding_uc_witness` — the commitments to the two messages emulate each other with
  distance `0`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.Commitments.Pedersen

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.UCDSL

/-- Pedersen parameters over the pairing group of `ZMod 2` with the exponent `β = 1`. -/
noncomputable def zmodPedersenParams : PedersenParams where
  P := zmodPairingGroup 2
  β := 1
  hβ := one_ne_zero

/-- The Pedersen hiding adversary over `zmodPedersenParams` that chooses the messages `0` and
`1` and outputs `true`. -/
noncomputable def zmodPedersenAdv : zmodPedersenParams.PedHidingAdv where
  choose := SPComp.pure (0, 1)
  distinguish _ := SPComp.pure true

/-- `pedersen_perfect_hiding` at `zmodPedersenParams` and `zmodPedersenAdv`: the hiding
advantage is `0`. -/
theorem pedersen_perfect_hiding_witness :
    zmodPedersenParams.PedHiding_Advantage zmodPedersenAdv = 0 :=
  zmodPedersenParams.pedersen_perfect_hiding zmodPedersenAdv

/-- `pedersen_hiding_uc` at `zmodPedersenParams` with environment output type `Unit`. -/
theorem pedersen_hiding_uc_witness :
    UCEmulates 0
      (UCSpec.ofGame (ZMod zmodPedersenParams.P.p × ZMod zmodPedersenParams.P.p)
        zmodPedersenParams.P.G₁ Unit)
      (UCProtocol.ofGame (fun (p : ZMod zmodPedersenParams.P.p × ZMod zmodPedersenParams.P.p) =>
        SPComp.bind (SPComp.sample (ZMod zmodPedersenParams.P.p)) fun r =>
          SPComp.pure (zmodPedersenParams.commit p.1 r)))
      (UCProtocol.ofGame (fun (p : ZMod zmodPedersenParams.P.p × ZMod zmodPedersenParams.P.p) =>
        SPComp.bind (SPComp.sample (ZMod zmodPedersenParams.P.p)) fun r =>
          SPComp.pure (zmodPedersenParams.commit p.2 r))) :=
  zmodPedersenParams.pedersen_hiding_uc Unit

end CatCrypt.Examples.Commitments.Pedersen

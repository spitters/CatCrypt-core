/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.ShamirSecretSharing

/-!
# Witness of perfect privacy of Shamir secret sharing

`shamir_perfect_privacy` quantifies over a prime `p`, the number `d` of revealed points, the
points, which must be nonzero, the two secrets and the adversary. The theorem here applies it
over `ZMod 2` with one revealed point `1`, the secrets `0` and `1` and the adversary that
outputs `true`.

## Main results

* `shamir_perfect_privacy_witness` — the privacy advantage of that adversary is `0`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.ShamirSecretSharing

open CatCrypt.Core

/-- `shamir_perfect_privacy` over `ZMod 2` at the single revealed point `1`, the secrets `0`, `1`
and the constant adversary `true`: its privacy advantage is `0`. -/
theorem shamir_perfect_privacy_witness :
    PrivAdv (p := 2) (fun _ : Fin 1 => 1) 0 1 (fun _ => SPComp.pure true) = 0 :=
  shamir_perfect_privacy (fun _ : Fin 1 => 1) (fun _ => by decide) 0 1
    (fun _ => SPComp.pure true)

end CatCrypt.Examples.ShamirSecretSharing

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.Commitment

/-!
# Witnesses of hiding and binding of the example commitments

`maskComm_perfect_hiding` quantifies over the two messages and the adversary; the first theorem
applies it at the messages `false`, `true` and the adversary that outputs the commitment.
`idComm_perfectly_binding` quantifies over a commitment and two verifying openings; the second
theorem applies it to the commitment `true` and two honest openings of it.

## Main results

* `maskComm_perfect_hiding_witness` — the hiding advantage of that adversary is `0`
* `idComm_perfectly_binding_witness` — the two honest openings have the same message
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.Commitment

open CatCrypt.Core

/-- `maskComm_perfect_hiding` at the messages `false`, `true` and the adversary that outputs
the commitment: its hiding advantage is `0`. -/
theorem maskComm_perfect_hiding_witness :
    Hiding_Adv MaskComm false true (fun c => SPComp.pure c) = 0 :=
  maskComm_perfect_hiding false true (fun c => SPComp.pure c)

/-- `idComm_perfectly_binding` at the commitment `true` and the two openings `(true, ())`,
both of which verify. -/
theorem idComm_perfectly_binding_witness :
    (show IdComm.Message from true) = (show IdComm.Message from true) :=
  idComm_perfectly_binding (show IdComm.Commitment from true) true true () () (by decide)
    (by decide)

end CatCrypt.Examples.Commitment

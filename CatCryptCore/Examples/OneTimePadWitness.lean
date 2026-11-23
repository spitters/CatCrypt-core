/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.OneTimePad

/-!
# Witness of perfect IND-CPA security of the one-time pad

`otp_perfect_indcpa` quantifies over the two messages and the adversary. The theorem here
applies it at the messages `false` and `true` and the adversary that outputs the ciphertext.

## Main results

* `otp_perfect_indcpa_witness` — the IND-CPA advantage of that adversary is `0`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.OTP

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.SecurityDefs

/-- `otp_perfect_indcpa` at the messages `false`, `true` and the adversary that outputs the
ciphertext: its IND-CPA advantage is `0`. -/
theorem otp_perfect_indcpa_witness :
    INDCPA_Adv BoolOTP false true (fun c => SPComp.pure c) = 0 :=
  otp_perfect_indcpa false true (fun c => SPComp.pure c)

end CatCrypt.Examples.OTP

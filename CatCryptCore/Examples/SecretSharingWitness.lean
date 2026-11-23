/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.SecretSharing

/-!
# Witness of perfect privacy of 2-of-2 XOR secret sharing

`ss_perfect_privacy` quantifies over the corrupted party, the two secrets and the adversary. The
theorem here applies it at the party `false`, the secrets `false` and `true` and the adversary
that outputs the share it sees.

## Main results

* `ss_perfect_privacy_witness` — the privacy advantage of that adversary is `0`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.SecretSharing

open CatCrypt.Core

/-- `ss_perfect_privacy` at the corrupted party `false`, the secrets `false`, `true` and the
adversary that outputs the share: its privacy advantage is `0`. -/
theorem ss_perfect_privacy_witness :
    SS_Privacy_Adv false false true (fun s => SPComp.pure s) = 0 :=
  ss_perfect_privacy false false true (fun s => SPComp.pure s)

end CatCrypt.Examples.SecretSharing

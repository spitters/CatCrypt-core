/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.EncryptThenMAC

/-!
# Encrypt-then-MAC under Chosen-Ciphertext Attack

This file studies the Encrypt-then-MAC construction of `EncryptThenMAC.lean`
against the IND-CCA game of `SecurityDefs.lean`, in which the adversary is handed
a decryption oracle on every ciphertext except the challenge. Following Rosulek,
*The Joy of Cryptography*, §10 (authenticated encryption), and Bellare &
Namprempre, *Authenticated Encryption: Relations among Notions*.

## The bound at the one-bit XOR instance

The natural hope is that Encrypt-then-MAC achieves *perfect* IND-CCA (advantage
`0`) because "a MAC that rejects forged ciphertexts makes the decryption oracle
useless." That hope is **false** in this information-theoretic single-shot model,
for two independent reasons, both cryptographic content rather than framework
artifacts:

1. **No perfect MAC exists over a finite tag space.** An unbounded adversary can
   present an off-challenge ciphertext with a guessed tag; it verifies with
   probability at least `1 / |Tag|`, which is strictly positive. So the integrity
   (authenticity) gap between the real decryption oracle and an always-reject
   oracle is never exactly `0`.
2. **The one-time-pad decryption oracle leaks the key.** For the XOR / OTP
   instantiation `BoolEtM`, a single successful decryption query returns
   `ke ⊕ c`, exposing the confidentiality key. Under the challenge-preserving key
   bijection `ke ↦ ke ⊕ (m₀ ⊕ m₁)` used to prove perfect IND-CPA, that oracle
   answer *shifts by* `m₀ ⊕ m₁`, so it distinguishes the two worlds outright.
   Concretely: `boolXorMac km c = km ⊕ c` over a single bit is trivially
   forgeable, and `BoolEtM` is *not* IND-CCA secure. (Advantage `0` holds only
   degenerately, when `m₀ = m₁`.)

The IND-CCA advantage of any scheme is bounded by the IND-CPA advantage plus
the decryption-oracle authenticity gaps (`SecurityDefs.INDCCA_reduces_to_INDCPA`).
For the XOR instantiation the IND-CPA contribution is exactly `0`
(`boolEtM_perfect_indcpa`), leaving the two gaps. The challenge `(c, t)` reveals
the MAC key `t ⊕ c`, so for `m₀ ≠ m₁` one decryption query wins, and for that
adversary the sum of the two gaps is at least `1`.

## Main result

* `boolEtM_indcca_reduces` — `BoolEtM`'s IND-CCA advantage is bounded by its two
  decryption-oracle authenticity gaps alone; the confidentiality (IND-CPA)
  contribution is exactly `0`. The bound is at least `1` for the adversary above,
  so it is no security statement for `BoolEtM`.

## References

* [Rosulek, The Joy of Cryptography, §10; Construction 10.9, Claim 10.10]
* [Bellare & Namprempre, Authenticated Encryption: Relations among Notions]
-/

@[expose] public section

namespace CatCrypt.Examples.EtMCCA

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Examples.EncryptThenMAC

open scoped ENNReal

/-- **The IND-CCA advantage of the one-bit XOR Encrypt-then-MAC scheme is at most its
two decryption-oracle gaps.** For the XOR / one-time-pad instantiation `BoolEtM`,
the IND-CCA advantage of every (oracle-using) adversary is bounded by the two
*authenticity gaps* — the advantage of telling the real decryption oracle apart
from the always-reject oracle in each world.

The general reduction `INDCCA_reduces_to_INDCPA` supplies a middle IND-CPA term;
here it is exactly `0` by `boolEtM_perfect_indcpa`, the perfect IND-CPA security
of the one-time pad. The challenge ciphertext reveals the key of the XOR MAC, so
for `m₀ ≠ m₁` an adversary wins with one decryption query, and the right-hand
side is at least `1` for it: `BoolEtM` is not IND-CCA secure. -/
theorem boolEtM_indcca_reduces (m₀ m₁ : Bool)
    (A : (BoolEtM.Ciphertext → SPComp (Option BoolEtM.Plaintext)) →
         BoolEtM.Ciphertext → SPComp Bool) :
    INDCCA_Adv BoolEtM m₀ m₁ A ≤
      Advantage (INDCCA_Game BoolEtM m₀ m₁ true A) (INDCCA_rejectGame BoolEtM m₀ m₁ true A)
      + Advantage (INDCCA_rejectGame BoolEtM m₀ m₁ false A) (INDCCA_Game BoolEtM m₀ m₁ false A) := by
  -- The confidentiality (IND-CPA) contribution of the reject-oracle adversary is 0.
  simpa [boolEtM_perfect_indcpa] using INDCCA_reduces_to_INDCPA BoolEtM m₀ m₁ A

end CatCrypt.Examples.EtMCCA

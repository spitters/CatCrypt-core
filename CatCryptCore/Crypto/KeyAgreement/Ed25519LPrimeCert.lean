/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PrattCertificate

/-!
# Machine-checked primality of the Ed25519 group order `ℓ`

`Nat.Prime ed25519Llit` for `ℓ = 2^252 + 27742317777372353535851937790883648493`
from an inline Pratt certificate tree checked by kernel reduction
(`PrattCertificate.pratt_prime`). The same `ℓ` is the order of Curve25519's
prime-order subgroup. Nested nodes certify the prime factors of `ℓ - 1` above
`2^20`; the factors below `2^20` are leaves checked by trial division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.Ed25519LPrimeCert

open CatCrypt.PrattCertificate

/-- The Ed25519 group order `ℓ`, as a literal (definitionally equal to
    `2^252 + 27742317777372353535851937790883648493`). -/
def ed25519Llit : ℕ :=
  0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed

/-- `Nat.Prime ed25519Llit`, by a Pratt certificate with root witness `2`. -/
theorem ed25519Llit_prime : Nat.Prime ed25519Llit := by
  pratt_prime
    .node ed25519Llit 2
        [2, 3, 11,
        .node 198211423230930754013084525763697 5
          [2, 3, 23,
          .node 58964693 2
            [2,
            .node 14741173 2 [2, 3, 409477]],
          .node 3044861653679985063343 5 [2, 3, 11, 30703, 82163, 132667, 137849]],
        .node 276602624281642239937218680557139826668747 2
          [2, 7,
          .node 19757330305831588566944191468367130476339 2
            [2, 269,
            .node 213441916511 13
              [2, 5, 73,
              .node 292386187 2 [2, 3, 307, 5879]],
            .node 172054593956031949258510691 2
              [2, 5, 1361, 2851,
              .node 4434155615661930479 17
                [2, 41, 43,
                .node 1257559732178653 2
                  [2, 3, 7, 23, 531581,
                  .node 1224481 13 [2, 3, 5, 2551]]]]]]]

end CatCrypt.Crypto.Util.Ed25519LPrimeCert

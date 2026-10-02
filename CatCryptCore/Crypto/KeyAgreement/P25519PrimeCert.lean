/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PrattCertificate

/-!
# Machine-checked primality of the Curve25519 base-field prime

`Nat.Prime p25519lit` for `p25519lit = 2^255 - 19` from an inline Pratt
certificate tree checked by kernel reduction (`PrattCertificate.pratt_prime`).
Nested nodes certify the prime factors of `p - 1` above `2^20`; the factors below
`2^20` are leaves checked by trial division.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Util.P25519PrimeCert

open CatCrypt.PrattCertificate

/-- The certified prime `57896044618658097711785492504343953926634992332820282019728792003956564819949`
    (`255`-bit), the Curve25519 base-field modulus `2^255 - 19`.
    `N - 1 = 2^2 · 3 · 65147 · 74058212732561358302231226437062788676166966415465897661863160754340907`. -/
def p25519lit : Nat := 57896044618658097711785492504343953926634992332820282019728792003956564819949

/-- `Nat.Prime p25519lit`, by a Pratt certificate with root witness `2`. -/
theorem p25519lit_prime : Nat.Prime p25519lit := by
  pratt_prime
    .node p25519lit 2
        [2, 3, 65147,
        .node 74058212732561358302231226437062788676166966415465897661863160754340907 2
          [2, 3, 353, 57467, 132049,
          .node 1923133 2 [2, 3, 43, 3727],
          .node 31757755568855353 10 [2, 3, 31, 107, 223, 4153, 430751],
          .node 75445702479781427272750846543864801 7
            [2, 3, 5, 75707,
            .node 72106336199 7
              [2, 13,
              .node 2773320623 5 [2, 2437, 569003]],
            .node 1919519569386763 2
              [2, 3, 7, 19, 47, 127,
              .node 8574133 2 [2, 3, 7, 103, 991]]]]]

end CatCrypt.Crypto.Util.P25519PrimeCert

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Bytes as base-256 digits

Three bit masks of a byte stated on its value, and the bound of a number whose base-256 digits
are `k` bytes. The mask lemmas belong next to `UInt8.toNat_and` in `Init/Data/UInt/Bitwise.lean`
(Lean core); the digit bound next to `Nat.ofDigits_lt_base_pow_length` in
`Mathlib/Data/Nat/Digits/Defs.lean`.

## Main results

* `UInt8.toNat_and_248` — `(x &&& 248).toNat = 8 * (x.toNat / 8)`
* `UInt8.toNat_and_127_or_64` — `((x &&& 127) ||| 64).toNat = 64 + x.toNat % 64`
* `UInt8.ofNat_and_127_of_lt` — `UInt8.ofNat m &&& 127 = UInt8.ofNat m` for `m < 128`
* `Fin.sum_toNat_mul_256_pow_lt` — `∑ i : Fin k, (f i).toNat * 256 ^ i < 256 ^ k`
-/

@[expose] public section

set_option autoImplicit false

namespace UInt8

/-- Clearing the three low bits of a byte. -/
theorem toNat_and_248 (x : UInt8) : (x &&& 248).toNat = 8 * (x.toNat / 8) := by
  rw [UInt8.toNat_and]
  have := UInt8.toNat_lt x
  generalize x.toNat = m at this ⊢
  revert m
  decide +kernel

/-- Clearing bit 7 and setting bit 6 of a byte. -/
theorem toNat_and_127_or_64 (x : UInt8) :
    ((x &&& 127) ||| 64).toNat = 64 + x.toNat % 64 := by
  rw [UInt8.toNat_or, UInt8.toNat_and]
  have := UInt8.toNat_lt x
  generalize x.toNat = m at this ⊢
  revert m
  decide +kernel

/-- Clearing bit 7 of a byte below `128` leaves it unchanged. -/
theorem ofNat_and_127_of_lt {m : ℕ} (hm : m < 128) : UInt8.ofNat m &&& 127 = UInt8.ofNat m := by
  revert m
  decide +kernel

end UInt8

namespace Fin

/-- A number whose base-256 digits are `k` bytes is below `256 ^ k`. -/
theorem sum_toNat_mul_256_pow_lt {k : ℕ} (f : Fin k → UInt8) :
    ∑ i : Fin k, (f i).toNat * 256 ^ i.val < 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have h1 := ih (fun i => f i.castSucc)
      have h2 : (f (Fin.last k)).toNat * 256 ^ k ≤ 255 * 256 ^ k :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (UInt8.toNat_lt _))
      rw [pow_succ]
      omega

end Fin

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# Big-endian byte codecs

The big-endian base-256 codec between natural numbers and byte arrays in the
representation of hax extractions (`Array Int`, one byte per entry, the most
significant byte first).

* `beDecode a` is the number whose base-256 digits are the bytes of `a`.
* `beEncode len n` is the `len`-byte encoding of `n`.
* `beDecode_beEncode`: decoding inverts encoding on numbers below `256 ^ len`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCryptCore.Crypto.BigEndianCodec

/-- The number whose big-endian base-256 digits are the entries of `a`. -/
def beDecode (a : Array Int) : ℕ := a.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- The `len`-byte big-endian base-256 encoding of `n`, the most significant byte first;
    it is the encoding of `n % 256 ^ len`. -/
def beEncode (len n : ℕ) : Array Int :=
  (Array.range len).map fun i => ((n / 256 ^ (len - 1 - i) % 256 : ℕ) : Int)

/-- The encoding has `len` bytes. -/
@[simp] theorem size_beEncode (len n : ℕ) : (beEncode len n).size = len := by
  simp [beEncode]

/-- The encoding of zero is `len` zero bytes. -/
theorem beEncode_zero (len : ℕ) : beEncode len 0 = Array.replicate len 0 := by
  unfold beEncode; apply Array.ext <;> simp

/-- Decoding inverts encoding on numbers below `256 ^ len`. -/
theorem beDecode_beEncode {len n : ℕ} (h : n < 256 ^ len) :
    beDecode (beEncode len n) = n := by
  have digits : ∀ k, k ≤ len →
      (List.range k).foldl (fun acc i => acc * 256 + n / 256 ^ (len - 1 - i) % 256) 0 =
        n / 256 ^ (len - k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.range_zero, List.foldl_nil, Nat.sub_zero]
      exact (Nat.div_eq_of_lt h).symm
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      obtain ⟨e, he⟩ : ∃ e, len - 1 - k = e ∧ len - k = e + 1 := ⟨len - 1 - k, rfl, by omega⟩
      rw [he.1, he.2, show len - (k + 1) = e by omega, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      exact Nat.div_add_mod' (n / 256 ^ e) 256
  unfold beDecode beEncode
  rw [← Array.foldl_toList, Array.toList_map, Array.toList_range, List.foldl_map]
  simp only [Int.toNat_natCast]
  rw [digits len (Nat.le_refl len)]
  simp

end CatCryptCore.Crypto.BigEndianCodec

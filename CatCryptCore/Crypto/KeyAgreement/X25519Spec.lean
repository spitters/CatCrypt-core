/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KeyAgreement.Curve25519
public import CatCryptCore.Crypto.KeyAgreement.MontgomeryXOnly

/-!
# The X25519 function of RFC 7748 over `Fp25519`

The X25519 function of RFC 7748 §5 as a Lean function on 32-byte words, written with field
arithmetic in `Fp25519` and the field-level x-only Montgomery ladder `xladderFold`:

```
x25519_spec sk pk
  = encodeUCoord (X * Z⁻¹)   where ((X, Z), _) = xladderFold a24 (decodeUCoord pk, 1)
                                                   (scalarBits sk)
```

`scalarBits sk` lists the 255 bits of the clamped scalar `clamp sk`, least significant first,
so that the ladder consumes bit 254 first and bit 0 last.

## Main definitions

* `bytesToNat`, `natToBytes` — 32 little-endian bytes and the numbers below `2^256`
* `clamp` — the scalar clamping of RFC 7748 §5 on bytes
* `decodeUCoord`, `encodeUCoord` — the u-coordinate codecs (decoding masks bit 255)
* `bitsOfMSB`, `scalarBits` — the bit decomposition consumed by the ladder
* `x25519_spec`, `x25519_base_spec` — the X25519 function and its base-point form (`u = 9`)

## Main results

* `bitsToNat_append` — `bitsToNat` of a concatenation
* `bitsOfMSB_eq` — `bitsOfMSB m k` lists the bits `m - 1, …, 0` of `k`
* `bitsToNat_reverse_bitsOfMSB` — reading the reversed list back gives `k % 2 ^ m`
* `eight_dvd_clampScalar`, `clampScalar_bounds` — a clamped scalar is a multiple of `8` in
  `[2 ^ 254, 2 ^ 255)`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ECC

/-- `bitsToNat` of a concatenation: the second list is read at the length of the first. -/
theorem bitsToNat_append (l l' : List Bool) :
    bitsToNat (l ++ l') = bitsToNat l + 2 ^ l.length * bitsToNat l' := by
  induction l with
  | nil => simp [bitsToNat]
  | cons b l ih =>
      simp only [List.cons_append, bitsToNat, ih, List.length_cons, pow_succ]
      ring

/-! ## Bounds of the clamped scalar -/

/-- A clamped scalar is a multiple of `8`. -/
theorem eight_dvd_clampScalar (k : Nat) : 8 ∣ clampScalar k := by
  rw [Nat.dvd_iff_mod_eq_zero, show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.and_two_pow_sub_one_eq_mod]
  have h₁ : (2 ^ 256 - 1 - 7) &&& ((2 ^ 256 - 1 - 2 ^ 255) &&& (2 ^ 3 - 1)) = 0 := by decide
  have h₂ : 2 ^ 254 &&& (2 ^ 3 - 1) = 0 := by decide
  simp only [clampScalar, Nat.and_or_distrib_right, Nat.and_assoc, h₁, h₂, Nat.and_zero,
    Nat.or_zero]

/-- A clamped scalar lies in `[2 ^ 254, 2 ^ 255)`. -/
theorem clampScalar_bounds (k : Nat) : 2 ^ 254 ≤ clampScalar k ∧ clampScalar k < 2 ^ 255 := by
  refine ⟨Nat.right_le_or, Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_right ?_) ?_⟩ <;>
    norm_num

end CatCrypt.Crypto.ECC

namespace CatCrypt.Crypto.KeyAgreement.X25519.Spec

open CatCrypt.Crypto.ECC

/-! ## Byte-level encoding and decoding -/

/-- A 32-byte X25519 word (scalar or u-coordinate). -/
abbrev X25519Word := Vector UInt8 32

/-- 32 little-endian bytes as a number below `2 ^ 256`. -/
def bytesToNat (b : X25519Word) : Nat :=
  (List.finRange 32).foldl
    (fun acc i => acc + (b[i.val]'(i.isLt)).toNat * 2^(8 * i.val)) 0

/-- The 32 little-endian bytes of a number, modulo `2 ^ 256`. -/
def natToBytes (n : Nat) : X25519Word :=
  Vector.ofFn (fun i => UInt8.ofNat ((n / 2^(8 * i.val)) % 256))

/-! ## Scalar clamping (RFC 7748 §5)

Clamping clears bits 0, 1, 2 of byte 0 and bit 7 of byte 31, and sets bit 6 of byte 31. The
clamped scalar is a multiple of `8` in `[2 ^ 254, 2 ^ 255)` (`eight_dvd_clampScalar`,
`clampScalar_bounds` for the numeric form `clampScalar`). -/

/-- Clamp a 32-byte scalar per RFC 7748. -/
def clamp (sk : X25519Word) : X25519Word :=
  let b0 := sk[0] &&& 248
  let b31_raw := sk[31]
  let b31 := (b31_raw &&& 127) ||| 64
  Vector.ofFn (fun i =>
    if i = ⟨0, by omega⟩ then b0
    else if i = ⟨31, by omega⟩ then b31
    else sk[i.val]'(i.isLt))

/-! ## u-coordinate decoding and encoding

RFC 7748 §5 encodes a u-coordinate as 32 little-endian bytes; decoding masks the high bit of
the last byte. -/

/-- Decode a u-coordinate to `Fp25519`, masking the high bit of byte 31. -/
def decodeUCoord (pk : X25519Word) : Fp25519 :=
  let pk_masked : X25519Word := Vector.ofFn (fun i =>
    if i = ⟨31, by omega⟩ then pk[31] &&& 127
    else pk[i.val]'(i.isLt))
  (bytesToNat pk_masked : Fp25519)

/-- Encode an `Fp25519` value as the 32 little-endian bytes of its canonical
    representative. -/
def encodeUCoord (u : Fp25519) : X25519Word :=
  natToBytes u.val

/-! ## Bit decomposition for the ladder

`xladderFold` consumes the scalar as a list of bits whose head is bit 0 (the convention of
`bitsToNat`); it processes the head last, so the ladder runs from bit 254 down to bit 0. -/

/-- The bits `n - 1, …, 0` of `k`, most significant first. Defined by structural recursion
    on `n`, so that a symbolic `k` does not unfold the list. -/
def bitsOfMSB : Nat → Nat → List Bool
  | 0,     _ => []
  | n + 1, k => ((k / 2^n) % 2 = 1) :: bitsOfMSB n k

/-- The 255 bits of the clamped scalar of `sk`, least significant first. -/
def scalarBits (sk : X25519Word) : List Bool :=
  let n := bytesToNat (clamp sk)
  (bitsOfMSB 255 n).reverse

/-! ## The X25519 function -/

/-- The Curve25519 ladder constant `a24 = 121666` in `Fp25519`. -/
noncomputable def a24 : Fp25519 := curve25519FpParams.a24

/-- **The X25519 function** (RFC 7748 §5): decode the u-coordinate of `pk`, run the
    projective x-only ladder `xladderFold a24 (u, 1)` over the bits of the clamped scalar of
    `sk`, and encode the affine coordinate `X * Z⁻¹` of its first component. -/
noncomputable def x25519_spec (sk pk : X25519Word) : X25519Word :=
  let u := decodeUCoord pk
  let bits := scalarBits sk
  let result_pair := xladderFold a24 (u, 1) bits
  encodeUCoord (result_pair.1.1 * result_pair.1.2⁻¹)

/-- X25519 at the base point `u = 9` of RFC 7748: the public key of `sk`. -/
noncomputable def x25519_base_spec (sk : X25519Word) : X25519Word :=
  x25519_spec sk (natToBytes 9)

/-! ## The bit decomposition read back -/

/-- `bitsOfMSB m k` is the list of the bits `m - 1, …, 0` of `k`. -/
theorem bitsOfMSB_eq (m k : Nat) :
    bitsOfMSB m k
      = ((List.range m).map fun i => decide ((k / 2 ^ i) % 2 = 1)).reverse := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [bitsOfMSB, ih, List.range_succ, List.map_append, List.reverse_append]
      rfl

theorem length_bitsOfMSB (m k : Nat) : (bitsOfMSB m k).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [bitsOfMSB, ih]

/-- Reading the reversed bits `m - 1, …, 0` of `k` least significant first gives `k` modulo
    `2 ^ m`. -/
theorem bitsToNat_reverse_bitsOfMSB (m k : Nat) :
    bitsToNat (bitsOfMSB m k).reverse = k % 2 ^ m := by
  induction m with
  | zero => simp [bitsOfMSB, bitsToNat, Nat.mod_one]
  | succ m ih =>
      rw [bitsOfMSB, List.reverse_cons, bitsToNat_append, ih, List.length_reverse,
        length_bitsOfMSB, Nat.mod_pow_succ]
      simp only [bitsToNat]
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ m) with h | h <;> simp [h]

end CatCrypt.Crypto.KeyAgreement.X25519.Spec

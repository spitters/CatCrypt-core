/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# The bit-reversal permutation on indices `0 .. 2^w - 1`

The NTT bit-reversal stage permutes the indices of a length-`2^w` vector by
**reversing the `w`-bit binary representation** of each index. The definitions
below give that index permutation abstractly — the index-level counterpart of the
`BitVec.reverse`-based stage eliminated by `BitrevElimPass` — and proves it is
an involution, hence a permutation (bijection) of `Fin (2^w)`.

## Construction

The cleanest representation routes through the `w`-bit list of an index:

* `toBits w i` — the low-bit-first list of the bottom `w` bits of `i`
  (length `w`);
* `fromBits` — interpret a low-bit-first bit list as a natural number.

These are mutually inverse on the relevant domains: `fromBits (toBits w i) =
i % 2^w` (`fromBits_toBits`) and `toBits bs.length (fromBits bs) = bs`
(`toBits_fromBits`). Bit-reversal is then *literally list reversal* of the
bit representation:

```
bitrev w i = fromBits (toBits w i).reverse
```

so the involution `bitrev w (bitrev w i) = i` (for `i < 2^w`) is `List.reverse`
being self-inverse (`List.reverse_reverse`) sandwiched between the two
round-trips. From `Function.Involutive` we get `Function.Bijective` and an
`Equiv.Perm (Fin (2^w))` for free.

Worked example (`w = 3`): `bitrev 3 1 = 4` (`001 ↦ 100`), and
`bitrev 3 (bitrev 3 1) = 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Lattice.BitReversalGeneric

/-- The low-bit-first list of the bottom `w` bits of `i`. Entry `k` is bit `k`
of `i`, so `(toBits w i)[k] = i.testBit k`. -/
def toBits (w i : ℕ) : List Bool :=
  (List.range w).map (fun k => i.testBit k)

/-- Interpret a low-bit-first bit list as a natural number: the head is the
least-significant bit. -/
def fromBits : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * fromBits bs

@[simp] theorem toBits_length (w i : ℕ) : (toBits w i).length = w := by
  simp [toBits]

/-- `fromBits` of a length-`n` list lands below `2^n`. -/
theorem fromBits_lt (bs : List Bool) : fromBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [fromBits]
  | cons b bs ih =>
    simp only [fromBits, List.length_cons, pow_succ]
    rcases b with _ | _ <;> simp <;> omega

/-- Peel the least-significant bit: `toBits (w+1) i` is bit `0` of `i` followed
by the bits of `i / 2`. -/
theorem toBits_succ (w i : ℕ) :
    toBits (w + 1) i = i.testBit 0 :: toBits w (i / 2) := by
  simp only [toBits, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Function.comp, Nat.testBit_succ]

/-- Round-trip: reading back the bottom `w` bits recovers `i mod 2^w`. -/
theorem fromBits_toBits (w i : ℕ) : fromBits (toBits w i) = i % 2 ^ w := by
  induction w generalizing i with
  | zero => simp [toBits, fromBits, Nat.mod_one]
  | succ w ih =>
    rw [toBits_succ, fromBits, ih, Nat.testBit_zero, pow_succ, mul_comm (2 ^ w) 2,
      Nat.mod_mul]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

/-- Inverse round-trip: `toBits` at the list's own length recovers the list. -/
theorem toBits_fromBits (bs : List Bool) :
    toBits bs.length (fromBits bs) = bs := by
  induction bs with
  | nil => simp [toBits, fromBits]
  | cons b bs ih =>
    rw [List.length_cons, toBits_succ, fromBits]
    have hb0 : ((if b then 1 else 0) + 2 * fromBits bs).testBit 0 = b := by
      rw [Nat.testBit_zero]
      rcases b with _ | _ <;> simp
    have hbd : ((if b then 1 else 0) + 2 * fromBits bs) / 2 = fromBits bs := by
      rcases b with _ | _ <;> simp
      omega
    rw [hb0, hbd, ih]

/-- The bit-reversal permutation on indices: reverse the `w`-bit binary
representation of `i`. This is `List.reverse` on the bit list, lifted to
indices through the `toBits`/`fromBits` round-trip. -/
def bitrev (w i : ℕ) : ℕ := fromBits (toBits w i).reverse

/-- Bit-reversal stays within range: `i < 2^w → bitrev w i < 2^w`. -/
theorem bitrev_lt {w i : ℕ} (_h : i < 2 ^ w) : bitrev w i < 2 ^ w := by
  have := fromBits_lt (toBits w i).reverse
  simpa [bitrev, toBits_length] using this

/-- **Involution.** Reversing the `w`-bit representation twice is the
identity on `[0, 2^w)`: `i < 2^w → bitrev w (bitrev w i) = i`. The middle step
is `List.reverse_reverse`. -/
theorem bitrev_bitrev {w i : ℕ} (h : i < 2 ^ w) : bitrev w (bitrev w i) = i := by
  unfold bitrev
  have hlen : (toBits w i).reverse.length = w := by simp
  have key : toBits w (fromBits (toBits w i).reverse) = (toBits w i).reverse := by
    have := toBits_fromBits (toBits w i).reverse
    rwa [hlen] at this
  rw [key, List.reverse_reverse, fromBits_toBits, Nat.mod_eq_of_lt h]

/-- Bit-reversal as an endomorphism of `Fin (2^w)`. -/
def bitrevFin (w : ℕ) (i : Fin (2 ^ w)) : Fin (2 ^ w) :=
  ⟨bitrev w i.1, bitrev_lt i.2⟩

/-- `bitrevFin` is a self-inverse (involution) — immediate from `bitrev_bitrev`,
using each `Fin` element's own `< 2^w` proof. -/
theorem bitrevFin_involutive (w : ℕ) : Function.Involutive (bitrevFin w) := by
  intro i
  ext
  exact bitrev_bitrev i.2

/-- An involution is a bijection, so bit-reversal permutes `Fin (2^w)`. -/
theorem bitrevFin_bijective (w : ℕ) : Function.Bijective (bitrevFin w) :=
  (bitrevFin_involutive w).bijective

/-- Bit-reversal packaged as a permutation `Equiv.Perm (Fin (2^w))`. Its own
inverse, by the involution. -/
def bitrevPerm (w : ℕ) : Equiv.Perm (Fin (2 ^ w)) :=
  (bitrevFin_involutive w).toPerm _

/-- The permutation is its own inverse. -/
@[simp] theorem bitrevPerm_symm (w : ℕ) : (bitrevPerm w).symm = bitrevPerm w := by
  rfl

/-! ## Worked examples (`w = 3`)

`001 ↦ 100`, `010 ↦ 010` (a fixed point), `011 ↦ 110`. -/

example : bitrev 3 1 = 4 := by decide
example : bitrev 3 (bitrev 3 1) = 1 := by decide
example : bitrev 3 2 = 2 := by decide
example : bitrev 3 3 = 6 := by decide

end CatCrypt.Crypto.Lattice.BitReversalGeneric

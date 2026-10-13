/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# FIPS 203 §4.2.1 Compress / Decompress for ML-KEM

Computable `Compress_d` and `Decompress_d` over `ZMod 3329` and `ZMod (2^d)`,
using integer round-half-up (no reals).

For a coefficient `x ∈ Z_q` with `q = 3329`:

* `compress_d d x = round((2^d / q) · x) mod 2^d`, implemented as
  `((2^d · x.val + ⌊q/2⌋) / q) mod 2^d`.
* `decompress_d d y = round((q / 2^d) · y)`, implemented as
  `(q · y.val + ⌊2^d/2⌋) / 2^d`.

FIPS 203 §4.2.1 states two properties of the pair. Compression after decompression
is the identity for `d < 12`, which is `compress_decompress`. Decompression after
compression is approximate: the result differs from the input by at most
`round(q / 2^(d+1)) = (q + 2^d) / 2^(d+1)`, named `errorBound d`, where the difference
is measured modulo `q`, as the distance `centeredAbs` on the circle `ZMod q`; this is
`decompress_compress_centered`. The reduction modulo `2^d` in `compress_d` wraps the
compressed value to `0` exactly when the input lies within `errorBound d` of `q`, and
the distance modulo `q` covers that case. For ML-KEM the parameters are `d_u = 10`
(bound 2) and `d_v = 4` (bound 104).

## Main definitions

* `q` — the ML-KEM modulus `3329`.
* `compress_d d x` — `Compress_d` of FIPS 203 §4.2.1, as
  `((2^d · x.val + ⌊q/2⌋) / q) mod 2^d`.
* `decompress_d d y` — `Decompress_d` of FIPS 203 §4.2.1, as
  `(q · y.val + ⌊2^d/2⌋) / 2^d`.
* `errorBound d` — the bound `round(q / 2^(d+1)) = (q + 2^d) / 2^(d+1)`.
* `centeredAbs z` — the distance of `z : ZMod q` from `0` modulo `q`.

## Main results

* `decompress_compress_centered` — for `1 ≤ d ≤ 12` and every `x : ZMod q`,
  `decompress_d d (compress_d d x)` is within `errorBound d` of `x` in the distance
  modulo `q`.
* `compress_decompress` — for `d < 12` and every `y : ZMod (2^d)`,
  `compress_d d (decompress_d d y) = y`.
* `roundtrip_error_int` — the arithmetic lemma behind the first result: for `d ≥ 1`
  and a natural number `x`, the integer distance between `x` and
  `⌊(3329 · c + 2^d / 2) / 2^d⌋` with `c = ⌊(2^d · x + 1664) / 3329⌋`, the compression
  before reduction modulo `2^d`, is at most `(3329 + 2^d) / (2 · 2^d)`.

## References

* NIST FIPS 203 §4.2.1
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.Compress

/-- ML-KEM modulus. Reducible, so that `ZMod q` unifies with `ZMod 3329`. -/
abbrev q : ℕ := 3329

/-- FIPS 203 Compress_d: round `x ∈ Z_q` to `Z_{2^d}`.

    `Compress_d(x) = round((2^d / q) · x) mod 2^d`. -/
def compress_d (d : ℕ) (x : ZMod q) : ZMod (2 ^ d) :=
  ((2 ^ d * x.val + q / 2) / q : ℕ)

/-- FIPS 203 Decompress_d: map `y ∈ Z_{2^d}` back to `Z_q`.

    `Decompress_d(y) = round((q / 2^d) · y)`. -/
def decompress_d (d : ℕ) (y : ZMod (2 ^ d)) : ZMod q :=
  ((q * y.val + 2 ^ d / 2) / 2 ^ d : ℕ)

/-- The FIPS 203 §4.2.1 round-trip error bound `round(q / 2^(d+1))`. -/
def errorBound (d : ℕ) : ℕ := (q + 2 ^ d) / 2 ^ (d + 1)

/-- The arithmetic of the FIPS 203 §4.2.1 compression error, over natural numbers.

    For a natural number `x`, let `c` be the compression `round((2^d / q) · x)` before
    reduction modulo `2^d` and `x'` the decompression `round((q / 2^d) · c)`. Then
    `|x' - x| ≤ (q + 2^d) / (2 · 2^d)`, the value of `errorBound d`, for `d ≥ 1`.
    `decompress_compress_centered` derives the statement about `compress_d` and
    `decompress_d` from it. -/
theorem roundtrip_error_int (d : ℕ) (hd : 1 ≤ d) (x : ℕ) :
    let n : ℕ := 2 ^ d
    let c : ℕ := (n * x + 1664) / 3329
    let x' : ℕ := (3329 * c + n / 2) / n
    |(x' : ℤ) - x| ≤ ((3329 : ℤ) + n) / (2 * n) := by
  intro n c x'
  -- Make the let-bound `c`, `x'` opaque locals with their defining equations, so the
  -- linear-arithmetic view never confuses `x'` with its (syntactically distinct) quotient.
  have hcdef : c = (n * x + 1664) / 3329 := rfl
  have hx'def : x' = (3329 * c + n / 2) / n := rfl
  clear_value c x'
  -- `n = 2 * k` with `k = 2^(d-1)`, so `n / 2 = k` and no floor-division atom survives.
  obtain ⟨k, hk, hkpos⟩ : ∃ k, n = 2 * k ∧ 0 < k := by
    refine ⟨2 ^ (d - 1), ?_, Nat.two_pow_pos _⟩
    show 2 ^ d = 2 * 2 ^ (d - 1)
    rw [← pow_succ']
    congr 1
    omega
  have hn : 0 < n := by omega
  have hhalf : n / 2 = k := by omega
  -- Obtain the two remainders as opaque bounded ℕ variables (no `%`/`/` survives
  -- into the linear-arithmetic view — that avoids the quotient-form desync).
  obtain ⟨rc, hrc_lt, hrc_eq⟩ : ∃ rc, rc < 3329 ∧ 3329 * c + rc = n * x + 1664 :=
    ⟨(n * x + 1664) % 3329, Nat.mod_lt _ (by norm_num), by
      have h := Nat.div_add_mod (n * x + 1664) 3329; rw [← hcdef] at h; omega⟩
  obtain ⟨rx, hrx_lt, hrx_eq⟩ : ∃ rx, rx < n ∧ n * x' + rx = 3329 * c + k :=
    ⟨(3329 * c + n / 2) % n, Nat.mod_lt _ hn, by
      have h := Nat.div_add_mod (3329 * c + n / 2) n; rw [← hx'def] at h; omega⟩
  -- cast the clean (division-free) facts to ℤ
  have hcZ : (3329 : ℤ) * c + rc = n * x + 1664 := by exact_mod_cast hrc_eq
  have hx'Z : (n : ℤ) * x' + rx = 3329 * c + k := by exact_mod_cast hrx_eq
  have hnZ : (n : ℤ) = 2 * k := by exact_mod_cast hk
  have hcmZ : (rc : ℤ) < 3329 := by exact_mod_cast hrc_lt
  have hx'mZ : (rx : ℤ) < n := by exact_mod_cast hrx_lt
  have hr1 : (0 : ℤ) ≤ (rc : ℤ) := by positivity
  have hr2 : (0 : ℤ) ≤ (rx : ℤ) := by positivity
  have pos : (0 : ℤ) < 2 * n := by positivity
  rw [Int.le_ediv_iff_mul_le pos]
  have key : |(x' : ℤ) - x| * (2 * n) = |((x' : ℤ) - x) * (2 * n)| := by
    rw [abs_mul, abs_of_pos pos]
  rw [key, abs_le]
  -- `(x'-x)·2n = 2·(n·x') - 2·(n·x)`; hx'Z, hcZ pin `n·x'`, `n·x` linearly
  have expand : ((x' : ℤ) - x) * (2 * n) = 2 * ((n : ℤ) * x') - 2 * ((n : ℤ) * x) := by ring
  rw [expand]
  constructor <;> nlinarith [hcZ, hx'Z, hcmZ, hx'mZ, hr1, hr2, hnZ]

/-! ## The round trip in `ZMod q`

`roundtrip_error_int` bounds the compression error of a natural number before the
reduction modulo `2^d` in `compress_d`. That reduction wraps exactly when the input is
within `errorBound d` of `q`, and then the decompressed value is `0`. Both cases are
covered by measuring the error as a distance in `ZMod q`. -/

/-- The distance of `z` from `0` on the circle `ZMod q`: the smaller of its
canonical representative and that representative's complement. -/
def centeredAbs (z : ZMod q) : ℕ := min z.val (q - z.val)

/-- The canonical representatives of `a - b` and of `b` sum to that of `a` modulo
`q`. -/
private lemma val_sub_add_val (a b : ZMod q) :
    ((a - b).val + b.val) % 3329 = a.val % 3329 := by
  have hcast : (((a - b).val + b.val : ℕ) : ZMod q) = ((a.val : ℕ) : ZMod q) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.natCast_val,
      ZMod.cast_id, ZMod.cast_id, ZMod.cast_id]
    ring
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast

/-- A bound on the two one-sided differences of the canonical representatives bounds
the circle distance of the difference. -/
theorem centeredAbs_sub_le (a b : ZMod q) (E : ℕ)
    (hab : a.val ≤ b.val + E) (hba : b.val ≤ a.val + E) :
    centeredAbs (a - b) ≤ E := by
  have ha : a.val < 3329 := ZMod.val_lt a
  have hb : b.val < 3329 := ZMod.val_lt b
  have hv : (a - b).val < 3329 := ZMod.val_lt (a - b)
  have hmod := val_sub_add_val a b
  show min (a - b).val (3329 - (a - b).val) ≤ E
  omega

/-- When the compressed value wraps to zero, closeness of `b` to `q` bounds the
circle distance of `0 - b`. -/
theorem centeredAbs_zero_sub_le (b : ZMod q) (E : ℕ) (h : 3329 ≤ b.val + E) :
    centeredAbs (0 - b) ≤ E := by
  have hb : b.val < 3329 := ZMod.val_lt b
  have hv : ((0 : ZMod q) - b).val < 3329 := ZMod.val_lt _
  have hmod := val_sub_add_val 0 b
  have h0 : (0 : ZMod q).val = 0 := ZMod.val_zero
  show min ((0 : ZMod q) - b).val (3329 - ((0 : ZMod q) - b).val) ≤ E
  omega

/-- FIPS 203 §4.2.1, decompression after compression: `Decompress_d (Compress_d x)`
differs from `x` by at most `round(q / 2^(d+1))` modulo `q`.

For `1 ≤ d ≤ 12` and every `x : ZMod q`, the distance modulo `q` between
`decompress_d d (compress_d d x)` and `x` is at most `errorBound d`. The reduction
modulo `2 ^ d` inside `compress_d` is included: when it wraps, `x` lies within
`errorBound d` of `q` and the decompressed value is `0`.

The bound `d ≤ 12` gives `2 ^ d / 2 < q`, which makes the decompressed natural number
already reduced modulo `q`. It holds for every FIPS 203 compression parameter:
`d_u ∈ {10, 11}`, `d_v ∈ {4, 5}`, `d = 1` for the message encoding and `d = 12` for
the 12-bit byte encoding. -/
theorem decompress_compress_centered (d : ℕ) (hd : 1 ≤ d) (hd12 : d ≤ 12) (x : ZMod q) :
    centeredAbs (decompress_d d (compress_d d x) - x) ≤ errorBound d := by
  have : NeZero (2 ^ d) := ⟨by positivity⟩
  have hn : 0 < 2 ^ d := Nat.two_pow_pos d
  have hnle : 2 ^ d ≤ 4096 := by
    calc 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd12
      _ = 4096 := by norm_num
  have hv : x.val < 3329 := ZMod.val_lt x
  have h1664 : (3329 : ℕ) / 2 = 1664 := by norm_num
  have hEB : errorBound d = (3329 + 2 ^ d) / (2 * 2 ^ d) := by
    show (3329 + 2 ^ d) / 2 ^ (d + 1) = (3329 + 2 ^ d) / (2 * 2 ^ d)
    rw [pow_succ, Nat.mul_comm]
  have hc0_lt : (2 ^ d * x.val + 1664) / 3329 < 2 ^ d + 1 := by
    apply Nat.div_lt_of_lt_mul
    have h1 : 2 ^ d * x.val ≤ 2 ^ d * 3328 := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (compress_d d x).val = c := ⟨_, rfl⟩
  have hc_lt : c < 2 ^ d := hc ▸ ZMod.val_lt _
  have hcomp : c = ((2 ^ d * x.val + 1664) / 3329) % 2 ^ d := by
    rw [← hc]
    show (((2 ^ d * x.val + 3329 / 2) / 3329 : ℕ) : ZMod (2 ^ d)).val = _
    rw [h1664, ZMod.val_natCast]
  have hdec : (decompress_d d (compress_d d x)).val
      = (3329 * c + 2 ^ d / 2) / 2 ^ d := by
    have hlt : (3329 * c + 2 ^ d / 2) / 2 ^ d < 3329 := by
      apply Nat.div_lt_of_lt_mul
      omega
    show (((3329 * (compress_d d x).val + 2 ^ d / 2) / 2 ^ d : ℕ) : ZMod q).val = _
    rw [hc, ZMod.val_natCast_of_lt hlt]
  have step : ∀ u w : ℕ,
      ((u : ℤ) - (w : ℤ)) * (2 * ((2 ^ d : ℕ) : ℤ)) ≤ 3329 + ((2 ^ d : ℕ) : ℤ) →
      u ≤ w + errorBound d := by
    intro u w h
    rcases Nat.le_total u w with hle | hle
    · omega
    · have hcast : ((u - w : ℕ) : ℤ) = (u : ℤ) - (w : ℤ) := by
        push_cast [Nat.cast_sub hle]; ring
      have h' : (((u - w) * (2 * 2 ^ d) : ℕ) : ℤ) ≤ ((3329 + 2 ^ d : ℕ) : ℤ) := by
        push_cast
        rw [hcast]
        exact h
      have hnat : (u - w) * (2 * 2 ^ d) ≤ 3329 + 2 ^ d := by exact_mod_cast h'
      have hdivle := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * 2 ^ d)).mpr hnat
      have h2 := Nat.sub_le_iff_le_add.mp hdivle
      rw [hEB]
      omega
  rcases Nat.lt_or_ge ((2 ^ d * x.val + 1664) / 3329) (2 ^ d) with hlt | hge
  · -- no wrap: the bound of `roundtrip_error_int` applies directly
    have hceq : c = (2 ^ d * x.val + 1664) / 3329 := by
      rw [hcomp, Nat.mod_eq_of_lt hlt]
    have hmain : |((((3329 * ((2 ^ d * x.val + 1664) / 3329) + 2 ^ d / 2) / 2 ^ d : ℕ)) : ℤ)
        - ((x.val : ℕ) : ℤ)|
        ≤ ((3329 : ℤ) + ((2 ^ d : ℕ) : ℤ)) / (2 * ((2 ^ d : ℕ) : ℤ)) :=
      roundtrip_error_int d hd x.val
    rw [← hceq] at hmain
    have h2n : (0 : ℤ) < 2 * ((2 ^ d : ℕ) : ℤ) := by positivity
    rw [Int.le_ediv_iff_mul_le h2n] at hmain
    have key : |(((3329 * c + 2 ^ d / 2) / 2 ^ d : ℕ) : ℤ) - ((x.val : ℕ) : ℤ)|
        * (2 * ((2 ^ d : ℕ) : ℤ))
        = |((((3329 * c + 2 ^ d / 2) / 2 ^ d : ℕ) : ℤ) - ((x.val : ℕ) : ℤ))
            * (2 * ((2 ^ d : ℕ) : ℤ))| := by
      rw [abs_mul, abs_of_pos h2n]
    rw [key, abs_le] at hmain
    obtain ⟨hlo, hhi⟩ := hmain
    refine centeredAbs_sub_le _ _ _ ?_ ?_
    · rw [hdec]
      exact step _ _ hhi
    · rw [hdec]
      refine step _ _ ?_
      linarith
  · -- wrap: the compressed value is `0` and `x` lies close to `q`
    have hc0n : (2 ^ d * x.val + 1664) / 3329 = 2 ^ d := by omega
    have hc0 : c = 0 := by rw [hcomp, hc0n, Nat.mod_self]
    have hyz : (3329 * c + 2 ^ d / 2) / 2 ^ d = 0 := by
      rw [hc0]
      exact Nat.div_eq_of_lt (by omega)
    have hzero : decompress_d d (compress_d d x) = 0 := by
      have h := (ZMod.natCast_zmod_val (decompress_d d (compress_d d x))).symm
      rw [hdec, hyz] at h
      simpa using h
    have hgapmul : 2 ^ d * 3329 ≤ 2 ^ d * x.val + 1664 :=
      (Nat.le_div_iff_mul_le (by norm_num)).mp (le_of_eq hc0n.symm)
    have hgap : 2 ^ d * (3329 - x.val) ≤ 1664 := by
      rw [Nat.mul_sub]
      omega
    have hclose : 3329 ≤ x.val + errorBound d := by
      have hstep : (3329 - x.val) * (2 * 2 ^ d) ≤ 3329 + 2 ^ d := by
        have hre : (3329 - x.val) * (2 * 2 ^ d) = 2 * (2 ^ d * (3329 - x.val)) := by ring
        rw [hre]
        omega
      have hdivle := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * 2 ^ d)).mpr hstep
      rw [hEB]
      omega
    rw [hzero]
    exact centeredAbs_zero_sub_le x _ hclose

/-- FIPS 203 §4.2.1, compression after decompression: `Compress_d (Decompress_d y) = y`
for `d < 12` and every `y : ZMod (2 ^ d)`. -/
theorem compress_decompress (d : ℕ) (hd : d < 12) (y : ZMod (2 ^ d)) :
    compress_d d (decompress_d d y) = y := by
  have : NeZero (2 ^ d) := ⟨by positivity⟩
  have h1664 : (3329 : ℕ) / 2 = 1664 := by norm_num
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 ^ d = n := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ, y.val = c := ⟨_, rfl⟩
  have hyd : c < 2 ^ d := hc ▸ ZMod.val_lt y
  have hy : c < n := hn ▸ hyd
  have hnle : n ≤ 2048 := by
    rw [← hn]
    calc 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hn0 : 0 < n := by omega
  have hdm := Nat.div_add_mod (3329 * c + n / 2) n
  have hrx := Nat.mod_lt (3329 * c + n / 2) hn0
  generalize hx' : (3329 * c + n / 2) / n = x' at hdm
  generalize (3329 * c + n / 2) % n = rx at hdm hrx
  have hx'lt : x' < 3329 := by
    rw [← hx']
    apply Nat.div_lt_of_lt_mul
    omega
  have hdec : (decompress_d d y).val = x' := by
    show (((3329 * y.val + 2 ^ d / 2) / 2 ^ d : ℕ) : ZMod q).val = x'
    rw [hc, hn, hx', ZMod.val_natCast_of_lt hx'lt]
  have hdiv : (2 ^ d * x' + 1664) / 3329 = c := by
    rw [hn]
    apply Nat.div_eq_of_lt_le <;> omega
  have hval : (compress_d d (decompress_d d y)).val = c := by
    show (((2 ^ d * (decompress_d d y).val + 3329 / 2) / 3329 : ℕ) : ZMod (2 ^ d)).val = c
    rw [hdec, h1664, hdiv, ZMod.val_natCast_of_lt hyd]
  apply ZMod.val_injective
  rw [hval, hc]

end CatCrypt.Crypto.MLKEM.Compress

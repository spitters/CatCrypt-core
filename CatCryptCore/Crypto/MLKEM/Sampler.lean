/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Util.ZMod3329

/-!
# FIPS 203 ML-KEM samplers over the owned sponge

Computable reference implementations of the two ML-KEM coefficient samplers,
producing polynomials over the prime field `Zq3329 := ZMod 3329`:

* `sampleNTT` — FIPS 203 Algorithm 7 (`SampleNTT`): rejection sampling of an
  NTT-domain polynomial from a SHAKE-128 XOF byte stream.
* `sampleCBD_eta` — FIPS 203 Algorithm 8 (`SamplePolyCBD_eta`): the centered
  binomial sampler for the noise polynomials, from a `64 * eta`-byte PRF stream.

Both operate on the byte output of the owned sponge (`Crypto/Hash/SHAKE.lean`,
`Crypto/Hash/Keccak.lean`): `sampleNTT` consumes the SHAKE-128 XOF squeeze of
the seed `rho ‖ i ‖ j`; `sampleCBD_eta` consumes the SHAKE-256 PRF squeeze of
`sigma ‖ N`. The byte stream is passed in explicitly so these definitions stay
computable and axiom-free — the caller supplies the squeezed prefix.

## API

* `rejNTT` — the list-consuming rejection core of Algorithm 7.
* `sampleNTT` — Algorithm 7 packaged as `Fin 256 → Zq3329`.
* `SampleNTTFills` — the adequacy statement: the stream yields ≥ 256 accepted
  coefficients (met by a long-enough XOF prefix).
* `bitsLE` — little-endian bit expansion of a byte list (FIPS 203 `BytesToBits`).
* `sumBits`, `cbdCoeff` — the per-coefficient centered-binomial value.
* `sampleCBD_eta` — Algorithm 8 packaged as `Fin 256 → Zq3329`.
* `cbdCoeff_bound` — the range property `-eta ≤ coeff ≤ eta`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Util

namespace CatCrypt.Crypto.MLKEM.Sampler

/-- The ML-KEM prime field `Z/3329Z`. -/
abbrev Zq : Type := Zq3329

/-- FIPS 203 modulus `q = 3329`. -/
def q : Nat := 3329

/-! ## Algorithm 7 — `SampleNTT` (rejection sampling) -/

/-- The rejection core of FIPS 203 Algorithm 7. Consume the XOF byte stream in
three-byte groups; each group yields two 12-bit candidates
`d1 = b0 + 256 * (b1 mod 16)` and `d2 = (b1 div 16) + 16 * b2`; a candidate is
kept iff it is `< q`. Accepted coefficients are returned in stream order.

This is list-consuming rather than fuel-bounded: the recursion terminates on the
finite input list, so no explicit fuel is needed. A caller squeezes enough XOF
bytes that at least 256 coefficients are accepted (see `SampleNTTFills`). -/
def rejNTT : List UInt8 → List Zq
  | b0 :: b1 :: b2 :: rest =>
      let x0 := b0.toNat
      let x1 := b1.toNat
      let x2 := b2.toNat
      let d1 := x0 + 256 * (x1 % 16)
      let d2 := (x1 / 16) + 16 * x2
      let tail := rejNTT rest
      let tail := if d2 < q then (Zq3329.fromNat d2) :: tail else tail
      if d1 < q then (Zq3329.fromNat d1) :: tail else tail
  | _ => []

/-- FIPS 203 Algorithm 7 as a polynomial `Fin 256 → Zq3329`: read the first 256
accepted coefficients of the rejection stream, padding with `0` should the
supplied prefix fall short (an adequate XOF prefix never triggers padding — see
`SampleNTTFills`). -/
def sampleNTT (xofStream : List UInt8) : Fin 256 → Zq :=
  fun i => (rejNTT xofStream).getD i.val (Zq3329.fromNat 0)

/-- Adequacy of a SHAKE-128 XOF prefix for Algorithm 7: the rejection sampler
accepts at least 256 coefficients, so `sampleNTT` reads real coefficients for
every index and never falls back to the `0` default. A sufficiently long XOF
squeeze satisfies this with overwhelming probability. -/
def SampleNTTFills (xofStream : List UInt8) : Prop :=
  256 ≤ (rejNTT xofStream).length

/-- When the stream is adequate, `sampleNTT` reads the `i`-th accepted
coefficient directly (no default padding). -/
theorem sampleNTT_of_fills (xofStream : List UInt8)
    (h : SampleNTTFills xofStream) (i : Fin 256) :
    sampleNTT xofStream i = (rejNTT xofStream)[i.val]'(lt_of_lt_of_le i.isLt h) := by
  unfold sampleNTT
  have hlt : i.val < (rejNTT xofStream).length := lt_of_lt_of_le i.isLt h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]

/-! ## Algorithm 8 — `SamplePolyCBD_eta` (centered binomial) -/

/-- FIPS 203 `BytesToBits`: expand a byte list to its bit list, least-significant
bit first within each byte. Byte `b` contributes bits `b_0, …, b_7` with
`b_j = (b >>> j) &&& 1`. -/
def bitsLE (bytes : List UInt8) : List Nat :=
  (bytes.map (fun b => (List.range 8).map (fun j => (b.toNat >>> j) &&& 1))).flatten

/-- Every bit produced by `bitsLE` is `0` or `1`. -/
theorem bitsLE_mem_le (bytes : List UInt8) : ∀ x ∈ bitsLE bytes, x ≤ 1 := by
  intro x hx
  unfold bitsLE at hx
  simp only [List.mem_flatten, List.mem_map] at hx
  obtain ⟨l, ⟨b, _, rfl⟩, hxl⟩ := hx
  simp only [List.mem_map] at hxl
  obtain ⟨j, _, rfl⟩ := hxl
  exact Nat.and_le_right

/-- A defaulted read of `bitsLE` is bounded by `1` at every index. -/
theorem bitsLE_getD_le (bytes : List UInt8) (k : Nat) :
    (bitsLE bytes).getD k 0 ≤ 1 := by
  by_cases hk : k < (bitsLE bytes).length
  · have hget : (bitsLE bytes).getD k 0 = (bitsLE bytes)[k] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rw [hget]
    exact bitsLE_mem_le bytes _ (List.getElem_mem hk)
  · have hge : (bitsLE bytes).length ≤ k := by omega
    have hnone : (bitsLE bytes)[k]? = none := List.getElem?_eq_none hge
    have hzero : (bitsLE bytes).getD k 0 = 0 := by
      simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    rw [hzero]
    omega

/-- Sum of `len` consecutive bits of `bits` starting at index `start`. -/
def sumBits (bits : List Nat) (start len : Nat) : Nat :=
  ((List.range len).map (fun j => bits.getD (start + j) 0)).sum

/-- A window of `len` bits sums to at most `len` when every entry is `≤ 1`. -/
theorem sumBits_le (bits : List Nat) (start len : Nat)
    (h : ∀ k, bits.getD k 0 ≤ 1) : sumBits bits start len ≤ len := by
  unfold sumBits
  calc ((List.range len).map (fun j => bits.getD (start + j) 0)).sum
      ≤ ((List.range len).map (fun _ => 1)).sum := by
        apply List.sum_le_sum
        intro j _
        exact h (start + j)
    _ = len := by simp

/-- The `i`-th centered-binomial coefficient (FIPS 203 Algorithm 8): the sum of
`eta` bits minus the sum of the following `eta` bits, taken from the bit stream
of the PRF output at offset `2 * eta * i`. -/
def cbdCoeff (eta : Nat) (bits : List Nat) (i : Nat) : Int :=
  (sumBits bits (2 * eta * i) eta : Int) - (sumBits bits (2 * eta * i + eta) eta : Int)

/-- FIPS 203 Algorithm 8 as a polynomial `Fin 256 → Zq3329`: expand the
`64 * eta`-byte PRF stream to bits, then map each coefficient into the field. -/
def sampleCBD_eta (eta : Nat) (prf_bytes : List UInt8) : Fin 256 → Zq :=
  let bits := bitsLE prf_bytes
  fun i => Zq3329.fromInt (cbdCoeff eta bits i.val)

/-- Range of the centered-binomial coefficient: `-eta ≤ cbdCoeff ≤ eta` for the
bit stream of any PRF output. -/
theorem cbdCoeff_bound (eta : Nat) (bytes : List UInt8) (i : Nat) :
    -(eta : Int) ≤ cbdCoeff eta (bitsLE bytes) i
      ∧ cbdCoeff eta (bitsLE bytes) i ≤ (eta : Int) := by
  have ha := sumBits_le (bitsLE bytes) (2 * eta * i) eta (bitsLE_getD_le bytes)
  have hb := sumBits_le (bitsLE bytes) (2 * eta * i + eta) eta (bitsLE_getD_le bytes)
  unfold cbdCoeff
  omega

end CatCrypt.Crypto.MLKEM.Sampler

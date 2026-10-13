/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# Generic radix-2 Cooley–Tukey decimation-in-time recursion step

The arithmetic core of the radix-2 number-theoretic transform, proved over a
*generic* commutative ring `R` and a *generic* size `n`. The concrete
`NTT4PointPass` and `NTT8PointPass` are unrollings of the single recursion step
proved here, rather than separately hand-derived networks.

## Objects

* `dft n ω x k = Σⱼ x j · ωʲᵏ` — the definitional length-`n` discrete /
  number-theoretic transform, a `Finset.sum` over `Fin n`.
* `evenPart`, `oddPart` — the even- and odd-indexed sub-sequences of a length-`2n`
  input, each a `Fin n → R`.

## The recursion step

`dft_even_odd_split` is the standard decimation-in-time (DIT) butterfly
recurrence:

`dft (2n) ω x (k ↑ to Fin (2n)) = dft n (ω²) (evenPart x) k + ωᵏ · dft n (ω²) (oddPart x) k`

i.e. `Xₖ = Eₖ + ωᵏ Oₖ`, where `E` is the half-length DFT of the even-indexed
inputs and `O` the half-length DFT of the odd-indexed inputs, both at the
squared twiddle `ω²`. **No root-of-unity hypothesis is needed** — the identity is
pure index arithmetic: `ω^(2jk) = (ω²)^(jk)` factors the even lane and `ω^k`
factors out of the odd lane. The full radix-2 network is obtained by recursing on
`E` and `O` and combining via the `ctButterfly` of `NTTButterflyPass` (the
twiddle-cancellation step); the root-of-unity hypothesis enters only when one
folds the upper half (`X_{k+n} = E_k − ωᵏ O_k`), as exhibited concretely in
`NTT4PointPass` / `NTT8PointPass`.

## Sum-split mechanism

The even/odd separation is `sum_range_two_mul` (a self-contained induction on
`n`), reached from the `Fin (2n)` sum via `Fin.sum_univ_eq_sum_range`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Lattice.NTTRecursionPass

open Finset

variable {R : Type*} [CommRing R]

/-- Generic length-`n` discrete / number-theoretic transform:
`Xₖ = Σⱼ xⱼ ωʲᵏ`, a `Finset.sum` over `Fin n`. No relation on `ω` is assumed by
the definition. -/
def dft (n : ℕ) (ω : R) (x : Fin n → R) (k : Fin n) : R :=
  ∑ j : Fin n, x j * ω ^ (j.val * k.val)

/-- Even-indexed sub-sequence of a length-`2n` input: `(evenPart x) i = x (2i)`. -/
def evenPart {n : ℕ} (x : Fin (2 * n) → R) (i : Fin n) : R :=
  x ⟨2 * i.val, by omega⟩

/-- Odd-indexed sub-sequence of a length-`2n` input: `(oddPart x) i = x (2i+1)`. -/
def oddPart {n : ℕ} (x : Fin (2 * n) → R) (i : Fin n) : R :=
  x ⟨2 * i.val + 1, by omega⟩

/-! ## Even/odd range-sum split (self-contained) -/

/-- Sum over `range (2 * n)` decomposes as the even-indexed entries plus the
odd-indexed entries. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i
      = (∑ i ∈ range n, f (2 * i)) + (∑ i ∈ range n, f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k) + 1 + 1 := by ring
    rw [h2, sum_range_succ, sum_range_succ, ih,
        sum_range_succ (fun i => f (2 * i)) k,
        sum_range_succ (fun i => f (2 * i + 1)) k]
    abel

/-! ## The Cooley–Tukey decimation-in-time recursion step -/

/-- **Generic radix-2 DIT recursion step.** For any length-`2n` input `x`,
twiddle `ω`, and lower-half index `k : Fin n` (cast into `Fin (2n)` via
`Fin.castLE`):

`dft (2n) ω x (k↑) = dft n (ω²) (evenPart x) k + ωᵏ · dft n (ω²) (oddPart x) k`.

This is the standard `Xₖ = Eₖ + ωᵏ Oₖ` butterfly recurrence. It needs **no**
root-of-unity hypothesis: `ω^(2jk) = (ω²)^(jk)` factors the even lane and the
odd lane carries the extra `ω^k`. The concrete `ntt4`/`ntt8` networks are
unrollings of this step. -/
theorem dft_even_odd_split {n : ℕ} (ω : R) (x : Fin (2 * n) → R) (k : Fin n) :
    dft (2 * n) ω x (Fin.castLE (by omega) k)
      = dft n (ω ^ 2) (evenPart x) k
        + ω ^ k.val * dft n (ω ^ 2) (oddPart x) k := by
  -- A padded summand `g : ℕ → R` that agrees with the `Fin (2n)` term on
  -- `j < 2n` and is `0` elsewhere, so the `Fin (2n)` sum is a `range (2n)` sum.
  set kk : ℕ := k.val with hkk
  have hcast : (Fin.castLE (by omega : n ≤ 2 * n) k).val = kk := rfl
  set g : ℕ → R :=
    fun j => (if h : j < 2 * n then x ⟨j, h⟩ else 0) * ω ^ (j * kk) with hg
  -- LHS as a range sum.
  have hLHS : dft (2 * n) ω x (Fin.castLE (by omega) k) = ∑ j ∈ range (2 * n), g j := by
    rw [dft]
    rw [← Fin.sum_univ_eq_sum_range g (2 * n)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hg, hcast, j.isLt, dif_pos]
  rw [hLHS, sum_range_two_mul g n]
  -- Even lane = E_k.
  have hEven : (∑ i ∈ range n, g (2 * i)) = dft n (ω ^ 2) (evenPart x) k := by
    rw [dft, ← Fin.sum_univ_eq_sum_range (fun i => g (2 * i)) n]
    apply Finset.sum_congr rfl
    intro i _
    have hi : 2 * i.val < 2 * n := by omega
    simp only [hg, evenPart, hi, dif_pos]
    rw [hkk, ← pow_mul]
    ring_nf
  -- Odd lane = ωᵏ · O_k.
  have hOdd : (∑ i ∈ range n, g (2 * i + 1))
      = ω ^ kk * dft n (ω ^ 2) (oddPart x) k := by
    rw [dft, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i => g (2 * i + 1)) n]
    apply Finset.sum_congr rfl
    intro i _
    have hi : 2 * i.val + 1 < 2 * n := by omega
    simp only [hg, oddPart, hi, dif_pos]
    rw [hkk, ← pow_mul]
    ring_nf
  rw [hEven, hOdd, hkk]

/-- **Upper-half companion of the DIT recursion step.** With `ω` a `2n`-th root
of unity (`ω^(2n) = 1`), the output at index `k + n` reuses the *same* half-DFTs
`E`, `O` as the lower-half output at index `k`:

`dft (2n) ω x (k+n) = dft n (ω²) (evenPart x) k + ωⁿ · ωᵏ · dft n (ω²) (oddPart x) k`.

The even lane is unchanged because `ω^(2in) = (ω^(2n))ⁱ = 1`; the odd lane picks
up the extra factor `ωⁿ` (which is `−1` for a primitive `2n`-th root, giving the
`Eₖ − ωᵏ Oₖ` butterfly). Together with `dft_even_odd_split` this is the full
radix-2 butterfly: both halves are computed from one pair of half-length
transforms, exactly the structure `ntt4`/`ntt8` unroll. -/
theorem dft_upper_split {n : ℕ} (ω : R) (hω : ω ^ (2 * n) = 1)
    (x : Fin (2 * n) → R) (k : Fin n) :
    dft (2 * n) ω x ⟨k.val + n, by omega⟩
      = dft n (ω ^ 2) (evenPart x) k
        + ω ^ n * ω ^ k.val * dft n (ω ^ 2) (oddPart x) k := by
  set kk : ℕ := k.val with hkk
  set g : ℕ → R :=
    fun j => (if h : j < 2 * n then x ⟨j, h⟩ else 0) * ω ^ (j * (kk + n)) with hg
  have hLHS : dft (2 * n) ω x ⟨k.val + n, by omega⟩ = ∑ j ∈ range (2 * n), g j := by
    rw [dft]
    rw [← Fin.sum_univ_eq_sum_range g (2 * n)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hg, j.isLt, dif_pos, hkk]
  rw [hLHS, sum_range_two_mul g n]
  -- Even lane: `ω^(2i·n) = (ω^(2n))ⁱ = 1`, so the even lane is again `E_k`.
  have hEven : (∑ i ∈ range n, g (2 * i)) = dft n (ω ^ 2) (evenPart x) k := by
    rw [dft, ← Fin.sum_univ_eq_sum_range (fun i => g (2 * i)) n]
    apply Finset.sum_congr rfl
    intro i _
    have hi : 2 * i.val < 2 * n := by omega
    simp only [hg, evenPart, hi, dif_pos]
    have hpow : ω ^ (2 * i.val * (kk + n)) = (ω ^ 2) ^ (i.val * kk) := by
      have hexp : 2 * i.val * (kk + n) = 2 * (i.val * kk) + (2 * n) * i.val := by ring
      rw [hexp, pow_add, pow_mul ω 2, pow_mul ω (2 * n), hω, one_pow, mul_one]
    rw [hpow]
  -- Odd lane: extra factor `ω^((2i+1)·n) = (ω^(2n))ⁱ · ωⁿ = ωⁿ`.
  have hOdd : (∑ i ∈ range n, g (2 * i + 1))
      = ω ^ n * ω ^ kk * dft n (ω ^ 2) (oddPart x) k := by
    rw [dft, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i => g (2 * i + 1)) n]
    apply Finset.sum_congr rfl
    intro i _
    have hi : 2 * i.val + 1 < 2 * n := by omega
    simp only [hg, oddPart, hi, dif_pos]
    have hpow : ω ^ ((2 * i.val + 1) * (kk + n))
        = ω ^ n * ω ^ kk * (ω ^ 2) ^ (i.val * kk) := by
      have hexp : (2 * i.val + 1) * (kk + n)
          = n + kk + (2 * (i.val * kk) + (2 * n) * i.val) := by ring
      rw [hexp, pow_add, pow_add, pow_add, pow_mul ω 2, pow_mul ω (2 * n),
        hω, one_pow, mul_one]
    rw [hpow]; ring
  rw [hEven, hOdd, hkk]

/-! ## Base case: the length-2 DFT is the radix-2 butterfly -/

/-- The base case the recursion bottoms out at: the length-2 DFT is exactly the
Cooley–Tukey butterfly `(x₀ + x₁, x₀ + ω·x₁)`. Recursing `dft_even_odd_split` /
`dft_upper_split` down to size 2 and combining with this base case reproduces the
explicit `ntt4`/`ntt8` networks. -/
theorem dft_two (ω : R) (x : Fin 2 → R) :
    dft 2 ω x 0 = x 0 + x 1 ∧ dft 2 ω x 1 = x 0 + ω * x 1 := by
  refine ⟨?_, ?_⟩
  · simp [dft, Fin.sum_univ_two]
  · simp [dft, Fin.sum_univ_two]; ring

end CatCrypt.Crypto.Lattice.NTTRecursionPass

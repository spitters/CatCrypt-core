/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Lattice.NegacyclicTransformGeneric

/-!
# The twist-defined negacyclic convolution is the explicit signed convolution

`NegacyclicTransformGeneric.lean` *defines* negacyclic convolution as
`negaConv ψ = untwist ∘ cyclicConv ∘ twist` — the clean diagonalizable object,
deferring the identification with the textbook signed convolution on
`R[X]/(Xⁿ+1)`. This file discharges that deferred identification.

With `ψ` a primitive `2n`-th root of unity (so `ψⁿ = −1`), the twist exponents
of the two operands combine, after the outer `untwist`, into a `+1`/`−1` sign:
`+xᵢ y_{k−i}` when the `Fin n` index does **not** wrap (`i.val ≤ k.val`) and
`−xᵢ y_{k−i}` when it does. That signed sum is exactly the negacyclic
convolution `signedNegaConv`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Lattice.SignedNegacyclicConv

open Finset
open CatCrypt.Crypto.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Lattice.NegacyclicTransformGeneric

/-- The explicit **signed** negacyclic convolution (multiplication in
`R[X]/(Xⁿ+1)`): `(x ⋆ y) k = Σᵢ ±xᵢ · y_{k−i}` over `Fin n` subtraction, with the
sign `−1` exactly when the index wraps (`i.val > k.val`) and `+1` otherwise.
Defined over any commutative ring, so that it is the ring multiplication for
`ZMod q` at every `q`, prime or not; the identification with the twist-defined
`negaConv` below needs a field. -/
def signedNegaConv {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (x y : Fin n → R) : Fin n → R :=
  fun k => ∑ i : Fin n,
    (if i.val ≤ k.val then x i * y (k - i) else - (x i * y (k - i)))

variable {R : Type*} [Field R] {ψ : R} {n : ℕ} [NeZero n]

/-- A primitive `2n`-th root of unity satisfies `ψⁿ = −1`: `(ψⁿ)² = ψ^{2n} = 1`
forces `ψⁿ ∈ {1, −1}`, and `ψⁿ = 1` is ruled out by primitivity (`0 < n < 2n`). -/
lemma psi_pow_n (hψ : IsPrimitiveRoot ψ (2 * n)) : ψ ^ n = -1 := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsq : (ψ ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm n 2]
    exact hψ.pow_eq_one
  have hne : ψ ^ n ≠ 1 :=
    hψ.pow_ne_one_of_pos_of_lt hn0.ne' (by omega)
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact absurd h hne
  · exact h

/-- The combined twist/untwist ψ-power factor on the `(i, k)` lane collapses to a
sign: `ψ^{i.val} · ψ^{(k−i).val} · (ψ⁻¹)^{k.val} = ±1`, with `+1` when the `Fin n`
index does not wrap and `−1` when it does. This is the `ψⁿ = −1` bookkeeping. -/
lemma twist_pow_factor (hψ : IsPrimitiveRoot ψ (2 * n)) (i k : Fin n) :
    ψ ^ (i.val) * ψ ^ ((k - i).val) * (ψ⁻¹) ^ (k.val)
      = if i.val ≤ k.val then (1 : R) else -1 := by
  have h2n : 0 < 2 * n := by
    have := Nat.pos_of_ne_zero (NeZero.ne n); omega
  have hψ0 : ψ ≠ 0 := by
    intro h
    have h1 : (0 : R) ^ (2 * n) = 1 := h ▸ hψ.pow_eq_one
    rw [zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hinv : (ψ⁻¹) ^ (k.val) = (ψ ^ (k.val))⁻¹ := by
    rw [inv_pow]
  have hk : k.val < n := k.is_lt
  have hi : i.val < n := i.is_lt
  rw [Fin.val_sub]
  by_cases hik : i.val ≤ k.val
  · -- no wrap: (n - i + k) % n = k - i, exponents sum to k
    rw [ite_eq_left hik]
    have hlt : (n - i.val + k.val) % n = k.val - i.val := by
      rw [show n - i.val + k.val = (k.val - i.val) + 1 * n by omega,
        Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hlt, hinv, ← pow_add]
    rw [show i.val + (k.val - i.val) = k.val by omega]
    rw [mul_inv_cancel₀ (pow_ne_zero _ hψ0)]
  · -- wrap: (n - i + k) % n = n - i + k (since < n), exponents sum to n + k
    rw [ite_eq_right hik]
    have hik' : k.val < i.val := Nat.lt_of_not_le hik
    have hlt : (n - i.val + k.val) % n = n - i.val + k.val := by
      apply Nat.mod_eq_of_lt; omega
    rw [hlt, hinv, ← pow_add]
    rw [show i.val + (n - i.val + k.val) = n + k.val by omega]
    rw [pow_add, psi_pow_n hψ]
    rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hψ0), mul_one]

/-- **The deferred `ψⁿ = −1` identification**: the twist-defined negacyclic
convolution `negaConv = untwist ∘ cyclicConv ∘ twist` equals the explicit signed
convolution on `R[X]/(Xⁿ+1)`, when `ψ` is a primitive `2n`-th root of unity. The
per-lane twist exponents combine, after the outer untwist, into the `±1`
wraparound sign of `signedNegaConv`. -/
theorem negaConv_eq_signed (hψ : IsPrimitiveRoot ψ (2 * n)) (x y : Fin n → R) :
    negaConv ψ x y = signedNegaConv x y := by
  funext k
  simp only [negaConv, signedNegaConv, untwist, cyclicConv, twist, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show x i * ψ ^ i.val * (y (k - i) * ψ ^ (k - i).val) * (ψ⁻¹) ^ k.val
        = (x i * y (k - i)) * (ψ ^ i.val * ψ ^ (k - i).val * (ψ⁻¹) ^ k.val) by ring]
  rw [twist_pow_factor hψ i k]
  by_cases hik : i.val ≤ k.val
  · rw [ite_eq_left hik, ite_eq_left hik, mul_one]
  · rw [ite_eq_right hik, ite_eq_right hik, mul_neg_one]

end CatCrypt.Crypto.Lattice.SignedNegacyclicConv

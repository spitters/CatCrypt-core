/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Optimizer.Lattice.NTTRecursionPass
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The DFT diagonalizes cyclic convolution

This is the algebraic reason number-theoretic-transform (NTT) based polynomial
multiplication works: pointwise multiplication of two length-`n` DFTs equals the
DFT of their length-`n` *cyclic* convolution (multiplication in `R[X]/(Xⁿ−1)`).

Over a commutative ring `R` with a primitive `n`-th root of unity `ω`,

`dft n ω (cyclicConv n x y) k = dft n ω x k * dft n ω y k`.

The proof reindexes the inner convolution sum by the bijection `j ↦ j + i` on
`Fin n` and uses `ω ^ (a % n) = ω ^ a` (a consequence of `ω ^ n = 1`) to undo the
modular wraparound introduced by `Fin n` addition.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric

open Finset
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass

variable {R : Type*} [CommRing R]

/-- Length-`n` cyclic convolution (multiplication in `R[X]/(Xⁿ−1)`):
`(x ⋆ y) k = Σᵢ xᵢ · y_{k−i}`, where `k − i` is subtraction in `Fin n` (mod `n`). -/
def cyclicConv (n : ℕ) [NeZero n] (x y : Fin n → R) : Fin n → R :=
  fun k => ∑ i : Fin n, x i * y (k - i)

/-- `ω ^ (a % n) = ω ^ a` when `ω ^ n = 1`: the modular wraparound of `Fin n`
addition is invisible to the twiddle `ω`. -/
private lemma ω_pow_mod {ω : R} {n : ℕ} (hn : ω ^ n = 1) (a : ℕ) :
    ω ^ (a % n) = ω ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, hn, one_pow, one_mul]

/-- The wraparound `% n` introduced by `Fin n` addition is invisible to `ω` even
inside the `· * k` twiddle exponent: `ω ^ ((a % n) * b) = ω ^ (a * b)`. -/
private lemma ω_pow_mod_mul {ω : R} {n : ℕ} (hn : ω ^ n = 1) (a b : ℕ) :
    ω ^ ((a % n) * b) = ω ^ (a * b) := by
  rw [pow_mul, pow_mul, ω_pow_mod hn]

/-- **Cyclic convolution theorem**: the DFT diagonalizes cyclic convolution.
Pointwise product of the two transforms equals the transform of the cyclic
convolution. This is why NTT-based multiplication is correct. -/
theorem dft_cyclicConv {ω : R} {n : ℕ} [NeZero n] (hω : IsPrimitiveRoot ω n)
    (x y : Fin n → R) (k : Fin n) :
    dft n ω (cyclicConv n x y) k = dft n ω x k * dft n ω y k := by
  have hn : ω ^ n = 1 := hω.pow_eq_one
  simp only [dft, cyclicConv, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight i)
    (fun m => x i * y (m - i) * ω ^ (m.val * k.val))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Equiv.coe_addRight]
  rw [add_sub_cancel_right, Fin.add_def, ω_pow_mod_mul hn, Nat.add_mul, pow_add]
  ring

end CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Lattice.CyclicConvolutionGeneric

/-!
# The twisted DFT diagonalizes negacyclic convolution

This is the algebraic reason the ML-KEM / ML-DSA number-theoretic transform
works: those schemes multiply in `R[X]/(Xⁿ + 1)` (the *negacyclic* ring), not
`R[X]/(Xⁿ − 1)`. The negacyclic setting is obtained from the already-proven
cyclic convolution theorem (`dft_cyclicConv`) by the standard **ψ-twist**, where
`ψ` is a `2n`-th root of unity (so `ψ² = ω` is the primitive `n`-th root used by
the underlying DFT).

* `twist ψ x j = x j · ψʲ` pre-multiplies coefficient `j` by `ψʲ`.
* `untwist ψ z j = z j · (ψ⁻¹)ʲ` is its inverse (over a field, `ψ ≠ 0`).
* `ndft ψ x = dft n (ψ²) (twist ψ x)` is the twisted/negacyclic forward
  transform. Expanding, `ndft ψ x k = Σⱼ xⱼ · ψ^(j(2k+1))`.
* `negaConv ψ x y = untwist ψ (cyclicConv n (twist ψ x) (twist ψ y))` is the
  negacyclic convolution, *defined* here as the untwisted cyclic convolution of
  the twisted operands — the standard `negaConv = untwist ∘ cyclicConv ∘ twist`
  identity taken as the definition.

The main theorem `ndft_negaConv` is then a ~2-line reduction to
`dft_cyclicConv`: the forward `twist` cancels the `untwist` inside `ndft` via
`twist_untwist`, leaving exactly the cyclic convolution theorem.

Identifying `negaConv` with the explicit *signed* convolution
`Σ_{i+j≡k} xᵢyⱼ − Σ_{i+j≡k+n} xᵢyⱼ` (the `ψⁿ = −1` sign bookkeeping over
`Fin n` subtraction) is a separate lemma, deliberately **not** done here — the
twist-definition is the clean diagonalizable object.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Lattice.NegacyclicTransformGeneric

open Finset
open CatCrypt.Crypto.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Lattice.CyclicConvolutionGeneric

variable {R : Type*} [Field R] {ψ : R} {n : ℕ} [NeZero n]

/-- Pre-multiply coefficient `j` by `ψʲ`: the ψ-twist mapping `R[X]/(Xⁿ+1)`
arithmetic into `R[X]/(Xⁿ−1)` arithmetic. -/
def twist (ψ : R) (x : Fin n → R) : Fin n → R := fun j => x j * ψ ^ (j.val)

/-- The inverse of `twist`: post-multiply coefficient `j` by `(ψ⁻¹)ʲ`. -/
def untwist (ψ : R) (z : Fin n → R) : Fin n → R := fun j => z j * (ψ⁻¹) ^ (j.val)

omit [NeZero n] in
/-- `twist` is a left inverse of `untwist` when `ψ ≠ 0`. -/
lemma twist_untwist (hψ : ψ ≠ 0) (z : Fin n → R) :
    twist ψ (untwist ψ z) = z := by
  funext j
  simp only [twist, untwist, mul_assoc, ← mul_pow, inv_mul_cancel₀ hψ, one_pow, mul_one]

omit [NeZero n] in
/-- `untwist` is a left inverse of `twist` when `ψ ≠ 0`. -/
lemma untwist_twist (hψ : ψ ≠ 0) (x : Fin n → R) :
    untwist ψ (twist ψ x) = x := by
  funext j
  simp only [twist, untwist, mul_assoc, ← mul_pow, mul_inv_cancel₀ hψ, one_pow, mul_one]

/-- The twisted / negacyclic forward transform: the length-`n` DFT at twiddle
`ψ²` of the `ψ`-twisted input. Expands to `ndft ψ x k = Σⱼ xⱼ · ψ^(j(2k+1))`. -/
def ndft (ψ : R) (x : Fin n → R) : Fin n → R := fun k => dft n (ψ ^ 2) (twist ψ x) k

/-- Negacyclic convolution, defined as the untwisted cyclic convolution of the
twisted operands (multiplication in `R[X]/(Xⁿ+1)`). -/
def negaConv (ψ : R) (x y : Fin n → R) : Fin n → R :=
  untwist ψ (cyclicConv n (twist ψ x) (twist ψ y))

/-- **Negacyclic convolution theorem**: the twisted DFT diagonalizes negacyclic
convolution. Pointwise product of the two twisted transforms equals the twisted
transform of the negacyclic convolution. This is why NTT-based multiplication in
`R[X]/(Xⁿ+1)` (the ML-KEM / ML-DSA setting) is correct. -/
theorem ndft_negaConv (hω : IsPrimitiveRoot (ψ ^ 2) n) (hψ : ψ ≠ 0)
    (x y : Fin n → R) (k : Fin n) :
    ndft ψ (negaConv ψ x y) k = ndft ψ x k * ndft ψ y k := by
  simp only [ndft, negaConv, twist_untwist hψ]
  exact dft_cyclicConv hω _ _ k

end CatCrypt.Crypto.Lattice.NegacyclicTransformGeneric

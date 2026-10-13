/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Optimizer.Lattice.NTTFullInversionGeneric

/-!
# DFT bijection: the synthesis half `dft ∘ idft = id`

`NTTFullInversionGeneric.idft_dft` proves the analysis-then-synthesis direction
`idft n ω (dft n ω x) = x`. This module proves the *other* composition,
`dft n ω (idft n ω X) = X`, so that over a field with a primitive `n`-th root of
unity `ω` (and `(n : R) ≠ 0`) the pair `(dft, idft)` is a bijection.

## The main theorem

`dft_idft : dft n ω (idft n ω X) = X`. Expanding both maps gives the double sum

`dft n ω (idft n ω X) k = ∑_j ((n)⁻¹ · ∑_l X l · (ω⁻¹)^(l·j)) · ω^(j·k)`.

Pull the `(n)⁻¹` scalar out of the `j`-sum, swap the two sums
(`Finset.sum_comm`), and factor out `X l`; the inner `j`-sum becomes
`∑_j ω^(k·j) · (ω⁻¹)^(l·j)` — the left-hand side of `ntt_orthogonality hω k l`.
Orthogonality collapses it to `if k = l then n else 0`; `Finset.sum_ite_eq` (the
bound variable `l` sits on the right of `k = l`) kills the outer `l`-sum, leaving
`(n)⁻¹ · (n · X k) = X k` via `inv_mul_cancel₀`.

## The bijection

`dftEquiv` packages `dft` and `idft` into an `Equiv (Fin n → R) (Fin n → R)`
whose `left_inv`/`right_inv` are `idft_dft` and `dft_idft`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.DFTBijectionGeneric

open Finset
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Optimizer.Lattice.NTTInverseGeneric
open CatCrypt.Crypto.Optimizer.Lattice.NTTFullInversionGeneric

variable {R : Type*} [Field R]

/-- **DFT bijection (synthesis half).** For `ω` a primitive `n`-th root of unity
over a field with `(n : R) ≠ 0`, the analysis map `dft` is a left inverse of the
synthesis map `idft`:

`dft n ω (idft n ω X) = X`.

Together with `idft_dft` this makes `(dft, idft)` a bijection. The proof pulls
the `(n)⁻¹` out of the `j`-sum, swaps sums (`Finset.sum_comm`), and collapses the
inner sum with `ntt_orthogonality hω k l` (= `n · [k = l]`); `inv_mul_cancel₀`
cancels the `(n)⁻¹ · n` normalisation. -/
theorem dft_idft {ω : R} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : (n : R) ≠ 0)
    (X : Fin n → R) :
    dft n ω (idft n ω X) = X := by
  funext k
  simp only [dft, idft]
  -- Distribute `ω^(x·k)` into the inner `j`-sum, pull `(n)⁻¹` out, then swap sums.
  rw [Finset.sum_congr rfl (fun x _ => by rw [mul_assoc, Finset.sum_mul])]
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- Inner `x`-sum is `X y · (∑ x ω^(k·x)·(ω⁻¹)^(y·x))`; orthogonality collapses it.
  have hinner : ∀ y : Fin n,
      (∑ x : Fin n, X y * ω⁻¹ ^ (y.val * x.val) * ω ^ (x.val * k.val))
        = X y * (if k = y then (n : R) else 0) := by
    intro y
    rw [← ntt_orthogonality hω k y, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun y _ => hinner y)]
  simp only [mul_ite, mul_zero,
    Finset.sum_ite_eq Finset.univ k (fun y => X y * (n : R)), Finset.mem_univ, if_true]
  rw [mul_comm (X k) (n : R), ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The DFT as an explicit bijection on `Fin n → R`. With `ω` a primitive `n`-th
root of unity over a field and `(n : R) ≠ 0`, `dft` and `idft` are mutually
inverse (`idft_dft` and `dft_idft`), so they assemble into an `Equiv`. -/
noncomputable def dftEquiv {ω : R} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    (hn : (n : R) ≠ 0) : (Fin n → R) ≃ (Fin n → R) where
  toFun := dft n ω
  invFun := idft n ω
  left_inv := idft_dft hω hn
  right_inv := dft_idft hω hn

end CatCrypt.Crypto.Optimizer.Lattice.DFTBijectionGeneric

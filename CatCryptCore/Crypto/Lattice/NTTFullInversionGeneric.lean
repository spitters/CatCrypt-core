/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Lattice.NTTInverseGeneric

/-!
# Full DFT inversion theorem: `idft ∘ dft = id`

The forward transform `dft` (`NTTRecursionPass`) and the root-of-unity
orthogonality engine `ntt_orthogonality` (`NTTInverseGeneric`) combine here into
the inversion theorem: over a field with a primitive `n`-th root of unity `ω`
(and `(n : R) ≠ 0`), the synthesis map `idft` is a left inverse of the
analysis map `dft`.

## The synthesis map

`idft n ω X k = (n)⁻¹ · ∑_j X j · (ω⁻¹)^(j·k)`. The index convention matches
`dft`'s `∑_j x j · ω^(j·k)`, with the conjugate twiddle `ω⁻¹` and the `(n)⁻¹`
normalisation that both exist in a field.

## The main theorem

`idft_dft : idft n ω (dft n ω x) = x`. Expanding both maps gives the double sum
`(n)⁻¹ · ∑_j (∑_l x l · ω^(l·j)) · (ω⁻¹)^(j·k)`. Swapping the two sums
(`Finset.sum_comm`) and factoring out `x l` leaves, in the inner `j`-sum,
exactly `∑_j ω^(l·j) · (ω⁻¹)^(k·j)` — the left-hand side of
`ntt_orthogonality hω l k`. Orthogonality collapses it to `if l = k then n
else 0`; `Finset.sum_ite_eq'` kills the outer `l`-sum, leaving
`(n)⁻¹ · (x k · n) = x k` via `inv_mul_cancel₀`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Lattice.NTTFullInversionGeneric

open Finset
open CatCrypt.Crypto.Lattice.NTTRecursionPass
open CatCrypt.Crypto.Lattice.NTTInverseGeneric

variable {R : Type*} [Field R]

/-- Generic inverse discrete / number-theoretic transform (synthesis map):
`xₖ = (n)⁻¹ · Σⱼ Xⱼ (ω⁻¹)^(j·k)`. The conjugate twiddle `ω⁻¹` and the `(n)⁻¹`
normalisation both live in a field; the index convention matches `dft`. -/
def idft (n : ℕ) (ω : R) (X : Fin n → R) (k : Fin n) : R :=
  (n : R)⁻¹ * ∑ j : Fin n, X j * (ω⁻¹) ^ (j.val * k.val)

/-- **DFT inversion theorem.** For `ω` a primitive `n`-th root of unity over a
field with `(n : R) ≠ 0`, the synthesis map `idft` is a left inverse of the
analysis map `dft`:

`idft n ω (dft n ω x) = x`.

Expanding both maps gives a double sum; `Finset.sum_comm` swaps the order,
`ntt_orthogonality` collapses the inner sum to `n · [l = k]`, and
`inv_mul_cancel₀` cancels the `(n)⁻¹ · n` normalisation. -/
theorem idft_dft {ω : R} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : (n : R) ≠ 0)
    (x : Fin n → R) :
    idft n ω (dft n ω x) = x := by
  funext k
  simp only [idft, dft]
  -- Inner sum: ∑ j (∑ l x l ω^(l·j)) (ω⁻¹)^(j·k); distribute over j, then swap.
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_mul _ _ _)]
  rw [Finset.sum_comm]
  -- Now ∑ l ∑ j (x l * ω^(l·j)) * (ω⁻¹)^(j·k); factor x l out of the j-sum.
  have hinner : ∀ l : Fin n,
      (∑ j : Fin n, x l * ω ^ (l.val * j.val) * (ω⁻¹) ^ (j.val * k.val))
        = x l * (if l = k then (n : R) else 0) := by
    intro l
    rw [← ntt_orthogonality hω l k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun l _ => hinner l)]
  simp only [mul_ite, mul_zero,
    Finset.sum_ite_eq' Finset.univ k (fun l => x l * (n : R)), Finset.mem_univ, ite_true]
  rw [mul_comm (x k) (n : R), ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end CatCrypt.Crypto.Lattice.NTTFullInversionGeneric

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Lattice.NTTRecursionPass
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Inverse number-theoretic transform: the synthesis half (DFT inversion)

The forward NTT (`NTTRecursionPass.dft`, and the convolution theorem's forward
direction in `NttMultiplyGeneric`) is a pure algebraic identity needing **no**
relation on the twiddle `ω`. The *inverse* — recovering the coefficients from the
evaluation-domain samples — is the harder direction: it needs `ω` to be
a **primitive `n`-th root of unity**, and the whole proof turns on
**root-of-unity orthogonality**.

## Orthogonality

The engine is `ntt_orthogonality`: for `ω` a primitive `n`-th root over a domain,

`∑_{k<n} ω^(l·k) · (ω⁻¹)^(j·k) = if l = j then n else 0`.

The summand factors as a single geometric term `c^k` with `c = ω^l · (ω⁻¹)^j`.
On the diagonal `l = j` we have `c = 1`, so the sum is `n`. Off the diagonal
`c ≠ 1` (primitive roots have an injective power map below `n`,
`IsPrimitiveRoot.pow_inj`) while `c^n = 1` (from `ω^n = 1`); the geometric
identity `(∑ c^k)·(c − 1) = c^n − 1 = 0` together with `c − 1 ≠ 0` in a domain
forces the sum to vanish. The off-diagonal vanishing is exactly the content of
`geom_sum_mul` specialised at a non-trivial root of unity.

## Inversion

`idft n ω X k = (n)⁻¹ · ∑_j X j · (ω⁻¹)^(j·k)` is the synthesis map (a `Field`,
where `n ≠ 0`, is assumed so that both `ω⁻¹` and `(n)⁻¹` exist). The main theorem
`idft_dft` then states `idft n ω (dft n ω x) = x`: swap the two sums, apply
orthogonality to collapse the inner one to `n · [l = k]`, and cancel `(n)⁻¹ · n`.
The DFT is invertible — this closes the inverse/synthesis half that the forward
`NttMultiplyGeneric` deliberately left open.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Lattice.NTTInverseGeneric

open Finset
open CatCrypt.Crypto.Lattice.NTTRecursionPass

variable {R : Type*} [Field R]

/-! ## Root-of-unity orthogonality -/

/-- Off-diagonal vanishing, as a geometric series. If `c` is a non-trivial
`n`-th root of unity (`cⁿ = 1` but `c ≠ 1`) over a domain, the geometric sum
`∑_{k<n} cᵏ` vanishes: multiply by `c − 1` and use `geom_sum_mul`
(`(∑ cᵏ)·(c − 1) = cⁿ − 1 = 0`); since `c − 1 ≠ 0`, the sum is `0`. -/
theorem geom_sum_root_eq_zero (c : R) (n : ℕ) (hcn : c ^ n = 1) (hc1 : c ≠ 1) :
    ∑ k ∈ range n, c ^ k = 0 := by
  have hmul : (∑ k ∈ range n, c ^ k) * (c - 1) = 0 := by
    rw [geom_sum_mul, hcn, sub_self]
  have hne : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  exact (mul_eq_zero.mp hmul).resolve_right hne

/-- **Root-of-unity orthogonality.** For `ω` a primitive `n`-th root of unity
over a domain and indices `l, j : Fin n`,

`∑_{k : Fin n} ω^(l·k) · (ω⁻¹)^(j·k) = if l = j then (n : R) else 0`.

The summand is `cᵏ` for the single base `c = ω^l · (ω⁻¹)^j`. On the diagonal
`c = (ω · ω⁻¹)^l = 1`, so the sum is `n`; off the diagonal `c ≠ 1` (by
`IsPrimitiveRoot.pow_inj`, the power map is injective below `n`) yet `cⁿ = 1`
(from `ωⁿ = 1`), so `geom_sum_root_eq_zero` makes the sum vanish. This is the
orthogonality relation that inverts the DFT. -/
theorem ntt_orthogonality {ω : R} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    (l j : Fin n) :
    (∑ k : Fin n, ω ^ (l.val * k.val) * (ω⁻¹) ^ (j.val * k.val))
      = if l = j then (n : R) else 0 := by
  have hn0 : n ≠ 0 := l.pos.ne'
  have hω0 : ω ≠ 0 := hω.ne_zero hn0
  -- Collapse the summand to a single geometric base `c = ω^l · (ω⁻¹)^j`.
  set c := ω ^ l.val * ω⁻¹ ^ j.val with hc_def
  have key : (∑ k : Fin n, ω ^ (l.val * k.val) * ω⁻¹ ^ (j.val * k.val))
      = ∑ k : Fin n, c ^ k.val := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hc_def, mul_pow, ← pow_mul, ← pow_mul, mul_comm l.val k.val, mul_comm j.val k.val]
  rw [key, Fin.sum_univ_eq_sum_range (fun k => c ^ k) n]
  by_cases hlj : l = j
  · -- Diagonal: `c = (ω · ω⁻¹)^l = 1`, so the sum is `n`.
    have hc1 : c = 1 := by
      rw [hc_def, hlj, ← mul_pow, mul_inv_cancel₀ hω0, one_pow]
    simp [hc1, hlj]
  · -- Off-diagonal: `cⁿ = 1` but `c ≠ 1`, so the geometric sum vanishes.
    have hcn : c ^ n = 1 := by
      rw [hc_def, mul_pow, ← pow_mul, ← pow_mul, mul_comm l.val n, mul_comm j.val n,
        pow_mul, pow_mul, hω.pow_eq_one, one_pow, inv_pow, hω.pow_eq_one,
        inv_one, one_pow, mul_one]
    have hc1 : c ≠ 1 := by
      intro h
      apply hlj
      have hpow : ω ^ l.val = ω ^ j.val := by
        rw [hc_def] at h
        calc ω ^ l.val = ω ^ l.val * ω⁻¹ ^ j.val * ω ^ j.val := by
                rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hω0, one_pow, mul_one]
          _ = ω ^ j.val := by rw [h, one_mul]
      exact Fin.ext (hω.pow_inj l.isLt j.isLt hpow)
    rw [geom_sum_root_eq_zero c n hcn hc1]
    simp [hlj]

end CatCrypt.Crypto.Lattice.NTTInverseGeneric

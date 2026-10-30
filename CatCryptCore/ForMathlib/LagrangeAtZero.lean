/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Lagrange coefficients at zero

The value at `0` of the Lagrange basis polynomial of a node set, and the interpolation
identity at `0`: for distinct nodes `x i` (`i ∈ s`) and a polynomial `f` of degree less than
`#s`, `∑ i ∈ s, λᵢ · f (x i) = f 0`, where `λᵢ = ∏ j ∈ s.erase i, x j / (x j - x i)`. This is the
reconstruction step of Shamir secret sharing and of threshold decryption.

## Main definitions

* `lagrangeAt0 s x i` — the Lagrange basis polynomial of node `i` evaluated at `0`.

## Main results

* `lagrangeAt0_eq_prod` — the closed form `∏ j ∈ s.erase i, x j / (x j - x i)`.
* `sum_lagrangeAt0_mul_eval` — the interpolation identity at `0`.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace Lagrange

variable {F ι : Type*} [Field F] [DecidableEq ι]

/-- The Lagrange basis polynomial of node `i` for the nodes `x` on `s`, evaluated at `0`. -/
noncomputable def lagrangeAt0 (s : Finset ι) (x : ι → F) (i : ι) : F :=
  (Lagrange.basis s x i).eval 0

/-- The Lagrange coefficient at `0` is `∏ j ∈ s.erase i, x j / (x j - x i)`. -/
theorem lagrangeAt0_eq_prod (s : Finset ι) (x : ι → F) (i : ι) :
    lagrangeAt0 s x i = ∏ j ∈ s.erase i, x j / (x j - x i) := by
  unfold lagrangeAt0 Lagrange.basis
  rw [eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  grind

/-- Interpolation at `0`: for distinct nodes and `f` of degree less than `#s`,
`∑ i ∈ s, lagrangeAt0 s x i * f.eval (x i) = f.eval 0`. -/
theorem sum_lagrangeAt0_mul_eval {s : Finset ι} {x : ι → F} (hx : Set.InjOn x s) (f : F[X])
    (hf : f.degree < s.card) :
    ∑ i ∈ s, lagrangeAt0 s x i * f.eval (x i) = f.eval 0 := by
  conv_rhs => rw [Lagrange.eq_interpolate hx hf]
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, lagrangeAt0]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Lagrange

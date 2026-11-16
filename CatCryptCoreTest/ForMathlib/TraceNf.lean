/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.ForMathlib.Tactic.TraceNf

/-!
# Tests for the `trace_nf` tactic

Trace identities up to rotation of words, with rectangular factors, sums, scalars and finite
sums; real parts of traces of Hermitian words up to reversal, over `ℂ` and over an `RCLike`
field; the rotation `a * B * a * S` to `(a * S) * (a * B)` of the quantum leftover hash lemma;
normalisation at a hypothesis; and the vector forms `star x ⬝ᵥ (M *ᵥ y)`, `(x ᵥ* M) ⬝ᵥ y` and
`‖WithLp.toLp 2 v‖ ^ 2`.
-/

set_option autoImplicit false

open Matrix

example {n m k : Type*} [Fintype n] [Fintype m] [Fintype k] (A : Matrix n m ℂ)
    (B : Matrix m k ℂ) (C : Matrix k n ℂ) :
    (A * B * C).trace = (B * (C * A)).trace := by
  trace_nf

example {n : Type*} [Fintype n] (A B C D : Matrix n n ℂ) :
    (A * B * (C * D)).trace + (D * A * B * C).trace = 2 * (C * D * A * B).trace := by
  trace_nf

example {n : Type*} [Fintype n] (A B C : Matrix n n ℂ) (c : ℂ) :
    (A * (B + c • C)).trace = (B * A).trace + c * (C * A).trace := by
  trace_nf

example {n : Type*} [Fintype n] (A B C : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (A * B * C).trace.re = (C * B * A).trace.re := by
  trace_nf

example {n : Type*} [Fintype n] (W : Matrix n n ℂ) (x : n → ℂ) :
    ‖WithLp.toLp 2 (W *ᵥ x)‖ ^ 2 = (star x ⬝ᵥ ((Wᴴ * W) *ᵥ x)).re := by
  trace_nf

example {n : Type*} [Fintype n] (M N P : Matrix n n ℂ) (x y : n → ℂ) :
    (x ᵥ* M) ⬝ᵥ (N *ᵥ (P *ᵥ y)) = x ⬝ᵥ ((M * (N * P)) *ᵥ y) := by
  trace_nf

example {n : Type*} [Fintype n] (a B S : Matrix n n ℂ) :
    (a * B * a * S).trace = ((a * S) * (a * B)).trace := by
  trace_nf

example {n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜] (P Q R : Matrix n n 𝕜)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hR : R.IsHermitian) :
    RCLike.re (P * Q * Q * R).trace = RCLike.re (Q * P * R * Q).trace := by
  trace_nf

example {n ι : Type*} [Fintype n] (s : Finset ι) (f : ι → Matrix n n ℂ) (A : Matrix n n ℂ) :
    (A * ∑ i ∈ s, f i).trace = ∑ i ∈ s, (f i * A).trace := by
  trace_nf

example {n : Type*} [Fintype n] (A B : Matrix n n ℂ) (c : ℂ)
    (h : (A * B).trace - (B * A).trace + c = 0) : c = 0 := by
  trace_nf at h
  exact h

example {n : Type*} [Fintype n] (M : Matrix n n ℂ) (x y : n → ℂ) :
    star (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = star x ⬝ᵥ ((Mᴴ * M) *ᵥ y) := by
  trace_nf

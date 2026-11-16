/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Quantum.TensorProductPositivity

/-!
# Tests for the `positivity` extension of `TensorProduct.kronecker`

Goals `0 ≤ kronecker A B` and `(kronecker A B).PosSemidef` closed by `psd` from hypotheses on the
factors: two hypotheses, a nested product and a product with a congruence factor.
-/

set_option autoImplicit false

open CatCrypt.Quantum.TensorProduct
open scoped ComplexOrder MatrixOrder

example {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (hA : 0 ≤ A) (hB : B.PosSemidef) : 0 ≤ kronecker A B := by psd

example {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (hA : A.PosSemidef) (hB : 0 ≤ B) : (kronecker A B).PosSemidef := by psd

example {d₁ d₂ d₃ : ℕ} (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (C : Matrix (Fin d₃) (Fin d₃) ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ kronecker (kronecker A B) C := by psd

example {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (K : Matrix (Fin d₂) (Fin d₂) ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ kronecker A (K.conjTranspose * B * K) := by psd

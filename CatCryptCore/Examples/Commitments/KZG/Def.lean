/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Assumptions.tSDH
import CatCryptCore.Examples.Commitments.PolyCommitScheme
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# KZG Polynomial Commitment (PolyCommitDL) — Definitions

This file defines the KZG polynomial commitment scheme (PolyCommitDL)
from [Kate, Zaverucha, Goldberg 2010].

## Main definitions

* `KZG.Poly` — Polynomial type: `Polynomial (ZMod P.p)` with degree ≤ t
* `KZG.commit` — Commitment: `C = ∏ᵢ srs[i]^cᵢ` where cᵢ are coefficients
* `KZG.create_witness` — Evaluation witness via polynomial division
* `KZG.verify_eval` — Pairing-based verification
* `KZG.setup` — Probabilistic SRS generation

## Design

Polynomials are `Polynomial (ZMod P.p)` (unbounded Mathlib polynomials);
degree bounds are enforced as side conditions in theorems rather than in types,
following the SSProve/Commitments approach.

## References

* [Kate, Zaverucha, Goldberg, *Constant-Size Commitments to Polynomials*, 2010 — §3.2]
* [SSProve/Commitments — KZG.v](https://github.com/SSProve/Commitments)
-/

namespace CatCrypt.Examples.Commitments.KZG

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.PairingGroup
open Polynomial
open scoped ENNReal

variable (P : PairingGroup) (t : ℕ)

/-! ## Polynomial Type -/

/-- Polynomials over `ZMod P.p`. We use Mathlib's `Polynomial` directly
    and enforce degree bounds as side conditions. -/
abbrev Poly := Polynomial (ZMod P.p)

/-! ## Commitment -/

/-- Commit a polynomial to a group element using the SRS.

Given SRS `[g₁^(α⁰), g₁^(α¹), ..., g₁^(αᵗ)]` and polynomial `φ = ∑ cᵢ Xⁱ`,
the commitment is `C = ∏ᵢ srs[i]^cᵢ = g₁^(φ(α))`.

We sum over coefficients 0..t. If φ has degree > t, higher coefficients are ignored. -/
noncomputable def commit (pk : Fin (t + 1) → P.G₁) (φ : Poly P) : P.G₁ :=
  ∏ i : Fin (t + 1), pk i ^ᵍ (φ.coeff i)

/-- Commitment using raw SRS (combines srs₁ with commit) -/
noncomputable def commitSRS (α : ZMod P.p) (φ : Poly P) : P.G₁ :=
  commit P t (srs₁ (P := P) α t) φ

/-- Key property: commitment with SRS equals g₁^(φ(α)) when deg φ ≤ t.

This is the fundamental correctness property of the commitment scheme:
evaluating the polynomial at the secret α in the exponent. -/
theorem commitSRS_eq (α : ZMod P.p) (φ : Poly P)
    (hdeg : φ.natDegree ≤ t) :
    commitSRS P t α φ = P.g₁ ^ᵍ (φ.eval α) := by
  unfold commitSRS commit srs₁
  -- Goal: ∏ i, (g₁ ^ᵍ (α^i)) ^ᵍ (φ.coeff i) = g₁ ^ᵍ (φ.eval α)
  -- Step 1: composition (g₁ ^ᵍ a) ^ᵍ b = g₁ ^ᵍ (a * b)
  simp_rw [zpowZMod₁_zpowZMod₁]
  -- Goal: ∏ i, g₁ ^ᵍ (α^i * φ.coeff i) = g₁ ^ᵍ (φ.eval α)
  simp_rw [mul_comm (α ^ _) (φ.coeff _)]
  -- Goal: ∏ i, g₁ ^ᵍ (φ.coeff i * α^i) = g₁ ^ᵍ (φ.eval α)
  -- Step 2: collapse product into sum
  rw [zpowZMod₁_finprod_univ]
  -- Goal: g₁ ^ᵍ (∑ i : Fin (t+1), φ.coeff i * α^i) = g₁ ^ᵍ (φ.eval α)
  -- Step 3: identify sum with eval
  congr 1
  rw [eval_eq_sum_range' (by omega : φ.natDegree < t + 1)]
  rw [Fin.sum_univ_eq_sum_range (fun i => φ.coeff i * α ^ i) (t + 1)]

/-! ## Setup -/

/-- KZG Setup: sample random α, produce SRS in G₁ and verification key in G₂.

Returns `(pk, vk)` where:
- `pk : Fin (t+1) → G₁` is `[g₁, g₁^α, ..., g₁^(αᵗ)]`
- `vk : G₂ × G₂` is `(g₂, g₂^α)` -/
noncomputable def setup : SPComp ((Fin (t + 1) → P.G₁) × (P.G₂ × P.G₂)) := do
  let α ← SPComp.sample (ZMod P.p)
  SPComp.pure (srs₁ (P := P) α t, srs₂ (P := P) α)

/-! ## Create Witness (Evaluation Proof) -/

/-- The witness polynomial `ψ(X) = (φ(X) - φ(z)) / (X - z)`.

By the polynomial remainder theorem, if we evaluate φ at z and subtract,
`(X - z)` divides `(φ(X) - φ(z))`, so the quotient is exact. -/
noncomputable def witnessPoly (φ : Poly P) (z : ZMod P.p) : Poly P :=
  (φ - C (φ.eval z)) /ₘ (X - C z)

/-- Create evaluation witness: compute ψ and the evaluation y = φ(z).

Returns `(w, y)` where:
- `w = commit(pk, ψ)` is the witness commitment (in G₁)
- `y = φ(z)` is the evaluation value -/
noncomputable def create_witness (pk : Fin (t + 1) → P.G₁)
    (φ : Poly P) (z : ZMod P.p) : P.G₁ × ZMod P.p :=
  let y := φ.eval z
  let ψ := witnessPoly P φ z
  (commit P t pk ψ, y)

/-! ## Verification -/

/-- Verify an evaluation proof using the bilinear pairing.

Checks: `e(C · g₁^(-y), g₂) = e(w, g₂^α · g₂^(-z))`

This is equivalent to checking that `φ(α) - y = ψ(α) · (α - z)` in the exponent,
which holds iff ψ is the correct quotient polynomial for φ(z) = y. -/
noncomputable def verify_eval (vk : P.G₂ × P.G₂) (C : P.G₁)
    (z y : ZMod P.p) (w : P.G₁) : Prop :=
  P.e (C * (P.g₁ ^ᵍ y)⁻¹) P.g₂ = P.e w (vk.2 * (P.g₂ ^ʰ z)⁻¹)

/-- Decidable instance for verify_eval (via DecidableEq on GT) -/
noncomputable instance (vk : P.G₂ × P.G₂) (C : P.G₁) (z y : ZMod P.p) (w : P.G₁) :
    Decidable (verify_eval P vk C z y w) :=
  inferInstanceAs (Decidable (_ = _))

/-- Decidable version of verify_eval for use in Bool-returning games -/
noncomputable def verify_eval_bool (vk : P.G₂ × P.G₂) (C : P.G₁)
    (z y : ZMod P.p) (w : P.G₁) : Bool :=
  if verify_eval P vk C z y w then true else false

/-! ## Polynomial Division Lemma -/

/-- Key Mathlib fact: `φ(z) = y` implies `(X - C z) ∣ (φ - C y)`.
    This follows from the factor theorem: `(X - a) ∣ p ↔ p.IsRoot a`. -/
theorem isRoot_sub_eval (φ : Poly P) (z : ZMod P.p) :
    (φ - C (φ.eval z)).IsRoot z := by
  simp [IsRoot, eval_sub, eval_C]

/-- The witness polynomial times (X - z) equals φ - C(φ(z)). -/
theorem witnessPoly_spec (φ : Poly P) (z : ZMod P.p) :
    (X - C z) * witnessPoly P φ z = φ - C (φ.eval z) := by
  unfold witnessPoly
  exact mul_divByMonic_eq_iff_isRoot.mpr (isRoot_sub_eval P φ z)

end CatCrypt.Examples.Commitments.KZG

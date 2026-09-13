/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PairingGroup
public import CatCryptCore.Core.Code

/-!
# Algebraic Group Model (AGM)

This file formalizes the Algebraic Group Model, where adversaries must provide
algebraic representations of all group elements they output.

## Main definitions

* `AGMRepr` — a group element of G₁ paired with a claimed exponent vector
* `AGMRepr.Valid` — the representation equation against a given basis
* `AGMRepr.ofCoeffs` — the element computed from a basis and an exponent vector
* `AGMAdversary` — an adversary that receives the SRS and outputs representations

## Main results

* `AGMRepr.ofCoeffs_valid` — the computed element satisfies the equation
* `AGMRepr.element_eq_of_valid_srs₁` — against the KZG SRS, a valid
  representation is `g₁ ^ᵍ φ(α)` for the extracted polynomial `φ`

## Overview

In the AGM, any group element output by the adversary must be accompanied by
a vector of exponents showing how it was computed from the input group elements.
For KZG, the input is the SRS `[g₁, g₁^α, ..., g₁^(αᵗ)]`, and the output
commitment C comes with `[c₀, ..., cₜ]`. A representation is valid for the SRS
`srs` when `C = ∏ srs[i]^cᵢ`. Validity is relative to the SRS the game supplies:
the game checks it and counts an invalid representation as a loss for the
adversary (Fuchsbauer–Kiltz–Loss, Definition 2.1).

A valid representation means the adversary "knows" a polynomial
`φ(X) = ∑ cᵢ Xⁱ` such that `C = g₁^(φ(α))`, enabling knowledge extraction.

## References

* [Fuchsbauer, Kiltz, Loss, *The Algebraic Group Model and its Applications*, CRYPTO 2018]
* [Rothmann, Kreuzer — Algebraic_Group_Model.thy in Isabelle]
* [ArkLib — AGM/Basic.lean]
-/

@[expose] public section

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob
open PairingGroup
open Polynomial
open scoped ENNReal

variable (P : PairingGroup) (t : ℕ)

/-! ## AGM Representation -/

/-- A group element of G₁ together with a claimed algebraic representation
    with respect to a basis of size `t + 1`: a vector of exponents
    `[c₀, ..., cₜ]` in `ZMod p`. Whether the exponents represent the element
    depends on the basis and is the proposition `AGMRepr.Valid`. -/
structure AGMRepr where
  /-- The exponent vector -/
  coeffs : Fin (t + 1) → ZMod P.p
  /-- The represented group element -/
  element : P.G₁

/-- The representation equation against the basis `pk`:
    `element = ∏ᵢ pk[i]^coeffs[i]`. -/
def AGMRepr.Valid (repr : AGMRepr P t) (pk : Fin (t + 1) → P.G₁) : Prop :=
  repr.element = ∏ i : Fin (t + 1), pk i ^ᵍ (repr.coeffs i)

noncomputable instance AGMRepr.instDecidableValid (repr : AGMRepr P t) (pk : Fin (t + 1) → P.G₁) :
    Decidable (repr.Valid P t pk) :=
  inferInstanceAs (Decidable (_ = _))

/-- The representation whose element is computed from the basis `pk` and the
    exponent vector `coeffs`. -/
noncomputable def AGMRepr.ofCoeffs (pk : Fin (t + 1) → P.G₁)
    (coeffs : Fin (t + 1) → ZMod P.p) : AGMRepr P t :=
  ⟨coeffs, ∏ i : Fin (t + 1), pk i ^ᵍ (coeffs i)⟩

/-- A representation computed from a basis is valid for that basis. -/
theorem AGMRepr.ofCoeffs_valid (pk : Fin (t + 1) → P.G₁)
    (coeffs : Fin (t + 1) → ZMod P.p) :
    (AGMRepr.ofCoeffs P t pk coeffs).Valid P t pk :=
  rfl

/-- Extract the polynomial from an AGM representation.
    The polynomial is `φ(X) = ∑ᵢ cᵢ · Xⁱ` where cᵢ are the coefficients. -/
noncomputable def AGMRepr.toPoly (repr : AGMRepr P t) : Polynomial (ZMod P.p) :=
  ∑ i : Fin (t + 1), Polynomial.C (repr.coeffs i) * Polynomial.X ^ i.val

/-! ## Extracted Polynomial Properties -/

/-- Coefficient of toPoly at position j matches the AGM coefficient. -/
theorem AGMRepr.toPoly_coeff (repr : AGMRepr P t) (j : Fin (t + 1)) :
    (repr.toPoly).coeff j.val = repr.coeffs j := by
  unfold AGMRepr.toPoly
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow]; simp
  · intro i _ hij
    simp [Ne.symm (Fin.val_ne_of_ne hij)]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The extracted polynomial has degree at most t. -/
theorem AGMRepr.toPoly_natDegree_le (repr : AGMRepr P t) :
    (repr.toPoly).natDegree ≤ t := by
  unfold AGMRepr.toPoly
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact le_trans (natDegree_C_mul_X_pow_le _ _) (Nat.lt_succ_iff.mp i.isLt)

/-- The representation whose exponents are the first `t + 1` coefficients of `φ`
    extracts to `φ` when `φ` has degree at most `t`. -/
theorem AGMRepr.toPoly_ofCoeffs_coeff (pk : Fin (t + 1) → P.G₁)
    (φ : Polynomial (ZMod P.p)) (hdeg : φ.natDegree ≤ t) :
    (AGMRepr.ofCoeffs P t pk (fun i => φ.coeff i)).toPoly = φ := by
  unfold AGMRepr.toPoly AGMRepr.ofCoeffs
  rw [Fin.sum_univ_eq_sum_range (fun i => C (φ.coeff i) * X ^ i) (t + 1)]
  exact (as_sum_range_C_mul_X_pow' φ (Nat.lt_succ_of_le hdeg)).symm

/-- A representation valid for the KZG SRS `srs₁ α t` has element `g₁ ^ᵍ φ(α)`,
    where `φ` is the extracted polynomial. -/
theorem AGMRepr.element_eq_of_valid_srs₁ (α : ZMod P.p) (repr : AGMRepr P t)
    (hvalid : repr.Valid P t (srs₁ (P := P) α t)) :
    repr.element = P.g₁ ^ᵍ (repr.toPoly.eval α) := by
  unfold AGMRepr.Valid srs₁ at hvalid
  rw [hvalid]
  simp_rw [zpowZMod₁_zpowZMod₁, mul_comm (α ^ _)]
  rw [zpowZMod₁_finprod_univ]
  congr 1
  simp only [AGMRepr.toPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-! ## AGM Adversary -/

/-- An AGM adversary for KZG.

In the AGM, the adversary receives the SRS and outputs a commitment C together
with an algebraic representation of C in terms of the SRS, an evaluation point,
a claimed value, and a witness with its representation. The game that runs the
adversary checks the representations against the SRS it supplied. -/
structure AGMAdversary where
  /-- The adversary's computation: given the SRS, output
      `(C_repr, z, y, w_repr)`, the commitment representation, the evaluation
      point, the claimed value and the witness representation. -/
  run : (Fin (t + 1) → P.G₁) →
    SPComp (AGMRepr P t × ZMod P.p × ZMod P.p × AGMRepr P t)

end CatCrypt.Crypto

/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.PairingGroup
import CatCryptCore.Core.Code

/-!
# Algebraic Group Model (AGM)

This file formalizes the Algebraic Group Model, where adversaries must provide
algebraic representations of all group elements they output.

## Main definitions

* `AGMRepr` — An algebraic representation: vector of exponents
* `AGMAdversary` — An adversary in the AGM that provides representations
* `extracted_poly` — The polynomial extracted from an AGM representation

## Overview

In the AGM, any group element output by the adversary must be accompanied by
a vector of exponents showing how it was computed from the input group elements.
For KZG, the input is the SRS `[g₁, g₁^α, ..., g₁^(αᵗ)]`, and the output
commitment C must come with `[c₀, ..., cₜ]` such that `C = ∏ srs[i]^cᵢ`.

This means the adversary "knows" a polynomial `φ(X) = ∑ cᵢ Xⁱ` such that
`C = g₁^(φ(α))`, enabling knowledge extraction.

## References

* [Fuchsbauer, Kiltz, Loss, *The Algebraic Group Model and its Applications*, CRYPTO 2018]
* [Rothmann, Kreuzer — Algebraic_Group_Model.thy in Isabelle]
* [ArkLib — AGM/Basic.lean]
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob
open PairingGroup
open Polynomial
open scoped ENNReal

variable (P : PairingGroup) (t : ℕ)

/-! ## AGM Representation -/

/-- An algebraic representation of a group element in G₁ with respect to
    the SRS of size t+1.

    A representation is a vector of exponents `[c₀, ..., cₜ]` in ZMod p
    such that the group element equals `∏ᵢ srs[i]^cᵢ`. -/
structure AGMRepr where
  /-- The exponent vector -/
  coeffs : Fin (t + 1) → ZMod P.p
  /-- The represented group element -/
  element : P.G₁
  /-- The representation is valid for a given SRS: element = ∏ srs[i]^coeffs[i].

      **Note:** The universal quantification over all pk is an AGM axiom: the adversary
      must provide coefficients that work for ANY group elements, not just the specific SRS.
      In practice, the game supplies one specific pk and validity is checked against it. -/
  valid : ∀ (pk : Fin (t + 1) → P.G₁),
    element = ∏ i : Fin (t + 1), pk i ^ᵍ (coeffs i)

/-- Extract the polynomial from an AGM representation.
    The polynomial is `φ(X) = ∑ᵢ cᵢ · Xⁱ` where cᵢ are the coefficients. -/
noncomputable def AGMRepr.toPoly (repr : AGMRepr P t) : Polynomial (ZMod P.p) :=
  ∑ i : Fin (t + 1), Polynomial.C (repr.coeffs i) * Polynomial.X ^ i.val

/-! ## Extracted Polynomial Properties -/

/-- Coefficient of toPoly at position j matches the AGM coefficient. -/
theorem AGMRepr.toPoly_coeff (repr : AGMRepr P t) (j : Fin (t + 1)) :
    (repr.toPoly).coeff j.val = repr.coeffs j := by
  unfold AGMRepr.toPoly
  rw [Polynomial.finset_sum_coeff]
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

/-! ## AGM Adversary -/

/-- An AGM adversary for KZG.

In the AGM, the adversary receives the SRS and outputs a commitment C together
with an algebraic representation showing how C was computed from the SRS.

The representation implicitly reveals the committed polynomial. -/
structure AGMAdversary where
  /-- The adversary's computation: given SRS, output (commitment, evaluation proof)
      together with algebraic representations. -/
  run : (Fin (t + 1) → P.G₁) →
    SPComp (AGMRepr P t × ZMod P.p × ZMod P.p × AGMRepr P t)
  -- Output: (C_repr, z, y, w_repr) where C_repr is commitment representation,
  -- z is evaluation point, y is claimed value, w_repr is witness representation

/-- The polynomial extracted from the commitment representation.
    This is a placeholder function — the actual extraction happens
    inline in `KnowledgeSoundness_Game` via `C_repr.toPoly`. -/
noncomputable def AGMAdversary.committedPoly (_A : AGMAdversary P t)
    (_pk : Fin (t + 1) → P.G₁) :
    (Fin (t + 1) → P.G₁) → Polynomial (ZMod P.p) :=
  fun _ => 0

/-! ## Knowledge Soundness Game -/

/-- Knowledge soundness game in the AGM:
    Adversary outputs (C, z, y, w) with algebraic representations.
    Adversary wins if:
    1. The evaluation proof verifies (pairing check passes)
    2. But y ≠ φ(z) where φ is the extracted polynomial

    If the adversary cannot win, then knowledge soundness holds:
    any valid evaluation proof implies knowledge of the committed polynomial.

    **Note:** This simplified game only checks y ≠ φ(z). The full game should also
    check `verify_eval` (the pairing check), but that lives in `KZG.Def` which would
    create heavy dependencies. The `verify_eval` check is needed in the actual security
    proof to establish that δ(α) = 0 (from the pairing equation). For the full game
    with verify_eval, see `KZG.KnowledgeSoundness`. -/
noncomputable def KnowledgeSoundness_Game (A : AGMAdversary P t) : SPComp Bool := do
  let α ← SPComp.sample (ZMod P.p)
  let pk := srs₁ (P := P) α t
  let _vk := srs₂ (P := P) α
  let (C_repr, z, y, _w_repr) ← A.run pk
  let φ := C_repr.toPoly
  -- Adversary wins if y ≠ φ(z) (simplified; full game also checks verify_eval)
  SPComp.pure (decide (y ≠ φ.eval z))

end CatCrypt.Crypto

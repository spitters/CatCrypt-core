/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.VCVioBridge.Relational

/-!
# Bridge Example — Advantage transfer pattern

Generic template showing how to take a quantitative VCVio result about
`Pr[= true | mx₀] - Pr[= true | mx₁]` and express it as a CatCrypt `Advantage`
bound on the lifted `SPComp` games.

This is the pattern for any computational reduction (PRGfromPRF, ElGamal vs DDH,
Schnorr vs DLog, etc.): prove the probability difference in VCVio, then derive
the CatCrypt Advantage statement via `advantage_probCompLift_le_of_probOutput_diff`.
-/

namespace CatCrypt.Crypto.VCVioBridge.Examples

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.VCVioBridge
open scoped ENNReal

/-- Template: if two `ProbComp Bool` games have `Pr[= true]` within `ε` of
    each other (in both directions), their lifted `Advantage` is ≤ ε. -/
theorem advantage_le_of_probOutput_diff
    (game₀ game₁ : ProbComp Bool) {ε : ℝ≥0∞}
    (h₀ : Pr[= true | game₀] - Pr[= true | game₁] ≤ ε)
    (h₁ : Pr[= true | game₁] - Pr[= true | game₀] ≤ ε) :
    Advantage (probCompLift game₀) (probCompLift game₁) ≤ ε :=
  advantage_probCompLift_le_of_probOutput_diff game₀ game₁ h₀ h₁

/-- Usage illustration: any concrete VCVio reduction that produces the pair of
    `Pr[= true | _] - Pr[= true | _] ≤ ε` hypotheses can feed them into the
    transfer lemma to obtain a CatCrypt `Advantage` bound. -/
example (game₀ game₁ : ProbComp Bool)
    (hbound : ∀ b : Bool,
      (Pr[= b | game₀]) - (Pr[= b | game₁]) ≤ (1 / 2 : ℝ≥0∞) ∧
      (Pr[= b | game₁]) - (Pr[= b | game₀]) ≤ (1 / 2 : ℝ≥0∞)) :
    Advantage (probCompLift game₀) (probCompLift game₁) ≤ (1 / 2 : ℝ≥0∞) :=
  advantage_le_of_probOutput_diff game₀ game₁ (hbound true).1 (hbound true).2

end CatCrypt.Crypto.VCVioBridge.Examples

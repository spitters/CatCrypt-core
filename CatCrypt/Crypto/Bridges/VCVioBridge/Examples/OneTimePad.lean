/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.VCVioBridge.Relational

/-!
# Bridge Example — One-Time Pad via `evalDist` equality

Demonstrates the transfer pattern: any two `ProbComp Bool` games with equal
`evalDist` yield zero `Advantage` on their `probCompLift`s.

For the full one-time-pad proof (perfect secrecy via bijection coupling), see
the upstream `Examples/OneTimePad.lean`. That proof lives at the `GameEquiv` /
`Pr[= · | _]` level. The bridge lemma below is what lets you *use* a VCVio
`evalDist` equality — from perfect secrecy, a bijection coupling, or any other
source — as a CatCrypt zero-advantage statement.
-/

namespace CatCrypt.Crypto.VCVioBridge.Examples

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.VCVioBridge
open scoped ENNReal

/-- Transfer template: any `evalDist` equality lifts to zero advantage. The OTP
    "rows-equal" theorem (`oneTimePad.cipherGivenMsg_equiv` in upstream) gives
    exactly this hypothesis after specializing to a `Bool`-returning wrapper. -/
theorem zero_advantage_of_evalDist_eq
    (game₀ game₁ : ProbComp Bool) (h : evalDist game₀ = evalDist game₁) :
    Advantage (probCompLift game₀) (probCompLift game₁) = 0 :=
  advantage_probCompLift_eq_zero_of_evalDist_eq game₀ game₁ h

/-- Corollary: if both sides of a proposed indistinguishability reduce to the
    same `ProbComp`, the advantage is zero. -/
theorem zero_advantage_of_eq (game : ProbComp Bool) :
    Advantage (probCompLift game) (probCompLift game) = 0 :=
  zero_advantage_of_evalDist_eq game game rfl

end CatCrypt.Crypto.VCVioBridge.Examples

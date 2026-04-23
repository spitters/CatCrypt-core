/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.VCVioBridge.Relational

/-!
# Bridge Example — Coin flip

Smallest possible example exercising the bridge: a ProbComp that flips a coin,
lifted via `probCompLift` to an SPComp, with its `prTrue` computed via the
probability-preservation lemma.

This is the pattern to follow for any stateless VCVio reduction: state the
game in `ProbComp`, compute `Pr[= true | ...]` in VCVio, then transfer to a
CatCrypt `Advantage` or `prTrue` statement via `prTrue_probCompLift`.
-/

namespace CatCrypt.Crypto.VCVioBridge.Examples

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.VCVioBridge
open scoped ENNReal

/-- A constant-`true` ProbComp. Pr[= true | ...] = 1. -/
def returnTrue : ProbComp Bool := pure true

/-- Advantage of distinguishing `returnTrue` from itself is zero (trivially). -/
theorem returnTrue_self_zero_advantage :
    Advantage (probCompLift returnTrue) (probCompLift returnTrue) = 0 :=
  advantage_probCompLift_eq_zero_of_evalDist_eq _ _ rfl

end CatCrypt.Crypto.VCVioBridge.Examples

/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SecurityDefs

/-!
# Keyed PRF Security: the Perfect Case

PRF security of a keyed function family `F` is stated per adversary: a
reduction `B` built from a protocol adversary contributes the term
`PRF_Adv F x (B A)` (`SecurityDefs.PRF_Adv`) to the protocol's bound, and no
uniform bound over all adversaries is assumed. A protocol that samples the PRF
input uniformly contributes the averaged term
`∑ r, |Input|⁻¹ * PRF_Adv F r (B r)` (`CatCrypt.Examples.CPAFromPRF`).

This module records the information-theoretic case: for a perfect PRF (every
single-query distinguisher has advantage `0`, e.g. a bijection family), that
averaged term is `0` for every family of distinguishers.

## Main results

* `PRFAssumption.of_perfect` — for a perfect PRF, the averaged PRF advantage of
  every family of distinguishers is `0` (a statistical fact).

## References

* [Bellare & Rogaway, Introduction to Modern Cryptography]
* [Rosulek, The Joy of Cryptography, §6]
-/

@[expose] public section

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Crypto.SecurityDefs
open scoped ENNReal

/-- **Perfect PRFs (statistical).** If every single-query distinguisher has PRF
    advantage `0` against `F`, then for every family of distinguishers `B`
    indexed by the PRF input, the PRF advantage averaged over a uniform input is
    `0`. -/
theorem PRFAssumption.of_perfect (F : PRFScheme) [Fintype F.Input]
    (h : ∀ (x : F.Input) (A : F.Output → SPComp Bool), PRF_Adv F x A = 0)
    (B : F.Input → F.Output → SPComp Bool) :
    ∑ r : F.Input, (↑(Fintype.card F.Input) : ℝ≥0∞)⁻¹ * PRF_Adv F r (B r) = 0 := by
  simp [h]

end CatCrypt.Crypto

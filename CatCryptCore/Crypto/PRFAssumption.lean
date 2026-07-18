/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs

/-!
# Keyed PRF Security Assumption

A `PRFAssumption F` packages the standard cryptographic hypothesis that a keyed
function family `F` is a secure pseudorandom function: there is an advantage
bound `ε` such that *every* single-query adversary distinguishes the keyed
evaluation `F(k, ·)` (with a uniform key) from a fresh uniform output with
advantage at most `ε`.

This is the reusable "PRF is ε-secure" assumption structure that reductions take
as a hypothesis. It is parameterized over the abstract `PRFScheme` of
`SecurityDefs`, so it composes with `PRF_Real` / `PRF_Ideal` / `PRF_Adv`.

## Main definitions

* `PRFAssumption F` — the record `⟨ε, bound⟩` asserting `PRF_Adv F x A ≤ ε`
  for all inputs `x` and adversaries `A`.
* `PRFAssumption.advantage_bound` — the packaged advantage bound.

## Main results

* `PRFAssumption.of_perfect` — a perfectly secure PRF (`PRF_Adv = 0`) satisfies
  the assumption with `ε = 0`.

## References

* [Bellare & Rogaway, Introduction to Modern Cryptography]
* [Rosulek, The Joy of Cryptography, §6]
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Crypto.SecurityDefs
open scoped ENNReal

/-- The keyed **PRF security assumption**: `F` is an ε-secure pseudorandom
    function. The field `bound` witnesses that no single-query adversary beats
    advantage `ε` at distinguishing `PRF_Real F x` from `PRF_Ideal F`. -/
structure PRFAssumption (F : PRFScheme) where
  /-- The PRF advantage bound `ε`. -/
  ε : ℝ≥0∞
  /-- Every single-query adversary has PRF advantage at most `ε`. -/
  bound : ∀ (x : F.Input) (A : F.Output → SPComp Bool), PRF_Adv F x A ≤ ε

/-- The packaged advantage bound of a PRF assumption. -/
theorem PRFAssumption.advantage_bound {F : PRFScheme} (H : PRFAssumption F)
    (x : F.Input) (A : F.Output → SPComp Bool) :
    PRF_Adv F x A ≤ H.ε :=
  H.bound x A

/-- A perfectly secure PRF (every adversary has advantage exactly `0`) satisfies
    the PRF assumption with `ε = 0`. -/
def PRFAssumption.of_perfect (F : PRFScheme)
    (h : ∀ (x : F.Input) (A : F.Output → SPComp Bool), PRF_Adv F x A = 0) :
    PRFAssumption F where
  ε := 0
  bound := fun x A => (h x A).le

end CatCrypt.Crypto

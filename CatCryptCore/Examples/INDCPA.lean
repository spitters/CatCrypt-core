/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Encryption
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Relational.Rules

/-!
# IND-CPA Security Games

The IND-CPA (Indistinguishability under Chosen Plaintext Attack) security games
for symmetric encryption schemes.

The IND-CPA game proceeds as:

1. The challenger generates a random key `k`.
2. The adversary chooses two messages `m₀`, `m₁`.
3. The challenger encrypts `mᵦ` for a random bit `b`.
4. The adversary tries to guess `b`.

An encryption scheme is IND-CPA secure if no efficient adversary can guess `b`
with probability significantly better than `1/2`.

## Main definitions

* `indCPA_real` — encrypt the first message (`b = 0`).
* `indCPA_ideal` — encrypt the second message (`b = 1`).
* `INDCPA_Advantage` — the distinguishing advantage.

## References

* [Bellare & Rogaway, *Introduction to Modern Cryptography*]
* [Katz & Lindell, *Introduction to Modern Cryptography*, Chapter 3]
-/

set_option autoImplicit false

namespace CatCryptCore.Examples.INDCPA

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open CatCrypt.Relational
open scoped ENNReal

/-! ## IND-CPA Security Games -/

variable (E : EncScheme)

/-- Real IND-CPA game: encrypt the first message `m₀`.

This corresponds to the game where the challenger bit `b = 0`, so the adversary
receives `Enc(k, m₀)`. -/
noncomputable def indCPA_real (m₀ _m₁ : E.Plaintext) : SPComp E.Ciphertext := do
  let k ← E.keyGen
  E.encrypt k m₀

/-- Ideal IND-CPA game: encrypt the second message `m₁`.

This corresponds to the game where the challenger bit `b = 1`, so the adversary
receives `Enc(k, m₁)`. -/
noncomputable def indCPA_ideal (_m₀ m₁ : E.Plaintext) : SPComp E.Ciphertext := do
  let k ← E.keyGen
  E.encrypt k m₁

/-- IND-CPA advantage: the distinguishing advantage between real and ideal games.

An encryption scheme is IND-CPA secure if for all efficient adversaries `A` and all
message pairs `(m₀, m₁)`, the advantage is negligible. -/
noncomputable def INDCPA_Advantage (m₀ m₁ : E.Plaintext) (A : E.Ciphertext → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (indCPA_real E m₀ m₁) (indCPA_ideal E m₀ m₁) A

/-! ## Perfect IND-CPA Security

Perfect IND-CPA security means the advantage is exactly `0` for all adversaries.
This is achievable by one-time-pad style encryption. -/

/-- An encryption scheme has perfect IND-CPA security if for all message pairs the
real and ideal games satisfy the pRHL judgment with `eqPost`.

The precondition `eqPre` (heap equality) holds when starting from empty heaps. -/
def PerfectINDCPA : Prop :=
  ∀ (m₀ m₁ : E.Plaintext),
    rHoare eqPre (indCPA_real E m₀ m₁) (indCPA_ideal E m₀ m₁) eqPost

/-- Perfect IND-CPA security implies zero advantage for all adversaries. -/
theorem perfect_indcpa_zero_advantage (hPerf : PerfectINDCPA E) :
    ∀ (m₀ m₁ : E.Plaintext) (A : E.Ciphertext → SPComp Bool),
      INDCPA_Advantage E m₀ m₁ A = 0 := by
  intro m₀ m₁ A
  unfold INDCPA_Advantage
  exact advantage_zero_of_rHoare _ _ (hPerf m₀ m₁) A

end CatCryptCore.Examples.INDCPA

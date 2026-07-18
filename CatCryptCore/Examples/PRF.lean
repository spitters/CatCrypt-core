/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Crypto.PRFAssumption
import CatCryptCore.Crypto.SwitchingLemma
import CatCryptCore.Crypto.MultiQueryPRF
import CatCryptCore.Prob.BirthdayBound
import CatCryptCore.Prob.XorBij
import CatCryptCore.Examples.OneTimePad
import CatCryptCore.Tactics

/-!
# Bijection-Family PRF: Perfect Security

A pseudorandom function built from a *bijection family* has perfect security.
Following Rosulek, The Joy of Cryptography, §6 (pseudorandom functions).

For each input `x`, if the map `k ↦ eval k x` is a bijection from keys to
outputs, then over a uniform key the PRF output `eval k x` is itself uniform on
the output space and independent of `x`. Hence the PRF real game (keyed
evaluation) and the PRF ideal game (a fresh uniform output) are perfectly
indistinguishable: the PRF advantage of *every* adversary is exactly `0`.

## Overview

This mirrors the one-time-pad argument (`CatCrypt.Examples.OTP`): the security
proof is the bijection-coupling technique. `liftR_uniform_bij` couples the
uniform key with the uniform output through the bijection `bij x : Key ≃ Output`;
`liftR_bind`/`liftR_pure` push the coupling through the `sample`-then-`pure`
structure of the games; and `PRF_Adv_zero_of_rHoare` collapses the advantage to
`0`.

## Main definitions

* `BijPRFFamily` — a family of key→output bijections indexed by input.
* `BijPRFFamily.toPRFScheme` — the core `PRFScheme` it induces (`eval k x = bij x k`).

## Main results

* `bijPRF_coupling` — the real and ideal PRF games couple with `eqPost`.
* `bijPRF_perfect` — a bijection-family PRF has perfect PRF security:
  `PRF_Adv B.toPRFScheme x A = 0` for every input `x` and adversary `A`.

## References

* [Rosulek, The Joy of Cryptography, §6 (pseudorandom functions)]
-/

namespace CatCrypt.Examples.PRF

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational

/-! ## Bijection-Family PRF -/

/-- A PRF given by a family of bijections `bij x : Key ≃ Output`, one per input.

For a uniform key, `bij x` maps the uniform key distribution onto the uniform
output distribution, which is the source of perfect security. -/
structure BijPRFFamily where
  /-- Key type -/
  Key : Type
  /-- Input (domain) type -/
  Input : Type
  /-- Output (range) type -/
  Output : Type
  [finKey : Fintype Key]
  [neKey : Nonempty Key]
  [finOutput : Fintype Output]
  [neOutput : Nonempty Output]
  /-- For each input, a bijection from keys to outputs -/
  bij : Input → (Key ≃ Output)

attribute [instance] BijPRFFamily.finKey BijPRFFamily.neKey
  BijPRFFamily.finOutput BijPRFFamily.neOutput

/-- The core `PRFScheme` induced by a bijection family: `eval k x = bij x k`. -/
def BijPRFFamily.toPRFScheme (B : BijPRFFamily) : PRFScheme where
  Key := B.Key
  Input := B.Input
  Output := B.Output
  eval := fun k x => B.bij x k

/-! ## Perfect PRF Security -/

/-- Coupling: for a bijection-family PRF the real and ideal games are
equidistributed.

Over a uniform key `k`, the real game returns `bij x k` while the ideal game
returns a fresh uniform output `r`; `liftR_uniform_bij (B.bij x)` couples them so
that `bij x k = r`, so the two games agree pointwise. -/
theorem bijPRF_coupling (B : BijPRFFamily) (x : B.Input) :
    rHoare eqPre
      (PRF_Real B.toPRFScheme x)
      (PRF_Ideal B.toPRFScheme)
      eqPost := by
  simp only [PRF_Real, PRF_Ideal, BijPRFFamily.toPRFScheme, SPComp.monad_bind_eq]
  ssprove_couple_bij (B.bij x)

/-- **A bijection-family PRF has perfect PRF security**: every adversary has PRF
advantage exactly `0`. -/
theorem bijPRF_perfect (B : BijPRFFamily) (x : B.Input)
    (A : B.toPRFScheme.Output → SPComp Bool) :
    PRF_Adv B.toPRFScheme x A = 0 :=
  PRF_Adv_zero_of_rHoare B.toPRFScheme x (bijPRF_coupling B x) A

/-! ## Example: the XOR PRF over `Bool`

`F(k, x) = k ⊕ x` is the bijection family `x ↦ boolXorBij x`; it is the PRF
counterpart of the one-time pad and inherits perfect security. -/

/-- The XOR PRF over `Bool` as a bijection family: `bij x = boolXorBij x`. -/
def boolXorPRF : BijPRFFamily where
  Key := Bool
  Input := Bool
  Output := Bool
  bij := boolXorBij

/-- The XOR PRF has perfect PRF security. -/
theorem boolXorPRF_perfect (x : Bool)
    (A : boolXorPRF.toPRFScheme.Output → SPComp Bool) :
    PRF_Adv boolXorPRF.toPRFScheme x A = 0 :=
  bijPRF_perfect boolXorPRF x A

/-! ## Cascade PRF: the computational bound

The bijection-family result above is *perfect* (`ε = 0`). The **computational**
cascade bound follows. For the double-encryption construction

    `cascade(k₁, k₂, x) = F(k₂, F(k₁, x))`

the PRF advantage is bounded by

    `Adv ≤ 2·ε_prf + q(q-1)/(2N)`,

a reduction to the base PRF's security (`ε_prf`) plus the PRF/PRP switching
(birthday) term. The three game hops are the Bellare–Rogaway triple-encryption
ladder:

| Step | Transition | Bound |
|------|-----------|-------|
| 0→1 | inner `F(k₁,·)` → random function | `ε_prf` (PRF assumption) |
| 1→2 | random function → random permutation | `q(q-1)/(2N)` (switching) |
| 2→3 | outer `F(k₂,·)` → random function | `ε_prf` (PRF assumption) |

The hop bounds are the cryptographic hypotheses (a `PRFAssumption` on the base
function, and the `SwitchingLemma` for the middle step); the theorem composes
them into the total bound by the advantage triangle inequality.
-/

open CatCrypt.Crypto
open CatCrypt.Tactic
open scoped ENNReal

/-- Birthday collision term `q(q-1)/(2N)`, the cost of the PRF→PRP switch. -/
noncomputable def birthdayTerm (q N : ℕ) : ℝ≥0∞ := (↑(q * (q - 1) / 2) : ℝ≥0∞) / ↑N

/-- **Cascade PRF computational bound** (the headline).

For any 4-game hybrid sequence `G` realising the cascade ladder, if the three
hops are bounded by `ε_prf`, the birthday term, and `ε_prf` respectively, then

    `Adv(G₀, G₃) ≤ 2·ε_prf + q(q-1)/(2N)`.

The hop hypotheses `h01`/`h23` are the base-PRF security assumption (see
`cascade_prf_bound_of_assumption`) and `h12` is the PRF/PRP switching bound
(`CatCrypt.Crypto.SwitchingLemma`). The composition is the advantage triangle
inequality. -/
theorem cascade_prf_bound {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (ε_prf : ℝ≥0∞) (q N : ℕ)
    (h01 : AdvantageA (G 0) (G 1) A ≤ ε_prf)
    (h12 : AdvantageA (G 1) (G 2) A ≤ birthdayTerm q N)
    (h23 : AdvantageA (G 2) (G 3) A ≤ ε_prf) :
    AdvantageA (G 0) (G 3) A ≤ 2 * ε_prf + birthdayTerm q N := by
  calc AdvantageA (G 0) (G 3) A ≤ ε_prf + birthdayTerm q N + ε_prf := by
        adv_game_hop [G 1, G 2]
    _ = 2 * ε_prf + birthdayTerm q N := by ring

/-- **Cascade PRF bound from a base-PRF security assumption.**

If the inner and outer single-query components each satisfy a `PRFAssumption`
(with `Hout.ε ≤ Hin.ε`), and the outer cascade hops are bounded by the
corresponding component PRF advantages (`h01`, `h23` — the reduction's
soundness) with the middle hop bounded by the switching term, then the cascade
advantage is at most `2·Hin.ε + q(q-1)/(2N)`. -/
theorem cascade_prf_bound_of_assumption {α : Type}
    {Finner Fouter : PRFScheme}
    (Hin : PRFAssumption Finner) (Hout : PRFAssumption Fouter) (hε : Hout.ε ≤ Hin.ε)
    (G : ℕ → SPComp α) (A : α → SPComp Bool) (q N : ℕ)
    (xin : Finner.Input) (Ain : Finner.Output → SPComp Bool)
    (xout : Fouter.Input) (Aout : Fouter.Output → SPComp Bool)
    (h01 : AdvantageA (G 0) (G 1) A ≤ PRF_Adv Finner xin Ain)
    (h12 : AdvantageA (G 1) (G 2) A ≤ birthdayTerm q N)
    (h23 : AdvantageA (G 2) (G 3) A ≤ PRF_Adv Fouter xout Aout) :
    AdvantageA (G 0) (G 3) A ≤ 2 * Hin.ε + birthdayTerm q N :=
  cascade_prf_bound G A Hin.ε q N
    (h01.trans (Hin.bound xin Ain))
    h12
    (h23.trans ((Hout.bound xout Aout).trans hε))

/-- **Perfect cascade corollary.** When the base PRF is information-theoretically
secure (`ε_prf = 0`) and there is no collision opportunity (`q ≤ 1`, so the
birthday term is `0`), the cascade advantage is exactly `0`. -/
theorem cascade_prf_perfect {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (q N : ℕ) (hq : q ≤ 1)
    (h01 : AdvantageA (G 0) (G 1) A ≤ 0)
    (h12 : AdvantageA (G 1) (G 2) A ≤ birthdayTerm q N)
    (h23 : AdvantageA (G 2) (G 3) A ≤ 0) :
    AdvantageA (G 0) (G 3) A = 0 := by
  have hbirth : birthdayTerm q N = 0 := by interval_cases q <;> simp [birthdayTerm]
  simpa [hbirth] using cascade_prf_bound G A 0 q N h01 h12 h23

/-! ## Tactic showcase: discharging a cascade hop with `bind_vcgen`

For a bijection-family base function each cascade hop is *perfectly*
indistinguishable — its advantage is `0`. We discharge such a hop by proving the
two single-query games are literally the *same* `SPComp` distribution, using the
`bind_vcgen` run-to-completion tactic: it normalizes the monad structure and, via
the supplied change-of-variables bijection `B.bij x`, collapses `sample k; return
bij(x,k)` to a fresh uniform sample. This is the ε = 0 exact-coupling case that
feeds `cascade_prf_bound` with `ε_prf = 0`. -/

/-- The real and ideal single-query PRF games for a bijection family are the
*same* `SPComp` computation. Proved by `bind_vcgen using (B.bij x)`: the
change-of-variables through the bijection rewrites the keyed evaluation into a
plain uniform sample. -/
theorem bijPRF_game_eq (B : BijPRFFamily) (x : B.Input) :
    PRF_Real B.toPRFScheme x = PRF_Ideal B.toPRFScheme := by
  rw [← SPComp.bind_pure (PRF_Ideal B.toPRFScheme)]
  simp only [PRF_Real, PRF_Ideal, BijPRFFamily.toPRFScheme, SPComp.monad_bind_eq]
  bind_vcgen using (B.bij x)

/-- A bijection-family PRF has PRF advantage `0`, re-proved through the
`bind_vcgen` game-equality `bijPRF_game_eq` (an alternative to the relational
coupling of `bijPRF_perfect`). This is exactly a cascade hop with `ε_prf = 0`. -/
theorem bijPRF_adv_zero_via_vcgen (B : BijPRFFamily) (x : B.Input)
    (A : B.toPRFScheme.Output → SPComp Bool) :
    PRF_Adv B.toPRFScheme x A = 0 := by
  simp only [PRF_Adv, AdvantageA, bijPRF_game_eq, Advantage_self]

/-- A bijection-family base function satisfies the `PRFAssumption` with `ε = 0`,
witnessed by the `bind_vcgen` proof `bijPRF_adv_zero_via_vcgen`. -/
noncomputable def bijPRF_assumption (B : BijPRFFamily) : PRFAssumption B.toPRFScheme :=
  PRFAssumption.of_perfect B.toPRFScheme (bijPRF_adv_zero_via_vcgen B)

end CatCrypt.Examples.PRF

/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SecurityDefs
public import CatCryptCore.Prob.XorBij
public import CatCryptCore.Tactics
public import CatCryptCore.Tactics.AutoMetrics

/-!
# Pseudorandom generators: bijections and the triple construction

A pseudorandom generator that is a *bijection* from seeds to outputs has perfect
security. Following Rosulek, The Joy of Cryptography, §5 (pseudorandom
generators).

If the stretch map `s ↦ stretch s` is a bijection from the seed space onto the
output space, then over a uniform seed the generator output is itself uniform on
the output space. Hence the PRG real game (stretch a uniform seed) and the PRG
ideal game (a fresh uniform output) are perfectly indistinguishable: the PRG
advantage of *every* adversary is exactly `0`.

## Overview

This mirrors the one-time-pad and bijection-PRF arguments
(`CatCrypt.Examples.OTP`, `CatCrypt.Examples.PRF`): the security proof is the
bijection-coupling technique. `liftR_uniform_bij` couples the uniform seed with
the uniform output through the bijection `bij : Seed ≃ Output`;
`liftR_bind`/`liftR_pure` push the coupling through the `sample`-then-`pure`
structure of the real game; and `PRG_Adv_zero_of_rHoare` collapses the advantage
to `0`.

A bijection forces `|Seed| = |Output|`, so a bijection generator is *not*
length-extending. A length-extending PRG has an image that is a vanishing subset
of the output space, so it can only be *computationally* secure. For a
length-doubling generator `G`, the triple construction `G₃` is reduced to `G`
(`triple_prg_bound`): for every adversary `A`, the advantage against `G₃` is at
most the sum of the advantages of two distinguishers against `G`, both defined
in this file (`DoublePRG.tripleRedFirst`, `DoublePRG.tripleRedSecond`).

The earlier statements `triple_prg_uniform_bound` and
`triple_prg_bound_of_assumption` concerned a game with independent seeds, not
`G₃`, and took the hop bounds as hypotheses; the structure `PRGAssumption`
carried a bound `∀ A, PRG_Adv G A ≤ ε`, which no length-extending generator
satisfies for `ε < 1 - |Seed|/|Output|`. All are replaced by
`triple_prg_bound`.

## Main definitions

* `PRGScheme` — a length-preserving/extending generator `stretch : Seed → Output`.
* `PRG_Real` / `PRG_Ideal` / `PRG_Adv` — the PRG distinguishing game and advantage.
* `BijPRG` — a seed→output bijection.
* `BijPRG.toPRGScheme` — the `PRGScheme` it induces (`stretch s = bij s`).
* `DoublePRG`, `DoublePRG.triple` — a length-doubling generator and the
  length-tripling construction.
* `DoublePRG.tripleRedFirst`, `DoublePRG.tripleRedSecond` — the two
  distinguishers against the base generator.

## Main results

* `PRG_Adv_zero_of_rHoare` — a perfectly-indistinguishable PRG has advantage `0`.
* `bijPRG_coupling` — the real and ideal PRG games couple with `eqPost`.
* `bijPRG_perfect` — a bijection PRG has perfect security:
  `PRG_Adv B.toPRGScheme A = 0` for every adversary `A`.
* `triple_prg_bound` — `PRG_Adv G₃ A ≤ PRG_Adv G (tripleRedFirst A) +
  PRG_Adv G (tripleRedSecond A)` for every adversary `A`.

## References

* [Rosulek, The Joy of Cryptography, §5 (pseudorandom generators)]
-/

@[expose] public section

namespace CatCrypt.Examples.PRG

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational

open scoped ENNReal

/-! ## PRG Scheme and Game -/

/-- A pseudorandom generator: a deterministic map `stretch` from a seed space to
an output space.

Security asks that, for a uniform seed, `stretch s` is indistinguishable from a
uniform element of `Output`. -/
structure PRGScheme where
  /-- Seed (input) type -/
  Seed : Type
  /-- Output (stretched) type -/
  Output : Type
  [finSeed : Fintype Seed]
  [neSeed : Nonempty Seed]
  [finOutput : Fintype Output]
  [neOutput : Nonempty Output]
  /-- The deterministic stretch function -/
  stretch : Seed → Output

attribute [instance] PRGScheme.finSeed PRGScheme.neSeed
  PRGScheme.finOutput PRGScheme.neOutput

/-- PRG real game: stretch a uniformly random seed. -/
noncomputable def PRG_Real (G : PRGScheme) : SPComp G.Output := do
  let s ← SPComp.sample G.Seed
  SPComp.pure (G.stretch s)

/-- PRG ideal game: return a uniformly random output. -/
noncomputable def PRG_Ideal (G : PRGScheme) : SPComp G.Output :=
  SPComp.sample G.Output

/-- PRG advantage: distinguishing the stretched seed from a uniform output. -/
noncomputable def PRG_Adv (G : PRGScheme) (A : G.Output → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (PRG_Real G) (PRG_Ideal G) A

/-- If a PRG's real game is perfectly indistinguishable from the ideal game, the
PRG advantage is `0` for every adversary. -/
theorem PRG_Adv_zero_of_rHoare (G : PRGScheme)
    (h : rHoare eqPre (PRG_Real G) (PRG_Ideal G) eqPost) :
    ∀ A, PRG_Adv G A = 0 :=
  advantage_zero_of_rHoare _ _ h

/-! ## Bijection PRG -/

/-- A PRG given by a bijection `bij : Seed ≃ Output`.

For a uniform seed, `bij` maps the uniform seed distribution onto the uniform
output distribution, which is the source of perfect security. -/
structure BijPRG where
  /-- Seed type -/
  Seed : Type
  /-- Output type -/
  Output : Type
  [finSeed : Fintype Seed]
  [neSeed : Nonempty Seed]
  [finOutput : Fintype Output]
  [neOutput : Nonempty Output]
  /-- A bijection from seeds to outputs -/
  bij : Seed ≃ Output

attribute [instance] BijPRG.finSeed BijPRG.neSeed
  BijPRG.finOutput BijPRG.neOutput

/-- The `PRGScheme` induced by a bijection: `stretch s = bij s`. -/
def BijPRG.toPRGScheme (B : BijPRG) : PRGScheme where
  Seed := B.Seed
  Output := B.Output
  stretch := fun s => B.bij s

/-! ## Perfect Security -/

/-- Coupling: for a bijection PRG the real and ideal games are equidistributed.

Over a uniform seed `s`, the real game returns `bij s` while the ideal game
returns a fresh uniform output `r`; `liftR_uniform_bij B.bij` couples them so
that `bij s = r`, so the two games agree pointwise. -/
theorem bijPRG_coupling (B : BijPRG) :
    rHoare eqPre
      (PRG_Real B.toPRGScheme)
      (PRG_Ideal B.toPRGScheme)
      eqPost := by
  simp only [PRG_Real, PRG_Ideal, BijPRG.toPRGScheme, SPComp.monad_bind_eq]
  ssprove_couple_bij (B.bij)

/-- **A bijection PRG has perfect security**: every adversary has PRG advantage
exactly `0`. -/
theorem bijPRG_perfect (B : BijPRG) (A : B.toPRGScheme.Output → SPComp Bool) :
    PRG_Adv B.toPRGScheme A = 0 := by
  grind [PRG_Adv_zero_of_rHoare, bijPRG_coupling]

/-! ## Example: the XOR PRG over `Bool`

`G(s) = s ⊕ c` for a fixed mask `c` is the bijection `boolXorBij c`; it is a
(non-extending) bijection generator and inherits perfect security. -/

/-- The XOR generator over `Bool` as a bijection PRG: `bij = boolXorBij c`. -/
def boolXorPRG (c : Bool) : BijPRG where
  Seed := Bool
  Output := Bool
  bij := boolXorBij c

/-- The XOR generator over `Bool` has perfect PRG security. -/
theorem boolXorPRG_perfect (c : Bool)
    (A : (boolXorPRG c).toPRGScheme.Output → SPComp Bool) :
    PRG_Adv (boolXorPRG c).toPRGScheme A = 0 := by
  grind [bijPRG_perfect, boolXorPRG]

open CatCrypt.Tactic

/-! ### The bijection case by `bind_vcgen`

For a bijection PRG the real and ideal games are the *same* `SPComp`
distribution. The `bind_vcgen` run-to-completion tactic proves this: through the
change-of-variables bijection `B.bij` it collapses `sample s; return bij s` to a
fresh uniform sample. -/

/-- The real and ideal PRG games for a bijection PRG are the *same* `SPComp`
computation. Proved by `bind_vcgen using B.bij`: the change-of-variables through
the bijection rewrites the stretched seed into a plain uniform sample. -/
theorem bijPRG_game_eq (B : BijPRG) :
    PRG_Real B.toPRGScheme = PRG_Ideal B.toPRGScheme := by
  rw [PRG_Ideal, ← SPComp.bind_pure (SPComp.sample B.toPRGScheme.Output)]
  simp only [PRG_Real, BijPRG.toPRGScheme, SPComp.monad_bind_eq]
  bind_vcgen using B.bij

/-- A bijection PRG has PRG advantage `0`, re-proved through the `bind_vcgen`
game-equality `bijPRG_game_eq` (an alternative to the relational coupling of
`bijPRG_perfect`). -/
theorem bijPRG_adv_zero_via_vcgen (B : BijPRG)
    (A : B.toPRGScheme.Output → SPComp Bool) :
    PRG_Adv B.toPRGScheme A = 0 := by
  simp_all [PRG_Adv, AdvantageA, bijPRG_game_eq, Advantage_self]

/-! ## Triple-from-double PRG: the reduction

Given a *length-doubling* base generator `G : Seed → Seed × Seed`, the
length-tripling construction

    `G₃(s) = let (a, b) := G(s); let (c, d) := G(a); (c, d, b)`

is a PRG whenever `G` is (Rosulek, The Joy of Cryptography, §5.3). The
reduction runs three games on the output space `Seed × Seed × Seed`:

| Game | Output |
|------|--------|
| `H₀` = `PRG_Real G₃` | `G₃(s)` for a uniform seed `s` |
| `H₁` = `tripleHyb` | `(G(a).1, G(a).2, b)` for uniform `a, b` |
| `H₂` = `PRG_Ideal G₃` | a uniform triple |

The hop `H₀ → H₁` replaces the first call `G(s)` by a uniform pair; the
distinguisher `tripleRedFirst A` receives the pair and finishes the
construction. The hop `H₁ → H₂` replaces the second call `G(a)` by a uniform
pair; the distinguisher `tripleRedSecond A` receives the pair and samples the
last component itself. Both distinguishers attack the base generator `G`, and
each hop is an equality of games, so `triple_prg_bound` states, for every
adversary `A`,

    `PRG_Adv G₃ A ≤ PRG_Adv G (tripleRedFirst A) + PRG_Adv G (tripleRedSecond A)`. -/

/-- A length-doubling base generator `stretch : Seed → Seed × Seed`, the input to
the triple construction. -/
structure DoublePRG where
  /-- Seed type -/
  Seed : Type
  [finSeed : Fintype Seed]
  [neSeed : Nonempty Seed]
  /-- The length-doubling stretch function -/
  stretch : Seed → Seed × Seed

attribute [instance] DoublePRG.finSeed DoublePRG.neSeed

/-- The length-tripling construction: apply `G` twice, rearrange outputs. -/
def DoublePRG.triple (G : DoublePRG) (s : G.Seed) : G.Seed × G.Seed × G.Seed :=
  let (a, b) := G.stretch s
  let (c, d) := G.stretch a
  (c, d, b)

/-- The base doubling generator as a `PRGScheme` (`Output = Seed × Seed`). -/
def DoublePRG.toInnerPRG (G : DoublePRG) : PRGScheme where
  Seed := G.Seed
  Output := G.Seed × G.Seed
  stretch := G.stretch

/-- The triple construction as a `PRGScheme` (`Output = Seed × Seed × Seed`). -/
def DoublePRG.toTriplePRG (G : DoublePRG) : PRGScheme where
  Seed := G.Seed
  Output := G.Seed × G.Seed × G.Seed
  stretch := G.triple

/-- Intermediate game `H₁`: the first call of `G` is replaced by a uniform pair
`(a, b)`, the second call `G(a)` is kept. -/
noncomputable def DoublePRG.tripleHyb (G : DoublePRG) :
    SPComp (G.Seed × G.Seed × G.Seed) := do
  let a ← SPComp.sample G.Seed
  let b ← SPComp.sample G.Seed
  SPComp.pure ((G.stretch a).1, (G.stretch a).2, b)

/-- Distinguisher against `G` for the hop `H₀ → H₁`: on a pair `(a, b)` it
expands `a` with `G` and runs `A` on `(G(a).1, G(a).2, b)`. -/
def DoublePRG.tripleRedFirst (G : DoublePRG)
    (A : G.Seed × G.Seed × G.Seed → SPComp Bool) :
    G.Seed × G.Seed → SPComp Bool :=
  fun ab => A ((G.stretch ab.1).1, (G.stretch ab.1).2, ab.2)

/-- Distinguisher against `G` for the hop `H₁ → H₂`: on a pair `(c, d)` it
samples a uniform seed `b` and runs `A` on `(c, d, b)`. -/
noncomputable def DoublePRG.tripleRedSecond (G : DoublePRG)
    (A : G.Seed × G.Seed × G.Seed → SPComp Bool) :
    G.Seed × G.Seed → SPComp Bool :=
  fun cd => SPComp.bind (SPComp.sample G.Seed) fun b => A (cd.1, cd.2, b)

/-- `H₀` against `A` is the real `G` game against `tripleRedFirst A`. -/
theorem DoublePRG.real_bind_eq_redFirst (G : DoublePRG)
    (A : G.Seed × G.Seed × G.Seed → SPComp Bool) :
    (PRG_Real G.toTriplePRG).bind A = (PRG_Real G.toInnerPRG).bind (G.tripleRedFirst A) := by
  show ((SPComp.sample G.Seed).bind fun s => SPComp.pure (G.triple s)).bind A =
    ((SPComp.sample G.Seed).bind fun s => SPComp.pure (G.stretch s)).bind (G.tripleRedFirst A)
  simp only [DoublePRG.triple, DoublePRG.tripleRedFirst, SPComp.bind_assoc, SPComp.pure_bind]

/-- The ideal `G` game against `tripleRedFirst A` is `H₁` against `A`. -/
theorem DoublePRG.ideal_bind_redFirst_eq (G : DoublePRG)
    (A : G.Seed × G.Seed × G.Seed → SPComp Bool) :
    (PRG_Ideal G.toInnerPRG).bind (G.tripleRedFirst A) = G.tripleHyb.bind A := by
  show (SPComp.sample (G.Seed × G.Seed)).bind (G.tripleRedFirst A) = G.tripleHyb.bind A
  simp only [DoublePRG.tripleHyb, DoublePRG.tripleRedFirst, SPComp.sample_prod_eq,
    SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- `H₁` against `A` is the real `G` game against `tripleRedSecond A`. -/
theorem DoublePRG.hyb_bind_eq_redSecond (G : DoublePRG)
    (A : G.Seed × G.Seed × G.Seed → SPComp Bool) :
    G.tripleHyb.bind A = (PRG_Real G.toInnerPRG).bind (G.tripleRedSecond A) := by
  show G.tripleHyb.bind A =
    ((SPComp.sample G.Seed).bind fun s => SPComp.pure (G.stretch s)).bind (G.tripleRedSecond A)
  simp only [DoublePRG.tripleHyb, DoublePRG.tripleRedSecond, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]

/-- The ideal `G` game against `tripleRedSecond A` is `H₂` against `A`. -/
theorem DoublePRG.ideal_bind_redSecond_eq (G : DoublePRG)
    (A : G.Seed × G.Seed × G.Seed → SPComp Bool) :
    (PRG_Ideal G.toInnerPRG).bind (G.tripleRedSecond A) =
      (PRG_Ideal G.toTriplePRG).bind A := by
  show (SPComp.sample (G.Seed × G.Seed)).bind (G.tripleRedSecond A) =
    (SPComp.sample (G.Seed × G.Seed × G.Seed)).bind A
  simp only [DoublePRG.tripleRedSecond, SPComp.sample_prod_eq, SPComp.bind_assoc,
    SPComp.pure_bind]

/-- **Triple-from-double PRG bound.** For every adversary `A` against the triple
construction,

    `PRG_Adv G₃ A ≤ PRG_Adv G (tripleRedFirst A) + PRG_Adv G (tripleRedSecond A)`,

where both distinguishers attack the base doubling generator `G`. -/
theorem triple_prg_bound (G : DoublePRG) (A : G.Seed × G.Seed × G.Seed → SPComp Bool) :
    PRG_Adv G.toTriplePRG A ≤
      PRG_Adv G.toInnerPRG (G.tripleRedFirst A) + PRG_Adv G.toInnerPRG (G.tripleRedSecond A) := by
  unfold PRG_Adv AdvantageA
  rw [G.real_bind_eq_redFirst A, ← G.ideal_bind_redSecond_eq A]
  refine (advantage_triangle _ (G.tripleHyb.bind A) _).trans (add_le_add ?_ ?_)
  · rw [← G.ideal_bind_redFirst_eq A]
  · rw [G.hyb_bind_eq_redSecond A]

end CatCrypt.Examples.PRG

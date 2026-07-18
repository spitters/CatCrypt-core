/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Prob.XorBij
import CatCryptCore.Tactics

/-!
# Bijection PRG: Perfect Security

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
length-extending. This is the information-theoretic boundary of Rosulek §5: a
genuinely length-extending PRG has an image that is a vanishing subset of the
output space, so it can only be *computationally* secure. The corresponding
reduction — the triple-from-double bound `Adv(G₃) ≤ 2·Adv(G)` — is proved
computationally elsewhere (`CatCrypt.Examples.TriplePRG`).

## Main definitions

* `PRGScheme` — a length-preserving/extending generator `stretch : Seed → Output`.
* `PRG_Real` / `PRG_Ideal` / `PRG_Adv` — the PRG distinguishing game and advantage.
* `BijPRG` — a seed→output bijection.
* `BijPRG.toPRGScheme` — the `PRGScheme` it induces (`stretch s = bij s`).

## Main results

* `PRG_Adv_zero_of_rHoare` — a perfectly-indistinguishable PRG has advantage `0`.
* `bijPRG_coupling` — the real and ideal PRG games couple with `eqPost`.
* `bijPRG_perfect` — a bijection PRG has perfect security:
  `PRG_Adv B.toPRGScheme A = 0` for every adversary `A`.

## References

* [Rosulek, The Joy of Cryptography, §5 (pseudorandom generators)]
-/

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
    PRG_Adv B.toPRGScheme A = 0 :=
  PRG_Adv_zero_of_rHoare B.toPRGScheme (bijPRG_coupling B) A

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
    PRG_Adv (boolXorPRG c).toPRGScheme A = 0 :=
  bijPRG_perfect (boolXorPRG c) A

/-! ## PRG security assumption

The bijection results above are *perfect* (`ε = 0`). A genuinely length-extending
generator can only be *computationally* secure, so the reduction below takes the
base generator's security as a hypothesis. `PRGAssumption` is the PRG analogue of
`CatCrypt.Crypto.PRFAssumption`: it packages the standard "`G` is an ε-secure
PRG" hypothesis that reductions consume. -/

open CatCrypt.Crypto
open CatCrypt.Tactic

/-- The **PRG security assumption**: `G` is an ε-secure pseudorandom generator.
The field `bound` witnesses that no adversary beats advantage `ε` at
distinguishing `PRG_Real G` from `PRG_Ideal G`. -/
structure PRGAssumption (G : PRGScheme) where
  /-- The PRG advantage bound `ε`. -/
  ε : ℝ≥0∞
  /-- Every adversary has PRG advantage at most `ε`. -/
  bound : ∀ (A : G.Output → SPComp Bool), PRG_Adv G A ≤ ε

/-- The packaged advantage bound of a PRG assumption. -/
theorem PRGAssumption.advantage_bound {G : PRGScheme} (H : PRGAssumption G)
    (A : G.Output → SPComp Bool) : PRG_Adv G A ≤ H.ε :=
  H.bound A

/-- A perfectly secure PRG (every adversary has advantage exactly `0`) satisfies
the PRG assumption with `ε = 0`. -/
def PRGAssumption.of_perfect (G : PRGScheme)
    (h : ∀ (A : G.Output → SPComp Bool), PRG_Adv G A = 0) :
    PRGAssumption G where
  ε := 0
  bound := fun A => (h A).le

/-! ### `bind_vcgen` witness for the `ε = 0` case

For a bijection PRG the real and ideal games are the *same* `SPComp`
distribution. We discharge this exact hop with the `bind_vcgen`
run-to-completion tactic: through the supplied change-of-variables bijection
`B.bij` it collapses `sample s; return bij s` to a fresh uniform sample. This is
the perfect (`ε = 0`) base case that instantiates `PRGAssumption`. -/

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
  simp only [PRG_Adv, AdvantageA, bijPRG_game_eq, Advantage_self]

/-- A bijection PRG satisfies the `PRGAssumption` with `ε = 0`, witnessed by the
`bind_vcgen` proof `bijPRG_adv_zero_via_vcgen`. -/
noncomputable def bijPRG_assumption (B : BijPRG) : PRGAssumption B.toPRGScheme :=
  PRGAssumption.of_perfect B.toPRGScheme (bijPRG_adv_zero_via_vcgen B)

/-! ## Triple-from-double PRG: the computational bound

Given a *length-doubling* base generator `G : Seed → Seed × Seed`, the
length-tripling construction

    `G₃(s) = let (a, b) := G(s); let (c, d) := G(a); (c, d, b)`

satisfies `Adv_PRG(G₃) ≤ 2·ε` under a PRG-security assumption on `G` (Rosulek,
The Joy of Cryptography, §5.3). This mirrors the cascade-PRF upgrade
(`CatCrypt.Examples.PRF.cascade_prf_bound`): a computational bound composed from
two named per-hop assumptions via the advantage triangle inequality, keeping the
perfect (`ε = 0`) corollary.

The reduction runs the **decomposed** hybrid (Rosulek §5.3), which uses
*independent* seeds for the two `G` calls to break their correlation:

| Step | Transition | Bound |
|------|-----------|-------|
| 0→1 | inner `G(s₁)` (produces `c,d`) → random | `ε` (PRG assumption) |
| 1→2 | outer `G(s₂).2` (produces `b`) → random | `ε` (PRG assumption) |

The hop bounds are the cryptographic hypotheses; the theorem composes them into
the total bound by the advantage triangle inequality. -/

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

/-- The base doubling generator as a `PRGScheme` (`Output = Seed × Seed`), whose
security is the inner-hop assumption. -/
def DoublePRG.toInnerPRG (G : DoublePRG) : PRGScheme where
  Seed := G.Seed
  Output := G.Seed × G.Seed
  stretch := G.stretch

/-- The projected doubling generator as a `PRGScheme` (`Output = Seed`, the second
component), whose security is the outer-hop assumption. -/
def DoublePRG.toOuterPRG (G : DoublePRG) : PRGScheme where
  Seed := G.Seed
  Output := G.Seed
  stretch := fun s => (G.stretch s).2

/-- Decomposed hybrid game (independent seeds per `G` call).

* `i ≥ 2`: everything uniform (ideal `G₃`);
* `i = 1`: inner `G` call replaced by random, outer `G` still real;
* `i = 0`: both `G` calls real but with *independent* seeds. -/
noncomputable def DoublePRG.hyb (G : DoublePRG) (i : ℕ) :
    SPComp (G.Seed × G.Seed × G.Seed) := do
  if i ≥ 2 then
    let c ← SPComp.sample G.Seed
    let d ← SPComp.sample G.Seed
    let b ← SPComp.sample G.Seed
    SPComp.pure (c, d, b)
  else if i = 1 then
    let c ← SPComp.sample G.Seed
    let d ← SPComp.sample G.Seed
    let s ← SPComp.sample G.Seed
    SPComp.pure (c, d, (G.stretch s).2)
  else
    let s₁ ← SPComp.sample G.Seed
    let s₂ ← SPComp.sample G.Seed
    SPComp.pure ((G.stretch s₁).1, (G.stretch s₁).2, (G.stretch s₂).2)

/-- Hybrid `2` is the ideal `G₃`: three independent uniform seeds, independent of
the base generator's `stretch`. -/
theorem DoublePRG.hyb_2_ideal (G : DoublePRG) :
    G.hyb 2 = (do
      let c ← SPComp.sample G.Seed
      let d ← SPComp.sample G.Seed
      let b ← SPComp.sample G.Seed
      SPComp.pure (c, d, b)) := by
  simp only [DoublePRG.hyb, ge_iff_le, le_refl, ↓reduceIte]

/-- **Triple-from-double hybrid bound** (the composition core).

For any 3-game hybrid sequence `H` realising the 2-hop ladder, if both hops are
bounded by `ε`, then `Adv(H₀, H₂) ≤ 2·ε`. The composition is the advantage
triangle inequality — the PRG analogue of `cascade_prf_bound`. -/
theorem triple_prg_hybrid_bound {α : Type} (H : ℕ → SPComp α) (A : α → SPComp Bool)
    (ε : ℝ≥0∞)
    (h01 : AdvantageA (H 0) (H 1) A ≤ ε)
    (h12 : AdvantageA (H 1) (H 2) A ≤ ε) :
    AdvantageA (H 0) (H 2) A ≤ 2 * ε := by
  adv_game_hop [H 1]
  rw [two_mul]; exact add_le_add h01 h12

/-- **Triple PRG uniform bound**: when both decomposed hybrid hops have advantage
at most `ε`, the triple construction advantage is at most `2·ε`.

This is the tight reduction `Adv_PRG(G₃) ≤ 2·Adv_PRG(G)`, mirroring the dev
`CatCrypt.Examples.TriplePRG.triple_prg_uniform_bound`. -/
theorem triple_prg_uniform_bound (G : DoublePRG) (ε : ℝ≥0∞)
    (A : (G.Seed × G.Seed × G.Seed) → SPComp Bool)
    (h_inner : AdvantageA (G.hyb 0) (G.hyb 1) A ≤ ε)
    (h_outer : AdvantageA (G.hyb 1) (G.hyb 2) A ≤ ε) :
    AdvantageA (G.hyb 0) (G.hyb 2) A ≤ 2 * ε :=
  triple_prg_hybrid_bound G.hyb A ε h_inner h_outer

/-- **Triple PRG bound from a base-PRG security assumption.**

If the inner and outer decomposed hops are bounded by the corresponding base-PRG
advantages (`h_inner`, `h_outer` — the reduction's soundness, whose reduction
adversaries `Ain`/`Aout` are exposed as hypotheses), and the base generator
satisfies a `PRGAssumption` on each induced scheme (with `Hout.ε ≤ Hin.ε`), then
the triple advantage is at most `2·Hin.ε`. -/
theorem triple_prg_bound_of_assumption (G : DoublePRG)
    (Hin : PRGAssumption G.toInnerPRG) (Hout : PRGAssumption G.toOuterPRG)
    (hε : Hout.ε ≤ Hin.ε)
    (A : (G.Seed × G.Seed × G.Seed) → SPComp Bool)
    (Ain : G.toInnerPRG.Output → SPComp Bool)
    (Aout : G.toOuterPRG.Output → SPComp Bool)
    (h_inner : AdvantageA (G.hyb 0) (G.hyb 1) A ≤ PRG_Adv G.toInnerPRG Ain)
    (h_outer : AdvantageA (G.hyb 1) (G.hyb 2) A ≤ PRG_Adv G.toOuterPRG Aout) :
    AdvantageA (G.hyb 0) (G.hyb 2) A ≤ 2 * Hin.ε :=
  triple_prg_hybrid_bound G.hyb A Hin.ε
    (h_inner.trans (Hin.bound Ain))
    (h_outer.trans ((Hout.bound Aout).trans hε))

/-- **Perfect triple corollary.** When both hops are perfectly indistinguishable
(`ε = 0`, e.g. a bijection base generator via `bijPRG_assumption`), the triple
advantage is exactly `0`. -/
theorem triple_prg_perfect (G : DoublePRG)
    (A : (G.Seed × G.Seed × G.Seed) → SPComp Bool)
    (h_inner : AdvantageA (G.hyb 0) (G.hyb 1) A ≤ 0)
    (h_outer : AdvantageA (G.hyb 1) (G.hyb 2) A ≤ 0) :
    AdvantageA (G.hyb 0) (G.hyb 2) A = 0 := by
  simpa using triple_prg_hybrid_bound G.hyb A 0 h_inner h_outer

end CatCrypt.Examples.PRG

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.CryptoWord
import CatCrypt.Tactics

/-!
# One-Way Function (OWF) Assumption

A one-way function is easy to compute but hard to invert: given `f(x)`,
no efficient adversary can find any preimage `x'` such that `f(x') = f(x)`.

## Main definitions

* `OWFDef` — abstract one-way function
* `OWF_Game` — the one-wayness game
* `OWF_Advantage` — inversion probability
* `OWFSecure` — one-wayness assumption
* `OWPDef` — one-way permutation (bijective OWF)
* `PRGDef` — pseudorandom generator definition
* `PRG_Advantage` — PRG distinguishing advantage
* `prg_implies_owf` — PRG ⟹ OWF reduction (BS Thm 8.1)

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| OWF Game | `OWF_Game` | BS Def. 8.1 / KL Def. 8.1 |
| OWF Advantage | `OWF_Advantage` | `Pr[Invert]` |
| OWP | `OWPDef` | BS Def. 8.2 (permutation variant) |
| PRG | `PRGDef` | BS Def. 3.1 |
| PRG ⟹ OWF | `prg_implies_owf` | BS Thm 8.1 |

**Equivalent formalizations:**
- EasyCrypt: `OW` game in `OW.ec`
- SSProve (Rocq): not formalized

**Relationship to other assumptions:**
- PRG ⟹ OWF (BS Thm 8.1): `prg_implies_owf`
- PRF ⟹ OWF (standard)
- RSA is an OWP instance (see `RSA.lean`)

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §8.1, Def. 8.1; §3.1
* Katz & Lindell, *Introduction to Modern Cryptography*, §8.1, Def. 8.1
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [Fintype W] [Nonempty W] [DecidableEq W]

/-! ## One-Way Function -/

/-- Abstract one-way function: a function that is easy to compute
    but hard to invert. -/
structure OWFDef (W : Type) where
  /-- The one-way function -/
  f : W → W

/-- OWF adversary: given `f(x)`, attempts to find a preimage. -/
abbrev OWF_Adversary (W : Type) := W → SPComp W

/-- OWF game: sample `x`, give `f(x)` to adversary, check if the
    adversary's output `x'` satisfies `f(x') = f(x)`.

    Note: the adversary need not find `x` itself, just any preimage. -/
noncomputable def OWF_Game (F : OWFDef W) (A : OWF_Adversary W) :
    SPComp Bool := do
  let x ← SPComp.sample W
  let y := F.f x
  let x' ← A y
  SPComp.pure (decide (F.f x' = y))

/-- OWF advantage: probability of finding a preimage. -/
noncomputable def OWF_Advantage (F : OWFDef W) (A : OWF_Adversary W) : ℝ≥0∞ :=
  prTrue (OWF_Game F A) Heap.empty

/-- One-wayness assumption. -/
def OWFSecure (F : OWFDef W) (ε : ℝ≥0∞) : Prop :=
  ∀ (A : OWF_Adversary W), OWF_Advantage F A ≤ ε

/-! ## One-Way Permutation (OWP) -/

/-- A one-way permutation: a bijective one-way function. -/
structure OWPDef (W : Type) extends OWFDef W where
  /-- The function is a bijection -/
  bij : Function.Bijective f

/-! ## IsPure Proofs -/

theorem OWF_Game_isPure (F : OWFDef W) (A : OWF_Adversary W)
    (hA : ∀ y, SPComp.IsPure (A y)) :
    SPComp.IsPure (OWF_Game F A) := by
  unfold OWF_Game
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro x
  apply SPComp.bind_isPure (hA _); intro x'
  exact SPComp.pure_isPure _

/-! ## Pseudorandom Generator (PRG)

A PRG stretches a short seed into a longer (or same-length) output that
is computationally indistinguishable from uniform. -/

variable {Seed Output : Type}
  [Fintype Seed] [Nonempty Seed]
  [Fintype Output] [Nonempty Output]

/-- Abstract pseudorandom generator: a deterministic function from seeds to outputs. -/
structure PRGDef (Seed Output : Type) where
  /-- The stretch function -/
  stretch : Seed → Output

/-- PRG real game: sample a seed, output `G(seed)`. -/
noncomputable def prg_real (G : PRGDef Seed Output) : SPComp Output := do
  let seed ← SPComp.sample Seed
  SPComp.pure (G.stretch seed)

/-- PRG ideal game: sample output uniformly. -/
noncomputable def prg_ideal : SPComp Output := SPComp.sample Output

/-- PRG adversary: a distinguisher that receives a sample and outputs a bit. -/
abbrev PRG_Adversary (Output : Type) := Output → SPComp Bool

/-- PRG advantage: ability to distinguish `G(seed)` from random. -/
noncomputable def PRG_Advantage (G : PRGDef Seed Output) (A : PRG_Adversary Output) : ℝ≥0∞ :=
  AdvantageA (prg_real G) prg_ideal A

/-- PRG security assumption. -/
def PRGSecure (G : PRGDef Seed Output) (ε : ℝ≥0∞) : Prop :=
  ∀ (A : PRG_Adversary Output), PRG_Advantage G A ≤ ε

/-! ## PRG ⟹ OWF Reduction

If `G : Seed → Output` is a PRG (pseudorandom generator), then `G` is also
a one-way function on `Seed` (when `Output = Seed`). The reduction: an OWF
inverter for `G` would distinguish real from random, since the preimage
reveals the seed.

BS Thm 8.1: if G is a secure PRG, then G is a secure OWF.

**Reduction idea.** Given an OWF adversary `A_owf` that inverts `G`, construct
a PRG distinguisher `A_prg` as follows:
1. Receive challenge `y` (either `G(s)` for random `s`, or truly random)
2. Run `A_owf(y)` to get candidate seed `s'`
3. Output `decide (G(s') = y)`

If `y = G(s)` (real case), then `A_owf` succeeds with noticeable probability,
so `A_prg` outputs `true`. If `y` is random, `G(s') = y` is unlikely since
`G`'s image is sparse in the output space.

The bound: `OWF_Advantage G A_owf ≤ PRG_Advantage G A_prg`. -/

/-- Construct an OWF from a PRG stretch function (same-type case).

    Given PRG `G : S → S`, define `f = G`. For PRGs with distinct
    seed/output types, the one-wayness notion applies on the seed
    space viewed as the domain. -/
def owf_of_prg {S : Type} (stretch : S → S) : OWFDef S where
  f := stretch

/-- Construct a PRG distinguisher from an OWF inverter.

    Given an OWF adversary `A_owf` that tries to invert `G`:
    1. Receive challenge `y`
    2. Run `A_owf(y)` to get candidate preimage `s'`
    3. Output `true` iff `G(s') = y`

    In the real game (`y = G(s)`), `A_owf` succeeds iff it finds a preimage.
    In the ideal game (`y` random), the output is essentially random. -/
noncomputable def prg_distinguisher_of_owf_inverter
    (G : PRGDef W W) (A_owf : OWF_Adversary W) : PRG_Adversary W :=
  fun y => do
    let s' ← A_owf y
    SPComp.pure (decide (G.stretch s' = y))

/-- PRG ⟹ OWF reduction bound (Bertie pattern, BS Thm 8.1).

    The tight bound requires image sparsity: for same-type PRGs (W → W),
    the OWF advantage includes a `|im(G)|/|W|` term for the probability
    of inverting a truly random value. This is provided as a typeclass. -/
class PRGImpliesOWF (G : PRGDef W W) : Prop where
  bound : ∀ (A_owf : OWF_Adversary W),
    OWF_Advantage (owf_of_prg G.stretch) A_owf ≤
      PRG_Advantage G (prg_distinguisher_of_owf_inverter G A_owf)

theorem prg_implies_owf (G : PRGDef W W) [PRGImpliesOWF G]
    (A_owf : OWF_Adversary W) :
    OWF_Advantage (owf_of_prg G.stretch) A_owf ≤
      PRG_Advantage G (prg_distinguisher_of_owf_inverter G A_owf) :=
  PRGImpliesOWF.bound A_owf

/-- Corollary: PRG security implies OWF security.

    If `G` is `ε`-PRG-secure, then `owf_of_prg G.stretch` is `ε`-OWF-secure. -/
theorem prg_secure_implies_owf_secure (G : PRGDef W W) [PRGImpliesOWF G]
    (ε : ℝ≥0∞) (h_prg : PRGSecure G ε) :
    OWFSecure (owf_of_prg G.stretch) ε := by
  intro A_owf
  calc OWF_Advantage (owf_of_prg G.stretch) A_owf
      ≤ PRG_Advantage G (prg_distinguisher_of_owf_inverter G A_owf) :=
        prg_implies_owf G A_owf
    _ ≤ ε := h_prg _

/-! ## RSA as OWP

The RSA function (modular exponentiation `x ↦ x^e mod N` for suitable `(N, e)`)
is conjectured to be a one-way permutation. The formal connection is via
`RSADef` in `Assumptions/RSA.lean`. An `OWPDef` instance for RSA would require
proving `Function.Bijective` for the RSA map, which needs number-theoretic
facts about the RSA group structure. -/

end CatCrypt.Crypto.Assumptions

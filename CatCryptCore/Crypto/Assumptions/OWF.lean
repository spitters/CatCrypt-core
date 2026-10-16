/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Crypto.ForkingLemma
public import CatCryptCore.Tactics

/-!
# One-Way Function (OWF) Assumption

A one-way function is easy to compute but hard to invert: given `f(x)`,
no efficient adversary can find any preimage `x'` such that `f(x') = f(x)`.

## Main definitions

* `OWFDef` — abstract one-way function
* `OWF_Game` — the one-wayness game
* `OWF_Advantage` — inversion probability
* `OWPDef` — one-way permutation (bijective OWF)
* `PRGDef` — pseudorandom generator definition
* `PRG_Advantage` — PRG distinguishing advantage
* `prg_distinguisher_of_owf_inverter` — PRG distinguisher from an OWF inverter
* `owf_le_prg` — PRG ⟹ OWF reduction (BS Thm 8.1): for every inverter `A`,
  `OWF_Advantage (owf_of_prg G.stretch) A ≤
    PRG_Advantage G (prg_distinguisher_of_owf_inverter G A) + |im G| / |W|`

The predicates `OWFSecure F ε` and `PRGSecure G ε` (`∀ A, … ≤ ε`), the class
`PRGImpliesOWF` (whose only field was the conclusion of `prg_implies_owf`), and the
theorems `prg_implies_owf` and `prg_secure_implies_owf_secure` are removed; `owf_le_prg`
replaces them.

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| OWF Game | `OWF_Game` | BS Def. 8.1 / KL Def. 8.1 |
| OWF Advantage | `OWF_Advantage` | `Pr[Invert]` |
| OWP | `OWPDef` | BS Def. 8.2 (permutation variant) |
| PRG | `PRGDef` | BS Def. 3.1 |
| PRG ⟹ OWF | `owf_le_prg` | BS Thm 8.1 |

**Equivalent formalizations:**
- EasyCrypt: `OW` game in `OW.ec`
- SSProve (Rocq): not formalized

**Relationship to other assumptions:**
- PRG ⟹ OWF (BS Thm 8.1): `owf_le_prg`
- PRF ⟹ OWF (standard)
- RSA is an OWP instance (see `RSA.lean`)

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §8.1, Def. 8.1; §3.1
* Katz & Lindell, *Introduction to Modern Cryptography*, §8.1, Def. 8.1
-/

@[expose] public section

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
  simp_all [SPComp.bind_isPure, SPComp.pure_isPure]

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

In the real case (`y = G(s)`) the distinguisher outputs `true` exactly when `A_owf`
inverts, so its success probability is the OWF advantage. In the ideal case (`y`
uniform) it can output `true` only if `y` lies in the image of `G`, which has
probability `|im G| / |W|`. Hence

    OWF_Advantage G A_owf ≤ PRG_Advantage G A_prg + |im G| / |W|. -/

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

/-- A continuation whose success probability is at most `ε` from every state keeps the
    success probability of the composed computation at most `ε`. -/
private theorem prTrue_bind_le_const {α : Type} (c : SPComp α) (k : α → SPComp Bool)
    (ε : ℝ≥0∞) (h₀ : Heap) (hk : ∀ a h', prTrue (k a) h' ≤ ε) :
    prTrue (c.bind k) h₀ ≤ ε :=
  (ForkingLemma.prTrue_bind_mono_const ε c k (fun _ => SPComp.pure true) h₀ fun a h' => by
      rw [ForkingLemma.prTrue_pure_bool]; simpa using hk a h').trans
    (mul_le_of_le_one_right' (prTrue_le_one _ _))

/-- The real PRG game run against `prg_distinguisher_of_owf_inverter G A_owf` is the OWF
    game of `owf_of_prg G.stretch` against `A_owf`. -/
theorem owf_game_eq_prg_real (G : PRGDef W W) (A_owf : OWF_Adversary W) :
    OWF_Game (owf_of_prg G.stretch) A_owf =
      (prg_real G).bind (prg_distinguisher_of_owf_inverter G A_owf) := by
  unfold OWF_Game prg_real prg_distinguisher_of_owf_inverter owf_of_prg
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- In the ideal PRG game the distinguisher `prg_distinguisher_of_owf_inverter G A_owf`
    outputs `true` with probability at most `|im G| / |W|`. -/
theorem prTrue_prg_ideal_distinguisher_le (G : PRGDef W W) (A_owf : OWF_Adversary W) :
    prTrue ((prg_ideal (Output := W)).bind (prg_distinguisher_of_owf_inverter G A_owf))
        Heap.empty ≤
      ((Finset.univ.image G.stretch).card : ℝ≥0∞) / Fintype.card W := by
  unfold prg_ideal
  rw [prTrue_bind_sample]
  have hpt : ∀ y, prTrue (prg_distinguisher_of_owf_inverter G A_owf y) Heap.empty ≤
      if y ∈ Finset.univ.image G.stretch then 1 else 0 := by
    intro y
    split_ifs with hy
    · exact prTrue_le_one _ _
    · unfold prg_distinguisher_of_owf_inverter
      simp only [SPComp.monad_bind_eq]
      refine prTrue_bind_le_const _ _ _ _ fun s' h' => ?_
      have hne : G.stretch s' ≠ y := fun h => hy (Finset.mem_image.mpr ⟨s', by simp, h⟩)
      simp [ForkingLemma.prTrue_pure_bool, hne]
  calc ∑ y : W, (Fintype.card W : ℝ≥0∞)⁻¹ *
          prTrue (prg_distinguisher_of_owf_inverter G A_owf y) Heap.empty
      ≤ ∑ y : W, (Fintype.card W : ℝ≥0∞)⁻¹ *
          (if y ∈ Finset.univ.image G.stretch then 1 else 0) :=
        Finset.sum_le_sum fun y _ => by gcongr; exact hpt y
    _ = ((Finset.univ.image G.stretch).card : ℝ≥0∞) / Fintype.card W := by
        rw [← Finset.mul_sum, Finset.sum_boole, ENNReal.div_eq_inv_mul]
        simp

/-- **PRG ⟹ OWF** (BS Thm 8.1). For every inverter `A_owf`,

    `OWF_Advantage (owf_of_prg G.stretch) A_owf ≤
      PRG_Advantage G (prg_distinguisher_of_owf_inverter G A_owf) + |im G| / |W|`.

    The OWF game is the real PRG game of the distinguisher (`owf_game_eq_prg_real`);
    in the ideal game the distinguisher outputs `true` with probability at most
    `|im G| / |W|` (`prTrue_prg_ideal_distinguisher_le`). -/
theorem owf_le_prg (G : PRGDef W W) (A_owf : OWF_Adversary W) :
    OWF_Advantage (owf_of_prg G.stretch) A_owf ≤
      PRG_Advantage G (prg_distinguisher_of_owf_inverter G A_owf) +
        ((Finset.univ.image G.stretch).card : ℝ≥0∞) / Fintype.card W := by
  set D := prg_distinguisher_of_owf_inverter G A_owf
  have hreal : OWF_Advantage (owf_of_prg G.stretch) A_owf =
      prTrue ((prg_real G).bind D) Heap.empty := by
    unfold OWF_Advantage; rw [owf_game_eq_prg_real]
  rw [hreal]
  calc prTrue ((prg_real G).bind D) Heap.empty
      ≤ (prTrue ((prg_real G).bind D) Heap.empty -
          prTrue ((prg_ideal (Output := W)).bind D) Heap.empty) +
        prTrue ((prg_ideal (Output := W)).bind D) Heap.empty := le_tsub_add
    _ ≤ PRG_Advantage G D +
          ((Finset.univ.image G.stretch).card : ℝ≥0∞) / Fintype.card W :=
        add_le_add (le_max_left _ _) (prTrue_prg_ideal_distinguisher_le G A_owf)

/-! ## RSA as OWP

The RSA function (modular exponentiation `x ↦ x^e mod N` for suitable `(N, e)`)
is conjectured to be a one-way permutation. The formal connection is via
`RSADef` in `Assumptions/RSA.lean`. An `OWPDef` instance for RSA would require
proving `Function.Bijective` for the RSA map, which needs number-theoretic
facts about the RSA group structure. -/

end CatCrypt.Crypto.Assumptions

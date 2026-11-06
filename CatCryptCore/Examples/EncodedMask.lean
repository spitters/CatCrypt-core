/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SamplerCert
public import Mathlib.Data.ZMod.Basic

/-!
# An encoded game over a certified sampler

A worked instance of the encoded-assumption interface. The game `maskGame n` over the sampler
on `ZMod n` shows `(a, a + b)` (real) or `(a, b)` (ideal) for independent draws `a`, `b`. The
encoded games `encReal μ`, `encIdeal μ` draw from a sampler `μ` and show the pair encoded as
residues `{m : ℕ // m < n}` by `ZMod.val`. They are realized by `maskGame n` at `μ` under the
encoding `encPair`, so for any certificate `c` the advantage of a distinguisher of residues
between `encReal c.μ` and `encIdeal c.μ` is the advantage of `encodedRed encPair A` against
`maskGame n` at `c.ν`, plus `4 * c.δ`.

## Main results

* `maskGame_realizes` — `Realizes (encReal μ) (encIdeal μ) (maskGame n) μ encPair`
* `encMask_advantage_le` — `AdvantageA (encReal c.μ) (encIdeal c.μ) A ≤
  (maskGame n).advAt c.ν (encodedRed encPair A) + 4 * c.δ`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Examples.EncodedMask

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Crypto
open scoped ENNReal

variable (n : ℕ) [NeZero n]

/-- Residues modulo `n` as natural numbers below `n`. -/
abbrev Residue : Type := {m : ℕ // m < n}

variable {n}

/-- The encoding of an element of `ZMod n` as its residue. -/
def encZ (x : ZMod n) : Residue n := ⟨x.val, ZMod.val_lt x⟩

/-- The encoding of a pair, componentwise. -/
def encPair (p : ZMod n × ZMod n) : Residue n × Residue n := (encZ p.1, encZ p.2)

variable (n)

/-- The masking game over a sampler on `ZMod n`: `(a, a + b)` against `(a, b)`. -/
noncomputable def maskGame : SampledGame (ZMod n) (ZMod n × ZMod n) where
  nR := 2
  nI := 2
  real xs := SPComp.pure (xs 0, xs 0 + xs 1)
  ideal xs := SPComp.pure (xs 0, xs 1)

variable {n}

/-- The encoded real game at the sampler `μ`. -/
noncomputable def encReal (μ : SDistr (ZMod n)) : SPComp (Residue n × Residue n) :=
  (sampleFrom μ).bind fun a => (sampleFrom μ).bind fun b =>
    SPComp.pure (encZ a, encZ (a + b))

/-- The encoded ideal game at the sampler `μ`. -/
noncomputable def encIdeal (μ : SDistr (ZMod n)) : SPComp (Residue n × Residue n) :=
  (sampleFrom μ).bind fun a => (sampleFrom μ).bind fun b => SPComp.pure (encZ a, encZ b)

/-- The encoded games are the image of `maskGame n` at `μ` under `encPair`. -/
theorem maskGame_realizes (μ : SDistr (ZMod n)) :
    Realizes (encReal μ) (encIdeal μ) (maskGame n) μ encPair where
  real := by
    simp only [encReal, SampledGame.realAt, maskGame, sampleFrom_replicateFin_succ_bind,
      sampleFrom_replicateFin_zero_bind, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  ideal := by
    simp only [encIdeal, SampledGame.idealAt, maskGame, sampleFrom_replicateFin_succ_bind,
      sampleFrom_replicateFin_zero_bind, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    rfl

/-- The advantage of a distinguisher of residues between the encoded games at the certified
sampler `c.μ` is at most the advantage of `encodedRed encPair A` against `maskGame n` at the
reference sampler `c.ν`, plus `c.δ` for each of the four draws. -/
theorem encMask_advantage_le (c : SamplerCert (ZMod n))
    (A : Residue n × Residue n → SPComp Bool) :
    AdvantageA (encReal c.μ) (encIdeal c.μ) A ≤
      (maskGame n).advAt c.ν (encodedRed encPair A) + 4 * c.δ := by
  have h := advantageA_le_of_realizes (maskGame n) c encPair (maskGame_realizes c.μ) A
  norm_num [maskGame] at h
  exact h

end CatCryptCore.Examples.EncodedMask

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SampledGame
public import CatCryptCore.Crypto.TVHops

/-!
# Sampler certificates and the statistical charge per draw

A `SamplerCert X` is a sampler `μ` on `X` with a certified bound `δ` on its total variation
distance to a reference sampler `ν`. Certificates compose along a chain of samplers
(`SamplerCert.trans`, adding the bounds) and through a function on the samples
(`SamplerCert.map`, keeping the bound). A game over a sampler played at `μ` instead of `ν`
changes the advantage of any distinguisher by at most `δ` per draw, and a game pair realized
by an encoded game at `μ` is bounded by the game at `ν` against the encoding reduction plus
that charge.

## Main definitions

* `SamplerCert`, `SamplerCert.trans`, `SamplerCert.map`

## Main results

* `SampledGame.advAt_le_tvDist` — `G.advAt μ A ≤ G.advAt ν A + (G.nR + G.nI) * tvDist μ ν`
* `SampledGame.advAt_le` — `G.advAt c.μ A ≤ G.advAt c.ν A + (G.nR + G.nI) * c.δ`
* `advantageA_le_of_realizes` — for `P`, `Q` realized by `G` at `c.μ` under `enc`,
  `AdvantageA P Q A ≤ G.advAt c.ν (encodedRed enc A) + (G.nR + G.nI) * c.δ`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform
open scoped ENNReal

/-- A sampler with a certified statistical distance to a reference sampler. -/
structure SamplerCert (X : Type) where
  /-- The sampler. -/
  μ : SDistr X
  /-- The reference sampler. -/
  ν : SDistr X
  /-- The certified bound. -/
  δ : ℝ≥0∞
  /-- The sampler does not fail. -/
  mass_μ : SDistr.mass μ = 1
  /-- The reference sampler does not fail. -/
  mass_ν : SDistr.mass ν = 1
  /-- The total variation distance is at most `δ`. -/
  tv_le : tvDist μ ν ≤ δ

namespace SamplerCert

variable {X Y : Type}

/-- Two certificates along a chain `c₁.μ`, `c₁.ν = c₂.μ`, `c₂.ν`: the sum of the bounds. -/
noncomputable def trans (c₁ c₂ : SamplerCert X) (h : c₁.ν = c₂.μ) : SamplerCert X where
  μ := c₁.μ
  ν := c₂.ν
  δ := c₁.δ + c₂.δ
  mass_μ := c₁.mass_μ
  mass_ν := c₂.mass_ν
  tv_le := (tvDist_triangle c₁.μ c₁.ν c₂.ν).trans
    (add_le_add c₁.tv_le (h ▸ c₂.tv_le))

/-- The image of a certificate under a function on the samples, with the same bound. -/
noncomputable def map (f : X → Y) (c : SamplerCert X) : SamplerCert Y where
  μ := c.μ.bind fun x => SDistr.pure (f x)
  ν := c.ν.bind fun x => SDistr.pure (f x)
  δ := c.δ
  mass_μ := mass_bind_of_mass_one c.mass_μ fun _ => SDistr.mass_pure _
  mass_ν := mass_bind_of_mass_one c.mass_ν fun _ => SDistr.mass_pure _
  tv_le := (tvDist_bind_le _ _ _).trans c.tv_le

end SamplerCert

namespace SampledGame

variable {X V : Type}

/-- Playing a game over a sampler at `μ` instead of `ν` costs `tvDist μ ν` per draw. -/
theorem advAt_le_tvDist (G : SampledGame X V) (μ ν : SDistr X) (A : V → SPComp Bool) :
    G.advAt μ A ≤ G.advAt ν A + (G.nR + G.nI) * tvDist μ ν := by
  have hR := advantageA_sampleFrom_le G.real (G.idealAt μ) A
    (replicateFin G.nR μ) (replicateFin G.nR ν)
  have hI := advantageA_sampleFrom_le G.ideal (G.realAt ν) A
    (replicateFin G.nI μ) (replicateFin G.nI ν)
  have hR' := tvDist_replicateFin_le G.nR μ ν
  have hI' := tvDist_replicateFin_le G.nI μ ν
  rw [AdvantageA_sym ((sampleFrom (replicateFin G.nI ν)).bind G.ideal)] at hI
  calc G.advAt μ A
      ≤ AdvantageA (G.realAt ν) (G.idealAt μ) A + tvDist (replicateFin G.nR μ)
          (replicateFin G.nR ν) := hR
    _ ≤ (G.advAt ν A + tvDist (replicateFin G.nI μ) (replicateFin G.nI ν)) +
          tvDist (replicateFin G.nR μ) (replicateFin G.nR ν) := by
        rw [AdvantageA_sym]; exact add_le_add_left hI _
    _ ≤ (G.advAt ν A + G.nI * tvDist μ ν) + G.nR * tvDist μ ν := by gcongr
    _ = G.advAt ν A + (G.nR + G.nI) * tvDist μ ν := by ring

/-- Playing a game over a sampler at the certified sampler `c.μ` instead of the reference
`c.ν` costs `c.δ` per draw. -/
theorem advAt_le (G : SampledGame X V) (c : SamplerCert X) (A : V → SPComp Bool) :
    G.advAt c.μ A ≤ G.advAt c.ν A + (G.nR + G.nI) * c.δ :=
  (G.advAt_le_tvDist c.μ c.ν A).trans (by gcongr; exact c.tv_le)

end SampledGame

/-- A game pair realized by the encoded game `G` at the certified sampler `c.μ`: its
advantage is at most the advantage of the encoding reduction against `G` at the reference
sampler, plus `c.δ` per draw. -/
theorem advantageA_le_of_realizes {X V W : Type} {P Q : SPComp W} (G : SampledGame X V)
    (c : SamplerCert X) (enc : V → W) (h : Realizes P Q G c.μ enc) (A : W → SPComp Bool) :
    AdvantageA P Q A ≤ G.advAt c.ν (encodedRed enc A) + (G.nR + G.nI) * c.δ := by
  rw [h.advantageA_eq]
  exact G.advAt_le c _

end CatCrypt.Crypto

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SampledGame
public import CatCryptCore.Examples.CyclicGroupDDH

/-!
# The DDH games over a cyclic group as a game over an exponent sampler

The real DDH game draws two exponents `a, b` and shows `(g^a, g^b, g^(a·b))`; the ideal game
draws three exponents `a, b, c` and shows `(g^a, g^b, g^c)`. As a `SampledGame` over the
exponents, its advantage at the uniform sampler is `DDH_Advantage`, and at any other sampler
`μ` it is the DDH advantage with exponents drawn from `μ`.

## Main definitions

* `ddhSampled G : SampledGame CG.Exp (DDHTriple G)` with `nR = 2`, `nI = 3`

## Main results

* `ddhSampled_realAt_uniform`, `ddhSampled_idealAt_uniform` — at the uniform sampler the games
  are `DDH_real G` and `DDH_ideal G`
* `DDH_Advantage_eq_advAt` — `DDH_Advantage G A = (ddhSampled G).advAt (SDistr.uniform _) A`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform
open CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

variable (G : Type) [CG : CyclicGroup G]

/-- The DDH games as a game over two (real) or three (ideal) exponent draws. -/
noncomputable def ddhSampled : SampledGame CG.Exp (DDHTriple G) where
  nR := 2
  nI := 3
  real xs := SPComp.pure (CG.pow (xs 0), CG.pow (xs 1), CG.pow (CG.expMul (xs 0) (xs 1)))
  ideal xs := SPComp.pure (CG.pow (xs 0), CG.pow (xs 1), CG.pow (xs 2))

/-- At the uniform sampler the real game of `ddhSampled G` is `DDH_real G`. -/
theorem ddhSampled_realAt_uniform :
    (ddhSampled G).realAt (SDistr.uniform CG.Exp) = DDH_real G := by
  simp only [SampledGame.realAt, ddhSampled, sampleFrom_replicateFin_succ_bind,
    sampleFrom_replicateFin_zero_bind, sampleFrom_uniform]
  rfl

/-- At the uniform sampler the ideal game of `ddhSampled G` is `DDH_ideal G`. -/
theorem ddhSampled_idealAt_uniform :
    (ddhSampled G).idealAt (SDistr.uniform CG.Exp) = DDH_ideal G := by
  simp only [SampledGame.idealAt, ddhSampled, sampleFrom_replicateFin_succ_bind,
    sampleFrom_replicateFin_zero_bind, sampleFrom_uniform]
  rfl

/-- The DDH advantage is the advantage of `ddhSampled G` at the uniform exponent sampler. -/
theorem DDH_Advantage_eq_advAt (A : DDHTriple G → SPComp Bool) :
    DDH_Advantage G A = (ddhSampled G).advAt (SDistr.uniform CG.Exp) A := by
  rw [SampledGame.advAt, ddhSampled_realAt_uniform, ddhSampled_idealAt_uniform]
  rfl

end CatCrypt.Crypto

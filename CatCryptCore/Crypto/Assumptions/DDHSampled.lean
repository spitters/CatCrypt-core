/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SampledGame
public import CatCryptCore.Examples.CyclicGroupDDH
public import CatCryptCore.Crypto.Assumptions.DDH

/-!
# The DDH games over a cyclic group as a game over an exponent sampler, and DDH with the ideal
value drawn by key generation

The real DDH game draws two exponents `a, b` and shows `(g^a, g^b, g^(a·b))`; the ideal game
draws three exponents `a, b, c` and shows `(g^a, g^b, g^c)`. As a `SampledGame` over the
exponents, its advantage at the uniform sampler is `DDH_Advantage`, and at any other sampler
`μ` it is the DDH advantage with exponents drawn from `μ`.

For a Diffie-Hellman definition `D : DDHDef W`, the ideal game `DDH_Game_IdealK` shows as its
third value the public part of a fresh key pair instead of a uniform element of `W`. When the
public part of a key pair is uniform on `W`, it is the ideal game `DDH_Game_Ideal`. The views of
the real game and of this ideal game are `DDH_ViewReal D` and `DDH_ViewIdealK D`.

## Main definitions

* `ddhSampled G : SampledGame CG.Exp (DDHTriple G)` with `nR = 2`, `nI = 3`
* `Assumptions.DDH_ViewReal`, `Assumptions.DDH_ViewIdealK` — the views of the DDH games over
  `DDHDef`, the ideal value drawn by key generation
* `Assumptions.DDH_Game_IdealK`, `Assumptions.DDH_AdvantageK`

## Main results

* `ddhSampled_realAt_uniform`, `ddhSampled_idealAt_uniform` — at the uniform sampler the games
  are `DDH_real G` and `DDH_ideal G`
* `DDH_Advantage_eq_advAt` — `DDH_Advantage G A = (ddhSampled G).advAt (SDistr.uniform _) A`
* `Assumptions.DDH_Game_IdealK_eq_Ideal` — under `D.keygen.map Prod.snd = SPComp.sample W`,
  `DDH_Game_IdealK D A = DDH_Game_Ideal D A`
* `Assumptions.DDH_AdvantageK_eq_advantageA` — `DDH_AdvantageK D A` is the advantage of the
  uncurried `A` between the two views
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

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-- The view of the real DDH game: the public parts of two key pairs and their shared value. -/
noncomputable def DDH_ViewReal (D : DDHDef W) : SPComp (W × W × W) :=
  D.keygen.bind fun ka => D.keygen.bind fun kb => SPComp.pure (ka.2, kb.2, D.ecdh ka.1 kb.2)

/-- The view of the ideal DDH game whose third value is the public part of a fresh key pair. -/
noncomputable def DDH_ViewIdealK (D : DDHDef W) : SPComp (W × W × W) :=
  D.keygen.bind fun ka => D.keygen.bind fun kb => D.keygen.bind fun kc =>
    SPComp.pure (ka.2, kb.2, kc.2)

/-- The DDH ideal game whose third value is the public part of a fresh key pair. -/
noncomputable def DDH_Game_IdealK (D : DDHDef W) (A : DDH_Adversary W) : SPComp Bool :=
  (DDH_ViewIdealK D).bind fun t => A t.1 t.2.1 t.2.2

/-- The DDH advantage against the ideal game with the third value drawn by key generation. -/
noncomputable def DDH_AdvantageK (D : DDHDef W) (A : DDH_Adversary W) : ℝ≥0∞ :=
  Advantage (DDH_Game_Real D A) (DDH_Game_IdealK D A)

/-- The real DDH game is the adversary run on the real view. -/
theorem DDH_Game_Real_eq_bind (D : DDHDef W) (A : DDH_Adversary W) :
    DDH_Game_Real D A = (DDH_ViewReal D).bind fun t => A t.1 t.2.1 t.2.2 := by
  simp only [DDH_ViewReal, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

/-- `DDH_AdvantageK D A` is the advantage of the uncurried `A` between the views. -/
theorem DDH_AdvantageK_eq_advantageA (D : DDHDef W) (A : DDH_Adversary W) :
    DDH_AdvantageK D A =
      AdvantageA (DDH_ViewReal D) (DDH_ViewIdealK D) fun t => A t.1 t.2.1 t.2.2 := by
  rw [DDH_AdvantageK, DDH_Game_Real_eq_bind]
  rfl

/-- When the public part of a key pair is uniform, the ideal game with the third value drawn
by key generation is the ideal DDH game. -/
theorem DDH_Game_IdealK_eq_Ideal (D : DDHDef W) (h : D.keygen.map Prod.snd = SPComp.sample W)
    (A : DDH_Adversary W) : DDH_Game_IdealK D A = DDH_Game_Ideal D A := by
  have hk : ∀ k : W → SPComp Bool, (D.keygen.bind fun kc => k kc.2) = (SPComp.sample W).bind k :=
    fun k => by rw [← h, SPComp.map, SPComp.bind_assoc]; simp only [SPComp.pure_bind]
  simp only [DDH_Game_IdealK, DDH_ViewIdealK, SPComp.bind_assoc, SPComp.pure_bind, hk]
  rfl

/-- Under the same hypothesis, `DDH_AdvantageK D A = DDH_Advantage D A`. -/
theorem DDH_AdvantageK_eq (D : DDHDef W) (h : D.keygen.map Prod.snd = SPComp.sample W)
    (A : DDH_Adversary W) : DDH_AdvantageK D A = DDH_Advantage D A := by
  rw [DDH_AdvantageK, DDH_Game_IdealK_eq_Ideal D h, DDH_Advantage]

end CatCrypt.Crypto.Assumptions

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.RRelWRPUC
public import CatCryptCoreTest.Refinement.RRelWRPProbBiasedCoin

/-!
# Tests of the game hop from refinement: the biased coin

The biased coin refines the constant `true` up to `1/4`. Instance search gives the game bound and
the game hop `UCFromGameC`, and a 2-cell `ProtMorε` whose simulator samples.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Refinement.WRP

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto RefinementWP
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCDSL CatCrypt.Crypto.UCComposition
open scoped ENNReal

/-- The biased coin refines the constant `true` up to `1/4`, as a family over one input. -/
instance instRefinesFamilyUpToBiasedCoin :
    RefinesFamilyUpTo (fun _ : Unit => biasedCoin) (fun _ => SPComp.pure true) 4⁻¹ :=
  .of_rHoareApprox fun _ => rHoareApprox_biasedCoin

/-- The biased coin does not depend on the heap. -/
instance instPureGameBiasedCoin : PureGame fun _ : Unit => biasedCoin :=
  ⟨fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _⟩

/-- The constant `true` does not depend on the heap. -/
instance instPureGamePureTrue : PureGame fun _ : Unit => SPComp.pure true :=
  ⟨fun _ => SPComp.pure_isPure _⟩

-- The game hop from the biased coin to the constant `true`, by instance search.
example (V : Type) :
    UCEmulatesCSim (UCSpec.ofGame Unit Bool V) (UCProtocol.ofGame fun _ => biasedCoin)
      (UCProtocol.ofGame fun _ => SPComp.pure true) id (gameUCBound fun _ _ => 4⁻¹) :=
  UCFromGameC.uc

-- The error of that statement lies strictly between `0` and `1`.
example : (0 : ℝ≥0∞) < 4⁻¹ ∧ (4⁻¹ : ℝ≥0∞) < 1 :=
  ⟨by simp, by simp⟩

-- A 2-cell whose simulator samples: the ideal interface carries no data, the real one `true`.
noncomputable example :
    UCMonad.ProtMorε (T := SPComp) (hon := Unit) (out := Unit)
      ⟨Unit, fun _ => SPComp.pure (.inr ())⟩ ⟨Bool, fun _ => SPComp.pure (.inr true)⟩ 4⁻¹ :=
  haveI : RefinesFamilyUpTo (fun _ : Unit => SPComp.pure (Sum.inr true : Unit ⊕ Bool))
      (fun _ => SPComp.pure (Sum.inr () : Unit ⊕ Unit) >>=
        UCMonad.UCMonadBase.ucMapSum pure fun _ => biasedCoin) 4⁻¹ :=
    .of_rHoareApprox fun _ => rHoareApprox_of_forall_absDiff fun D s => by
      have hcoin :=
        rHoareApprox_absDiff_prTrue rHoareApprox_biasedCoin (fun b => D (.inr b)) s
      simpa [UCMonad.UCMonadBase.ucMapSum, UCMonad.mapSumSP, SPComp.map, SPComp.bind_assoc,
        absDiff_comm] using hcoin
  UCMonad.ProtMorε.ofRefines fun _ => biasedCoin

end CatCrypt.Refinement.WRP

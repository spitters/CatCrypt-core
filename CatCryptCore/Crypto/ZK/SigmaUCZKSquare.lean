/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ZK.SigmaUCZK
public import CatCryptCore.Category.ProtBicatReactive

/-!
# Honest-verifier Σ-protocol zero-knowledge as a one-shot square

The ideal functionality `sigma_ideal` takes the prover's input `(x, w)`; when `R(x, w)` holds it
hands the statement `x` to the simulator interface, otherwise it aborts with the honest output.
The real protocol `sigma_real` runs the Σ-protocol with a uniformly sampled challenge and leaks
the transcript `(a, e, z)`. The simulator `sigma_uc_sim` receives `x`, samples a challenge `e`,
runs the SHVZK simulator `simulate x e` and outputs the transcript; it never uses the witness.

This file states the zero-knowledge result of `SigmaUCZK` with this simulator as an explicit
simulator map (`UCEmulatesCSim`), and as a realization of the one-activation ideal system
behind the bundled simulator `simWrapSim` (a square). Both statements cover one activation, an
honest verifier (the challenge is sampled by the protocol) and the zero-knowledge direction
(corrupt verifier); they say nothing about knowledge soundness.

## Main results

* `sigma_uc_zk_secure_csim` — `sigma_real` emulates `sigma_ideal` with the straight-line
  simulator map of `sigma_uc_sim`, at distance `0`.
* `sigma_uc_zk_square` — `Sys.oneShot (sigma_real sp)` realizes `Sys.oneShot (sigma_ideal sp)`
  behind `simWrapSim ev (sigma_uc_sim sp _ SPComp.pure)`, at distance `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ZK.SigmaUCZK

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable (sp : CatCrypt.Examples.Sigma.SigmaProtocol)

/-- `sigma_uc_sim` is the straight-line simulator of its output at the dummy adversary. -/
theorem sigma_uc_sim_eq_simOf (V : Type) (A : Transcript sp → SPComp V) :
    sigma_uc_sim sp V A = simOf (sigma_uc_sim sp _ SPComp.pure) A := by
  funext x
  simp only [sigma_uc_sim, simOf, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- The simulator `sigma_uc_sim` at the dummy adversary never fails when `simulate` never
fails. -/
theorem sigma_uc_sim_pure_noFail (hsim : ∀ x e, SPComp.NoFail (sp.simulate x e))
    (x : sp.Statement) : SPComp.NoFail (sigma_uc_sim sp _ SPComp.pure x) := by
  simp only [sigma_uc_sim, SPComp.monad_bind_eq]
  exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail fun e =>
    Assumptions.SPComp.bind_noFail (hsim x e) fun _ => SPComp.pure_noFail _

/-- **Honest-verifier Σ zero-knowledge with an explicit simulator map, at distance `0`.**
Ideal functionality `sigma_ideal`: it hands the statement to the simulator when the relation
holds. Real protocol `sigma_real`: the Σ-protocol with a sampled challenge, leaking the
transcript. Simulator: `simOf` of `sigma_uc_sim` at the dummy adversary, which samples a
challenge and runs `simulate`, without the witness. One activation, honest verifier,
zero-knowledge direction only. (genuine UC) -/
theorem sigma_uc_zk_secure_csim (hshvzk : SHVZK sp) (V : Type) :
    UCEmulatesCSim ⟨sp.Statement × sp.Witness, Unit, Transcript sp, sp.Statement, V⟩
      (sigma_real sp) (sigma_ideal sp) (simOf (sigma_uc_sim sp _ SPComp.pure))
      (fun _ _ => 0) := by
  rintro A ⟨⟨x, w⟩, h, D⟩
  simp only [Env.gap, ← sigma_uc_sim_eq_simOf, sigma_view_eq sp hshvzk x w V A, absDiff_self,
    le_refl]

/-- **Honest-verifier Σ zero-knowledge as a one-shot square, at distance `0`.**
The one-activation system of the real protocol `sigma_real` realizes the one-activation ideal
functionality `sigma_ideal` behind the bundled simulator `simWrapSim ev` of `sigma_uc_sim` at the
dummy adversary, which turns the statement into a simulated transcript without the witness. One
activation, honest verifier, zero-knowledge direction only. (genuine UC) -/
theorem sigma_uc_zk_square (hshvzk : SHVZK sp)
    (hsim : ∀ x e, SPComp.NoFail (sp.simulate x e))
    (ev : sp.Statement × sp.Witness → sp.Statement × sp.Witness → Prop) :
    RealizesSim (Sys.oneShot (sigma_real sp)) (Sys.oneShot (sigma_ideal sp))
      (simWrapSim ev (sigma_uc_sim sp _ SPComp.pure) (sigma_uc_sim_pure_noFail sp hsim))
      (fun _ _ => 0) := by
  have h := Realizes.trans
    (realizes_oneShot_of_ucEmulatesCSim (sigma_uc_zk_secure_csim sp hshvzk _))
    (realizes_oneShot_simWrap (sigma_ideal sp) _ (sigma_uc_sim_pure_noFail sp hsim))
  exact fun ζ => (h ζ).mono fun Z => by simp [oneShotBound]

end CatCrypt.Crypto.ZK.SigmaUCZK

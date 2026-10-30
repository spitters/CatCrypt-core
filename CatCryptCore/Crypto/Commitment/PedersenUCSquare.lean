/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Commitment.PedersenUC
public import CatCryptCore.Category.ProtBicatReactive

/-!
# The Pedersen commit phase as a one-shot square

The ideal functionality `pedersen_commit_ideal` takes the committer's message `m` and tells the
simulator interface only that a commitment was made. The real protocol `pedersen_commit_real`
samples randomness `r` and leaks the commitment exponent `m + t · r`. The simulator
`pedersen_commit_sim` hands the adversary a uniform exponent; it does not receive `m`.

This file states the commit-phase result of `PedersenUC` with this simulator as an explicit
simulator map (`UCEmulatesCSim`), and as a realization of the one-activation ideal system
behind the bundled simulator `simWrapSim` (a square). Both statements cover one activation of
the commit phase, an honest committer and a corrupt receiver (hiding).

## Main results

* `pedersen_uc_commit_phase_csim` — `pedersen_commit_real` emulates `pedersen_commit_ideal`
  with the straight-line simulator map of `pedersen_commit_sim`, at distance `0`.
* `pedersen_commit_phase_square` — `Sys.oneShot (pedersen_commit_real gp crs)` realizes
  `Sys.oneShot (pedersen_commit_ideal gp crs)` behind `simWrapSim ev` of
  `pedersen_commit_sim`, at distance `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Commitment.PedersenUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open CatCrypt.Examples
open scoped ENNReal

variable (gp : GroupParam)

/-- `pedersen_commit_sim` is the straight-line simulator of its output at the dummy
adversary. -/
theorem pedersen_commit_sim_eq_simOf (V : Type) (A : gp.Scalar → SPComp V) :
    pedersen_commit_sim gp V A = simOf (pedersen_commit_sim gp _ SPComp.pure) A := by
  funext u
  simp only [pedersen_commit_sim, simOf, SPComp.bind_pure]

/-- The simulator `pedersen_commit_sim` at the dummy adversary never fails. -/
theorem pedersen_commit_sim_pure_noFail (u : Unit) :
    SPComp.NoFail (pedersen_commit_sim gp _ SPComp.pure u) := by
  simp only [pedersen_commit_sim, SPComp.bind_pure]
  exact Assumptions.SPComp.sample_noFail

/-- **The Pedersen commit phase with an explicit simulator map, at distance `0`.**
Ideal functionality `pedersen_commit_ideal`: it tells the simulator that a commitment was made.
Real protocol `pedersen_commit_real`: it leaks the commitment exponent `m + t · r` of a uniform
`r`. Simulator: `simOf` of `pedersen_commit_sim` at the dummy adversary, a uniform exponent,
without `m`. One activation of the commit phase, honest committer, corrupt receiver.
(genuine UC) -/
theorem pedersen_uc_commit_phase_csim (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero) (V : Type) :
    UCEmulatesCSim ⟨gp.Scalar, Unit, gp.Scalar, Unit, V⟩
      (pedersen_commit_real gp crs) (pedersen_commit_ideal gp crs)
      (simOf (pedersen_commit_sim gp _ SPComp.pure)) (fun _ _ => 0) := by
  rintro A ⟨m, h, D⟩
  simp only [Env.gap, ← pedersen_commit_sim_eq_simOf, pedersen_commit_view_eq gp crs ht m V A,
    absDiff_self, le_refl]

/-- **The Pedersen commit phase as a one-shot square, at distance `0`.**
The one-activation system of the real commit phase `pedersen_commit_real` realizes the
one-activation ideal functionality `pedersen_commit_ideal` behind the bundled simulator
`simWrapSim ev` of `pedersen_commit_sim` at the dummy adversary, which answers the notification
of a commitment with a uniform exponent. One activation of the commit phase, honest committer,
corrupt receiver. (genuine UC) -/
theorem pedersen_commit_phase_square (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero) (ev : gp.Scalar → gp.Scalar → Prop) :
    RealizesSim (Sys.oneShot (pedersen_commit_real gp crs))
      (Sys.oneShot (pedersen_commit_ideal gp crs))
      (simWrapSim ev (pedersen_commit_sim gp _ SPComp.pure) (pedersen_commit_sim_pure_noFail gp))
      (fun _ _ => 0) := by
  have h := Realizes.trans
    (realizes_oneShot_of_ucEmulatesCSim (pedersen_uc_commit_phase_csim gp crs ht _))
    (realizes_oneShot_simWrap (pedersen_commit_ideal gp crs) _
      (pedersen_commit_sim_pure_noFail gp))
  exact fun ζ => (h ζ).mono fun Z => by simp [oneShotBound]

end CatCrypt.Crypto.Commitment.PedersenUC

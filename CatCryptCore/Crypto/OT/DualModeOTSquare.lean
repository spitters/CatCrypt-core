/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.DualModeOT
public import CatCryptCore.Category.ProtBicatReactive

/-!
# Dual-mode oblivious transfer against a corrupt receiver as a one-shot square

The ideal functionality `dualOT_ideal` takes the sender's messages `m₀, m₁` and the receiver's
choice bit `b`; it hands the simulator interface `b` and an encryption of the chosen message
`m_b` under `pk_b`. The real protocol `dualOT_real` encrypts both messages, `m₀` under `pk₀` and
`m₁` under `pk₁`, and leaks both ciphertexts. The simulator `dualOT_sim` places the chosen
ciphertext in slot `b` and a uniform group element in the other slot.

This file states the sender-message privacy result of `DualModeOT` with this simulator as an
explicit simulator map (`UCEmulatesCSim`), and as a realization of the one-activation ideal
system behind the bundled simulator `simWrapSim` (a square). Both statements cover one
activation and a corrupt receiver; the ideal functionality reveals the choice bit, so receiver
privacy is not covered.

## Main results

* `dualOT_view_eq` — the real view and the simulated ideal view coincide pointwise when both
  public keys are non-identity.
* `dualOT_uc_secure_zero_csim` — `dualOT_real` emulates `dualOT_ideal` with the straight-line
  simulator map of `dualOT_sim`, at distance `0`.
* `dualOT_square` — `Sys.oneShot (dualOT_real gp crs)` realizes `Sys.oneShot (dualOT_ideal gp crs)`
  behind `simWrapSim ev` of `dualOT_sim`, at distance `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.DualModeOT

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open CatCrypt.Examples
open scoped ENNReal

variable (gp : GroupParam)

/-- `dualOT_sim` is the straight-line simulator of its output at the dummy adversary. -/
theorem dualOT_sim_eq_simOf (crs : DualModeCRS gp) (V : Type) (A : gp.G × gp.G → SPComp V) :
    dualOT_sim gp crs V A = simOf (dualOT_sim gp crs _ SPComp.pure) A := by
  funext ⟨b, ct⟩
  cases b <;> simp [dualOT_sim, simOf, SPComp.bind_assoc, SPComp.pure_bind]

/-- The simulator `dualOT_sim` at the dummy adversary never fails. -/
theorem dualOT_sim_pure_noFail (crs : DualModeCRS gp) (x : Bool × gp.G) :
    SPComp.NoFail (dualOT_sim gp crs _ SPComp.pure x) := by
  obtain ⟨b, ct⟩ := x
  unfold dualOT_sim
  exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail fun _ => by
    cases b <;> exact SPComp.pure_noFail _

/-- Encryption under a non-identity key with uniform randomness, followed by `K`, is a uniform
group element followed by `K` (`dualEnc_uniform`). -/
theorem bind_sample_dualEnc {β : Type} (pk m : gp.G) (h : pk ≠ gp.identity)
    (K : gp.G → SPComp β) :
    SPComp.bind (SPComp.sample gp.Scalar) (fun r => K (dualEnc gp pk m r)) =
      SPComp.bind (SPComp.sample gp.G) K := by
  rw [← dualEnc_uniform gp pk m h]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]

/-- When both public keys are non-identity, the real view of the adversary `A` and the ideal
view with the simulator `dualOT_sim` coincide pointwise. -/
theorem dualOT_view_eq (crs : DualModeCRS gp)
    (h0 : crs.pk₀ ≠ gp.identity) (h1 : crs.pk₁ ≠ gp.identity) (V : Type)
    (A : gp.G × gp.G → SPComp V) (a : OTInput gp) :
    SPComp.bind (dualOT_real gp crs a) (mapSum SPComp.pure A) =
      SPComp.bind (dualOT_ideal gp crs a) (mapSum SPComp.pure (dualOT_sim gp crs V A)) := by
  simp only [dualOT_real, dualOT_ideal, dualOT_sim, SPComp.bind_assoc, SPComp.pure_bind,
    mapSum_inr, SPComp.map]
  cases a.choice
  · simp only [Bool.false_eq_true, ite_false]
    refine congrArg _ (funext fun r => ?_)
    exact bind_sample_dualEnc gp crs.pk₁ a.m₁ h1 fun ct =>
      SPComp.bind (A (dualEnc gp crs.pk₀ a.m₀ r, ct)) fun v => SPComp.pure (Sum.inr v : Unit ⊕ V)
  · simp only [ite_true]
    rw [SPComp.isPure_bind_comm (SPComp.sample gp.Scalar) (SPComp.sample gp.Scalar) _
      (SPComp.sample_isPure _) (SPComp.sample_isPure _)]
    refine congrArg _ (funext fun r => ?_)
    exact bind_sample_dualEnc gp crs.pk₀ a.m₀ h0 fun ct =>
      SPComp.bind (A (ct, dualEnc gp crs.pk₁ a.m₁ r)) fun v => SPComp.pure (Sum.inr v : Unit ⊕ V)

/-- **Dual-mode OT against a corrupt receiver with an explicit simulator map, at distance `0`.**
Ideal functionality `dualOT_ideal`: it hands the simulator the choice bit and an encryption of
the chosen message. Real protocol `dualOT_real`: it leaks encryptions of both messages.
Simulator: `simOf` of `dualOT_sim` at the dummy adversary, the chosen ciphertext beside a
uniform group element. Both public keys are non-identity. One activation, corrupt receiver.
(genuine UC) -/
theorem dualOT_uc_secure_zero_csim (crs : DualModeCRS gp)
    (h0 : crs.pk₀ ≠ gp.identity) (h1 : crs.pk₁ ≠ gp.identity) (V : Type) :
    UCEmulatesCSim ⟨OTInput gp, Unit, gp.G × gp.G, Bool × gp.G, V⟩
      (dualOT_real gp crs) (dualOT_ideal gp crs)
      (simOf (dualOT_sim gp crs _ SPComp.pure)) (fun _ _ => 0) := by
  rintro A ⟨a, h, D⟩
  simp only [Env.gap, ← dualOT_sim_eq_simOf, dualOT_view_eq gp crs h0 h1 V A a, absDiff_self,
    le_refl]

/-- **Dual-mode OT against a corrupt receiver as a one-shot square, at distance `0`.**
The one-activation system of the real protocol `dualOT_real` realizes the one-activation ideal
functionality `dualOT_ideal` behind the bundled simulator `simWrapSim ev` of `dualOT_sim` at the
dummy adversary, which completes the chosen ciphertext with a uniform group element in the
other slot. Both public keys are non-identity. One activation, corrupt receiver.
(genuine UC) -/
theorem dualOT_square (crs : DualModeCRS gp)
    (h0 : crs.pk₀ ≠ gp.identity) (h1 : crs.pk₁ ≠ gp.identity)
    (ev : OTInput gp → OTInput gp → Prop) :
    RealizesSim (Sys.oneShot (dualOT_real gp crs)) (Sys.oneShot (dualOT_ideal gp crs))
      (simWrapSim ev (dualOT_sim gp crs _ SPComp.pure) (dualOT_sim_pure_noFail gp crs))
      (fun _ _ => 0) := by
  have h := Realizes.trans
    (realizes_oneShot_of_ucEmulatesCSim (dualOT_uc_secure_zero_csim gp crs h0 h1 _))
    (realizes_oneShot_simWrap (dualOT_ideal gp crs) _ (dualOT_sim_pure_noFail gp crs))
  exact fun ζ => (h ζ).mono fun Z => by simp [oneShotBound]

end CatCrypt.Crypto.OT.DualModeOT

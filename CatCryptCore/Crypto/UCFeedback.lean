/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCInterleave

/-!
# Bounded feedback of reactive systems

The loopback of a system `S` on the interface `(E ⊕ X, O ⊕ X)` along the wire `X` is a system
on `(E, O)`: an outer event `e` activates `S` on `inl e`; an output `inr x` of `S` is fed back
to `S` as the event `inr x`; the first output `inl o` ends the activation with the outer output
`o`. The feedback hybrid `MultiHybrid.fbHybrid n cut` is this interaction as a multi-call
hybrid with fuel `n`: an activation makes at most `n + 1` calls, and a wire value `x` answered
to the last allowed call is ended with the output `cut x`. The loopback is the feedback hybrid
running with `S` (`Sys.loopback`), so the environment reduction of multi-call hybrids applies
to it (`Open.feedback`): its reduced environment runs `Z.rounds * (n + 1)` rounds of `S`.

## Main definitions

* `MultiHybrid.fbHybrid n cut`: the feedback hybrid with fuel `n` and cut-off map `cut`.
* `Sys.loopback S n cut`: the loopback of `S` along its wire.
* `Open.feedback n cut idle`: the feedback hybrid as an open system.
* `Simulator.loopback S n cut`: the feedback hybrid running with the simulator `S`.

## Main results

* `Realizes.loopback`: if `R` realizes `I` with bound `b`, both idle at `idle`, then the
  loopback of `R` realizes the loopback of `I` with bound `b` at the reduced environment.
* `MultiHybrid.fbHybrid_opaque`: the feedback hybrid is opaque from `V.sum VX` to `V` when
  the wire view `VX` relates as events the wire values it relates as outputs and `cut` maps
  related wire values to related outputs.
* `Sys.Opaque.loopback`: under the same conditions, the loopback of a system opaque for
  `V.sum VX` is opaque for `V`.
* `RealizesSim.loopback`: if `R` realizes `I` behind the simulator `S`, then the loopback of
  `R` realizes `I` behind `Simulator.loopback S`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

namespace MultiHybrid

variable {E O X : Type}

/-- The feedback hybrid with fuel `n`: an outer event `e` is passed to the subroutine as
`inl e`; an answer `inl o` ends the activation with the output `o`, and an answer `inr x` is
passed back to the subroutine as `inr x`. A wire value `x` answered to the last allowed call
ends the activation with the output `cut x`. -/
noncomputable def fbHybrid (n : ℕ) (cut : X → O) : MultiHybrid Unit E O (E ⊕ X) (O ⊕ X) where
  init := ()
  fuel := n
  start _ e := SPComp.pure ((), .inl (.inl e))
  resume _ r := match r with
    | .inl o => SPComp.pure ((), .inr o)
    | .inr x => SPComp.pure ((), .inl (.inr x))
  finish _ r := match r with
    | .inl o => SPComp.pure ((), o)
    | .inr x => SPComp.pure ((), cut x)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ r := by cases r <;> exact SPComp.pure_noFail _
  finish_noFail _ r := by cases r <;> exact SPComp.pure_noFail _

/-- **Opacity of the feedback hybrid**: it is opaque from `V.sum VX` to `V` when every two
wire values related by `VX.out` are related by `VX.ev` and `cut` maps them to outputs related
by `V.out`. -/
theorem fbHybrid_opaque (n : ℕ) (cut : X → O) (V : PubView E O) (VX : PubView X X)
    (hstable : ∀ x x', VX.out x x' → VX.ev x x')
    (hcut : ∀ x x', VX.out x x' → V.out (cut x) (cut x')) :
    (fbHybrid n cut).Opaque V (V.sum VX) := by
  refine ⟨fun _ _ => True, trivial, ?_, ?_, ?_⟩
  · intro s s' e e' _ he
    exact rHoare_ret fun _ _ h => ⟨h, trivial, Sum.LiftRel.inl he⟩
  · rintro s s' (o | x) (o' | x') _ ho
    · exact rHoare_ret fun _ _ h => ⟨h, trivial, (Sum.liftRel_inl_inl.mp ho : V.out o o')⟩
    · exact absurd ho Sum.not_liftRel_inl_inr
    · exact absurd ho Sum.not_liftRel_inr_inl
    · exact rHoare_ret fun _ _ h =>
        ⟨h, trivial, Sum.LiftRel.inr (hstable x x' (Sum.liftRel_inr_inr.mp ho))⟩
  · rintro s s' (o | x) (o' | x') _ ho
    · exact rHoare_ret fun _ _ h => ⟨h, trivial, Sum.liftRel_inl_inl.mp ho⟩
    · exact absurd ho Sum.not_liftRel_inl_inr
    · exact absurd ho Sum.not_liftRel_inr_inl
    · exact rHoare_ret fun _ _ h => ⟨h, trivial, hcut x x' (Sum.liftRel_inr_inr.mp ho)⟩

end MultiHybrid

namespace Sys

variable {τ υ E O X : Type}

/-- The loopback of `S` along its wire `X` with fuel `n` and cut-off map `cut`: the feedback
hybrid running with `S`. -/
noncomputable def loopback (S : Sys τ (E ⊕ X) (O ⊕ X)) (n : ℕ) (cut : X → O) :
    Sys (Unit × τ) E O :=
  (MultiHybrid.fbHybrid n cut).withSub S

/-- **Opacity under feedback**: the loopback of a system opaque for `V.sum VX` is opaque for
`V` when every two wire values related by `VX.out` are related by `VX.ev` and `cut` maps them
to outputs related by `V.out`. -/
theorem Opaque.loopback {S : Sys τ (E ⊕ X) (O ⊕ X)} {V : PubView E O} {VX : PubView X X}
    (hS : S.Opaque (V.sum VX)) (n : ℕ) (cut : X → O)
    (hstable : ∀ x x', VX.out x x' → VX.ev x x')
    (hcut : ∀ x x', VX.out x x' → V.out (cut x) (cut x')) :
    (S.loopback n cut).Opaque V :=
  (MultiHybrid.fbHybrid_opaque n cut V VX hstable hcut).withSub hS

end Sys

namespace Open

variable {E O X : Type}

/-- The feedback hybrid as an open system from `(E ⊕ X, O ⊕ X)` to `(E, O)`, with the
environment reduction at the idle event `idle`. -/
noncomputable def feedback (n : ℕ) (cut : X → O) (idle : E ⊕ X) : Open E O (E ⊕ X) (O ⊕ X) :=
  Open.ofMultiHybrid (MultiHybrid.fbHybrid n cut) idle

end Open

/-- **Realization under feedback** (composition plumbing). If `R` realizes `I` with bound `b`,
and `R` and `I` are idle at `idle`, then the loopback of `R` realizes the loopback of `I` with
bound `b` at the reduced environment of the feedback hybrid, which runs `n + 1` rounds of the
subroutine per round of the outer environment. -/
theorem Realizes.loopback {τ υ E O X : Type} {R : Sys τ (E ⊕ X) (O ⊕ X)}
    {I : Sys υ (E ⊕ X) (O ⊕ X)} {b : (ζ : Type) → Env (Strat ζ (E ⊕ X) (O ⊕ X)) ζ → ℝ≥0∞}
    (idle : E ⊕ X) (oR oI : O ⊕ X) (hR : MultiHybrid.IdleAt R idle oR)
    (hI : MultiHybrid.IdleAt I idle oI) (h : Realizes R I b) (n : ℕ) (cut : X → O) :
    Realizes (R.loopback n cut) (I.loopback n cut)
      (fun ζ Z => b (MultiHybrid.RState Unit ζ (E ⊕ X) O)
        ((MultiHybrid.fbHybrid n cut).reduceEnv idle Z)) := by
  have h' := (Open.feedback n cut idle).realizes_withSub ⟨oR, hR⟩ ⟨oI, hI⟩ h
  intro ζ Z
  refine le_of_le_of_eq (h' ζ Z) ?_
  exact congrArg (b _) (Open.reduceEnv_ofMultiHybrid _ idle Z)

namespace Simulator

variable {E O X EG OG : Type} {V : PubView E O} {VX : PubView X X} {W : PubView EG OG}

/-- The loopback of the simulator `S` along its wire `X`: the feedback hybrid running with
`S`. It is opaque from `W` to `V` when every two wire values related by `VX.out` are related
by `VX.ev` and `cut` maps them to outputs related by `V.out`. -/
noncomputable def loopback (S : Simulator (E ⊕ X) (O ⊕ X) EG OG (V.sum VX) W) (n : ℕ)
    (cut : X → O) (hstable : ∀ x x', VX.out x x' → VX.ev x x')
    (hcut : ∀ x x', VX.out x x' → V.out (cut x) (cut x')) : Simulator E O EG OG V W :=
  (Simulator.ofMultiHybrid (MultiHybrid.fbHybrid n cut)
    (MultiHybrid.fbHybrid_opaque n cut V VX hstable hcut)).comp S

/-- Unfolding lemma of `Simulator.loopback`: running with `I`, it is the loopback of the system
`S.withSub I`. -/
theorem loopback_withSub {υ : Type} (S : Simulator (E ⊕ X) (O ⊕ X) EG OG (V.sum VX) W)
    (n : ℕ) (cut : X → O) (hstable : ∀ x x', VX.out x x' → VX.ev x x')
    (hcut : ∀ x x', VX.out x x' → V.out (cut x) (cut x')) (I : Sys υ EG OG) :
    (S.loopback n cut hstable hcut).withSub I = (S.withSub I).loopback n cut :=
  rfl

end Simulator

/-- **Realization behind a simulator under feedback** (composition plumbing). If `R` realizes
`I` behind the simulator `S` with bound `b`, and `R` and `S` running with `I` are idle at
`idle`, then the loopback of `R` realizes `I` behind the loopback of `S` with bound `b` at the
reduced environment of the feedback hybrid. -/
theorem RealizesSim.loopback {τ υ E O X EG OG : Type} {V : PubView E O} {VX : PubView X X}
    {W : PubView EG OG} {R : Sys τ (E ⊕ X) (O ⊕ X)} {I : Sys υ EG OG}
    {S : Simulator (E ⊕ X) (O ⊕ X) EG OG (V.sum VX) W}
    {b : (ζ : Type) → Env (Strat ζ (E ⊕ X) (O ⊕ X)) ζ → ℝ≥0∞}
    (idle : E ⊕ X) (oR oI : O ⊕ X) (hR : MultiHybrid.IdleAt R idle oR)
    (hI : MultiHybrid.IdleAt (S.withSub I) idle oI) (h : RealizesSim R I S b) (n : ℕ)
    (cut : X → O) (hstable : ∀ x x', VX.out x x' → VX.ev x x')
    (hcut : ∀ x x', VX.out x x' → V.out (cut x) (cut x')) :
    RealizesSim (R.loopback n cut) I (S.loopback n cut hstable hcut)
      (fun ζ Z => b (MultiHybrid.RState Unit ζ (E ⊕ X) O)
        ((MultiHybrid.fbHybrid n cut).reduceEnv idle Z)) :=
  Realizes.loopback idle oR oI hR hI h n cut

end CatCrypt.Crypto.UCTransparent

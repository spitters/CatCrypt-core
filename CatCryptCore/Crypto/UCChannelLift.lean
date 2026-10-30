/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSemiHonest
public import CatCryptCore.Crypto.UCChannel

/-!
# A subroutine beside a channel

A protocol that uses a subroutine `G` and a channel `C` runs over the parallel composition of the
two, with the ports regrouped: the honest ports of `G` and `C` form the honest port, and their
adversary ports form the adversary port (`Sys.withChan`, the parallel composition `Sys.par` on
ports relabelled by `chanEv` and `chanOut`). This is the interface on which the modular UC
theorem (`RealizesSim.modular`) and the semi-honest composition theorem
(`RealizesSim.semiHonest_modular`) take a subroutine.

**Statement.** Let `ρ` (real) realize `G` (ideal) behind the simulator `(idSim EH OH).tensor S`,
which forwards the honest port and runs `S` on the adversary port. Then `ρ.withChan C` (real)
realizes `G.withChan C` (ideal) behind `(idSim (EH ⊕ EC) (OH ⊕ OC)).tensor (S.tensor (idSim ED
OD))` (simulator): forwarding on the honest ports, `S` on the adversary port of `G` and
forwarding on the adversary port of `C` (`RealizesSim.withChan`). The bound is that of `ρ` at the
environment reduced through the relabelling and through the context of `C`.

**Proof.** The parallel composition with `C` preserves the realization (`realizes_par_left`), the
relabelling preserves it (`Open.realizes_relabel`), and the relabelled parallel composition of
the simulated `G` with `C` is the simulator above over `G.withChan C`, at distance `0`
(`realizes_withChan_tensor`): a state map that moves the state of `S` outwards commutes with the
steps, for subroutines that answer each event on the port of the event.

## Main definitions

* `chanEv`, `chanOut`: the regrouping of the ports.
* `Sys.withChan`: a system beside a channel, with the ports regrouped.
* `chanSim`: the simulator of the lifted realization.

## Main results

* `Sys.withChan_portTyped`: the regrouped system answers each event on the port of the event.
* `realizes_withChan_tensor`: the simulator moved over the channel, at distance `0`.
* `RealizesSim.withChan`: the lifting lemma.
* `RealizesSim.withFChan`: the lifting lemma for the ideal channel `FChan cap ℓ`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open MultiHybrid
open scoped ENNReal

variable {EH EA EC ED OH OA OC OD : Type}

/-! ## Regrouping the ports -/

/-- The event map of the regrouping: an honest event of the subroutine or of the channel, or an
adversary event of either, as an event of the parallel composition. -/
def chanEv : (EH ⊕ EC) ⊕ (EA ⊕ ED) → (EH ⊕ EA) ⊕ (EC ⊕ ED)
  | .inl (.inl h) => .inl (.inl h)
  | .inl (.inr c) => .inr (.inl c)
  | .inr (.inl a) => .inl (.inr a)
  | .inr (.inr d) => .inr (.inr d)

/-- The output map of the regrouping. -/
def chanOut : (OH ⊕ OA) ⊕ (OC ⊕ OD) → (OH ⊕ OC) ⊕ (OA ⊕ OD)
  | .inl (.inl h) => .inl (.inl h)
  | .inl (.inr a) => .inr (.inl a)
  | .inr (.inl c) => .inl (.inr c)
  | .inr (.inr d) => .inr (.inr d)

namespace Sys

variable {τ υ : Type}

/-- The system `X` beside the channel `C`: their parallel composition, with the honest ports
and the adversary ports regrouped. -/
noncomputable def withChan (X : Sys τ (EH ⊕ EA) (OH ⊕ OA)) (C : Sys υ (EC ⊕ ED) (OC ⊕ OD)) :
    Sys (τ × υ) ((EH ⊕ EC) ⊕ (EA ⊕ ED)) ((OH ⊕ OC) ⊕ (OA ⊕ OD)) :=
  (X.par C).mapPorts chanEv chanOut

/-- The left port of `X.withChan C`: the honest ports of `X` and `C`. -/
noncomputable def chanPortL (XL : Sys τ EH OH) (CL : Sys υ EC OC) (t₀ : τ) (u₀ : υ) :
    Sys (τ × υ) (EH ⊕ EC) (OH ⊕ OC) :=
  ofPorts (XL.onFst u₀) (CL.onSnd t₀)

/-- The right port of `X.withChan C`: the adversary ports of `X` and `C`. -/
noncomputable def chanPortR (XR : Sys τ EA OA) (CR : Sys υ ED OD) (t₀ : τ) (u₀ : υ) :
    Sys (τ × υ) (EA ⊕ ED) (OA ⊕ OD) :=
  ofPorts (XR.onFst u₀) (CR.onSnd t₀)

variable {X : Sys τ (EH ⊕ EA) (OH ⊕ OA)} {C : Sys υ (EC ⊕ ED) (OC ⊕ OD)}
  {XL : Sys τ EH OH} {XR : Sys τ EA OA} {CL : Sys υ EC OC} {CR : Sys υ ED OD}

/-- A step of `X.withChan C` on an honest event is a step of `chanPortL`. -/
theorem withChan_step_inl
    (hXL : ∀ t e, X.step t (.inl e) = SPComp.map (fun q => (q.1, .inl q.2)) (XL.step t e))
    (hCL : ∀ t e, C.step t (.inl e) = SPComp.map (fun q => (q.1, .inl q.2)) (CL.step t e))
    (t : τ × υ) (e : EH ⊕ EC) :
    (X.withChan C).step t (.inl e) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((chanPortL XL CL X.init C.init).step t e) := by
  obtain ⟨t, u⟩ := t
  rcases e with e | e
  · simp [withChan, mapPorts, relabel, chanPortL, chanEv, chanOut, hXL, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
  · simp [withChan, mapPorts, relabel, chanPortL, chanEv, chanOut, hCL, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]

/-- A step of `X.withChan C` on an adversary event is a step of `chanPortR`. -/
theorem withChan_step_inr
    (hXR : ∀ t e, X.step t (.inr e) = SPComp.map (fun q => (q.1, .inr q.2)) (XR.step t e))
    (hCR : ∀ t e, C.step t (.inr e) = SPComp.map (fun q => (q.1, .inr q.2)) (CR.step t e))
    (t : τ × υ) (e : EA ⊕ ED) :
    (X.withChan C).step t (.inr e) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((chanPortR XR CR X.init C.init).step t e) := by
  obtain ⟨t, u⟩ := t
  rcases e with e | e
  · simp [withChan, mapPorts, relabel, chanPortR, chanEv, chanOut, hXR, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
  · simp [withChan, mapPorts, relabel, chanPortR, chanEv, chanOut, hCR, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]

/-- A system beside a channel, both answering each event on the port of the event, answers each
event on the port of the event. -/
theorem withChan_portTyped (hX : X.PortTyped) (hC : C.PortTyped) : (X.withChan C).PortTyped := by
  obtain ⟨XL, XR, hXL, hXR⟩ := hX
  obtain ⟨CL, CR, hCL, hCR⟩ := hC
  exact ⟨_, _, withChan_step_inl hXL hCL, withChan_step_inr hXR hCR⟩

end Sys

/-! ## The simulator moved over the channel -/

variable {σS EA' OA' : Type}

/-- The simulator of the lifted realization: forwarding on the honest ports, `S` on the
adversary port of the subroutine and forwarding on the adversary port of the channel. -/
noncomputable def chanSim (EH OH EC OC ED OD : Type) (S : MultiHybrid σS EA OA EA' OA') :
    MultiHybrid (Unit × (σS × Unit)) ((EH ⊕ EC) ⊕ (EA ⊕ ED)) ((OH ⊕ OC) ⊕ (OA ⊕ OD))
      ((EH ⊕ EC) ⊕ (EA' ⊕ ED)) ((OH ⊕ OC) ⊕ (OA' ⊕ OD)) :=
  (idSim (EH ⊕ EC) (OH ⊕ OC)).tensor (S.tensor (idSim ED OD))

/-- **The simulator moved over the channel.** For `G` and `C` that answer each event on the port
of the event, `(idSim EH OH).tensor S` over `G`, beside `C`, and `chanSim` over `G` beside `C`
realize each other at distance `0`. -/
theorem realizes_withChan_tensor {τ υ : Type} (S : MultiHybrid σS EA OA EA' OA')
    (G : Sys τ (EH ⊕ EA') (OH ⊕ OA')) (hG : G.PortTyped)
    (C : Sys υ (EC ⊕ ED) (OC ⊕ OD)) (hC : C.PortTyped) :
    Realizes ((((idSim EH OH).tensor S).withSub G).withChan C)
      ((chanSim EH OH EC OC ED OD S).withSub (G.withChan C)) (fun _ _ => 0) := by
  obtain ⟨gL, gR, hGL, hGR⟩ := hG
  obtain ⟨cL, cR, hCL, hCR⟩ := hC
  have hWL := Sys.withChan_step_inl (C := C) hGL hCL
  have hWR := Sys.withChan_step_inr (C := C) hGR hCR
  refine realizes_zero_of_stepMap _ _
    (fun p => (((), (p.1.1.2, ())), (p.1.2, p.2))) rfl ?_
  have hPL : ∀ y g, (Sys.chanPortR gR cR G.init C.init).step y (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((gR.onFst C.init).step y g) := fun _ _ => rfl
  have hPR : ∀ y g, (Sys.chanPortR gR cR G.init C.init).step y (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((cR.onSnd G.init).step y g) := fun _ _ => rfl
  rintro ⟨⟨⟨⟨⟩, s⟩, t⟩, u⟩ ((e | e) | (e | e))
  · rw [chanSim, tensor_withSub_step_inl _ _ _ _ hWL, idSim_stepFuel]
    simp [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut,
      tensor_withSub_step_inl _ _ G gL hGL, idSim_stepFuel, Sys.chanPortL, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
  · rw [chanSim, tensor_withSub_step_inl _ _ _ _ hWL, idSim_stepFuel]
    simp [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut, Sys.chanPortL, hCL,
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [chanSim, tensor_withSub_step_inr _ _ _ _ hWR, tensor_stepFuel_inl _ _ _ _ hPL,
      stepFuel_onFst]
    simp [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut,
      tensor_withSub_step_inr _ _ G gR hGR, idSim_fuel, tensor_fuel, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
  · rw [chanSim, tensor_withSub_step_inr _ _ _ _ hWR, tensor_stepFuel_inr _ _ _ _ hPR,
      idSim_stepFuel]
    simp [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut, hCR, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]

/-! ## The lifting lemma -/

/-- **A subroutine beside a channel.** If `ρ` realizes `G` behind `(idSim EH OH).tensor S` with
bound `bρ`, then `ρ` beside the channel `C` realizes `G` beside `C` behind `chanSim`, with bound
`bρ` at the environment reduced through the regrouping of the ports and through the context of
`C`. The subroutine `G` and the channel answer each event on the port of the event, `C` is
lossless, and `ρ` and the simulated `G` are idle at `idle`. -/
theorem RealizesSim.withChan {τρ τG υ : Type} {VH : PubView EH OH} {VA : PubView EA OA}
    {WA : PubView EA' OA'} {VC : PubView EC OC} {VD : PubView ED OD}
    (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA)
    (ρ : Sys τρ (EH ⊕ EA) (OH ⊕ OA)) (G : Sys τG (EH ⊕ EA') (OH ⊕ OA')) (hG : G.PortTyped)
    (C : Sys υ (EC ⊕ ED) (OC ⊕ OD)) (hC : C.PortTyped)
    (hCf : ∀ u e, SPComp.NoFail (C.step u e)) (idle : EH ⊕ EA)
    (hρI : ∃ o, IdleAt ρ idle o) (hGI : ∃ o, IdleAt (((idSim EH OH).tensor S).withSub G) idle o)
    {bρ : (ζ : Type) → Env (Strat ζ (EH ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞}
    (hρ : RealizesSim ρ G (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS) bρ) :
    RealizesSim (ρ.withChan C) (G.withChan C)
      (Simulator.tensor (idSim (EH ⊕ EC) (OH ⊕ OC)) (S.tensor (idSim ED OD))
        (idSim_opaque (VH.sum VC)) (hS.tensor (idSim_opaque VD)))
      (fun ζ Z => bρ (RState υ (ζ × Unit) (EH ⊕ EA) ((OH ⊕ OA) ⊕ (OC ⊕ OD)))
        ((parCtxL C hCf).reduceEnv idle
          ((Open.relabel () (fun e => ((), chanEv e)) fun _ => chanOut).reduceEnv Z))) := by
  obtain ⟨oρ, hρI⟩ := hρI
  obtain ⟨oG, hGI⟩ := hGI
  have h₁ := realizes_par_left C hCf idle hρI hGI hρ
  have h₂ := Open.realizes_relabel () (fun e => ((), chanEv (EH := EH) (EC := EC) e))
    (fun _ => chanOut) h₁
  have h₃ := realizes_withChan_tensor S G hG C hC
  exact fun ζ Z => le_of_le_of_eq ((Realizes.trans h₂ h₃) ζ Z) (add_zero _)

/-- The ideal channel never fails. -/
theorem FChan_noFail {V Leak : Type} (cap : CatCrypt.Crypto.Choreography.ChannelCap)
    (ℓ : V → Leak) (u : ChanSt V) (e : ChanHEv V ⊕ ChanAEv V) :
    SPComp.NoFail ((FChan cap ℓ).step u e) := by
  rcases e with e | e <;>
    simp only [FChan, Sys.ofPorts_step_inl, Sys.ofPorts_step_inr, FChan.honSys, FChan.advSys,
      SPComp.map] <;>
    exact Assumptions.SPComp.bind_noFail (SPComp.pure_noFail _) fun _ => SPComp.pure_noFail _

/-- **A subroutine beside the ideal channel**: `RealizesSim.withChan` for `FChan cap ℓ`, whose
honest port is seen through `honView cap ℓ` and whose adversary port is forwarded. -/
theorem RealizesSim.withFChan {τρ τG V Leak : Type} {VH : PubView EH OH} {VA : PubView EA OA}
    {WA : PubView EA' OA'} (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA)
    (ρ : Sys τρ (EH ⊕ EA) (OH ⊕ OA)) (G : Sys τG (EH ⊕ EA') (OH ⊕ OA')) (hG : G.PortTyped)
    (cap : CatCrypt.Crypto.Choreography.ChannelCap) (ℓ : V → Leak) (idle : EH ⊕ EA)
    (hρI : ∃ o, IdleAt ρ idle o) (hGI : ∃ o, IdleAt (((idSim EH OH).tensor S).withSub G) idle o)
    {bρ : (ζ : Type) → Env (Strat ζ (EH ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞}
    (hρ : RealizesSim ρ G (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS) bρ) :
    RealizesSim (ρ.withChan (FChan cap ℓ)) (G.withChan (FChan cap ℓ))
      (Simulator.tensor (idSim (EH ⊕ ChanHEv V) (OH ⊕ ChanHOut V))
        (S.tensor (idSim (ChanAEv V) (ChanAOut V Leak)))
        (idSim_opaque (VH.sum (honView cap ℓ))) (hS.tensor (idSim_opaque PubView.eqView)))
      (fun ζ Z => bρ (RState (ChanSt V) (ζ × Unit) (EH ⊕ EA)
          ((OH ⊕ OA) ⊕ (ChanHOut V ⊕ ChanAOut V Leak)))
        ((parCtxL (FChan cap ℓ) (FChan_noFail cap ℓ)).reduceEnv idle
          ((Open.relabel () (fun e => ((), chanEv e)) fun _ => chanOut).reduceEnv Z))) :=
  RealizesSim.withChan S hS ρ G hG (FChan cap ℓ) (FChan_portTyped cap ℓ) _ idle hρI hGI hρ

/-- **Modular composition with a subroutine and a channel.** Let `πH` use the honest ports of a
subroutine and of a channel `C`, and forward their adversary ports. If `ρ` realizes `G` behind
`(idSim EH OH).tensor S` with bound `bρ`, and `πH` over `G` beside `C` realizes `F` behind `SF`
with bound `bF`, then `πH` over `ρ` beside `C` realizes `F` behind `extendFwd EF OF` of `S`
beside the forwarding of the channel's adversary port, composed with `SF`. The bound is `bρ` at
the environment reduced through the protocol, the regrouping and the context of `C`, plus `bF`
at the environment reduced through the extended simulator. -/
theorem RealizesSim.modular_withChan {σ τρ τG τF υ EF OF EI OI : Type}
    {VF : PubView EF OF} {VH : PubView EH OH} {VA : PubView EA OA} {WA : PubView EA' OA'}
    {VC : PubView EC OC} {VD : PubView ED OD} {VI : PubView EI OI}
    (πH : MultiHybrid σ EF OF (EH ⊕ EC) (OH ⊕ OC)) (S : MultiHybrid σS EA OA EA' OA')
    (hS : S.Opaque VA WA) (ρ : Sys τρ (EH ⊕ EA) (OH ⊕ OA)) (G : Sys τG (EH ⊕ EA') (OH ⊕ OA'))
    (hG : G.PortTyped) (C : Sys υ (EC ⊕ ED) (OC ⊕ OD)) (hC : C.PortTyped)
    (hCf : ∀ u e, SPComp.NoFail (C.step u e)) (F : Sys τF EI OI)
    (SF : Simulator (EF ⊕ (EA' ⊕ ED)) (OF ⊕ (OA' ⊕ OD)) EI OI (VF.sum (WA.sum VD)) VI)
    (idleρ : EH ⊕ EA) (idle : (EH ⊕ EC) ⊕ (EA ⊕ ED)) (idleG : (EH ⊕ EC) ⊕ (EA' ⊕ ED))
    (idle' : EF ⊕ (EA' ⊕ ED))
    (hρI₀ : ∃ o, IdleAt ρ idleρ o)
    (hGI₀ : ∃ o, IdleAt (((idSim EH OH).tensor S).withSub G) idleρ o)
    (hρI : ∃ o, IdleAt (ρ.withChan C) idle o)
    (hGI : ∃ o, IdleAt ((chanSim EH OH EC OC ED OD S).withSub (G.withChan C)) idle o)
    (hπGI : ∃ o, IdleAt ((πH.tensor (idSim (EA' ⊕ ED) (OA' ⊕ OD))).withSub (G.withChan C))
      idle' o)
    (hFI : ∃ o, IdleAt (SF.withSub F) idle' o)
    {bρ : (ζ : Type) → Env (Strat ζ (EH ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞}
    {bF : (ζ : Type) → Env (Strat ζ (EF ⊕ (EA' ⊕ ED)) (OF ⊕ (OA' ⊕ OD))) ζ → ℝ≥0∞}
    (hρ : RealizesSim ρ G (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS) bρ)
    (hF : RealizesSim ((πH.tensor (idSim (EA' ⊕ ED) (OA' ⊕ OD))).withSub (G.withChan C)) F SF
      bF) :
    RealizesSim ((πH.tensor (idSim (EA ⊕ ED) (OA ⊕ OD))).withSub (ρ.withChan C)) F
      ((Simulator.ofMultiHybrid (extendFwd EF OF (S.tensor (idSim ED OD)))
        ((hS.tensor (idSim_opaque VD)).extendFwd VF)).comp SF)
      (fun ζ Z =>
        bρ (RState υ ((RState (σ × Unit) ζ ((EH ⊕ EC) ⊕ (EA ⊕ ED)) (OF ⊕ (OA ⊕ OD))) × Unit)
            (EH ⊕ EA) ((OH ⊕ OA) ⊕ (OC ⊕ OD)))
          ((parCtxL C hCf).reduceEnv idleρ
            ((Open.relabel () (fun e => ((), chanEv e)) fun _ => chanOut).reduceEnv
              ((πH.tensor (idSim (EA ⊕ ED) (OA ⊕ OD))).reduceEnv idle Z))) +
        bF (RState (Unit × (σS × Unit)) ζ (EF ⊕ (EA' ⊕ ED)) (OF ⊕ (OA ⊕ OD)))
          ((extendFwd EF OF (S.tensor (idSim ED OD))).reduceEnv idle' Z)) :=
  RealizesSim.modular (VH := VH.sum VC) πH (S.tensor (idSim ED OD)) (hS.tensor (idSim_opaque VD))
    (ρ.withChan C) (G.withChan C) (Sys.withChan_portTyped hG hC) F SF idle idleG idle' hρI hGI
    hπGI hFI (RealizesSim.withChan S hS ρ G hG C hC hCf idleρ hρI₀ hGI₀ hρ) hF

end CatCrypt.Crypto.UCTransparent

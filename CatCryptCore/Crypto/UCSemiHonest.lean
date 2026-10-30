/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCGlobalPipe

/-!
# Composition with a semi-honest corrupt party that drives the subroutine

In the modular UC theorem (`RealizesSim.modular`) the adversary port of the composite is the
adversary port of the subroutine, forwarded by the protocol. A semi-honest corrupt party runs its
own code, and that code may call the subroutine on its adversary port (as in a role swap, where a
corrupt party of the outer protocol plays a corrupt party of the subroutine). Such a party is a
multi-call hybrid `πA` with outer port `(EX, OX)` and subroutine port the adversary port
`(EA, OA)` of the subroutine; the composite is `πH.tensor πA` over the subroutine, where `πH` is
the code of the honest parties.

If `ρ` realizes `G` behind `(idSim EH OH).tensor S`, then `πH.tensor πA` over `ρ` realizes `πH`
forwarding the adversary port of `G` over `G`, behind the corrupt-party wrapper `πA` composed with
`S`, each extended by forwarding on the outer honest port (`semiHonestSim`). The bound is that of
`ρ` realizing `G` at the environment reduced through `πH.tensor πA`
(`RealizesSim.semiHonest`). The proof composes the realization of `ρ` under `πH.tensor πA`
(`MultiHybrid.realizes_compose`) with a state map at distance `0`
(`MultiHybrid.realizes_tensor_wrap`), for `πA` and `πH` of equal fuel. The composite simulator
is opaque over every opaque subroutine (`semiHonestSim_opaque`). Followed by a realization of an
ideal functionality `F` by the hybrid over `G`, the theorem gives the realization of `F` by the
composite (`RealizesSim.semiHonest_modular`).

## Main definitions

* `semiHonestSim`: the corrupt-party wrapper composed with the simulator of the subroutine.
* `semiHonestSimR`: the same, with the environment reductions at idle events.

## Main results

* `MultiHybrid.stepFuel_stepMap`: state maps commute with activations.
* `MultiHybrid.tensor_wrap_step`, `MultiHybrid.realizes_tensor_wrap`: the wrapper and the
  simulator moved out of the composite, at distance `0`.
* `semiHonestSim_opaque`: opacity of the composite simulator.
* `RealizesSim.semiHonest`: the semi-honest composition theorem.
* `RealizesSim.semiHonest_modular`: its composite with a realization of `F` over `G`.
* `SemiHonestExample.realizesSim`: an instance with forwarding parties.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

namespace MultiHybrid

section StepMap

variable {σ τ υ E O EG OG : Type}

/-- A state map `g` from `X` to `Y` that commutes with single steps commutes with the
activations of `π` against `X` and `Y`, for every number of calls. -/
theorem stepFuel_stepMap (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (Y : Sys υ EG OG)
    (g : τ → υ)
    (hstep : ∀ t e, SPComp.map (fun p => (g p.1, p.2)) (X.step t e) = Y.step (g t) e)
    (n : ℕ) (s : σ) (t : τ) (e : E) :
    SPComp.map (fun p => ((p.1.1, g p.1.2), p.2)) (π.stepFuel X n (s, t) e) =
      π.stepFuel Y n (s, g t) e := by
  simp [stepFuel, ← drive_stepMap π X Y g hstep, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]

end StepMap

section Wrap

variable {σH σA σS τ EF OF EH OH EX OX EA OA EA' OA' : Type}

/-- **The wrapper and the simulator moved out.** For `πA` and `πH` of equal fuel and a
subroutine `G` that answers every event on the port of the event, `πH.tensor πA` over
`(idSim EH OH).tensor S` over `G` and `extendFwd EF OF πA` over `extendFwd EF OF S` over `πH`
forwarding the adversary port of `G` over `G` have equal steps, up to the state map that moves
the states of `πA` and `S` outwards. -/
theorem tensor_wrap_step (πH : MultiHybrid σH EF OF EH OH) (πA : MultiHybrid σA EX OX EA OA)
    (S : MultiHybrid σS EA OA EA' OA') (hfuel : πA.fuel = πH.fuel)
    (G : Sys τ (EH ⊕ EA') (OH ⊕ OA')) (hG : G.PortTyped)
    (p : (σH × σA) × ((Unit × σS) × τ)) (e : EF ⊕ EX) :
    SPComp.map (fun q => ((((), q.1.1.2), (((), q.1.2.1.2), ((q.1.1.1, ()), q.1.2.2))), q.2))
        (((πH.tensor πA).withSub (((idSim EH OH).tensor S).withSub G)).step p e) =
      ((extendFwd EF OF πA).withSub ((extendFwd EF OF S).withSub
        ((πH.tensor (idSim EA' OA')).withSub G))).step
        (((), p.1.2), (((), p.2.1.2), ((p.1.1, ()), p.2.2))) e := by
  obtain ⟨KL, KR, hL, hR⟩ := hG
  have hYL := tensor_withSub_portL (idSim EH OH) S G KL hL
  rw [portL_idSim] at hYL
  have hYR := tensor_withSub_portR (idSim EH OH) S G KR hR
  have hZL := tensor_withSub_portL πH (idSim EA' OA') G KL hL
  have hZR := tensor_withSub_portR πH (idSim EA' OA') G KR hR
  rw [portR_idSim] at hZR
  have hWL := tensor_withSub_portL (idSim EF OF) S _ _ hZL
  rw [portL_idSim] at hWL
  have hWR := tensor_withSub_portR (idSim EF OF) S _ _ hZR
  obtain ⟨⟨sH, sA⟩, ⟨⟨⟩, sS⟩, t⟩ := p
  unfold extendFwd
  rcases e with ef | x
  · rw [tensor_withSub_portL _ _ _ _ hYL, tensor_withSub_portL _ _ _ _ hWL, portL_idSim]
    simp only [Sys.onSnd_step, portL]
    rw [stepFuel_onSnd]
    simp [idSim_fuel, hfuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · have hg : ∀ (y : (Unit × σS) × τ) (a : EA),
        SPComp.map (fun q => ((q.1.1, ((sH, ()), q.1.2)), q.2))
          ((portR (idSim EH OH) S KR).step y a) =
        (portR (idSim EF OF) S (KR.onSnd (πH.init, ()))).step (y.1, ((sH, ()), y.2)) a := by
      rintro ⟨⟨⟨⟩, sS'⟩, t'⟩ a
      simp only [portR]
      rw [stepFuel_onSnd]
      simp [idSim_fuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    rw [tensor_withSub_portR _ _ _ _ hYR, tensor_withSub_portR _ _ _ _ hWR]
    set YR := portR (idSim EH OH) S KR
    set WR := portR (idSim EF OF) S (KR.onSnd (πH.init, ()))
    simp only [portR, idSim_fuel, hfuel, max_self, Nat.zero_max]
    rw [← stepFuel_stepMap πA YR WR (fun y => (y.1, ((sH, ()), y.2))) hg πH.fuel sA
      (((), sS), t) x]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **The wrapper and the simulator moved out**, as a realization at distance `0`. -/
theorem realizes_tensor_wrap (πH : MultiHybrid σH EF OF EH OH)
    (πA : MultiHybrid σA EX OX EA OA) (S : MultiHybrid σS EA OA EA' OA')
    (hfuel : πA.fuel = πH.fuel) (G : Sys τ (EH ⊕ EA') (OH ⊕ OA')) (hG : G.PortTyped) :
    Realizes ((πH.tensor πA).withSub (((idSim EH OH).tensor S).withSub G))
      ((extendFwd EF OF πA).withSub ((extendFwd EF OF S).withSub
        ((πH.tensor (idSim EA' OA')).withSub G))) (fun _ _ => 0) :=
  realizes_zero_of_stepMap _ _
    (fun p => (((), p.1.2), (((), p.2.1.2), ((p.1.1, ()), p.2.2)))) rfl
    (tensor_wrap_step πH πA S hfuel G hG)

end Wrap

end MultiHybrid

open MultiHybrid

section SemiHonest

variable {σA σS EF OF EX OX EA OA EA' OA' : Type} {VX : PubView EX OX} {VA : PubView EA OA}
  {WA : PubView EA' OA'}

/-- The corrupt-party wrapper `πA` composed with the simulator `S` of the subroutine, each
extended by forwarding on the honest port `(EF, OF)`: a simulator from the adversary port
`(EA', OA')` of the subroutine to the outer adversary port `(EX, OX)`. -/
noncomputable def semiHonestSim (VF : PubView EF OF) (πA : MultiHybrid σA EX OX EA OA)
    (hA : πA.Opaque VX VA) (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA) :
    Simulator (EF ⊕ EX) (OF ⊕ OX) (EF ⊕ EA') (OF ⊕ OA') (VF.sum VX) (VF.sum WA) :=
  (Simulator.ofMultiHybrid (extendFwd EF OF πA) (hA.extendFwd VF)).comp
    (Simulator.ofMultiHybrid (extendFwd EF OF S) (hS.extendFwd VF))

/-- Unfolding lemma of `semiHonestSim`: over `X`, the extended wrapper over the extended
simulator over `X`. -/
@[simp] theorem semiHonestSim_withSub (VF : PubView EF OF) (πA : MultiHybrid σA EX OX EA OA)
    (hA : πA.Opaque VX VA) (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA) {τ : Type}
    (X : Sys τ (EF ⊕ EA') (OF ⊕ OA')) :
    (semiHonestSim VF πA hA S hS).withSub X =
      (extendFwd EF OF πA).withSub ((extendFwd EF OF S).withSub X) := rfl

/-- **Opacity of the composite simulator**: over a subroutine opaque for `VF.sum WA`, the
wrapper over the simulator is opaque for `VF.sum VX`. -/
theorem semiHonestSim_opaque (VF : PubView EF OF) (πA : MultiHybrid σA EX OX EA OA)
    (hA : πA.Opaque VX VA) (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA) {τ : Type}
    (X : Sys τ (EF ⊕ EA') (OF ⊕ OA')) (hX : X.Opaque (VF.sum WA)) :
    ((extendFwd EF OF πA).withSub ((extendFwd EF OF S).withSub X)).Opaque (VF.sum VX) :=
  (semiHonestSim VF πA hA S hS).isOpaque X hX

/-- **Semi-honest composition.** Let `πH` be the code of the honest parties, with outer port
`(EF, OF)` and the honest port `(EH, OH)` of the subroutine, and `πA` the code of a semi-honest
corrupt party, with outer port `(EX, OX)` and the adversary port `(EA, OA)` of the subroutine,
of the fuel of `πH`. If `ρ` realizes `G` behind `(idSim EH OH).tensor S` with bound `bρ`, then
`πH.tensor πA` over `ρ` realizes `πH` forwarding the adversary port of `G` over `G`, behind the
wrapper `πA` composed with `S` (`semiHonestSim`), with bound `bρ` at the environment reduced
through `πH.tensor πA`. The subroutine `G` answers every event on the port of the event, and `ρ`
and `S` over `G` are idle at `idle`. -/
theorem RealizesSim.semiHonest {σH τρ τG EH OH : Type} {VF : PubView EF OF}
    {VH : PubView EH OH} (πH : MultiHybrid σH EF OF EH OH) (πA : MultiHybrid σA EX OX EA OA)
    (hA : πA.Opaque VX VA) (hfuel : πA.fuel = πH.fuel) (S : MultiHybrid σS EA OA EA' OA')
    (hS : S.Opaque VA WA) (ρ : Sys τρ (EH ⊕ EA) (OH ⊕ OA)) (G : Sys τG (EH ⊕ EA') (OH ⊕ OA'))
    (hG : G.PortTyped) (idle : EH ⊕ EA) (hρI : ∃ o, IdleAt ρ idle o)
    (hGI : ∃ o, IdleAt (((idSim EH OH).tensor S).withSub G) idle o)
    {bρ : (ζ : Type) → Env (Strat ζ (EH ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞}
    (hρ : RealizesSim ρ G (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS) bρ) :
    RealizesSim ((πH.tensor πA).withSub ρ) ((πH.tensor (idSim EA' OA')).withSub G)
      (semiHonestSim VF πA hA S hS)
      (fun ζ Z => bρ (RState (σH × σA) ζ (EH ⊕ EA) (OF ⊕ OX))
        ((πH.tensor πA).reduceEnv idle Z)) := by
  obtain ⟨oρ, hρI⟩ := hρI
  obtain ⟨oG, hGI⟩ := hGI
  have h := realizes_compose (πH.tensor πA) idle oρ oG ρ _ _ hρI hGI _ _
    (realizes_tensor_wrap πH πA S hfuel G hG) hρ
  intro ζ Z
  refine le_of_le_of_eq (h ζ Z) ?_
  simp only [add_zero]

/-- The corrupt-party wrapper composed with the simulator of the subroutine, with the
environment reductions at the idle events `idleA` of the wrapper and `idleS` of the
simulator. -/
noncomputable def semiHonestSimR (VF : PubView EF OF) (πA : MultiHybrid σA EX OX EA OA)
    (hA : πA.Opaque VX VA) (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA)
    (idleA : EF ⊕ EA) (idleS : EF ⊕ EA') :
    SimR (EF ⊕ EX) (OF ⊕ OX) (EF ⊕ EA') (OF ⊕ OA') (VF.sum VX) (VF.sum WA) :=
  (SimR.ofMultiHybrid (extendFwd EF OF πA) (hA.extendFwd VF) idleA).comp
    (SimR.ofMultiHybrid (extendFwd EF OF S) (hS.extendFwd VF) idleS)

/-- **Semi-honest modular composition.** Under the hypotheses of `RealizesSim.semiHonest`, if
`πH` forwarding the adversary port of `G` over `G` realizes `F` behind `SF` with bound `bF`, then
`πH.tensor πA` over `ρ` realizes `F` behind the wrapper `πA` composed with `S` and with `SF`,
with bound `bρ` at the environment reduced through `πH.tensor πA` plus `bF` at the environment
reduced through the extended wrapper and the extended simulator. The hybrid over `G` and `SF`
over `F` are idle at `idleS`, and the extended simulator over each of them at `idleA`. -/
theorem RealizesSim.semiHonest_modular {σH τρ τG τF EH OH EI OI : Type} {VF : PubView EF OF}
    {VH : PubView EH OH} {VI : PubView EI OI} (πH : MultiHybrid σH EF OF EH OH)
    (πA : MultiHybrid σA EX OX EA OA) (hA : πA.Opaque VX VA) (hfuel : πA.fuel = πH.fuel)
    (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA) (ρ : Sys τρ (EH ⊕ EA) (OH ⊕ OA))
    (G : Sys τG (EH ⊕ EA') (OH ⊕ OA')) (hG : G.PortTyped) (F : Sys τF EI OI)
    (SF : Simulator (EF ⊕ EA') (OF ⊕ OA') EI OI (VF.sum WA) VI)
    (idle : EH ⊕ EA) (idleA : EF ⊕ EA) (idleS : EF ⊕ EA') (hρI : ∃ o, IdleAt ρ idle o)
    (hGI : ∃ o, IdleAt (((idSim EH OH).tensor S).withSub G) idle o)
    (hJ : (semiHonestSimR VF πA hA S hS idleA idleS).Adm
      ((πH.tensor (idSim EA' OA')).withSub G))
    (hI : (semiHonestSimR VF πA hA S hS idleA idleS).Adm (SF.withSub F))
    {bρ : (ζ : Type) → Env (Strat ζ (EH ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞}
    {bF : (ζ : Type) → Env (Strat ζ (EF ⊕ EA') (OF ⊕ OA')) ζ → ℝ≥0∞}
    (hρ : RealizesSim ρ G (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS) bρ)
    (hF : RealizesSim ((πH.tensor (idSim EA' OA')).withSub G) F SF bF) :
    RealizesSim ((πH.tensor πA).withSub ρ) F ((semiHonestSim VF πA hA S hS).comp SF)
      (fun ζ Z => bρ (RState (σH × σA) ζ (EH ⊕ EA) (OF ⊕ OX))
          ((πH.tensor πA).reduceEnv idle Z) +
        bF _ ((extendFwd EF OF S).reduceEnv idleS ((extendFwd EF OF πA).reduceEnv idleA Z))) := by
  have h := RealizesSim.comp (semiHonestSimR VF πA hA S hS idleA idleS) SF hJ hI
    (RealizesSim.semiHonest (VH := VH) πH πA hA hfuel S hS ρ G hG idle hρI hGI hρ) hF
  intro ζ Z
  refine le_of_le_of_eq (h ζ Z) ?_
  have hE : ((Open.ofMultiHybrid (extendFwd EF OF πA) idleA).comp
      (Open.ofMultiHybrid (extendFwd EF OF S) idleS)).reduceEnv Z =
      (extendFwd EF OF S).reduceEnv idleS ((extendFwd EF OF πA).reduceEnv idleA Z) := by
    rw [Open.reduceEnv_comp, Open.reduceEnv_ofMultiHybrid, Open.reduceEnv_ofMultiHybrid]
    rfl
  exact congrArg (fun E => bρ (RState (σH × σA) ζ (EH ⊕ EA) (OF ⊕ OX))
    ((πH.tensor πA).reduceEnv idle Z) + bF _ E) hE

end SemiHonest

/-! ## An instance with forwarding parties -/

namespace SemiHonestExample

/-- The view of `Unit ⊕ Unit` with every event and output public. -/
def V : PubView (Unit ⊕ Unit) (Unit ⊕ Unit) := PubView.ofProj _root_.id _root_.id

/-- The view of `Unit` with every event and output public. -/
def VU : PubView Unit Unit := PubView.ofProj _root_.id _root_.id

/-- The subroutine on `Unit ⊕ Unit` that answers each event on the port of the event. -/
noncomputable def G : Sys Unit (Unit ⊕ Unit) (Unit ⊕ Unit) := ⟨(), fun t e => SPComp.pure (t, e)⟩

/-- The real subroutine: the forwarding simulators over `G`. -/
noncomputable def ρ : Sys ((Unit × Unit) × Unit) (Unit ⊕ Unit) (Unit ⊕ Unit) :=
  ((idSim Unit Unit).tensor (idSim Unit Unit)).withSub G

/-- `G` answers each event on the port of the event. -/
theorem G_portTyped : G.PortTyped :=
  ⟨⟨(), fun t e => SPComp.pure (t, e)⟩, ⟨(), fun t e => SPComp.pure (t, e)⟩,
    fun t e => by simp [G, SPComp.map, SPComp.pure_bind],
    fun t e => by simp [G, SPComp.map, SPComp.pure_bind]⟩

/-- The semi-honest composition theorem for forwarding honest and corrupt parties. -/
theorem realizesSim :
    RealizesSim (((idSim Unit Unit).tensor (idSim Unit Unit)).withSub ρ)
      (((idSim Unit Unit).tensor (idSim Unit Unit)).withSub G)
      (semiHonestSim VU (idSim Unit Unit) (idSim_opaque VU) (idSim Unit Unit) (idSim_opaque VU))
      (fun _ _ => 0) :=
  RealizesSim.semiHonest (VH := VU) (idSim Unit Unit) (idSim Unit Unit) (idSim_opaque VU) rfl
    (idSim Unit Unit) (idSim_opaque VU) ρ G G_portTyped (.inl ())
    ⟨.inl (), fun _ => by simp [ρ, G, withSub, tensor, idSim, drive, SPComp.map, SPComp.pure_bind]⟩
    ⟨.inl (), fun _ => by simp [G, withSub, tensor, idSim, drive, SPComp.map, SPComp.pure_bind]⟩
    (bρ := fun _ _ => 0) (fun _ => DistC.refl _)

end SemiHonestExample

end CatCrypt.Crypto.UCTransparent

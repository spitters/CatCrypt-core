/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCGlobalSquare

/-!
# Modular composition over a shared global functionality

A square over a global functionality (`GSquare`) exposes one port of the global functionality
`G` to the environment. A protocol `π` that uses a subprotocol `ρ` over `G` and calls `G`
itself needs two exposed ports: the port of `π` and the port of the environment. This file
derives the realization with two exposed ports from a square with one, and from it the modular
composition theorem over a shared global functionality.

The two-port form of a protocol `ρ` over `G` is `gReal3 ρ G`: `ρ` beside the forwarding
simulator on two ports of `G`, over the three-port merge `G.merge3`, with the ports ordered as
the honest port of `ρ` beside the first port of `G`, and the adversary port of `ρ` beside the
second port of `G`. It is the one-port form `gReal ρ G` behind the router `Open.twoPort`, a port
relabelling that sends both ports of `G` to the single port of `G` and remembers the port of the
pending event (`gReal3_eq_relabel`, for every fuel of `ρ`).

The router commutes with the simulator of one-shot emulation at distance `0`
(`realizes_relabel_gSimHybrid`): the simulator `S` on the adversary port beside forwarding on
the honest port and on the port of `G`, behind the router, is the simulator `S` beside
forwarding on the second port of `G`, on the adversary side of the two-port interface. This
needs the ideal system to answer each event on the port of the event (`Sys.PortTyped3`).

## Main definitions

* `Sys.copair`: two systems on one state, answering the two ports of a sum interface.
* `Sys.PortTyped3`: a system on a three-port interface that answers each event on its port.
* `Sys.twoPortEv`, `Sys.twoPortOut`, `Open.twoPort`: the router onto one port of `G`.
* `Sys.gPermEv`, `Sys.gPermOut`, `gReal3`: the protocol over `G.merge3` with two exposed ports.

## Main results

* `MultiHybrid.tensor_stepFuel_inl`, `MultiHybrid.tensor_stepFuel_inr`: activations of the
  tensor with any number of calls.
* `gReal3_eq_relabel`: the three-port merge form is the one-port form behind the router.
* `realizes_relabel_gSimHybrid`: the router commuted past the simulator at distance `0`.
* `GSquare.twoPort`: a square pinned to `G` gives the realization with two exposed ports.
* `GSquare.modular`: the modular composition theorem over a shared global functionality.
* `GSquare.modular_fwd`: the same with a hybrid simulator that forwards the environment's port
  of `G`, so that the composite simulator forwards it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Systems on a three-port interface -/

namespace Sys

variable {υ E₁ O₁ E₂ O₂ E₃ O₃ : Type}

/-- Two systems on one state as a system on the sum interface: an event on a port is a step
of the system of that port, answered on the same port. -/
noncomputable def copair (init : υ) (X₁ : Sys υ E₁ O₁) (X₂ : Sys υ E₂ O₂) :
    Sys υ (E₁ ⊕ E₂) (O₁ ⊕ O₂) where
  init := init
  step t := Sum.elim (fun e => SPComp.map (fun q => (q.1, .inl q.2)) (X₁.step t e))
    (fun e => SPComp.map (fun q => (q.1, .inr q.2)) (X₂.step t e))

/-- The system `Y` on the interface `(E₁ ⊕ E₂) ⊕ E₃` answers every event on the port of the
event: its steps on each port are those of a system on that port with the state of `Y`. -/
def PortTyped3 (Y : Sys υ ((E₁ ⊕ E₂) ⊕ E₃) ((O₁ ⊕ O₂) ⊕ O₃)) : Prop :=
  ∃ (Y₁ : Sys υ E₁ O₁) (Y₂ : Sys υ E₂ O₂) (Y₃ : Sys υ E₃ O₃),
    (∀ t e, Y.step t (.inl (.inl e)) =
      SPComp.map (fun q => (q.1, .inl (.inl q.2))) (Y₁.step t e)) ∧
    (∀ t e, Y.step t (.inl (.inr e)) =
      SPComp.map (fun q => (q.1, .inl (.inr q.2))) (Y₂.step t e)) ∧
    (∀ t e, Y.step t (.inr e) = SPComp.map (fun q => (q.1, .inr q.2)) (Y₃.step t e))

end Sys

/-! ## Activations of the tensor with any number of calls -/

namespace MultiHybrid

variable {σ σ' τ E O E' O' EG OG EG' OG' : Type}

/-- An activation of the tensor on a left event, with `n` calls after the first, against a
subroutine that answers left events on the left port with `XL`, is an activation of `π` against
`XL`. -/
theorem tensor_stepFuel_inl (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (XL : Sys τ EG OG)
    (hX : ∀ t g, X.step t (.inl g) = SPComp.map (fun q => (q.1, .inl q.2)) (XL.step t g))
    (n : ℕ) (s : σ) (s' : σ') (t : τ) (e : E) :
    (π.tensor π').stepFuel X n ((s, s'), t) (.inl e) =
      SPComp.map (fun p => (((p.1.1, s'), p.1.2), Sum.inl p.2)) (π.stepFuel XL n (s, t) e) := by
  simp only [stepFuel, tensor_start_inl, tensor_drive_inl π π' X XL hX, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]

/-- An activation of the tensor on a right event, with `n` calls after the first, against a
subroutine that answers right events on the right port with `XR`, is an activation of `π'`
against `XR`. -/
theorem tensor_stepFuel_inr (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (XR : Sys τ EG' OG')
    (hX : ∀ t g, X.step t (.inr g) = SPComp.map (fun q => (q.1, .inr q.2)) (XR.step t g))
    (n : ℕ) (s : σ) (s' : σ') (t : τ) (e : E') :
    (π.tensor π').stepFuel X n ((s, s'), t) (.inr e) =
      SPComp.map (fun p => (((s, p.1.1), p.1.2), Sum.inr p.2)) (π'.stepFuel XR n (s', t) e) := by
  simp only [stepFuel, tensor_start_inr, tensor_drive_inr π π' X XR hX, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

/-! ## The router onto one port of the global functionality -/

namespace Sys

variable {EH EA EG OH OA OG : Type}

/-- The event map of the router: the honest port and the first port of `G` carry the tag
`true`, the adversary port and the second port of `G` the tag `false`, and both ports of `G`
go to the single port of `G`. -/
def twoPortEv : (EH ⊕ EG) ⊕ (EA ⊕ EG) → Bool × ((EH ⊕ EA) ⊕ EG)
  | .inl (.inl h) => (true, .inl (.inl h))
  | .inl (.inr g) => (true, .inr g)
  | .inr (.inl a) => (false, .inl (.inr a))
  | .inr (.inr g) => (false, .inr g)

/-- The output map of the router: an answer of `G` goes to the port of `G` named by the tag. -/
def twoPortOut : Bool → (OH ⊕ OA) ⊕ OG → (OH ⊕ OG) ⊕ (OA ⊕ OG)
  | _, .inl (.inl h) => .inl (.inl h)
  | _, .inl (.inr a) => .inr (.inl a)
  | true, .inr g => .inl (.inr g)
  | false, .inr g => .inr (.inr g)

/-- The event map from the two-port interface to the tensor of a protocol with the forwarding
simulator on two ports of `G`. -/
def gPermEv : (EH ⊕ EG) ⊕ (EA ⊕ EG) → (EH ⊕ EA) ⊕ (EG ⊕ EG)
  | .inl (.inl h) => .inl (.inl h)
  | .inl (.inr g) => .inr (.inl g)
  | .inr (.inl a) => .inl (.inr a)
  | .inr (.inr g) => .inr (.inr g)

/-- The output map from the tensor of a protocol with the forwarding simulator on two ports of
`G` to the two-port interface. -/
def gPermOut : (OH ⊕ OA) ⊕ (OG ⊕ OG) → (OH ⊕ OG) ⊕ (OA ⊕ OG)
  | .inl (.inl h) => .inl (.inl h)
  | .inl (.inr a) => .inr (.inl a)
  | .inr (.inl g) => .inl (.inr g)
  | .inr (.inr g) => .inr (.inr g)

end Sys

/-- **The router** as an open system: the two-port interface onto the one-port interface of a
protocol over `G`. The reduced environment remembers the tag of the pending event. -/
noncomputable def Open.twoPort (EH OH EA OA EG OG : Type) :
    Open ((EH ⊕ EG) ⊕ (EA ⊕ EG)) ((OH ⊕ OG) ⊕ (OA ⊕ OG)) ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG) :=
  Open.relabel true Sys.twoPortEv Sys.twoPortOut

section Router

variable {υ EH EA EG OH OA OG : Type}

/-- Behind the router, the honest port and the first port of `G` of a system that answers each
event on its port are answered by the copair of the honest and the `G` components. -/
theorem relabel_twoPort_step_inl (Y : Sys υ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG))
    (YH : Sys υ EH OH) (YG : Sys υ EG OG)
    (hH : ∀ t e, Y.step t (.inl (.inl e)) =
      SPComp.map (fun q => (q.1, .inl (.inl q.2))) (YH.step t e))
    (hG : ∀ t e, Y.step t (.inr e) = SPComp.map (fun q => (q.1, .inr q.2)) (YG.step t e))
    (t : υ) (x : EH ⊕ EG) :
    (Y.relabel Sys.twoPortEv Sys.twoPortOut).step t (.inl x) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((Sys.copair Y.init YH YG).step t x) := by
  rcases x with h | g
  · simp [Sys.relabel, Sys.twoPortEv, Sys.copair, hH, Sys.twoPortOut, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
  · simp [Sys.relabel, Sys.twoPortEv, Sys.copair, hG, Sys.twoPortOut, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]

/-- Behind the router, the adversary port and the second port of `G` of a system that answers
each event on its port are answered by the copair of the adversary and the `G` components. -/
theorem relabel_twoPort_step_inr (Y : Sys υ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG))
    (YA : Sys υ EA OA) (YG : Sys υ EG OG)
    (hA : ∀ t e, Y.step t (.inl (.inr e)) =
      SPComp.map (fun q => (q.1, .inl (.inr q.2))) (YA.step t e))
    (hG : ∀ t e, Y.step t (.inr e) = SPComp.map (fun q => (q.1, .inr q.2)) (YG.step t e))
    (t : υ) (x : EA ⊕ EG) :
    (Y.relabel Sys.twoPortEv Sys.twoPortOut).step t (.inr x) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((Sys.copair Y.init YA YG).step t x) := by
  rcases x with a | g
  · simp [Sys.relabel, Sys.twoPortEv, Sys.copair, hA, Sys.twoPortOut, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
  · simp [Sys.relabel, Sys.twoPortEv, Sys.copair, hG, Sys.twoPortOut, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]

/-- A system that answers each event on its port of the three-port interface answers each event
on its port of the two-port interface behind the router. -/
theorem Sys.PortTyped3.portTyped_relabel {Y : Sys υ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)}
    (hY : Y.PortTyped3) : (Y.relabel Sys.twoPortEv Sys.twoPortOut).PortTyped := by
  obtain ⟨YH, YA, YG, hH, hA, hG⟩ := hY
  exact ⟨_, _, relabel_twoPort_step_inl Y YH YG hH hG, relabel_twoPort_step_inr Y YA YG hA hG⟩

end Router

/-! ## The protocol over the three-port merge -/

section Merge3

variable {σ τ EH EA EG OH OA OG : Type}

/-- **The protocol with two exposed ports of the global functionality**: `π` beside the
forwarding simulator on two ports of `G`, over the three-port merge `G.merge3`, on the
interface with the honest port beside the first port of `G` and the adversary port beside the
second port of `G`. -/
noncomputable def gReal3 (π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG) (G : Sys τ EG OG) :
    Sys ((σ × Unit) × τ) ((EH ⊕ EG) ⊕ (EA ⊕ EG)) ((OH ⊕ OG) ⊕ (OA ⊕ OG)) :=
  ((π.tensor (MultiHybrid.idSim (EG ⊕ EG) (OG ⊕ OG))).withSub G.merge3).mapPorts Sys.gPermEv
    Sys.gPermOut

/-- **Flattening**: the protocol over the three-port merge is the protocol over the merge
behind the router, for every fuel of `π`. -/
theorem gReal3_eq_relabel (π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG) (G : Sys τ EG OG) :
    gReal3 π G = (gReal π G).relabel Sys.twoPortEv Sys.twoPortOut := by
  have h3L : ∀ t g, G.merge3.step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) (G.step t g) := fun _ _ => rfl
  have h3R : ∀ t g, G.merge3.step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) (G.merge.step t g) := by
    intro t g
    rcases g with g | g <;>
      simp [Sys.merge3, Sys.merge, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have h2L : ∀ t g, G.merge.step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) (G.step t g) := fun _ _ => rfl
  have h2R : ∀ t g, G.merge.step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) (G.step t g) := fun _ _ => rfl
  unfold gReal3 gReal Sys.mapPorts Sys.relabel
  congr 1
  funext t e
  obtain ⟨⟨s, ⟨⟩⟩, x⟩ := t
  rcases e with (h | g) | (a | g)
  · simp only [Sys.gPermEv, Sys.twoPortEv]
    rw [MultiHybrid.tensor_withSub_step_inl _ _ _ _ h3L,
      MultiHybrid.tensor_withSub_step_inl _ _ _ _ h2L]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg (SPComp.bind _) (funext fun p => ?_)
    rcases p with ⟨_, o | o⟩ <;> rfl
  · simp only [Sys.gPermEv, Sys.twoPortEv]
    rw [MultiHybrid.tensor_withSub_step_inr _ _ _ _ h3R, MultiHybrid.idSim_stepFuel,
      MultiHybrid.tensor_withSub_step_inr _ _ _ _ h2R, MultiHybrid.idSim_stepFuel, h2L]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sys.gPermOut, Sys.twoPortOut]
  · simp only [Sys.gPermEv, Sys.twoPortEv]
    rw [MultiHybrid.tensor_withSub_step_inl _ _ _ _ h3L,
      MultiHybrid.tensor_withSub_step_inl _ _ _ _ h2L]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg (SPComp.bind _) (funext fun p => ?_)
    rcases p with ⟨_, o | o⟩ <;> rfl
  · simp only [Sys.gPermEv, Sys.twoPortEv]
    rw [MultiHybrid.tensor_withSub_step_inr _ _ _ _ h3R, MultiHybrid.idSim_stepFuel,
      MultiHybrid.tensor_withSub_step_inr _ _ _ _ h2R, MultiHybrid.idSim_stepFuel, h2R]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sys.gPermOut, Sys.twoPortOut]

/-- The protocol over the three-port merge answers each event on its port of the two-port
interface when the protocol over the merge answers each event on its port of the three-port
interface. -/
theorem gReal3_portTyped {π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG} {G : Sys τ EG OG}
    (h : (gReal π G).PortTyped3) : (gReal3 π G).PortTyped := by
  rw [gReal3_eq_relabel]
  exact h.portTyped_relabel

end Merge3

/-! ## The router commuted past the simulator -/

section Commute

variable {σS υ EH EA EA' EG OH OA OA' OG : Type}

open MultiHybrid in
/-- **The router commuted past the simulator of one-shot emulation**, at distance `0`. Behind
the router, the simulator `S` on the adversary port beside forwarding on the honest port and on
the port of `G`, over `Y`, and the forwarding simulator on the honest side beside `S` and
forwarding on the second port of `G`, over `Y` behind the router, realize each other. The
system `Y` answers each event on its port. -/
theorem realizes_relabel_gSimHybrid (S : MultiHybrid σS EA OA EA' OA')
    (Y : Sys υ ((EH ⊕ EA') ⊕ EG) ((OH ⊕ OA') ⊕ OG)) (hY : Y.PortTyped3) :
    Realizes (((gSimHybrid EH OH EG OG S).withSub Y).relabel Sys.twoPortEv Sys.twoPortOut)
      (((idSim (EH ⊕ EG) (OH ⊕ OG)).tensor (S.tensor (idSim EG OG))).withSub
        (Y.relabel Sys.twoPortEv Sys.twoPortOut)) (fun _ _ => 0) := by
  obtain ⟨YH, YA, YG, hH, hA, hG⟩ := hY
  have hL : ∀ t x, Y.step t (.inl x) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((Sys.copair Y.init YH YA).step t x) := by
    intro t x
    rcases x with h | a
    · simp [Sys.copair, hH, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [Sys.copair, hA, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have hLH : ∀ t h, (Sys.copair Y.init YH YA).step t (.inl h) =
      SPComp.map (fun q => (q.1, .inl q.2)) (YH.step t h) := fun _ _ => rfl
  have hLA : ∀ t a, (Sys.copair Y.init YH YA).step t (.inr a) =
      SPComp.map (fun q => (q.1, .inr q.2)) (YA.step t a) := fun _ _ => rfl
  have hRA : ∀ t a, (Sys.copair Y.init YA YG).step t (.inl a) =
      SPComp.map (fun q => (q.1, .inl q.2)) (YA.step t a) := fun _ _ => rfl
  have hRG : ∀ t g, (Sys.copair Y.init YA YG).step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) (YG.step t g) := fun _ _ => rfl
  have hRL := relabel_twoPort_step_inl Y YH YG hH hG
  have hRR := relabel_twoPort_step_inr Y YA YG hA hG
  refine realizes_zero_of_stepMap _ _ (fun p => (((), (p.1.1.2, ())), p.2)) rfl ?_
  rintro ⟨⟨⟨⟨⟩, sS⟩, ⟨⟩⟩, t⟩ ((h | g) | (a | g))
  · rw [tensor_withSub_step_inl _ _ _ _ hRL, idSim_stepFuel]
    simp only [Sys.relabel, Sys.twoPortEv, gSimHybrid]
    rw [tensor_withSub_step_inl _ _ Y _ hL, tensor_stepFuel_inl _ _ _ YH hLH, idSim_stepFuel]
    simp [Sys.copair, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sys.twoPortOut]
  · rw [tensor_withSub_step_inl _ _ _ _ hRL, idSim_stepFuel]
    simp only [Sys.relabel, Sys.twoPortEv, gSimHybrid]
    rw [tensor_withSub_step_inr _ _ Y _ hG, idSim_stepFuel]
    simp [Sys.copair, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sys.twoPortOut]
  · rw [tensor_withSub_step_inr _ _ _ _ hRR, tensor_stepFuel_inl _ _ _ YA hRA]
    simp only [Sys.relabel, Sys.twoPortEv, gSimHybrid]
    rw [tensor_withSub_step_inl _ _ Y _ hL, tensor_stepFuel_inr _ _ _ YA hLA]
    simp only [tensor, idSim, Nat.zero_max, Nat.max_zero, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg (SPComp.bind _) (funext fun p => ?_)
    rfl
  · rw [tensor_withSub_step_inr _ _ _ _ hRR, tensor_stepFuel_inr _ _ _ YG hRG, idSim_stepFuel]
    simp only [Sys.relabel, Sys.twoPortEv, gSimHybrid]
    rw [tensor_withSub_step_inr _ _ Y _ hG, idSim_stepFuel]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sys.twoPortOut]

end Commute

/-! ## Two exposed ports and the modular theorem -/

namespace GSquare

open MultiHybrid

variable {σρ σF σS τG EH OH EA OA EA' OA' EG OG : Type} {VH : PubView EH OH}
  {VA : PubView EA OA} {WA : PubView EA' OA'} {WG : PubView EG OG}

/-- **Two exposed ports from one.** A square over `G` for `ρ` above `F`, pinned to `G`, gives the
realization of `gReal3 F G` by `gReal3 ρ G` behind the forwarding simulator on the honest side
(honest port and first port of `G`) beside `S` and forwarding on the second port of `G`. The
bound is that of the square at the environment reduced through the router. The protocol `F`
over `G` answers each event on its port. -/
theorem twoPort {G : Sys τG EG OG} {ρ : MultiHybrid σρ (EH ⊕ EA) (OH ⊕ OA) EG OG}
    {F : MultiHybrid σF (EH ⊕ EA') (OH ⊕ OA') EG OG} {S : MultiHybrid σS EA OA EA' OA'}
    {hS : S.Opaque VA WA} {idleρ idleF : EG ⊕ EG}
    {b : {τ : Type} → Sys τ EG OG → (ζ : Type) →
      Env (Strat ζ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) ζ → ℝ≥0∞}
    (h : GSquare (VH := VH) (WG := WG) ρ F S hS idleρ idleF (pinSub G) b)
    (hF : (gReal F G).PortTyped3) :
    RealizesSim (gReal3 ρ G) (gReal3 F G)
      (Simulator.tensor (idSim (EH ⊕ EG) (OH ⊕ OG)) (S.tensor (idSim EG OG))
        (idSim_opaque (VH.sum WG)) (hS.tensor (idSim_opaque WG)))
      (fun ζ Z => b G (ζ × Bool) ((Open.twoPort EH OH EA OA EG OG).reduceEnv Z)) := by
  have h₁ := Open.realizes_relabel true Sys.twoPortEv Sys.twoPortOut h.realizes_gReal
  have h₂ := realizes_relabel_gSimHybrid S (gReal F G) hF
  have h₃ := Realizes.trans h₁ h₂
  unfold RealizesSim
  rw [gReal3_eq_relabel, gReal3_eq_relabel]
  intro ζ Z
  refine le_of_le_of_eq (h₃ ζ Z) ?_
  simp only [add_zero]
  rfl

/-- **Modular composition over a shared global functionality.** Let `ρ` realize `F₁` over `G`
by a square pinned to `G` with simulator `S`, and let `π` be a protocol that calls the honest
port of `F₁` and the global functionality `G`. If `π` over `F₁` with two exposed ports of `G`
(`gReal3 F₁ G`) realizes `F` behind `SF` with bound `bF`, then `π` over `ρ` with two exposed
ports of `G` realizes `F` behind the extension by forwarding on the port of `π` of `S` beside
forwarding on the port of `G`, composed with `SF`. The composite simulator forwards the
environment's port of `G` in its first factor. The bound is the bound of the square at the
environment reduced through `π` and the router, plus `bF` at the environment reduced through
the extension. The protocol `F₁` over `G` answers each event on its port, and the systems
involved are idle at the idle events of the reductions. -/
theorem modular {σ τF EF OF EI OI : Type} {VF : PubView EF OF} {VI : PubView EI OI}
    {G : Sys τG EG OG} (π : MultiHybrid σ EF OF (EH ⊕ EG) (OH ⊕ OG))
    {ρ : MultiHybrid σρ (EH ⊕ EA) (OH ⊕ OA) EG OG}
    {F₁ : MultiHybrid σF (EH ⊕ EA') (OH ⊕ OA') EG OG} {S : MultiHybrid σS EA OA EA' OA'}
    {hS : S.Opaque VA WA} {idleρ idleF : EG ⊕ EG}
    {b : {τ : Type} → Sys τ EG OG → (ζ : Type) →
      Env (Strat ζ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) ζ → ℝ≥0∞}
    (h : GSquare (VH := VH) (WG := WG) ρ F₁ S hS idleρ idleF (pinSub G) b)
    (hF₁ : (gReal F₁ G).PortTyped3) (F : Sys τF EI OI)
    (SF : Simulator (EF ⊕ (EA' ⊕ EG)) (OF ⊕ (OA' ⊕ OG)) EI OI (VF.sum (WA.sum WG)) VI)
    (idle : (EH ⊕ EG) ⊕ (EA ⊕ EG)) (idleG : (EH ⊕ EG) ⊕ (EA' ⊕ EG))
    (idle' : EF ⊕ (EA' ⊕ EG))
    (hρI : ∃ o, IdleAt (gReal3 ρ G) idle o)
    (hGI : ∃ o, IdleAt (((idSim (EH ⊕ EG) (OH ⊕ OG)).tensor (S.tensor (idSim EG OG))).withSub
      (gReal3 F₁ G)) idle o)
    (hπGI : ∃ o, IdleAt ((π.tensor (idSim (EA' ⊕ EG) (OA' ⊕ OG))).withSub (gReal3 F₁ G)) idle' o)
    (hFI : ∃ o, IdleAt (SF.withSub F) idle' o)
    {bF : (ζ : Type) → Env (Strat ζ (EF ⊕ (EA' ⊕ EG)) (OF ⊕ (OA' ⊕ OG))) ζ → ℝ≥0∞}
    (hπ : RealizesSim ((π.tensor (idSim (EA' ⊕ EG) (OA' ⊕ OG))).withSub (gReal3 F₁ G)) F SF bF) :
    RealizesSim ((π.tensor (idSim (EA ⊕ EG) (OA ⊕ OG))).withSub (gReal3 ρ G)) F
      ((Simulator.ofMultiHybrid (extendFwd EF OF (S.tensor (idSim EG OG)))
        ((hS.tensor (idSim_opaque WG)).extendFwd VF)).comp SF)
      (fun ζ Z =>
        b G (RState (σ × Unit) ζ ((EH ⊕ EG) ⊕ (EA ⊕ EG)) (OF ⊕ (OA ⊕ OG)) × Bool)
            ((Open.twoPort EH OH EA OA EG OG).reduceEnv
              ((π.tensor (idSim (EA ⊕ EG) (OA ⊕ OG))).reduceEnv idle Z)) +
          bF (RState (Unit × (σS × Unit)) ζ (EF ⊕ (EA' ⊕ EG)) (OF ⊕ (OA ⊕ OG)))
            ((extendFwd EF OF (S.tensor (idSim EG OG))).reduceEnv idle' Z)) :=
  RealizesSim.modular π (S.tensor (idSim EG OG)) (hS.tensor (idSim_opaque WG)) (gReal3 ρ G)
    (gReal3 F₁ G) (gReal3_portTyped hF₁) F SF idle idleG idle' hρI hGI hπGI hFI
    (h.twoPort hF₁) hπ

/-- **Modular composition over a shared global functionality, non-programmable form.** The
theorem `modular` with the simulator of the hybrid realization of the form of one-shot
emulation: forwarding on the port of `π`, a simulator `SA` on the adversary port of `F₁`, and
forwarding on the environment's port of `G`. Both factors of the composite simulator forward
the environment's port of `G`. -/
theorem modular_fwd {σ σA τF EF OF EAF OAF : Type} {VF : PubView EF OF}
    {WAF : PubView EAF OAF} {G : Sys τG EG OG} (π : MultiHybrid σ EF OF (EH ⊕ EG) (OH ⊕ OG))
    {ρ : MultiHybrid σρ (EH ⊕ EA) (OH ⊕ OA) EG OG}
    {F₁ : MultiHybrid σF (EH ⊕ EA') (OH ⊕ OA') EG OG} {S : MultiHybrid σS EA OA EA' OA'}
    {hS : S.Opaque VA WA} {idleρ idleF : EG ⊕ EG}
    {b : {τ : Type} → Sys τ EG OG → (ζ : Type) →
      Env (Strat ζ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) ζ → ℝ≥0∞}
    (h : GSquare (VH := VH) (WG := WG) ρ F₁ S hS idleρ idleF (pinSub G) b)
    (hF₁ : (gReal F₁ G).PortTyped3) (F : Sys τF (EF ⊕ (EAF ⊕ EG)) (OF ⊕ (OAF ⊕ OG)))
    (SA : MultiHybrid σA EA' OA' EAF OAF) (hSA : SA.Opaque WA WAF)
    (idle : (EH ⊕ EG) ⊕ (EA ⊕ EG)) (idleG : (EH ⊕ EG) ⊕ (EA' ⊕ EG))
    (idle' : EF ⊕ (EA' ⊕ EG))
    (hρI : ∃ o, IdleAt (gReal3 ρ G) idle o)
    (hGI : ∃ o, IdleAt (((idSim (EH ⊕ EG) (OH ⊕ OG)).tensor (S.tensor (idSim EG OG))).withSub
      (gReal3 F₁ G)) idle o)
    (hπGI : ∃ o, IdleAt ((π.tensor (idSim (EA' ⊕ EG) (OA' ⊕ OG))).withSub (gReal3 F₁ G)) idle' o)
    (hFI : ∃ o, IdleAt (((idSim EF OF).tensor (SA.tensor (idSim EG OG))).withSub F) idle' o)
    {bF : (ζ : Type) → Env (Strat ζ (EF ⊕ (EA' ⊕ EG)) (OF ⊕ (OA' ⊕ OG))) ζ → ℝ≥0∞}
    (hπ : RealizesSim ((π.tensor (idSim (EA' ⊕ EG) (OA' ⊕ OG))).withSub (gReal3 F₁ G)) F
      (Simulator.tensor (idSim EF OF) (SA.tensor (idSim EG OG)) (idSim_opaque VF)
        (hSA.tensor (idSim_opaque WG))) bF) :
    RealizesSim ((π.tensor (idSim (EA ⊕ EG) (OA ⊕ OG))).withSub (gReal3 ρ G)) F
      ((Simulator.ofMultiHybrid (extendFwd EF OF (S.tensor (idSim EG OG)))
        ((hS.tensor (idSim_opaque WG)).extendFwd VF)).comp
        (Simulator.tensor (idSim EF OF) (SA.tensor (idSim EG OG)) (idSim_opaque VF)
          (hSA.tensor (idSim_opaque WG))))
      (fun ζ Z =>
        b G (RState (σ × Unit) ζ ((EH ⊕ EG) ⊕ (EA ⊕ EG)) (OF ⊕ (OA ⊕ OG)) × Bool)
            ((Open.twoPort EH OH EA OA EG OG).reduceEnv
              ((π.tensor (idSim (EA ⊕ EG) (OA ⊕ OG))).reduceEnv idle Z)) +
          bF (RState (Unit × (σS × Unit)) ζ (EF ⊕ (EA' ⊕ EG)) (OF ⊕ (OA ⊕ OG)))
            ((extendFwd EF OF (S.tensor (idSim EG OG))).reduceEnv idle' Z)) :=
  modular π h hF₁ F _ idle idleG idle' hρI hGI hπGI hFI hπ

end GSquare

end CatCrypt.Crypto.UCTransparent

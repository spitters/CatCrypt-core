/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCGlobalCompose
public import CatCryptCore.Crypto.UCFuelPad

/-!
# Parallel composition over a shared global functionality

Two protocols `π₁` and `π₂` over a global functionality `G` run side by side on one copy of `G`
in `gPar π₁ π₂ G`: the tensor of `π₁`, `π₂` and the forwarding simulator on the port of `G`,
over the three-port merge `G.merge3`.

If `π₁` realizes `F₁` over `G` behind `T₁` and `π₂` realizes `F₂` over `G` behind `T₂`, both
forwarding the port of `G`, then `gPar π₁ π₂ G` realizes `gPar F₁ F₂ G` behind `T₁` composed
with `T₂` (`realizes_gPar`), for protocols and functionalities of equal fuel. The proof is a
hybrid argument: `gPar π₁ π₂ G` is `π₂` beside forwarding over the protocol `π₁` over `G` with
the port of `G` exposed (`gPar_step_gParR`), and `π₁` beside forwarding over `π₂` over `G`
(`gPar_step_gParL`); each simulator commutes with the other protocol at distance `0`
(`gParR_step_comm`, `gParL_step_comm`). Each activation of the outer protocol calls the global
functionality through the protocol over `G`, one step of `G` per call, so no activation of a
multi-call hybrid is nested inside another. Padding the fuels with the counted forms of
`UCFuelPad` makes the fuels equal (`Realizes.liftFuel`, `GSquare.liftFuel`).

The sequential hybrid `gSeqHybrid` runs the left protocol and then the right protocol in one
activation and outputs both answers. For a simulator of the left protocol that post-processes
its answers by a pure computation `f`, the post-processing moves to the end of the activation,
past the step of the right protocol (`realizes_gSeq_postSim`, by
`SPComp.isPure_bind_comm_left`), and the composite is `realizes_gSeq`.

## Main definitions

* `MultiHybrid.portL`, `MultiHybrid.portR`: the ports of a tensor over a subroutine.
* `gPar`: two protocols on one copy of a global functionality.
* `gParR`, `gParL`, `gParROpen`, `gParLOpen`: one protocol beside forwarding over the other.
* `Open.mergeMid`: the merge of a port of `G` into the right port of a two-port subroutine.
* `Sys.PortTyped3R`: a system on `E₁ ⊕ (E₂ ⊕ E₃)` that answers each event on its port.
* `MultiHybrid.postSim`: the pure post-processing simulator.
* `gSeqHybrid`, `seqEnd`: both protocols in one activation, and the post-processing at its end.

## Main results

* `MultiHybrid.realizes_withSub_of_stepMap`: state maps under a multi-call hybrid.
* `gPar_step_gParR`, `gPar_step_gParL`: flattening.
* `gParR_step_comm`, `gParL_step_comm`: a simulator commuted past the other protocol.
* `realizes_gPar`: parallel composition over a shared global functionality.
* `Realizes.liftFuel`, `GSquare.liftFuel`: padding the fuels.
* `realizes_gSeq_postSim`: end delivery of a pure post-processing.
* `realizes_gSeq`: sequential composition over a shared global functionality.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## The ports of a tensor over a subroutine -/

namespace MultiHybrid

variable {σ σ' τ υ E O E' O' EG OG EG' OG' : Type}

/-- Unfolding lemma of `tensor`: the fuel is the larger fuel. -/
theorem tensor_fuel (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG') :
    (π.tensor π').fuel = max π.fuel π'.fuel := rfl

/-- Unfolding lemma of `idSim`: the fuel is `0`. -/
theorem idSim_fuel (E O : Type) : (idSim E O).fuel = 0 := rfl

/-- Unfolding lemma of `withSub`: a step is an activation with the fuel of `π`. -/
theorem withSub_step (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (p : σ × τ) (e : E) :
    (π.withSub X).step p e = π.stepFuel X π.fuel p e := rfl

/-- The left port of the tensor of `π` and `π'` over a subroutine with left port `XL`: an event
is an activation of `π` against `XL` with the fuel of the tensor, the state of `π'`
unchanged. -/
noncomputable def portL (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (XL : Sys τ EG OG) : Sys ((σ × σ') × τ) E O where
  init := ((π.init, π'.init), XL.init)
  step p e := SPComp.map (fun q => (((q.1.1, p.1.2), q.1.2), q.2))
    (π.stepFuel XL (max π.fuel π'.fuel) (p.1.1, p.2) e)

/-- The right port of the tensor of `π` and `π'` over a subroutine with right port `XR`. -/
noncomputable def portR (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (XR : Sys τ EG' OG') : Sys ((σ × σ') × τ) E' O' where
  init := ((π.init, π'.init), XR.init)
  step p e := SPComp.map (fun q => (((p.1.1, q.1.1), q.1.2), q.2))
    (π'.stepFuel XR (max π.fuel π'.fuel) (p.1.2, p.2) e)

/-- A step of the tensor over `X` on a left event is a step of its left port. -/
theorem tensor_withSub_portL (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (XL : Sys τ EG OG)
    (hX : ∀ t g, X.step t (.inl g) = SPComp.map (fun q => (q.1, .inl q.2)) (XL.step t g))
    (p : (σ × σ') × τ) (e : E) :
    ((π.tensor π').withSub X).step p (.inl e) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((portL π π' XL).step p e) := by
  obtain ⟨⟨s, s'⟩, t⟩ := p
  rw [tensor_withSub_step_inl π π' X XL hX]
  simp [portL, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- A step of the tensor over `X` on a right event is a step of its right port. -/
theorem tensor_withSub_portR (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (XR : Sys τ EG' OG')
    (hX : ∀ t g, X.step t (.inr g) = SPComp.map (fun q => (q.1, .inr q.2)) (XR.step t g))
    (p : (σ × σ') × τ) (e : E') :
    ((π.tensor π').withSub X).step p (.inr e) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((portR π π' XR).step p e) := by
  obtain ⟨⟨s, s'⟩, t⟩ := p
  rw [tensor_withSub_step_inr π π' X XR hX]
  simp [portR, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The tensor over a subroutine that answers each event on its port answers each event on its
port. -/
theorem tensor_withSub_portTyped (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') {X : Sys τ (EG ⊕ EG') (OG ⊕ OG')} (hX : X.PortTyped) :
    ((π.tensor π').withSub X).PortTyped := by
  obtain ⟨XL, XR, hL, hR⟩ := hX
  exact ⟨_, _, tensor_withSub_portL π π' X XL hL, tensor_withSub_portR π π' X XR hR⟩

/-- The left port of the forwarding simulator beside `π'` is the subroutine port on the second
component of the state. -/
theorem portL_idSim (π' : MultiHybrid σ' E' O' EG' OG') (XL : Sys τ E O) :
    portL (idSim E O) π' XL = XL.onSnd ((), π'.init) := by
  unfold portL Sys.onSnd
  congr 1
  funext p e
  obtain ⟨⟨⟨⟩, s'⟩, t⟩ := p
  simp [idSim_stepFuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The right port of `π` beside the forwarding simulator is the subroutine port on the second
component of the state. -/
theorem portR_idSim (π : MultiHybrid σ E O EG OG) (XR : Sys τ E' O') :
    portR π (idSim E' O') XR = XR.onSnd (π.init, ()) := by
  unfold portR Sys.onSnd
  congr 1
  funext p e
  obtain ⟨⟨s, ⟨⟩⟩, t⟩ := p
  simp [idSim_stepFuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- A state map `g` from `X` to `Y` that commutes with single steps commutes with the rest of an
activation of `π`. -/
theorem drive_stepMap (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (Y : Sys υ EG OG)
    (g : τ → υ)
    (hstep : ∀ t e, SPComp.map (fun p => (g p.1, p.2)) (X.step t e) = Y.step (g t) e) :
    ∀ n s d t, SPComp.map (fun p => (p.1, g p.2.1, p.2.2)) (π.drive X n s d t) =
      π.drive Y n s d (g t) := by
  intro n
  induction n with
  | zero =>
    rintro s (e | o) t
    · simp [drive, ← hstep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [drive, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    rintro s (e | o) t
    · simp [drive, ← hstep, ← ih, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [drive, SPComp.map, SPComp.pure_bind]

/-- A state map from `X` to `Y` that commutes with single steps commutes with the steps of
`π.withSub X` and `π.withSub Y`. -/
theorem withSub_stepMap (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (Y : Sys υ EG OG)
    (g : τ → υ)
    (hstep : ∀ t e, SPComp.map (fun p => (g p.1, p.2)) (X.step t e) = Y.step (g t) e)
    (p : σ × τ) (e : E) :
    SPComp.map (fun q => ((q.1.1, g q.1.2), q.2)) ((π.withSub X).step p e) =
      (π.withSub Y).step (p.1, g p.2) e := by
  simp [withSub, ← drive_stepMap π X Y g hstep, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]

/-- **State maps under a multi-call hybrid**: a state map from `X` to `Y` that preserves the
initial state and commutes with single steps gives `π.withSub X` realizing `π.withSub Y` at
distance `0`. -/
theorem realizes_withSub_of_stepMap (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (Y : Sys υ EG OG) (g : τ → υ)
    (hstep : ∀ t e, SPComp.map (fun p => (g p.1, p.2)) (X.step t e) = Y.step (g t) e)
    (hinit : g X.init = Y.init) :
    Realizes (π.withSub X) (π.withSub Y) (fun _ _ => 0) :=
  realizes_zero_of_stepMap _ _ (fun p => (p.1, g p.2)) (by simp [withSub, hinit])
    (withSub_stepMap π X Y g hstep)

end MultiHybrid

/-! ## Two protocols beside each other on one copy of the global functionality -/

section Par

variable {σ₁ σ₂ τ E₁ O₁ E₂ O₂ EG OG : Type}

/-- **Two protocols on one global functionality**: `π₁`, `π₂` and the forwarding simulator on the
port of `G`, over the three-port merge. -/
noncomputable def gPar (π₁ : MultiHybrid σ₁ E₁ O₁ EG OG) (π₂ : MultiHybrid σ₂ E₂ O₂ EG OG)
    (G : Sys τ EG OG) :
    Sys ((σ₁ × (σ₂ × Unit)) × τ) (E₁ ⊕ (E₂ ⊕ EG)) (O₁ ⊕ (O₂ ⊕ OG)) :=
  (π₁.tensor (π₂.tensor (MultiHybrid.idSim EG OG))).withSub G.merge3

/-- The protocol `π₂` beside the forwarding simulator on the port `(E₁, O₁)` and on the port of
the global functionality: the hybrid that runs `π₂` over a protocol on `(E₁ ⊕ EG, O₁ ⊕ OG)`,
with its queries to `G` merged into the port of `G` (`Open.mergeRight`). -/
noncomputable def gParR (π₂ : MultiHybrid σ₂ E₂ O₂ EG OG) (E₁ O₁ : Type) :
    MultiHybrid (Unit × (σ₂ × Unit)) (E₁ ⊕ (E₂ ⊕ EG)) (O₁ ⊕ (O₂ ⊕ OG)) (E₁ ⊕ (EG ⊕ EG))
      (O₁ ⊕ (OG ⊕ OG)) :=
  (MultiHybrid.idSim E₁ O₁).tensor (π₂.tensor (MultiHybrid.idSim EG OG))

/-- The protocol `π₁` beside the forwarding simulator on the port `(E₂ ⊕ EG, O₂ ⊕ OG)`: the
hybrid that runs `π₁` over a protocol on `(E₂ ⊕ EG, O₂ ⊕ OG)`, with its queries to `G` merged
into the port of `G` (`Open.mergeMid`). -/
noncomputable def gParL (π₁ : MultiHybrid σ₁ E₁ O₁ EG OG) (E₂ O₂ : Type) :
    MultiHybrid (σ₁ × Unit) (E₁ ⊕ (E₂ ⊕ EG)) (O₁ ⊕ (O₂ ⊕ OG)) (EG ⊕ (E₂ ⊕ EG))
      (OG ⊕ (O₂ ⊕ OG)) :=
  π₁.tensor (MultiHybrid.idSim (E₂ ⊕ EG) (O₂ ⊕ OG))

end Par

namespace Open

variable {A OA EG OG : Type}

/-- The event map of the merge of a left port of `G` into the right port of a two-port
subroutine: a left event goes to the port of `G` with the tag `true`, a right event is passed on
with the tag `false`. -/
def mergeMidEv : EG ⊕ (A ⊕ EG) → Bool × (A ⊕ EG)
  | .inl g => (true, .inr g)
  | .inr x => (false, x)

/-- The output map of the merge of a left port of `G` into the right port: an answer of `G` at
the tag `true` goes to the left port. -/
def mergeMidOut : Bool → OA ⊕ OG → OG ⊕ (OA ⊕ OG)
  | _, .inl o => .inr (.inl o)
  | true, .inr g => .inl g
  | false, .inr g => .inr (.inr g)

/-- The merge of a left port of `G` into the right port of a two-port subroutine. -/
noncomputable def mergeMid (A OA EG OG : Type) :
    Open (EG ⊕ (A ⊕ EG)) (OG ⊕ (OA ⊕ OG)) (A ⊕ EG) (OA ⊕ OG) :=
  relabel true mergeMidEv mergeMidOut

end Open

section Merge

variable {υ A OA EG OG : Type}

/-- The merge into the right port, left events: an event of `Y` on its right port. -/
theorem relabel_mergeMid_step_inl (Y : Sys υ (A ⊕ EG) (OA ⊕ OG)) (YR : Sys υ EG OG)
    (hR : ∀ t g, Y.step t (.inr g) = SPComp.map (fun q => (q.1, .inr q.2)) (YR.step t g))
    (t : υ) (g : EG) :
    (Y.relabel Open.mergeMidEv Open.mergeMidOut).step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) (YR.step t g) := by
  simp [Sys.relabel, Open.mergeMidEv, hR, Open.mergeMidOut, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]

/-- The merge into the right port, right events: the steps of `Y`. -/
theorem relabel_mergeMid_step_inr (Y : Sys υ (A ⊕ EG) (OA ⊕ OG)) (t : υ) (x : A ⊕ EG) :
    (Y.relabel Open.mergeMidEv Open.mergeMidOut).step t (.inr x) =
      SPComp.map (fun q => (q.1, .inr q.2)) (Y.step t x) := by
  simp only [Sys.relabel, Open.mergeMidEv]
  congr 1
  funext q
  rcases q with ⟨t', o | o⟩ <;> rfl

end Merge

section Merge

variable {υ A OA EG OG : Type}

/-- The merge on the right port, left events: a left event of `Y` on its left port. -/
theorem relabel_mergeRight_step_inl (Y : Sys υ (A ⊕ EG) (OA ⊕ OG)) (YL : Sys υ A OA)
    (hL : ∀ t a, Y.step t (.inl a) = SPComp.map (fun q => (q.1, .inl q.2)) (YL.step t a))
    (t : υ) (a : A) :
    (Y.relabel Open.mergeRightEv Open.mergeRightOut).step t (.inl a) =
      SPComp.map (fun q => (q.1, .inl q.2)) (YL.step t a) := by
  simp [Sys.relabel, Open.mergeRightEv, hL, Open.mergeRightOut, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]

/-- The merge on the right port, right events: both right ports are the right port of `Y`. -/
theorem relabel_mergeRight_step_inr (Y : Sys υ (A ⊕ EG) (OA ⊕ OG)) (YR : Sys υ EG OG)
    (hR : ∀ t g, Y.step t (.inr g) = SPComp.map (fun q => (q.1, .inr q.2)) (YR.step t g))
    (t : υ) (x : EG ⊕ EG) :
    (Y.relabel Open.mergeRightEv Open.mergeRightOut).step t (.inr x) =
      SPComp.map (fun q => (q.1, .inr q.2)) (YR.merge.step t x) := by
  rcases x with g | g <;>
    simp [Sys.relabel, Open.mergeRightEv, hR, Open.mergeRightOut, Sys.merge, Sys.mergeOut,
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end Merge

section Flatten

open MultiHybrid

variable {σ₁ σ₂ τ E₁ O₁ E₂ O₂ EG OG : Type}

/-- **Flattening, right.** For protocols of equal fuel, `gPar π₁ π₂ G` is `gParR π₂` over the
protocol `π₁` over `G` with the port of `G` exposed, up to the state map that moves the state of
`π₂`. -/
theorem gPar_step_gParR (π₁ : MultiHybrid σ₁ E₁ O₁ EG OG) (π₂ : MultiHybrid σ₂ E₂ O₂ EG OG)
    (hf : π₁.fuel = π₂.fuel) (G : Sys τ EG OG) (p : (σ₁ × (σ₂ × Unit)) × τ)
    (e : E₁ ⊕ (E₂ ⊕ EG)) :
    SPComp.map (fun q => ((((), q.1.1.2), ((q.1.1.1, ()), q.1.2)), q.2))
        ((gPar π₁ π₂ G).step p e) =
      ((gParR π₂ E₁ O₁).withSub ((gReal π₁ G).relabel Open.mergeRightEv
        Open.mergeRightOut)).step (((), p.1.2), ((p.1.1, ()), p.2)) e := by
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
  have hRL := relabel_mergeRight_step_inl (gReal π₁ G) _
    (tensor_withSub_portL π₁ (idSim EG OG) G.merge G h2L)
  have hRR := relabel_mergeRight_step_inr (gReal π₁ G) _
    (tensor_withSub_portR π₁ (idSim EG OG) G.merge G h2R)
  rw [portR_idSim] at hRR
  obtain ⟨⟨s₁, s₂, ⟨⟩⟩, t⟩ := p
  unfold gPar
  rcases e with e₁ | e₂ | g
  · rw [tensor_withSub_portL _ _ _ _ h3L, gParR, tensor_withSub_portL _ _ _ _ hRL, portL_idSim]
    simp [portL, tensor_fuel, idSim_fuel, hf, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_portR _ _ _ _ h3R, gParR, tensor_withSub_portR _ _ _ _ hRR]
    simp only [portR]
    rw [tensor_stepFuel_inl _ _ _ G h2L, tensor_stepFuel_inl _ _ _ _ (fun _ _ => rfl),
      stepFuel_onSnd]
    simp [tensor_fuel, idSim_fuel, hf, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_portR _ _ _ _ h3R, gParR, tensor_withSub_portR _ _ _ _ hRR]
    simp only [portR]
    rw [tensor_stepFuel_inr _ _ _ G h2R, tensor_stepFuel_inr _ _ _ _ (fun _ _ => rfl),
      idSim_stepFuel, idSim_stepFuel]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **Flattening, left.** For protocols of equal fuel, `gPar π₁ π₂ G` is `gParL π₁` over the
protocol `π₂` over `G` with the port of `G` exposed, up to the state map that moves the state of
`π₁`. -/
theorem gPar_step_gParL (π₁ : MultiHybrid σ₁ E₁ O₁ EG OG) (π₂ : MultiHybrid σ₂ E₂ O₂ EG OG)
    (hf : π₁.fuel = π₂.fuel) (G : Sys τ EG OG) (p : (σ₁ × (σ₂ × Unit)) × τ)
    (e : E₁ ⊕ (E₂ ⊕ EG)) :
    SPComp.map (fun q => (((q.1.1.1, ()), (q.1.1.2, q.1.2)), q.2)) ((gPar π₁ π₂ G).step p e) =
      ((gParL π₁ E₂ O₂).withSub ((gReal π₂ G).relabel Open.mergeMidEv
        Open.mergeMidOut)).step ((p.1.1, ()), (p.1.2, p.2)) e := by
  have h3L : ∀ t g, G.merge3.step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) (G.step t g) := fun _ _ => rfl
  have h3R : ∀ t g, G.merge3.step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) (G.merge.step t g) := by
    intro t g
    rcases g with g | g <;>
      simp [Sys.merge3, Sys.merge, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have h2R : ∀ t g, G.merge.step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) (G.step t g) := fun _ _ => rfl
  have hGR := tensor_withSub_portR π₂ (idSim EG OG) G.merge G h2R
  rw [portR_idSim] at hGR
  have hML := relabel_mergeMid_step_inl (gReal π₂ G) _ hGR
  obtain ⟨⟨s₁, s₂, ⟨⟩⟩, t⟩ := p
  unfold gPar
  rcases e with e₁ | x
  · rw [tensor_withSub_portL _ _ _ _ h3L, gParL, tensor_withSub_portL _ _ _ _ hML]
    simp only [portL]
    rw [stepFuel_onSnd]
    simp [tensor_fuel, idSim_fuel, hf, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_portR _ _ _ _ h3R, gParL,
      tensor_withSub_portR _ _ _ _ (relabel_mergeMid_step_inr (gReal π₂ G)), portR_idSim]
    simp only [portR, Sys.onSnd_step, gReal, withSub_step]
    simp [tensor_fuel, idSim_fuel, hf, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end Flatten

/-! ## The simulator commuted past the other protocol -/

section Commute

open MultiHybrid

variable {σ₁ σ₂ ρ υ E₁ O₁ E₂ O₂ E₁' O₁' E₂' O₂' EG OG : Type}

/-- **The simulator of the left protocol commuted past the right protocol.** `gParR π₂` over
the simulator `T₁` beside forwarding on the port of `G` over `Y`, and `T₁` beside forwarding over
`gParR π₂` over `Y`, up to the state map that moves the state of `T₁`. The system `Y` answers
each event on its port. -/
theorem gParR_step_comm (π₂ : MultiHybrid σ₂ E₂ O₂ EG OG) (T₁ : MultiHybrid ρ E₁ O₁ E₁' O₁')
    (Y : Sys υ (E₁' ⊕ EG) (O₁' ⊕ OG)) (hY : Y.PortTyped)
    (p : (Unit × (σ₂ × Unit)) × ((ρ × Unit) × υ)) (e : E₁ ⊕ (E₂ ⊕ EG)) :
    SPComp.map (fun q => ((q.1.2.1, (q.1.1, q.1.2.2)), q.2))
        (((gParR π₂ E₁ O₁).withSub (((T₁.tensor (idSim EG OG)).withSub Y).relabel
          Open.mergeRightEv Open.mergeRightOut)).step p e) =
      ((T₁.tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))).withSub ((gParR π₂ E₁' O₁').withSub
        (Y.relabel Open.mergeRightEv Open.mergeRightOut))).step (p.2.1, (p.1, p.2.2)) e := by
  obtain ⟨YL, YR, hL, hR⟩ := hY
  have hTL := tensor_withSub_portL T₁ (idSim EG OG) Y YL hL
  have hTR := tensor_withSub_portR T₁ (idSim EG OG) Y YR hR
  rw [portR_idSim] at hTR
  have hXL := relabel_mergeRight_step_inl _ _ hTL
  have hXR := relabel_mergeRight_step_inr _ _ hTR
  have hWL := tensor_withSub_portL (idSim E₁' O₁') (π₂.tensor (idSim EG OG)) _ YL
    (relabel_mergeRight_step_inl Y YL hL)
  rw [portL_idSim] at hWL
  have hWR := tensor_withSub_portR (idSim E₁' O₁') (π₂.tensor (idSim EG OG)) _ _
    (relabel_mergeRight_step_inr Y YR hR)
  obtain ⟨⟨⟨⟩, s₂, ⟨⟩⟩, ⟨r, ⟨⟩⟩, t⟩ := p
  unfold gParR
  rcases e with e₁ | e₂ | g
  · rw [tensor_withSub_portL _ _ _ _ hXL, portL_idSim, tensor_withSub_portL _ _ _ _ hWL]
    simp only [Sys.onSnd_step, portL]
    rw [stepFuel_onSnd]
    simp [idSim_fuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_portR _ _ _ _ hXR, tensor_withSub_portR _ _ _ _ hWR, portR_idSim]
    simp only [Sys.onSnd_step, portR]
    rw [tensor_stepFuel_inl _ _ _ _ (fun _ _ => rfl), tensor_stepFuel_inl _ _ _ _
      (fun _ _ => rfl), stepFuel_onSnd]
    simp [tensor_fuel, idSim_fuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_portR _ _ _ _ hXR, tensor_withSub_portR _ _ _ _ hWR, portR_idSim]
    simp only [Sys.onSnd_step, portR]
    rw [tensor_stepFuel_inr _ _ _ _ (fun _ _ => rfl), tensor_stepFuel_inr _ _ _ _
      (fun _ _ => rfl), idSim_stepFuel, idSim_stepFuel]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **The simulator of the right protocol commuted past the left protocol.** `gParL π₁` over
the simulator `T₂` beside forwarding on the port of `G` over `Y`, and forwarding on `(E₁, O₁)`
beside `T₂` and forwarding on the port of `G`, over `gParL π₁` over `Y`, up to the state map
that moves the state of `T₂`. The system `Y` answers each event on its port. -/
theorem gParL_step_comm (π₁ : MultiHybrid σ₁ E₁ O₁ EG OG) (T₂ : MultiHybrid ρ E₂ O₂ E₂' O₂')
    (Y : Sys υ (E₂' ⊕ EG) (O₂' ⊕ OG)) (hY : Y.PortTyped)
    (p : (σ₁ × Unit) × ((ρ × Unit) × υ)) (e : E₁ ⊕ (E₂ ⊕ EG)) :
    SPComp.map (fun q => ((((), q.1.2.1), (q.1.1, q.1.2.2)), q.2))
        (((gParL π₁ E₂ O₂).withSub (((T₂.tensor (idSim EG OG)).withSub Y).relabel
          Open.mergeMidEv Open.mergeMidOut)).step p e) =
      (((idSim E₁ O₁).tensor (T₂.tensor (idSim EG OG))).withSub ((gParL π₁ E₂' O₂').withSub
        (Y.relabel Open.mergeMidEv Open.mergeMidOut))).step (((), p.2.1), (p.1, p.2.2)) e := by
  obtain ⟨YL, YR, hL, hR⟩ := hY
  have hTL := tensor_withSub_portL T₂ (idSim EG OG) Y YL hL
  have hTR := tensor_withSub_portR T₂ (idSim EG OG) Y YR hR
  rw [portR_idSim] at hTR
  have hWL := tensor_withSub_portL π₁ (idSim (E₂' ⊕ EG) (O₂' ⊕ OG)) _ YR
    (relabel_mergeMid_step_inl Y YR hR)
  have hWR := tensor_withSub_portR π₁ (idSim (E₂' ⊕ EG) (O₂' ⊕ OG)) _ Y
    (relabel_mergeMid_step_inr Y)
  rw [portR_idSim] at hWR
  have hYL : ∀ t g, (Y.onSnd (π₁.init, ())).step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((YL.onSnd (π₁.init, ())).step t g) := by
    rintro ⟨a, t⟩ g
    simp [hL, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have hYR : ∀ t g, (Y.onSnd (π₁.init, ())).step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((YR.onSnd (π₁.init, ())).step t g) := by
    rintro ⟨a, t⟩ g
    simp [hR, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  obtain ⟨⟨s₁, ⟨⟩⟩, ⟨r, ⟨⟩⟩, t⟩ := p
  unfold gParL
  rcases e with e₁ | e₂ | g
  · rw [tensor_withSub_portL _ _ _ _ (relabel_mergeMid_step_inl _ _ hTR),
      tensor_withSub_portL _ _ _ _ hWL, portL_idSim]
    simp only [Sys.onSnd_step, portL]
    rw [stepFuel_onSnd]
    simp [idSim_fuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_portR _ _ _ _ (relabel_mergeMid_step_inr _), portR_idSim,
      tensor_withSub_portR _ _ _ _ hWR]
    simp only [Sys.onSnd_step, portR]
    rw [hTL, tensor_stepFuel_inl _ _ _ _ hYL, stepFuel_onSnd]
    simp [portL, tensor_fuel, idSim_fuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_portR _ _ _ _ (relabel_mergeMid_step_inr _), portR_idSim,
      tensor_withSub_portR _ _ _ _ hWR]
    simp only [Sys.onSnd_step, portR]
    rw [hTR, tensor_stepFuel_inr _ _ _ _ hYR, idSim_stepFuel]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end Commute

/-! ## Parallel composition of two squares over one global functionality -/

section ParCompose

open MultiHybrid

variable {σ₁ σ₂ φ₁ φ₂ ρ₁ ρ₂ τ E₁ O₁ E₂ O₂ E₁' O₁' E₂' O₂' EG OG : Type}

/-- The protocol over `G` with the port of `G` exposed answers each event on its port. -/
theorem gReal_portTyped (π : MultiHybrid σ₁ E₁ O₁ EG OG) (G : Sys τ EG OG) :
    (gReal π G).PortTyped :=
  tensor_withSub_portTyped π (idSim EG OG) (Sys.merge_portTyped G)

/-- `gParR π₂` over the merge on the right port, as an open system with the idle event
`idle`. -/
noncomputable def gParROpen (π₂ : MultiHybrid σ₂ E₂ O₂ EG OG) (E₁ O₁ : Type)
    (idle : E₁ ⊕ (EG ⊕ EG)) : Open (E₁ ⊕ (E₂ ⊕ EG)) (O₁ ⊕ (O₂ ⊕ OG)) (E₁ ⊕ EG) (O₁ ⊕ OG) :=
  (Open.ofMultiHybrid (gParR π₂ E₁ O₁) idle).comp (Open.mergeRight E₁ O₁ EG OG)

/-- `gParL π₁` over the merge into the right port, as an open system with the idle event
`idle`. -/
noncomputable def gParLOpen (π₁ : MultiHybrid σ₁ E₁ O₁ EG OG) (E₂ O₂ : Type)
    (idle : EG ⊕ (E₂ ⊕ EG)) : Open (E₁ ⊕ (E₂ ⊕ EG)) (O₁ ⊕ (O₂ ⊕ OG)) (E₂ ⊕ EG) (O₂ ⊕ OG) :=
  (Open.ofMultiHybrid (gParL π₁ E₂ O₂) idle).comp (Open.mergeMid E₂ O₂ EG OG)

/-- **Parallel composition over a shared global functionality.** Let `π₁` realize `F₁` over
`G` behind `T₁` beside forwarding on the port of `G` with bound `b₁`, and `π₂` realize `F₂`
behind `T₂` beside forwarding with bound `b₂`. For protocols and functionalities of equal fuel,
`π₁` and `π₂` on one copy of `G` realize `F₁` and `F₂` on one copy of `G` behind `T₁` beside
forwarding, composed with forwarding beside `T₂` beside forwarding. The bound is `b₁` at the
environment reduced through `π₂` and the merge, plus `b₂` at the environment reduced through
`T₁`, `F₁` and the merge. The systems involved are idle at the idle events of the reductions. -/
theorem realizes_gPar {π₁ : MultiHybrid σ₁ E₁ O₁ EG OG} {π₂ : MultiHybrid σ₂ E₂ O₂ EG OG}
    {F₁ : MultiHybrid φ₁ E₁' O₁' EG OG} {F₂ : MultiHybrid φ₂ E₂' O₂' EG OG}
    {T₁ : MultiHybrid ρ₁ E₁ O₁ E₁' O₁'} {T₂ : MultiHybrid ρ₂ E₂ O₂ E₂' O₂'} {G : Sys τ EG OG}
    (hπ : π₁.fuel = π₂.fuel) (hF₁ : F₁.fuel = π₂.fuel) (hF : F₁.fuel = F₂.fuel)
    (idleR : E₁ ⊕ (EG ⊕ EG)) (idleL : EG ⊕ (E₂ ⊕ EG)) (idleT : E₁' ⊕ (E₂ ⊕ EG))
    (hR₁ : ∃ o, IdleAt ((gReal π₁ G).relabel Open.mergeRightEv Open.mergeRightOut) idleR o)
    (hR₂ : ∃ o, IdleAt (((T₁.tensor (idSim EG OG)).withSub (gReal F₁ G)).relabel
      Open.mergeRightEv Open.mergeRightOut) idleR o)
    (hL₁ : ∃ o, IdleAt ((gReal π₂ G).relabel Open.mergeMidEv Open.mergeMidOut) idleL o)
    (hL₂ : ∃ o, IdleAt (((T₂.tensor (idSim EG OG)).withSub (gReal F₂ G)).relabel
      Open.mergeMidEv Open.mergeMidOut) idleL o)
    (hT₁ : ∃ o, IdleAt ((gParLOpen F₁ E₂ O₂ idleL).withSub (gReal π₂ G)) idleT o)
    (hT₂ : ∃ o, IdleAt ((gParLOpen F₁ E₂ O₂ idleL).withSub
      ((T₂.tensor (idSim EG OG)).withSub (gReal F₂ G))) idleT o)
    {b₁ : (ζ : Type) → Env (Strat ζ (E₁ ⊕ EG) (O₁ ⊕ OG)) ζ → ℝ≥0∞}
    {b₂ : (ζ : Type) → Env (Strat ζ (E₂ ⊕ EG) (O₂ ⊕ OG)) ζ → ℝ≥0∞}
    (h₁ : Realizes (gReal π₁ G) ((T₁.tensor (idSim EG OG)).withSub (gReal F₁ G)) b₁)
    (h₂ : Realizes (gReal π₂ G) ((T₂.tensor (idSim EG OG)).withSub (gReal F₂ G)) b₂) :
    Realizes (gPar π₁ π₂ G)
      ((T₁.tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))).withSub
        (((idSim E₁' O₁').tensor (T₂.tensor (idSim EG OG))).withSub (gPar F₁ F₂ G)))
      (fun _ Z => b₁ _ ((gParROpen π₂ E₁ O₁ idleR).reduceEnv Z) +
        b₂ _ ((gParLOpen F₁ E₂ O₂ idleL).reduceEnv
          ((Open.ofMultiHybrid (T₁.tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))) idleT).reduceEnv Z))) := by
  -- the real system as `gParR π₂` over `π₁`
  have r₀ : Realizes (gPar π₁ π₂ G) ((gParROpen π₂ E₁ O₁ idleR).withSub (gReal π₁ G))
      (fun _ _ => 0) :=
    realizes_zero_of_stepMap _ _ (fun p => (((), p.1.2), ((p.1.1, ()), p.2))) rfl
      (gPar_step_gParR π₁ π₂ hπ G)
  -- the first square under `gParR π₂`
  have r₁ := (gParROpen π₂ E₁ O₁ idleR).realizes_withSub ⟨trivial, hR₁⟩ ⟨trivial, hR₂⟩ h₁
  -- `T₁` commuted past `π₂`
  have r₂ : Realizes ((gParROpen π₂ E₁ O₁ idleR).withSub
        ((T₁.tensor (idSim EG OG)).withSub (gReal F₁ G)))
      ((T₁.tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))).withSub ((gParR π₂ E₁' O₁').withSub
        ((gReal F₁ G).relabel Open.mergeRightEv Open.mergeRightOut))) (fun _ _ => 0) :=
    realizes_zero_of_stepMap _ _ (fun p => (p.2.1, (p.1, p.2.2))) rfl
      (gParR_step_comm π₂ T₁ _ (gReal_portTyped F₁ G))
  -- `F₁` beside `π₂` from the right form to the left form, under `T₁`
  have hRL : ∀ (q : (Unit × (σ₂ × Unit)) × ((φ₁ × Unit) × τ)) (e : E₁' ⊕ (E₂ ⊕ EG)),
      SPComp.map (fun p => ((p.1.2.1, (p.1.1.2, p.1.2.2)), p.2))
        (((gParR π₂ E₁' O₁').withSub
          ((gReal F₁ G).relabel Open.mergeRightEv Open.mergeRightOut)).step q e) =
      ((gParL F₁ E₂ O₂).withSub ((gReal π₂ G).relabel Open.mergeMidEv Open.mergeMidOut)).step
        (q.2.1, (q.1.2, q.2.2)) e := by
    rintro ⟨⟨⟨⟩, s₂, ⟨⟩⟩, ⟨s₁, ⟨⟩⟩, t⟩ e
    have hA := gPar_step_gParR F₁ π₂ hF₁ G ((s₁, (s₂, ())), t) e
    have hB := gPar_step_gParL F₁ π₂ hF₁ G ((s₁, (s₂, ())), t) e
    dsimp only at hA hB
    rw [← hA, ← hB]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have r₃ := realizes_withSub_of_stepMap (T₁.tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))) _ _
    (fun q : (Unit × (σ₂ × Unit)) × ((φ₁ × Unit) × τ) => (q.2.1, (q.1.2, q.2.2))) hRL rfl
  -- the second square under `gParL F₁` and `T₁`
  have r₄ := (Open.ofMultiHybrid (T₁.tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))) idleT).realizes_withSub
    hT₁ hT₂ ((gParLOpen F₁ E₂ O₂ idleL).realizes_withSub ⟨trivial, hL₁⟩ ⟨trivial, hL₂⟩ h₂)
  -- `T₂` commuted past `F₁`, under `T₁`
  have r₅ := realizes_withSub_of_stepMap (T₁.tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))) _ _
    (fun p : (φ₁ × Unit) × ((ρ₂ × Unit) × ((φ₂ × Unit) × τ)) => (((), p.2.1), (p.1, p.2.2)))
    (gParL_step_comm F₁ T₂ _ (gReal_portTyped F₂ G)) rfl
  -- the ideal system from the left form, under both simulators
  have hLP : ∀ (q : (φ₁ × Unit) × ((φ₂ × Unit) × τ)) (e : E₁' ⊕ (E₂' ⊕ EG)),
      SPComp.map (fun p => (((p.1.1.1, p.1.2.1), p.1.2.2), p.2))
        (((gParL F₁ E₂' O₂').withSub
          ((gReal F₂ G).relabel Open.mergeMidEv Open.mergeMidOut)).step q e) =
      (gPar F₁ F₂ G).step ((q.1.1, q.2.1), q.2.2) e := by
    rintro ⟨⟨s₁, ⟨⟩⟩, ⟨s₂, ⟨⟩⟩, t⟩ e
    have hB := gPar_step_gParL F₁ F₂ hF G ((s₁, (s₂, ())), t) e
    dsimp only at hB
    rw [← hB]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have r₆ := realizes_withSub_of_stepMap (T₁.tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))) _ _
    (fun p : (Unit × (ρ₂ × Unit)) × ((φ₁ × Unit) × ((φ₂ × Unit) × τ)) =>
      (p.1, ((p.2.1.1, p.2.2.1), p.2.2.2)))
    (withSub_stepMap ((idSim E₁' O₁').tensor (T₂.tensor (idSim EG OG))) _ _
      (fun q : (φ₁ × Unit) × ((φ₂ × Unit) × τ) => ((q.1.1, q.2.1), q.2.2)) hLP) rfl
  intro ζ Z
  refine le_of_le_of_eq
    ((((((r₀.trans r₁).trans r₂).trans r₃).trans r₄).trans r₅).trans r₆ ζ Z) ?_
  simp only [add_zero, zero_add]

end ParCompose

/-! ## Padding the fuel of a protocol over a global functionality -/

section LiftFuel

open MultiHybrid

variable {σ φ ρ τ E O E' O' EG OG : Type}

/-- The protocol over `G` in counted form with fuel `n` takes the steps of the protocol, up to
the counter, for `π.fuel ≤ n`. -/
theorem gReal_counted_step (π : MultiHybrid σ E O EG OG) {n : ℕ} (hn : π.fuel ≤ n)
    (G : Sys τ EG OG) (p : ((σ × ℕ) × Unit) × τ) (e : E ⊕ EG) :
    SPComp.map (fun q => (((q.1.1.1.1, ()), q.1.2), q.2)) ((gReal (π.counted n) G).step p e) =
      (gReal π G).step ((p.1.1.1, ()), p.2) e := by
  have h2L : ∀ t g, G.merge.step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) (G.step t g) := fun _ _ => rfl
  have h2R : ∀ t g, G.merge.step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) (G.step t g) := fun _ _ => rfl
  obtain ⟨⟨⟨s, k⟩, ⟨⟩⟩, t⟩ := p
  unfold gReal
  rcases e with e | g
  · rw [tensor_withSub_portL _ _ _ _ h2L, tensor_withSub_portL _ _ _ _ h2L]
    have hc := counted_withSub_step π hn G ((s, k), t) e
    rw [withSub_step, withSub_step] at hc
    simp only [portL, idSim_fuel, Nat.max_zero, ← hc]
    simp [counted, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_portR _ _ _ _ h2R, tensor_withSub_portR _ _ _ _ h2R, portR_idSim,
      portR_idSim]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The protocol over `G` in counted form and the protocol realize each other at distance
`0`. -/
theorem realizes_gReal_counted (π : MultiHybrid σ E O EG OG) {n : ℕ} (hn : π.fuel ≤ n)
    (G : Sys τ EG OG) : Realizes (gReal (π.counted n) G) (gReal π G) (fun _ _ => 0) :=
  realizes_zero_of_stepMap _ _ (fun p => ((p.1.1.1, ()), p.2)) rfl
    (gReal_counted_step π hn G)

/-- **Padding the fuel.** A realization of `T` beside forwarding over `F` over `G` by `π` over
`G` holds, with the same bound, for the counted forms of `π` and `F` with fuels `n` and `m` at
least their fuels. -/
theorem Realizes.liftFuel {π : MultiHybrid σ E O EG OG} {F : MultiHybrid φ E' O' EG OG}
    {T : MultiHybrid ρ E O E' O'} {G : Sys τ EG OG} {n m : ℕ} (hn : π.fuel ≤ n)
    (hm : F.fuel ≤ m) {b : (ζ : Type) → Env (Strat ζ (E ⊕ EG) (O ⊕ OG)) ζ → ℝ≥0∞}
    (h : Realizes (gReal π G) ((T.tensor (idSim EG OG)).withSub (gReal F G)) b) :
    Realizes (gReal (π.counted n) G)
      ((T.tensor (idSim EG OG)).withSub (gReal (F.counted m) G)) b := by
  have hF := realizes_withSub_of_stepMap (T.tensor (idSim EG OG)) _ _
    (fun p : ((φ × ℕ) × Unit) × τ => ((p.1.1.1, ()), p.2)) (gReal_counted_step F hm G) rfl
  intro ζ Z
  refine le_of_le_of_eq
    ((((realizes_gReal_counted π hn G).trans h).trans fun ζ => (hF ζ).symm) ζ Z) ?_
  simp only [add_zero, zero_add]

/-- **Padding the fuel of a square.** A square over `G` pinned to `G` gives the square of the
counted forms of the protocol and the functionality with fuels at least their fuels, with the
same simulator and the bound at `G`. -/
theorem GSquare.liftFuel {σS τG EH OH EA OA EA' OA' : Type} {VH : PubView EH OH}
    {VA : PubView EA OA} {WA : PubView EA' OA'} {WG : PubView EG OG} {G : Sys τG EG OG}
    {π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG}
    {F : MultiHybrid φ (EH ⊕ EA') (OH ⊕ OA') EG OG} {S : MultiHybrid σS EA OA EA' OA'}
    {hS : S.Opaque VA WA} {idleπ idleF : EG ⊕ EG}
    {b : {τ : Type} → Sys τ EG OG → (ζ : Type) →
      Env (Strat ζ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) ζ → ℝ≥0∞}
    (h : GSquare (VH := VH) (WG := WG) π F S hS idleπ idleF (pinSub G) b) {n m : ℕ}
    (hn : π.fuel ≤ n) (hm : F.fuel ≤ m) (idleπ' idleF' : EG ⊕ EG) :
    GSquare (VH := VH) (WG := WG) (π.counted n) (F.counted m) S hS idleπ' idleF' (pinSub G)
      (fun _ => b G) :=
  GSquare.ofRealizes idleπ' idleF' (Realizes.liftFuel hn hm h.realizes_gReal)

end LiftFuel

/-! ## Systems on a right-nested three-port interface -/

namespace Sys

variable {υ E₁ O₁ E₂ O₂ E₃ O₃ : Type}

/-- The system `Y` on the interface `E₁ ⊕ (E₂ ⊕ E₃)` answers every event on the port of the
event: its steps on each port are those of a system on that port with the state of `Y`. -/
def PortTyped3R (Y : Sys υ (E₁ ⊕ (E₂ ⊕ E₃)) (O₁ ⊕ (O₂ ⊕ O₃))) : Prop :=
  ∃ (Y₁ : Sys υ E₁ O₁) (Y₂ : Sys υ E₂ O₂) (Y₃ : Sys υ E₃ O₃),
    (∀ t e, Y.step t (.inl e) = SPComp.map (fun q => (q.1, .inl q.2)) (Y₁.step t e)) ∧
    (∀ t e, Y.step t (.inr (.inl e)) =
      SPComp.map (fun q => (q.1, .inr (.inl q.2))) (Y₂.step t e)) ∧
    (∀ t e, Y.step t (.inr (.inr e)) =
      SPComp.map (fun q => (q.1, .inr (.inr q.2))) (Y₃.step t e))

/-- The three-port merge answers every event on the port of the event. -/
theorem merge3_portTyped3R {τ EG OG : Type} (G : Sys τ EG OG) : G.merge3.PortTyped3R :=
  ⟨G, G, G, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end Sys

namespace MultiHybrid

variable {σ σ' σ'' τ E O E' O' E'' O'' EG OG EG' OG' EG'' OG'' : Type}

/-- The tensor of three multi-call hybrids over a subroutine that answers each event on its port
answers each event on its port. -/
theorem tensor_tensor_withSub_portTyped3R (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') (π'' : MultiHybrid σ'' E'' O'' EG'' OG'')
    {X : Sys τ (EG ⊕ (EG' ⊕ EG'')) (OG ⊕ (OG' ⊕ OG''))} (hX : X.PortTyped3R) :
    ((π.tensor (π'.tensor π'')).withSub X).PortTyped3R := by
  obtain ⟨X₁, X₂, X₃, h₁, h₂, h₃⟩ := hX
  have hR : ∀ t x, X.step t (.inr x) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((Sys.copair X.init X₂ X₃).step t x) := by
    rintro t (e | e) <;>
      simp [Sys.copair, h₂, h₃, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  refine ⟨portL π (π'.tensor π'') X₁,
    ⟨((π.init, (π'.init, π''.init)), X.init), fun p e =>
      SPComp.map (fun q => (((p.1.1, (q.1.1, p.1.2.2)), q.1.2), q.2))
        (π'.stepFuel X₂ (max π.fuel (π'.tensor π'').fuel) (p.1.2.1, p.2) e)⟩,
    ⟨((π.init, (π'.init, π''.init)), X.init), fun p e =>
      SPComp.map (fun q => (((p.1.1, (p.1.2.1, q.1.1)), q.1.2), q.2))
        (π''.stepFuel X₃ (max π.fuel (π'.tensor π'').fuel) (p.1.2.2, p.2) e)⟩,
    tensor_withSub_portL _ _ _ _ h₁, ?_, ?_⟩
  · rintro ⟨⟨s, s', s''⟩, t⟩ e
    rw [tensor_withSub_portR _ _ _ _ hR]
    simp only [portR]
    rw [tensor_stepFuel_inl _ _ _ X₂ (fun _ _ => rfl)]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rintro ⟨⟨s, s', s''⟩, t⟩ e
    rw [tensor_withSub_portR _ _ _ _ hR]
    simp only [portR]
    rw [tensor_stepFuel_inr _ _ _ X₃ (fun _ _ => rfl)]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **The pure post-processing simulator**: an event is passed on, and the answer is mapped by
`f`, in one call per activation. -/
noncomputable def postSim (E : Type) {O O' : Type} (f : O' → SPComp O)
    (hf : ∀ o, SPComp.NoFail (f o)) : MultiHybrid Unit E O E O' where
  init := ()
  fuel := 0
  start _ e := SPComp.pure ((), .inl e)
  resume _ o := SPComp.map (fun o' => ((), .inr o')) (f o)
  finish _ o := SPComp.map (fun o' => ((), o')) (f o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ o := Assumptions.SPComp.bind_noFail (hf o) fun _ => SPComp.pure_noFail _
  finish_noFail _ o := Assumptions.SPComp.bind_noFail (hf o) fun _ => SPComp.pure_noFail _

/-- An activation of the post-processing simulator, with any fuel, is one step of the
subroutine followed by `f`. -/
theorem postSim_stepFuel {E O O' : Type} (f : O' → SPComp O) (hf : ∀ o, SPComp.NoFail (f o))
    (X : Sys τ E O') (n : ℕ) (u : Unit) (t : τ) (e : E) :
    (postSim E f hf).stepFuel X n (u, t) e =
      SPComp.bind (X.step t e) fun q => SPComp.map (fun o => (((), q.1), o)) (f q.2) := by
  cases n <;> simp [stepFuel, postSim, drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

/-! ## Both protocols in one activation, with both results delivered at the end -/

section Seq

open MultiHybrid

variable {υ E₁ O₁ O₁' E₂ O₂ EG OG : Type}

/-- **The sequential hybrid over two protocols on one global functionality**: an event
`(x₁, x₂)` calls the left protocol on `x₁`, then the right protocol on `x₂`, and outputs both
answers; an event on the port of `G` is passed on. The state holds `x₂` and then the answer of
the left protocol during an activation. Answers on unexpected ports give the default output. -/
noncomputable def gSeqHybrid (E₁ E₂ O₁ O₂ EG OG : Type) [Inhabited O₁] [Inhabited O₂] :
    MultiHybrid (Option (E₂ ⊕ O₁)) ((E₁ × E₂) ⊕ EG) ((O₁ × O₂) ⊕ OG) (E₁ ⊕ (E₂ ⊕ EG))
      (O₁ ⊕ (O₂ ⊕ OG)) where
  init := none
  fuel := 1
  start _ e := match e with
    | .inl x => SPComp.pure (some (.inl x.2), .inl (.inl x.1))
    | .inr g => SPComp.pure (none, .inl (.inr (.inr g)))
  resume s o := match s, o with
    | some (.inl x₂), .inl o₁ => SPComp.pure (some (.inr o₁), .inl (.inr (.inl x₂)))
    | _, .inr (.inr g) => SPComp.pure (none, .inr (.inr g))
    | _, _ => SPComp.pure (none, .inr (.inl default))
  finish s o := match s, o with
    | some (.inr o₁), .inr (.inl o₂) => SPComp.pure (none, .inl (o₁, o₂))
    | _, .inr (.inr g) => SPComp.pure (none, .inr g)
    | _, _ => SPComp.pure (none, .inl default)
  start_noFail _ e := by rcases e with x | g <;> exact SPComp.pure_noFail _
  resume_noFail s o := by split <;> exact SPComp.pure_noFail _
  finish_noFail s o := by split <;> exact SPComp.pure_noFail _

/-- The post-processing at the end of a sequential activation: `f` on the answer of the left
protocol, the answer of `G` unchanged. -/
noncomputable def seqEnd (O₂ OG : Type) (f : O₁' → SPComp O₁) :
    (O₁' × O₂) ⊕ OG → SPComp ((O₁ × O₂) ⊕ OG) :=
  Sum.elim (fun p => SPComp.map (fun o => .inl (o, p.2)) (f p.1)) fun g => SPComp.pure (.inr g)

/-- The post-processing at the end never fails when `f` never fails. -/
theorem seqEnd_noFail {f : O₁' → SPComp O₁} (hf : ∀ o, SPComp.NoFail (f o))
    (r : (O₁' × O₂) ⊕ OG) : SPComp.NoFail (seqEnd O₂ OG f r) := by
  rcases r with p | g
  · simp only [seqEnd, Sum.elim_inl, SPComp.map]
    exact Assumptions.SPComp.bind_noFail (hf _) fun _ => SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

/-- **End delivery.** For a pure post-processing `f`, the sequential hybrid over `f` on the left
port beside forwarding over `Y`, and the post-processing by `f` at the end over the sequential
hybrid over `Y`, take the same steps up to the state of the sequential hybrid, which is empty
between activations. The system `Y` answers each event on its port. -/
theorem gSeq_postSim_step [Inhabited O₁] [Inhabited O₁'] [Inhabited O₂]
    (f : O₁' → SPComp O₁) (hf : ∀ o, SPComp.NoFail (f o)) (hp : ∀ o, SPComp.IsPure (f o))
    (Y : Sys υ (E₁ ⊕ (E₂ ⊕ EG)) (O₁' ⊕ (O₂ ⊕ OG))) (hY : Y.PortTyped3R)
    (p : Option (E₂ ⊕ O₁) × ((Unit × Unit) × υ)) (e : (E₁ × E₂) ⊕ EG) :
    SPComp.map (fun q => (((), (none, q.1.2.2)), q.2))
        (((gSeqHybrid E₁ E₂ O₁ O₂ EG OG).withSub
          (((postSim E₁ f hf).tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))).withSub Y)).step p e) =
      ((postSim ((E₁ × E₂) ⊕ EG) (seqEnd O₂ OG f) (seqEnd_noFail hf)).withSub
        ((gSeqHybrid E₁ E₂ O₁' O₂ EG OG).withSub Y)).step ((), (none, p.2.2)) e := by
  obtain ⟨Y₁, Y₂, Y₃, h₁, h₂, h₃⟩ := hY
  have hR : ∀ t x, Y.step t (.inr x) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((Sys.copair Y.init Y₂ Y₃).step t x) := by
    rintro t (x | g) <;>
      simp [Sys.copair, h₂, h₃, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have hXL := tensor_withSub_portL (postSim E₁ f hf) (idSim (E₂ ⊕ EG) (O₂ ⊕ OG)) Y Y₁ h₁
  have hXR := tensor_withSub_portR (postSim E₁ f hf) (idSim (E₂ ⊕ EG) (O₂ ⊕ OG)) Y _ hR
  rw [portR_idSim] at hXR
  obtain ⟨s, ⟨⟨⟩, ⟨⟩⟩, t⟩ := p
  rw [withSub_step (gSeqHybrid E₁ E₂ O₁ O₂ EG OG), withSub_step (postSim _ _ _),
    postSim_stepFuel, withSub_step (gSeqHybrid E₁ E₂ O₁' O₂ EG OG)]
  rcases e with ⟨x₁, x₂⟩ | g
  · simp only [stepFuel, drive, gSeqHybrid, hXL, hXR, h₁, h₂, portL, Sys.onSnd_step,
      Sys.copair, seqEnd, Sum.elim_inl, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    simp only [postSim, idSim_fuel, max_self, drive, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
    exact congrArg (SPComp.bind _) (funext fun a => SPComp.isPure_bind_comm_left _ _ _ (hp a.2))
  · simp only [stepFuel, drive, gSeqHybrid, hXR, h₃, Sys.onSnd_step, Sys.copair, seqEnd,
      Sum.elim_inr, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **End delivery**, as a realization at distance `0`: for a pure post-processing `f`, the
sequential hybrid over `f` on the left port beside forwarding over `Y` realizes the
post-processing by `f` at the end over the sequential hybrid over `Y`. -/
theorem realizes_gSeq_postSim [Inhabited O₁] [Inhabited O₁'] [Inhabited O₂]
    (f : O₁' → SPComp O₁) (hf : ∀ o, SPComp.NoFail (f o)) (hp : ∀ o, SPComp.IsPure (f o))
    (Y : Sys υ (E₁ ⊕ (E₂ ⊕ EG)) (O₁' ⊕ (O₂ ⊕ OG))) (hY : Y.PortTyped3R) :
    Realizes ((gSeqHybrid E₁ E₂ O₁ O₂ EG OG).withSub
        (((postSim E₁ f hf).tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))).withSub Y))
      ((postSim ((E₁ × E₂) ⊕ EG) (seqEnd O₂ OG f) (seqEnd_noFail hf)).withSub
        ((gSeqHybrid E₁ E₂ O₁' O₂ EG OG).withSub Y)) (fun _ _ => 0) :=
  realizes_zero_of_stepMap _ _
    (fun p : Option (E₂ ⊕ O₁) × ((Unit × Unit) × υ) =>
      ((), ((none : Option (E₂ ⊕ O₁')), p.2.2))) rfl
    (gSeq_postSim_step f hf hp Y hY)

end Seq

/-! ## Sequential composition over one global functionality -/

section SeqCompose

open MultiHybrid

variable {σ₁ σ₂ φ₁ φ₂ ρ₂ τ E₁ O₁ O₁' E₂ O₂ E₂' O₂' EG OG : Type}

/-- Two protocols on one global functionality answer every event on the port of the event. -/
theorem gPar_portTyped3R (π₁ : MultiHybrid σ₁ E₁ O₁ EG OG) (π₂ : MultiHybrid σ₂ E₂ O₂ EG OG)
    (G : Sys τ EG OG) : (gPar π₁ π₂ G).PortTyped3R :=
  tensor_tensor_withSub_portTyped3R π₁ π₂ (idSim EG OG) (Sys.merge3_portTyped3R G)

/-- **Sequential composition over a shared global functionality, both results delivered at the
end.** Let `π₁` realize `F₁` over `G` behind the pure post-processing `f` beside forwarding on the
port of `G`, and `π₂` realize `F₂` behind `T₂` beside forwarding. For protocols and
functionalities of equal fuel, the sequential hybrid over `π₁` and `π₂` on one copy of `G`
realizes the post-processing by `f` at the end over the sequential hybrid over `F₁` and `F₂` on
one copy of `G` behind forwarding beside `T₂` beside forwarding. The bound is that of
`realizes_gPar` at the environment reduced through the sequential hybrid. -/
theorem realizes_gSeq [Inhabited O₁] [Inhabited O₁'] [Inhabited O₂]
    {π₁ : MultiHybrid σ₁ E₁ O₁ EG OG} {π₂ : MultiHybrid σ₂ E₂ O₂ EG OG}
    {F₁ : MultiHybrid φ₁ E₁ O₁' EG OG} {F₂ : MultiHybrid φ₂ E₂' O₂' EG OG}
    {T₂ : MultiHybrid ρ₂ E₂ O₂ E₂' O₂'} {G : Sys τ EG OG}
    (f : O₁' → SPComp O₁) (hf : ∀ o, SPComp.NoFail (f o)) (hp : ∀ o, SPComp.IsPure (f o))
    (hπ : π₁.fuel = π₂.fuel) (hF₁ : F₁.fuel = π₂.fuel) (hF : F₁.fuel = F₂.fuel)
    (idleR : E₁ ⊕ (EG ⊕ EG)) (idleL : EG ⊕ (E₂ ⊕ EG)) (idleT : E₁ ⊕ (E₂ ⊕ EG))
    (idleS : E₁ ⊕ (E₂ ⊕ EG))
    (hR₁ : ∃ o, IdleAt ((gReal π₁ G).relabel Open.mergeRightEv Open.mergeRightOut) idleR o)
    (hR₂ : ∃ o, IdleAt ((((postSim E₁ f hf).tensor (idSim EG OG)).withSub (gReal F₁ G)).relabel
      Open.mergeRightEv Open.mergeRightOut) idleR o)
    (hL₁ : ∃ o, IdleAt ((gReal π₂ G).relabel Open.mergeMidEv Open.mergeMidOut) idleL o)
    (hL₂ : ∃ o, IdleAt (((T₂.tensor (idSim EG OG)).withSub (gReal F₂ G)).relabel
      Open.mergeMidEv Open.mergeMidOut) idleL o)
    (hT₁ : ∃ o, IdleAt ((gParLOpen F₁ E₂ O₂ idleL).withSub (gReal π₂ G)) idleT o)
    (hT₂ : ∃ o, IdleAt ((gParLOpen F₁ E₂ O₂ idleL).withSub
      ((T₂.tensor (idSim EG OG)).withSub (gReal F₂ G))) idleT o)
    (hS₁ : ∃ o, IdleAt (gPar π₁ π₂ G) idleS o)
    (hS₂ : ∃ o, IdleAt (((postSim E₁ f hf).tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG))).withSub
      (((idSim E₁ O₁').tensor (T₂.tensor (idSim EG OG))).withSub (gPar F₁ F₂ G))) idleS o)
    {b₁ : (ζ : Type) → Env (Strat ζ (E₁ ⊕ EG) (O₁ ⊕ OG)) ζ → ℝ≥0∞}
    {b₂ : (ζ : Type) → Env (Strat ζ (E₂ ⊕ EG) (O₂ ⊕ OG)) ζ → ℝ≥0∞}
    (h₁ : Realizes (gReal π₁ G) (((postSim E₁ f hf).tensor (idSim EG OG)).withSub (gReal F₁ G))
      b₁)
    (h₂ : Realizes (gReal π₂ G) ((T₂.tensor (idSim EG OG)).withSub (gReal F₂ G)) b₂) :
    Realizes ((gSeqHybrid E₁ E₂ O₁ O₂ EG OG).withSub (gPar π₁ π₂ G))
      ((postSim ((E₁ × E₂) ⊕ EG) (seqEnd O₂ OG f) (seqEnd_noFail hf)).withSub
        ((gSeqHybrid E₁ E₂ O₁' O₂ EG OG).withSub
          (((idSim E₁ O₁').tensor (T₂.tensor (idSim EG OG))).withSub (gPar F₁ F₂ G))))
      (fun _ Z =>
        b₁ _ ((gParROpen π₂ E₁ O₁ idleR).reduceEnv
          ((Open.ofMultiHybrid (gSeqHybrid E₁ E₂ O₁ O₂ EG OG) idleS).reduceEnv Z)) +
        b₂ _ ((gParLOpen F₁ E₂ O₂ idleL).reduceEnv
          ((Open.ofMultiHybrid ((postSim E₁ f hf).tensor (idSim (E₂ ⊕ EG) (O₂ ⊕ OG)))
            idleT).reduceEnv
              ((Open.ofMultiHybrid (gSeqHybrid E₁ E₂ O₁ O₂ EG OG) idleS).reduceEnv Z)))) := by
  have hP := realizes_gPar hπ hF₁ hF idleR idleL idleT hR₁ hR₂ hL₁ hL₂ hT₁ hT₂ h₁ h₂
  have r₁ := (Open.ofMultiHybrid (gSeqHybrid E₁ E₂ O₁ O₂ EG OG) idleS).realizes_withSub hS₁ hS₂ hP
  have r₂ := realizes_gSeq_postSim f hf hp _
    (tensor_tensor_withSub_portTyped3R (idSim E₁ O₁') T₂ (idSim EG OG) (gPar_portTyped3R F₁ F₂ G))
  intro ζ Z
  refine le_of_le_of_eq ((r₁.trans r₂) ζ Z) ?_
  simp only [add_zero]

end SeqCompose

end CatCrypt.Crypto.UCTransparent

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCGlobal

/-!
# Squares over a shared global functionality

A protocol `π` that uses a global functionality on the interface `(EG, OG)` is a multi-call
hybrid with that subroutine interface. Its form with the port of the global functionality
exposed to the environment is the open system `gOpen π idle`: the tensor of `π` with the
forwarding simulator on `(EG, OG)`, over the merge `Open.merge EG OG`, which serves both ports
with one copy of the global functionality. Over a global functionality `G` it is the system
`gReal π G`.

A square over the global functionality (`GSquare`) has top `gOpen π`, bottom `gOpen F`, the
identity simulator on `(EG, OG)` as left edge and the simulator `gSim S` on the right: the
forwarding simulator on the honest port, the simulator `S` on the adversary port and the
forwarding simulator on the port of the global functionality (the simulator of one-shot GUC
emulation, which has no access to the state of the global functionality). The admissibility
`pinSub G` pins the subroutine to `G`. Every protocol gives an identity square, at bound `0`,
with the forwarding simulator on the adversary port (`GSquare.refl`).

A simulator `S` with a port of its own on the global functionality is combined with the
environment's port by the router `gRouter`, a multi-call hybrid with one call per activation
that sends the simulator's queries and the environment's queries to the single port of the
global functionality and returns each answer to the port of its query (`gSimB`, `GSquareB`). The
router forwards the environment's port in the sense of `MultiHybrid.ForwardsEnv`, which allows
other queries on the forwarded port; the forwarding of `MultiHybrid.Forwards` is the case of the
identity state map (`MultiHybrid.Forwards.forwardsEnv`).

## Main definitions

* `gOpen`, `gReal`: the protocol with the port of the global functionality exposed.
* `pinSub`: the admissibility of the subroutine `G` alone.
* `gSimHybrid`, `gSim`: the simulator on the adversary port, forwarding the other ports.
* `GSquare`: the square over a global functionality.
* `MultiHybrid.ForwardsEnv`: forwarding of the environment's queries on a shared port.
* `gRouter`, `gSimB`, `GSquareB`: the simulator with its own port on the global functionality.

## Main results

* `gSimHybrid_opaque`, `gRouter_opaque`: opacity of the simulators.
* `GSquare.realizes_gReal`, `GSquare.ofRealizes`: a square pinned to `G` is the realization
  between `gReal π G` and `gSim S` over `gReal F G`.
* `GSquare.refl`: the identity square at bound `0`.
* `gSimHybrid_forwardsEnv`, `gRouter_forwardsEnv`: both simulators forward the environment's
  queries to the global functionality.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

/-! ## The protocol with the port of the global functionality exposed -/

section Protocol

variable {σ τ E O EG OG : Type}

/-- The protocol `π` over a global functionality with the port of the global functionality
exposed: `π` beside the forwarding simulator on `(EG, OG)`, over the merge of the two ports.
The idle event `idle` of the merged port is the idle event of the environment reduction. -/
noncomputable def gOpen (π : MultiHybrid σ E O EG OG) (idle : EG ⊕ EG) :
    Open (E ⊕ EG) (O ⊕ OG) EG OG :=
  (Open.ofMultiHybrid (π.tensor (MultiHybrid.idSim EG OG)) idle).comp (Open.merge EG OG)

/-- The protocol `π` over the global functionality `G`, with the port of `G` exposed. -/
noncomputable def gReal (π : MultiHybrid σ E O EG OG) (G : Sys τ EG OG) :
    Sys ((σ × Unit) × τ) (E ⊕ EG) (O ⊕ OG) :=
  (π.tensor (MultiHybrid.idSim EG OG)).withSub G.merge

/-- The admissibility of the subroutine `G` alone: a subroutine is admissible when it is `G`. -/
def pinSub {τG : Type} (G : Sys τG EG OG) : {τ : Type} → Sys τ EG OG → Prop :=
  fun {τ} K => ∃ h : τ = τG, h ▸ K = G

/-- The subroutine `G` is admissible for `pinSub G`. -/
theorem pinSub_self (G : Sys τ EG OG) : pinSub G G := ⟨rfl, rfl⟩

end Protocol

/-! ## The simulator of one-shot emulation -/

section TierA

variable {σS EH OH EA OA EA' OA' EG OG : Type}

/-- The simulator `S` on the adversary port, beside the forwarding simulators on the honest
port `(EH, OH)` and on the port `(EG, OG)` of the global functionality. -/
noncomputable def gSimHybrid (EH OH EG OG : Type) (S : MultiHybrid σS EA OA EA' OA') :
    MultiHybrid ((Unit × σS) × Unit) ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG) ((EH ⊕ EA') ⊕ EG)
      ((OH ⊕ OA') ⊕ OG) :=
  ((MultiHybrid.idSim EH OH).tensor S).tensor (MultiHybrid.idSim EG OG)

/-- **Opacity of the simulator**: if `S` is opaque from `WA` to `VA`, the simulator
`gSimHybrid EH OH EG OG S` is opaque for the sums of the views. -/
theorem gSimHybrid_opaque {VH : PubView EH OH} {VA : PubView EA OA} {WA : PubView EA' OA'}
    {WG : PubView EG OG} {S : MultiHybrid σS EA OA EA' OA'} (hS : S.Opaque VA WA) :
    (gSimHybrid EH OH EG OG S).Opaque ((VH.sum VA).sum WG) ((VH.sum WA).sum WG) :=
  ((MultiHybrid.idSim_opaque VH).tensor hS).tensor (MultiHybrid.idSim_opaque WG)

/-- The simulator of one-shot emulation over a global functionality, as a bundled simulator. -/
noncomputable def gSim {VH : PubView EH OH} {VA : PubView EA OA} {WA : PubView EA' OA'}
    (WG : PubView EG OG) (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA) :
    Simulator ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG) ((EH ⊕ EA') ⊕ EG) ((OH ⊕ OA') ⊕ OG)
      ((VH.sum VA).sum WG) ((VH.sum WA).sum WG) :=
  Simulator.ofMultiHybrid (gSimHybrid EH OH EG OG S) (gSimHybrid_opaque hS)

/-- The forwarding simulators on all three ports and a system `X` realize one another at
distance `0`. -/
theorem realizes_gSimHybrid_idSim {τ : Type} (X : Sys τ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) :
    Realizes X ((gSimHybrid EH OH EG OG (MultiHybrid.idSim EA OA)).withSub X) (fun _ _ => 0) :=
  realizes_zero_of_stepMap X _ (fun t => ((((), ()), ()), t)) rfl fun t e => by
    rcases e with (e | e) | e <;>
      simp only [SPComp.map, MultiHybrid.withSub, gSimHybrid, MultiHybrid.tensor,
        MultiHybrid.idSim, max_self, Prod.mk.eta, SPComp.pure_bind, Sum.map_inl, Sum.map_inr,
        Sum.elim_inl, Sum.elim_inr, MultiHybrid.drive, SPComp.bind_assoc] <;>
      refine congrArg (SPComp.bind _) (funext fun q => ?_) <;>
      rcases q with ⟨t', (o | o) | o⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, SPComp.pure_bind]

end TierA

/-! ## Squares over a global functionality -/

section Squares

variable {σ σF σS EH OH EA OA EA' OA' EG OG : Type} {VH : PubView EH OH} {VA : PubView EA OA}
  {WA : PubView EA' OA'} {WG : PubView EG OG}

/-- **The square over a global functionality**: top `gOpen π`, bottom `gOpen F`, the identity
simulator on the port of the global functionality on the left and `gSim WG S hS` on the right,
at the admissibility `A` and the bound `b`. -/
def GSquare (π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG)
    (F : MultiHybrid σF (EH ⊕ EA') (OH ⊕ OA') EG OG) (S : MultiHybrid σS EA OA EA' OA')
    (hS : S.Opaque VA WA) (idleπ idleF : EG ⊕ EG) (A : {τ : Type} → Sys τ EG OG → Prop)
    (b : {τ : Type} → Sys τ EG OG → (ζ : Type) →
      Env (Strat ζ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) ζ → ℝ≥0∞) : Prop :=
  Square (gOpen π idleπ) (gOpen F idleF) (Simulator.id EG OG WG) (gSim (VH := VH) WG S hS) A b

namespace GSquare

/-- A square pinned to `G` is the realization of `gSim WG S hS` over `gReal F G` by
`gReal π G`. -/
theorem realizes_gReal {τG : Type} {G : Sys τG EG OG}
    {π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG}
    {F : MultiHybrid σF (EH ⊕ EA') (OH ⊕ OA') EG OG} {S : MultiHybrid σS EA OA EA' OA'}
    {hS : S.Opaque VA WA} {idleπ idleF : EG ⊕ EG}
    {b : {τ : Type} → Sys τ EG OG → (ζ : Type) →
      Env (Strat ζ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) ζ → ℝ≥0∞}
    (h : GSquare (VH := VH) (WG := WG) π F S hS idleπ idleF (pinSub G) b) :
    Realizes (gReal π G) ((gSim (VH := VH) WG S hS).withSub (gReal F G)) (b G) :=
  h.realizes G (pinSub_self G)

/-- A realization of `gSim WG S hS` over `gReal F G` by `gReal π G` is a square pinned to
`G`. -/
theorem ofRealizes {τG : Type} {G : Sys τG EG OG}
    {π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG}
    {F : MultiHybrid σF (EH ⊕ EA') (OH ⊕ OA') EG OG} {S : MultiHybrid σS EA OA EA' OA'}
    {hS : S.Opaque VA WA} (idleπ idleF : EG ⊕ EG)
    {b : (ζ : Type) → Env (Strat ζ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) ζ → ℝ≥0∞}
    (h : Realizes (gReal π G) ((gSim (VH := VH) WG S hS).withSub (gReal F G)) b) :
    GSquare (VH := VH) (WG := WG) π F S hS idleπ idleF (pinSub G) (fun _ => b) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨rfl, rfl⟩ := hK
  exact h

/-- **The identity square over a global functionality**: the protocol `π` above itself, with
the forwarding simulator on the adversary port, at bound `0`, for every admissibility. This is
the square of a functionality whose ideal form is its real form, such as a common reference
string. -/
theorem refl (π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG) (idle : EG ⊕ EG)
    (A : {τ : Type} → Sys τ EG OG → Prop) :
    GSquare (VH := VH) (WG := WG) π π (MultiHybrid.idSim EA OA) (MultiHybrid.idSim_opaque VA)
      idle idle A (fun _ _ _ => 0) :=
  ⟨fun _ _ => realizes_gSimHybrid_idSim _⟩

end GSquare

end Squares

/-! ## Forwarding of the environment's queries on a shared port -/

namespace MultiHybrid

variable {σ E O E' O' EG OG : Type}

/-- The multi-call hybrid `π` forwards the environment's queries on the port `(EG, OG)` with
the state map `fwd`: an event `inr g` moves the state `s` to `fwd s` and is passed on as the
subroutine event `inr g`, and in a state `fwd s` an answer `inr o` is returned unchanged
without a change of state. Other subroutine events on the port, such as queries of the
simulator itself, are allowed. -/
structure ForwardsEnv (π : MultiHybrid σ (E ⊕ EG) (O ⊕ OG) (E' ⊕ EG) (O' ⊕ OG))
    (fwd : σ → σ) : Prop where
  /-- An event on the port is passed on. -/
  start : ∀ s g, π.start s (.inr g) = SPComp.pure (fwd s, .inl (.inr g))
  /-- An answer on the port in a forwarding state is returned. -/
  resume : ∀ s o, π.resume (fwd s) (.inr o) = SPComp.pure (fwd s, .inr (.inr o))
  /-- An answer on the port to the last allowed call in a forwarding state is returned. -/
  finish : ∀ s o, π.finish (fwd s) (.inr o) = SPComp.pure (fwd s, .inr o)

/-- Forwarding without a change of state is forwarding of the environment's queries with the
identity state map. -/
theorem Forwards.forwardsEnv {π : MultiHybrid σ (E ⊕ EG) (O ⊕ OG) (E' ⊕ EG) (O' ⊕ OG)}
    (h : Forwards π) : ForwardsEnv π _root_.id :=
  ⟨h.start, h.resume, h.finish⟩

end MultiHybrid

/-- The simulator of one-shot emulation forwards the environment's queries to the global
functionality. -/
theorem gSimHybrid_forwardsEnv {σS EH OH EA OA EA' OA' EG OG : Type}
    (S : MultiHybrid σS EA OA EA' OA') :
    (gSimHybrid EH OH EG OG S).ForwardsEnv _root_.id :=
  (MultiHybrid.forwards_tensor_idSim _ EG OG).forwardsEnv

/-! ## The router of a simulator with its own port on the global functionality -/

section TierB

variable {σS EH OH EA OA EA' OA' EG OG : Type}

/-- **The router**: one call per activation onto the honest port, the adversary port and the
single port of the global functionality. A query of the simulator on its port `inr` of the
adversary interface and a query of the environment on the port of the global functionality both
go to the port of the global functionality; the state records whether the pending query is the
simulator's (`true`), and the answer is returned to the port of the query. -/
noncomputable def gRouter (EH OH EA' OA' EG OG : Type) :
    MultiHybrid Bool ((EH ⊕ (EA' ⊕ EG)) ⊕ EG) ((OH ⊕ (OA' ⊕ OG)) ⊕ OG) ((EH ⊕ EA') ⊕ EG)
      ((OH ⊕ OA') ⊕ OG) where
  init := false
  fuel := 0
  start s e := match e with
    | .inl (.inl h) => SPComp.pure (s, .inl (.inl (.inl h)))
    | .inl (.inr (.inl a)) => SPComp.pure (s, .inl (.inl (.inr a)))
    | .inl (.inr (.inr g)) => SPComp.pure (true, .inl (.inr g))
    | .inr g => SPComp.pure (false, .inl (.inr g))
  resume s o := match o with
    | .inl (.inl h) => SPComp.pure (s, .inr (.inl (.inl h)))
    | .inl (.inr a) => SPComp.pure (s, .inr (.inl (.inr (.inl a))))
    | .inr g => match s with
      | true => SPComp.pure (true, .inr (.inl (.inr (.inr g))))
      | false => SPComp.pure (false, .inr (.inr g))
  finish s o := match o with
    | .inl (.inl h) => SPComp.pure (s, .inl (.inl h))
    | .inl (.inr a) => SPComp.pure (s, .inl (.inr (.inl a)))
    | .inr g => match s with
      | true => SPComp.pure (true, .inl (.inr (.inr g)))
      | false => SPComp.pure (false, .inr g)
  start_noFail s e := by
    rcases e with (h | a | g) | g <;> exact SPComp.pure_noFail _
  resume_noFail s o := by
    rcases s with _ | _ <;> rcases o with (h | a) | g <;> exact SPComp.pure_noFail _
  finish_noFail s o := by
    rcases s with _ | _ <;> rcases o with (h | a) | g <;> exact SPComp.pure_noFail _

/-- **Opacity of the router** under the sums of the views, with the equality of tags as the
unwinding relation. -/
theorem gRouter_opaque (VH : PubView EH OH) (WA : PubView EA' OA') (WG : PubView EG OG) :
    (gRouter EH OH EA' OA' EG OG).Opaque ((VH.sum (WA.sum WG)).sum WG) ((VH.sum WA).sum WG) := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    rcases he with ((he | (he | he)) | he) <;>
      exact rHoare_ret fun _ _ h => ⟨h, rfl, by simp_all [PubView.StepRel, PubView.sum]⟩
  · rintro s _ o o' rfl ho
    rcases s with _ | _ <;> rcases ho with ((ho | ho) | ho) <;>
      exact rHoare_ret fun _ _ h => ⟨h, rfl, by simp_all [PubView.StepRel, PubView.sum]⟩
  · rintro s _ o o' rfl ho
    rcases s with _ | _ <;> rcases ho with ((ho | ho) | ho) <;>
      exact rHoare_ret fun _ _ h => ⟨h, rfl, by simp_all [PubView.sum]⟩

/-- The router forwards the environment's queries to the global functionality, with the state
map to the tag `false`. -/
theorem gRouter_forwardsEnv :
    (gRouter EH OH EA' OA' EG OG).ForwardsEnv fun _ => false :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The simulator with its own port on the global functionality**: the simulator `S`, whose
subroutine interface carries a port `(EG, OG)` of the global functionality, on the adversary
port beside the forwarding simulators, followed by the router onto the single port of the
global functionality. -/
noncomputable def gSimB {VH : PubView EH OH} {VA : PubView EA OA} {WA : PubView EA' OA'}
    (WG : PubView EG OG) (S : MultiHybrid σS EA OA (EA' ⊕ EG) (OA' ⊕ OG))
    (hS : S.Opaque VA (WA.sum WG)) :
    Simulator ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG) ((EH ⊕ EA') ⊕ EG) ((OH ⊕ OA') ⊕ OG)
      ((VH.sum VA).sum WG) ((VH.sum WA).sum WG) :=
  (gSim WG S hS).comp
    (Simulator.ofMultiHybrid (gRouter EH OH EA' OA' EG OG) (gRouter_opaque VH WA WG))

end TierB

/-- **The square over a global functionality with a simulator that has its own port on it**:
top `gOpen π`, bottom `gOpen F`, the identity simulator on the left and `gSimB WG S hS` on the
right, at the admissibility `A` and the bound `b`. -/
def GSquareB {σ σF σS EH OH EA OA EA' OA' EG OG : Type} {VH : PubView EH OH}
    {VA : PubView EA OA} {WA : PubView EA' OA'} {WG : PubView EG OG}
    (π : MultiHybrid σ (EH ⊕ EA) (OH ⊕ OA) EG OG)
    (F : MultiHybrid σF (EH ⊕ EA') (OH ⊕ OA') EG OG)
    (S : MultiHybrid σS EA OA (EA' ⊕ EG) (OA' ⊕ OG)) (hS : S.Opaque VA (WA.sum WG))
    (idleπ idleF : EG ⊕ EG) (A : {τ : Type} → Sys τ EG OG → Prop)
    (b : {τ : Type} → Sys τ EG OG → (ζ : Type) →
      Env (Strat ζ ((EH ⊕ EA) ⊕ EG) ((OH ⊕ OA) ⊕ OG)) ζ → ℝ≥0∞) : Prop :=
  Square (gOpen π idleπ) (gOpen F idleF) (Simulator.id EG OG WG) (gSimB (VH := VH) WG S hS) A b

end CatCrypt.Crypto.UCTransparent

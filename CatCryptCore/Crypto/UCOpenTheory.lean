/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCFeedback
public import CatCryptCore.Crypto.UCParallel
public import CatCryptCore.Crypto.UCGlobal
public import PolyFun.Interaction.Open.OpenTheory
-- import all: unfolds the boundary equivalences `tensorComm` and `tensorAssoc`
import all PolyFun.Interaction.Interface

/-!
# Reactive systems as a PolyFun open theory

The reactive systems `Sys` of `UCTransparent` form an `OpenTheory` of PolyFun. A port boundary
`Δ` with interfaces in `Type` is read as a pair of types: the events of a system on `Δ` are the
packets of the input interface `Δ.In` (`Ev Δ`), and its outputs are the packets of the output
interface `Δ.Out` together with the empty output `none` (`Out Δ`). An object on `Δ` is a system
with these events and outputs and a bundled state type (`SysObj`).

* `map f` relabels the ports along the boundary morphism `f` (`Sys.mapPorts`): an event is
  translated back along `f.onIn`, an output forward along `f.onOut`.
* `par` is the parallel composition `Sys.par`, its ports read through the sum interface.
* `wire` connects the shared boundary `Γ` of the parallel composite: the loopback
  `Sys.loopback` of `Sys.par` along the wire `Γ.In ⊕ Γ.Out` with fuel `n`, where a packet
  emitted on `Γ` by one side is the next event of the other side, and an activation whose fuel
  runs out ends with the empty output (`wire_sys`).
* `plug` is the loopback of the parallel composite of a system and its context along the whole
  boundary. The closed system has no events.

The empty output makes the cut-off of the loopback uniform over all boundaries, the empty one
included. The theory is a direct instance: an object is a `Sys`, not an `OpenProcess`. PolyFun's
`OpenProcess` composes by interleaving step protocols under a scheduler sampler, while an
activation of a `Sys` is one call answered by one output, which is the semantics of the
composition theorems of `UCTransparent` (`Realizes.loopback`, `realizes_par`).

## Main definitions

* `UCOpenTheory.Ev`, `UCOpenTheory.Out` — the events and outputs at a port boundary
* `UCOpenTheory.sysOpenTheory n` — the open theory of reactive systems, wire fuel `n`

## Main results

* `UCOpenTheory.sysOpenTheory_isLawful` — `map` is functorial and `par`, `wire`, `plug` are
  natural in the boundary (`OpenTheory.IsLawful`), with equality of systems
* `UCOpenTheory.wire_sys` — `wire` is the loopback of the routed parallel composite
* `UCOpenTheory.view_par_assoc`, `UCOpenTheory.view_par_comm`,
  `UCOpenTheory.view_par_leftUnit`, `UCOpenTheory.view_par_rightUnit` — the symmetric
  monoidal laws of `par`, as equalities of views; the two sides have different state types
  (`(τ₁ × τ₂) × τ₃` and `τ₁ × (τ₂ × τ₃)`), so `OpenTheory.IsMonoidal` does not hold with
  equality of objects; the unit is `unitObj`, the `OpenTheory.HasUnit` unit
* `Sys.loopback_mapPorts_eq` — relabelling the outer ports of a loopback is the loopback of the
  relabelled system
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.Sys

open CatCrypt.Core

variable {τ υ E O E' O' E'' O'' X : Type}

/-- Relabelling the ports of a system by identities is the system itself. -/
theorem mapPorts_id (S : Sys τ E O) : S.mapPorts (fun e => e) (fun o => o) = S := by
  cases S
  simp only [mapPorts, relabel, Sys.mk.injEq, true_and]
  funext t e
  exact SPComp.map_id _

/-- Relabelling twice is relabelling by the composite maps. -/
theorem mapPorts_mapPorts (S : Sys τ E O) (f : E' → E) (g : O → O') (f' : E'' → E')
    (g' : O' → O'') :
    (S.mapPorts f g).mapPorts f' g' = S.mapPorts (fun e => f (f' e)) (fun o => g' (g o)) := by
  simp only [mapPorts, relabel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The parallel composition of relabelled systems is the relabelled parallel composition. -/
theorem par_mapPorts {EX OX EY OY : Type} (S : Sys τ E O) (T : Sys υ E' O') (f : EX → E)
    (g : O → OX) (f' : EY → E') (g' : O' → OY) :
    (S.mapPorts f g).par (T.mapPorts f' g') =
      (S.par T).mapPorts (Sum.map f f') (Sum.map g g') := by
  simp only [par, mapPorts, relabel, Sys.mk.injEq, true_and]
  funext s e
  cases e <;> simp only [Sum.elim_inl, Sum.elim_inr, Sum.map_inl, Sum.map_inr, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]

/-- Relabelling the outer ports of a loopback is the loopback of the relabelled system, the
wire unchanged. -/
theorem loopback_mapPorts_eq (S : Sys τ (E ⊕ X) (O ⊕ X)) (f : E' → E) (g : O → O') (n : ℕ)
    (cut : X → O) :
    (S.mapPorts (Sum.map f id) (Sum.map g id)).loopback n (fun x => g (cut x)) =
      (S.loopback n cut).mapPorts f g := by
  have hdrive : ∀ (k : ℕ) (ev : E' ⊕ X) (t : τ),
      (MultiHybrid.fbHybrid n fun x => g (cut x)).drive
          (S.mapPorts (Sum.map f id) (Sum.map g id)) k () (.inl ev) t =
        SPComp.map (fun p => (p.1, p.2.1, g p.2.2))
          ((MultiHybrid.fbHybrid n cut).drive S k () (.inl (Sum.map f id ev)) t) := by
    intro k
    induction k with
    | zero =>
      intro ev t
      simp only [MultiHybrid.drive, mapPorts, relabel, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      congr 1
      funext q
      rcases q with ⟨t', o | x⟩ <;>
        simp only [MultiHybrid.fbHybrid, Sum.map_inl, Sum.map_inr, SPComp.pure_bind, id]
    | succ k ih =>
      intro ev t
      simp only [MultiHybrid.drive, mapPorts, relabel, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      congr 1
      funext q
      rcases q with ⟨t', o | x⟩
      · simp only [MultiHybrid.fbHybrid, Sum.map_inl, SPComp.pure_bind, MultiHybrid.drive]
      · simp only [MultiHybrid.fbHybrid, Sum.map_inr, SPComp.pure_bind, id]
        exact ih (.inr x) t'
  simp only [loopback, MultiHybrid.withSub, mapPorts, relabel, Sys.mk.injEq, true_and]
  funext t e
  have h := hdrive n (.inl e) t.2
  simp only [SPComp.map] at h ⊢
  erw [SPComp.pure_bind, SPComp.pure_bind]
  erw [h]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]
  rfl

end CatCrypt.Crypto.UCTransparent.Sys

namespace CatCrypt.Crypto.UCOpenTheory

open CatCrypt.Core CatCrypt.Crypto.UCTransparent
open Interaction Interaction.Open

/-! ## Events and outputs at a port boundary -/

/-- The events of a system on the boundary `Δ`: the packets of its input interface. -/
abbrev Ev (Δ : PortBoundary) : Type := Interface.Packet Δ.In

/-- The outputs of a system on the boundary `Δ`: a packet of its output interface, or `none`
for an activation that emits nothing. -/
abbrev Out (Δ : PortBoundary) : Type := Option (Interface.Packet Δ.Out)

/-- The empty boundary has no events. -/
def noEv {α : Sort _} (e : Ev PortBoundary.empty) : α :=
  match e with
  | ⟨a, _⟩ => nomatch a

section Packets

variable {I J : Interface.{0, 0}}

/-- A packet of the sum interface as a packet of one of the summands. -/
def unsum : Interface.Packet (Interface.sum I J) → Interface.Packet I ⊕ Interface.Packet J
  | ⟨.inl a, b⟩ => .inl ⟨a, b⟩
  | ⟨.inr a, b⟩ => .inr ⟨a, b⟩

/-- A packet of one of the summands as a packet of the sum interface. -/
def insum : Interface.Packet I ⊕ Interface.Packet J → Interface.Packet (Interface.sum I J)
  | .inl ⟨a, b⟩ => ⟨.inl a, b⟩
  | .inr ⟨a, b⟩ => ⟨.inr a, b⟩

/-- `unsum` inverts `insum`. -/
@[simp] theorem unsum_insum (s : Interface.Packet I ⊕ Interface.Packet J) :
    unsum (insum s) = s := by
  rcases s with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl

/-- `insum` inverts `unsum`. -/
@[simp] theorem insum_unsum (p : Interface.Packet (Interface.sum I J)) :
    insum (unsum p) = p := by
  rcases p with ⟨a | a, b⟩ <;> rfl

/-- The sum of two interface morphisms acts on each summand. -/
theorem mapPacket_sum_insum {I' J' : Interface.{0, 0}} (f : Interface.Hom I I')
    (g : Interface.Hom J J') (s : Interface.Packet I ⊕ Interface.Packet J) :
    Interface.Hom.mapPacket (Interface.Hom.sum f g) (insum s) =
      insum (Sum.map (Interface.Hom.mapPacket f) (Interface.Hom.mapPacket g) s) := by
  rcases s with p | p
  · exact congrArg (fun h => Interface.Hom.mapPacket h p) (Interface.Hom.comp_sum_inl f g)
  · exact congrArg (fun h => Interface.Hom.mapPacket h p) (Interface.Hom.comp_sum_inr f g)

/-- The sum of two interface morphisms acts on each summand, read through `unsum`. -/
theorem unsum_mapPacket_sum {I' J' : Interface.{0, 0}} (f : Interface.Hom I I')
    (g : Interface.Hom J J') (p : Interface.Packet (Interface.sum I J)) :
    unsum (Interface.Hom.mapPacket (Interface.Hom.sum f g) p) =
      Sum.map (Interface.Hom.mapPacket f) (Interface.Hom.mapPacket g) (unsum p) := by
  rw [← insum_unsum p, mapPacket_sum_insum, unsum_insum, unsum_insum]

/-- The output of a parallel composite: the output of the activated side, read in the sum
interface. -/
def parOut :
    Option (Interface.Packet I) ⊕ Option (Interface.Packet J) →
      Option (Interface.Packet (Interface.sum I J))
  | .inl o => o.map fun p => insum (.inl p)
  | .inr o => o.map fun p => insum (.inr p)

end Packets

/-! ## The operations -/

section Ops

variable {Δ Δ₁ Δ₂ Γ : PortBoundary}

/-- The system `W` with its ports relabelled along the boundary morphism `f`. -/
noncomputable def mapObj (f : PortBoundary.Hom Δ₁ Δ₂) (W : SysObj (Ev Δ₁) (Out Δ₁)) :
    SysObj (Ev Δ₂) (Out Δ₂) :=
  ⟨W.St, W.sys.mapPorts (Interface.Hom.mapPacket f.onIn)
    (Option.map (Interface.Hom.mapPacket f.onOut))⟩

/-- The parallel composition of `W₁` and `W₂` on the tensor boundary. -/
noncomputable def parObj (W₁ : SysObj (Ev Δ₁) (Out Δ₁)) (W₂ : SysObj (Ev Δ₂) (Out Δ₂)) :
    SysObj (Ev (Δ₁.tensor Δ₂)) (Out (Δ₁.tensor Δ₂)) :=
  ⟨W₁.St × W₂.St, (W₁.sys.par W₂.sys).mapPorts unsum parOut⟩

/-- The routing of events in a wiring: an outer event goes to the side it is addressed to; a
wire value on `Γ.In` is an event of the left side, a wire value on `Γ.Out` an event of the right
side. -/
def wireEv :
    Ev (Δ₁.tensor Δ₂) ⊕ (Interface.Packet Γ.In ⊕ Interface.Packet Γ.Out) →
      Ev (Δ₁.tensor Γ) ⊕ Ev (Γ.swap.tensor Δ₂)
  | .inl p => match unsum p with
    | .inl e => .inl (insum (.inl e))
    | .inr e => .inr (insum (.inr e))
  | .inr (.inl x) => .inl (insum (.inr x))
  | .inr (.inr y) => .inr (insum (.inl y))

/-- The routing of outputs in a wiring: an output on an outer boundary is an outer output; a
packet emitted on the shared boundary `Γ` is a wire value. -/
def wireOut :
    Out (Δ₁.tensor Γ) ⊕ Out (Γ.swap.tensor Δ₂) →
      Out (Δ₁.tensor Δ₂) ⊕ (Interface.Packet Γ.In ⊕ Interface.Packet Γ.Out)
  | .inl none => .inl none
  | .inl (some p) => match unsum p with
    | .inl o => .inl (some (insum (.inl o)))
    | .inr y => .inr (.inr y)
  | .inr none => .inl none
  | .inr (some p) => match unsum p with
    | .inl x => .inr (.inl x)
    | .inr o => .inl (some (insum (.inr o)))

/-- Unfolding lemma of `wireEv` at an outer event. -/
@[simp] theorem wireEv_inl (s : Ev Δ₁ ⊕ Ev Δ₂) :
    wireEv (Γ := Γ) (.inl (insum s)) =
      Sum.elim (fun e => .inl (insum (.inl e))) (fun e => .inr (insum (.inr e))) s := by
  rcases s with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl

/-- Unfolding lemma of `wireOut` at an output of the left side. -/
@[simp] theorem wireOut_inl_some (s : Interface.Packet Δ₁.Out ⊕ Interface.Packet Γ.Out) :
    wireOut (Δ₂ := Δ₂) (.inl (some (insum s))) =
      Sum.elim (fun o => .inl (some (insum (.inl o)))) (fun y => .inr (.inr y)) s := by
  rcases s with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl

/-- Unfolding lemma of `wireOut` at an output of the right side. -/
@[simp] theorem wireOut_inr_some (s : Interface.Packet Γ.In ⊕ Interface.Packet Δ₂.Out) :
    wireOut (Δ₁ := Δ₁) (.inr (some (insum s))) =
      Sum.elim (fun x => .inr (.inl x)) (fun o => .inl (some (insum (.inr o)))) s := by
  rcases s with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl

/-- The routed parallel composite of a wiring: `Sys.par` of the two sides, its ports relabelled
into the outer boundary and the wire. -/
noncomputable def wireCore (W₁ : SysObj (Ev (Δ₁.tensor Γ)) (Out (Δ₁.tensor Γ)))
    (W₂ : SysObj (Ev (Γ.swap.tensor Δ₂)) (Out (Γ.swap.tensor Δ₂))) :
    Sys (W₁.St × W₂.St) (Ev (Δ₁.tensor Δ₂) ⊕ (Interface.Packet Γ.In ⊕ Interface.Packet Γ.Out))
      (Out (Δ₁.tensor Δ₂) ⊕ (Interface.Packet Γ.In ⊕ Interface.Packet Γ.Out)) :=
  (W₁.sys.par W₂.sys).mapPorts wireEv wireOut

/-- The wiring of `W₁` and `W₂` along `Γ` with fuel `n`: the loopback of the routed parallel
composite, an activation cut off with the empty output. -/
noncomputable def wireObj (n : ℕ) (W₁ : SysObj (Ev (Δ₁.tensor Γ)) (Out (Δ₁.tensor Γ)))
    (W₂ : SysObj (Ev (Γ.swap.tensor Δ₂)) (Out (Γ.swap.tensor Δ₂))) :
    SysObj (Ev (Δ₁.tensor Δ₂)) (Out (Δ₁.tensor Δ₂)) :=
  ⟨Unit × (W₁.St × W₂.St), (wireCore W₁ W₂).loopback n fun _ => none⟩

/-- The routing of events in a plugging: a wire value on `Δ.In` is an event of the system, a
wire value on `Δ.Out` an event of the context. -/
def plugEv :
    Ev PortBoundary.empty ⊕ (Interface.Packet Δ.In ⊕ Interface.Packet Δ.Out) →
      Ev Δ ⊕ Ev Δ.swap
  | .inl e => noEv e
  | .inr x => x

/-- The routing of outputs in a plugging: every packet emitted is a wire value. -/
def plugOut :
    Out Δ ⊕ Out Δ.swap →
      Out PortBoundary.empty ⊕ (Interface.Packet Δ.In ⊕ Interface.Packet Δ.Out)
  | .inl none => .inl none
  | .inl (some o) => .inr (.inr o)
  | .inr none => .inl none
  | .inr (some i) => .inr (.inl i)

/-- The system `W` closed against the context `K` with fuel `n`. -/
noncomputable def plugObj (n : ℕ) (W : SysObj (Ev Δ) (Out Δ))
    (K : SysObj (Ev Δ.swap) (Out Δ.swap)) :
    SysObj (Ev PortBoundary.empty) (Out PortBoundary.empty) :=
  ⟨Unit × (W.St × K.St), ((W.sys.par K.sys).mapPorts plugEv plugOut).loopback n fun _ => none⟩

end Ops

/-! ## The open theory -/

/-- Reactive systems as a PolyFun open theory, wire fuel `n`: objects at `Δ` are systems with
events `Ev Δ` and outputs `Out Δ`. -/
noncomputable def sysOpenTheory (n : ℕ) : OpenTheory where
  Obj Δ := SysObj (Ev Δ) (Out Δ)
  map f W := mapObj f W
  par W₁ W₂ := parObj W₁ W₂
  wire W₁ W₂ := wireObj n W₁ W₂
  plug W K := plugObj n W K

variable {n : ℕ}

/-- Unfolding lemma of `wire`: the loopback of the routed parallel composite, cut off with the
empty output. -/
theorem wire_sys {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : (sysOpenTheory n).Obj (Δ₁.tensor Γ))
    (W₂ : (sysOpenTheory n).Obj (Γ.swap.tensor Δ₂)) :
    SysObj.sys ((sysOpenTheory n).wire W₁ W₂) = (wireCore W₁ W₂).loopback n fun _ => none :=
  rfl

/-- Two closed systems with the same state type and initial state are equal: they have no
events. -/
theorem closed_eq {τ : Type} (S T : Sys τ (Ev PortBoundary.empty) (Out PortBoundary.empty))
    (h : S.init = T.init) : S = T := by
  cases S
  cases T
  cases h
  congr
  funext _ e
  exact noEv e

/-- Reactive systems form a lawful open theory: `map` is functorial, and `par`, `wire` and
`plug` are natural in the boundary, with equality of systems. -/
instance sysOpenTheory_isLawful (n : ℕ) : OpenTheory.IsLawful (sysOpenTheory n) where
  map_id W := by
    rcases W with ⟨St, S⟩
    change SysObj.mk St (S.mapPorts _ _) = SysObj.mk St S
    congr 1
    convert Sys.mapPorts_id S using 2 <;> funext o <;> cases o <;> rfl
  map_comp g f W := by
    rcases W with ⟨St, S⟩
    change SysObj.mk St (S.mapPorts _ _) = SysObj.mk St ((S.mapPorts _ _).mapPorts _ _)
    rw [Sys.mapPorts_mapPorts]
    congr 2
    funext o
    cases o <;> rfl
  map_par f₁ f₂ W₁ W₂ := by
    rcases W₁ with ⟨St₁, S₁⟩
    rcases W₂ with ⟨St₂, S₂⟩
    change SysObj.mk _ (((S₁.par S₂).mapPorts unsum parOut).mapPorts _ _) =
      SysObj.mk _ (((S₁.mapPorts _ _).par (S₂.mapPorts _ _)).mapPorts unsum parOut)
    rw [Sys.par_mapPorts, Sys.mapPorts_mapPorts, Sys.mapPorts_mapPorts]
    congr 2
    · funext e
      exact unsum_mapPacket_sum _ _ e
    · funext o
      rcases o with (_ | p) | (_ | p)
      · rfl
      · exact congrArg some (mapPacket_sum_insum _ _ (.inl p))
      · rfl
      · exact congrArg some (mapPacket_sum_insum _ _ (.inr p))
  map_wire f₁ f₂ W₁ W₂ := by
    rcases W₁ with ⟨St₁, S₁⟩
    rcases W₂ with ⟨St₂, S₂⟩
    change SysObj.mk _ ((((S₁.par S₂).mapPorts wireEv wireOut).loopback n
        fun _ => none).mapPorts _ _) =
      SysObj.mk _ ((((S₁.mapPorts _ _).par (S₂.mapPorts _ _)).mapPorts wireEv wireOut).loopback n
        fun _ => none)
    rw [← Sys.loopback_mapPorts_eq, Sys.par_mapPorts, Sys.mapPorts_mapPorts,
      Sys.mapPorts_mapPorts]
    congr 3
    · funext e
      rcases e with p | (x | y)
      · rw [← insum_unsum p]
        rcases unsum p with q | q <;>
          simp [PortBoundary.Hom.tensor, PortBoundary.Hom.id, mapPacket_sum_insum]
      · exact congrArg Sum.inl
          (mapPacket_sum_insum f₁.onIn (Interface.Hom.id _) (.inr x)).symm
      · exact congrArg Sum.inr
          (mapPacket_sum_insum (Interface.Hom.id _) f₂.onIn (.inl y)).symm
    · funext o
      rcases o with (_ | p) | (_ | p)
      · rfl
      · rw [← insum_unsum p]
        rcases unsum p with q | q <;>
          simp [PortBoundary.Hom.tensor, PortBoundary.Hom.id, mapPacket_sum_insum]
      · rfl
      · rw [← insum_unsum p]
        rcases unsum p with q | q <;>
          simp [PortBoundary.Hom.tensor, PortBoundary.Hom.id, mapPacket_sum_insum]
  map_plug f W K := by
    rcases W with ⟨St₁, S₁⟩
    rcases K with ⟨St₂, S₂⟩
    exact congrArg (SysObj.mk _) (closed_eq _ _ rfl)

/-! ## Monoidal laws up to views -/

/-- The unit system on the empty boundary: one state and no events. -/
noncomputable def unitObj : SysObj (Ev PortBoundary.empty) (Out PortBoundary.empty) :=
  ⟨Unit, ⟨(), fun _ e => noEv e⟩⟩

/-- The unit system as the unit of the open theory. -/
noncomputable instance (n : ℕ) : OpenTheory.HasUnit (sysOpenTheory n) := ⟨unitObj⟩

/-- **Associativity of `par`, up to views.** -/
theorem view_par_assoc {Δ₁ Δ₂ Δ₃ : PortBoundary} (W₁ : SysObj (Ev Δ₁) (Out Δ₁))
    (W₂ : SysObj (Ev Δ₂) (Out Δ₂)) (W₃ : SysObj (Ev Δ₃) (Out Δ₃)) {ζ : Type}
    (Z : Strat ζ (Ev (Δ₁.tensor (Δ₂.tensor Δ₃))) (Out (Δ₁.tensor (Δ₂.tensor Δ₃)))) :
    view (SysObj.sys ((sysOpenTheory n).map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
      ((sysOpenTheory n).par ((sysOpenTheory n).par W₁ W₂) W₃))) Z =
      view (SysObj.sys ((sysOpenTheory n).par W₁ ((sysOpenTheory n).par W₂ W₃))) Z := by
  refine view_eq_of_stepMap _ _ (fun s => (s.1.1, (s.1.2, s.2))) rfl ?_ Z
  rintro ⟨⟨t₁, t₂⟩, t₃⟩ ⟨a | a | a, b⟩
  · have h : unsum ((PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).onIn.toHom.mapPacket
        ⟨Sum.inl a, b⟩) = .inl ⟨Sum.inl a, b⟩ := rfl
    simp only [sysOpenTheory, mapObj, parObj, Sys.mapPorts, Sys.relabel, Sys.par, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    rw [h]
    simp only [unsum, Sum.elim, SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg (SPComp.bind _) (funext fun q => ?_)
    rcases q with ⟨s, _ | ⟨c, d⟩⟩ <;> rfl
  · have h : unsum ((PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).onIn.toHom.mapPacket
        ⟨Sum.inr (Sum.inl a), b⟩) = .inl ⟨Sum.inr a, b⟩ := rfl
    simp only [sysOpenTheory, mapObj, parObj, Sys.mapPorts, Sys.relabel, Sys.par, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    rw [h]
    simp only [unsum, Sum.elim, SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg (SPComp.bind _) (funext fun q => ?_)
    rcases q with ⟨s, _ | ⟨c, d⟩⟩ <;> rfl
  · have h : unsum ((PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).onIn.toHom.mapPacket
        ⟨Sum.inr (Sum.inr a), b⟩) = .inr ⟨a, b⟩ := rfl
    simp only [sysOpenTheory, mapObj, parObj, Sys.mapPorts, Sys.relabel, Sys.par, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    rw [h]
    simp only [unsum, Sum.elim, SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg (SPComp.bind _) (funext fun q => ?_)
    rcases q with ⟨s, _ | ⟨c, d⟩⟩ <;> rfl

/-- **Commutativity of `par`, up to views.** -/
theorem view_par_comm {Δ₁ Δ₂ : PortBoundary} (W₁ : SysObj (Ev Δ₁) (Out Δ₁))
    (W₂ : SysObj (Ev Δ₂) (Out Δ₂)) {ζ : Type}
    (Z : Strat ζ (Ev (Δ₂.tensor Δ₁)) (Out (Δ₂.tensor Δ₁))) :
    view (SysObj.sys ((sysOpenTheory n).map (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
      ((sysOpenTheory n).par W₁ W₂))) Z =
      view (SysObj.sys ((sysOpenTheory n).par W₂ W₁)) Z := by
  refine view_eq_of_stepMap _ _ Prod.swap rfl ?_ Z
  rintro ⟨t₁, t₂⟩ ⟨a | a, b⟩
  · have h : unsum ((PortBoundary.Equiv.tensorComm Δ₁ Δ₂).onIn.toHom.mapPacket
        ⟨Sum.inl a, b⟩) = .inr ⟨a, b⟩ := rfl
    simp only [sysOpenTheory, mapObj, parObj, Sys.mapPorts, Sys.relabel, Sys.par, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    rw [h]
    simp only [unsum, Sum.elim, SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg (SPComp.bind _) (funext fun q => ?_)
    rcases q with ⟨s, _ | ⟨c, d⟩⟩ <;> rfl
  · have h : unsum ((PortBoundary.Equiv.tensorComm Δ₁ Δ₂).onIn.toHom.mapPacket
        ⟨Sum.inr a, b⟩) = .inl ⟨a, b⟩ := rfl
    simp only [sysOpenTheory, mapObj, parObj, Sys.mapPorts, Sys.relabel, Sys.par, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    rw [h]
    simp only [unsum, Sum.elim, SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg (SPComp.bind _) (funext fun q => ?_)
    rcases q with ⟨s, _ | ⟨c, d⟩⟩ <;> rfl

/-- **Left unit law of `par`, up to views.** -/
theorem view_par_leftUnit {Δ : PortBoundary} (W : SysObj (Ev Δ) (Out Δ)) {ζ : Type}
    (Z : Strat ζ (Ev Δ) (Out Δ)) :
    view (SysObj.sys ((sysOpenTheory n).map (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom
      ((sysOpenTheory n).par unitObj W))) Z =
      view (SysObj.sys W) Z := by
  refine view_eq_of_stepMap _ _ Prod.snd rfl ?_ Z
  rintro ⟨t₁, t₂⟩ ⟨a, b⟩
  simp only [sysOpenTheory, mapObj, parObj, Sys.mapPorts, Sys.relabel, Sys.par, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]
  have h : unsum ((PortBoundary.Equiv.tensorEmptyLeft Δ).onIn.toHom.mapPacket ⟨a, b⟩) =
      .inr ⟨a, b⟩ := rfl
  rw [h]
  dsimp only [Sum.elim]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]
  conv_rhs => rw [← SPComp.bind_pure (W.sys.step t₂ ⟨a, b⟩)]
  refine congrArg (SPComp.bind _) (funext fun q => ?_)
  rcases q with ⟨s, _ | ⟨c, d⟩⟩ <;> rfl

/-- **Right unit law of `par`, up to views.** -/
theorem view_par_rightUnit {Δ : PortBoundary} (W : SysObj (Ev Δ) (Out Δ)) {ζ : Type}
    (Z : Strat ζ (Ev Δ) (Out Δ)) :
    view (SysObj.sys ((sysOpenTheory n).map (PortBoundary.Equiv.tensorEmptyRight Δ).toHom
      ((sysOpenTheory n).par W unitObj))) Z =
      view (SysObj.sys W) Z := by
  refine view_eq_of_stepMap _ _ Prod.fst rfl ?_ Z
  rintro ⟨t₁, t₂⟩ ⟨a, b⟩
  simp only [sysOpenTheory, mapObj, parObj, Sys.mapPorts, Sys.relabel, Sys.par, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]
  have h : unsum ((PortBoundary.Equiv.tensorEmptyRight Δ).onIn.toHom.mapPacket ⟨a, b⟩) =
      .inl ⟨a, b⟩ := rfl
  rw [h]
  dsimp only [Sum.elim]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]
  conv_rhs => rw [← SPComp.bind_pure (W.sys.step t₁ ⟨a, b⟩)]
  refine congrArg (SPComp.bind _) (funext fun q => ?_)
  rcases q with ⟨s, _ | ⟨c, d⟩⟩ <;> rfl

end CatCrypt.Crypto.UCOpenTheory

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCInterleave

/-!
# Transparent functionalities with an honest port and an adversary port

The ideal world `ideal F S` of a transparent functionality `F` hands every event, honest inputs
included, to the simulator `S`, which proposes the next state and output. This file splits `F`
into a system with two ports and turns `S` into a simulator that reaches honest inputs only
through the adversary port, so that a realization of `ideal F S` becomes a realization behind an
opaque bundled simulator (`RealizesSim`).

An event splitting `sp : EvSplit E P` gives the honest input `sp.hon e : Option P` of an event
and the completion `sp.rest e : P → E`, which puts an honest input in place of the honest input
of `e`. The port system `F.ports` has state `(trace, exploded flag, pending honest input)`:

* honest port: `submit p` records `p` as pending; `read` answers the output of the last trace
  entry, or the exploded output once the flag is set;
* adversary port: `peek` leaks the pending honest input; `propose ev o s` appends the entry
  `(e, o, s)` to the trace, where `e` is the event `ev` or the completion `ev` of the pending
  input, sets the flag when the guard of `F` fails on the extended trace, clears the pending
  input and answers `o`, or the exploded output once the flag is set.

The simulator `transSim S sp hS o₀` forwards the honest input of an outer event to the honest
port without keeping it, reads it back with `peek`, runs `S` on the completed event, proposes
the result and answers the outer event with the honest `read`. An event without honest input is
run through `S` and proposed directly; the answer of the proposal is the outer output. The
simulator is opaque from the view `sp.view`, which relates events with honest inputs and equal
completions, to the view `portView`, which relates any two `submit` events
(`transSim_opaque`): its decisions do not depend on honest inputs.

## Main definitions

* `EvSplit`, `EvSplit.sum`, `EvSplit.prod`: event splittings.
* `THonEv`, `TAdvEv`, `TAdvOut`, `TSt`: the ports and the state of the port system.
* `TFunc.ports`: the port system of a transparent functionality.
* `transSim`, `transSimulator`: the simulator of the adversary port and its bundled form.

## Main results

* `transSim_opaque`: the simulator is opaque.
* `ideal_realizes_ports`: `ideal F S` realizes `transSim` over `F.ports` at distance `0`.
* `realizesSim_ports_of_realizes`: a realization of `ideal F S` with bound `b` is a realization
  of `F.ports` behind `transSimulator` with bound `b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

/-! ## Event splittings -/

/-- A splitting of the events `E` into an honest input of type `P` and a remainder: `hon e` is
the honest input of `e`, if any, and `rest e p` is `e` with `p` in place of its honest input. -/
structure EvSplit (E P : Type) where
  /-- The honest input of an event. -/
  hon : E → Option P
  /-- The event with a given honest input in place of its own. -/
  rest : E → P → E
  /-- Completing an event with its own honest input gives the event. -/
  rest_hon : ∀ e p, hon e = some p → rest e p = e

namespace EvSplit

variable {E P A G : Type}

/-- The splitting of `Event P A`: honest events carry their input. -/
def sum : EvSplit (Event P A) P where
  hon := Sum.getLeft?
  rest e p := match e with
    | .inl _ => .inl p
    | .inr a => .inr a
  rest_hon e p h := by
    cases e with
    | inl q => simp only [Sum.getLeft?_inl, Option.some.injEq] at h; subst h; rfl
    | inr a => rfl

/-- The splitting of pairs: the honest input of the first component, the second kept. -/
def prod (sp : EvSplit E P) : EvSplit (E × G) P where
  hon e := sp.hon e.1
  rest e p := (sp.rest e.1 p, e.2)
  rest_hon e p h := by rw [sp.rest_hon e.1 p h]

/-- The public view of the outer interface: two events without honest input are related when
equal, two events with honest inputs when their completions are equal; outputs are related when
equal. -/
def view {O : Type} (sp : EvSplit E P) : PubView E O where
  ev e e' := (sp.hon e = none ∧ e = e') ∨
    ((sp.hon e).isSome ∧ (sp.hon e').isSome ∧ sp.rest e = sp.rest e')
  out := Eq

end EvSplit

/-! ## The port system -/

/-- Events of the honest port. -/
inductive THonEv (P : Type) where
  /-- Submit the honest input `p`. -/
  | submit (p : P)
  /-- Read the current output. -/
  | read

/-- Events of the adversary port. -/
inductive TAdvEv (σ E O P : Type) where
  /-- Leak the pending honest input. -/
  | peek
  /-- Propose the entry with event `ev` (an event, or the completion of the pending honest
  input), output `o` and state `s`. -/
  | propose (ev : E ⊕ (P → E)) (o : O) (s : σ)

/-- Outputs of the adversary port. -/
inductive TAdvOut (P O : Type) where
  /-- The pending honest input. -/
  | leak (p : Option P)
  /-- The output of a proposal. -/
  | out (o : O)

/-- The state of the port system: trace, exploded flag and pending honest input. -/
abbrev TSt (σ E O P : Type) := Trace σ E O × Bool × Option P

variable {σ τ E O P : Type}

/-- The event of a proposed entry: the event itself, or the completion of the pending honest
input. -/
def entryEv : E ⊕ (P → E) → Option P → Option E
  | .inl e, _ => some e
  | .inr r, some p => some (r p)
  | .inr _, none => none

namespace TFunc

/-- The output read on the honest port: the exploded output once the flag is set, otherwise
the output of the last trace entry. -/
def readOut (F : TFunc σ E O) (tr : Trace σ E O) (x : Bool) : O :=
  if x then F.exploded else ((tr.getLast?.map fun q => q.2.1).getD F.exploded)

/-- The honest port of `F`: `submit p` records `p` as pending, `read` answers `readOut`. -/
noncomputable def honSys (F : TFunc σ E O) : Sys (TSt σ E O P) (THonEv P) (Option O) where
  init := ([], false, none)
  step t
    | .submit p => SPComp.pure ((t.1, t.2.1, some p), none)
    | .read => SPComp.pure (t, some (F.readOut t.1 t.2.1))

/-- The adversary port of `F`: `peek` leaks the pending honest input; `propose ev o s`
appends the entry of the event `entryEv ev`, sets the flag when the guard fails on the extended
trace, clears the pending input and answers `o` unless exploded. -/
noncomputable def advSys (F : TFunc σ E O) : Sys (TSt σ E O P) (TAdvEv σ E O P) (TAdvOut P O) where
  init := ([], false, none)
  step t
    | .peek => SPComp.pure (t, .leak t.2.2)
    | .propose ev o s =>
      match entryEv ev t.2.2 with
      | none => SPComp.pure (t, .out F.exploded)
      | some e =>
        let tr := t.1 ++ [(e, o, s)]
        let x := t.2.1 || !F.guard tr
        SPComp.pure ((tr, x, none), .out (if x then F.exploded else o))

/-- **The port system of the transparent functionality `F`**: the honest port `honSys` and the
adversary port `advSys` on one state, each answering on its own port. -/
noncomputable def ports (F : TFunc σ E O) :
    Sys (TSt σ E O P) (THonEv P ⊕ TAdvEv σ E O P) (Option O ⊕ TAdvOut P O) where
  init := ([], false, none)
  step t := Sum.elim (fun e => SPComp.map (fun q => (q.1, .inl q.2)) (F.honSys.step t e))
    (fun e => SPComp.map (fun q => (q.1, .inr q.2)) (F.advSys.step t e))

/-- The port system answers every event on the port of the event. -/
theorem ports_portTyped (F : TFunc σ E O) : (F.ports (P := P)).PortTyped :=
  ⟨F.honSys, F.advSys, fun _ _ => rfl, fun _ _ => rfl⟩

end TFunc

/-- The view of the port interface: two `submit` events are related whatever their inputs;
other events and all outputs are related when equal. -/
def portView : PubView (THonEv P ⊕ TAdvEv σ E O P) (Option O ⊕ TAdvOut P O) where
  ev := Sum.LiftRel (fun g g' => g = g' ∨ ∃ p p', g = .submit p ∧ g' = .submit p') Eq
  out := Eq

/-! ## The simulator of the adversary port -/

/-- The phase of the simulator within an activation. -/
inductive TPhase (P E : Type) where
  /-- Between activations. -/
  | idle
  /-- An honest input was forwarded; its completion is `r`. -/
  | sub (r : P → E)
  /-- The pending honest input was requested; its completion is `r`. -/
  | peek (r : P → E)
  /-- The entry of an honest event was proposed. -/
  | propH
  /-- The entry of an event without honest input was proposed. -/
  | propA

/-- **The simulator of the adversary port** for the transparent simulator `S`. On an event `e`
with honest input `p` it submits `p` on the honest port and keeps only the completion
`sp.rest e`, reads the pending input back with `peek`, runs `S` on the completed event,
proposes the resulting state and output, and answers with the honest `read`. On an event
without honest input it runs `S` on `e` and proposes the result, whose answer is the outer
output. Unexpected answers give the output `o₀`. -/
noncomputable def transSim (S : Sys σ E O) (sp : EvSplit E P)
    (hS : ∀ s e, SPComp.NoFail (S.step s e)) (o₀ : O) :
    MultiHybrid (σ × TPhase P E) E O (THonEv P ⊕ TAdvEv σ E O P) (Option O ⊕ TAdvOut P O) where
  init := (S.init, .idle)
  fuel := 3
  start t e :=
    match sp.hon e with
    | some p => SPComp.pure ((t.1, .sub (sp.rest e)), .inl (.inl (.submit p)))
    | none => SPComp.bind (S.step t.1 e) fun q =>
        SPComp.pure ((q.1, .propA), .inl (.inr (.propose (.inl e) q.2 q.1)))
  resume t o :=
    match t.2, o with
    | .sub r, _ => SPComp.pure ((t.1, .peek r), .inl (.inr .peek))
    | .peek r, .inr (.leak (some p)) => SPComp.bind (S.step t.1 (r p)) fun q =>
        SPComp.pure ((q.1, .propH), .inl (.inr (.propose (.inr r) q.2 q.1)))
    | .propH, _ => SPComp.pure ((t.1, .idle), .inl (.inl .read))
    | .propA, .inr (.out o') => SPComp.pure ((t.1, .idle), .inr o')
    | _, _ => SPComp.pure ((t.1, .idle), .inr o₀)
  finish t o :=
    match o with
    | .inl (some o') => SPComp.pure ((t.1, .idle), o')
    | _ => SPComp.pure ((t.1, .idle), o₀)
  start_noFail t e := by
    split
    · exact SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail (hS _ _) fun _ => SPComp.pure_noFail _
  resume_noFail t o := by
    split
    all_goals first
      | exact SPComp.pure_noFail _
      | exact Assumptions.SPComp.bind_noFail (hS _ _) fun _ => SPComp.pure_noFail _
  finish_noFail t o := by
    split <;> exact SPComp.pure_noFail _

/-- Decisions of the simulator are related to themselves. -/
theorem stepRel_portView_refl {O' : Type} (sp : EvSplit E P)
    (d : (THonEv P ⊕ TAdvEv σ E O P) ⊕ O') :
    PubView.StepRel (sp.view : PubView E O')
      (portView : PubView _ (Option O ⊕ TAdvOut P O)) d d := by
  rcases d with (g | g) | o
  · exact Sum.LiftRel.inl (Or.inl rfl)
  · exact Sum.LiftRel.inr rfl
  · rfl

/-- **The simulator of the adversary port is opaque** from `sp.view` to `portView`, with the
equality of states as unwinding relation: its decisions and outputs do not depend on honest
inputs. -/
theorem transSim_opaque (S : Sys σ E O) (sp : EvSplit E P)
    (hS : ∀ s e, SPComp.NoFail (S.step s e)) (o₀ : O) :
    (transSim S sp hS o₀).Opaque sp.view portView := by
  have hrefl : ∀ {α : Type} (c : SPComp ((σ × TPhase P E) × α))
      (Q : α → α → Prop), (∀ a, Q a a) →
      rHoare eqPre c c (fun r h r' h' => h = h' ∧ r.1 = r'.1 ∧ Q r.2 r'.2) := by
    intro α c Q hQ
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, hQ _⟩) (rHoare_refl _)
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl (⟨-, rfl⟩ | ⟨h1, h2, hr⟩)
    · exact hrefl _ _ (stepRel_portView_refl sp)
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp h2
      simp only [transSim, hp, hp']
      exact rHoare_ret fun _ _ h => ⟨h, by rw [hr], Sum.LiftRel.inl (Or.inr ⟨p, p', rfl, rfl⟩)⟩
  · rintro s _ o _ rfl rfl
    exact hrefl _ _ (stepRel_portView_refl sp)
  · rintro s _ o _ rfl rfl
    exact hrefl _ _ fun _ => rfl

/-- **The bundled simulator of the adversary port** for the transparent simulator `S`. -/
noncomputable def transSimulator (S : Sys σ E O) (sp : EvSplit E P)
    (hS : ∀ s e, SPComp.NoFail (S.step s e)) (o₀ : O) :
    Simulator E O (THonEv P ⊕ TAdvEv σ E O P) (Option O ⊕ TAdvOut P O) sp.view portView :=
  Simulator.ofMultiHybrid (transSim S sp hS o₀) (transSim_opaque S sp hS o₀)

/-! ## The bridge -/

/-- **The transparent ideal world is the simulator over the port system**: `ideal F S`
realizes `transSim S sp hS F.exploded` running with `F.ports` at distance `0`, through the
state map that adds the idle phase and the empty pending input. -/
theorem ideal_realizes_ports (F : TFunc σ E O) (S : Sys σ E O) (sp : EvSplit E P)
    (hS : ∀ s e, SPComp.NoFail (S.step s e)) :
    Realizes (ideal F S) ((transSim S sp hS F.exploded).withSub F.ports) (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ _
    (fun t => ((t.1, .idle), (t.2.1, t.2.2, (none : Option P)))) rfl fun t e => ?_
  obtain ⟨s, tr, x⟩ := t
  cases h : sp.hon e with
  | none =>
    simp [ideal, MultiHybrid.withSub, transSim, MultiHybrid.drive, TFunc.ports, TFunc.advSys,
      entryEv, h, SPComp.map, SPComp.bind_assoc]
  | some p =>
    have hr := sp.rest_hon e p h
    simp [ideal, MultiHybrid.withSub, transSim, MultiHybrid.drive, TFunc.ports, TFunc.advSys,
      TFunc.honSys, TFunc.readOut, entryEv, h, hr, SPComp.map, SPComp.bind_assoc]

/-- **From the transparent ideal world to realization behind an opaque simulator.** If `R`
realizes `ideal F S` with bound `b`, then `R` realizes the port system `F.ports` behind the
bundled simulator of the adversary port `transSimulator S sp hS F.exploded` with bound `b`. -/
theorem realizesSim_ports_of_realizes {R : Sys τ E O} (F : TFunc σ E O) (S : Sys σ E O)
    (sp : EvSplit E P) (hS : ∀ s e, SPComp.NoFail (S.step s e))
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes R (ideal F S) b) :
    RealizesSim R F.ports (transSimulator S sp hS F.exploded) b :=
  fun ζ => ((h.trans (ideal_realizes_ports F S sp hS)) ζ).mono fun _ => by simp

end CatCrypt.Crypto.UCTransparent

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentMulti
public import CatCryptCore.Relational.Rules

/-!
# Opaque simulators for transparent realization

A realization `Realizes R (π.withSub I) bound` with a multi-call simulator `π` folds the
adversary into the environment: the simulator receives every outer event, honest inputs
included, and produces every outer output. A simulator that runs a copy of `R` therefore
witnesses the statement whenever `R` does not fail. Opacity is the condition that turns it into
a security statement: the outputs of the simulator, up to the honest values they carry, depend
on its arguments only through their public parts (noninterference; Acay, Gancher, Recto and
Myers, CSF 2024, §VI).

A public view of an interface `(E, O)` is a pair of relations, on events and on outputs, that
relate two events or outputs differing only in honest values (`PubView`); the view of a family
of projections relates elements with equal projections (`PubView.ofProj`). Opacity is an
unwinding condition (Goguen and Meseguer) on a relation of states, holding initially and
preserved by every step from related states on related arguments, the steps coupled at equal
heaps (`rHoare eqPre`) with related results. A system is opaque for a view (`Sys.Opaque`); a
multi-call simulator is opaque from the view `W` of its subroutine to the view `V` of its outer
interface (`MultiHybrid.Opaque`), and running it over an opaque subroutine gives an opaque
system (`MultiHybrid.Opaque.withSub`).

A bundled simulator (`Simulator`) is a transformer of subroutine systems that carries opacity
in this form: it sends systems opaque for `W` to systems opaque for `V`. Simulators compose
(`Simulator.comp`), which is the composite `S₁.withSub (S₂.withSub I)` of the chains of
`MultiHybrid.realizes_compose`, and opaque multi-call simulators are simulators
(`Simulator.ofMultiHybrid`). `RealizesSim R I S bound` is realization of `I` by `R` behind the
simulator `S`.

## Main definitions

* `PubView E O`, `PubView.ofProj`: public views of an interface.
* `PubView.StepRel`: the relation on decisions of a simulator (a subroutine event or an outer
  output).
* `Sys.Unwinding`, `Sys.Opaque`: opacity of a system for a view.
* `MultiHybrid.Unwinding`, `MultiHybrid.Opaque`: opacity of a multi-call simulator.
* `MultiHybrid.idSim`: the simulator that forwards every event to its subroutine.
* `Simulator`, `Simulator.id`, `Simulator.comp`, `Simulator.ofMultiHybrid`: bundled opaque
  simulators.
* `RealizesSim R I S bound`: `Realizes R (S.withSub I) bound`.

## Main results

* `MultiHybrid.Opaque.withSub`: an opaque simulator over an opaque subroutine is opaque.
* `MultiHybrid.idSim_opaque`: the forwarding simulator is opaque for every view.
* `MultiHybrid.realizes_idSim_withSub`: the forwarding simulator over `X` realizes `X` at
  distance `0`.
* `Simulator.comp`: opacity is closed under sequential composition of simulators.
* `RealizesSim.toUCEmulatesCSim`: realization behind a simulator gives concrete UC emulation.
* `RealizesSim.compose_ofMultiHybrid`: realization behind an opaque multi-call simulator over
  `J`, and realization of `J` behind `S₂`, give realization behind the composite simulator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

/-! ## Public views -/

/-- A public view of the interface `(E, O)`: the relation `ev` on events and the relation `out`
on outputs relate two events or outputs that differ only in honest values. -/
structure PubView (E O : Type) where
  /-- Events with equal public parts. -/
  ev : E → E → Prop
  /-- Outputs with equal public parts (their adversary-directed parts, for outer outputs). -/
  out : O → O → Prop

namespace PubView

variable {E O EG OG LE LO : Type}

/-- The view of the projections `pe` of events and `po` of outputs: equal projections. -/
def ofProj (pe : E → LE) (po : O → LO) : PubView E O where
  ev e e' := pe e = pe e'
  out o o' := po o = po o'

/-- Two decisions of a simulator with outer view `V` and subroutine view `W` with equal public
parts: both subroutine events related by `W.ev`, or both outer outputs related by `V.out`. -/
def StepRel (V : PubView E O) (W : PubView EG OG) : EG ⊕ O → EG ⊕ O → Prop
  | .inl g, .inl g' => W.ev g g'
  | .inr o, .inr o' => V.out o o'
  | _, _ => False

end PubView

/-- An `rHoare` triple at the precondition `eqPre` conjoined with a fact `P`. -/
private theorem rHoare_eqPre_and {α β : Type} {P : Prop} {c₁ : SPComp α} {c₂ : SPComp β}
    {Ψ : RPost α β} (h : P → rHoare eqPre c₁ c₂ Ψ) :
    rHoare (fun h₁ h₂ => h₁ = h₂ ∧ P) c₁ c₂ Ψ :=
  fun h₁ h₂ hp => h hp.2 h₁ h₂ hp.1

/-! ## Opaque systems -/

namespace Sys

variable {τ E O : Type}

/-- The unwinding condition of the system `X` for the view `V` and the relation `T` on its
states: `T` holds initially, and steps from `T`-related states on events related by `V.ev` are
coupled at equal heaps into `T`-related states with outputs related by `V.out`. -/
structure Unwinding (X : Sys τ E O) (V : PubView E O) (T : τ → τ → Prop) : Prop where
  /-- The initial state is related to itself. -/
  init : T X.init X.init
  /-- A step on events with equal public parts. -/
  step : ∀ t t' e e', T t t' → V.ev e e' →
    rHoare eqPre (X.step t e) (X.step t' e')
      (fun p h p' h' => h = h' ∧ T p.1 p'.1 ∧ V.out p.2 p'.2)

/-- The system `X` is opaque for the view `V`: it has an unwinding relation. The public parts
of its outputs depend only on the public parts of its events. -/
def Opaque (X : Sys τ E O) (V : PubView E O) : Prop :=
  ∃ T, Unwinding X V T

/-- Opacity for a view gives opacity for every view that relates fewer events and more
outputs. -/
theorem Opaque.mono {X : Sys τ E O} {V V' : PubView E O} (h : X.Opaque V)
    (hev : ∀ e e', V'.ev e e' → V.ev e e') (hout : ∀ o o', V.out o o' → V'.out o o') :
    X.Opaque V' := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, hT.init, fun t t' e e' ht he => ?_⟩
  exact rHoare_conseq (fun _ _ hh => hh) (fun _ _ _ _ hp => ⟨hp.1, hp.2.1, hout _ _ hp.2.2⟩)
    (hT.step t t' e e' ht (hev e e' he))

end Sys

/-! ## Opaque multi-call simulators -/

namespace MultiHybrid

variable {σ τ E O EG OG : Type}

/-- The unwinding condition of the simulator `π` from the subroutine view `W` to the outer view
`V`, for the relation `R` on its states: `R` holds initially, and `start` (on events related by
`V.ev`), `resume` and `finish` (on answers related by `W.out`) from `R`-related states are
coupled at equal heaps into `R`-related states with decisions related by `V.StepRel W`
(`start`, `resume`) or outputs related by `V.out` (`finish`). -/
structure Unwinding (π : MultiHybrid σ E O EG OG) (V : PubView E O) (W : PubView EG OG)
    (R : σ → σ → Prop) : Prop where
  /-- The initial state is related to itself. -/
  init : R π.init π.init
  /-- `start` on outer events with equal public parts. -/
  start : ∀ s s' e e', R s s' → V.ev e e' →
    rHoare eqPre (π.start s e) (π.start s' e')
      (fun r h r' h' => h = h' ∧ R r.1 r'.1 ∧ V.StepRel W r.2 r'.2)
  /-- `resume` on subroutine answers with equal public parts. -/
  resume : ∀ s s' o o', R s s' → W.out o o' →
    rHoare eqPre (π.resume s o) (π.resume s' o')
      (fun r h r' h' => h = h' ∧ R r.1 r'.1 ∧ V.StepRel W r.2 r'.2)
  /-- `finish` on subroutine answers with equal public parts. -/
  finish : ∀ s s' o o', R s s' → W.out o o' →
    rHoare eqPre (π.finish s o) (π.finish s' o')
      (fun r h r' h' => h = h' ∧ R r.1 r'.1 ∧ V.out r.2 r'.2)

/-- The simulator `π` is opaque from the subroutine view `W` to the outer view `V`: it has an
unwinding relation. Its outer outputs and the subroutine events it chooses, up to the honest
values they carry, depend only on the public parts of its arguments. -/
def Opaque (π : MultiHybrid σ E O EG OG) (V : PubView E O) (W : PubView EG OG) : Prop :=
  ∃ R, Unwinding π V W R

/-- The rest of one activation of a simulator with the unwinding relation `R` over a subroutine
with the unwinding relation `T`, from related states and related decisions: related final
states and outer outputs related by `V.out`. -/
theorem Unwinding.drive {π : MultiHybrid σ E O EG OG} {V : PubView E O} {W : PubView EG OG}
    {R : σ → σ → Prop} (hπ : Unwinding π V W R) {X : Sys τ EG OG} {T : τ → τ → Prop}
    (hX : Sys.Unwinding X W T) :
    ∀ (n : ℕ) (s s' : σ) (d d' : EG ⊕ O) (t t' : τ), R s s' → V.StepRel W d d' → T t t' →
      rHoare eqPre (π.drive X n s d t) (π.drive X n s' d' t')
        (fun p h p' h' => h = h' ∧ R p.1 p'.1 ∧ T p.2.1 p'.2.1 ∧ V.out p.2.2 p'.2.2) := by
  intro n
  induction n with
  | zero =>
    rintro s s' (g | o) (g' | o') t t' hs hd ht
    · refine rHoare_bind
        (Ψ := fun q h q' h' => h = h' ∧ T q.1 q'.1 ∧ W.out q.2 q'.2)
        (hX.step t t' g g' ht hd) fun q q' => ?_
      refine rHoare_eqPre_and (P := T q.1 q'.1 ∧ W.out q.2 q'.2) fun hq => ?_
      refine rHoare_bind
        (Ψ := fun r h r' h' => h = h' ∧ R r.1 r'.1 ∧ V.out r.2 r'.2)
        (hπ.finish s s' q.2 q'.2 hs hq.2) fun r r' => ?_
      exact rHoare_eqPre_and (P := R r.1 r'.1 ∧ V.out r.2 r'.2) fun hr =>
        rHoare_ret fun _ _ e => ⟨e, hr.1, hq.1, hr.2⟩
    · exact (hd : False).elim
    · exact (hd : False).elim
    · exact rHoare_ret fun _ _ e => ⟨e, hs, ht, hd⟩
  | succ n ih =>
    rintro s s' (g | o) (g' | o') t t' hs hd ht
    · refine rHoare_bind
        (Ψ := fun q h q' h' => h = h' ∧ T q.1 q'.1 ∧ W.out q.2 q'.2)
        (hX.step t t' g g' ht hd) fun q q' => ?_
      refine rHoare_eqPre_and (P := T q.1 q'.1 ∧ W.out q.2 q'.2) fun hq => ?_
      refine rHoare_bind
        (Ψ := fun r h r' h' => h = h' ∧ R r.1 r'.1 ∧ V.StepRel W r.2 r'.2)
        (hπ.resume s s' q.2 q'.2 hs hq.2) fun r r' => ?_
      exact rHoare_eqPre_and (P := R r.1 r'.1 ∧ V.StepRel W r.2 r'.2) fun hr =>
        ih r.1 r'.1 r.2 r'.2 q.1 q'.1 hr.1 hr.2 hq.1
    · exact (hd : False).elim
    · exact (hd : False).elim
    · exact rHoare_ret fun _ _ e => ⟨e, hs, ht, hd⟩

/-- A simulator with the unwinding relation `R` over a subroutine with the unwinding relation
`T` composes to a system with the unwinding relation `R × T`. -/
theorem Unwinding.withSub {π : MultiHybrid σ E O EG OG} {V : PubView E O} {W : PubView EG OG}
    {R : σ → σ → Prop} (hπ : Unwinding π V W R) {X : Sys τ EG OG} {T : τ → τ → Prop}
    (hX : Sys.Unwinding X W T) :
    Sys.Unwinding (π.withSub X) V (fun a b => R a.1 b.1 ∧ T a.2 b.2) := by
  refine ⟨⟨hπ.init, hX.init⟩, fun s s' e e' hs he => ?_⟩
  dsimp only [MultiHybrid.withSub]
  refine rHoare_bind (Ψ := fun (r : σ × (EG ⊕ O)) h (r' : σ × (EG ⊕ O)) h' =>
      h = h' ∧ R r.1 r'.1 ∧ V.StepRel W r.2 r'.2)
    (hπ.start _ _ e e' hs.1 he) fun r r' => ?_
  refine rHoare_eqPre_and (P := R r.1 r'.1 ∧ V.StepRel W r.2 r'.2) fun hr => ?_
  refine rHoare_bind (Ψ := fun p h p' h' =>
      h = h' ∧ R p.1 p'.1 ∧ T p.2.1 p'.2.1 ∧ V.out p.2.2 p'.2.2)
    (hπ.drive hX π.fuel r.1 r'.1 r.2 r'.2 s.2 s'.2 hr.1 hr.2 hs.2) fun p p' => ?_
  exact rHoare_eqPre_and (P := R p.1 p'.1 ∧ T p.2.1 p'.2.1 ∧ V.out p.2.2 p'.2.2)
    fun hp => rHoare_ret fun _ _ e => ⟨e, ⟨hp.1, hp.2.1⟩, hp.2.2⟩

/-- **Opacity over a subroutine**: an opaque simulator over an opaque subroutine is an opaque
system. -/
theorem Opaque.withSub {π : MultiHybrid σ E O EG OG} {V : PubView E O} {W : PubView EG OG}
    (hπ : π.Opaque V W) {X : Sys τ EG OG} (hX : X.Opaque W) : (π.withSub X).Opaque V := by
  obtain ⟨R, hR⟩ := hπ
  obtain ⟨T, hT⟩ := hX
  exact ⟨_, hR.withSub hT⟩

/-- The simulator that forwards every outer event to its subroutine and returns the answer as
the outer output, in one call per activation. -/
noncomputable def idSim (E O : Type) : MultiHybrid Unit E O E O where
  init := ()
  fuel := 0
  start _ e := SPComp.pure ((), .inl e)
  resume _ o := SPComp.pure ((), .inr o)
  finish _ o := SPComp.pure ((), o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The forwarding simulator is opaque from `V` to `V`, for every view `V`. -/
theorem idSim_opaque (V : PubView E O) : (idSim E O).Opaque V V := by
  refine ⟨fun _ _ => True, trivial, ?_, ?_, ?_⟩
  · intro s s' e e' _ he
    exact rHoare_ret fun _ _ h => ⟨h, trivial, he⟩
  · intro s s' o o' _ ho
    exact rHoare_ret fun _ _ h => ⟨h, trivial, ho⟩
  · intro s s' o o' _ ho
    exact rHoare_ret fun _ _ h => ⟨h, trivial, ho⟩

/-- One step of the forwarding simulator over `X` is one step of `X`. -/
theorem idSim_withSub_step (X : Sys τ E O) (t : Unit × τ) (e : E) :
    ((idSim E O).withSub X).step t e =
      SPComp.map (fun p => (((), p.1), p.2)) (X.step t.2 e) := by
  simp [withSub, idSim, drive, SPComp.map, SPComp.pure_bind]

/-- The forwarding simulator over `X` realizes `X`, and `X` realizes it, at distance `0`. -/
theorem realizes_idSim_withSub (X : Sys τ E O) :
    Realizes X ((idSim E O).withSub X) (fun _ _ => 0) :=
  realizes_zero_of_stepMap X _ (fun t => ((), t)) rfl fun t e => by
    rw [idSim_withSub_step]

end MultiHybrid

/-! ## Bundled simulators -/

/-- A simulator from the subroutine interface `(EG, OG)` with view `W` to the outer interface
`(E, O)` with view `V`: a transformer of subroutine systems, with state `St τ` over a
subroutine with state `τ`, that sends systems opaque for `W` to systems opaque for `V`. -/
structure Simulator (E O EG OG : Type) (V : PubView E O) (W : PubView EG OG) : Type 1 where
  /-- The state of the simulator over a subroutine with state `τ`. -/
  St : Type → Type
  /-- The simulator running with the subroutine system `X`. -/
  withSub : {τ : Type} → Sys τ EG OG → Sys (St τ) E O
  /-- Opacity: over a subroutine opaque for `W`, the system is opaque for `V`. -/
  isOpaque : ∀ {τ : Type} (X : Sys τ EG OG), X.Opaque W → (withSub X).Opaque V

namespace Simulator

variable {E O EM OM EG OG : Type} {V : PubView E O} {U : PubView EM OM} {W : PubView EG OG}

/-- The identity simulator: the subroutine itself. -/
def id (E O : Type) (V : PubView E O) : Simulator E O E O V V where
  St τ := τ
  withSub X := X
  isOpaque _ h := h

/-- **Sequential composition of simulators**: `S₁` running with `S₂` running with the
subroutine. Opacity is closed under it. -/
def comp (S₁ : Simulator E O EM OM V U) (S₂ : Simulator EM OM EG OG U W) :
    Simulator E O EG OG V W where
  St τ := S₁.St (S₂.St τ)
  withSub X := S₁.withSub (S₂.withSub X)
  isOpaque X h := S₁.isOpaque _ (S₂.isOpaque X h)

/-- An opaque multi-call simulator as a simulator. -/
noncomputable def ofMultiHybrid {σ : Type} (π : MultiHybrid σ E O EG OG) (h : π.Opaque V W) :
    Simulator E O EG OG V W where
  St τ := σ × τ
  withSub X := π.withSub X
  isOpaque _ hX := h.withSub hX

/-- A simulator for a view, as a simulator for a view of the subroutine that relates more
events and fewer answers and an outer view that relates fewer events and more outputs. -/
def mono (S : Simulator E O EG OG V W) {V' : PubView E O} {W' : PubView EG OG}
    (hVev : ∀ e e', V'.ev e e' → V.ev e e') (hVout : ∀ o o', V.out o o' → V'.out o o')
    (hWev : ∀ g g', W.ev g g' → W'.ev g g') (hWout : ∀ o o', W'.out o o' → W.out o o') :
    Simulator E O EG OG V' W' where
  St := S.St
  withSub := S.withSub
  isOpaque X h := (S.isOpaque X (h.mono hWev hWout)).mono hVev hVout

end Simulator

/-! ## Realization behind a simulator -/

/-- `R` realizes `I` behind the simulator `S` with bound `bound`: `R` realizes `S` running with
`I`. -/
def RealizesSim {τ υ E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    (R : Sys τ E O) (I : Sys υ EG OG) (S : Simulator E O EG OG V W)
    (bound : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞) : Prop :=
  Realizes R (S.withSub I) bound

namespace RealizesSim

variable {τ υ υ' σ E O EM OM EG OG : Type} {V : PubView E O} {U : PubView EM OM}
  {W : PubView EG OG}

/-- Realization behind a simulator gives concrete UC emulation (composition plumbing) in the
sense of `UCConcrete.UCEmulatesCSim`, in the form of `Realizes.toUCEmulatesCSim`. -/
theorem toUCEmulatesCSim {R : Sys τ E O} {I : Sys υ EG OG} {S : Simulator E O EG OG V W}
    {bound : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : RealizesSim R I S bound)
    (ζ Λ : Type) :
    UCEmulatesCSim ⟨Strat ζ E O, ζ, Empty, Empty, Λ⟩
      (fun s => SPComp.bind (view R s) fun z => SPComp.pure (Sum.inl z))
      (fun s => SPComp.bind (view (S.withSub I) s) fun z => SPComp.pure (Sum.inl z)) _root_.id
      (fun A Z => bound ζ (Env.postcomp (fun z => SPComp.pure (Sum.inl z))
        (Env.postcomp (mapSum SPComp.pure A) Z))) :=
  Realizes.toUCEmulatesCSim h ζ Λ

/-- **Composition behind simulators** (composition plumbing). If `R` realizes `J` behind the
opaque multi-call simulator `π` with bound `b₁`, and `J` realizes `I` behind `S₂` with bound
`b₂`, with `J` and `S₂` running with `I` idle at `idle`, then `R` realizes `I` behind the
composite simulator with bound `b₁` plus `b₂` at the reduced environment. -/
theorem compose_ofMultiHybrid {R : Sys τ E O} {J : Sys υ EM OM} {I : Sys υ' EG OG}
    (π : MultiHybrid σ E O EM OM) (hπ : π.Opaque V U) (S₂ : Simulator EM OM EG OG U W)
    (idle : EM) (oJ oI : OM) (hJ : MultiHybrid.IdleAt J idle oJ)
    (hI : MultiHybrid.IdleAt (S₂.withSub I) idle oI)
    {b₁ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {b₂ : (ζ : Type) → Env (Strat ζ EM OM) ζ → ℝ≥0∞}
    (h₁ : RealizesSim R J (Simulator.ofMultiHybrid π hπ) b₁) (h₂ : RealizesSim J I S₂ b₂) :
    RealizesSim R I ((Simulator.ofMultiHybrid π hπ).comp S₂)
      (fun ζ Z => b₁ ζ Z + b₂ (MultiHybrid.RState σ ζ EM O) (π.reduceEnv idle Z)) := by
  have hsub := MultiHybrid.realizes_compose π idle oJ oI J (S₂.withSub I)
    (π.withSub (S₂.withSub I)) hJ hI (fun _ _ => 0) b₂ (fun _ => DistC.refl _) h₂
  intro ζ Z
  have h := Realizes.trans h₁ hsub ζ Z
  simp only [add_zero] at h
  exact h

end RealizesSim

end CatCrypt.Crypto.UCTransparent

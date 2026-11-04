/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.TraceEquiv
public import CatCryptCore.Crypto.UCLoopbackObservationBridge
public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.UCOracleGame

/-!
# Local rewriting of reactive systems up to trace equivalence

Trace equivalence `Sys.TraceEq` (`TraceEquiv.lean`) is the exact view equivalence of reactive
systems: two systems are trace equivalent exactly when they have equal views against every
environment (`Sys.traceEq_iff_view_eq`), equivalently when each realizes the other at bound `0`
(`Sys.traceEq_iff_realizes_zero`). This file makes it a rewriting relation. It is an equivalence
relation with `Trans` instances, so that a hop between two systems is written as a `calc` chain of
local rewrites, each justified by a law of this file or by a finer relation, and converted into a
realization at the ends (`Sys.TraceEq.realizes_left`, `Sys.TraceEq.realizes_right`). A `calc`
chain cannot chain `Realizes` itself, whose bound is its last argument.

The finer relations embed into trace equivalence: step maps on an invariant (`StepMapOn`, and
the unbundled form of `view_eq_of_stepMap`), step equivalence (`StepEq`), exact coupling
bisimulations (`UCCoupling.CouplingBisim`) and testing equivalence (`EmulatesΩ`). Trace
equivalence is a congruence for every open system (`Open.withSub`), hence for multi-call hybrids
over subroutines idle at a common event, for the parallel composition, the loopback and the
relabelling of ports.

The invariant of a step map is preserved when it holds at every possible outcome of a step
(`IsOutcome`). The possible outcomes of a point mass, a map and a bind are computed by the simp
lemmas `isOutcome_pure_iff`, `isOutcome_map_iff` and `isOutcome_bind_pure_iff`, and the
universal statements over them by `forall_isOutcome_pure`, `forall_isOutcome_map` and
`forall_isOutcome_bind`.

## Main results

* `Sys.traceEq_equivalence`, `Sys.TraceEq.trans` and the `Trans` instance: trace equivalence as a
  `calc` relation, written `R ≈ₜ I` (scoped in `CatCrypt.Crypto.UCTransparent.Sys`).
* `Sys.traceEq_iff_view_eq`: trace equivalence is equality of all views.
* `Sys.StepMapOn.traceEq`, `Sys.traceEq_of_stepMap`, `Sys.StepEq.traceEq`,
  `UCCoupling.CouplingBisim.traceEq`, `UCLoopbackObservation.EmulatesΩ.traceEq`: the bridges.
* `Sys.TraceEq.realizes_left`, `Sys.TraceEq.realizes_right`, `Sys.TraceEq.realizesSim_left`,
  `Sys.TraceEq.realizesSim_right`: rewriting either side of a realization.
* `Sys.TraceEq.openWithSub`, `Sys.TraceEq.withSub`, `Sys.TraceEq.par`, `Sys.TraceEq.loopback`,
  `Sys.TraceEq.mapPorts`: congruences.
* `Sys.traceEq_of_step_eq_on`, `Sys.traceEq_of_fst`, `Sys.traceEq_of_equiv`: equal steps on an
  invariant, an unused state component, renamed states.
* `MultiHybrid.withSub_step_of_fuel_eq_zero`: the step of a hybrid that makes one call.
* `KeyedSys.traceEq_lazy`: moving the draw of a key to its first use; `KeyedSys.lazy_pres`:
  invariants of a lazily keyed system.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCLoopbackObservation
open scoped ENNReal

/-! ## Possible outcomes -/

section Outcome

variable {α β : Type}

/-- The possible outcomes of a point mass: its value. -/
@[simp, grind =] theorem isOutcome_pure_iff {a b : α} : IsOutcome (SPComp.pure a) b ↔ a = b := by
  refine ⟨isOutcome_pure, fun h => ⟨Heap.empty, Heap.empty, ?_⟩⟩
  subst h
  simp [SPComp.pure_def, SDistr.pure, PMF.pure_apply]

/-- The possible outcomes of a map: the images of the possible outcomes. -/
@[simp, grind =] theorem isOutcome_map_iff {c : SPComp α} {f : α → β} {b : β} :
    IsOutcome (SPComp.map f c) b ↔ ∃ a, IsOutcome c a ∧ f a = b := by
  refine ⟨fun h => ?_, fun ⟨a, ha, hb⟩ => hb ▸ isOutcome_map f ha⟩
  obtain ⟨a, ha, hb⟩ := isOutcome_bind h
  exact ⟨a, ha, isOutcome_pure hb⟩

/-- The possible outcomes of a bind with a point-mass continuation. -/
@[simp] theorem isOutcome_bind_pure_iff {c : SPComp α} {f : α → β} {b : β} :
    IsOutcome (SPComp.bind c fun a => SPComp.pure (f a)) b ↔ ∃ a, IsOutcome c a ∧ f a = b :=
  isOutcome_map_iff

/-- A property of every possible outcome of a point mass is a property of its value. -/
@[simp] theorem forall_isOutcome_pure {P : α → Prop} {a : α} :
    (∀ b, IsOutcome (SPComp.pure a) b → P b) ↔ P a := by
  simp

/-- A property of every possible outcome of a map is a property of the image of every possible
outcome. -/
theorem forall_isOutcome_map {P : β → Prop} {c : SPComp α} {f : α → β} :
    (∀ b, IsOutcome (SPComp.map f c) b → P b) ↔ ∀ a, IsOutcome c a → P (f a) := by
  simp

/-- A property of the possible outcomes of every continuation is a property of the possible
outcomes of the bind. The converse fails: a continuation may run from a heap the head never
reaches. -/
theorem forall_isOutcome_bind {P : β → Prop} {c : SPComp α} {f : α → SPComp β}
    (h : ∀ a, IsOutcome c a → ∀ b, IsOutcome (f a) b → P b) :
    ∀ b, IsOutcome (SPComp.bind c f) b → P b := fun _ hb => by
  obtain ⟨a, ha, hab⟩ := isOutcome_bind hb
  exact h a ha _ hab

attribute [grind →] isOutcome_bind

end Outcome

namespace Sys

variable {τ υ ρ τ' υ' E O EG OG X : Type}

/-! ## Trace equivalence as a `calc` relation -/

@[inherit_doc] scoped infix:50 " ≈ₜ " => TraceEq

/-- Trace equivalence is reflexive. -/
@[refl] theorem TraceEq.refl (R : Sys τ E O) : TraceEq R R := fun _ => rfl

/-- Trace equivalence is symmetric. -/
@[symm] theorem TraceEq.symm {R : Sys τ E O} {I : Sys υ E O} (h : TraceEq R I) : TraceEq I R :=
  fun hs => (h hs).symm

/-- Trace equivalence is transitive. -/
theorem TraceEq.trans {R : Sys τ E O} {I : Sys υ E O} {J : Sys ρ E O} (h₁ : TraceEq R I)
    (h₂ : TraceEq I J) : TraceEq R J :=
  fun hs => (h₁ hs).trans (h₂ hs)

/-- Trace equivalence of the systems with a given state type is an equivalence relation. -/
theorem traceEq_equivalence : Equivalence (@TraceEq τ τ E O) :=
  ⟨TraceEq.refl, TraceEq.symm, TraceEq.trans⟩

instance : @Trans (Sys τ E O) (Sys υ E O) (Sys ρ E O) TraceEq TraceEq TraceEq :=
  ⟨TraceEq.trans⟩

/-- Equal systems are trace equivalent. -/
theorem TraceEq.of_eq {R R' : Sys τ E O} (h : R = R') : TraceEq R R' :=
  h ▸ TraceEq.refl R

/-- **Trace equivalence is equality of views.** -/
theorem traceEq_iff_view_eq {R : Sys τ E O} {I : Sys υ E O} :
    TraceEq R I ↔ ∀ (ζ : Type) (Z : Strat ζ E O), view R Z = view I Z :=
  traceEq_iff_realizes_zero.trans realizes_zero_iff_view_eq

/-- Trace-equivalent systems realize one another at distance `0`. -/
theorem TraceEq.realizes {R : Sys τ E O} {I : Sys υ E O} (h : TraceEq R I) :
    Realizes R I (fun _ _ => 0) :=
  traceEq_iff_realizes_zero.mp h

/-! ## Bridges from the finer relations -/

/-- A step map on an invariant gives trace equivalence. -/
theorem StepMapOn.traceEq {R : Sys τ E O} {I : Sys υ E O} {Inv : τ → Prop} {f : τ → υ}
    (h : StepMapOn R I Inv f) : TraceEq R I :=
  traceEq_iff_realizes_zero.mpr h.realizes

/-- A state map that sends the initial state to the initial state and commutes with single
steps gives trace equivalence (`view_eq_of_stepMap`). -/
theorem traceEq_of_stepMap (R : Sys τ E O) (I : Sys υ E O) (f : τ → υ) (hinit : f R.init = I.init)
    (hstep : ∀ t e, SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = I.step (f t) e) :
    TraceEq R I :=
  traceEq_iff_view_eq.mpr fun _ => view_eq_of_stepMap R I f hinit hstep

/-- Step-equivalent bundled systems are trace equivalent. -/
theorem StepEq.traceEq {A B : SysObj E O} (h : StepEq A B) : TraceEq A.sys B.sys :=
  traceEq_iff_realizes_zero.mpr h.realizes.1

/-! ## Rewriting a realization -/

/-- The first system of a realization may be replaced by a trace-equivalent one. -/
theorem TraceEq.realizes_left {R : Sys τ E O} {R' : Sys τ' E O} {I : Sys υ E O}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : TraceEq R R') (hR : Realizes R I b) :
    Realizes R' I b := fun ζ => by
  rw [← funext (h.view_eq (ζ := ζ))]
  exact hR ζ

/-- The second system of a realization may be replaced by a trace-equivalent one. -/
theorem TraceEq.realizes_right {R : Sys τ E O} {I : Sys υ E O} {I' : Sys υ' E O}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : TraceEq I I') (hR : Realizes R I b) :
    Realizes R I' b := fun ζ => by
  rw [← funext (h.view_eq (ζ := ζ))]
  exact hR ζ

/-- The real system of a realization behind a simulator may be replaced by a trace-equivalent
one. -/
theorem TraceEq.realizesSim_left {V : PubView E O} {W : PubView EG OG} {R : Sys τ E O}
    {R' : Sys τ' E O} {I : Sys υ EG OG} {S : Simulator E O EG OG V W}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : TraceEq R R')
    (hR : RealizesSim R I S b) : RealizesSim R' I S b :=
  h.realizes_left hR

/-- The simulated system of a realization behind a simulator may be replaced by a
trace-equivalent one. -/
theorem TraceEq.realizesSim_right {V : PubView E O} {W : PubView EG OG} {R : Sys τ E O}
    {I : Sys υ EG OG} {I' : Sys υ' EG OG} {S : Simulator E O EG OG V W}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : TraceEq (S.withSub I) (S.withSub I'))
    (hR : RealizesSim R I S b) : RealizesSim R I' S b :=
  h.realizes_right hR

/-- A realization at distance `0` of a system trace equivalent to the simulated one. -/
theorem TraceEq.realizesSim {V : PubView E O} {W : PubView EG OG} {R : Sys τ E O}
    {I : Sys υ EG OG} {S : Simulator E O EG OG V W} (h : TraceEq R (S.withSub I)) :
    RealizesSim R I S (fun _ _ => 0) :=
  h.realizes

/-! ## Congruences -/

/-- **Trace equivalence under an open system**, for admissible subroutines. -/
theorem TraceEq.openWithSub (P : Open E O EG OG) {X : Sys τ EG OG} {Y : Sys υ EG OG}
    (hX : P.Adm X) (hY : P.Adm Y) (h : TraceEq X Y) : TraceEq (P.withSub X) (P.withSub Y) :=
  traceEq_iff_realizes_zero.mpr (P.realizes_withSub hX hY h.realizes)

/-- Trace equivalence under a multi-call hybrid, for subroutines idle at a common event. -/
theorem TraceEq.withSub {σ : Type} (π : MultiHybrid σ E O EG OG) {X : Sys τ EG OG}
    {Y : Sys υ EG OG} (idle : EG) {oX oY : OG} (hX : MultiHybrid.IdleAt X idle oX)
    (hY : MultiHybrid.IdleAt Y idle oY) (h : TraceEq X Y) :
    TraceEq (π.withSub X) (π.withSub Y) :=
  h.openWithSub (Open.ofMultiHybrid π idle) ⟨oX, hX⟩ ⟨oY, hY⟩

/-- Trace equivalence under the relabelling of ports. -/
theorem TraceEq.mapPorts {E' O' : Type} {X : Sys τ EG OG} {Y : Sys υ EG OG} (h : TraceEq X Y)
    (fe : E' → EG) (fo : OG → O') : TraceEq (X.mapPorts fe fo) (Y.mapPorts fe fo) :=
  h.openWithSub (Open.mapPorts fe fo) trivial trivial

/-- Trace equivalence under the loopback, for systems idle at a common event, for every fuel and
cut-off map. -/
theorem TraceEq.loopback {R : Sys τ (E ⊕ X) (O ⊕ X)} {I : Sys υ (E ⊕ X) (O ⊕ X)}
    (idle : E ⊕ X) {oR oI : O ⊕ X} (hR : MultiHybrid.IdleAt R idle oR)
    (hI : MultiHybrid.IdleAt I idle oI) (h : TraceEq R I) (n : ℕ) (cut : X → O) :
    TraceEq (R.loopback n cut) (I.loopback n cut) :=
  traceEq_iff_realizes_zero.mpr (h.realizes.loopback idle oR oI hR hI n cut)

/-- Trace equivalence under the parallel composition, for lossless systems `Y` and `X'` and
systems idle at `idleL` on the left and at `idleR` on the right. -/
theorem TraceEq.par {E' O' : Type} {X : Sys τ E O} {X' : Sys τ' E O} {Y : Sys υ E' O'}
    {Y' : Sys υ' E' O'} (hY : ∀ u e, SPComp.NoFail (Y.step u e))
    (hX' : ∀ t e, SPComp.NoFail (X'.step t e)) (idleL : E) (idleR : E') {oX oX' : O}
    {oY oY' : O'} (hXi : MultiHybrid.IdleAt X idleL oX) (hX'i : MultiHybrid.IdleAt X' idleL oX')
    (hYi : MultiHybrid.IdleAt Y idleR oY) (hY'i : MultiHybrid.IdleAt Y' idleR oY')
    (hXX : TraceEq X X') (hYY : TraceEq Y Y') : TraceEq (X.par Y) (X'.par Y') :=
  traceEq_iff_realizes_zero.mpr fun ζ Z =>
    (realizes_par hY hX' idleL idleR hXi hX'i hYi hY'i hXX.realizes hYY.realizes ζ Z).trans
      (by simp)

/-! ## Laws on systems as written -/

/-- **Equal steps on an invariant.** Two systems with the same initial state whose steps agree on
the states of an invariant that holds initially and at every possible outcome of a step from a
state satisfying it are trace equivalent. -/
theorem traceEq_of_step_eq_on (R I : Sys τ E O) (Inv : τ → Prop) (hinit : R.init = I.init)
    (hInv : Inv R.init) (hpres : ∀ t e, Inv t → ∀ q, IsOutcome (R.step t e) q → Inv q.1)
    (hstep : ∀ t e, Inv t → R.step t e = I.step t e) : TraceEq R I :=
  StepMapOn.traceEq (f := id)
    { init_inv := hInv
      init_map := hinit
      pres := hpres
      step := fun t e ht => by simp [SPComp.map, ← hstep t e ht, SPComp.bind_pure] }

/-- **An unused state component.** A system on states `τ × υ` whose steps, read on the first
component, are those of `S` from the first component, is trace equivalent to `S`. -/
theorem traceEq_of_fst (R : Sys (τ × υ) E O) (S : Sys τ E O) (hinit : R.init.1 = S.init)
    (hstep : ∀ t u e, SPComp.map (fun p => (p.1.1, p.2)) (R.step (t, u) e) = S.step t e) :
    TraceEq R S :=
  traceEq_of_stepMap R S Prod.fst hinit fun t e => hstep t.1 t.2 e

/-- **Renamed states.** A system whose steps are those of `R` on states renamed by the bijection
`φ` is trace equivalent to `R`. -/
theorem traceEq_of_equiv (R : Sys τ E O) (I : Sys υ E O) (φ : τ ≃ υ) (hinit : I.init = φ R.init)
    (hstep : ∀ u e, I.step u e = SPComp.map (fun p => (φ p.1, p.2)) (R.step (φ.symm u) e)) :
    TraceEq R I :=
  traceEq_of_stepMap R I φ hinit.symm fun t e => by simp [hstep]

end Sys

namespace MultiHybrid

variable {σ τ E O EG OG : Type}

/-- **The step of a hybrid that makes one call.** With fuel `0`, an activation of `π.withSub X`
starts `π`, and either outputs at once or makes one call of `X` and finishes `π` on its answer. -/
theorem withSub_step_of_fuel_eq_zero (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (h : π.fuel = 0) (t : σ × τ) (e : E) :
    (π.withSub X).step t e = SPComp.bind (π.start t.1 e) fun r =>
      Sum.elim (fun g => SPComp.bind (X.step t.2 g) fun q =>
          SPComp.map (fun r' => ((r'.1, q.1), r'.2)) (π.finish r.1 q.2))
        (fun o => SPComp.pure ((r.1, t.2), o)) r.2 := by
  simp only [withSub, h]
  congr 1
  funext r
  obtain ⟨s, g | o⟩ := r
  · simp [drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · simp [drive, SPComp.pure_bind]

end MultiHybrid

end CatCrypt.Crypto.UCTransparent

namespace CatCrypt.Crypto.UCCoupling

open CatCrypt.Crypto.UCTransparent

variable {τ υ E O : Type}

/-- A coupling bisimulation gives trace equivalence. -/
theorem CouplingBisim.traceEq {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) : Sys.TraceEq R I :=
  Sys.traceEq_iff_realizes_zero.mpr (realizes_zero_of_coupling h).1

end CatCrypt.Crypto.UCCoupling

namespace CatCrypt.Crypto.UCLoopbackObservation

open CatCrypt.Crypto.UCTransparent

variable {τ υ E O : Type}

/-- Testing equivalence of the open systems of two systems gives trace equivalence. -/
theorem EmulatesΩ.traceEq {R : Sys τ E O} {I : Sys υ E O}
    (h : EmulatesΩ (sysObj R) (sysObj I)) : Sys.TraceEq R I :=
  Sys.traceEq_iff_realizes_zero.mpr h.realizes

end CatCrypt.Crypto.UCLoopbackObservation

namespace CatCrypt.Crypto.UCTransparent.KeyedSys

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.NonUniform

variable {K τ E O : Type}

/-- **Moving a draw to its first use.** Two keyed systems with the same initial state and the
same keyed steps, each of whose activations that do not read the key step as without it, are
trace equivalent when their keys are drawn lazily from the same distribution, whatever the
activations at which each reads the key: both have the view of the average over the key of the
system with that key (`KeyedSys.view_lazy`). -/
theorem traceEq_lazy (S S' : KeyedSys K τ E O) (μ : PMF K) (hinit : S.init = S'.init)
    (hstep : S.step = S'.step)
    (hind : ∀ k t e, S.uses t e = false → S.step k t e = S.step₀ t e)
    (hind' : ∀ k t e, S'.uses t e = false → S'.step k t e = S'.step₀ t e) :
    Sys.TraceEq (S.lazy μ) (S'.lazy μ) := by
  refine Sys.traceEq_iff_view_eq.mpr fun ζ Z => ?_
  rw [view_lazy S μ hind, view_lazy S' μ hind']
  have hk : ∀ k, S.withKey k = S'.withKey k := fun k => by
    simp only [withKey, hinit, hstep]
  simp only [hk]

/-- **Invariants of a lazily keyed system.** An invariant `Inv` of the states with an optional
key holds at every possible outcome of a step of `S.lazy μ` from a state satisfying it when it
does so with the key, at every key for an activation without the key that reads it, and without
the key for an activation that does not read it. -/
theorem lazy_pres (S : KeyedSys K τ E O) (μ : PMF K) (Inv : Option K × τ → Prop)
    (hsome : ∀ k t e, Inv (some k, t) → ∀ q, IsOutcome (S.step k t e) q → Inv (some k, q.1))
    (huses : ∀ t e, Inv (none, t) → S.uses t e = true →
      ∀ k q, IsOutcome (S.step k t e) q → Inv (some k, q.1))
    (hnone : ∀ t e, Inv (none, t) → S.uses t e = false →
      ∀ q, IsOutcome (S.step₀ t e) q → Inv (none, q.1)) :
    ∀ t e, Inv t → ∀ q, IsOutcome ((S.lazy μ).step t e) q → Inv q.1 := by
  rintro ⟨_ | k, t⟩ e hI q hq
  · cases hu : S.uses t e
    · rw [lazy_step_none_of_not_uses S μ hu, isOutcome_bind_pure_iff] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      exact hnone t e hI hu p hp
    · rw [lazy_step_none_of_uses S μ hu] at hq
      obtain ⟨k, -, hq⟩ := isOutcome_bind hq
      obtain ⟨p, hp, rfl⟩ := isOutcome_bind_pure_iff.mp hq
      exact huses t e hI hu k p hp
  · simp only [lazy, lazyStep, isOutcome_bind_pure_iff] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact hsome k t e hI p hp

end CatCrypt.Crypto.UCTransparent.KeyedSys

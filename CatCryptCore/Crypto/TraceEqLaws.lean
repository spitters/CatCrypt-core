/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.TraceEquiv
public import CatCryptCore.Crypto.UCLoopbackObservationBridge
public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.UCDelayedDraw

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
(`IsOutcome`); the possible outcomes of point masses, maps and binds are computed by the lemmas
of `CatCryptCore.Crypto.UCFeedbackLaws`.

## Main results

* `Sys.traceEq_equivalence`, `Sys.TraceEq.trans` and the `Trans` instance: trace equivalence as a
  `calc` relation, written `R ≈ₜ I` (scoped in `CatCrypt.Crypto.UCTransparent.Sys`).
* `Sys.traceEq_iff_view_eq`: trace equivalence is equality of all views.
* `Sys.StepMapOn.traceEq`, `Sys.traceEq_of_stepMap`, `Sys.StepEq.traceEq`,
  `UCCoupling.CouplingBisim.traceEq`, `UCLoopbackObservation.EmulatesΩ.traceEq`: the bridges.
* `Sys.TraceEq.realizes_left`, `Sys.TraceEq.realizes_right`: rewriting either side of a
  realization.
* `Sys.TraceEq.withSub_open`, `Sys.TraceEq.withSub`, `Sys.TraceEq.par`, `Sys.TraceEq.loopback`,
  `Sys.TraceEq.mapPorts`: congruences.
* `Sys.traceEq_of_step_eq_on`, `Sys.traceEq_of_map_fst_step`, `Sys.traceEq_of_equiv`: equal
  steps on an invariant, an unused state component, renamed states.
* `view_eq_of_stepMap_on`: equal views from a step map on an invariant, in the factored form
  of the invariant.
* `Sys.DelayedDraw.traceEq`: two delayed draws against the same eager systems are trace
  equivalent (delayed draws: `CatCryptCore.Crypto.UCDelayedDraw`).
* `KeyedSys.traceEq_lazy`: moving the draw of a key to its first use.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCLoopbackObservation
open scoped ENNReal

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

/-- A realization at distance `0` of a system trace equivalent to the simulated one. -/
theorem TraceEq.realizesSim {V : PubView E O} {W : PubView EG OG} {R : Sys τ E O}
    {I : Sys υ EG OG} {S : Simulator E O EG OG V W} (h : TraceEq R (S.withSub I)) :
    RealizesSim R I S (fun _ _ => 0) :=
  h.realizes

/-! ## Congruences -/

/-- **Trace equivalence under an open system**, for admissible subroutines. -/
theorem TraceEq.withSub_open (P : Open E O EG OG) {X : Sys τ EG OG} {Y : Sys υ EG OG}
    (hX : P.Adm X) (hY : P.Adm Y) (h : TraceEq X Y) : TraceEq (P.withSub X) (P.withSub Y) :=
  traceEq_iff_realizes_zero.mpr (P.realizes_withSub hX hY h.realizes)

@[deprecated (since := "2026-11-04")] alias TraceEq.openWithSub := TraceEq.withSub_open

/-- Trace equivalence under a multi-call hybrid, for subroutines idle at a common event. -/
theorem TraceEq.withSub {σ : Type} (π : MultiHybrid σ E O EG OG) {X : Sys τ EG OG}
    {Y : Sys υ EG OG} (idle : EG) {oX oY : OG} (hX : MultiHybrid.IdleAt X idle oX)
    (hY : MultiHybrid.IdleAt Y idle oY) (h : TraceEq X Y) :
    TraceEq (π.withSub X) (π.withSub Y) :=
  h.withSub_open (Open.ofMultiHybrid π idle) ⟨oX, hX⟩ ⟨oY, hY⟩

/-- Trace equivalence under the relabelling of ports. -/
theorem TraceEq.mapPorts {E' O' : Type} {X : Sys τ EG OG} {Y : Sys υ EG OG} (h : TraceEq X Y)
    (fe : E' → EG) (fo : OG → O') : TraceEq (X.mapPorts fe fo) (Y.mapPorts fe fo) :=
  h.withSub_open (Open.mapPorts fe fo) trivial trivial

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
theorem traceEq_of_map_fst_step (R : Sys (τ × υ) E O) (S : Sys τ E O) (hinit : R.init.1 = S.init)
    (hstep : ∀ t u e, SPComp.map (fun p => (p.1.1, p.2)) (R.step (t, u) e) = S.step t e) :
    TraceEq R S :=
  traceEq_of_stepMap R S Prod.fst hinit fun t e => hstep t.1 t.2 e

@[deprecated (since := "2026-11-04")] alias traceEq_of_fst := traceEq_of_map_fst_step

/-- **Renamed states.** A system whose steps are those of `R` on states renamed by the bijection
`φ` is trace equivalent to `R`. -/
theorem traceEq_of_equiv (R : Sys τ E O) (I : Sys υ E O) (φ : τ ≃ υ) (hinit : I.init = φ R.init)
    (hstep : ∀ u e, I.step u e = SPComp.map (fun p => (φ p.1, p.2)) (R.step (φ.symm u) e)) :
    TraceEq R I :=
  traceEq_of_stepMap R I φ hinit.symm fun t e => by simp [hstep]

end Sys

variable {τ υ ζ E O : Type}

/-- Two systems related by a state map `f` have equal views when `f` sends the initial state to
the initial state and commutes with single steps from the states satisfying an invariant `Inv`,
which holds initially and at every state a step from a state satisfying it reaches. -/
theorem view_eq_of_stepMap_on (R : Sys τ E O) (I : Sys υ E O) (Inv : τ → Prop)
    (f : τ → υ) (hInv : Inv R.init) (hinit : f R.init = I.init)
    (hpres : ∀ t e, Inv t → ∃ (α : Type) (c : SPComp α) (g : α → τ × O),
      R.step t e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧ ∀ a, Inv (g a).1)
    (hstep : ∀ t e, Inv t → SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = I.step (f t) e)
    (Z : Strat ζ E O) : view R Z = view I Z :=
  Sys.traceEq_iff_view_eq.mp (Sys.traceEq_iff_realizes_zero.mpr
    (realizes_zero_of_stepMap_on R I Inv f hInv hinit hpres hstep)) _ Z

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

namespace CatCrypt.Crypto.UCTransparent.Sys

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.NonUniform

variable {K σ σ' τ υ E O EG OG ζ : Type}

/-! ## Delayed draws -/

/-- **Delayed draws against the same eager systems are trace equivalent**: two systems that
delay the draw of a key of distribution `μ` against the same family `W k` both have the view of
the average over `k ← μ` of the views of `W k` (`Sys.DelayedDraw.view_eq`). -/
theorem DelayedDraw.traceEq {L₁ : Sys σ E O} {L₂ : Sys σ' E O} {W : K → Sys τ E O}
    {μ : PMF K} {Inv₁ : σ → Prop} {Inv₂ : σ' → Prop} {D₁ : σ → SDistr (K × τ)}
    {D₂ : σ' → SDistr (K × τ)} (h₁ : DelayedDraw L₁ W μ Inv₁ D₁)
    (h₂ : DelayedDraw L₂ W μ Inv₂ D₂) : TraceEq L₁ L₂ :=
  traceEq_iff_view_eq.mpr fun _ Z => (h₁.view_eq Z).trans (h₂.view_eq Z).symm

end CatCrypt.Crypto.UCTransparent.Sys

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
  have hk : S'.withKey = S.withKey := funext fun k => by simp only [withKey, hinit, hstep]
  exact (delayedDraw_lazy S μ hind).traceEq (hk ▸ delayedDraw_lazy S' μ hind')

end CatCrypt.Crypto.UCTransparent.KeyedSys

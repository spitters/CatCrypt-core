/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import CatCryptCore.Crypto.UCTransport
public import CatCryptCore.Quantum.ClassicalLiftSys

/-!
# Transport of UC goals along observation-preserving maps

The tactic `transport_along P` reduces a goal about the images `F X`, `F Y` of systems under an
observation-preserving map `P : ObsPreserving F G` (a lifted, compiled or composite system) to
the same goal about `X`, `Y`, by the transport theorems of `UCTransport`
(`ObsPreserving.transport_eq`, `Realizes.transport`, `RealizesSim.transport`,
`QRealizes.transport`, `EmulatesΩ.transport_id`). The relation goals `F X (F X)` and the bias
side conditions of the map of observations are closed by the tactic. This is the
Broadbent–Karvonen transport of realization along a structure-preserving functor: security is
proved at the source and the goal at the target follows (classical UC to quantum UC, source
system to compiled code).

The file also states the classical lift into quantum systems as an observation-preserving map:
from the setting `pureSetting E O ζ` of heap-independent classical reactive systems tested by
heap-independent strategies and observed through their view from the empty heap, to
`qSetting E O d ζ`. The map of systems is the graph of `liftQObj` (the system `liftQSys`), the
map of tests is `liftTest` (the strategy `liftStrat`), and the field `cascade` is
`qview_liftQSys`.

## Main definitions

* `transport_along P`, `transport_along P using K` — the transport tactic; with `using K` the
  goal is an equation of observations against the image test of `K`
* `transport_rel` — closes the relation goals `F X Y` of the graph of a map, of
  `compiledRel` and of composites
* `pureSetting`, `liftQObj`, `liftRel`, `liftTest`, `liftDist`
* `liftObsPreserving` — the classical lift as an observation-preserving map

## Main results

* `liftQObj_obs_eq_of_realizes` — a classical realization at distance `0` gives equal
  observations of the lifts against every lifted environment, by `transport_along`
-/

set_option autoImplicit false

/-- Closes a goal `F X Y` where `F` is the relation of an observation-preserving map: a
hypothesis, the second case of `compiledRel`, the graph of a function, the identity case of
`compiledRel`, or the relation of a composite, whose components are closed right to left. -/
syntax (name := transportRel) "transport_rel" : tactic

macro_rules
  | `(tactic| transport_rel) => `(tactic| first
      | with_reducible assumption
      | exact Or.inr ⟨rfl, rfl⟩
      | exact rfl
      | exact Or.inl rfl
      | (apply Exists.intro
         apply And.intro
         rotate_left
         transport_rel
         transport_rel))

/-- `transport_guard_head c` succeeds when the goal is an application of the constant `c`, and
fails otherwise; it unfolds nothing. -/
syntax (name := transportGuardHead) "transport_guard_head " ident : tactic

public meta section

open Lean Elab Tactic in
/-- The elaborator of `transport_guard_head`: compares the head constant of the goal. -/
@[tactic transportGuardHead]
def evalTransportGuardHead : Tactic := fun stx => withMainContext do
  let n ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let t ← instantiateMVars (← getMainTarget)
  unless t.consumeMData.getAppFn.isConstOf n do
    throwError "transport_guard_head: the goal is not an application of {n}"

end

/-- Closes the side condition of a transport theorem on the map of observations: it does not
increase the bias, or it is the identity. -/
syntax (name := transportBias) "transport_bias" : tactic

macro_rules
  | `(tactic| transport_bias) => `(tactic| first
      | exact fun _ _ _ => le_rfl
      | exact fun _ _ => rfl
      | assumption)

/-- `transport_along P` reduces a goal about the images of systems under the
observation-preserving map `P` to the same goal about the source systems. Goals:
`RealizesSim R' I' S' b`, `Realizes R' I' b` (maps of `envSetting` with the identity on
environments), `QRealizes R'.sys I'.sys ε` (a family of maps of `qSetting`), `EmulatesΩ X' Y'`
(maps of `loopSetting` with the identity on tests), and `B.obs X' (G K) = B.obs Y' (G K)`, which
becomes `∀ K, A.obs X K = A.obs Y K`. `transport_along P using K` gives the test `K` of the last
form explicitly. The relation goals are closed by `transport_rel`, the conditions on the map of
observations by `transport_bias`; a condition `transport_bias` does not close is left as the
first goal. -/
syntax (name := transportAlong) "transport_along " term (" using " term)? : tactic

macro_rules
  | `(tactic| transport_along $P using $K) => `(tactic|
      refine CatCrypt.Crypto.UCTransport.ObsPreserving.transport_eq $P
        (by transport_rel) (by transport_rel) ?_ $K)
  | `(tactic| transport_along $P) => `(tactic| first
      | (transport_guard_head CatCrypt.Crypto.UCTransparent.RealizesSim
         refine CatCrypt.Crypto.UCTransport.RealizesSim.transport $P ?_
           (by transport_rel) (by transport_rel) ?_
         try transport_bias)
      | (transport_guard_head CatCrypt.Crypto.UCTransparent.Realizes
         refine CatCrypt.Crypto.UCTransport.Realizes.transport $P ?_
           (by transport_rel) (by transport_rel) ?_
         try transport_bias)
      | (transport_guard_head CatCrypt.Quantum.ReactiveUC.QRealizes
         refine CatCrypt.Crypto.UCTransport.QRealizes.transport $P ?_
           (by transport_rel) (by transport_rel) ?_
         try transport_bias)
      | (transport_guard_head CatCrypt.Crypto.UCLoopbackObservation.EmulatesΩ
         refine CatCrypt.Crypto.UCTransport.EmulatesΩ.transport_id $P
           (by transport_rel) (by transport_rel) ?_)
      | (transport_guard_head Eq
         refine CatCrypt.Crypto.UCTransport.ObsPreserving.transport_eq $P
           (by transport_rel) (by transport_rel) ?_ _))

@[expose] public section

namespace CatCrypt.Crypto.UCTransport

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Quantum.ReactiveUC
open CatCrypt.Quantum.ClassicalLiftSys
open _root_.Quantum (SubInstrument)
open _root_.Quantum.SubInstrument (ofSDistr)
open scoped ENNReal

/-! ## The classical lift as an observation-preserving map -/

section Lift

variable (E O : Type) (d : ℕ) (ζ : Type)

/-- The setting of heap-independent classical reactive systems with events `E` and outputs `O`,
tested by heap-independent strategies with state `ζ` and observed through the view from the
empty heap. -/
noncomputable def pureSetting : ObsSetting where
  System := PSysObj E O
  Test := {Z : Strat ζ E O // StratPure Z}
  Closed := CatCrypt.Prob.SDistr ζ
  Obs := CatCrypt.Prob.SDistr ζ
  cascade R Z := heapFree (view R.1.sys Z.1)
  observe μ := μ

variable {E O ζ}

/-- The lift of a heap-independent classical system to a quantum system on `Fin d` with the
trivial private register. -/
noncomputable def liftQObj (R : PSysObj E O) : QSysObj E O d where
  H := Unit
  τ := R.1.St
  sys := liftQSys R.1.sys

/-- The graph of `liftQObj`. -/
def liftRel : PSysObj E O → QSysObj E O d → Prop :=
  fun W W' => W' = liftQObj d W

/-- The lift of a heap-independent strategy to a quantum environment. -/
noncomputable def liftTest (Z : {Z : Strat ζ E O // StratPure Z}) : QStrat ζ E O d :=
  liftStrat Z.1

/-- The lift of a distribution of views to a quantum computation: prepare the trivial register,
apply the diagonal subinstrument of the distribution, discard the register. -/
noncomputable def liftDist (μ : CatCrypt.Prob.SDistr ζ) : CatCrypt.Quantum.CPComp d ζ :=
  (appendBasis ()).bind fun _ =>
    (ofSDistr μ).bind fun z => discardRight.bind fun _ => SubInstrument.pure z

/-- **The classical lift is observation preserving.** The view of a lifted environment against a
lifted system is the lift of the classical view from the empty heap (`qview_liftQSys`). -/
noncomputable def liftObsPreserving :
    ObsPreserving (pureSetting E O ζ) (qSetting E O d ζ) (liftRel d) (liftTest d) where
  onClosed := liftDist d
  onObs := liftDist d
  cascade := by
    rintro ⟨⟨τ, S⟩, hS⟩ W' ⟨Z, hZ⟩ rfl
    exact qview_liftQSys hS hZ
  observation _ := rfl

/-- A classical realization at distance `0` between heap-independent systems gives equal
observations of their lifts against every lifted heap-independent environment. -/
theorem liftQObj_obs_eq_of_realizes {τ υ : Type} {S : UCTransparent.Sys τ E O}
    {I : UCTransparent.Sys υ E O} (hS : S.HeapPure) (hI : I.HeapPure)
    (h : Realizes S I fun _ _ => 0) (Z : {Z : Strat ζ E O // StratPure Z}) :
    (qSetting E O d ζ).obs (liftQObj d ⟨⟨τ, S⟩, hS⟩) (liftTest d Z) =
      (qSetting E O d ζ).obs (liftQObj d ⟨⟨υ, I⟩, hI⟩) (liftTest d Z) := by
  transport_along liftObsPreserving d using Z
  intro K
  exact heapFree_view_eq_of_realizes h K.1

end Lift

/-! ## Tests -/

section Tests

/-- The quantum views of the lifts, from a classical realization at distance `0`. -/
example {E O ζ τ υ : Type} {d : ℕ} {S : UCTransparent.Sys τ E O}
    {I : UCTransparent.Sys υ E O} (hS : S.HeapPure) (hI : I.HeapPure)
    (h : Realizes S I fun _ _ => 0) (Z : Strat ζ E O) (hZ : StratPure Z) :
    qview (liftQSys (d := d) S) (liftStrat Z) = qview (liftQSys I) (liftStrat Z) := by
  change (qSetting E O d ζ).obs (liftQObj d ⟨⟨τ, S⟩, hS⟩) (liftTest d ⟨Z, hZ⟩) =
    (qSetting E O d ζ).obs (liftQObj d ⟨⟨υ, I⟩, hI⟩) (liftTest d ⟨Z, hZ⟩)
  transport_along liftObsPreserving d
  intro K
  exact heapFree_view_eq_of_realizes h K.1

/-- `RealizesSim.ofCompiled` by `transport_along` the compiled-step map. -/
example {τ υ E O C EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {init : τ} {coins : τ → E → SPComp C} {δ : τ → E → C → τ × O}
    {code : τ → E → C → Option (τ × O)} {Inv : τ → Prop} {I : UCTransparent.Sys υ EG OG}
    {S : Simulator E O EG OG V W} {b : (ζ : Type) → UCConcrete.Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : CompiledStep δ code Inv) (h0 : Inv init)
    (hs : RealizesSim (Sys.ofCore init coins δ) I S b) :
    RealizesSim (Sys.ofCode init coins code) I S b := by
  transport_along compiledObsPreserving (coins := coins) h h0
  exact hs

/-- Two compiled-step maps composed: a realization between two core systems is a realization
between their compiled forms. -/
example {τ τ₂ E O C C₂ : Type}
    {init : τ} {coins : τ → E → SPComp C} {δ : τ → E → C → τ × O}
    {code : τ → E → C → Option (τ × O)} {Inv : τ → Prop}
    {init₂ : τ₂} {coins₂ : τ₂ → E → SPComp C₂} {δ₂ : τ₂ → E → C₂ → τ₂ × O}
    {code₂ : τ₂ → E → C₂ → Option (τ₂ × O)} {Inv₂ : τ₂ → Prop}
    {b : (ζ : Type) → UCConcrete.Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : CompiledStep δ code Inv) (h0 : Inv init)
    (h₂ : CompiledStep δ₂ code₂ Inv₂) (h0₂ : Inv₂ init₂)
    (hs : Realizes (Sys.ofCore init coins δ) (Sys.ofCore init₂ coins₂ δ₂) b) :
    Realizes (Sys.ofCode init coins code) (Sys.ofCode init₂ coins₂ code₂) b := by
  transport_along (compiledObsPreserving (coins := coins) h h0).comp
    (compiledObsPreserving (coins := coins₂) h₂ h0₂)
  exact hs

/-- The classical lift composed with the identity map of `qSetting`, at an equation of
observations. -/
example {E O ζ τ υ : Type} {d : ℕ} {S : UCTransparent.Sys τ E O}
    {I : UCTransparent.Sys υ E O} (hS : S.HeapPure) (hI : I.HeapPure)
    (h : Realizes S I fun _ _ => 0) (Z : {Z : Strat ζ E O // StratPure Z}) :
    (qSetting E O d ζ).obs (liftQObj d ⟨⟨τ, S⟩, hS⟩) (liftTest d Z) =
      (qSetting E O d ζ).obs (liftQObj d ⟨⟨υ, I⟩, hI⟩) (liftTest d Z) := by
  transport_along (liftObsPreserving d).comp (ObsPreserving.id _) using Z
  intro K
  exact heapFree_view_eq_of_realizes h K.1

/-- Quantum realization along the identity family of maps of `qSetting`. -/
example {E O : Type} {d : ℕ} {ε : ℝ≥0∞} {R I : QSysObj E O d}
    (h : QRealizes R.sys I.sys ε) : QRealizes R.sys I.sys ε := by
  transport_along fun ζ => ObsPreserving.id (qSetting E O d ζ)
  exact h

end Tests

end CatCrypt.Crypto.UCTransport

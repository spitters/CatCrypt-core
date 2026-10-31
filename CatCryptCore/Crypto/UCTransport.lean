/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackObservationBridge
public import CatCryptCore.Crypto.UCCompiled
public import CatCryptCore.Quantum.QRealizes

/-!
# Transport of UC realization along observation-preserving maps

An observation setting (`ObsSetting`) consists of systems, environment tests, the closed system
that the cascade of a system with a test produces, and the observation of a closed system. A map
of systems between two settings, given as a relation `F` (the graph of a possibly partial map)
together with a map `G` of tests, is observation preserving (`ObsPreserving F G`) when the
cascade of an image system with an image test is observed as the image of the source cascade
(field `cascade`) and the observation of an image closed system is the image of the source
observation (field `observation`). Every statement about the observations of a pair of systems
that is stable under the map of observations transports to the images of the systems, against
the environments in the image of `G` (`ObsPreserving.transport`). This is the concrete form of
the transport of realization along a structure-preserving functor of Broadbent and Karvonen.

The settings of this file:

* `loopSetting Δ`: open systems of `loopOpenTheory` on `Δ`, tests on `Δ.swap ⊗ bitBoundary`,
  cascade `runTest`, observation `obsBit`. Testing equivalence in it is `EmulatesΩ`.
* `envSetting E O`: classical reactive systems, environments with a heap and a distinguisher,
  the cascade with the environment test `stratTest`, observation `obsBit`. Realization
  `Realizes` is a bound on the observations in it (`realizes_iff_envSetting`).
* `qSetting E O d ζ`: quantum reactive systems, quantum environments with state `ζ`, and the
  view `qview` as observation. `QRealizes` is a diamond-distance bound on the observations.

The instances proved here are the identity (`ObsPreserving.id`), composites
(`ObsPreserving.comp`) and the compiled-step map of `UCCompiled` (`compiledObsPreserving`), from
which `RealizesSim.ofCompiled` follows by `RealizesSim.transport`.

Two further maps instantiate `ObsPreserving` in the same way. The classical lift
(`Quantum/ClassicalLiftSys.lean`) is a map from a setting of heap-pure classical systems tested by
pure strategies, observed through their view, to `qSetting`: `F` is the graph of `liftQSys`,
`G` is `liftStrat`, and the field `cascade` is `qview_liftQSys`, whose right-hand side is the map
of observations applied to the classical view. The quantum compiled step (dev
`Quantum/QCompiledStep.lean`) is a map from `qSetting` to itself: `F` relates the source quantum
system to its compiled form `QSys.ofCompiled`, `G` and the map of observations are identities,
and the field `cascade` is the equality of the views of the two systems.

## Main definitions

* `ObsSetting`, `ObsSetting.obs`
* `ObsPreserving F G` — a map of systems that preserves the cascade with an environment test and
  the observation
* `loopSetting`, `envSetting`, `qSetting`, `QSysObj`
* `compiledRel`, `compiledObsPreserving` — the compiled-step map

## Main results

* `ObsPreserving.transport`, `ObsPreserving.transport_eq` — transport of a statement about
  observations, and of equality of observations, to the image systems
* `EmulatesΩ.transport`, `EmulatesΩε.transport` — transport of UC testing equivalence through the
  bit boundary
* `Realizes.transport`, `RealizesSim.transport` — transport of classical realization, with a
  simulator and a bound
* `QRealizes.transport` — transport of quantum realization
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.UCTransport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCLoopbackObservation
open CatCrypt.Crypto.UCLoopbackOpenTheory Interaction Interaction.Open
open scoped ENNReal

universe u v w x u' v' w' x' u'' v'' w'' x''

/-! ## Observation settings and observation-preserving maps -/

/-- A setting of UC observation: systems, environment tests, the closed systems produced by the
cascade of a system with a test, and the observation of a closed system. -/
structure ObsSetting where
  /-- The systems. -/
  System : Type u
  /-- The environment tests. -/
  Test : Type v
  /-- The closed systems. -/
  Closed : Type w
  /-- The observations. -/
  Obs : Type x
  /-- The cascade of a system with a test. -/
  cascade : System → Test → Closed
  /-- The observation of a closed system. -/
  observe : Closed → Obs

/-- The observation of the system `W` against the test `K`. -/
def ObsSetting.obs (A : ObsSetting.{u, v, w, x}) (W : A.System) (K : A.Test) : A.Obs :=
  A.observe (A.cascade W K)

/-- A map of systems from `A` to `B`, given by the relation `F` and the map of tests `G`, that
preserves the cascade with an environment test and the observation. -/
structure ObsPreserving (A : ObsSetting.{u, v, w, x}) (B : ObsSetting.{u', v', w', x'})
    (F : A.System → B.System → Prop) (G : A.Test → B.Test) where
  /-- The map of closed systems. -/
  onClosed : A.Closed → B.Closed
  /-- The map of observations. -/
  onObs : A.Obs → B.Obs
  /-- The cascade of an image system with an image test is observed as the image of the
  cascade. -/
  cascade : ∀ W W' K, F W W' →
    B.observe (B.cascade W' (G K)) = B.observe (onClosed (A.cascade W K))
  /-- The observation of an image closed system is the image of the observation. -/
  observation : ∀ X, B.observe (onClosed X) = onObs (A.observe X)

namespace ObsPreserving

variable {A : ObsSetting.{u, v, w, x}} {B : ObsSetting.{u', v', w', x'}}
  {C : ObsSetting.{u'', v'', w'', x''}}
  {F : A.System → B.System → Prop} {G : A.Test → B.Test}

/-- The observation of an image system against an image test is the image of the observation. -/
theorem obs_eq (P : ObsPreserving A B F G) {W : A.System} {W' : B.System} (h : F W W')
    (K : A.Test) : B.obs W' (G K) = P.onObs (A.obs W K) :=
  (P.cascade W W' K h).trans (P.observation _)

/-- **Transport.** A statement `Q₁` about the observations of `real` and `ideal` whose image under
the map of observations satisfies `Q₂` gives `Q₂` for the observations of the image systems
against the image tests. -/
theorem transport (P : ObsPreserving A B F G)
    {Q₁ : (A.Test → A.Obs) → (A.Test → A.Obs) → Prop}
    {Q₂ : (A.Test → B.Obs) → (A.Test → B.Obs) → Prop}
    (hQ : ∀ f g, Q₁ f g → Q₂ (P.onObs ∘ f) (P.onObs ∘ g))
    {real ideal : A.System} {real' ideal' : B.System} (hr : F real real') (hi : F ideal ideal')
    (h : Q₁ (A.obs real) (A.obs ideal)) :
    Q₂ (fun K => B.obs real' (G K)) (fun K => B.obs ideal' (G K)) := by
  have er : (fun K => B.obs real' (G K)) = P.onObs ∘ A.obs real := funext (P.obs_eq hr)
  have ei : (fun K => B.obs ideal' (G K)) = P.onObs ∘ A.obs ideal := funext (P.obs_eq hi)
  rw [er, ei]
  exact hQ _ _ h

/-- **Transport of testing equivalence.** If every test observes the same on `real` and on
`ideal`, every image test observes the same on the image systems. -/
theorem transport_eq (P : ObsPreserving A B F G) {real ideal : A.System}
    {real' ideal' : B.System} (hr : F real real') (hi : F ideal ideal')
    (h : ∀ K, A.obs real K = A.obs ideal K) (K : A.Test) :
    B.obs real' (G K) = B.obs ideal' (G K) := by
  rw [P.obs_eq hr, P.obs_eq hi, h K]

/-- The identity map of a setting is observation preserving. -/
def id (A : ObsSetting.{u, v, w, x}) : ObsPreserving A A Eq _root_.id where
  onClosed X := X
  onObs o := o
  cascade := by
    rintro W _ K rfl
    rfl
  observation _ := rfl

/-- The composite of observation-preserving maps is observation preserving. -/
def comp {F' : B.System → C.System → Prop} {G' : B.Test → C.Test}
    (P : ObsPreserving A B F G) (P' : ObsPreserving B C F' G') :
    ObsPreserving A C (fun W W'' => ∃ W', F W W' ∧ F' W' W'') (G' ∘ G) where
  onClosed := P'.onClosed ∘ P.onClosed
  onObs := P'.onObs ∘ P.onObs
  cascade := by
    rintro W W'' K ⟨W', h, h'⟩
    rw [Function.comp_apply, P'.cascade _ _ _ h', P'.observation, P.cascade _ _ _ h,
      Function.comp_apply, P'.observation]
  observation X := by
    rw [Function.comp_apply, P'.observation, P.observation]
    rfl

end ObsPreserving

/-! ## Testing equivalence through the bit boundary -/

/-- The setting of open systems on `Δ` tested through the bit boundary. -/
noncomputable def loopSetting (Δ : PortBoundary) : ObsSetting where
  System := loopOpenTheory.Obj Δ
  Test := loopOpenTheory.Obj (Δ.swap.tensor bitBoundary)
  Closed := loopOpenTheory.Obj bitBoundary
  Obs := SPComp Bool
  cascade := runTest
  observe := obsBit

/-- **Transport of `EmulatesΩ`.** An observation-preserving map of bit-boundary settings sends
testing-equivalent systems to systems that every image test observes alike. -/
theorem EmulatesΩ.transport {Δ Δ' : PortBoundary}
    {F : loopOpenTheory.Obj Δ → loopOpenTheory.Obj Δ' → Prop}
    {G : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary) →
      loopOpenTheory.Obj (Δ'.swap.tensor bitBoundary)}
    (P : ObsPreserving (loopSetting Δ) (loopSetting Δ') F G)
    {real ideal : loopOpenTheory.Obj Δ} {real' ideal' : loopOpenTheory.Obj Δ'}
    (hr : F real real') (hi : F ideal ideal') (h : EmulatesΩ real ideal)
    (K : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary)) :
    obsBit (runTest real' (G K)) = obsBit (runTest ideal' (G K)) :=
  P.transport_eq hr hi h K

/-- **Transport of `EmulatesΩ` along a map with the identity on tests.** -/
theorem EmulatesΩ.transport_id {Δ : PortBoundary}
    {F : loopOpenTheory.Obj Δ → loopOpenTheory.Obj Δ → Prop}
    (P : ObsPreserving (loopSetting Δ) (loopSetting Δ) F _root_.id)
    {real ideal real' ideal' : loopOpenTheory.Obj Δ}
    (hr : F real real') (hi : F ideal ideal') (h : EmulatesΩ real ideal) :
    EmulatesΩ real' ideal' :=
  EmulatesΩ.transport P hr hi h

/-- **Transport of `EmulatesΩε`.** If the map of observations does not increase the bias of any
test at any initial heap, emulation up to `ε` transports to the image systems against the image
tests. -/
theorem EmulatesΩε.transport {Δ Δ' : PortBoundary} {ε : ℝ≥0∞}
    {F : loopOpenTheory.Obj Δ → loopOpenTheory.Obj Δ' → Prop}
    {G : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary) →
      loopOpenTheory.Obj (Δ'.swap.tensor bitBoundary)}
    (P : ObsPreserving (loopSetting Δ) (loopSetting Δ') F G)
    (hΦ : ∀ (c c' : SPComp Bool) (h₀ : Heap),
      absDiff (prTrue (P.onObs c) h₀) (prTrue (P.onObs c') h₀) ≤
        absDiff (prTrue c h₀) (prTrue c' h₀))
    {real ideal : loopOpenTheory.Obj Δ} {real' ideal' : loopOpenTheory.Obj Δ'}
    (hr : F real real') (hi : F ideal ideal') (h : EmulatesΩε ε real ideal)
    (K : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary)) (h₀ : Heap) :
    absDiff (prTrue (obsBit (runTest real' (G K))) h₀)
      (prTrue (obsBit (runTest ideal' (G K))) h₀) ≤ ε :=
  (P.transport (Q₁ := fun f g => ∀ K h₀, absDiff (prTrue (f K) h₀) (prTrue (g K) h₀) ≤ ε)
    (Q₂ := fun f g => ∀ K h₀, absDiff (prTrue (f K) h₀) (prTrue (g K) h₀) ≤ ε)
    (fun _ _ hfg K h₀ => (hΦ _ _ h₀).trans (hfg K h₀)) hr hi h) K h₀

/-! ## Realization against environments -/

/-- The setting of classical reactive systems with events `E` and outputs `O`, tested by
environments through the environment test `stratTest` and observed through the bit boundary. -/
noncomputable def envSetting (E O : Type) : ObsSetting where
  System := Σ τ : Type, UCTransparent.Sys τ E O
  Test := Σ ζ : Type, Env (Strat ζ E O) ζ
  Closed := loopOpenTheory.Obj bitBoundary
  Obs := SPComp Bool
  cascade R Z := runTest (sysObj R.2) (stratTest Z.2.input Z.2.dist)
  observe := obsBit

/-- The observation of an environment in `envSetting` is its view followed by its
distinguisher. -/
theorem envSetting_obs {τ ζ E O : Type} (R : UCTransparent.Sys τ E O) (Z : Env (Strat ζ E O) ζ) :
    (envSetting E O).obs ⟨τ, R⟩ ⟨ζ, Z⟩ = SPComp.bind (view R Z.input) Z.dist := by
  change obsBit (runTest (sysObj R) (stratTest Z.input Z.dist)) = _
  rw [runTest_stratTest, obsBit_sysObj_comp_stratHom]

/-- Realization with bound `b` is the bound `b` on the bias of the observations of every
environment of `envSetting`. -/
theorem realizes_iff_envSetting {τ υ E O : Type} {R : UCTransparent.Sys τ E O}
    {I : UCTransparent.Sys υ E O} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} :
    Realizes R I b ↔ ∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ),
      absDiff (prTrue ((envSetting E O).obs ⟨τ, R⟩ ⟨ζ, Z⟩) Z.heap)
        (prTrue ((envSetting E O).obs ⟨υ, I⟩ ⟨ζ, Z⟩) Z.heap) ≤ b ζ Z := by
  simp only [envSetting_obs, Realizes, DistC, Env.gap]

/-- **Transport of realization.** Along an observation-preserving map of `envSetting` with the
identity on environments, whose map of observations does not increase the bias, a realization
of `I` by `R` with bound `b` is a realization of the image of `I` by the image of `R` with the
same bound. -/
theorem Realizes.transport {τ υ τ' υ' E O : Type}
    {F : (envSetting E O).System → (envSetting E O).System → Prop}
    (P : ObsPreserving (envSetting E O) (envSetting E O) F _root_.id)
    (hΦ : ∀ (c c' : SPComp Bool) (h₀ : Heap),
      absDiff (prTrue (P.onObs c) h₀) (prTrue (P.onObs c') h₀) ≤
        absDiff (prTrue c h₀) (prTrue c' h₀))
    {R : UCTransparent.Sys τ E O} {I : UCTransparent.Sys υ E O}
    {R' : UCTransparent.Sys τ' E O} {I' : UCTransparent.Sys υ' E O}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hr : F ⟨τ, R⟩ ⟨τ', R'⟩) (hi : F ⟨υ, I⟩ ⟨υ', I'⟩) (h : Realizes R I b) :
    Realizes R' I' b := by
  rw [realizes_iff_envSetting] at h ⊢
  intro ζ Z
  have er := P.obs_eq hr ⟨ζ, Z⟩
  have ei := P.obs_eq hi ⟨ζ, Z⟩
  simp only [_root_.id] at er ei
  rw [er, ei]
  exact (hΦ _ _ _).trans (h ζ Z)

/-- **Transport of realization behind a simulator.** If the map relates `S.withSub I` to
`S'.withSub I'`, a realization of `I` behind `S` by `R` is a realization of `I'` behind `S'` by
the image of `R`, with the same bound. -/
theorem RealizesSim.transport {τ υ τ' υ' E O EG OG EG' OG' : Type}
    {V : PubView E O} {W : PubView EG OG} {W' : PubView EG' OG'}
    {F : (envSetting E O).System → (envSetting E O).System → Prop}
    (P : ObsPreserving (envSetting E O) (envSetting E O) F _root_.id)
    (hΦ : ∀ (c c' : SPComp Bool) (h₀ : Heap),
      absDiff (prTrue (P.onObs c) h₀) (prTrue (P.onObs c') h₀) ≤
        absDiff (prTrue c h₀) (prTrue c' h₀))
    {R : UCTransparent.Sys τ E O} {I : UCTransparent.Sys υ EG OG}
    {R' : UCTransparent.Sys τ' E O} {I' : UCTransparent.Sys υ' EG' OG'}
    {S : Simulator E O EG OG V W} {S' : Simulator E O EG' OG' V W'}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hr : F ⟨τ, R⟩ ⟨τ', R'⟩) (hs : F ⟨_, S.withSub I⟩ ⟨_, S'.withSub I'⟩)
    (h : RealizesSim R I S b) : RealizesSim R' I' S' b :=
  Realizes.transport P hΦ hr hs h

/-! ## The compiled-step map -/

/-- The graph of the compiled-step map: it relates the source system `Sys.ofCore init coins δ`
to the code system `Sys.ofCode init coins code`, and every system to itself. -/
def compiledRel {τ E O C : Type} (init : τ) (coins : τ → E → SPComp C)
    (δ : τ → E → C → τ × O) (code : τ → E → C → Option (τ × O)) :
    (envSetting E O).System → (envSetting E O).System → Prop :=
  fun W W' => W = W' ∨
    (W = ⟨τ, Sys.ofCore init coins δ⟩ ∧ W' = ⟨τ, Sys.ofCode init coins code⟩)

/-- **The compiled-step map is observation preserving.** Under `CompiledStep` and `Inv init`,
the compiled-step map, with the identity on environments, closed systems and observations,
preserves the cascade with every environment test. -/
noncomputable def compiledObsPreserving {τ E O C : Type} {init : τ} {coins : τ → E → SPComp C}
    {δ : τ → E → C → τ × O} {code : τ → E → C → Option (τ × O)} {Inv : τ → Prop}
    (h : CompiledStep δ code Inv) (h0 : Inv init) :
    ObsPreserving (envSetting E O) (envSetting E O) (compiledRel init coins δ code)
      _root_.id where
  onClosed X := X
  onObs c := c
  cascade := by
    rintro W W' ⟨ζ, Z⟩ (rfl | ⟨rfl, rfl⟩)
    · rfl
    · change (envSetting E O).obs _ ⟨ζ, Z⟩ = (envSetting E O).obs _ ⟨ζ, Z⟩
      rw [envSetting_obs, envSetting_obs,
        realizes_zero_iff_view_eq.1 (realizes_zero_of_compiledStep h h0) ζ Z.input]
  observation _ := rfl

/-- `RealizesSim.ofCompiled` is the transport of a realization along the compiled-step map. -/
example {τ υ E O C EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {init : τ} {coins : τ → E → SPComp C} {δ : τ → E → C → τ × O}
    {code : τ → E → C → Option (τ × O)} {Inv : τ → Prop} {I : UCTransparent.Sys υ EG OG}
    {S : Simulator E O EG OG V W} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : CompiledStep δ code Inv) (h0 : Inv init)
    (hs : RealizesSim (Sys.ofCore init coins δ) I S b) :
    RealizesSim (Sys.ofCode init coins code) I S b :=
  RealizesSim.transport (compiledObsPreserving h h0) (fun _ _ _ => le_rfl)
    (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl) hs

/-! ## Quantum realization -/

open CatCrypt.Quantum.ReactiveUC in
/-- A quantum reactive system with events `E` and outputs `O` on the register `Fin d`, bundled
with its private register `H` and its classical state `τ`. -/
structure QSysObj (E O : Type) (d : ℕ) where
  /-- The private register. -/
  H : Type
  /-- The private register is finite. -/
  [fin : Fintype H]
  /-- The private register has decidable equality. -/
  [dec : DecidableEq H]
  /-- The classical state. -/
  τ : Type
  /-- The system. -/
  sys : QSys H τ E O d

attribute [instance] QSysObj.fin QSysObj.dec

open CatCrypt.Quantum.ReactiveUC in
/-- The setting of quantum reactive systems tested by quantum environments with state `ζ` and
observed through the view `qview`. -/
noncomputable def qSetting (E O : Type) (d : ℕ) (ζ : Type) : ObsSetting where
  System := QSysObj E O d
  Test := QStrat ζ E O d
  Closed := CatCrypt.Quantum.CPComp d ζ
  Obs := CatCrypt.Quantum.CPComp d ζ
  cascade R Z := qview R.sys Z
  observe c := c

open CatCrypt.Quantum.ReactiveUC in
/-- **Transport of quantum realization.** Along a family of observation-preserving maps of
`qSetting`, one for each environment state type, with the identity on environments and on
observations, a realization at distance `ε` is a realization of the images at distance `ε`. -/
theorem QRealizes.transport {E O : Type} {d : ℕ} {ε : ℝ≥0∞}
    {F : QSysObj E O d → QSysObj E O d → Prop}
    (P : ∀ ζ : Type, ObsPreserving (qSetting E O d ζ) (qSetting E O d ζ) F _root_.id)
    (hΦ : ∀ (ζ : Type) (c : CatCrypt.Quantum.CPComp d ζ), (P ζ).onObs c = c)
    {R I R' I' : QSysObj E O d} (hr : F R R') (hi : F I I')
    (h : QRealizes R.sys I.sys ε) : QRealizes R'.sys I'.sys ε := by
  intro ζ
  have e : ∀ {W W' : QSysObj E O d}, F W W' → ∀ Z : QStrat ζ E O d,
      qview W'.sys Z = qview W.sys Z := fun hW Z => by
    have := ((P ζ).obs_eq hW Z).trans (hΦ ζ _)
    exact this
  exact quc_congr _ _ (h ζ) (funext fun Z => by rw [e hr Z]) (funext fun Z => by rw [e hi Z])

end CatCrypt.Crypto.UCTransport

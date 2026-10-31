/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.OpenSystem
public import CatCryptCore.Crypto.UCMonad.CPCompUC
public import CatCryptCore.Crypto.UCMonad.DiamondEmulation

/-!
# Quantitative runs and realization of quantum reactive systems

Two pieces of the quantum UC layer.

The closed run of an open process. `closedRun p k s` runs `k` steps of the open process
`p` from the state `s`, each step sampling a complete path of the step protocol with the
step sampler and moving to the next state. It is defined for every monad; for the quantum
open processes of `CatCrypt.Quantum.OpenSystem` it is a subinstrument on the register.
It commutes with transport along a monad morphism (`closedRun_hoist`), so the run of a
process placed on a factor of a register is the placed run (`closedRun_frame`).
`envRun` is the run of an environment plugged against a world in `quantumOpenTheory`,
observed through the environment's process state.

Realization of quantum reactive systems. A quantum reactive system `QSys H τ E O d` has a
classical state `τ` and a private register `H`; on each activation by an event `E` it acts
on the joint register `Fin d × H` and returns a new state and an output `O`. An environment
`QStrat ζ E O d` acts on the register `Fin d` only, chooses each event and observes each
output; its internal state `ζ` is its view. The view `qview S Z : CPComp d ζ` prepares the
private register in its initial basis state, runs `Z` against `S` for `Z.rounds` activations
and discards the private register. `QRealizes R I ε` is the diamond-distance bound
`QUCEmulatesDiamond ε` between the view maps of `R` and `I`, for every environment state
type. A simulator `QSim` translates the events and outputs of the real interface to those of
the ideal one; it is absorbed into the environment (`QSim.absorb`), and
`QRealizesSim R I S ε` compares the view of `R` with the view of `I` against the absorbed
environment.

## Main definitions

* `OpenSystem.closedRun p k s` — the `k`-step run of an open process
* `OpenSystem.envRun σ W Z k s` — the run of `Z` plugged against `W`, observed through `Z`'s
  state
* `ReactiveUC.appendBasis`, `ReactiveUC.discardRight` — preparing a register in a basis
  state and discarding it, as Kraus subinstruments
* `ReactiveUC.QSys`, `ReactiveUC.QStrat`, `ReactiveUC.qloop`, `ReactiveUC.qview`
* `ReactiveUC.QRealizes R I ε`, `ReactiveUC.QSim`, `ReactiveUC.QRealizesSim R I S ε`

## Main results

* `OpenSystem.closedRun_hoist`, `OpenSystem.closedRun_frame`
* `ReactiveUC.qview_hom` — a map of environment states that commutes with the environment
  steps commutes with the view
* `ReactiveUC.QRealizes.refl`, `ReactiveUC.QRealizes.trans`
* `ReactiveUC.QRealizesSim.refl` (identity simulator, `ε = 0`),
  `ReactiveUC.QRealizesSim.trans` (composite simulator, `ε₁ + ε₂`)
-/

@[expose] public section

set_option autoImplicit false

universe u w w' w''

noncomputable section

namespace CatCrypt.Quantum.OpenSystem

open Interaction Interaction.Open Concurrent

/-! ## The closed run of an open process -/

section ClosedRun

variable {Party : Type u} {m : Type w → Type w'} [Monad m] {Δ : PortBoundary}

/-- The `k`-step run of the open process `p` from the state `s`: each step samples a
complete path of the step protocol with the step sampler and moves to the next state. -/
def closedRun (p : OpenProcess.{u, w, w, w'} m Party Δ) : ℕ → p.Proc → m p.Proc
  | 0, s => pure s
  | k + 1, s => TypeTree.samplePath _ (p.stepSampler s) >>= fun tr =>
      closedRun p k ((p.step s).next tr)

/-- Unfolding lemma: the run of no step returns the state. -/
theorem closedRun_zero (p : OpenProcess.{u, w, w, w'} m Party Δ) (s : p.Proc) :
    closedRun p 0 s = pure s := rfl

/-- Unfolding lemma: a run of `k + 1` steps samples one step and runs `k` steps from the
next state. -/
theorem closedRun_succ (p : OpenProcess.{u, w, w, w'} m Party Δ) (k : ℕ) (s : p.Proc) :
    closedRun p (k + 1) s = TypeTree.samplePath _ (p.stepSampler s) >>= fun tr =>
      closedRun p k ((p.step s).next tr) := rfl

/-- Along a family `φ` that preserves `pure` and `bind`, the run of the transported process
is the transported run. -/
theorem closedRun_hoist {n : Type w → Type w''} [Monad n]
    (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
    (hpure : ∀ {X : Type w} (x : X), φ X (pure x) = pure x)
    (hbind : ∀ {X Y : Type w} (c : m X) (f : X → m Y),
      φ Y (c >>= f) = φ X c >>= fun x => φ Y (f x))
    (p : OpenProcess.{u, w, w, w'} m Party Δ) (k : ℕ) (s : p.Proc) :
    closedRun (hoist φ p) k s = φ _ (closedRun p k s) := by
  induction k generalizing s with
  | zero => exact (hpure s).symm
  | succ k ih =>
    change TypeTree.samplePath _ (TypeTree.Decoration.map φ _ (p.stepSampler s)) >>=
        (fun tr => closedRun (hoist φ p) k ((p.step s).next tr)) =
      φ _ (TypeTree.samplePath _ (p.stepSampler s) >>= fun tr =>
        closedRun p k ((p.step s).next tr))
    rw [samplePath_hoist φ hpure hbind, hbind]
    exact congrArg _ (funext fun tr => ih _)

end ClosedRun

section QuantumRun

open _root_.Quantum

variable {Party : Type u} {M N : Type} [Fintype M] [Fintype N] {Δ : PortBoundary}

/-- The run of a quantum open process placed on the left factor of `M × N` is the run of the
process, placed on the left factor. -/
theorem closedRun_frame (p : QOpenProcess.{u, 0} Party M Δ) (k : ℕ) (s : p.Proc) :
    closedRun (hoist (frameHom M N) p) k s = (closedRun p k s).frame N :=
  closedRun_hoist (frameHom M N) (fun x => SubInstrument.frame_pure N x)
    (fun c f => SubInstrument.frame_bind N c f) p k s

/-- The `k`-step run of the environment `Z` plugged against the world `W` in the quantum open
theory with scheduler `σ`, observed through the process state of `Z`. -/
def envRun (σ : SubInstrument M M (ULift Bool)) (W : QOpenProcess.{u, 0} Party M Δ)
    (Z : QOpenProcess.{u, 0} Party M (PortBoundary.swap Δ)) (k : ℕ) (s : W.Proc × Z.Proc) :
    SubInstrument M M Z.Proc :=
  SubInstrument.bind (closedRun ((quantumOpenTheory.{u, 0} Party M σ).plug W Z) k s)
    fun c => SubInstrument.pure c.2

end QuantumRun

end CatCrypt.Quantum.OpenSystem

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open Matrix
open CatCrypt.Crypto.UCMonad.DiamondNorm
open UCMonad.QuantumUC
open scoped ENNReal

/-! ## Preparing and discarding a register

Lemmas about QuantumFoundations' `SubInstrument` alone. -/

section Register

variable {A H : Type} [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H]

/-- The isometry `|a⟩ ↦ |a, h₀⟩` that appends the basis state `h₀` of `H`. -/
def appendKraus (h₀ : H) : Matrix (A × H) A ℂ :=
  Matrix.of fun x a => if x = (a, h₀) then 1 else 0

/-- `appendKraus h₀` is an isometry. -/
theorem appendKraus_isometry (h₀ : H) :
    ∑ _u : Unit, (appendKraus (A := A) h₀)ᴴ * appendKraus h₀ = 1 := by
  ext a a'
  simp [appendKraus, Matrix.mul_apply, Matrix.one_apply]
  grind

/-- Preparing the register `H` in the basis state `h₀` beside `A`. -/
def appendBasis (h₀ : H) : SubInstrument A (A × H) Unit :=
  SubInstrument.ofKraus (fun _ => appendKraus h₀) (appendKraus_isometry h₀)

/-- The Kraus operator `⟨h|` on the right factor of `A × H`. -/
def discardKraus (h : H) : Matrix A (A × H) ℂ :=
  Matrix.of fun a x => if x = (a, h) then 1 else 0

/-- The operators `discardKraus h` satisfy the completeness relation. -/
theorem discardKraus_complete :
    ∑ h : H, (discardKraus (A := A) h)ᴴ * discardKraus h = 1 := by
  ext ⟨a, h⟩ ⟨a', h'⟩
  simp [discardKraus, Matrix.mul_apply, Matrix.one_apply, Matrix.sum_apply, Prod.ext_iff,
    ite_and, apply_ite (starRingEnd ℂ)]

/-- Discarding the right factor of `A × H`: the measurement of `H` in its basis, whose
branches sum to the partial trace over `H`. -/
def discardRight : SubInstrument (A × H) A H :=
  SubInstrument.ofKraus discardKraus discardKraus_complete

end Register

/-! ## Quantum reactive systems and environments -/

/-- A quantum reactive system with classical state `τ`, private register `H`, input events
`E` and outputs `O`, acting together with the environment register `Fin d`. -/
structure QSys (H : Type) [Fintype H] (τ E O : Type) (d : ℕ) where
  /-- Initial classical state. -/
  init : τ
  /-- Initial basis state of the private register. -/
  initReg : H
  /-- One activation: a subinstrument on the joint register with the new state and the
  output as outcome. -/
  step : τ → E → SubInstrument (Fin d × H) (Fin d × H) (τ × O)

/-- An interactive quantum environment with internal state `ζ`, acting on the register
`Fin d`. It runs for `rounds` activations; each activation chooses an event with `next` and
processes the output with `obs`. -/
structure QStrat (ζ E O : Type) (d : ℕ) where
  /-- Number of activations. -/
  rounds : ℕ
  /-- Initial environment state. -/
  init : ζ
  /-- Choice of the next event. -/
  next : ζ → CPComp d (ζ × E)
  /-- Observation of an output. -/
  obs : ζ → O → CPComp d ζ

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
variable {τ υ ζ ζ₁ ζ₂ E O : Type} {d : ℕ}

omit [DecidableEq H] in
/-- The joint run of the environment `Z` and the system `S` for `n` activations from the
configuration `(environment state, system state)`, on the register `Fin d × H`. The
environment's operations act on `Fin d` only. -/
def qloop (S : QSys H τ E O d) (Z : QStrat ζ E O d) :
    ℕ → ζ × τ → SubInstrument (Fin d × H) (Fin d × H) (ζ × τ)
  | 0, c => SubInstrument.pure c
  | n + 1, c =>
    ((Z.next c.1).frame H).bind fun a =>
      (S.step c.2 a.2).bind fun p =>
        ((Z.obs a.1 p.2).frame H).bind fun z =>
          qloop S Z n (z, p.1)

/-- The view of the environment `Z` against `S`: prepare the private register in its initial
basis state, run `Z.rounds` activations, discard the private register and return the final
environment state. -/
def qview (S : QSys H τ E O d) (Z : QStrat ζ E O d) : CPComp d ζ :=
  (appendBasis S.initReg).bind fun _ =>
    (qloop S Z Z.rounds (Z.init, S.init)).bind fun c =>
      discardRight.bind fun _ => SubInstrument.pure c.1

omit [DecidableEq H] in
/-- A map `f` of environment states that commutes with the steps of two environments commutes
with their joint runs. -/
theorem qloop_hom (S : QSys H τ E O d) (Z₁ : QStrat ζ₁ E O d) (Z₂ : QStrat ζ₂ E O d)
    (f : ζ₁ → ζ₂)
    (hn : ∀ z, (Z₁.next z).bind (fun a => SubInstrument.pure (f a.1, a.2)) = Z₂.next (f z))
    (ho : ∀ z o, (Z₁.obs z o).bind (fun z' => SubInstrument.pure (f z')) = Z₂.obs (f z) o)
    (n : ℕ) (z : ζ₁) (t : τ) :
    (qloop S Z₁ n (z, t)).bind (fun c => SubInstrument.pure (f c.1, c.2)) =
      qloop S Z₂ n (f z, t) := by
  induction n generalizing z t with
  | zero => exact SubInstrument.pure_bind _ _
  | succ n ih =>
    simp only [qloop, ← hn, ← ho, SubInstrument.frame_bind, SubInstrument.frame_pure,
      SubInstrument.bind_assoc, SubInstrument.pure_bind, ← ih]

/-- **Morphism of environments.** A map `f` of environment states that sends the initial
state of `Z₁` to that of `Z₂` and commutes with the steps maps the view of `Z₁` to the view
of `Z₂`. -/
theorem qview_hom (S : QSys H τ E O d) (Z₁ : QStrat ζ₁ E O d) (Z₂ : QStrat ζ₂ E O d)
    (f : ζ₁ → ζ₂) (hr : Z₁.rounds = Z₂.rounds) (hi : f Z₁.init = Z₂.init)
    (hn : ∀ z, (Z₁.next z).bind (fun a => SubInstrument.pure (f a.1, a.2)) = Z₂.next (f z))
    (ho : ∀ z o, (Z₁.obs z o).bind (fun z' => SubInstrument.pure (f z')) = Z₂.obs (f z) o) :
    (qview S Z₁).bind (fun z => SubInstrument.pure (f z)) = qview S Z₂ := by
  simp only [qview, ← hr, ← hi, ← qloop_hom S Z₁ Z₂ f hn ho, SubInstrument.bind_assoc,
    SubInstrument.pure_bind]

/-! ## Realization -/

/-- `R` realizes `I` at distance `ε`: for every environment state type `ζ`, the view maps of
`R` and `I` are within diamond distance `ε`, with a reference register of every size. -/
def QRealizes {τ υ E O : Type} (R : QSys H τ E O d) (I : QSys H' υ E O d) (ε : ℝ≥0∞) :
    Prop :=
  ∀ ζ : Type, QUCEmulatesDiamond ε (fun Z : QStrat ζ E O d => (qview R Z).toQComp)
    (fun Z => (qview I Z).toQComp) (fun Z => CPComp.branch_cp (qview R Z))
    (fun Z => CPComp.branch_cp (qview I Z))

/-- Every system realizes itself at distance `0`. -/
theorem QRealizes.refl (R : QSys H τ E O d) : QRealizes R R 0 :=
  fun _ => QUCEmulatesDiamond.refl 0 _ _

/-- Realization is transitive with additive distance. -/
theorem QRealizes.trans {τ' H'' : Type} [Fintype H''] [DecidableEq H'']
    {R : QSys H τ E O d} {M : QSys H' υ E O d} {I : QSys H'' τ' E O d} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : QRealizes R M ε₁) (h₂ : QRealizes M I ε₂) : QRealizes R I (ε₁ + ε₂) :=
  fun ζ => QUCEmulatesDiamond.trans (h₁ ζ) (h₂ ζ)

/-! ## Two facts on the diamond-distance bound -/

/-- Restricting the inputs of two channels along a map `φ` keeps a diamond-distance bound. -/
theorem quc_precomp {α α' β : Type} {ε : ℝ≥0∞} {f g : α → QComp d β}
    {hf : IsCPChannel f} {hg : IsCPChannel g} (h : QUCEmulatesDiamond ε f g hf hg)
    (φ : α' → α) :
    QUCEmulatesDiamond ε (fun a => f (φ a)) (fun a => g (φ a)) (fun a => hf (φ a))
      (fun a => hg (φ a)) :=
  le_trans (iSup_le fun r => le_iSup_of_le r (iSup_le fun D => le_iSup_of_le D
    (iSup_le fun a => le_iSup_of_le (φ a) le_rfl))) h

/-- A diamond-distance bound transported along equalities of the two channels. -/
theorem quc_congr {α β : Type} {ε : ℝ≥0∞} {f f' g g' : α → QComp d β}
    {hf : IsCPChannel f} {hg : IsCPChannel g} (hf' : IsCPChannel f') (hg' : IsCPChannel g')
    (h : QUCEmulatesDiamond ε f g hf hg) (ef : f = f') (eg : g = g') :
    QUCEmulatesDiamond ε f' g' hf' hg' := by
  subst ef eg
  exact h

/-! ## Simulators -/

/-- A simulator with classical state `σ` between the real interface (events `E`, outputs `O`)
and the ideal interface (events `EG`, outputs `OG`). It translates each real event to an
ideal event and each ideal output to a real output, acting on the environment register. -/
structure QSim (σ E O EG OG : Type) (d : ℕ) where
  /-- Initial simulator state. -/
  init : σ
  /-- Translation of a real event. -/
  pre : σ → E → CPComp d (σ × EG)
  /-- Translation of an ideal output. -/
  post : σ → OG → CPComp d (σ × O)

namespace QSim

variable {σ σ₁ σ₂ EM OM EG OG : Type}

/-- The environment `Z` with the simulator `S` absorbed: an environment for the ideal
interface whose state pairs the state of `Z` with the simulator state. -/
def absorb (S : QSim σ E O EG OG d) (Z : QStrat ζ E O d) : QStrat (ζ × σ) EG OG d where
  rounds := Z.rounds
  init := (Z.init, S.init)
  next c := (Z.next c.1).bind fun a =>
    (S.pre c.2 a.2).bind fun b => SubInstrument.pure ((a.1, b.1), b.2)
  obs c og := (S.post c.2 og).bind fun b =>
    (Z.obs c.1 b.2).bind fun z => SubInstrument.pure (z, b.1)

/-- The identity simulator. -/
def id : QSim Unit E O E O d where
  init := ()
  pre _ e := SubInstrument.pure ((), e)
  post _ o := SubInstrument.pure ((), o)

/-- The composite of a simulator `S₁` from the real to a middle interface and a simulator
`S₂` from the middle to the ideal interface. -/
def comp (S₁ : QSim σ₁ E O EM OM d) (S₂ : QSim σ₂ EM OM EG OG d) :
    QSim (σ₁ × σ₂) E O EG OG d where
  init := (S₁.init, S₂.init)
  pre s e := (S₁.pre s.1 e).bind fun a =>
    (S₂.pre s.2 a.2).bind fun b => SubInstrument.pure ((a.1, b.1), b.2)
  post s og := (S₂.post s.2 og).bind fun b =>
    (S₁.post s.1 b.2).bind fun a => SubInstrument.pure ((a.1, b.1), a.2)

end QSim

variable {σ σ₁ σ₂ EM OM EG OG : Type}

/-- The view of `Z` against the ideal system `I` behind the simulator `S`: the view of the
absorbed environment, projected to the state of `Z`. -/
def simView (I : QSys H' υ EG OG d) (S : QSim σ E O EG OG d) (Z : QStrat ζ E O d) :
    CPComp d ζ :=
  (qview I (S.absorb Z)).bind fun c => SubInstrument.pure c.1

/-- `R` realizes `I` behind the simulator `S` at distance `ε`: for every environment state
type, the view map of `R` and the view map of `I` behind `S` are within diamond distance
`ε`. -/
def QRealizesSim (R : QSys H τ E O d) (I : QSys H' υ EG OG d) (S : QSim σ E O EG OG d)
    (ε : ℝ≥0∞) : Prop :=
  ∀ ζ : Type, QUCEmulatesDiamond ε (fun Z : QStrat ζ E O d => (qview R Z).toQComp)
    (fun Z => (simView I S Z).toQComp) (fun Z => CPComp.branch_cp (qview R Z))
    (fun Z => CPComp.branch_cp (simView I S Z))

/-- Behind the identity simulator the view is the view of the system. -/
theorem simView_id (R : QSys H τ E O d) (Z : QStrat ζ E O d) :
    simView R QSim.id Z = qview R Z :=
  qview_hom R (QSim.id.absorb Z) Z Prod.fst rfl rfl
    (fun c => by
      simp only [QSim.absorb, QSim.id, SubInstrument.bind_assoc, SubInstrument.pure_bind,
        Prod.mk.eta, SubInstrument.bind_pure])
    (fun c o => by
      simp only [QSim.absorb, QSim.id, SubInstrument.bind_assoc, SubInstrument.pure_bind,
        SubInstrument.bind_pure])

/-- Behind a composite simulator the view is the view behind the second simulator of the
environment with the first simulator absorbed, projected to the state of `Z`. -/
theorem simView_comp {τ' H'' : Type} [Fintype H''] [DecidableEq H'']
    (I : QSys H'' τ' EG OG d) (S₁ : QSim σ₁ E O EM OM d) (S₂ : QSim σ₂ EM OM EG OG d)
    (Z : QStrat ζ E O d) :
    simView I (S₁.comp S₂) Z =
      (simView I S₂ (S₁.absorb Z)).bind fun c => SubInstrument.pure c.1 := by
  rw [simView, simView, ← qview_hom I (S₂.absorb (S₁.absorb Z)) ((S₁.comp S₂).absorb Z)
    (fun c => (c.1.1, (c.1.2, c.2))) rfl rfl
    (fun c => by
      simp only [QSim.absorb, QSim.comp, SubInstrument.bind_assoc, SubInstrument.pure_bind])
    (fun c o => by
      simp only [QSim.absorb, QSim.comp, SubInstrument.bind_assoc, SubInstrument.pure_bind])]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind]

/-- Every system realizes itself behind the identity simulator at distance `0`. -/
theorem QRealizesSim.refl (R : QSys H τ E O d) : QRealizesSim R R QSim.id 0 := fun ζ =>
  quc_congr _ _ (QRealizes.refl R ζ) rfl (funext fun Z => by rw [simView_id])

/-- Realization behind a simulator is transitive: the simulators compose and the distances
add. -/
theorem QRealizesSim.trans {τ' H'' : Type} [Fintype H''] [DecidableEq H'']
    {R : QSys H τ E O d} {M : QSys H' υ EM OM d} {I : QSys H'' τ' EG OG d}
    {S₁ : QSim σ₁ E O EM OM d} {S₂ : QSim σ₂ EM OM EG OG d} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : QRealizesSim R M S₁ ε₁) (h₂ : QRealizesSim M I S₂ ε₂) :
    QRealizesSim R I (S₁.comp S₂) (ε₁ + ε₂) := by
  intro ζ
  have hk : IsCPChannel fun c : ζ × σ₁ =>
      CPComp.toQComp (SubInstrument.pure c.1 : CPComp d ζ) :=
    fun c => CPComp.branch_cp _
  have h₂' := QUCEmulatesDiamond.comp_right _ hk
    (fun Z b => by beta_reduce; rw [← CPComp.toQComp_qbind]; exact CPComp.branch_cp _ b)
    (fun Z b => by beta_reduce; rw [← CPComp.toQComp_qbind]; exact CPComp.branch_cp _ b)
    (quc_precomp (h₂ (ζ × σ₁)) (QSim.absorb S₁ (ζ := ζ)))
  refine QUCEmulatesDiamond.trans (h₁ ζ) (quc_congr _ _ h₂' ?_ ?_)
  · exact funext fun Z => (CPComp.toQComp_qbind _ _).symm
  · exact funext fun Z => by rw [simView_comp]; exact (CPComp.toQComp_qbind _ _).symm

end CatCrypt.Quantum.ReactiveUC

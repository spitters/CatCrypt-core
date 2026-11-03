/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizesMem
public import CatCryptCore.Crypto.UCTransport

/-!
# Environment-dependent quantum realization and quantum environment pullbacks

Quantum realization with an environment-dependent bound. The diamond distance of two views at
one environment is `cpDist p q`: the diamond distance of the two instruments `p` and `q`
on `Fin d`, each read as a channel with the one-point input. `QRealizesB R I b` bounds, for
every environment `Z`, the diamond distance of the views of `Z` against `R` and against `I` by
`b ζ Z`; the bound `b` is a function of the quantum environment. `QRealizesSimB` and
`QRealizesSimQB` are the same notion behind a simulator, the second against environments with a
memory register. Each is reflexive at the zero bound and transitive with the sum of the bounds,
the second bound evaluated at the environment with the first simulator absorbed. The constant
bound is an instance: `QRealizes R I ε` holds iff `QRealizesB R I (fun _ _ => ε)`
(`QRealizes_iff_const`), and likewise for `QRealizesSim` and `QRealizesSimQ`.

Quantum environment pullbacks. A pullback `F : QEnvPullback E O E' O' d` is a map `F.map` of
quantum systems from the interface `(E, O)` to the interface `(E', O')`, a map `F.pull` of
quantum environments in the opposite direction (the environment reduction `Z ↦ Z·C`, with
state `F.Ctx ζ` over an environment with state `ζ`) and a projection `F.out` of the state of
the pulled-back environment to the state of `Z`, such that the view of `Z` against `F.map X`
is the view of `F.pull Z` against `X`, projected by `F.out`. This is the quantum analogue of the
environment pullback `EnvPullback` of `CatCrypt.Crypto.UCPullback`; the advantage equality is
replaced by the view equation, which gives the diamond-distance inequality
`cpDist_map_le` by data processing.

**Pullback law** (`QEnvPullback.realizes_map`): if `X` realizes `Y` with bound `b`, then
`F.map X` realizes `F.map Y` with bound `b ∘ F.pull`. Pullbacks compose (`QEnvPullback.comp`)
with unit `QEnvPullback.id`, and a context with two holes is two pullbacks and
`QRealizesB.trans` (`QEnvPullback.realizes_twoHole`).

Simulator absorption is a quantum context with one hole: `QSim.attach S Y` runs the system `Y`
of the ideal interface behind the simulator `S`, and its view against `Z` is the view of `Y`
against the absorbed environment `S.absorb Z` (`qview_attach`). `QSim.toQEnvPullback` is the
pullback with `pull = S.absorb`, and realization behind `S` is realization of `S.attach I`
(`QRealizesSimB_iff_attach`).

## Main definitions

* `cpDist`, `QRealizesB`, `QRealizesSimB`, `QRealizesSimQB`
* `QEnvPullback`, `QEnvPullback.id`, `QEnvPullback.comp`
* `QSim.attach`, `QSim.toQEnvPullback`

## Main results

* `QRealizesB.refl`, `QRealizesB.trans`, `QRealizes_iff_const`, and the same for the simulator
  forms
* `QEnvPullback.realizes_map`, `QEnvPullback.realizes_map_comp`,
  `QEnvPullback.realizes_twoHole`
* `qview_attach`, `QRealizesSimB_iff_attach`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open CatCrypt.Crypto.UCMonad.DiamondNorm
open UCMonad.QuantumUC
open CatCrypt.Crypto.UCTransport (QSysObj)
open scoped ENNReal

variable {H H' K : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype K] [DecidableEq K]
variable {τ υ ζ E O EG OG EM OM : Type} {d : ℕ}

/-! ## Diamond distance at one environment -/

/-- The diamond distance of two instruments on `Fin d`, each read as a channel with the
one-point input. -/
def cpDist {α : Type} (p q : CPComp d α) : ℝ≥0∞ :=
  qdistDiamond (fun _ : Unit => p.toQComp) (fun _ => q.toQComp) (fun _ => CPComp.branch_cp p)
    (fun _ => CPComp.branch_cp q)

/-- The diamond distance of an instrument to itself is `0`. -/
theorem cpDist_self {α : Type} (p : CPComp d α) : cpDist p p = 0 :=
  qdistDiamond_self _ _

/-- Triangle inequality of the diamond distance of instruments. -/
theorem cpDist_triangle {α : Type} (p q s : CPComp d α) :
    cpDist p s ≤ cpDist p q + cpDist q s :=
  qdistDiamond_triangle _ _ _ _ _ _

/-- Post-processing both instruments by a common map of outcomes does not increase the
diamond distance. -/
theorem cpDist_bind_pure_le {α β : Type} (p q : CPComp d α) (f : α → β) :
    cpDist (p.bind fun a => SubInstrument.pure (f a))
      (q.bind fun a => SubInstrument.pure (f a)) ≤ cpDist p q := by
  have hk : IsCPChannel fun c : α => CPComp.toQComp (SubInstrument.pure (f c) : CPComp d β) :=
    fun c => CPComp.branch_cp _
  have h0 : QUCEmulatesDiamond (cpDist p q) (fun _ : Unit => p.toQComp) (fun _ => q.toQComp)
      (fun _ => CPComp.branch_cp p) (fun _ => CPComp.branch_cp q) := le_refl (cpDist p q)
  have h := QUCEmulatesDiamond.comp_right _ hk
    (fun _ b => by beta_reduce; rw [← CPComp.toQComp_qbind]; exact CPComp.branch_cp _ b)
    (fun _ b => by beta_reduce; rw [← CPComp.toQComp_qbind]; exact CPComp.branch_cp _ b) h0
  exact quc_congr _ _ h (funext fun _ => (CPComp.toQComp_qbind _ _).symm)
    (funext fun _ => (CPComp.toQComp_qbind _ _).symm)

/-- A diamond-distance bound between two families of views is the same bound at each member. -/
theorem quc_iff_cpDist {α β : Type} {ε : ℝ≥0∞} (f g : α → CPComp d β) :
    QUCEmulatesDiamond ε (fun a => (f a).toQComp) (fun a => (g a).toQComp)
      (fun a => CPComp.branch_cp (f a)) (fun a => CPComp.branch_cp (g a)) ↔
      ∀ a, cpDist (f a) (g a) ≤ ε := by
  constructor
  · intro h a
    exact quc_precomp h (fun _ : Unit => a)
  · intro h
    unfold QUCEmulatesDiamond qdistDiamond qdist
    refine iSup_le fun r => iSup_le fun D => iSup_le fun a => ?_
    have ha := h a
    unfold cpDist qdistDiamond qdist at ha
    refine le_trans ?_ ha
    exact le_iSup_of_le r (le_iSup_of_le D (le_iSup_of_le () le_rfl))

/-! ## Environment-dependent realization -/

/-- `R` realizes `I` with the environment-dependent bound `b`: for every environment `Z`
with state `ζ`, the views of `Z` against `R` and against `I` are within diamond distance
`b ζ Z`. -/
def QRealizesB (R : QSys H τ E O d) (I : QSys H' υ E O d)
    (b : (ζ : Type) → QStrat ζ E O d → ℝ≥0∞) : Prop :=
  ∀ (ζ : Type) (Z : QStrat ζ E O d), cpDist (qview R Z) (qview I Z) ≤ b ζ Z

/-- Every system realizes itself with the zero bound. -/
theorem QRealizesB.refl (R : QSys H τ E O d) : QRealizesB R R fun _ _ => 0 := fun _ Z => by
  rw [cpDist_self]

/-- Realization with environment-dependent bounds is transitive; the bounds add. -/
theorem QRealizesB.trans {τ' H'' : Type} [Fintype H''] [DecidableEq H'']
    {R : QSys H τ E O d} {M : QSys H' υ E O d} {I : QSys H'' τ' E O d}
    {b₁ b₂ : (ζ : Type) → QStrat ζ E O d → ℝ≥0∞}
    (h₁ : QRealizesB R M b₁) (h₂ : QRealizesB M I b₂) :
    QRealizesB R I fun ζ Z => b₁ ζ Z + b₂ ζ Z := fun ζ Z =>
  le_trans (cpDist_triangle _ (qview M Z) _) (add_le_add (h₁ ζ Z) (h₂ ζ Z))

/-- Monotonicity in the bound. -/
theorem QRealizesB.mono {R : QSys H τ E O d} {I : QSys H' υ E O d}
    {b₁ b₂ : (ζ : Type) → QStrat ζ E O d → ℝ≥0∞} (h : QRealizesB R I b₁)
    (hle : ∀ ζ Z, b₁ ζ Z ≤ b₂ ζ Z) : QRealizesB R I b₂ := fun ζ Z =>
  le_trans (h ζ Z) (hle ζ Z)

/-- Realization at distance `ε` is realization with the constant bound `ε`. -/
theorem QRealizes_iff_const (R : QSys H τ E O d) (I : QSys H' υ E O d) (ε : ℝ≥0∞) :
    QRealizes R I ε ↔ QRealizesB R I fun _ _ => ε :=
  forall_congr' fun ζ => quc_iff_cpDist (fun Z : QStrat ζ E O d => qview R Z) _

/-! ## Environment-dependent realization behind a simulator -/

section Sim

variable {σ σ₁ σ₂ : Type}

/-- `R` realizes `I` behind the simulator `S` with the environment-dependent bound `b`. -/
def QRealizesSimB (R : QSys H τ E O d) (I : QSys H' υ EG OG d) (S : QSim σ E O EG OG d)
    (b : (ζ : Type) → QStrat ζ E O d → ℝ≥0∞) : Prop :=
  ∀ (ζ : Type) (Z : QStrat ζ E O d), cpDist (qview R Z) (simView I S Z) ≤ b ζ Z

/-- Realization behind `S` at distance `ε` is realization behind `S` with the constant bound
`ε`. -/
theorem QRealizesSim_iff_const (R : QSys H τ E O d) (I : QSys H' υ EG OG d)
    (S : QSim σ E O EG OG d) (ε : ℝ≥0∞) :
    QRealizesSim R I S ε ↔ QRealizesSimB R I S fun _ _ => ε :=
  forall_congr' fun ζ => quc_iff_cpDist (fun Z : QStrat ζ E O d => qview R Z) _

/-- Every system realizes itself behind the identity simulator with the zero bound. -/
theorem QRealizesSimB.refl (R : QSys H τ E O d) : QRealizesSimB R R QSim.id fun _ _ => 0 :=
  fun _ Z => by rw [simView_id, cpDist_self]

/-- Realization behind a simulator with environment-dependent bounds is transitive: the
simulators compose and the second bound is evaluated at the environment with the first
simulator absorbed. -/
theorem QRealizesSimB.trans {τ' H'' : Type} [Fintype H''] [DecidableEq H'']
    {R : QSys H τ E O d} {M : QSys H' υ EM OM d} {I : QSys H'' τ' EG OG d}
    {S₁ : QSim σ₁ E O EM OM d} {S₂ : QSim σ₂ EM OM EG OG d}
    {b₁ : (ζ : Type) → QStrat ζ E O d → ℝ≥0∞} {b₂ : (ζ : Type) → QStrat ζ EM OM d → ℝ≥0∞}
    (h₁ : QRealizesSimB R M S₁ b₁) (h₂ : QRealizesSimB M I S₂ b₂) :
    QRealizesSimB R I (S₁.comp S₂) fun ζ Z => b₁ ζ Z + b₂ (ζ × σ₁) (S₁.absorb Z) := by
  intro ζ Z
  refine le_trans (cpDist_triangle _ (simView M S₁ Z) _) (add_le_add (h₁ ζ Z) ?_)
  rw [simView_comp]
  exact le_trans (cpDist_bind_pure_le _ _ Prod.fst) (h₂ _ _)

end Sim

/-! ## Environment-dependent realization against environments with memory -/

section SimQ

variable {M M₁ M₂ σ σ₁ σ₂ : Type} [Fintype M] [DecidableEq M] [Fintype M₁] [DecidableEq M₁]
  [Fintype M₂] [DecidableEq M₂]

/-- `R` realizes `I` behind the simulator `S` with a private register, with the
environment-dependent bound `b`: for every memory register `K` and every environment `Z` with
memory `K`, the views are within diamond distance `b K ζ Z`. -/
def QRealizesSimQB (R : QSys H τ E O d) (I : QSys H' υ EG OG d) (S : QSimQ M σ E O EG OG d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞) :
    Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ζ : Type) (Z : QStratQ K ζ E O d),
    cpDist (qviewQ R Z) (simViewQ I S Z) ≤ b K ζ Z

/-- Realization behind `S` with a private register at distance `ε` is the same realization
with the constant bound `ε`. -/
theorem QRealizesSimQ_iff_const (R : QSys H τ E O d) (I : QSys H' υ EG OG d)
    (S : QSimQ M σ E O EG OG d) (ε : ℝ≥0∞) :
    QRealizesSimQ R I S ε ↔ QRealizesSimQB R I S fun _ _ _ _ _ => ε := by
  constructor
  · intro h K _ _ ζ
    exact (quc_iff_cpDist (fun Z : QStratQ K ζ E O d => qviewQ R Z) _).1 (h K ζ)
  · intro h K _ _ ζ
    exact (quc_iff_cpDist (fun Z : QStratQ K ζ E O d => qviewQ R Z) _).2 (h K ζ)

/-- Every system realizes itself behind the identity simulator with the zero bound. -/
theorem QRealizesSimQB.refl (R : QSys H τ E O d) :
    QRealizesSimQB R R QSimQ.id fun _ _ _ _ _ => 0 :=
  fun _ _ _ _ Z => by rw [simViewQ_id, cpDist_self]

/-- Realization behind a simulator with a private register and environment-dependent bounds is
transitive: the simulators compose, their registers are tensored, and the second bound is
evaluated at the environment with the first simulator absorbed. -/
theorem QRealizesSimQB.trans {τ' H'' : Type} [Fintype H''] [DecidableEq H'']
    {R : QSys H τ E O d} {M' : QSys H' υ EM OM d} {I : QSys H'' τ' EG OG d}
    {S₁ : QSimQ M₁ σ₁ E O EM OM d} {S₂ : QSimQ M₂ σ₂ EM OM EG OG d}
    {b₁ : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    {b₂ : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ EM OM d →
      ℝ≥0∞}
    (h₁ : QRealizesSimQB R M' S₁ b₁) (h₂ : QRealizesSimQB M' I S₂ b₂) :
    QRealizesSimQB R I (S₁.comp S₂)
      fun K _ _ ζ Z => b₁ K ζ Z + b₂ (K × M₁) (ζ × σ₁) (S₁.absorb Z) := by
  intro K _ _ ζ Z
  refine le_trans (cpDist_triangle _ (simViewQ M' S₁ Z) _) (add_le_add (h₁ K ζ Z) ?_)
  rw [simViewQ_comp]
  exact le_trans (cpDist_bind_pure_le _ _ Prod.fst) (h₂ _ _ _)

end SimQ

/-! ## Quantum environment pullbacks -/

/-- A quantum environment pullback from systems with interface `(E, O)` to systems with
interface `(E', O')`: a map of systems, a map of environments in the opposite direction with
state `Ctx ζ` over an environment with state `ζ`, and a projection `out` of that state, such
that the view of `Z` against the image of an admissible system is the view of `pull Z` against
the system, projected by `out`. -/
structure QEnvPullback (E O E' O' : Type) (d : ℕ) : Type 1 where
  /-- The map of systems. -/
  map : QSysObj E O d → QSysObj E' O' d
  /-- The state of the pulled-back environment over an environment with state `ζ`. -/
  Ctx : Type → Type
  /-- The map of environments (the environment reduction). -/
  pull : {ζ : Type} → QStrat ζ E' O' d → QStrat (Ctx ζ) E O d
  /-- The projection of the state of the pulled-back environment. -/
  out : {ζ : Type} → Ctx ζ → ζ
  /-- The admissible systems. -/
  Adm : QSysObj E O d → Prop
  /-- The view of `Z` against the image is the projected view of `pull Z`. -/
  view_map : ∀ {X : QSysObj E O d}, Adm X → ∀ {ζ : Type} (Z : QStrat ζ E' O' d),
    qview (map X).sys Z = (qview X.sys (pull Z)).bind fun c => SubInstrument.pure (out c)

namespace QEnvPullback

variable {E₁ O₁ E₂ O₂ E₃ O₃ : Type}

/-- The diamond distance of the views of `Z` against two images is at most that of the views
of `pull Z` against the two systems. -/
theorem cpDist_map_le (F : QEnvPullback E O E₁ O₁ d) {X Y : QSysObj E O d} (hX : F.Adm X)
    (hY : F.Adm Y) {ζ : Type} (Z : QStrat ζ E₁ O₁ d) :
    cpDist (qview (F.map X).sys Z) (qview (F.map Y).sys Z) ≤
      cpDist (qview X.sys (F.pull Z)) (qview Y.sys (F.pull Z)) := by
  rw [F.view_map hX, F.view_map hY]
  exact cpDist_bind_pure_le _ _ _

/-- **Pullback law.** If `X` realizes `Y` with bound `b`, both admissible, then `F.map X`
realizes `F.map Y` with bound `b` at the pulled-back environment. -/
theorem realizes_map (F : QEnvPullback E O E₁ O₁ d) {X Y : QSysObj E O d} (hX : F.Adm X)
    (hY : F.Adm Y) {b : (ζ : Type) → QStrat ζ E O d → ℝ≥0∞} (h : QRealizesB X.sys Y.sys b) :
    QRealizesB (F.map X).sys (F.map Y).sys fun ζ Z => b (F.Ctx ζ) (F.pull Z) := fun _ Z =>
  le_trans (F.cpDist_map_le hX hY Z) (h _ _)

/-- The pullback law at a bound that does not depend on the environment. -/
theorem realizes_map_const (F : QEnvPullback E O E₁ O₁ d) {X Y : QSysObj E O d}
    (hX : F.Adm X) (hY : F.Adm Y) {ε : ℝ≥0∞} (h : QRealizes X.sys Y.sys ε) :
    QRealizes (F.map X).sys (F.map Y).sys ε :=
  (QRealizes_iff_const _ _ ε).2 (F.realizes_map hX hY ((QRealizes_iff_const _ _ ε).1 h))

/-- The identity pullback: systems and environments unchanged. -/
def id (E O : Type) (d : ℕ) : QEnvPullback E O E O d where
  map X := X
  Ctx ζ := ζ
  pull Z := Z
  out c := c
  Adm _ := True
  view_map := by
    intro X _ ζ Z
    exact (SubInstrument.bind_pure _).symm

/-- **Composition of pullbacks**: `G` after `F` on systems, `F.pull` after `G.pull` on
environments, `G.out` after `F.out` on states. -/
def comp (F : QEnvPullback E O E₁ O₁ d) (G : QEnvPullback E₁ O₁ E₂ O₂ d) :
    QEnvPullback E O E₂ O₂ d where
  map X := G.map (F.map X)
  Ctx ζ := F.Ctx (G.Ctx ζ)
  pull Z := F.pull (G.pull Z)
  out c := G.out (F.out c)
  Adm X := F.Adm X ∧ G.Adm (F.map X)
  view_map := by
    intro X hX ζ Z
    rw [G.view_map hX.2, F.view_map hX.1]
    simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind]

/-- **The law for a composite**: the realization is pulled back through `G.pull` and then
through `F.pull`. -/
theorem realizes_map_comp (F : QEnvPullback E O E₁ O₁ d) (G : QEnvPullback E₁ O₁ E₂ O₂ d)
    {X Y : QSysObj E O d} (hX : F.Adm X) (hY : F.Adm Y) (hX' : G.Adm (F.map X))
    (hY' : G.Adm (F.map Y)) {b : (ζ : Type) → QStrat ζ E O d → ℝ≥0∞}
    (h : QRealizesB X.sys Y.sys b) :
    QRealizesB (G.map (F.map X)).sys (G.map (F.map Y)).sys
      fun ζ Z => b (F.Ctx (G.Ctx ζ)) (F.pull (G.pull Z)) :=
  (F.comp G).realizes_map ⟨hX, hX'⟩ ⟨hY, hY'⟩ h

/-- **Composition theorem for two holes.** Let `F` fill the first hole and `G` the second, and
let `F.map X'` and `G.map Y` have the same views. If `X` realizes `X'` with bound `bX` and `Y`
realizes `Y'` with bound `bY`, then `F.map X` realizes `G.map Y'` with the sum of `bX` at
`F.pull` and `bY` at `G.pull`. -/
theorem realizes_twoHole (F : QEnvPullback E₁ O₁ E O d) (G : QEnvPullback E₂ O₂ E O d)
    {X X' : QSysObj E₁ O₁ d} {Y Y' : QSysObj E₂ O₂ d}
    (hX : F.Adm X) (hX' : F.Adm X') (hY : G.Adm Y) (hY' : G.Adm Y')
    (hmid : ∀ (ζ : Type) (Z : QStrat ζ E O d),
      qview (F.map X').sys Z = qview (G.map Y).sys Z)
    {bX : (ζ : Type) → QStrat ζ E₁ O₁ d → ℝ≥0∞} {bY : (ζ : Type) → QStrat ζ E₂ O₂ d → ℝ≥0∞}
    (hXr : QRealizesB X.sys X'.sys bX) (hYr : QRealizesB Y.sys Y'.sys bY) :
    QRealizesB (F.map X).sys (G.map Y').sys
      fun ζ Z => bX (F.Ctx ζ) (F.pull Z) + bY (G.Ctx ζ) (G.pull Z) := by
  intro ζ Z
  refine le_trans (cpDist_triangle _ (qview (F.map X').sys Z) _)
    (add_le_add (F.realizes_map hX hX' hXr ζ Z) ?_)
  rw [hmid ζ Z]
  exact G.realizes_map hY hY' hYr ζ Z

end QEnvPullback

/-! ## Simulator absorption as a quantum context -/

namespace QSim

variable {σ : Type}

/-- The system `Y` of the ideal interface behind the simulator `S`: a system of the real
interface whose state pairs the simulator state with the state of `Y`. -/
def attach (S : QSim σ E O EG OG d) (Y : QSys H υ EG OG d) : QSys H (σ × υ) E O d where
  init := (S.init, Y.init)
  initReg := Y.initReg
  step c e := ((S.pre c.1 e).frame H).bind fun a =>
    (Y.step c.2 a.2).bind fun p =>
      ((S.post a.1 p.2).frame H).bind fun b => SubInstrument.pure ((b.1, p.1), b.2)

omit [DecidableEq H] in
/-- Unfolding lemma: the step of `S.attach Y`. -/
theorem attach_step (S : QSim σ E O EG OG d) (Y : QSys H υ EG OG d) (c : σ × υ) (e : E) :
    (S.attach Y).step c e = ((S.pre c.1 e).frame H).bind fun a =>
      (Y.step c.2 a.2).bind fun p =>
        ((S.post a.1 p.2).frame H).bind fun b => SubInstrument.pure ((b.1, p.1), b.2) :=
  rfl

/-- Unfolding lemma: the event choice of `S.absorb Z`. -/
theorem absorb_next (S : QSim σ E O EG OG d) (Z : QStrat ζ E O d) (c : ζ × σ) :
    (S.absorb Z).next c = (Z.next c.1).bind fun a =>
      (S.pre c.2 a.2).bind fun b => SubInstrument.pure ((a.1, b.1), b.2) :=
  rfl

/-- Unfolding lemma: the observation of `S.absorb Z`. -/
theorem absorb_obs (S : QSim σ E O EG OG d) (Z : QStrat ζ E O d) (c : ζ × σ) (og : OG) :
    (S.absorb Z).obs c og = (S.post c.2 og).bind fun b =>
      (Z.obs c.1 b.2).bind fun z => SubInstrument.pure (z, b.1) :=
  rfl

omit [DecidableEq H] in
/-- The run of `Z` against `S.attach Y` is the run of `S.absorb Z` against `Y`, with the
simulator state moved from the environment configuration to the system configuration. -/
theorem qloop_attach (S : QSim σ E O EG OG d) (Y : QSys H υ EG OG d) (Z : QStrat ζ E O d)
    (n : ℕ) (c : ζ × (σ × υ)) :
    qloop (S.attach Y) Z n c =
      (qloop Y (S.absorb Z) n ((c.1, c.2.1), c.2.2)).bind
        fun c => SubInstrument.pure (c.1.1, (c.1.2, c.2)) := by
  induction n generalizing c with
  | zero => simp only [qloop, SubInstrument.pure_bind]
  | succ n ih =>
    simp only [qloop, attach_step, absorb_next, absorb_obs, ih, SubInstrument.frame_bind,
      SubInstrument.frame_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind]

/-- **Absorption.** The view of `Z` against the system `Y` behind the simulator `S` is the
view of `Z` against `Y` behind `S`. -/
theorem qview_attach (S : QSim σ E O EG OG d) (Y : QSys H υ EG OG d) (Z : QStrat ζ E O d) :
    qview (S.attach Y) Z = simView Y S Z := by
  simp only [qview, simView, qloop_attach, SubInstrument.bind_assoc, SubInstrument.pure_bind]
  rfl

/-- Simulator absorption as a quantum environment pullback: `attach` on systems, `absorb` on
environments, projection to the state of the environment. -/
def toQEnvPullback (S : QSim σ E O EG OG d) : QEnvPullback EG OG E O d where
  map Y := { H := Y.H, τ := σ × Y.τ, sys := S.attach Y.sys }
  Ctx ζ := ζ × σ
  pull Z := S.absorb Z
  out c := c.1
  Adm _ := True
  view_map := by
    intro X _ ζ Z
    exact qview_attach S X.sys Z

end QSim

/-- Realization behind the simulator `S` is realization of `S.attach I`. -/
theorem QRealizesSimB_iff_attach {σ : Type} (R : QSys H τ E O d) (I : QSys H' υ EG OG d)
    (S : QSim σ E O EG OG d) (b : (ζ : Type) → QStrat ζ E O d → ℝ≥0∞) :
    QRealizesSimB R I S b ↔ QRealizesB R (S.attach I) b := by
  simp only [QRealizesSimB, QRealizesB, QSim.qview_attach]

end CatCrypt.Quantum.ReactiveUC

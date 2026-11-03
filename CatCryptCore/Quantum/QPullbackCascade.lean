/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QPullback
public import CatCryptCore.Quantum.QRealizesMemReset

/-!
# Quantum cascade, register transfer and pullbacks over environments with quantum memory

A simulator with a private register `M` attached to a system `Y` with private register `H`
(`QSimQ.attachQ S Y`) is a quantum system whose private register is `H × M`; `QSimQ.attachQL`
places the simulator register on the left, `M × H`. The **register transfer** lemma
(`qloopQ_attachQ`, `qloopQ_attachQL`) moves the simulator register from the system side of the
joint register `(Fin d × (H × M)) × K` to the environment memory `(Fin d × H) × (K × M)`: the
joint run of an environment `Z` with memory `K` against the attached system is, after this
reindexing, the joint run of the absorbed environment `S.absorb Z` (memory `K × M`) against
`Y`. Preparing and discarding the registers on both sides agree
(`appendBasis_transferReg_discard`), so the views agree (`qviewQ_attachQ`, `qviewQ_attachQL`):
the view of `Z` against `S.attachQ Y` is the view of `Z` against `Y` behind `S`.

The **quantum cascade** `QSys.cascade X Y` of a system `X` with events `E` and outputs `M` and a
system `Y` with events `M` and outputs `O` keeps the two private registers separate: its
register is `H × H'`. The system `Y` is a simulator with a private register in front of the hole
`X` (`QSys.asPostSim`), and `X` is a simulator behind the hole `Y` (`QSys.asPreSim`); the
cascade is the attachment of the first (`QSys.cascade` is defined as it) and equals the
attachment of the second (`QSys.cascade_eq_attachQL`).

A **quantum pullback over environments with memory** `F : QEnvPullbackQ E O E' O' d` is the
analogue of `QEnvPullback` for environments with a quantum memory register: the pulled-back
environment of an environment with memory `K` has memory `F.Mem K`, a finite register with
decidable equality. `QRealizesQB R I b` bounds the diamond distance of the views of every
environment with memory by the environment-dependent bound `b`. The **pullback law**
(`QEnvPullbackQ.realizes_map`), identity, composition and the two-hole law hold as for
`QEnvPullback`. Simulator absorption with a private register is a pullback on either side
(`QSimQ.toQEnvPullbackQ`, `QSimQ.toQEnvPullbackQL`), and so is each one-hole cascade context
(`QSys.cascadeLeft`, `QSys.cascadeRight`). The **composition theorem** for the quantum cascade
(`QRealizesQB.cascade`): if `X` realizes `X'` with bound `bX` and `Y` realizes `Y'` with bound
`bY`, then `X.cascade Y` realizes `X'.cascade Y'` with the bound `bX` at the environment that
absorbs `Y` plus `bY` at the environment that absorbs `X'`.

Search words: quantum cascade, private register, register transfer, quantum context, pullback,
composition theorem, environment with quantum memory, simulator absorption.

## Main definitions

* `transferReg`, `QSimQ.attachQ`, `QSimQ.attachQL`
* `QSys.asPostSim`, `QSys.asPreSim`, `QSys.cascade`
* `QRealizesQB`, `QEnvPullbackQ`, `QEnvPullbackQ.id`, `QEnvPullbackQ.comp`
* `QSimQ.toQEnvPullbackQ`, `QSimQ.toQEnvPullbackQL`, `QSys.cascadeLeft`, `QSys.cascadeRight`

## Main results

* `qloopQ_attachQ`, `qloopQ_attachQL` — register transfer for joint runs
* `qviewQ_attachQ`, `qviewQ_attachQL` — absorption of a simulator with a private register
* `QEnvPullbackQ.realizes_map`, `QEnvPullbackQ.realizes_twoHole`
* `QRealizesQB.cascade_left`, `QRealizesQB.cascade_right`, `QRealizesQB.cascade`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open CatCrypt.Crypto.UCTransport (QSysObj)
open scoped ENNReal

/-! ## The register transfer equivalence and the boundary -/

section Transfer

variable (A : Type) {H M R : Type} (K : Type)

/-- The equivalence `(A × R) × K ≃ (A × H) × (K × M)` that, for a system register `R ≃ H × M`,
keeps `H` beside `A` and moves `M` to the right of the environment memory `K`. -/
def transferReg (φ : H × M ≃ R) : (A × R) × K ≃ (A × H) × (K × M) where
  toFun x := ((x.1.1, (φ.symm x.1.2).1), (x.2, (φ.symm x.1.2).2))
  invFun y := ((y.1.1, φ (y.1.2, y.2.2)), y.2.1)
  left_inv x := by simp
  right_inv y := by simp

variable {A K} [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H] [Fintype M]
  [DecidableEq M] [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]

/-- Preparing the system register in `φ (h₀, m₀)` and the memory in `k₀`, running `X` and
discarding both registers is preparing `h₀` and `(k₀, m₀)`, running `X` reindexed by the
register transfer and discarding both registers. -/
theorem appendBasis_transferReg_discard {C : Type} [Fintype C] {γ β : Type} (φ : H × M ≃ R)
    (h₀ : H) (m₀ : M) (k₀ : K) (X : SubInstrument ((A × R) × K) ((A × R) × K) γ)
    (g : γ → SubInstrument A C β) :
    (appendBasis (φ (h₀, m₀))).bind (fun _ => (appendBasis k₀).bind fun _ =>
      X.bind fun c => discardRight.bind fun _ => discardRight.bind fun _ => g c) =
    (appendBasis h₀).bind (fun _ => (appendBasis (k₀, m₀)).bind fun _ =>
      (relabel (transferReg A K φ) X).bind fun c =>
        discardRight.bind fun _ => discardRight.bind fun _ => g c) := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  have hprep : ((appendBasis (k₀, m₀)).branch () ((appendBasis h₀).branch () ρ)).submatrix
      (transferReg A K φ) (transferReg A K φ) =
      (appendBasis k₀).branch () ((appendBasis (φ (h₀, m₀))).branch () ρ) := by
    ext ⟨⟨a, r⟩, k⟩ ⟨⟨a', r'⟩, k'⟩
    simp only [Matrix.submatrix_apply, appendBasis_branch_apply, transferReg, Equiv.coe_fn_mk,
      Prod.ext_iff, ← φ.symm_apply_eq]
    split_ifs <;> simp_all
  have hdisc : ∀ c (Y : Matrix ((A × R) × K) ((A × R) × K) ℂ),
      (discardRight.bind fun _ => discardRight.bind fun _ => g c).branch b Y =
      ((discardRight.bind fun _ => discardRight.bind fun _ => g c :
        SubInstrument ((A × H) × (K × M)) C β)).branch b
        (Y.submatrix (transferReg A K φ).symm (transferReg A K φ).symm) := by
    intro c Y
    simp only [SubInstrument.bind, DSubInstrument.branch_bind_apply, tsum_fintype,
      discardRight_branch_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv φ.symm _ _ fun r => by
      congr 1
      ext a a'
      simp [transferReg]
  simp only [branch_bind_unit]
  rw [SubInstrument.bind, SubInstrument.bind, DSubInstrument.branch_bind_apply,
    DSubInstrument.branch_bind_apply]
  refine tsum_congr fun c => ?_
  rw [relabel_branch, reindexMap_apply, hprep, hdisc]

end Transfer

/-! ## Attaching a simulator with a private register -/

namespace QSimQ

variable {H M K : Type} [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M] [Fintype K]
  [DecidableEq K]
variable {σ υ ζ E O EG OG : Type} {d : ℕ}

/-- The system `Y` of the ideal interface behind the simulator `S` with a private register:
a system of the real interface with private register `H × M` and state pairing the state of
`Y` with the simulator state. -/
def attachQ (S : QSimQ M σ E O EG OG d) (Y : QSys H υ EG OG d) : QSys (H × M) (υ × σ) E O d where
  init := (Y.init, S.init)
  initReg := (Y.initReg, S.initReg)
  step c e := (placeRight H M (S.pre c.2 e)).bind fun a =>
    (placeLeft H M (Y.step c.1 a.2)).bind fun p =>
      (placeRight H M (S.post a.1 p.2)).bind fun b => SubInstrument.pure ((p.1, b.1), b.2)

/-- The system `Y` behind the simulator `S` with the simulator register on the left: private
register `M × H`, state pairing the simulator state with the state of `Y`. -/
def attachQL (S : QSimQ M σ E O EG OG d) (Y : QSys H υ EG OG d) :
    QSys (M × H) (σ × υ) E O d where
  init := (S.init, Y.init)
  initReg := (S.initReg, Y.initReg)
  step c e := (placeLeft M H (S.pre c.1 e)).bind fun a =>
    (placeRight M H (Y.step c.2 a.2)).bind fun p =>
      (placeLeft M H (S.post a.1 p.2)).bind fun b => SubInstrument.pure ((b.1, p.1), b.2)

omit [DecidableEq H] [DecidableEq M] in
/-- Unfolding lemma: the step of `S.attachQ Y`. -/
theorem attachQ_step (S : QSimQ M σ E O EG OG d) (Y : QSys H υ EG OG d) (c : υ × σ) (e : E) :
    (S.attachQ Y).step c e = (placeRight H M (S.pre c.2 e)).bind fun a =>
      (placeLeft H M (Y.step c.1 a.2)).bind fun p =>
        (placeRight H M (S.post a.1 p.2)).bind fun b => SubInstrument.pure ((p.1, b.1), b.2) :=
  rfl

omit [DecidableEq H] [DecidableEq M] in
/-- Unfolding lemma: the step of `S.attachQL Y`. -/
theorem attachQL_step (S : QSimQ M σ E O EG OG d) (Y : QSys H υ EG OG d) (c : σ × υ) (e : E) :
    (S.attachQL Y).step c e = (placeLeft M H (S.pre c.1 e)).bind fun a =>
      (placeRight M H (Y.step c.2 a.2)).bind fun p =>
        (placeLeft M H (S.post a.1 p.2)).bind fun b => SubInstrument.pure ((b.1, p.1), b.2) :=
  rfl

omit [DecidableEq H] [DecidableEq M] [DecidableEq K] in
/-- **Register transfer.** The joint run of `Z` against `S.attachQ Y`, reindexed by moving the
simulator register from the system side to the environment memory, is the joint run of the
absorbed environment `S.absorb Z` against `Y`. -/
theorem qloopQ_attachQ (S : QSimQ M σ E O EG OG d) (Y : QSys H υ EG OG d)
    (Z : QStratQ K ζ E O d) (n : ℕ) (z : ζ) (y : υ) (s : σ) :
    (relabel (transferReg (Fin d) K (Equiv.refl (H × M)))
      (qloopQ (S.attachQ Y) Z n (z, (y, s)))).bind
      (fun c => SubInstrument.pure ((c.1, c.2.2), c.2.1)) =
      qloopQ Y (S.absorb Z) n ((z, s), y) := by
  have hb : ∀ {α β : Type} (p : SubInstrument (Fin d × (K × M)) (Fin d × (K × M)) α)
      (k : α → SubInstrument (Fin d × (K × M)) (Fin d × (K × M)) β),
      envPlace H (p.bind k) = (envPlace H p).bind fun a => envPlace H (k a) := by
    intro α β p k
    simp only [envPlace, SubInstrument.frame_bind, relabel_bind]
  have hp : ∀ {α : Type} (a : α),
      envPlace H (SubInstrument.pure a : SubInstrument (Fin d × (K × M)) (Fin d × (K × M)) α) =
        SubInstrument.pure a := by
    intro α a
    simp only [envPlace, SubInstrument.frame_pure, relabel_pure]
  have hZ : ∀ {α : Type} (w : SubInstrument (Fin d × K) (Fin d × K) α),
      relabel (transferReg (Fin d) K (Equiv.refl (H × M))) (envPlace (H × M) w) =
        envPlace H (placeLeft K M w) := by
    intro α w
    simp only [envPlace, placeLeft, frame_relabel, frame_frame, relabel_relabel]
    exact relabel_frame_eq _ _ _ (Equiv.prodComm _ _) fun _ _ => rfl
  have hS : ∀ {α : Type} (w : SubInstrument (Fin d × M) (Fin d × M) α),
      relabel (transferReg (Fin d) K (Equiv.refl (H × M))) ((placeRight H M w).frame K) =
        envPlace H (placeRight K M w) := by
    intro α w
    simp only [envPlace, placeRight, frame_relabel, frame_frame, relabel_relabel]
    exact relabel_frame_eq _ _ _ (Equiv.prodComm _ _) fun _ _ => rfl
  have hY : ∀ {α : Type} (w : SubInstrument (Fin d × H) (Fin d × H) α),
      relabel (transferReg (Fin d) K (Equiv.refl (H × M))) ((placeLeft H M w).frame K) =
        w.frame (K × M) := by
    intro α w
    rw [← relabel_refl (w.frame (K × M))]
    simp only [placeLeft, frame_relabel, frame_frame, relabel_relabel]
    exact relabel_frame_eq _ _ _ (Equiv.prodComm _ _) fun _ _ => rfl
  induction n generalizing z y s with
  | zero => simp only [qloopQ, relabel_pure, SubInstrument.pure_bind]
  | succ n ih =>
    simp only [qloopQ, attachQ_step, QSimQ.absorb, relabel_bind, SubInstrument.frame_bind,
      SubInstrument.frame_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind,
      hb, hp, hZ, hS, hY, ih]

omit [DecidableEq H] [DecidableEq M] [DecidableEq K] in
/-- **Register transfer**, simulator register on the left: the joint run of `Z` against
`S.attachQL Y`, reindexed by moving the simulator register to the environment memory, is the
joint run of `S.absorb Z` against `Y`. -/
theorem qloopQ_attachQL (S : QSimQ M σ E O EG OG d) (Y : QSys H υ EG OG d)
    (Z : QStratQ K ζ E O d) (n : ℕ) (z : ζ) (s : σ) (y : υ) :
    (relabel (transferReg (Fin d) K (Equiv.prodComm H M))
      (qloopQ (S.attachQL Y) Z n (z, (s, y)))).bind
      (fun c => SubInstrument.pure ((c.1, c.2.1), c.2.2)) =
      qloopQ Y (S.absorb Z) n ((z, s), y) := by
  have hb : ∀ {α β : Type} (p : SubInstrument (Fin d × (K × M)) (Fin d × (K × M)) α)
      (k : α → SubInstrument (Fin d × (K × M)) (Fin d × (K × M)) β),
      envPlace H (p.bind k) = (envPlace H p).bind fun a => envPlace H (k a) := by
    intro α β p k
    simp only [envPlace, SubInstrument.frame_bind, relabel_bind]
  have hp : ∀ {α : Type} (a : α),
      envPlace H (SubInstrument.pure a : SubInstrument (Fin d × (K × M)) (Fin d × (K × M)) α) =
        SubInstrument.pure a := by
    intro α a
    simp only [envPlace, SubInstrument.frame_pure, relabel_pure]
  have hZ : ∀ {α : Type} (w : SubInstrument (Fin d × K) (Fin d × K) α),
      relabel (transferReg (Fin d) K (Equiv.prodComm H M)) (envPlace (M × H) w) =
        envPlace H (placeLeft K M w) := by
    intro α w
    simp only [envPlace, placeLeft, frame_relabel, frame_frame, relabel_relabel]
    exact relabel_frame_eq _ _ _ (Equiv.refl _) fun _ _ => rfl
  have hS : ∀ {α : Type} (w : SubInstrument (Fin d × M) (Fin d × M) α),
      relabel (transferReg (Fin d) K (Equiv.prodComm H M)) ((placeLeft M H w).frame K) =
        envPlace H (placeRight K M w) := by
    intro α w
    simp only [envPlace, placeLeft, placeRight, frame_relabel, frame_frame, relabel_relabel]
    exact relabel_frame_eq _ _ _ (Equiv.prodComm _ _) fun _ _ => rfl
  have hY : ∀ {α : Type} (w : SubInstrument (Fin d × H) (Fin d × H) α),
      relabel (transferReg (Fin d) K (Equiv.prodComm H M)) ((placeRight M H w).frame K) =
        w.frame (K × M) := by
    intro α w
    rw [← relabel_refl (w.frame (K × M))]
    simp only [placeRight, frame_relabel, frame_frame, relabel_relabel]
    exact relabel_frame_eq _ _ _ (Equiv.prodComm _ _) fun _ _ => rfl
  induction n generalizing z s y with
  | zero => simp only [qloopQ, relabel_pure, SubInstrument.pure_bind]
  | succ n ih =>
    simp only [qloopQ, attachQL_step, QSimQ.absorb, relabel_bind, SubInstrument.frame_bind,
      SubInstrument.frame_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind,
      hb, hp, hZ, hS, hY, ih]

/-- **Absorption of a simulator with a private register.** The view of `Z` against
`S.attachQ Y` is the view of `Z` against `Y` behind `S`. -/
theorem qviewQ_attachQ (S : QSimQ M σ E O EG OG d) (Y : QSys H υ EG OG d)
    (Z : QStratQ K ζ E O d) : qviewQ (S.attachQ Y) Z = simViewQ Y S Z := by
  simp only [simViewQ, qviewQ]
  rw [show (S.absorb Z).init = (Z.init, S.init) from rfl,
    show (S.absorb Z).initReg = (Z.initReg, S.initReg) from rfl,
    show (S.absorb Z).rounds = Z.rounds from rfl, ← qloopQ_attachQ S Y Z]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind]
  have h := appendBasis_transferReg_discard (Equiv.refl (H × M)) Y.initReg S.initReg Z.initReg
    (qloopQ (S.attachQ Y) Z Z.rounds (Z.init, Y.init, S.init)) fun c => SubInstrument.pure c.1
  rw [Equiv.refl_apply] at h
  exact h

/-- **Absorption**, simulator register on the left: the view of `Z` against `S.attachQL Y` is
the view of `Z` against `Y` behind `S`. -/
theorem qviewQ_attachQL (S : QSimQ M σ E O EG OG d) (Y : QSys H υ EG OG d)
    (Z : QStratQ K ζ E O d) : qviewQ (S.attachQL Y) Z = simViewQ Y S Z := by
  simp only [simViewQ, qviewQ]
  rw [show (S.absorb Z).init = (Z.init, S.init) from rfl,
    show (S.absorb Z).initReg = (Z.initReg, S.initReg) from rfl,
    show (S.absorb Z).rounds = Z.rounds from rfl, ← qloopQ_attachQL S Y Z]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind]
  have h := appendBasis_transferReg_discard (Equiv.prodComm H M) Y.initReg S.initReg Z.initReg
    (qloopQ (S.attachQL Y) Z Z.rounds (Z.init, S.init, Y.init)) fun c => SubInstrument.pure c.1
  rw [Equiv.prodComm_apply, Prod.swap_prod_mk] at h
  exact h

end QSimQ

/-! ## Realization against environments with memory, with environment-dependent bounds -/

section RealizesQ

variable {H H' H'' M : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype H''] [DecidableEq H''] [Fintype M] [DecidableEq M]
variable {τ υ τ' σ E O EG OG : Type} {d : ℕ}

/-- `R` realizes `I` against environments with quantum memory with the environment-dependent
bound `b`: for every memory register `K` and every environment `Z` with memory `K`, the views of
`Z` against `R` and against `I` are within diamond distance `b K ζ Z`. -/
def QRealizesQB (R : QSys H τ E O d) (I : QSys H' υ E O d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞) :
    Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ζ : Type) (Z : QStratQ K ζ E O d),
    cpDist (qviewQ R Z) (qviewQ I Z) ≤ b K ζ Z

/-- Every system realizes itself against environments with memory with the zero bound. -/
theorem QRealizesQB.refl (R : QSys H τ E O d) : QRealizesQB R R fun _ _ _ _ _ => 0 :=
  fun _ _ _ _ Z => by rw [cpDist_self]

/-- Realization against environments with memory is transitive; the bounds add. -/
theorem QRealizesQB.trans {R : QSys H τ E O d} {N : QSys H' υ E O d} {I : QSys H'' τ' E O d}
    {b₁ b₂ : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d →
      ℝ≥0∞}
    (h₁ : QRealizesQB R N b₁) (h₂ : QRealizesQB N I b₂) :
    QRealizesQB R I fun K _ _ ζ Z => b₁ K ζ Z + b₂ K ζ Z := fun K _ _ ζ Z =>
  le_trans (cpDist_triangle _ (qviewQ N Z) _) (add_le_add (h₁ K ζ Z) (h₂ K ζ Z))

/-- Realization against environments with memory is realization behind the identity
simulator. -/
theorem QRealizesQB_iff_simQB_id (R : QSys H τ E O d) (I : QSys H' υ E O d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d →
      ℝ≥0∞) :
    QRealizesQB R I b ↔ QRealizesSimQB R I QSimQ.id b := by
  simp only [QRealizesQB, QRealizesSimQB, simViewQ_id]

/-- Realization against environments with memory gives realization against memoryless
environments, with the bound at the environment with the one-point memory register. -/
theorem QRealizesQB.toQRealizesB {R : QSys H τ E O d} {I : QSys H' υ E O d}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d →
      ℝ≥0∞}
    (h : QRealizesQB R I b) : QRealizesB R I fun ζ Z => b Unit ζ Z.toQ := fun ζ Z => by
  rw [← qviewQ_toQ, ← qviewQ_toQ]
  exact h Unit ζ Z.toQ

/-- Realization behind a simulator with a private register is realization of the system with
the simulator attached. -/
theorem QRealizesSimQB_iff_attachQ (R : QSys H τ E O d) (I : QSys H' υ EG OG d)
    (S : QSimQ M σ E O EG OG d)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d →
      ℝ≥0∞) :
    QRealizesSimQB R I S b ↔ QRealizesQB R (S.attachQ I) b := by
  simp only [QRealizesSimQB, QRealizesQB, QSimQ.qviewQ_attachQ]

end RealizesQ

/-! ## Quantum environment pullbacks over environments with memory -/

/-- A quantum environment pullback over environments with quantum memory, from systems with
interface `(E, O)` to systems with interface `(E', O')`: a map of systems, a map `pull` of
environments in the opposite direction that sends an environment with memory `K` and state `ζ`
to one with memory `Mem K` and state `Ctx ζ`, and a projection `out` of that state, such that
the view of `Z` against the image of an admissible system is the view of `pull Z` against the
system, projected by `out`. -/
structure QEnvPullbackQ (E O E' O' : Type) (d : ℕ) : Type 1 where
  /-- The map of systems. -/
  map : QSysObj E O d → QSysObj E' O' d
  /-- The memory register of the pulled-back environment over an environment with memory
  `K`. -/
  Mem : Type → Type
  /-- The memory register of the pulled-back environment is finite. -/
  [memFin : ∀ (K : Type) [Fintype K] [DecidableEq K], Fintype (Mem K)]
  /-- The memory register of the pulled-back environment has decidable equality. -/
  [memDec : ∀ (K : Type) [Fintype K] [DecidableEq K], DecidableEq (Mem K)]
  /-- The state of the pulled-back environment over an environment with state `ζ`. -/
  Ctx : Type → Type
  /-- The map of environments (the environment reduction). -/
  pull : {K : Type} → [Fintype K] → [DecidableEq K] → {ζ : Type} → QStratQ K ζ E' O' d →
    QStratQ (Mem K) (Ctx ζ) E O d
  /-- The projection of the state of the pulled-back environment. -/
  out : {ζ : Type} → Ctx ζ → ζ
  /-- The admissible systems. -/
  Adm : QSysObj E O d → Prop
  /-- The view of `Z` against the image is the projected view of `pull Z`. -/
  view_map : ∀ {X : QSysObj E O d}, Adm X → ∀ {K : Type} [Fintype K] [DecidableEq K]
    {ζ : Type} (Z : QStratQ K ζ E' O' d),
    qviewQ (map X).sys Z = (qviewQ X.sys (pull Z)).bind fun c => SubInstrument.pure (out c)

attribute [instance] QEnvPullbackQ.memFin QEnvPullbackQ.memDec

namespace QEnvPullbackQ

variable {E O E₁ O₁ E₂ O₂ : Type} {d : ℕ}

/-- **Pullback law.** If `X` realizes `Y` against environments with memory with bound `b`, both
admissible, then `F.map X` realizes `F.map Y` with bound `b` at the pulled-back environment. -/
theorem realizes_map (F : QEnvPullbackQ E O E₁ O₁ d) {X Y : QSysObj E O d} (hX : F.Adm X)
    (hY : F.Adm Y)
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    (h : QRealizesQB X.sys Y.sys b) :
    QRealizesQB (F.map X).sys (F.map Y).sys fun K _ _ ζ Z => b (F.Mem K) (F.Ctx ζ) (F.pull Z) :=
  fun K _ _ ζ Z => by
    rw [F.view_map hX, F.view_map hY]
    exact le_trans (cpDist_bind_pure_le _ _ _) (h _ _ _)

/-- The identity pullback over environments with memory. -/
def id (E O : Type) (d : ℕ) : QEnvPullbackQ E O E O d where
  map X := X
  Mem K := K
  memFin _ inst _ := inst
  memDec _ _ inst := inst
  Ctx ζ := ζ
  pull Z := Z
  out c := c
  Adm _ := True
  view_map := by
    intro X _ K _ _ ζ Z
    exact (SubInstrument.bind_pure _).symm

/-- **Composition of pullbacks over environments with memory**: `G` after `F` on systems,
`F.pull` after `G.pull` on environments, memory registers nested. -/
def comp (F : QEnvPullbackQ E O E₁ O₁ d) (G : QEnvPullbackQ E₁ O₁ E₂ O₂ d) :
    QEnvPullbackQ E O E₂ O₂ d where
  map X := G.map (F.map X)
  Mem K := F.Mem (G.Mem K)
  memFin _ _ _ := inferInstance
  memDec _ _ _ := inferInstance
  Ctx ζ := F.Ctx (G.Ctx ζ)
  pull Z := F.pull (G.pull Z)
  out c := G.out (F.out c)
  Adm X := F.Adm X ∧ G.Adm (F.map X)
  view_map := by
    intro X hX K _ _ ζ Z
    rw [G.view_map hX.2, F.view_map hX.1]
    simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind]

/-- **Composition theorem for two holes** against environments with memory. Let `F` fill the
first hole and `G` the second, and let `F.map X'` and `G.map Y` have the same views. If `X`
realizes `X'` with bound `bX` and `Y` realizes `Y'` with bound `bY`, then `F.map X` realizes
`G.map Y'` with the sum of `bX` at `F.pull` and `bY` at `G.pull`. -/
theorem realizes_twoHole (F : QEnvPullbackQ E₁ O₁ E O d) (G : QEnvPullbackQ E₂ O₂ E O d)
    {X X' : QSysObj E₁ O₁ d} {Y Y' : QSysObj E₂ O₂ d}
    (hX : F.Adm X) (hX' : F.Adm X') (hY : G.Adm Y) (hY' : G.Adm Y')
    (hmid : ∀ (K : Type) [Fintype K] [DecidableEq K] (ζ : Type) (Z : QStratQ K ζ E O d),
      qviewQ (F.map X').sys Z = qviewQ (G.map Y).sys Z)
    {bX : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E₁ O₁ d →
      ℝ≥0∞}
    {bY : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E₂ O₂ d →
      ℝ≥0∞}
    (hXr : QRealizesQB X.sys X'.sys bX) (hYr : QRealizesQB Y.sys Y'.sys bY) :
    QRealizesQB (F.map X).sys (G.map Y').sys fun K _ _ ζ Z =>
      bX (F.Mem K) (F.Ctx ζ) (F.pull Z) + bY (G.Mem K) (G.Ctx ζ) (G.pull Z) := by
  intro K _ _ ζ Z
  refine le_trans (cpDist_triangle _ (qviewQ (F.map X').sys Z) _)
    (add_le_add (F.realizes_map hX hX' hXr K ζ Z) ?_)
  rw [hmid K ζ Z]
  exact G.realizes_map hY hY' hYr K ζ Z

end QEnvPullbackQ

/-! ## Simulator absorption with a private register as a pullback -/

namespace QSimQ

variable {M σ E O EG OG : Type} [Fintype M] [DecidableEq M] {d : ℕ}

/-- Absorption of a simulator with a private register as a pullback over environments with
memory: `attachQ` on systems, `absorb` on environments, the simulator register added to the
memory. -/
def toQEnvPullbackQ (S : QSimQ M σ E O EG OG d) : QEnvPullbackQ EG OG E O d where
  map Y := { H := Y.H × M, τ := Y.τ × σ, sys := S.attachQ Y.sys }
  Mem K := K × M
  memFin _ _ _ := inferInstance
  memDec _ _ _ := inferInstance
  Ctx ζ := ζ × σ
  pull Z := S.absorb Z
  out c := c.1
  Adm _ := True
  view_map := by
    intro X _ K _ _ ζ Z
    exact qviewQ_attachQ S X.sys Z

/-- Absorption of a simulator with a private register, the simulator register on the left of
the system register, as a pullback over environments with memory. -/
def toQEnvPullbackQL (S : QSimQ M σ E O EG OG d) : QEnvPullbackQ EG OG E O d where
  map Y := { H := M × Y.H, τ := σ × Y.τ, sys := S.attachQL Y.sys }
  Mem K := K × M
  memFin _ _ _ := inferInstance
  memDec _ _ _ := inferInstance
  Ctx ζ := ζ × σ
  pull Z := S.absorb Z
  out c := c.1
  Adm _ := True
  view_map := by
    intro X _ K _ _ ζ Z
    exact qviewQ_attachQL S X.sys Z

end QSimQ

/-! ## The quantum cascade -/

namespace QSys

variable {H H' H₁ H₂ : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂]
variable {τ υ τ₁ υ₂ E M O : Type} {d : ℕ}

/-- The system `Y` with events `M` as a simulator with private register `H'` in front of a
system with outputs `M`: events pass through, outputs of the hole are fed to `Y`. -/
def asPostSim (E : Type) (Y : QSys H' υ M O d) : QSimQ H' υ E O E M d where
  init := Y.init
  initReg := Y.initReg
  pre u e := SubInstrument.pure (u, e)
  post := Y.step

/-- The system `X` with outputs `M` as a simulator with private register `H` behind a system
with events `M`: events are fed to `X`, outputs of the hole pass through. -/
def asPreSim (O : Type) (X : QSys H τ E M d) : QSimQ H τ E O M O d where
  init := X.init
  initReg := X.initReg
  pre := X.step
  post t o := SubInstrument.pure (t, o)

/-- The cascade of quantum systems with separate private registers: the outputs of `X` are the
events of `Y`, and the private register is `H × H'`. It is `X` with `Y` attached in front as a
simulator. -/
def cascade (X : QSys H τ E M d) (Y : QSys H' υ M O d) : QSys (H × H') (τ × υ) E O d :=
  (asPostSim E Y).attachQ X

omit [DecidableEq H] [DecidableEq H'] in
/-- The cascade is `Y` with `X` attached behind it as a simulator, its register on the left. -/
theorem cascade_eq_attachQL (X : QSys H τ E M d) (Y : QSys H' υ M O d) :
    X.cascade Y = (asPreSim O X).attachQL Y := by
  simp only [cascade, QSimQ.attachQ, QSimQ.attachQL, asPostSim, asPreSim]
  congr 1
  funext c e
  simp only [placeRight, placeLeft, SubInstrument.frame_pure, relabel_pure,
    SubInstrument.pure_bind]

/-- The cascade context with the hole on the left, `- ≫ Y`, as a pullback: the private register
of `Y` moves to the environment memory. -/
def cascadeLeft (E : Type) (Y : QSys H' υ M O d) : QEnvPullbackQ E M E O d :=
  (asPostSim E Y).toQEnvPullbackQ

/-- The cascade context with the hole on the right, `X ≫ -`, as a pullback: the private
register of `X` moves to the environment memory. -/
def cascadeRight (O : Type) (X : QSys H τ E M d) : QEnvPullbackQ M O E O d :=
  (asPreSim O X).toQEnvPullbackQL

end QSys

namespace QRealizesQB

variable {H H' H₁ H₂ : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂]
variable {τ υ τ₁ υ₂ E M O : Type} {d : ℕ}

/-- **Congruence of the cascade, hole on the left.** If `X` realizes `X'` with bound `b`, then
`X.cascade Y` realizes `X'.cascade Y` with bound `b` at the environment that absorbs `Y`. -/
theorem cascade_left {X : QSys H τ E M d} {X' : QSys H₁ τ₁ E M d}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E M d → ℝ≥0∞}
    (h : QRealizesQB X X' b) (Y : QSys H' υ M O d) :
    QRealizesQB (X.cascade Y) (X'.cascade Y)
      fun K _ _ ζ Z => b (K × H') (ζ × υ) ((QSys.asPostSim E Y).absorb Z) :=
  (QSys.cascadeLeft E Y).realizes_map (X := { H := H, τ := τ, sys := X })
    (Y := { H := H₁, τ := τ₁, sys := X' }) trivial trivial h

/-- **Congruence of the cascade, hole on the right.** If `Y` realizes `Y'` with bound `b`, then
`X.cascade Y` realizes `X.cascade Y'` with bound `b` at the environment that absorbs `X`. -/
theorem cascade_right {Y : QSys H' υ M O d} {Y' : QSys H₂ υ₂ M O d}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ M O d → ℝ≥0∞}
    (h : QRealizesQB Y Y' b) (X : QSys H τ E M d) :
    QRealizesQB (X.cascade Y) (X.cascade Y')
      fun K _ _ ζ Z => b (K × H) (ζ × τ) ((QSys.asPreSim O X).absorb Z) := by
  intro K _ _ ζ Z
  rw [QSys.cascade_eq_attachQL, QSys.cascade_eq_attachQL]
  exact (QSys.cascadeRight O X).realizes_map (X := { H := H', τ := υ, sys := Y })
    (Y := { H := H₂, τ := υ₂, sys := Y' }) trivial trivial h K ζ Z

/-- **Composition theorem for the quantum cascade.** If `X` realizes `X'` with bound `bX` and
`Y` realizes `Y'` with bound `bY`, against environments with memory, then `X.cascade Y` realizes
`X'.cascade Y'` with the bound `bX` at the environment that absorbs `Y` plus `bY` at the
environment that absorbs `X'`. -/
theorem cascade {X : QSys H τ E M d} {X' : QSys H₁ τ₁ E M d} {Y : QSys H' υ M O d}
    {Y' : QSys H₂ υ₂ M O d}
    {bX : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E M d → ℝ≥0∞}
    {bY : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ M O d → ℝ≥0∞}
    (hX : QRealizesQB X X' bX) (hY : QRealizesQB Y Y' bY) :
    QRealizesQB (X.cascade Y) (X'.cascade Y') fun K _ _ ζ Z =>
      bX (K × H') (ζ × υ) ((QSys.asPostSim E Y).absorb Z) +
        bY (K × H₁) (ζ × τ₁) ((QSys.asPreSim O X').absorb Z) :=
  (hX.cascade_left Y).trans (hY.cascade_right X')

end QRealizesQB

end CatCrypt.Quantum.ReactiveUC

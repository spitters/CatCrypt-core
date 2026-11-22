/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizes

/-!
# Splitting the view of a quantum reactive system along its outcomes

The view `qview S Z` of an environment `Z` against a quantum reactive system `S` is a
subinstrument whose outcome is the final environment state. Each activation of `S` is a
subinstrument with outcome the new system state and the output. Recording these outcomes gives
the system `QSys.record S`, whose state carries the list of the step outcomes so far, and the
history view `qviewHist S Z`, whose outcome is the final environment state together with the
history of the run. The view is the history view with the history discarded
(`qview_eq_bind_qviewHist`), so its branch at `z` is the sum over all histories of the branches
of the history view at `(z, w)` (`branch_qview_eq_tsum`): the branch at a history is the run with
all the outcomes of the system fixed, a completely positive map. The environment is adaptive,
with any order and number of events. A classification `cls` of the histories groups the sum
(`qviewCls`, `branch_qview_eq_tsum_cls`, `branch_qviewCls_eq_tsum`).

Search words: branch decomposition, outcome history, quantum reactive system, view,
subinstrument, classification of histories.

## Main definitions

* `ReactiveUC.QSys.record`: the system with the history of its step outcomes in its state.
* `ReactiveUC.qviewHist`, `ReactiveUC.qviewCls`: the view with the history of the run, and with
  a classification of it.

## Main results

* `ReactiveUC.qloop_record`, `ReactiveUC.qview_eq_bind_qviewHist`: recording the history does
  not change the run.
* `ReactiveUC.branch_qview_eq_tsum`, `ReactiveUC.branch_qview_eq_tsum_cls`,
  `ReactiveUC.branch_qviewCls_eq_tsum`: the view is the sum of the branch views.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum

/-! ## Recording the outcomes of a system -/

section Generic

variable {H : Type} [Fintype H] [DecidableEq H] {τ ζ E O κ : Type} {d : ℕ}

/-- The system `S` with the history of its step outcomes in its state: each activation runs the
step of `S` and appends its outcome, the new state and the output, to the history. -/
def QSys.record (S : QSys H τ E O d) : QSys H (τ × List (τ × O)) E O d where
  init := (S.init, [])
  initReg := S.initReg
  step c e := (S.step c.1 e).bind fun p => SubInstrument.pure ((p.1, c.2 ++ [p]), p.2)

omit [DecidableEq H] in
/-- Unfolding lemma of `QSys.record`: the step. -/
theorem QSys.record_step (S : QSys H τ E O d) (c : τ × List (τ × O)) (e : E) :
    S.record.step c e =
      (S.step c.1 e).bind fun p => SubInstrument.pure ((p.1, c.2 ++ [p]), p.2) := rfl

omit [DecidableEq H] in
/-- **Recording does not change the run.** The run of the recording system, with the history
discarded, is the run of the system. -/
theorem qloop_record (S : QSys H τ E O d) (Z : QStrat ζ E O d) (n : ℕ) (z : ζ) (t : τ)
    (w : List (τ × O)) :
    (qloop S.record Z n (z, (t, w))).bind (fun c => SubInstrument.pure (c.1, c.2.1)) =
      qloop S Z n (z, t) := by
  induction n generalizing z t w with
  | zero => exact SubInstrument.pure_bind _ _
  | succ n ih =>
    simp only [qloop, QSys.record_step, SubInstrument.bind_assoc, SubInstrument.pure_bind, ih]

/-- The view of `Z` against `S` with the history of the run: the outcome is the final
environment state together with the list of the step outcomes of `S`. -/
def qviewHist (S : QSys H τ E O d) (Z : QStrat ζ E O d) : CPComp d (ζ × List (τ × O)) :=
  (appendBasis S.initReg).bind fun _ =>
    (qloop S.record Z Z.rounds (Z.init, (S.init, []))).bind fun c =>
      discardRight.bind fun _ => SubInstrument.pure (c.1, c.2.2)

/-- The view is the history view with the history discarded. -/
theorem qview_eq_bind_qviewHist (S : QSys H τ E O d) (Z : QStrat ζ E O d) :
    qview S Z = (qviewHist S Z).bind fun c => SubInstrument.pure c.1 := by
  rw [qview, ← qloop_record S Z Z.rounds Z.init S.init []]
  simp only [qviewHist, SubInstrument.bind_assoc, SubInstrument.pure_bind]

/-- The branch at `a` of a subinstrument with the second component of its outcome discarded is
the sum over the second components `b` of the branches at `(a, b)`. -/
theorem branch_bind_pure_fst_apply {A α β : Type} [Fintype A]
    (X : SubInstrument A A (α × β)) (a : α) (ρ : Matrix A A ℂ) :
    (X.bind fun c => SubInstrument.pure c.1).branch a ρ = ∑' b, X.branch (a, b) ρ := by
  rw [← SubInstrument.map_eq_bind_pure, SubInstrument.branch_map_apply]
  let e : β ≃ (Prod.fst ⁻¹' {a} : Set (α × β)) :=
    { toFun := fun b => ⟨(a, b), rfl⟩
      invFun := fun c => c.1.2
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨a', b⟩, h⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
        subst h
        rfl }
  exact (e.tsum_eq (fun c => X.branch c.1 ρ)).symm

/-- **The view as a sum of branch views.** The branch at `z` of the view is the sum over all
histories `w` of the step outcomes of the branch of the history view at `(z, w)`: the run with
the outcomes `w` of the system fixed. -/
theorem branch_qview_eq_tsum (S : QSys H τ E O d) (Z : QStrat ζ E O d) (z : ζ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (qview S Z).branch z ρ = ∑' w, (qviewHist S Z).branch (z, w) ρ := by
  rw [qview_eq_bind_qviewHist, branch_bind_pure_fst_apply]

/-- The view with the history of the run classified by `cls`. -/
def qviewCls (S : QSys H τ E O d) (Z : QStrat ζ E O d) (cls : List (τ × O) → κ) :
    CPComp d (ζ × κ) :=
  (qviewHist S Z).bind fun c => SubInstrument.pure (c.1, cls c.2)

/-- The view is the classified view with the class discarded. -/
theorem qview_eq_bind_qviewCls (S : QSys H τ E O d) (Z : QStrat ζ E O d)
    (cls : List (τ × O) → κ) :
    qview S Z = (qviewCls S Z cls).bind fun c => SubInstrument.pure c.1 := by
  rw [qview_eq_bind_qviewHist, qviewCls, SubInstrument.bind_assoc]
  simp only [SubInstrument.pure_bind]

/-- **The view as a sum over the classes.** The branch at `z` of the view is the sum over the
classes `k` of the branches of the classified view at `(z, k)`. -/
theorem branch_qview_eq_tsum_cls (S : QSys H τ E O d) (Z : QStrat ζ E O d)
    (cls : List (τ × O) → κ) (z : ζ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (qview S Z).branch z ρ = ∑' k, (qviewCls S Z cls).branch (z, k) ρ := by
  rw [qview_eq_bind_qviewCls S Z cls, branch_bind_pure_fst_apply]

/-- **A class as a sum of branch views.** The branch of the classified view at `(z, k)` is the
sum over the histories `w` of class `k` of the branches of the history view at `(z, w)`. -/
theorem branch_qviewCls_eq_tsum (S : QSys H τ E O d) (Z : QStrat ζ E O d)
    (cls : List (τ × O) → κ) (z : ζ) (k : κ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (qviewCls S Z cls).branch (z, k) ρ =
      ∑' w : {w : List (τ × O) // cls w = k}, (qviewHist S Z).branch (z, w.1) ρ := by
  rw [qviewCls, ← SubInstrument.map_eq_bind_pure, SubInstrument.branch_map_apply]
  let e : {w : List (τ × O) // cls w = k} ≃
      ((fun c : ζ × List (τ × O) => (c.1, cls c.2)) ⁻¹' {(z, k)} : Set _) :=
    { toFun := fun w => ⟨(z, w.1), by simp [w.2]⟩
      invFun := fun c => ⟨c.1.2, by
        obtain ⟨⟨z', w⟩, h⟩ := c
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact h.2⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨z', w⟩, h⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rfl }
  exact (e.tsum_eq (fun c => (qviewHist S Z).branch c.1 ρ)).symm

end Generic

end CatCrypt.Quantum.ReactiveUC

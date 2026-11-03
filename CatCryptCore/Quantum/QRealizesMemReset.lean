/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizesMem

/-!
# Reset of a private register and the transfer of views

The reset `rstPriv h₀` of the private register `H` of `A × H`: the partial trace over `H`
followed by the preparation of the basis state `h₀`. It acts on `H` alone
(`frame_rstPriv`), so it commutes with every operation of an environment with quantum memory
(`rstPriv_frame_envPlace_comm`), and it does nothing after the preparation of `h₀`
(`appendBasis_appendBasis_rstPriv`).

A system whose steps keep the private register in its initial basis state, and whose steps agree
with those of a second system after a reset of that register, gives the same view as the second
system to every environment with quantum memory (`qviewQ_eq_of_reset`). This is a transfer
lemma between two systems that differ on states outside the reachable ones.

Search words: reset, private register, quantum memory, transfer of views, partial trace,
basis state preparation, quantum reactive system.

## Main definitions

* `ReactiveUC.rstPriv` — the reset of the private register to a basis state
* `ReactiveUC.resetH` — the reset of a register on its own

## Main results

* `ReactiveUC.rstPriv_branch_apply` — the entries of the reset
* `ReactiveUC.rstPriv_frame_envPlace_comm` — the reset commutes with environment operations
* `ReactiveUC.qloopQ_reset` — joint runs agree after a reset
* `ReactiveUC.qviewQ_eq_of_reset` — the transfer of views
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum

section Reset

/-- The branch of a subinstrument with one outcome sequenced before `k` is the branch of `k`
after the branch of `p`. -/
theorem branch_bind_unit {X Y W β : Type} [Fintype X] [Fintype Y] [Fintype W]
    (p : SubInstrument X Y Unit) (k : Unit → SubInstrument Y W β) (b : β)
    (ρ : Matrix X X ℂ) : (p.bind k).branch b ρ = (k ()).branch b (p.branch () ρ) := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply, tsum_fintype, Fintype.sum_unique]

variable {A H : Type} [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H]

/-- The reset of the private register `H` of `A × H` to the basis state `h₀`: the partial trace
over `H`, then the preparation of `h₀`. -/
def rstPriv (h₀ : H) : SubInstrument (A × H) (A × H) Unit :=
  discardRight.bind fun _ => appendBasis h₀

/-- The entries of the reset: the partial trace over `H` in the block `(h₀, h₀)`. -/
theorem rstPriv_branch_apply (h₀ : H) (ρ : Matrix (A × H) (A × H) ℂ) (x y : A × H) :
    (rstPriv h₀).branch () ρ x y =
      if x.2 = h₀ ∧ y.2 = h₀ then ∑ g, ρ (x.1, g) (y.1, g) else 0 := by
  rw [rstPriv, SubInstrument.bind, DSubInstrument.branch_bind_apply, tsum_fintype,
    Matrix.sum_apply]
  simp only [appendBasis_branch_apply, discardRight_branch_apply, Matrix.submatrix_apply]
  split_ifs <;> simp

/-- The reset of the register `H` on its own to the basis state `h₀`. -/
def resetH (h₀ : H) : SubInstrument H H Unit :=
  relabel (Equiv.punitProd H) (rstPriv (A := Unit) h₀)

/-- The reset of the private register, framed by `K`, is the reset of `H` alone placed beside
`A × K`. -/
theorem frame_rstPriv (h₀ : H) (K : Type) [Fintype K] :
    (rstPriv (A := A) h₀).frame K =
      relabel (midSwap A K H) (OpenSystem.frameLeft (resetH h₀) (A × K)) := by
  refine DSubInstrument.ext <| funext fun u => LinearMap.ext fun ρ => ?_
  cases u
  ext x y
  simp only [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply, relabel_branch,
    reindexMap_apply, Matrix.submatrix_apply, OpenSystem.frameLeft_branch,
    MatrixMap.amplifyLeft_apply, resetH, rstPriv_branch_apply]
  simp [midSwap]

variable {K : Type} [Fintype K] {τ υ ζ E O : Type} {d : ℕ}

/-- The reset of the private register commutes with an operation of an environment with
memory `K`. -/
theorem rstPriv_frame_envPlace_comm (h₀ : H) {α β : Type}
    (w : SubInstrument (Fin d × K) (Fin d × K) α)
    (k : α → SubInstrument ((Fin d × H) × K) ((Fin d × H) × K) β) :
    ((rstPriv h₀).frame K).bind (fun _ => (envPlace H w).bind k) =
      (envPlace H w).bind fun a => ((rstPriv h₀).frame K).bind fun _ => k a := by
  have h := congrArg (relabel (midSwap (Fin d) K H))
    (OpenSystem.frame_bind_frameLeft_comm w (resetH h₀))
  simp only [relabel_bind, relabel_pure] at h
  have h' := congrArg (fun X => X.bind fun ab => k ab.1) h
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind] at h'
  rw [envPlace, frame_rstPriv]
  exact h'.symm

/-- The reset of the private register after the preparation of its basis state `h₀` does
nothing. -/
theorem appendBasis_appendBasis_rstPriv [DecidableEq K] (h₀ : H) (k₀ : K) {β C : Type}
    [Fintype C]
    (X : SubInstrument ((A × H) × K) C β) :
    (appendBasis h₀).bind (fun _ => (appendBasis k₀).bind fun _ =>
      ((rstPriv h₀).frame K).bind fun _ => X) =
      (appendBasis h₀).bind fun _ => (appendBasis k₀).bind fun _ => X := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  simp only [branch_bind_unit]
  congr 1
  ext x y
  simp only [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply, rstPriv_branch_apply,
    Matrix.submatrix_apply, appendBasis_branch_apply]
  split_ifs <;> simp_all

/-- **Joint runs agree after a reset of the private register.** If the steps of `S₁` keep the
private register in `h₀` and agree with the steps of `S₂` up to `f` after a reset to `h₀`, then
the joint runs with every environment with memory agree after a reset to `h₀`. -/
theorem qloopQ_reset {S₁ : QSys H τ E O d} {S₂ : QSys H υ E O d} (Z : QStratQ K ζ E O d)
    (h₀ : H) (f : τ → υ)
    (hpres : ∀ t e, (rstPriv h₀).bind (fun _ => S₁.step t e) =
      ((rstPriv h₀).bind fun _ => S₁.step t e).bind fun p =>
        (rstPriv h₀).bind fun _ => SubInstrument.pure p)
    (hstep : ∀ t e, ((rstPriv h₀).bind fun _ => S₁.step t e).bind
        (fun p => SubInstrument.pure (f p.1, p.2)) =
      (rstPriv h₀).bind fun _ => S₂.step (f t) e)
    (n : ℕ) (z : ζ) (t : τ) :
    ((rstPriv h₀).frame K).bind (fun _ => (qloopQ S₁ Z n (z, t)).bind fun c =>
      SubInstrument.pure (c.1, f c.2)) =
      ((rstPriv h₀).frame K).bind fun _ => qloopQ S₂ Z n (z, f t) := by
  have hp' : ∀ t e {β : Type}
      (g : τ × O → SubInstrument ((Fin d × H) × K) ((Fin d × H) × K) β),
      ((rstPriv h₀).frame K).bind (fun _ => ((S₁.step t e).frame K).bind g) =
        ((rstPriv h₀).frame K).bind fun _ => ((S₁.step t e).frame K).bind fun p =>
          ((rstPriv h₀).frame K).bind fun _ => g p := by
    intro t e β g
    have h := congrArg (fun X => (X.frame K).bind g) (hpres t e)
    simpa only [SubInstrument.frame_bind, SubInstrument.frame_pure, SubInstrument.bind_assoc,
      SubInstrument.pure_bind] using h
  have hs' : ∀ t e {β : Type}
      (g : υ × O → SubInstrument ((Fin d × H) × K) ((Fin d × H) × K) β),
      ((rstPriv h₀).frame K).bind (fun _ => ((S₁.step t e).frame K).bind fun p => g (f p.1, p.2)) =
        ((rstPriv h₀).frame K).bind fun _ => ((S₂.step (f t) e).frame K).bind g := by
    intro t e β g
    have h := congrArg (fun X => (X.frame K).bind g) (hstep t e)
    simpa only [SubInstrument.frame_bind, SubInstrument.frame_pure, SubInstrument.bind_assoc,
      SubInstrument.pure_bind] using h
  induction n generalizing z t with
  | zero => simp only [qloopQ, SubInstrument.pure_bind]
  | succ n ih =>
    simp only [qloopQ, SubInstrument.bind_assoc]
    rw [rstPriv_frame_envPlace_comm, rstPriv_frame_envPlace_comm]
    congr 1
    funext a
    rw [hp']
    have hG : ∀ p : τ × O, ((rstPriv h₀).frame K).bind (fun _ =>
        (envPlace H (Z.obs a.1 p.2)).bind fun z' => (qloopQ S₁ Z n (z', p.1)).bind fun c =>
          SubInstrument.pure (c.1, f c.2)) =
        ((rstPriv h₀).frame K).bind fun _ =>
          (envPlace H (Z.obs a.1 p.2)).bind fun z' => qloopQ S₂ Z n (z', f p.1) := by
      intro p
      rw [rstPriv_frame_envPlace_comm, rstPriv_frame_envPlace_comm]
      congr 1
      funext z'
      exact ih z' p.1
    simp only [hG]
    rw [← hp' t a.2 (fun p => (envPlace H (Z.obs a.1 p.2)).bind fun z' =>
      qloopQ S₂ Z n (z', f p.1))]
    exact hs' t a.2 (fun p => (envPlace H (Z.obs a.1 p.2)).bind fun z' =>
      qloopQ S₂ Z n (z', p.1))

/-- **Views of systems that agree after a reset of the private register.** If the steps of
`S₁` keep the private register in its initial basis state `h₀` when they start in it, and the
steps of `S₁` and `S₂` agree, up to the state map `f`, after a reset of the private register to
`h₀`, then `S₁` and `S₂` give the same view to every environment with memory. -/
theorem qviewQ_eq_of_reset [DecidableEq K] {S₁ : QSys H τ E O d} {S₂ : QSys H υ E O d} (f : τ → υ)
    (hi : S₂.init = f S₁.init) (hr : S₁.initReg = S₂.initReg)
    (hpres : ∀ t e, (rstPriv S₁.initReg).bind (fun _ => S₁.step t e) =
      ((rstPriv S₁.initReg).bind fun _ => S₁.step t e).bind fun p =>
        (rstPriv S₁.initReg).bind fun _ => SubInstrument.pure p)
    (hstep : ∀ t e, ((rstPriv S₁.initReg).bind fun _ => S₁.step t e).bind
        (fun p => SubInstrument.pure (f p.1, p.2)) =
      (rstPriv S₁.initReg).bind fun _ => S₂.step (f t) e)
    (Z : QStratQ K ζ E O d) : qviewQ S₁ Z = qviewQ S₂ Z := by
  have hl := qloopQ_reset Z S₁.initReg f hpres hstep Z.rounds Z.init S₁.init
  have key := congrArg (fun X => X.bind fun c =>
    discardRight.bind fun _ => discardRight.bind fun _ => SubInstrument.pure c.1) hl
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind] at key
  simp only [qviewQ]
  rw [hi, ← hr, ← appendBasis_appendBasis_rstPriv S₁.initReg Z.initReg
      ((qloopQ S₁ Z Z.rounds (Z.init, S₁.init)).bind fun c =>
        discardRight.bind fun _ => discardRight.bind fun _ => SubInstrument.pure c.1),
    ← appendBasis_appendBasis_rstPriv S₁.initReg Z.initReg
      ((qloopQ S₂ Z Z.rounds (Z.init, f S₁.init)).bind fun c =>
        discardRight.bind fun _ => discardRight.bind fun _ => SubInstrument.pure c.1), key]

end Reset

end CatCrypt.Quantum.ReactiveUC

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRHL
public import CatCryptCore.Crypto.UCMonad.DiamondTensorStable

/-!
# Diamond-norm program indistinguishability

`QRHL.qIndist` is the distinguishing distance between two quantum programs over
distinguishers `D` and inputs `ρ` on the program's own dimension `d`, without a
reference register.

This file defines `qIndistDiamond`, the diamond-norm program
indistinguishability (`qIndist` stabilized over all reference registers), and
proves that it is a pseudometric and that it satisfies the frame rule:
tensoring both programs with an independent register does not increase the
diamond distance. The frame rule follows from `qdistDiamond_localOp₁_le`
(tensor-stability of the diamond distance).

A quantum program `C : QComp d α` is presented to the Kleisli-level diamond norm
`qdistDiamond` as the constant family `fun _ : Unit => C`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCMonad.QIndistDiamond

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Crypto.UCMonad.DiamondDominates
open CatCrypt.Crypto.UCMonad.DiamondTensorStable
open scoped ENNReal

variable {d : ℕ} {α : Type}

/-- The constant Kleisli family `fun _ : Unit => C` is a CP channel when every
branch of `C` is completely positive. -/
theorem constCP (C : QComp d α) (hc : ∀ a, IsCPMap (C.branch a)) :
    IsCPChannel (fun _ : Unit => C) := fun _ a => hc a

/-- **Diamond-norm program indistinguishability.** Two programs are
ε-indistinguishable in the diamond norm if, *after tensoring with any reference
register*, no distinguisher separates them by more than ε. This is `qIndist`
stabilized over reference registers. -/
noncomputable def qIndistDiamond (C₁ C₂ : QComp d α)
    (hc₁ : ∀ a, IsCPMap (C₁.branch a)) (hc₂ : ∀ a, IsCPMap (C₂.branch a))
    (ε : ℝ≥0∞) : Prop :=
  qdistDiamond (fun _ : Unit => C₁) (fun _ : Unit => C₂)
    (constCP C₁ hc₁) (constCP C₂ hc₂) ≤ ε

/-- Reflexivity. -/
theorem qIndistDiamond_refl (C : QComp d α) (hc : ∀ a, IsCPMap (C.branch a)) :
    qIndistDiamond C C hc hc 0 := by
  unfold qIndistDiamond
  rw [qdistDiamond_self]

/-- Symmetry. -/
theorem qIndistDiamond_symm {C₁ C₂ : QComp d α} {ε : ℝ≥0∞}
    {hc₁ : ∀ a, IsCPMap (C₁.branch a)} {hc₂ : ∀ a, IsCPMap (C₂.branch a)}
    (h : qIndistDiamond C₁ C₂ hc₁ hc₂ ε) : qIndistDiamond C₂ C₁ hc₂ hc₁ ε := by
  unfold qIndistDiamond at h ⊢
  rwa [qdistDiamond_sym]

/-- Triangle inequality. -/
theorem qIndistDiamond_triangle {C₁ C₂ C₃ : QComp d α} {ε₁ ε₂ : ℝ≥0∞}
    {hc₁ : ∀ a, IsCPMap (C₁.branch a)} {hc₂ : ∀ a, IsCPMap (C₂.branch a)}
    {hc₃ : ∀ a, IsCPMap (C₃.branch a)}
    (h₁ : qIndistDiamond C₁ C₂ hc₁ hc₂ ε₁)
    (h₂ : qIndistDiamond C₂ C₃ hc₂ hc₃ ε₂) :
    qIndistDiamond C₁ C₃ hc₁ hc₃ (ε₁ + ε₂) :=
  le_trans (qdistDiamond_triangle _ _ _ (constCP C₁ hc₁) (constCP C₂ hc₂)
    (constCP C₃ hc₃)) (add_le_add h₁ h₂)

/-- **Frame rule.** Tensoring both programs with an independent reference
register `e` does not increase the diamond distance; it follows from cb-norm
tensor-stability. The CP witnesses of the
extended programs are taken as hypotheses (the channel equalities are
independent of which witness is supplied). -/
theorem qIndistDiamond_localOp₁ {e : ℕ} (C₁ C₂ : QComp d α)
    (hc₁ : ∀ a, IsCPMap (C₁.branch a)) (hc₂ : ∀ a, IsCPMap (C₂.branch a))
    (hce₁ : ∀ a, IsCPMap ((localOp₁ (d₂ := e) C₁ hc₁).branch a))
    (hce₂ : ∀ a, IsCPMap ((localOp₁ (d₂ := e) C₂ hc₂).branch a))
    {ε : ℝ≥0∞} (h : qIndistDiamond C₁ C₂ hc₁ hc₂ ε) :
    qIndistDiamond (localOp₁ (d₂ := e) C₁ hc₁) (localOp₁ (d₂ := e) C₂ hc₂)
      hce₁ hce₂ ε :=
  le_trans
    (qdistDiamond_localOp₁_le (fun _ : Unit => C₁) (fun _ : Unit => C₂)
      (constCP C₁ hc₁) (constCP C₂ hc₂)
      (fun _ a => hce₁ a) (fun _ a => hce₂ a)) h

/-- **Consequence (ε-weakening).** A tighter bound implies a looser one. -/
theorem qIndistDiamond_conseq {C₁ C₂ : QComp d α} {ε ε' : ℝ≥0∞}
    {hc₁ : ∀ a, IsCPMap (C₁.branch a)} {hc₂ : ∀ a, IsCPMap (C₂.branch a)}
    (h : qIndistDiamond C₁ C₂ hc₁ hc₂ ε) (hε : ε ≤ ε') :
    qIndistDiamond C₁ C₂ hc₁ hc₂ ε' := le_trans h hε

/-- **Sequential composition.** Running a common CP continuation `k` after two
ε-close programs keeps them ε-close in the diamond distance, by
`qdistDiamond_comp_right`. -/
theorem qIndistDiamond_seq {β : Type} (C₁ C₂ : QComp d α) (k : α → QComp d β)
    (hc₁ : ∀ a, IsCPMap (C₁.branch a)) (hc₂ : ∀ a, IsCPMap (C₂.branch a))
    (hk : ∀ a b, IsCPMap ((k a).branch b))
    {ε : ℝ≥0∞} (h : qIndistDiamond C₁ C₂ hc₁ hc₂ ε) :
    qIndistDiamond (QComp.qbind C₁ k) (QComp.qbind C₂ k)
      (fun b => qbind_branch_isCPMap C₁ k hc₁ hk b)
      (fun b => qbind_branch_isCPMap C₂ k hc₂ hk b) ε :=
  le_trans
    (qdistDiamond_comp_right (fun _ : Unit => C₁) (fun _ : Unit => C₂) k
      (constCP C₁ hc₁) (constCP C₂ hc₂) hk
      (fun _ b => qbind_branch_isCPMap C₁ k hc₁ hk b)
      (fun _ b => qbind_branch_isCPMap C₂ k hc₂ hk b)) h

/-!
## The approximate qRHL proof system

The rules proved above for `qIndistDiamond`, an approximate relational logic for
quantum programs in the diamond (cb) norm:

| Rule | Lemma |
|------|-------|
| `C ~₀ C` (reflexivity) | `qIndistDiamond_refl` |
| symmetry | `qIndistDiamond_symm` |
| transitivity / hybrid (`ε₁ + ε₂`) | `qIndistDiamond_triangle` |
| consequence (ε-weakening) | `qIndistDiamond_conseq` |
| sequential composition (post-processing) | `qIndistDiamond_seq` |
| frame (tensor an independent register) | `qIndistDiamond_localOp₁` |

Every rule is proved at the diamond norm, so a bound derived in this system is
robust under an adversary's entangled ancilla and composes — the property the
induced-distance `qIndist` cannot provide. Soundness is by construction (the
judgment *is* the diamond-distance bound); a separate predicate-coupling
presentation à la Barthe could be layered on top but is not needed for the
metric content.
-/

end CatCrypt.Crypto.UCMonad.QIndistDiamond

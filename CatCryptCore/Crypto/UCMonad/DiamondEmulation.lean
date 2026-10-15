/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.DiamondTensorStable
public import CatCryptCore.Quantum.InstrumentCP

/-!
# Composition laws of diamond-distance emulation

Composition and framing laws for `QUCEmulatesDiamond ε f g`, the bound
`qdistDiamond f g ≤ ε` on completely-positive `QComp d` Kleisli morphisms, and
its comparison with the reference-free distance `qdist` of the `UCMonad (QComp d)`
instance.

Sequential composition on either side reduces to the reference-level laws
`qdist_comp_right` / `qdist_comp_left` because `localOp₁` commutes with `qbind`
(`localOp₁_qbind`). The tensor frame `(· ⊗ D)` is the bind-composite
`localOp₁ · >>= localOp₂ D` (`QComp.tensor_def`), so it is tensor-stability
(`qdistDiamond_localOp₁_le`) followed by post-processing. The comparison
`qdist ≤ qdistDiamond` is the `r = 1` term of the reference supremum: on a
one-dimensional reference, `localOp₁` is the relabelling `Fin d ≃ Fin (d * 1)`.

## Main results

* `QUCEmulatesDiamond.comp_right` — post-composition with a common CP
  continuation preserves the bound.
* `qdistDiamond_comp_left`, `QUCEmulatesDiamond.comp_left` — pre-composition
  with a common CP prefix preserves the distance and the bound.
* `QUCEmulatesDiamond.tensor_frame` — framing both channels by a fixed CP
  instrument `D` on a fresh register preserves the bound.
* `localOp₁_one_eq_reindexQComp` — on a one-dimensional reference register,
  `localOp₁` is `reindexQComp` along `Fin d ≃ Fin (d * 1)`.
* `qdist_le_qdistDiamond` — the reference-free distance `qdist`, over all
  `QComp` distinguishers, is at most the diamond distance.
* `QUCEmulatesDiamond.toUCEmulates` — a diamond bound gives `UCEmulates` in the
  `UCMonad (QComp d)` instance, with the adversary as simulator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCMonad.DiamondEmulation

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Crypto.UCMonad.DiamondTensorStable
open UCMonad.QuantumUC
open scoped ENNReal

/-! ## Pre-composition -/

/-- **Diamond-norm pre-composition.** Pre-composing two channels with a common
CP prefix `f` does not increase the diamond distance. The reference extension
commutes with `qbind` (`localOp₁_qbind`), which reduces the bound to the
reference-level law `qdist_comp_left`. -/
theorem qdistDiamond_comp_left {d : ℕ} {α β γ : Type} (f : α → QComp d β)
    (g₁ g₂ : β → QComp d γ) (hf : IsCPChannel f)
    (hg₁ : IsCPChannel g₁) (hg₂ : IsCPChannel g₂)
    (hfg₁ : IsCPChannel (fun a => QComp.qbind (f a) g₁))
    (hfg₂ : IsCPChannel (fun a => QComp.qbind (f a) g₂)) :
    qdistDiamond (fun a => QComp.qbind (f a) g₁) (fun a => QComp.qbind (f a) g₂)
        hfg₁ hfg₂ ≤ qdistDiamond g₁ g₂ hg₁ hg₂ := by
  refine iSup_le fun r => le_trans ?_ (le_iSup _ r)
  have hcomm : ∀ (g : β → QComp d γ) (hg : IsCPChannel g)
      (hfg : IsCPChannel (fun a => QComp.qbind (f a) g)),
      withRef r (fun a => QComp.qbind (f a) g) hfg
        = fun a => QComp.qbind (withRef r f hf a) (withRef r g hg) := by
    intro g hg hfg
    funext a
    exact localOp₁_qbind (f a) g (hf a) hg (hfg a)
  rw [hcomm g₁ hg₁ hfg₁, hcomm g₂ hg₂ hfg₂]
  exact qdist_comp_left (withRef r f hf) (withRef r g₁ hg₁) (withRef r g₂ hg₂)

/-! ## The reference-free distance is dominated by the diamond distance -/

/-- On a one-dimensional reference register, `localOp₁` is the relabelling of
`X` along `Fin d ≃ Fin (d * 1)`. -/
theorem localOp₁_one_eq_reindexQComp {d : ℕ} {α : Type} (X : QComp d α)
    (hX : ∀ a, IsCPMap (X.branch a)) :
    localOp₁ (d₂ := 1) X hX = reindexQComp (finCongr (Nat.mul_one d).symm) X := by
  apply QComp.ext_fun
  intro a M
  ext I J
  rw [localOp₁_branch_entry, reindexQComp_branch, Matrix.submatrix_apply]
  have hI : ((finProdEquiv d 1).symm I).1 = (finCongr (Nat.mul_one d).symm).symm I :=
    Fin.ext (by simp [finProdEquiv, finProdFinEquiv])
  have hJ : ((finProdEquiv d 1).symm J).1 = (finCongr (Nat.mul_one d).symm).symm J :=
    Fin.ext (by simp [finProdEquiv, finProdFinEquiv])
  have hblk : extractBlock M ((finProdEquiv d 1).symm I).2 ((finProdEquiv d 1).symm J).2
      = M.submatrix (finCongr (Nat.mul_one d).symm) (finCongr (Nat.mul_one d).symm) := by
    ext k l
    simp only [extractBlock_apply, Matrix.submatrix_apply]
    congr 1 <;> exact Fin.ext (by simp [finProdEquiv, finProdFinEquiv, Fin.fin_one_eq_zero])
  rw [hI, hJ, hblk]

/-- **`qdist` is dominated by the diamond distance.** Every distinguisher `D`
(completely positive or not) and input state `ρ` of `qdist` is reproduced by
the `r = 1` term of `qdistDiamond`, through the relabelling `Fin d ≃ Fin (d * 1)`
of the distinguisher and the state. -/
theorem qdist_le_qdistDiamond {d : ℕ} {α β : Type} (f g : α → QComp d β)
    (hf : IsCPChannel f) (hg : IsCPChannel g) :
    qdist f g ≤ qdistDiamond f g hf hg := by
  refine iSup_le fun D => iSup_le fun a => iSup_le fun ρ => ?_
  refine le_trans ?_ (le_iSup _ 1)
  have key : ∀ (h : α → QComp d β) (hh : IsCPChannel h),
      prTrue_Q (QComp.qbind (withRef 1 h hh a)
          (fun b => reindexQComp (finCongr (Nat.mul_one d).symm) (D b)))
          (reindexDensity (finCongr (Nat.mul_one d).symm) ρ)
        = prTrue_Q (QComp.qbind (h a) D) ρ := by
    intro h hh
    rw [withRef, localOp₁_one_eq_reindexQComp, ← qbind_reindexQComp,
      prTrue_Q_reindexQComp]
    exact prTrue_Q_val_congr _ (reindexDensity_symm_val _ ρ)
  exact le_iSup_of_le (fun b => reindexQComp (finCongr (Nat.mul_one d).symm) (D b))
    (le_iSup_of_le a (le_iSup_of_le (reindexDensity (finCongr (Nat.mul_one d).symm) ρ)
      (le_of_eq (by rw [key f hf, key g hg]))))

end CatCrypt.Crypto.UCMonad.DiamondEmulation

namespace CatCrypt.Crypto.UCMonad.DiamondNorm

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.UCMonad.DiamondTensorStable
open CatCrypt.Crypto.UCMonad.DiamondEmulation
open UCMonad.QuantumUC
open scoped ENNReal

/-- **Post-composition.** Post-composing both channels with a common CP
continuation `k` preserves the diamond-distance emulation bound. -/
theorem QUCEmulatesDiamond.comp_right {d : ℕ} {α β γ : Type} {ε : ℝ≥0∞}
    {f g : α → QComp d β} (k : β → QComp d γ)
    {hf : IsCPChannel f} {hg : IsCPChannel g} (hk : IsCPChannel k)
    (hfk : IsCPChannel (fun a => QComp.qbind (f a) k))
    (hgk : IsCPChannel (fun a => QComp.qbind (g a) k))
    (h : QUCEmulatesDiamond ε f g hf hg) :
    QUCEmulatesDiamond ε (fun a => QComp.qbind (f a) k)
      (fun a => QComp.qbind (g a) k) hfk hgk :=
  le_trans (qdistDiamond_comp_right f g k hf hg hk hfk hgk) h

/-- **Pre-composition.** Pre-composing both channels with a common CP prefix
`f` preserves the diamond-distance emulation bound. -/
theorem QUCEmulatesDiamond.comp_left {d : ℕ} {α β γ : Type} {ε : ℝ≥0∞}
    (f : α → QComp d β) {g₁ g₂ : β → QComp d γ}
    (hf : IsCPChannel f) {hg₁ : IsCPChannel g₁} {hg₂ : IsCPChannel g₂}
    (hfg₁ : IsCPChannel (fun a => QComp.qbind (f a) g₁))
    (hfg₂ : IsCPChannel (fun a => QComp.qbind (f a) g₂))
    (h : QUCEmulatesDiamond ε g₁ g₂ hg₁ hg₂) :
    QUCEmulatesDiamond ε (fun a => QComp.qbind (f a) g₁)
      (fun a => QComp.qbind (f a) g₂) hfg₁ hfg₂ :=
  le_trans (qdistDiamond_comp_left f g₁ g₂ hf hg₁ hg₂ hfg₁ hfg₂) h

/-- **Tensor frame.** Framing both channels by a fixed CP instrument `D` on a
fresh register `e` preserves the diamond-distance emulation bound. The framed
channel `(f a).tensor D` is `localOp₁ (f a) >>= localOp₂ D` by definition, so
the bound is tensor-stability (`qdistDiamond_localOp₁_le`) followed by
post-processing (`qdistDiamond_comp_right`). -/
theorem QUCEmulatesDiamond.tensor_frame {d e : ℕ} {α β γ : Type}
    {ε : ℝ≥0∞} (f g : α → QComp d β) (D : QComp e γ)
    (hf : IsCPChannel f) (hg : IsCPChannel g)
    (hD : ∀ c, IsCPMap (D.branch c))
    (hfe : IsCPChannel (fun a => localOp₁ (d₂ := e) (f a) (hf a)))
    (hge : IsCPChannel (fun a => localOp₁ (d₂ := e) (g a) (hg a)))
    (hk : IsCPChannel (fun b : β =>
      QComp.qbind (localOp₂ (d₁ := d) D hD) fun c => QComp.qpure (b, c)))
    (hfD : IsCPChannel (fun a => (f a).tensor D (hf a) hD))
    (hgD : IsCPChannel (fun a => (g a).tensor D (hg a) hD))
    (h : QUCEmulatesDiamond ε f g hf hg) :
    QUCEmulatesDiamond ε
      (fun a => (f a).tensor D (hf a) hD)
      (fun a => (g a).tensor D (hg a) hD) hfD hgD :=
  le_trans
    (qdistDiamond_comp_right
      (fun a => localOp₁ (d₂ := e) (f a) (hf a))
      (fun a => localOp₁ (d₂ := e) (g a) (hg a))
      (fun b => QComp.qbind (localOp₂ (d₁ := d) D hD)
        fun c => QComp.qpure (b, c))
      hfe hge hk hfD hgD)
    (le_trans (qdistDiamond_localOp₁_le f g hf hg hfe hge) h)

/-- **Lift to UC emulation.** A diamond-distance bound between two CP protocols
with the same interface gives `UCEmulates ε` in the `UCMonad (QComp d)`
instance, through `qdist_le_qdistDiamond` and `UCEmulates_of_sdist`; the
simulator is the adversary itself. (composition plumbing) -/
theorem QUCEmulatesDiamond.toUCEmulates {d : ℕ} {hon out leak view : Type}
    {ε : ℝ≥0∞} {π F : hon → QComp d (out ⊕ leak)}
    {hπ : IsCPChannel π} {hF : IsCPChannel F}
    (h : QUCEmulatesDiamond ε π F hπ hF) :
    UCMonad.UCEmulates (T := QComp d) (view := view) ε π F :=
  UCMonad.UCEmulates_of_sdist ε π F (le_trans (qdist_le_qdistDiamond π F hπ hF) h)

end CatCrypt.Crypto.UCMonad.DiamondNorm

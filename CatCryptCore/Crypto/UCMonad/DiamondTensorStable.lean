/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.DiamondDominates

/-!
# Tensor-stability of the diamond distance (cb-norm stabilization)

The completely-bounded / diamond distance is stable under tensoring with an
identity register:

  `qdistDiamond (localOp₁ f) (localOp₁ g) ≤ qdistDiamond f g`.

Extending both channels by an identity on a second register `e` does not increase
the diamond distance, because the reference supremum already ranges over the
extra register. This inequality is one half of the Broadbent–Karvonen monoidal
congruence (parallel composition with an independent session).

The proof reindexes the nested reference `(d·e)·r` to `d·(e·r)` (associativity of
`Fin`-products) and identifies a nested `localOp₁ ∘ localOp₁` with a single
`localOp₁` on the combined register, then matches acceptance probabilities.

Infrastructure:
* `reindexQComp` — transport a `QComp` along a dimension equivalence `Fin d ≃ Fin d'`
  (conjugation by `reindexLinearEquiv`), with the monad-morphism and
  trace/acceptance invariances.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCMonad.DiamondTensorStable

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Crypto.UCMonad.DiamondNormStates
open CatCrypt.Crypto.UCMonad.DiamondDominates
open UCMonad.QuantumUC
open scoped Matrix ENNReal ComplexOrder

variable {d d' : ℕ} {α β : Type}

/-- Trace is invariant under reindexing both axes by an equivalence. -/
theorem trace_submatrix_equiv {n n' : ℕ} (e : Fin n ≃ Fin n')
    (N : Matrix (Fin n') (Fin n') ℂ) :
    (N.submatrix e e).trace = N.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact e.sum_comp (fun j => N j j)

/-- Transport a `QComp d` to a `QComp d'` along a dimension equivalence
`e : Fin d ≃ Fin d'` (conjugation by the relabelling). -/
noncomputable def reindexQComp (e : Fin d ≃ Fin d') (X : QComp d α) : QComp d' α where
  branch a :=
    (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
      ((X.branch a).comp (Matrix.reindexLinearEquiv ℂ ℂ e e).symm.toLinearMap)
  branch_psd a M hM := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      Matrix.symm_reindexLinearEquiv, Matrix.coe_reindexLinearEquiv]
    refine (Matrix.posSemidef_submatrix_equiv e.symm).mpr ?_
    exact X.branch_psd a _ ((Matrix.posSemidef_submatrix_equiv e).mpr hM)
  branch_summable M := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact (X.branch_summable _).map (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.toAddMonoidHom
      (LinearMap.continuous_of_finiteDimensional _)
  branch_stp M hM := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      Matrix.symm_reindexLinearEquiv, Matrix.coe_reindexLinearEquiv,
      Matrix.reindex_apply, Equiv.symm_symm]
    have htr : ∀ a, ((X.branch a (M.submatrix e e)).submatrix e.symm e.symm).trace
        = (X.branch a (M.submatrix e e)).trace := fun a => trace_submatrix_equiv e.symm _
    simp_rw [htr]
    calc (∑' a, (X.branch a (M.submatrix e e)).trace).re
        ≤ (M.submatrix e e).trace.re :=
          X.branch_stp _ ((Matrix.posSemidef_submatrix_equiv e).mpr hM)
      _ = M.trace.re := by rw [trace_submatrix_equiv e M]

/-- Branch-apply formula for `reindexQComp`. -/
theorem reindexQComp_branch (e : Fin d ≃ Fin d') (X : QComp d α) (a : α)
    (M : Matrix (Fin d') (Fin d') ℂ) :
    (reindexQComp e X).branch a M
      = (X.branch a (M.submatrix e e)).submatrix e.symm e.symm := by
  simp only [reindexQComp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Matrix.symm_reindexLinearEquiv, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, Equiv.symm_symm]

/-- Transport a density matrix along a dimension equivalence. -/
noncomputable def reindexDensity (e : Fin d ≃ Fin d') (ρ : DensityMatrix d) :
    DensityMatrix d' where
  val := ρ.val.submatrix e.symm e.symm
  psd := (Matrix.posSemidef_submatrix_equiv e.symm).mpr ρ.psd
  tr_one := by rw [trace_submatrix_equiv e.symm ρ.val]; exact ρ.tr_one

-- Sealing `QComp.qbind` and `reindexQComp` stops the summability `defeq`s
-- from descending through the branch/bind projections.
attribute [local irreducible] QComp.qbind reindexQComp

set_option maxHeartbeats 3200000 in
/-- `reindexQComp` is a monad morphism: it commutes with Kleisli composition. -/
theorem qbind_reindexQComp {γ δ : Type} (e : Fin d ≃ Fin d')
    (X : QComp d γ) (g : γ → QComp d δ) :
    reindexQComp e (QComp.qbind X g)
      = QComp.qbind (reindexQComp e X) (fun c => reindexQComp e (g c)) := by
  apply QComp.ext_fun
  intro c M
  rw [reindexQComp_branch]
  -- LHS: reindex of the qbind sum.
  have hinj : Function.Injective (fun a : γ => (a, c)) :=
    fun a a' h => (Prod.mk.injEq _ _ _ _).mp h |>.1
  have hsumX : Summable (fun a => (g a).branch c (X.branch a (M.submatrix e e))) :=
    Pi.summable.mpr fun p => Pi.summable.mpr fun q =>
      (Pi.summable.mp (Pi.summable.mp
        (X.bind_uncurry_summable g (M.submatrix e e)) p) q).comp_injective hinj
  have hsumR : Summable
      (fun a => (reindexQComp e (g a)).branch c ((reindexQComp e X).branch a M)) :=
    Pi.summable.mpr fun p => Pi.summable.mpr fun q =>
      (Pi.summable.mp (Pi.summable.mp
        ((reindexQComp e X).bind_uncurry_summable
          (fun a => reindexQComp e (g a)) M) p) q).comp_injective hinj
  ext i j
  rw [qbind_branch_apply,
    show ((∑' a, (g a).branch c (X.branch a (M.submatrix e e))).submatrix e.symm e.symm) i j
      = (∑' a, (g a).branch c (X.branch a (M.submatrix e e))) (e.symm i) (e.symm j) from rfl,
    matrix_tsum_entry_gen _ hsumX (e.symm i) (e.symm j),
    qbind_branch_apply, matrix_tsum_entry_gen _ hsumR i j]
  refine tsum_congr (fun a => ?_)
  rw [reindexQComp_branch, reindexQComp_branch]
  have hid : ((X.branch a (M.submatrix e e)).submatrix (⇑e.symm) (⇑e.symm)).submatrix (⇑e) (⇑e)
      = X.branch a (M.submatrix e e) := by
    rw [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
  rw [hid, Matrix.submatrix_apply]

/-- Acceptance probability transports along `reindexQComp` (the reference
register is just relabelled). -/
theorem prTrue_Q_reindexQComp (e : Fin d ≃ Fin d') (X : QComp d Bool)
    (ρ : DensityMatrix d') :
    prTrue_Q (reindexQComp e X) ρ = prTrue_Q X (reindexDensity e.symm ρ) := by
  simp only [prTrue_Q, reindexQComp_branch, reindexDensity, Equiv.symm_symm]
  rw [trace_submatrix_equiv e.symm]

/-! ## Associativity coherence of the index equivalence -/

/-- Associativity of `finProdEquiv`: nesting the product `(d·e)·r` and relabelling
to `d·(e·r)` agrees with the direct `d·(e·r)` product. Both sides carry the index
`k·e·r + b·r + c`. -/
theorem fpe_assoc {d e r : ℕ} (k : Fin d) (b : Fin e) (c : Fin r) :
    finCongr (Nat.mul_assoc d e r)
        (finProdEquiv (d * e) r (finProdEquiv d e (k, b), c))
      = finProdEquiv d (e * r) (k, finProdEquiv e r (b, c)) := by
  apply Fin.ext
  simp only [finProdEquiv, finProdFinEquiv, finCongr_apply, Fin.val_cast,
    Equiv.coe_fn_mk, Fin.val_mk]
  ring

/-! ## Nesting identity: two reference extensions reassociate to one -/

/-- Reconstruction form of `fpe_assoc`: the `d`/`e`/`r` components extracted from
the nested `(d·e)·r` decomposition of `(finCongr).symm I` reassemble (via the
direct `d·(e·r)` product) to `I`. -/
theorem reassoc {d e r : ℕ} (I : Fin (d * (e * r))) :
    finProdEquiv d (e * r)
        (((finProdEquiv d e).symm ((finProdEquiv (d * e) r).symm
            ((finCongr (Nat.mul_assoc d e r)).symm I)).1).1,
         finProdEquiv e r
           (((finProdEquiv d e).symm ((finProdEquiv (d * e) r).symm
              ((finCongr (Nat.mul_assoc d e r)).symm I)).1).2,
            ((finProdEquiv (d * e) r).symm
              ((finCongr (Nat.mul_assoc d e r)).symm I)).2)) = I := by
  rw [← fpe_assoc]
  simp only [Prod.mk.eta, Equiv.apply_symm_apply]

/-- Applying `localOp₁` twice (registers `e` then `r`) equals a single `localOp₁`
on the combined register `e·r`, after reassociating the index. The outer CP
witness is taken as a hypothesis (the underlying channel equality is independent
of which witness is supplied). -/
theorem reindexQComp_localOp₁_localOp₁ {d e r : ℕ} (Y : QComp d α)
    (hY : ∀ a, IsCPMap (Y.branch a))
    (hco : ∀ a, IsCPMap ((localOp₁ (d₂ := e) Y hY).branch a)) :
    reindexQComp (finCongr (Nat.mul_assoc d e r))
        (localOp₁ (d₂ := r) (localOp₁ (d₂ := e) Y hY) hco)
      = localOp₁ (d₂ := e * r) Y hY := by
  apply QComp.ext_fun
  intro a M
  ext I J
  rw [reindexQComp_branch, Matrix.submatrix_apply,
    localOp₁_branch_entry, localOp₁_branch_entry, localOp₁_branch_entry]
  -- Decomposition components of `(finCongr).symm I` (and `J`).
  set i' := ((finProdEquiv (d * e) r).symm ((finCongr (Nat.mul_assoc d e r)).symm I)).1 with hi'
  set i₂ := ((finProdEquiv (d * e) r).symm ((finCongr (Nat.mul_assoc d e r)).symm I)).2 with hi₂
  set j' := ((finProdEquiv (d * e) r).symm ((finCongr (Nat.mul_assoc d e r)).symm J)).1 with hj'
  set j₂ := ((finProdEquiv (d * e) r).symm ((finCongr (Nat.mul_assoc d e r)).symm J)).2 with hj₂
  have hsymmI : (finProdEquiv d (e * r)).symm I
      = (((finProdEquiv d e).symm i').1,
         finProdEquiv e r (((finProdEquiv d e).symm i').2, i₂)) :=
    (Equiv.symm_apply_eq _).mpr (reassoc I).symm
  have hsymmJ : (finProdEquiv d (e * r)).symm J
      = (((finProdEquiv d e).symm j').1,
         finProdEquiv e r (((finProdEquiv d e).symm j').2, j₂)) :=
    (Equiv.symm_apply_eq _).mpr (reassoc J).symm
  rw [hsymmI, hsymmJ]
  -- The outer indices are now definitionally equal; reduce to the block equality.
  dsimp only
  have hblk :
      extractBlock (extractBlock (M.submatrix ⇑(finCongr (Nat.mul_assoc d e r))
            ⇑(finCongr (Nat.mul_assoc d e r))) i₂ j₂)
          ((finProdEquiv d e).symm i').2 ((finProdEquiv d e).symm j').2
        = extractBlock M (finProdEquiv e r (((finProdEquiv d e).symm i').2, i₂))
            (finProdEquiv e r (((finProdEquiv d e).symm j').2, j₂)) := by
    ext k l
    simp only [extractBlock_apply, Matrix.submatrix_apply, fpe_assoc]
  rw [hblk]

/-! ## cb-norm tensor-stability of the diamond distance -/

/-- Acceptance probability depends only on the density value. -/
theorem prTrue_Q_val_congr (W : QComp d Bool) {ρ₁ ρ₂ : DensityMatrix d}
    (h : ρ₁.val = ρ₂.val) : prTrue_Q W ρ₁ = prTrue_Q W ρ₂ := by
  simp only [prTrue_Q, h]

/-- Reindexing a density by `e` then `e.symm` returns the original value. -/
theorem reindexDensity_symm_val (e : Fin d ≃ Fin d') (ρ : DensityMatrix d) :
    (reindexDensity e.symm (reindexDensity e ρ)).val = ρ.val := by
  simp only [reindexDensity, Equiv.symm_symm, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id]

/-- **cb-norm tensor-stability.** Extending both channels by an identity register
`e` does not increase the diamond distance: `qdistDiamond (f ⊗ id) (g ⊗ id) ≤
qdistDiamond f g`. The outer CP witnesses are taken as hypotheses. This is one
half of the Broadbent–Karvonen monoidal congruence. -/
theorem qdistDiamond_localOp₁_le {d e : ℕ} {α β : Type} (f g : α → QComp d β)
    (hf : IsCPChannel f) (hg : IsCPChannel g)
    (hfe : IsCPChannel (fun a => localOp₁ (d₂ := e) (f a) (hf a)))
    (hge : IsCPChannel (fun a => localOp₁ (d₂ := e) (g a) (hg a))) :
    qdistDiamond (fun a => localOp₁ (d₂ := e) (f a) (hf a))
        (fun a => localOp₁ (d₂ := e) (g a) (hg a)) hfe hge
      ≤ qdistDiamond f g hf hg := by
  refine iSup_le fun r => ?_
  refine le_trans ?_ (le_iSup _ (e * r))
  refine iSup_le fun D => iSup_le fun x => iSup_le fun ρ => ?_
  refine le_iSup_of_le
    (fun b => reindexQComp (finCongr (Nat.mul_assoc d e r)) (D b))
    (le_iSup_of_le x (le_iSup_of_le
      (reindexDensity (finCongr (Nat.mul_assoc d e r)) ρ) ?_))
  have key : ∀ (h : α → QComp d β) (hh : IsCPChannel h)
      (hhe : IsCPChannel (fun a => localOp₁ (d₂ := e) (h a) (hh a))),
      prTrue_Q (QComp.qbind (withRef (e * r) h hh x)
          (fun b => reindexQComp (finCongr (Nat.mul_assoc d e r)) (D b)))
          (reindexDensity (finCongr (Nat.mul_assoc d e r)) ρ)
        = prTrue_Q (QComp.qbind
            (withRef r (fun a => localOp₁ (d₂ := e) (h a) (hh a)) hhe x) D) ρ := by
    intro h hh hhe
    rw [withRef, withRef, ← reindexQComp_localOp₁_localOp₁ (h x) (hh x) (hhe x),
      ← qbind_reindexQComp, prTrue_Q_reindexQComp]
    exact prTrue_Q_val_congr _ (reindexDensity_symm_val _ ρ)
  refine le_of_eq ?_
  rw [key f hf hfe, key g hg hge]

/-! ## Sequential composition (diamond-norm post-processing) -/

/-- **Diamond-norm post-processing (sequential composition).** Post-composing
both channels with a common CP continuation `k` cannot increase the diamond
distance. This is the diamond-norm PPL; the proof uses that `localOp₁` commutes
with `qbind` (`localOp₁_qbind`) and reduces to the reference-level PPL
`qdist_comp_right`. -/
theorem qdistDiamond_comp_right {d : ℕ} {α β γ : Type} (f g : α → QComp d β)
    (k : β → QComp d γ) (hf : IsCPChannel f) (hg : IsCPChannel g)
    (hk : IsCPChannel k)
    (hfk : IsCPChannel (fun a => QComp.qbind (f a) k))
    (hgk : IsCPChannel (fun a => QComp.qbind (g a) k)) :
    qdistDiamond (fun a => QComp.qbind (f a) k) (fun a => QComp.qbind (g a) k)
        hfk hgk ≤ qdistDiamond f g hf hg := by
  refine iSup_le fun r => le_trans ?_ (le_iSup _ r)
  have hcomm : ∀ (h : α → QComp d β) (hh : IsCPChannel h)
      (hhk : IsCPChannel (fun a => QComp.qbind (h a) k)),
      withRef r (fun a => QComp.qbind (h a) k) hhk
        = fun a => QComp.qbind (withRef r h hh a)
            (fun b => localOp₁ (d₂ := r) (k b) (hk b)) := by
    intro h hh hhk
    funext a
    exact localOp₁_qbind (h a) k (hh a) hk (hhk a)
  rw [hcomm f hf hfk, hcomm g hg hgk]
  exact qdist_comp_right (withRef r f hf) (withRef r g hg)
    (fun b => localOp₁ (d₂ := r) (k b) (hk b))

/-- **Monoidal congruence (parallel composition with an independent register).**
If `f` and `g` are diamond-ε-close, so are their identity-extensions `f ⊗ id` and
`g ⊗ id`. This is the Broadbent–Karvonen `≈`-respects-`⊗` property for the
diamond distance. -/
theorem QUCEmulatesDiamond_localOp₁ {d e : ℕ} {α β : Type} {ε : ℝ≥0∞}
    {f g : α → QComp d β} {hf : IsCPChannel f} {hg : IsCPChannel g}
    (hfe : IsCPChannel (fun a => localOp₁ (d₂ := e) (f a) (hf a)))
    (hge : IsCPChannel (fun a => localOp₁ (d₂ := e) (g a) (hg a)))
    (h : QUCEmulatesDiamond ε f g hf hg) :
    QUCEmulatesDiamond ε (fun a => localOp₁ (d₂ := e) (f a) (hf a))
      (fun a => localOp₁ (d₂ := e) (g a) (hg a)) hfe hge :=
  le_trans (qdistDiamond_localOp₁_le f g hf hg hfe hge) h

end CatCrypt.Crypto.UCMonad.DiamondTensorStable

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.DiamondNorm
public import CatCryptCore.Crypto.UCMonad.DiamondNormStates
public import CatCryptCore.Crypto.UCMonad.LocalOpFunctorial

/-!
# The diamond distance dominates the CP-induced distance

`qdist` (in `CatCryptCore.Crypto.UCMonad.QuantumUC`) quantifies over *all* `QComp d Bool` distinguishers,
including positive-but-not-completely-positive maps (e.g. the transpose) that
cannot be embedded into a reference register. That makes `qdist` larger than the
physical distinguishing advantage and means `qdist ≤ qdistDiamond` does **not**
hold for it.

This file introduces `qdistCP` — the **CP-restricted** induced distance, ranging
only over completely-positive (physical) distinguishers — and proves the
domination

  `qdistCP f g ≤ qdistDiamond f g`.

A CP distinguisher `D` lifts to the reference-extended system as `localOp₁ ∘ D`
(still a valid `QComp (d·1) Bool`), and on the product input `ρ ⊗ unit` the lifted
acceptance probability is unchanged — by `localOp₁_qbind` (functoriality of the
reference extension over sequencing) and `trace_localOp₁_branch_kronecker`. No
dimension reindexing is needed: the `r = 1` reference register already exhibits
the bare CP advantage inside `qdistDiamond`.

Supporting result of independent interest:

* `qbind_branch_isCPMap` — Kleisli composition (`qbind`) of CP channels is a CP
  channel. (`tensorIdMap` commutes with composition and with the defining `tsum`;
  the PSD cone is closed under summable sums via `tsum_posSemidef`.)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCMonad.DiamondDominates

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Crypto.UCMonad.DiamondNormStates
open UCMonad.QuantumUC
open scoped Matrix ENNReal ComplexOrder

variable {d : ℕ} {α β : Type}

/-! ## CP closure of Kleisli composition -/

/-- Entrywise commutation of a (matrix-valued) `tsum` over an arbitrary index
shape (generalises `matrix_tsum_entry` from square `Fin n` matrices). -/
theorem matrix_tsum_entry_gen {ι κ γ : Type} (N : γ → Matrix ι κ ℂ)
    (hN : Summable N) (i : ι) (j : κ) :
    (∑' a, N a) i j = ∑' a, N a i j :=
  (Pi.hasSum.mp (Pi.hasSum.mp hN.hasSum i) j).tsum_eq.symm

/-- Tsum of PSD matrices is PSD for a product index `Fin k × Fin d` (reindex to
`Fin (k*d)` and reuse `tsum_posSemidef`). -/
theorem tsum_posSemidef_prod {k : ℕ} {γ : Type}
    {f : γ → Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ}
    (hpsd : ∀ a, (f a).PosSemidef) (hf : Summable f) :
    (∑' a, f a).PosSemidef := by
  set e : Fin (k * d) ≃ Fin k × Fin d := finProdFinEquiv.symm with he
  have hsub : Summable (fun a => (f a).submatrix e e) :=
    Pi.summable.mpr fun i => Pi.summable.mpr fun j =>
      Pi.summable.mp (Pi.summable.mp hf (e i)) (e j)
  have hcomm : (∑' a, f a).submatrix e e = ∑' a, (f a).submatrix e e := by
    ext i j
    rw [Matrix.submatrix_apply, matrix_tsum_entry_gen _ hf (e i) (e j),
      matrix_tsum_entry_gen _ hsub i j]
    simp only [Matrix.submatrix_apply]
  have hps : (∑' a, (f a).submatrix e e).PosSemidef :=
    tsum_posSemidef (fun a => (Matrix.posSemidef_submatrix_equiv e).mpr (hpsd a)) hsub
  rw [← hcomm] at hps
  exact (Matrix.posSemidef_submatrix_equiv e).mp hps

-- Sealing `QComp.qbind` stops the summability `defeq`s from descending
-- through the branch/bind projections.
attribute [local irreducible] QComp.qbind

set_option maxHeartbeats 1000000 in
/-- **Kleisli composition of CP channels is a CP channel.** Each branch of
`qbind I g` is completely positive whenever every branch of `I` and of `g` is. -/
theorem qbind_branch_isCPMap {β γ : Type} (I : QComp d β) (g : β → QComp d γ)
    (hI : ∀ b, IsCPMap (I.branch b)) (hg : ∀ b c, IsCPMap ((g b).branch c))
    (c : γ) : IsCPMap ((QComp.qbind I g).branch c) := by
  intro k M hM
  -- Per-entry summability of the lifted composite family.
  have hsum : Summable
      (fun b => tensorIdMap (((g b).branch c).comp (I.branch b)) k M) := by
    refine Pi.summable.mpr fun p => Pi.summable.mpr fun q => ?_
    have hinj : Function.Injective (fun b : β => (b, c)) :=
      fun b b' h => (Prod.mk.injEq _ _ _ _).mp h |>.1
    have := (I.bind_uncurry_summable g (blockMatrix M p.1 q.1))
    have h2 := (Pi.summable.mp (Pi.summable.mp this p.2) q.2).comp_injective hinj
    simpa [tensorIdMap, blockMatrix, LinearMap.comp_apply] using! h2
  -- Summability of the un-lifted composite family (the qbind branch sum).
  have hsum0 : ∀ p q : Fin k × Fin d, Summable
      (fun b => (g b).branch c (I.branch b (blockMatrix M p.1 q.1))) := by
    intro p q
    have hinj : Function.Injective (fun b : β => (b, c)) :=
      fun b b' h => (Prod.mk.injEq _ _ _ _).mp h |>.1
    refine Pi.summable.mpr fun i => Pi.summable.mpr fun j => ?_
    exact (Pi.summable.mp (Pi.summable.mp
      (I.bind_uncurry_summable g (blockMatrix M p.1 q.1)) i) j).comp_injective hinj
  -- Rewrite `id_k ⊗ (qbind I g).branch c` as the sum of lifted composites.
  have heq : tensorIdMap ((QComp.qbind I g).branch c) k M
      = ∑' b, tensorIdMap (((g b).branch c).comp (I.branch b)) k M := by
    ext p q
    rw [matrix_tsum_entry_gen _ hsum p q]
    show ((QComp.qbind I g).branch c (blockMatrix M p.1 q.1)) p.2 q.2
        = ∑' b, (tensorIdMap (((g b).branch c).comp (I.branch b)) k M) p q
    rw [qbind_branch_apply, matrix_tsum_entry_gen _ (hsum0 p q) p.2 q.2]
    refine tsum_congr (fun b => ?_)
    rfl
  rw [heq]
  refine tsum_posSemidef_prod (fun b => ?_) hsum
  rw [tensorIdMap_comp]
  exact hg b c k _ (hI b k M hM)

/-! ## The unit state on dimension one -/

/-- The unique density matrix on a one-dimensional system (the `1×1` identity). -/
noncomputable def unitDensity1 : DensityMatrix 1 where
  val := 1
  psd := Matrix.PosSemidef.one
  tr_one := by simp

/-! ## Acceptance probability is preserved by the reference extension -/

/-- On a product input `ρ ⊗ unit`, the acceptance probability of `localOp₁ X`
equals that of `X` on `ρ` (the reference register is in a normalised state). -/
theorem prTrue_Q_localOp₁_kronecker {d₂ : ℕ} (X : QComp d Bool)
    (hcp : ∀ a, IsCPMap (X.branch a)) (ρ : DensityMatrix d) (σ : DensityMatrix d₂) :
    prTrue_Q (localOp₁ (d₂ := d₂) X hcp) (kroneckerDensity ρ σ) = prTrue_Q X ρ := by
  simp only [prTrue_Q, kroneckerDensity_val,
    trace_localOp₁_branch_kronecker X hcp true ρ.val σ.val, σ.tr_one, mul_one]

/-! ## CP-restricted induced distance and the domination theorem -/

/-- **CP-restricted induced distance.** Like `qdist` but the distinguisher `D`
ranges only over completely-positive channels (`IsCPChannel`), i.e. physical
measurements. This is the induced-distinguishability distance; it is
dominated by the diamond distance. -/
noncomputable def qdistCP (f g : α → QComp d β) : ℝ≥0∞ :=
  ⨆ (D : β → QComp d Bool) (_ : IsCPChannel D) (a : α) (ρ : DensityMatrix d),
    absDiff (prTrue_Q (QComp.qbind (f a) D) ρ)
            (prTrue_Q (QComp.qbind (g a) D) ρ)

/-- **The diamond distance dominates the CP-induced distance.** Every CP
distinguisher is reproduced inside `qdistDiamond` by its reference-extension
`localOp₁ ∘ D` on the `r = 1` register with input `ρ ⊗ unit`. -/
theorem qdistCP_le_qdistDiamond (f g : α → QComp d β)
    (hf : IsCPChannel f) (hg : IsCPChannel g) :
    qdistCP f g ≤ qdistDiamond f g hf hg := by
  refine iSup_le fun D => iSup_le fun hD => iSup_le fun a => iSup_le fun ρ => ?_
  -- Bound by the `r = 1` term of the diamond supremum.
  refine le_trans ?_ (le_iSup _ 1)
  -- The lifted distinguisher and product input.
  set D' : β → QComp (d * 1) Bool := fun b => localOp₁ (d₂ := 1) (D b) (hD b) with hD'
  -- Each acceptance probability is preserved by the lift.
  have key : ∀ (h : α → QComp d β) (hh : IsCPChannel h),
      prTrue_Q (QComp.qbind (withRef 1 h hh a) D') (kroneckerDensity ρ unitDensity1)
        = prTrue_Q (QComp.qbind (h a) D) ρ := by
    intro h hh
    have hcpAf : ∀ c, IsCPMap ((QComp.qbind (h a) D).branch c) :=
      fun c => qbind_branch_isCPMap (h a) D (hh a) hD c
    have hlift : QComp.qbind (withRef 1 h hh a) D'
        = localOp₁ (d₂ := 1) (QComp.qbind (h a) D) hcpAf := by
      rw [withRef, hD', localOp₁_qbind (h a) D (hh a) hD hcpAf]
    rw [hlift, prTrue_Q_localOp₁_kronecker (QComp.qbind (h a) D) hcpAf ρ unitDensity1]
  exact le_iSup_of_le D' (le_iSup_of_le a
    (le_iSup_of_le (kroneckerDensity ρ unitDensity1)
      (le_of_eq (by rw [key f hf, key g hg]))))

end CatCrypt.Crypto.UCMonad.DiamondDominates

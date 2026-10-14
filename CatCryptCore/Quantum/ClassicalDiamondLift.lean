/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.ClassicalLift
public import CatCryptCore.Crypto.UCMonad.DiamondTensorStable

/-!
# Classical-to-quantum distance lifting in the diamond norm

`CatCryptCore.Quantum.ClassicalLift` equates the classical statistical distance
with the distance without a reference register:
`sdistD f g = qdist (classicalEmbed∘f) (classicalEmbed∘g)`.

This file bounds the diamond distance of the embedded computations by the same
statistical distance. `classicalEmbed μ` has `branch a = μ(a)·id`, so tensoring
it with an identity reference gives `μ(a)·id` on the larger space again:

  `localOp₁ (classicalEmbed μ) = classicalEmbed μ`   (re-embedded at dimension `d·r`).

Hence every reference-register term of `qdistDiamond` already equals `sdistD`
(via `classicalEmbed_sdist_eq` at that dimension), so

  `qdistDiamond (classicalEmbed∘f) (classicalEmbed∘g) ≤ sdistD f g`,

that is, a statistical-distance bound on the classical computations bounds the
diamond distance of their embeddings, against distinguishers that hold a
reference register and post-process the classical outputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.ClassicalDiamondLift

open CatCrypt.Prob CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.UCMonad.DiamondNorm UCMonad.QuantumUC UCMonad.SDistrUC
open scoped ENNReal Matrix ComplexOrder

variable {d : ℕ} {α β : Type}

/-- Each branch of `classicalEmbed μ` is completely positive (it is `μ(a)·id`, a
nonnegative scalar multiple of the identity). -/
theorem classicalEmbed_isCPMap (μ : SDistr α) (a : α) :
    IsCPMap ((classicalEmbed (d := d) μ).branch a) := by
  intro k M hM
  have hbr : ((classicalEmbed (d := d) μ).branch a)
      = (((μ (some a)).toReal : ℂ)) • LinearMap.id := rfl
  rw [hbr]
  have : tensorIdMap (((μ (some a)).toReal : ℂ) • LinearMap.id) k M
      = ((μ (some a)).toReal : ℂ) • M := by
    ext p q
    simp [tensorIdMap, blockMatrix]
    rfl
  rw [this]
  exact hM.smul (Complex.zero_le_real.mpr ENNReal.toReal_nonneg)

/-- `classicalEmbed μ` as a CP channel (the `IsCPChannel` of the constant family). -/
theorem classicalEmbed_isCPChannel (f : α → SDistr β) :
    IsCPChannel (fun a => classicalEmbed (d := d) (f a)) :=
  fun a b => classicalEmbed_isCPMap (f a) b

/-- **The key lemma.** Tensoring `classicalEmbed μ` with an identity reference of
dimension `r` re-embeds it at dimension `d·r`: `localOp₁ (classicalEmbed μ) =
classicalEmbed μ`. (Because `μ(a)·id ⊗ id_r = μ(a)·id_{d·r}`.) -/
theorem localOp₁_classicalEmbed {r : ℕ} (μ : SDistr α)
    (hcp : ∀ a, IsCPMap ((classicalEmbed (d := d) μ).branch a)) :
    localOp₁ (d₂ := r) (classicalEmbed (d := d) μ) hcp
      = classicalEmbed (d := d * r) μ := by
  apply QComp.ext_fun
  intro a M
  ext i j
  rw [localOp₁_branch_entry]
  show (((μ (some a)).toReal : ℂ) • (extractBlock M _ _)) _ _
      = (((μ (some a)).toReal : ℂ) • M) i j
  rw [Matrix.smul_apply, Matrix.smul_apply, extractBlock_apply]
  congr 2 <;>
    rw [Prod.mk.eta, Equiv.apply_symm_apply]

/-- `withRef r (classicalEmbed∘f) = classicalEmbed∘f` re-embedded at `d·r`. -/
theorem withRef_classicalEmbed {r : ℕ} (f : α → SDistr β) :
    withRef r (fun a => classicalEmbed (d := d) (f a))
        (classicalEmbed_isCPChannel f)
      = fun a => classicalEmbed (d := d * r) (f a) :=
  funext fun a =>
    localOp₁_classicalEmbed (f a) fun b => classicalEmbed_isCPMap (f a) b

/-- There are no density matrices in dimension `0` (the unit-trace condition fails:
`tr 0 = 0 ≠ 1`). -/
instance : IsEmpty (DensityMatrix 0) :=
  ⟨fun ρ => by
    have := ρ.tr_one
    simp [Matrix.trace] at this⟩

/-- `qdist` in dimension `0` is `0` (no density-matrix inputs). -/
theorem qdist_dim_zero (f g : α → QComp 0 β) : qdist f g = 0 := by
  simp only [qdist]
  apply le_antisymm _ zero_le
  refine iSup_le fun D => iSup_le fun a => iSup_le fun ρ => ?_
  exact isEmptyElim ρ

/-- **Classical lifting in the diamond norm.** The diamond distance between the
quantum embeddings of two classical computations is at most their classical
statistical distance: `qdistDiamond (classicalEmbed∘f) (classicalEmbed∘g) ≤
sdistD f g`. -/
theorem qdistDiamond_classicalEmbed_le [NeZero d] (f g : α → SDistr β) :
    qdistDiamond (fun a => classicalEmbed (d := d) (f a))
        (fun a => classicalEmbed (d := d) (g a))
        (classicalEmbed_isCPChannel f) (classicalEmbed_isCPChannel g)
      ≤ sdistD f g := by
  refine iSup_le fun r => ?_
  rw [withRef_classicalEmbed f, withRef_classicalEmbed g]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [Nat.mul_zero]
    exact le_trans (le_of_eq (qdist_dim_zero _ _)) zero_le
  · have : NeZero (d * r) := ⟨Nat.mul_ne_zero (NeZero.ne d) hr.ne'⟩
    exact le_of_eq (classicalEmbed_sdist_eq f g).symm

/-- **Classical-to-quantum diamond-distance lifting.** If `sdistD f g ≤ ε` then
the diamond distance of the quantum embeddings is `≤ ε`; the diamond-norm
counterpart of `classical_to_quantum_uc_lift`. -/
theorem classical_to_quantum_diamond_lift [NeZero d] {ε : ℝ≥0∞}
    (f g : α → SDistr β) (h_cl : sdistD f g ≤ ε) :
    qdistDiamond (fun a => classicalEmbed (d := d) (f a))
        (fun a => classicalEmbed (d := d) (g a))
        (classicalEmbed_isCPChannel f) (classicalEmbed_isCPChannel g)
      ≤ ε :=
  le_trans (qdistDiamond_classicalEmbed_le f g) h_cl

end CatCrypt.Quantum.ClassicalDiamondLift

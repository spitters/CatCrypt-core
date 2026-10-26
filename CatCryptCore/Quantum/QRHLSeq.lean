/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRHL
public import CatCryptCore.ForMathlib.LinearMapMatrix

@[expose] public section

set_option autoImplicit false

/-!
# The two-sided sequence rule of qRHL

The judgement `qrHoare Φ C₁ C₂ Ψ` of `CatCrypt.Quantum.QRHL` constrains the joint
post-state summed over all outcome pairs. This file proves that this summed post-state
is the composite of a first-register total action and a second-register total action,
that the two actions commute, and that the summed post-state of `C₁; D₁ ~ C₂; D₂` is the
summed post-state of `D₁ ~ D₂` applied to that of `C₁ ~ C₂`. The two-sided sequence rule
follows.

The continuations `D₁`, `D₂` do not depend on the outcomes of `C₁`, `C₂`: the judgement
retains only the outcome-summed state, so an intermediate predicate `Θ` holds of the sum
and of no single outcome pair.

## Main definitions

* `totalMap C` — the total action `Y ↦ ∑' a, C.branch a Y` of an instrument, as a linear map
* `lift₁ f`, `lift₂ g` — a linear map acting on the first or the second register
* `jointPost C₁ C₂ ρ` — the joint post-state summed over outcome pairs
* `BipartitePred.jointPre C₁ C₂ Ψ` — the weakest precondition of `Ψ` under `C₁ ~ C₂`

## Main results

* `isCPMap_lift₁` — a completely positive map lifted to the first register is completely positive
* `lift₂_lift₁_comm` — maps on different registers commute, on every bipartite matrix
* `tsum_jointBranch_eq_lift` — the summed post-state is
  `lift₂ (totalMap C₂) (lift₁ (totalMap C₁) ρ)`
* `jointPost_qbind` — the joint post-state of a sequential composite is the composite of the
  joint post-states
* `qrhl_wp`, `qrhl_seq_wp` — the weakest-precondition rule and the sequence rule in
  weakest-precondition form
* `qrhl_seq` — the two-sided sequence rule
-/

open scoped Matrix ComplexOrder
open Matrix Classical

noncomputable section

namespace CatCrypt.Quantum.QRHL

variable {d₁ d₂ : ℕ} {α β γ δ : Type}

open CatCrypt.Quantum.TensorProduct

/-! ## Linear maps on matrices -/

/-- The total action `Y ↦ ∑' a, C.branch a Y` of an instrument, as a linear map. -/
def totalMap {d : ℕ} (C : QComp d α) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun Y := ∑' a, C.branch a Y
  map_add' X Y := by
    simp only [map_add]
    exact (C.branch_summable X).tsum_add (C.branch_summable Y)
  map_smul' c Y := by
    simp only [map_smul, RingHom.id_apply]
    exact (C.branch_summable Y).tsum_const_smul c

theorem totalMap_apply {d : ℕ} (C : QComp d α) (Y : Matrix (Fin d) (Fin d) ℂ) :
    totalMap C Y = ∑' a, C.branch a Y := rfl

/-- The total action of `C; D` is the total action of `D` after that of `C`. -/
theorem totalMap_qbind {d : ℕ} (C : QComp d α) (D : QComp d γ) :
    totalMap (QComp.qbind C fun _ => D) = (totalMap D).comp (totalMap C) := by
  refine LinearMap.ext fun Y => ?_
  simp only [LinearMap.comp_apply, totalMap_apply]
  refine tsum_congr fun c => ?_
  exact ((LinearMap.toContinuousLinearMap (D.branch c)).map_tsum
    (C.branch_summable _)).symm

/-! ## Maps on one register -/

/-- The linear map `f ⊗ id`: `f` applied to every block `extractBlock X i₂ j₂`. -/
def lift₁ (f : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₁) (Fin d₁) ℂ) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ →ₗ[ℂ]
      Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ where
  toFun X := Matrix.of fun i j =>
    f (extractBlock X ((finProdEquiv d₁ d₂).symm i).2 ((finProdEquiv d₁ d₂).symm j).2)
      ((finProdEquiv d₁ d₂).symm i).1 ((finProdEquiv d₁ d₂).symm j).1
  map_add' X Y := by ext i j; simp [extractBlock_add, map_add]
  map_smul' c X := by ext i j; simp [extractBlock_smul, map_smul]

/-- The linear map `id ⊗ g`: `g` applied to every block `extractBlock₁ X i₁ j₁`. -/
def lift₂ (g : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ →ₗ[ℂ]
      Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ where
  toFun X := Matrix.of fun i j =>
    g (extractBlock₁ X ((finProdEquiv d₁ d₂).symm i).1 ((finProdEquiv d₁ d₂).symm j).1)
      ((finProdEquiv d₁ d₂).symm i).2 ((finProdEquiv d₁ d₂).symm j).2
  map_add' X Y := by
    have h : ∀ k l, extractBlock₁ (X + Y) k l = extractBlock₁ X k l + extractBlock₁ Y k l := by
      intro k l; ext; simp [extractBlock₁_apply]
    ext i j; simp [h, map_add]
  map_smul' c X := by
    have h : ∀ k l, extractBlock₁ (c • X) k l = c • extractBlock₁ X k l := by
      intro k l; ext; simp [extractBlock₁_apply]
    ext i j; simp [h, map_smul]

theorem lift₁_apply (f : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₁) (Fin d₁) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i j : Fin (d₁ * d₂)) :
    lift₁ f X i j =
      f (extractBlock X ((finProdEquiv d₁ d₂).symm i).2 ((finProdEquiv d₁ d₂).symm j).2)
        ((finProdEquiv d₁ d₂).symm i).1 ((finProdEquiv d₁ d₂).symm j).1 := rfl

theorem lift₂_apply (g : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i j : Fin (d₁ * d₂)) :
    lift₂ g X i j =
      g (extractBlock₁ X ((finProdEquiv d₁ d₂).symm i).1 ((finProdEquiv d₁ d₂).symm j).1)
        ((finProdEquiv d₁ d₂).symm i).2 ((finProdEquiv d₁ d₂).symm j).2 := rfl

theorem extractBlock_lift₁
    (f : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₁) (Fin d₁) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i₂ j₂ : Fin d₂) :
    extractBlock (lift₁ f X) i₂ j₂ = f (extractBlock X i₂ j₂) := by
  ext i₁ j₁
  simp [extractBlock_apply, lift₁_apply]

theorem extractBlock₁_lift₂
    (g : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i₁ j₁ : Fin d₁) :
    extractBlock₁ (lift₂ g X) i₁ j₁ = g (extractBlock₁ X i₁ j₁) := by
  ext i₂ j₂
  simp [extractBlock₁_apply, lift₂_apply]

theorem lift₁_comp (f f' : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₁) (Fin d₁) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    lift₁ (f.comp f') X = lift₁ f (lift₁ f' X) := by
  ext i j
  simp [lift₁_apply, extractBlock_lift₁]

theorem lift₂_comp (g g' : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    lift₂ (g.comp g') X = lift₂ g (lift₂ g' X) := by
  ext i j
  simp [lift₂_apply, extractBlock₁_lift₂]

/-- A completely positive map lifted to the first register is completely
positive: `id_c ⊗ (Γ ⊗ id_k)` is `id_{c·k} ⊗ Γ` reindexed. -/
theorem _root_.CatCrypt.Quantum.isCPMap_lift₁ {m k : ℕ}
    {Γ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hΓ : IsCPMap Γ) : IsCPMap (lift₁ (d₂ := k) Γ) := by
  intro c M hM
  let h : Fin (c * k) × Fin m ≃ Fin c × Fin (m * k) :=
    ((finProdEquiv c k).symm.prodCongr (Equiv.refl _)).trans
      ((Equiv.prodAssoc _ _ _).trans
        ((Equiv.refl (Fin c)).prodCongr
          ((Equiv.prodComm (Fin k) (Fin m)).trans (finProdEquiv m k))))
  have key : tensorIdMap (lift₁ (d₂ := k) Γ) c M =
      (tensorIdMap Γ (c * k) (M.submatrix h h)).submatrix h.symm h.symm := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [h, tensorIdMap_apply, lift₁_apply]
    refine congrArg (fun X => Γ X _ _) ?_
    ext x y
    simp [blockMatrix, extractBlock_apply]
  rw [key]
  exact (hΓ (c * k) _ (hM.submatrix _)).submatrix _

/-- **Maps on different registers commute**: `(id ⊗ g) ∘ (f ⊗ id) = (f ⊗ id) ∘ (id ⊗ g)`
    on every bipartite matrix, entangled or not. -/
theorem lift₂_lift₁_comm
    (f : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₁) (Fin d₁) ℂ)
    (g : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    lift₂ g (lift₁ f X) = lift₁ f (lift₂ g X) := by
  ext i j
  obtain ⟨cf, hf⟩ : ∃ cf : Fin d₁ → Fin d₁ → ℂ, ∀ Y, f Y ((finProdEquiv d₁ d₂).symm i).1
      ((finProdEquiv d₁ d₂).symm j).1 = ∑ k, ∑ l, Y k l * cf k l :=
    ⟨_, fun Y => linearMap_apply_eq_sum_single f Y _ _⟩
  obtain ⟨cg, hg⟩ : ∃ cg : Fin d₂ → Fin d₂ → ℂ, ∀ Y, g Y ((finProdEquiv d₁ d₂).symm i).2
      ((finProdEquiv d₁ d₂).symm j).2 = ∑ k, ∑ l, Y k l * cg k l :=
    ⟨_, fun Y => linearMap_apply_eq_sum_single g Y _ _⟩
  rw [lift₂_apply, lift₁_apply, hg, hf]
  simp only [extractBlock₁_apply, extractBlock_apply, lift₁_apply, lift₂_apply,
    Equiv.symm_apply_apply, hf, hg]
  simp only [Finset.sum_mul, mul_assoc, mul_comm (cf _ _) (cg _ _),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin d₁)))
      (t := (Finset.univ : Finset (Fin d₂)))]

/-! ## The summed post-state -/

/-- The branch `C.branch a` lifted to the first register is `localOp₁`'s branch. -/
theorem lift₁_branch_eq_localOp₁ (C : QComp d₁ α) (hcp : ∀ a, IsCPMap (C.branch a)) (a : α)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    lift₁ (C.branch a) X = (localOp₁ (d₂ := d₂) C hcp).branch a X := rfl

/-- The branch `C.branch b` lifted to the second register is `localOp₂`'s branch. -/
theorem lift₂_branch_eq_localOp₂ (C : QComp d₂ β) (hcp : ∀ b, IsCPMap (C.branch b)) (b : β)
    (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    lift₂ (C.branch b) X = (localOp₂ (d₁ := d₁) C hcp).branch b X := rfl

/-- Each joint branch is the second-register branch after the first-register branch. -/
theorem jointBranch_eq_lift (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) (a : α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointBranch C₁ C₂ a b ρ = lift₂ (C₂.branch b) (lift₁ (C₁.branch a) ρ) := by
  ext i j
  simp [jointBranch, lift₂_apply, extractBlock₁, lift₁_apply]

theorem summable_lift₁ (C : QComp d₁ α) (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Summable fun a => lift₁ (C.branch a) X := by
  refine Pi.summable.mpr fun i => Pi.summable.mpr fun j => ?_
  simp only [lift₁_apply]
  exact Pi.summable.mp (Pi.summable.mp (C.branch_summable _) _) _

theorem summable_lift₂ (C : QComp d₂ β) (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Summable fun b => lift₂ (C.branch b) X := by
  refine Pi.summable.mpr fun i => Pi.summable.mpr fun j => ?_
  simp only [lift₂_apply]
  exact Pi.summable.mp (Pi.summable.mp (C.branch_summable _) _) _

theorem tsum_lift₁ (C : QComp d₁ α) (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑' a, lift₁ (C.branch a) X = lift₁ (totalMap C) X := by
  ext i j
  erw [Pi.tsum_apply (summable_lift₁ C X), Pi.tsum_apply (Pi.summable.mp (summable_lift₁ C X) _)]
  rw [lift₁_apply, totalMap_apply]
  erw [Pi.tsum_apply (C.branch_summable _),
    Pi.tsum_apply (Pi.summable.mp (C.branch_summable _) _)]
  rfl

theorem tsum_lift₂ (C : QComp d₂ β) (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑' b, lift₂ (C.branch b) X = lift₂ (totalMap C) X := by
  ext i j
  erw [Pi.tsum_apply (summable_lift₂ C X), Pi.tsum_apply (Pi.summable.mp (summable_lift₂ C X) _)]
  rw [lift₂_apply, totalMap_apply]
  erw [Pi.tsum_apply (C.branch_summable _),
    Pi.tsum_apply (Pi.summable.mp (C.branch_summable _) _)]
  rfl

/-- The family of joint branches is summable over outcome pairs. -/
theorem summable_jointBranch (C₁ : QComp d₁ α) (C₂ : QComp d₂ β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Summable fun p : α × β => jointBranch C₁ C₂ p.1 p.2 ρ := by
  refine Pi.summable.mpr fun i => Pi.summable.mpr fun j => ?_
  have key : Summable fun p : α × β => ∑ k, ∑ l,
      C₁.branch p.1 (extractBlock ρ k l) ((finProdEquiv d₁ d₂).symm i).1
        ((finProdEquiv d₁ d₂).symm j).1 *
      C₂.branch p.2 (Matrix.single k l 1) ((finProdEquiv d₁ d₂).symm i).2
        ((finProdEquiv d₁ d₂).symm j).2 := by
    refine summable_sum fun k _ => summable_sum fun l _ => ?_
    exact summable_mul_of_summable_norm
      (f := fun a => C₁.branch a (extractBlock ρ k l) ((finProdEquiv d₁ d₂).symm i).1
        ((finProdEquiv d₁ d₂).symm j).1)
      (g := fun b => C₂.branch b (Matrix.single k l 1) ((finProdEquiv d₁ d₂).symm i).2
        ((finProdEquiv d₁ d₂).symm j).2)
      (summable_norm_iff.mpr (Pi.summable.mp (Pi.summable.mp (C₁.branch_summable _) _) _))
      (summable_norm_iff.mpr (Pi.summable.mp (Pi.summable.mp (C₂.branch_summable _) _) _))
  refine key.congr fun p => ?_
  rw [jointBranch_eq_lift, lift₂_apply, linearMap_apply_eq_sum_single (C₂.branch p.2)]
  simp only [extractBlock₁_apply, lift₁_apply, Equiv.symm_apply_apply]

/-- **The summed post-state factors through the registers**: it is the total action of `C₂`
    on the second register after the total action of `C₁` on the first. -/
theorem tsum_jointBranch_eq_lift (C₁ : QComp d₁ α) (C₂ : QComp d₂ β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑' p : α × β, jointBranch C₁ C₂ p.1 p.2 ρ = lift₂ (totalMap C₂) (lift₁ (totalMap C₁) ρ) := by
  have hs := summable_jointBranch C₁ C₂ ρ
  rw [hs.tsum_prod' fun a => by
    simpa only [jointBranch_eq_lift] using summable_lift₂ C₂ (lift₁ (C₁.branch a) ρ)]
  simp only [jointBranch_eq_lift, tsum_lift₂]
  rw [← tsum_lift₁]
  exact ((lift₂ (d₁ := d₁) (totalMap C₂)).toContinuousLinearMap.map_tsum
    (summable_lift₁ C₁ ρ)).symm

/-- The joint post-state of `C₁ ~ C₂`: the joint branches summed over outcome pairs. -/
def jointPost (C₁ : QComp d₁ α) (C₂ : QComp d₂ β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ :=
  ∑' p : α × β, jointBranch C₁ C₂ p.1 p.2 ρ

/-- **Sequential composition of joint post-states**: the joint post-state of
    `C₁; D₁ ~ C₂; D₂` is the joint post-state of `D₁ ~ D₂` applied to that of `C₁ ~ C₂`. -/
theorem jointPost_qbind (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ) (C₂ : QComp d₂ β)
    (D₂ : QComp d₂ δ) (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointPost (QComp.qbind C₁ fun _ => D₁) (QComp.qbind C₂ fun _ => D₂) ρ =
      jointPost D₁ D₂ (jointPost C₁ C₂ ρ) := by
  simp only [jointPost, tsum_jointBranch_eq_lift]
  rw [totalMap_qbind, totalMap_qbind, lift₁_comp, lift₂_comp,
    lift₂_lift₁_comm (totalMap D₁) (totalMap C₂)]

/-- If every branch of `C₁` and of `C₂` is completely positive, the joint post-state of a
    PSD state is PSD. -/
theorem jointPost_psd (C₁ : QComp d₁ α) (C₂ : QComp d₂ β)
    (hcp₁ : ∀ a, IsCPMap (C₁.branch a)) (hcp₂ : ∀ b, IsCPMap (C₂.branch b))
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (hρ : ρ.PosSemidef) :
    (jointPost C₁ C₂ ρ).PosSemidef := by
  rw [jointPost, tsum_jointBranch_eq_lift, ← tsum_lift₂, ← tsum_lift₁]
  have h₁ : (∑' a, lift₁ (d₂ := d₂) (C₁.branch a) ρ).PosSemidef :=
    tsum_posSemidef (fun a => (localOp₁ C₁ hcp₁).branch_psd a ρ hρ) (summable_lift₁ C₁ ρ)
  exact tsum_posSemidef (fun b => (localOp₂ C₂ hcp₂).branch_psd b _ h₁) (summable_lift₂ C₂ _)

/-! ## Rules -/

/-- The weakest precondition of `Ψ` under `C₁ ~ C₂`: the predicate that holds of `ρ` exactly
    when `Ψ` holds of `jointPost C₁ C₂ ρ`. -/
def BipartitePred.jointPre (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) (Ψ : BipartitePred d₁ d₂) :
    BipartitePred d₁ d₂ :=
  fun ρ => Ψ (jointPost C₁ C₂ ρ)

/-- **Weakest-precondition rule**: `{jointPre C₁ C₂ Ψ} C₁ ~ C₂ {Ψ}`. -/
theorem qrhl_wp (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) (Ψ : BipartitePred d₁ d₂) :
    qrHoare (BipartitePred.jointPre C₁ C₂ Ψ) C₁ C₂ Ψ :=
  fun _ _ hΦ => hΦ

/-- **Sequence rule, weakest-precondition form**:
    `{jointPre C₁ C₂ (jointPre D₁ D₂ Ψ)} C₁; D₁ ~ C₂; D₂ {Ψ}`. -/
theorem qrhl_seq_wp (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ) (C₂ : QComp d₂ β)
    (D₂ : QComp d₂ δ) (Ψ : BipartitePred d₁ d₂) :
    qrHoare (BipartitePred.jointPre C₁ C₂ (BipartitePred.jointPre D₁ D₂ Ψ))
      (QComp.qbind C₁ fun _ => D₁) (QComp.qbind C₂ fun _ => D₂) Ψ := by
  intro ρ _ hΦ
  show Ψ (jointPost _ _ ρ)
  rw [jointPost_qbind]
  exact hΦ

/-- **Two-sided sequence rule**: if `{Φ} C₁ ~ C₂ {Θ}` and `{Θ} D₁ ~ D₂ {Ψ}`, and every branch
    of `C₁` and of `C₂` is completely positive, then `{Φ} C₁; D₁ ~ C₂; D₂ {Ψ}`, where
    `C; D` is `qbind C (fun _ => D)`. -/
theorem qrhl_seq {Φ Θ Ψ : BipartitePred d₁ d₂} (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ)
    (C₂ : QComp d₂ β) (D₂ : QComp d₂ δ)
    (hcp₁ : ∀ a, IsCPMap (C₁.branch a)) (hcp₂ : ∀ b, IsCPMap (C₂.branch b))
    (h₁ : qrHoare Φ C₁ C₂ Θ) (h₂ : qrHoare Θ D₁ D₂ Ψ) :
    qrHoare Φ (QComp.qbind C₁ fun _ => D₁) (QComp.qbind C₂ fun _ => D₂) Ψ := by
  intro ρ hρ hΦ
  show Ψ (jointPost _ _ ρ)
  rw [jointPost_qbind]
  exact h₂ _ (jointPost_psd C₁ C₂ hcp₁ hcp₂ ρ hρ) (h₁ ρ hρ hΦ)

end CatCrypt.Quantum.QRHL

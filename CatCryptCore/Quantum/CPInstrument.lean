/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.InstrumentCP
public import CatCryptCore.Crypto.UCMonad.DiamondDominates
public import CatCryptCore.Quantum.CPMapMatrixMap
public import QuantumFoundations.SubInstrument

@[expose] public section

set_option autoImplicit false

/-!
# Completely positive instruments

`QComp d α` carries `branch_psd`: each branch preserves positive
semidefiniteness. Complete positivity — preservation of positive
semidefiniteness by `id_k ⊗ Φ` for every `k` — is the separate predicate
`IsCPMap`, and it is the side condition of `localOp₁`, `localOp₂` and
`QComp.tensor`.

`CPComp d α` is QuantumFoundations' `Quantum.SubInstrument (Fin d) (Fin d) α`:
a family of completely positive branches whose traces over every finite set of
outcomes sum to at most the trace of the input. `CPComp.toQComp` forgets it to
a `QComp d α`, and `CPComp.mk'` builds one from a `QComp d α` whose branches
satisfy `IsCPMap`; the two notions of complete positivity agree by
`isCPMap_iff_isCP`. Equality of `CPComp`s is equality of the underlying
instruments (`CPComp.toQComp_injective`, `CPComp.ext`).

## Main definitions

* `CPComp`: an instrument whose every branch is completely positive
* `CPComp.toQComp`, `CPComp.mk'`: the passage to and from `QComp`
* `CPComp.qpure`, `CPComp.qbind`, `CPComp.qfail`: the monad operations, those
  of `Quantum.SubInstrument`
* `CPComp.tensor`: parallel composition, with no side-condition argument

## Main results

* `CPComp.ext`: equality of `CPComp`s is equality of the underlying
  instruments
* `CPComp.qpure_qbind`, `CPComp.qbind_qpure`, `CPComp.qbind_assoc`: the monad
  laws, those of `Quantum.SubInstrument`
* `CPComp.toQComp_qpure`, `CPComp.toQComp_qfail`, `CPComp.toQComp_qbind`:
  `toQComp` commutes with the monad operations
* `localOp₁_branch_isCPMap`, `localOp₂_branch_isCPMap`: lifting a completely
  positive instrument to one register of a bipartite system preserves
  complete positivity
* `QComp.tensor_branch_isCPMap`: the tensor of two instruments with
  completely positive branches has completely positive branches
-/

open scoped Matrix ComplexOrder ENNReal
open Matrix

noncomputable section

namespace CatCrypt.Quantum

open CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.UCMonad.DiamondDominates (qbind_branch_isCPMap)

/-! ## The completely positive instruments -/

/-- A sub-normalised quantum instrument all of whose branches are completely
positive: QuantumFoundations' subinstrument from `Fin d` to `Fin d`. -/
abbrev CPComp (d : ℕ) (α : Type) := _root_.Quantum.SubInstrument (Fin d) (Fin d) α

namespace CPComp

variable {d e : ℕ} {α β γ : Type}

/-- The underlying instrument of a completely positive instrument. -/
def toQComp (C : CPComp d α) : QComp d α where
  branch := C.branch
  branch_psd a _ hρ := (C.isCP_branch a).posSemidef hρ
  branch_summable := C.summable_branch_apply
  branch_stp ρ hρ := by
    rw [C.isCPTNIFamily.re_tsum_trace_apply]
    exact C.tsum_trace_re_le hρ

@[simp]
theorem toQComp_branch (C : CPComp d α) : C.toQComp.branch = C.branch := rfl

/-- Every branch of a completely positive instrument is completely positive in the sense of
`IsCPMap`. -/
theorem branch_cp (C : CPComp d α) (a : α) : IsCPMap (C.toQComp.branch a) :=
  isCPMap_of_isCP (C.isCP_branch a)

/-- The completely positive instrument with the branches of an instrument whose branches are
completely positive. -/
def mk' (I : QComp d α) (h : ∀ a, IsCPMap (I.branch a)) : CPComp d α where
  branch := I.branch
  isCP_branch a := (h a).isCP
  trace_le s ρ hρ := by
    have hs := trace_re_summable (I.branch_summable ρ)
    calc ∑ a ∈ s, (I.branch a ρ).trace.re
        ≤ ∑' a, (I.branch a ρ).trace.re :=
          hs.sum_le_tsum s fun a _ => trace_re_nonneg_of_psd (I.branch_psd a ρ hρ)
      _ = (∑' a, (I.branch a ρ).trace).re :=
          (Complex.re_tsum (trace_summable (I.branch_summable ρ))).symm
      _ ≤ ρ.trace.re := I.branch_stp ρ hρ

@[simp]
theorem branch_mk' (I : QComp d α) (h : ∀ a, IsCPMap (I.branch a)) :
    (mk' I h).branch = I.branch := rfl

@[simp]
theorem toQComp_mk' (I : QComp d α) (h : ∀ a, IsCPMap (I.branch a)) :
    (mk' I h).toQComp = I :=
  QComp.ext fun _ => rfl

@[simp]
theorem mk'_toQComp (C : CPComp d α) : mk' C.toQComp C.branch_cp = C :=
  _root_.Quantum.DSubInstrument.ext rfl

theorem toQComp_injective :
    Function.Injective (CPComp.toQComp (d := d) (α := α)) := fun _ _ h =>
  _root_.Quantum.DSubInstrument.ext (congrArg QComp.branch h)

theorem ext {C D : CPComp d α} (h : C.toQComp = D.toQComp) : C = D :=
  toQComp_injective h

/-! ## Monad operations -/

/-- The trivial instrument returning `a`. -/
def qpure (a : α) : CPComp d α := _root_.Quantum.SubInstrument.pure a

/-- The everywhere-zero instrument. -/
def qfail : CPComp d α := _root_.Quantum.SubInstrument.fail

/-- Kleisli composition of completely positive instruments. -/
def qbind (C : CPComp d α) (f : α → CPComp d β) : CPComp d β :=
  _root_.Quantum.SubInstrument.bind C f

@[simp]
theorem toQComp_qpure (a : α) :
    (qpure (d := d) a).toQComp = QComp.qpure a := by
  refine QComp.ext fun a' => ?_
  by_cases h : a' = a
  · subst h
    simp [qpure, QComp.qpure]
  · simp [qpure, QComp.qpure, h]

@[simp]
theorem toQComp_qfail :
    (qfail (d := d) (α := α)).toQComp = QComp.qfail :=
  QComp.ext fun _ => rfl

@[simp]
theorem toQComp_qbind (C : CPComp d α) (f : α → CPComp d β) :
    (C.qbind f).toQComp = QComp.qbind C.toQComp fun a => (f a).toQComp :=
  QComp.ext_fun fun b ρ => _root_.Quantum.DSubInstrument.branch_bind_apply C f b ρ

/-! ## Monad laws -/

theorem qpure_qbind (a : α) (f : α → CPComp d β) :
    (qpure a).qbind f = f a :=
  _root_.Quantum.SubInstrument.pure_bind a f

theorem qbind_qpure (C : CPComp d α) : C.qbind qpure = C :=
  _root_.Quantum.SubInstrument.bind_pure C

theorem qbind_assoc (C : CPComp d α) (f : α → CPComp d β)
    (g : β → CPComp d γ) :
    (C.qbind f).qbind g = C.qbind fun a => (f a).qbind g :=
  _root_.Quantum.SubInstrument.bind_assoc C f g

end CPComp

/-! ## Complete positivity of the local liftings -/

section LocalOp

variable {d₁ d₂ : ℕ} {α β : Type}

/-- Reindexing that moves the second register of a bipartite system into the
ancilla: `(c, (i₁, i₂)) ↦ ((c, i₂), i₁)`. -/
def ancillaSwap₁ (k d₁ d₂ : ℕ) :
    Fin k × Fin (d₁ * d₂) ≃ Fin (k * d₂) × Fin d₁ where
  toFun p :=
    (finProdEquiv k d₂ (p.1, ((finProdEquiv d₁ d₂).symm p.2).2),
      ((finProdEquiv d₁ d₂).symm p.2).1)
  invFun q :=
    (((finProdEquiv k d₂).symm q.1).1,
      finProdEquiv d₁ d₂ (q.2, ((finProdEquiv k d₂).symm q.1).2))
  left_inv p := by obtain ⟨c, i⟩ := p; simp
  right_inv q := by obtain ⟨u, i₁⟩ := q; simp

/-- Reindexing that moves the first register of a bipartite system into the
ancilla: `(c, (i₁, i₂)) ↦ ((c, i₁), i₂)`. -/
def ancillaSwap₂ (k d₁ d₂ : ℕ) :
    Fin k × Fin (d₁ * d₂) ≃ Fin (k * d₁) × Fin d₂ where
  toFun p :=
    (finProdEquiv k d₁ (p.1, ((finProdEquiv d₁ d₂).symm p.2).1),
      ((finProdEquiv d₁ d₂).symm p.2).2)
  invFun q :=
    (((finProdEquiv k d₁).symm q.1).1,
      finProdEquiv d₁ d₂ (((finProdEquiv k d₁).symm q.1).2, q.2))
  left_inv p := by obtain ⟨c, i⟩ := p; simp
  right_inv q := by obtain ⟨u, i₂⟩ := q; simp

@[simp]
theorem ancillaSwap₁_apply (k : ℕ) (p : Fin k × Fin (d₁ * d₂)) :
    ancillaSwap₁ k d₁ d₂ p =
      (finProdEquiv k d₂ (p.1, ((finProdEquiv d₁ d₂).symm p.2).2),
        ((finProdEquiv d₁ d₂).symm p.2).1) := rfl

@[simp]
theorem ancillaSwap₁_symm_apply (k : ℕ) (q : Fin (k * d₂) × Fin d₁) :
    (ancillaSwap₁ k d₁ d₂).symm q =
      (((finProdEquiv k d₂).symm q.1).1,
        finProdEquiv d₁ d₂ (q.2, ((finProdEquiv k d₂).symm q.1).2)) := rfl

@[simp]
theorem ancillaSwap₂_apply (k : ℕ) (p : Fin k × Fin (d₁ * d₂)) :
    ancillaSwap₂ k d₁ d₂ p =
      (finProdEquiv k d₁ (p.1, ((finProdEquiv d₁ d₂).symm p.2).1),
        ((finProdEquiv d₁ d₂).symm p.2).2) := rfl

@[simp]
theorem ancillaSwap₂_symm_apply (k : ℕ) (q : Fin (k * d₁) × Fin d₂) :
    (ancillaSwap₂ k d₁ d₂).symm q =
      (((finProdEquiv k d₁).symm q.1).1,
        finProdEquiv d₁ d₂ (((finProdEquiv k d₁).symm q.1).2, q.2)) := rfl

/-- The lifting of a completely positive instrument to the first register of a
bipartite system is completely positive: `id_k ⊗ (E_a ⊗ id_{d₂})` is
`id_{k·d₂} ⊗ E_a` reindexed along `ancillaSwap₁`. -/
theorem localOp₁_branch_isCPMap (op : QComp d₁ α)
    (hcp : ∀ a, IsCPMap (op.branch a)) (a : α) :
    IsCPMap ((localOp₁ (d₂ := d₂) op hcp).branch a) := by
  intro k M hM
  have hN : (M.submatrix (ancillaSwap₁ k d₁ d₂).symm
      (ancillaSwap₁ k d₁ d₂).symm).PosSemidef := hM.submatrix _
  have key : tensorIdMap ((localOp₁ (d₂ := d₂) op hcp).branch a) k M =
      (tensorIdMap (op.branch a) (k * d₂)
        (M.submatrix (ancillaSwap₁ k d₁ d₂).symm
          (ancillaSwap₁ k d₁ d₂).symm)).submatrix
        (ancillaSwap₁ k d₁ d₂) (ancillaSwap₁ k d₁ d₂) := by
    funext p q
    obtain ⟨c, i⟩ := p
    obtain ⟨c', j⟩ := q
    have hblk : blockMatrix (M.submatrix (ancillaSwap₁ k d₁ d₂).symm
        (ancillaSwap₁ k d₁ d₂).symm)
        (ancillaSwap₁ k d₁ d₂ (c, i)).1 (ancillaSwap₁ k d₁ d₂ (c', j)).1 =
        extractBlock (blockMatrix M c c')
          ((finProdEquiv d₁ d₂).symm i).2 ((finProdEquiv d₁ d₂).symm j).2 := by
      funext x y
      simp [blockMatrix, extractBlock]
    show (op.branch a (extractBlock (blockMatrix M c c')
        ((finProdEquiv d₁ d₂).symm i).2 ((finProdEquiv d₁ d₂).symm j).2))
        ((finProdEquiv d₁ d₂).symm i).1 ((finProdEquiv d₁ d₂).symm j).1 =
      (op.branch a (blockMatrix (M.submatrix (ancillaSwap₁ k d₁ d₂).symm
        (ancillaSwap₁ k d₁ d₂).symm)
        (ancillaSwap₁ k d₁ d₂ (c, i)).1 (ancillaSwap₁ k d₁ d₂ (c', j)).1))
        (ancillaSwap₁ k d₁ d₂ (c, i)).2 (ancillaSwap₁ k d₁ d₂ (c', j)).2
    rw [hblk]
    simp only [ancillaSwap₁_apply]
  rw [key]
  exact (hcp a (k * d₂) _ hN).submatrix _

/-- The lifting of a completely positive instrument to the second register of
a bipartite system is completely positive: `id_k ⊗ (id_{d₁} ⊗ E_b)` is
`id_{k·d₁} ⊗ E_b` reindexed along `ancillaSwap₂`. -/
theorem localOp₂_branch_isCPMap (op : QComp d₂ β)
    (hcp : ∀ b, IsCPMap (op.branch b)) (b : β) :
    IsCPMap ((localOp₂ (d₁ := d₁) op hcp).branch b) := by
  intro k M hM
  have hN : (M.submatrix (ancillaSwap₂ k d₁ d₂).symm
      (ancillaSwap₂ k d₁ d₂).symm).PosSemidef := hM.submatrix _
  have key : tensorIdMap ((localOp₂ (d₁ := d₁) op hcp).branch b) k M =
      (tensorIdMap (op.branch b) (k * d₁)
        (M.submatrix (ancillaSwap₂ k d₁ d₂).symm
          (ancillaSwap₂ k d₁ d₂).symm)).submatrix
        (ancillaSwap₂ k d₁ d₂) (ancillaSwap₂ k d₁ d₂) := by
    funext p q
    obtain ⟨c, i⟩ := p
    obtain ⟨c', j⟩ := q
    have hblk : blockMatrix (M.submatrix (ancillaSwap₂ k d₁ d₂).symm
        (ancillaSwap₂ k d₁ d₂).symm)
        (ancillaSwap₂ k d₁ d₂ (c, i)).1 (ancillaSwap₂ k d₁ d₂ (c', j)).1 =
        Matrix.of fun x y => (blockMatrix M c c')
          (finProdEquiv d₁ d₂ (((finProdEquiv d₁ d₂).symm i).1, x))
          (finProdEquiv d₁ d₂ (((finProdEquiv d₁ d₂).symm j).1, y)) := by
      funext x y
      simp [blockMatrix]
    show (op.branch b (Matrix.of fun x y => (blockMatrix M c c')
        (finProdEquiv d₁ d₂ (((finProdEquiv d₁ d₂).symm i).1, x))
        (finProdEquiv d₁ d₂ (((finProdEquiv d₁ d₂).symm j).1, y))))
        ((finProdEquiv d₁ d₂).symm i).2 ((finProdEquiv d₁ d₂).symm j).2 =
      (op.branch b (blockMatrix (M.submatrix (ancillaSwap₂ k d₁ d₂).symm
        (ancillaSwap₂ k d₁ d₂).symm)
        (ancillaSwap₂ k d₁ d₂ (c, i)).1 (ancillaSwap₂ k d₁ d₂ (c', j)).1))
        (ancillaSwap₂ k d₁ d₂ (c, i)).2 (ancillaSwap₂ k d₁ d₂ (c', j)).2
    rw [hblk]
    simp only [ancillaSwap₂_apply]
  rw [key]
  exact (hcp b (k * d₁) _ hN).submatrix _

end LocalOp

/-! ## The tensor of completely positive instruments -/

section Tensor

variable {d e : ℕ} {α β : Type}

/-- Every branch of a tensor of instruments with completely positive branches
is completely positive. -/
theorem QComp.tensor_branch_isCPMap (C : QComp d α) (D : QComp e β)
    (hC : ∀ a, IsCPMap (C.branch a)) (hD : ∀ b, IsCPMap (D.branch b))
    (ab : α × β) : IsCPMap ((C.tensor D hC hD).branch ab) := by
  rw [QComp.tensor_def]
  exact qbind_branch_isCPMap _ _ (localOp₁_branch_isCPMap C hC)
    (fun a => qbind_branch_isCPMap _ _ (localOp₂_branch_isCPMap D hD)
      fun b => qpure_branch_isCPMap (a, b)) ab

/-- Parallel composition of completely positive instruments on the two
registers of a `d * e`-dimensional system. The complete-positivity side
conditions of `QComp.tensor` are supplied by the `branch_cp` fields. -/
def CPComp.tensor (C : CPComp d α) (D : CPComp e β) : CPComp (d * e) (α × β) :=
  CPComp.mk' (QComp.tensor C.toQComp D.toQComp C.branch_cp D.branch_cp)
    (QComp.tensor_branch_isCPMap _ _ _ _)

@[simp]
theorem CPComp.toQComp_tensor (C : CPComp d α) (D : CPComp e β) :
    (C.tensor D).toQComp =
      QComp.tensor C.toQComp D.toQComp C.branch_cp D.branch_cp :=
  CPComp.toQComp_mk' _ _

end Tensor

end CatCrypt.Quantum

end

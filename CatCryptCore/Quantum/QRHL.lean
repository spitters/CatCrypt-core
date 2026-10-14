/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.Instrument
public import CatCryptCore.Quantum.TensorProduct
public import CatCryptCore.Quantum.PartialTrace
public import CatCryptCore.Quantum.UnitaryChannel
public import CatCryptCore.Quantum.CPMap

@[expose] public section

set_option autoImplicit false

/-!
# Quantum Relational Hoare Logic (qRHL)

Defines a quantum relational Hoare logic for relating two QComp programs,
following Unruh (2019) and Barthe et al. (2019).

## Mathematical Background

A qRHL judgment `{Φ} C₁ ~ C₂ {Ψ}` operates on a **bipartite** quantum system
H₁ ⊗ H₂ where C₁ acts on register 1 and C₂ acts on register 2. The pre/post-
conditions Φ, Ψ are predicates on bipartite density matrices.

Semantically: `{Φ} C₁ ~ C₂ {Ψ}` means for all joint states ρ on H₁ ⊗ H₂
satisfying Φ(ρ), applying C₁ on register 1 and C₂ on register 2 yields a
state satisfying Ψ.

## Main Definitions

* `BipartitePred` — predicate on bipartite density matrices
* `qrHoare` — the qRHL judgment
* Rules: `qrhl_skip`, `qrhl_conseq`, `qrhl_unitary_wp`, `qrhl_unitary`,
  `qrhl_one_sided_left_wp`, `qrhl_one_sided_left`, `qrhl_seq_one_sided_left`

## References

* Unruh, D. — *Quantum Relational Hoare Logic*, POPL 2019
* Barthe, G. et al. — *Relational Proofs for Quantum Programs*, POPL 2019
* Li, Y. & Ying, M. — *Algorithmic Analysis of Termination Problems for Quantum
  Programs*, POPL 2018
-/

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical

noncomputable section

namespace CatCrypt.Quantum.QRHL

variable {d₁ d₂ : ℕ} {α β : Type}

open CatCrypt.Quantum.PartialTrace
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.UnitaryChannel

/-! ## Bipartite Predicates -/

/-- A predicate on bipartite density matrices. -/
def BipartitePred (d₁ d₂ : ℕ) :=
  Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ → Prop

/-- True predicate: always holds. -/
def BipartitePred.top : BipartitePred d₁ d₂ := fun _ => True

/-- Product predicate: holds iff both marginals satisfy their respective predicates. -/
def BipartitePred.product
    (P₁ : Matrix (Fin d₁) (Fin d₁) ℂ → Prop)
    (P₂ : Matrix (Fin d₂) (Fin d₂) ℂ → Prop) :
    BipartitePred d₁ d₂ :=
  fun ρ => P₁ (partialTrace₂ ρ) ∧ P₂ (partialTrace₁ ρ)

/-- Equality predicate: the joint state equals a specific matrix. -/
def BipartitePred.eq (σ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    BipartitePred d₁ d₂ :=
  fun ρ => ρ = σ

/-- Separability predicate: state is a product state ρ₁ ⊗ ρ₂. -/
def BipartitePred.separable : BipartitePred d₁ d₂ :=
  fun ρ => ∃ (ρ₁ : Matrix (Fin d₁) (Fin d₁) ℂ) (ρ₂ : Matrix (Fin d₂) (Fin d₂) ℂ),
    ρ₁.PosSemidef ∧ ρ₂.PosSemidef ∧ ρ = TensorProduct.kronecker ρ₁ ρ₂

/-! ## Joint Evolution -/

/-- Apply C₁ on register 1 and C₂ on register 2, summing over outcome pairs.
    The joint evolution maps ρ to `∑'_{a,b} (C₁.branch(a) ⊗ C₂.branch(b))(ρ)`
    with outcomes `(a, b)`.

    Defined as `localOp₁(C₁) >>= λ a, localOp₂(C₂) >>= λ b, pure (a, b)`;
    local operations on different registers commute, so the order of the two
    local operations does not affect the result. -/
def jointEvolve (C₁ : QComp d₁ α) (C₂ : QComp d₂ β)
    (hC₁ : ∀ a, IsCPMap (C₁.branch a))
    (hC₂ : ∀ b, IsCPMap (C₂.branch b)) :
    QComp (d₁ * d₂) (α × β) :=
  QComp.qbind (localOp₁ C₁ hC₁) fun a =>
    QComp.qbind (localOp₂ C₂ hC₂) fun b =>
      QComp.qpure (a, b)

/-! ## Joint Branch Function -/

/-- The joint branch function for branch pair `(a, b)`: applies `C₁.branch a` on
    register 1 and `C₂.branch b` on register 2.

    `jointBranch C₁ C₂ a b ρ` at entry `((i₁,i₂),(j₁,j₂))` applies `C₁.branch a`
    to the `(i₂,j₂)`-block (viewing ρ as a grid of d₁×d₁ blocks), then applies
    `C₂.branch b` to the second-register blocks of the result. -/
def jointBranch (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) (a : α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ :=
  Matrix.of fun i j =>
    let ⟨i₁, i₂⟩ := (finProdEquiv d₁ d₂).symm i
    let ⟨j₁, j₂⟩ := (finProdEquiv d₁ d₂).symm j
    (C₂.branch b (Matrix.of fun i₂' j₂' =>
      (C₁.branch a (extractBlock ρ i₂' j₂')) i₁ j₁)) i₂ j₂

/-- Helper: the inner matrix fed to C₂ in `jointBranch`. -/
private def innerMatrix (C₁ : QComp d₁ α) (a : α)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₁ j₁ : Fin d₁) : Matrix (Fin d₂) (Fin d₂) ℂ :=
  Matrix.of fun i₂' j₂' => (C₁.branch a (extractBlock ρ i₂' j₂')) i₁ j₁

private theorem innerMatrix_add (C₁ : QComp d₁ α) (a : α)
    (ρ₁ ρ₂ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₁ j₁ : Fin d₁) :
    innerMatrix C₁ a (ρ₁ + ρ₂) i₁ j₁ =
      innerMatrix C₁ a ρ₁ i₁ j₁ + innerMatrix C₁ a ρ₂ i₁ j₁ := by
  ext p q
  simp [innerMatrix, Matrix.of_apply, Matrix.add_apply, extractBlock_add, map_add]

private theorem innerMatrix_smul (C₁ : QComp d₁ α) (a : α)
    (c : ℂ) (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₁ j₁ : Fin d₁) :
    innerMatrix C₁ a (c • ρ) i₁ j₁ = c • innerMatrix C₁ a ρ i₁ j₁ := by
  ext p q
  simp [innerMatrix, Matrix.of_apply, Matrix.smul_apply, extractBlock_smul, map_smul,
    smul_eq_mul]

private theorem jointBranch_unfold (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) (a : α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i j : Fin (d₁ * d₂)) :
    jointBranch C₁ C₂ a b ρ i j =
      let e := finProdEquiv d₁ d₂
      (C₂.branch b (innerMatrix C₁ a ρ (e.symm i).1 (e.symm j).1))
        (e.symm i).2 (e.symm j).2 := by
  simp [jointBranch, innerMatrix, Matrix.of_apply]

theorem jointBranch_add (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) (a : α) (b : β)
    (ρ₁ ρ₂ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointBranch C₁ C₂ a b (ρ₁ + ρ₂) =
      jointBranch C₁ C₂ a b ρ₁ + jointBranch C₁ C₂ a b ρ₂ := by
  ext i j
  simp only [jointBranch_unfold, Matrix.add_apply]
  rw [innerMatrix_add, map_add, Matrix.add_apply]

theorem jointBranch_smul (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) (a : α) (b : β)
    (c : ℂ) (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointBranch C₁ C₂ a b (c • ρ) = c • jointBranch C₁ C₂ a b ρ := by
  ext i j
  simp only [jointBranch_unfold, Matrix.smul_apply, smul_eq_mul]
  rw [innerMatrix_smul, map_smul, Matrix.smul_apply, smul_eq_mul]

/-! ## The qRHL Judgment -/

/-- **Quantum Relational Hoare Logic judgment** `{Φ} C₁ ~ C₂ {Ψ}`.

    For programs C₁ on d₁-dim and C₂ on d₂-dim, with bipartite pre/post-
    conditions on the joint system d₁ × d₂:

    For all joint PSD states ρ satisfying Φ, the post-evolution state
    (summing over all outcome pairs) satisfies Ψ.

    The post-evolution state is `∑'_{a,b} jointBranch(C₁,C₂,a,b)(ρ)` where
    `jointBranch` applies `C₁.branch a` on register 1 and `C₂.branch b`
    on register 2. -/
def qrHoare
    (Φ : BipartitePred d₁ d₂)
    (C₁ : QComp d₁ α)
    (C₂ : QComp d₂ β)
    (Ψ : BipartitePred d₁ d₂) : Prop :=
  ∀ (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ),
    ρ.PosSemidef → Φ ρ →
    Ψ (∑' (p : α × β), jointBranch C₁ C₂ p.1 p.2 ρ)

notation "⟪" Φ "⟫ " C₁ " ~ " C₂ " ⟪" Ψ "⟫" => qrHoare Φ C₁ C₂ Ψ

/-! ## Joint Branch on Pure / Identity -/

/-- Joint branch where C₂ is pure and outcome doesn't match gives 0. -/
theorem jointBranch_qpure_ne_right {b b' : β} (hb : b' ≠ b)
    (C₁ : QComp d₁ α) (a : α)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointBranch C₁ (QComp.qpure b) a b' ρ = 0 := by
  ext i j
  simp only [jointBranch, Matrix.of_apply, QComp.qpure, hb, ite_false,
    LinearMap.zero_apply, Matrix.zero_apply]

/-- Joint branch where both sides are pure is the identity (when outcomes match). -/
theorem jointBranch_qpure (a : α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointBranch (QComp.qpure a) (QComp.qpure b) a b ρ = ρ := by
  ext i j
  simp only [jointBranch, Matrix.of_apply, QComp.qpure, ite_true, LinearMap.id_coe, id_eq,
    extractBlock_apply, Matrix.of_apply]
  -- Goal: ρ (finProdEquiv d₁ d₂ (e⁻¹(i).1, e⁻¹(i).2)) (finProdEquiv d₁ d₂ (e⁻¹(j).1, e⁻¹(j).2)) = ρ i j
  simp [Equiv.apply_symm_apply]

/-- Joint branch where both sides are pure gives 0 for non-matching outcomes. -/
theorem jointBranch_qpure_ne {a a' : α} {b b' : β}
    (h : ¬(a' = a ∧ b' = b))
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointBranch (QComp.qpure a) (QComp.qpure b) a' b' ρ = 0 := by
  by_cases hb : b' = b
  · subst hb
    -- a' ≠ a
    have ha : a' ≠ a := fun ha => h ⟨ha, rfl⟩
    ext i j
    simp only [jointBranch, Matrix.of_apply, QComp.qpure, ite_true, LinearMap.id_coe, id_eq,
      Matrix.of_apply, ha, ite_false, LinearMap.zero_apply, Matrix.zero_apply]
  · exact jointBranch_qpure_ne_right hb (QComp.qpure a) a' ρ

/-! ## Structural Rules -/

/-- **Skip-Skip rule**: `{Φ} pure a ~ pure b {Φ}`.
    Pure computations do not change the quantum state. -/
theorem qrhl_skip (Φ : BipartitePred d₁ d₂) (a : α) (b : β) :
    qrHoare Φ (QComp.qpure a) (QComp.qpure b) Φ := by
  intro ρ _hρ hΦ
  convert hΦ using 1
  rw [tsum_eq_single (a, b) (fun ⟨a', b'⟩ hab => by
    exact jointBranch_qpure_ne (fun h => hab (Prod.ext h.1 h.2)) ρ)]
  exact jointBranch_qpure a b ρ

/-- **Consequence rule**: strengthen pre, weaken post.
    If `{Φ} C₁ ~ C₂ {Ψ}` and `Φ' → Φ` and `Ψ → Ψ'`, then `{Φ'} C₁ ~ C₂ {Ψ'}`. -/
theorem qrhl_conseq {Φ Φ' : BipartitePred d₁ d₂} {Ψ Ψ' : BipartitePred d₁ d₂}
    {C₁ : QComp d₁ α} {C₂ : QComp d₂ β}
    (h : qrHoare Φ C₁ C₂ Ψ)
    (hΦ : ∀ ρ, ρ.PosSemidef → Φ' ρ → Φ ρ)
    (hΨ : ∀ ρ, Ψ ρ → Ψ' ρ) :
    qrHoare Φ' C₁ C₂ Ψ' := by
  intro ρ hρ hΦ'
  exact hΨ _ (h ρ hρ (hΦ ρ hρ hΦ'))

/-! ## One-Sided Rules -/

/-- The joint state after running `C₁` on register 1 and `pure b` on register 2:
    the sum over outcomes `a` of `jointBranch C₁ (pure b) a b ρ`. -/
def oneSidedPost (C₁ : QComp d₁ α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ :=
  ∑' a, jointBranch C₁ (QComp.qpure b) a b ρ

/-- The weakest precondition of `Ψ` under `C₁ ~ pure b`: the predicate that holds of
    `ρ` exactly when `Ψ` holds of `oneSidedPost C₁ b ρ`. -/
def BipartitePred.oneSidedPre (C₁ : QComp d₁ α) (b : β) (Ψ : BipartitePred d₁ d₂) :
    BipartitePred d₁ d₂ :=
  fun ρ => Ψ (oneSidedPost C₁ b ρ)

/-- The post-state of `C₁ ~ pure b` summed over outcome pairs is `oneSidedPost C₁ b ρ`. -/
theorem tsum_jointBranch_qpure_right (C₁ : QComp d₁ α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑' (p : α × β), jointBranch C₁ (QComp.qpure b) p.1 p.2 ρ = oneSidedPost C₁ b ρ := by
  set F := fun (p : α × β) => jointBranch C₁ (QComp.qpure b) p.1 p.2 ρ
  set G := fun (a : α) => jointBranch C₁ (QComp.qpure b) a b ρ
  show ∑' p, F p = ∑' a, G a
  apply tsum_eq_tsum_of_ne_zero_bij (i := fun x => (x.1, b))
  · -- Injective
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Subtype.ext h.1
  · -- support F ⊆ range i
    intro ⟨a, b'⟩ hab
    simp only [F, Function.mem_support] at hab
    -- F(a, b') ≠ 0 implies b' = b
    have hb' : b' = b := by
      by_contra hne
      exact hab (jointBranch_qpure_ne_right hne C₁ a ρ)
    subst hb'
    exact ⟨⟨a, hab⟩, rfl⟩
  · -- f (i x) = g x
    intro ⟨a, _⟩; rfl

/-- **One-sided rule, weakest-precondition form**: `{oneSidedPre C₁ b Ψ} C₁ ~ pure b {Ψ}`. -/
theorem qrhl_one_sided_left_wp (C₁ : QComp d₁ α) (b : β) (Ψ : BipartitePred d₁ d₂) :
    qrHoare (BipartitePred.oneSidedPre C₁ b Ψ) C₁ (QComp.qpure b) Ψ := by
  intro ρ _hρ hΦ
  rw [tsum_jointBranch_qpure_right]
  exact hΦ

/-- Entries of `jointBranch C₁ (pure b) a b ρ`: `C₁.branch a` applied to the block of `ρ`
    indexed by the second-register coordinates. -/
theorem jointBranch_qpure_right_apply (C₁ : QComp d₁ α) (a : α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i j : Fin (d₁ * d₂)) :
    jointBranch C₁ (QComp.qpure b) a b ρ i j =
      C₁.branch a (extractBlock ρ ((finProdEquiv d₁ d₂).symm i).2
        ((finProdEquiv d₁ d₂).symm j).2)
        ((finProdEquiv d₁ d₂).symm i).1 ((finProdEquiv d₁ d₂).symm j).1 := by
  simp [jointBranch, QComp.qpure]

/-- The family `a ↦ jointBranch C₁ (pure b) a b ρ` is summable. -/
theorem summable_jointBranch_qpure_right (C₁ : QComp d₁ α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Summable (fun a => jointBranch C₁ (QComp.qpure b) a b ρ) := by
  refine Pi.summable.mpr fun i => Pi.summable.mpr fun j => ?_
  simp only [jointBranch_qpure_right_apply]
  exact Pi.summable.mp (Pi.summable.mp (C₁.branch_summable _) _) _

/-- Each block of `oneSidedPost C₁ b ρ` is the total action of `C₁` on the
    corresponding block of `ρ`. -/
theorem extractBlock_oneSidedPost (C₁ : QComp d₁ α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i₂ j₂ : Fin d₂) :
    extractBlock (oneSidedPost C₁ b ρ) i₂ j₂ = ∑' a, C₁.branch a (extractBlock ρ i₂ j₂) := by
  ext i₁ j₁
  rw [extractBlock_apply, oneSidedPost]
  erw [tsum_apply (summable_jointBranch_qpure_right C₁ b ρ),
    tsum_apply (Pi.summable.mp (summable_jointBranch_qpure_right C₁ b ρ) _),
    tsum_apply (C₁.branch_summable _), tsum_apply (Pi.summable.mp (C₁.branch_summable _) _)]
  simp only [jointBranch_qpure_right_apply, Equiv.symm_apply_apply]

/-- The first marginal of `oneSidedPost C₁ b ρ` is the total action of `C₁` on the
    first marginal of `ρ`. -/
theorem partialTrace₂_oneSidedPost (C₁ : QComp d₁ α) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    partialTrace₂ (oneSidedPost C₁ b ρ) = ∑' a, C₁.branch a (partialTrace₂ ρ) := by
  have hsum : ∀ X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ,
      partialTrace₂ X = ∑ k : Fin d₂, extractBlock X k k := by
    intro X; ext i₁ j₁
    simp [partialTrace₂_apply, Matrix.sum_apply, extractBlock_apply]
  rw [hsum, hsum]
  simp only [extractBlock_oneSidedPost, map_sum]
  exact (Summable.tsum_finsetSum fun k _ => C₁.branch_summable _).symm

/-- If `C₁` is trace-preserving, the second marginal of `oneSidedPost C₁ b ρ` is the
    second marginal of `ρ`. -/
theorem partialTrace₁_oneSidedPost (C₁ : QComp d₁ α) (b : β)
    (htp : ∀ σ : Matrix (Fin d₁) (Fin d₁) ℂ, (∑' a, C₁.branch a σ).trace = σ.trace)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    partialTrace₁ (oneSidedPost C₁ b ρ) = partialTrace₁ ρ := by
  have htr : ∀ (X : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i₂ j₂ : Fin d₂),
      partialTrace₁ X i₂ j₂ = (extractBlock X i₂ j₂).trace := by
    intro X i₂ j₂
    simp [partialTrace₁_apply, Matrix.trace, extractBlock_apply]
  ext i₂ j₂
  rw [htr, htr, extractBlock_oneSidedPost, htp]

/-- **One-sided rule**: if the total action of `C₁` preserves `P₁` on PSD states and is
    trace-preserving, then `{P₁ ⊗ P₂} C₁ ~ pure b {P₁ ⊗ P₂}` for the product predicate. -/
theorem qrhl_one_sided_left
    (P₁ : Matrix (Fin d₁) (Fin d₁) ℂ → Prop)
    (P₂ : Matrix (Fin d₂) (Fin d₂) ℂ → Prop)
    (C₁ : QComp d₁ α) (b : β)
    (h₁ : ∀ σ, σ.PosSemidef → P₁ σ →
      P₁ (∑' a, C₁.branch a σ))
    (htp : ∀ σ : Matrix (Fin d₁) (Fin d₁) ℂ, (∑' a, C₁.branch a σ).trace = σ.trace) :
    qrHoare (BipartitePred.product P₁ P₂) C₁ (QComp.qpure b)
      (BipartitePred.product P₁ P₂) := by
  refine qrhl_conseq (qrhl_one_sided_left_wp C₁ b _) ?_ (fun _ h => h)
  intro ρ hρ ⟨hP₁, hP₂⟩
  refine ⟨?_, ?_⟩
  · rw [partialTrace₂_oneSidedPost]
    exact h₁ _ (partialTrace₂_psd ρ hρ) hP₁
  · rw [partialTrace₁_oneSidedPost C₁ b htp]
    exact hP₂

/-- Two bipartite matrices with equal blocks are equal. -/
theorem eq_of_extractBlock_eq {X Y : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ}
    (h : ∀ i₂ j₂, extractBlock X i₂ j₂ = extractBlock Y i₂ j₂) : X = Y := by
  ext i j
  have := congrFun (congrFun (h ((finProdEquiv d₁ d₂).symm i).2
    ((finProdEquiv d₁ d₂).symm j).2) ((finProdEquiv d₁ d₂).symm i).1)
    ((finProdEquiv d₁ d₂).symm j).1
  simpa [extractBlock_apply] using this

/-- If every branch of `C₁` is completely positive, `oneSidedPost C₁ b` maps PSD states
    to PSD states. -/
theorem oneSidedPost_psd (C₁ : QComp d₁ α) (b : β) (hcp : ∀ a, IsCPMap (C₁.branch a))
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (hρ : ρ.PosSemidef) :
    (oneSidedPost C₁ b ρ).PosSemidef := by
  have heq : ∀ a, jointBranch C₁ (QComp.qpure b) a b ρ =
      (localOp₁ (d₂ := d₂) C₁ hcp).branch a ρ := by
    intro a; ext i j
    rw [jointBranch_qpure_right_apply]
    rfl
  unfold oneSidedPost
  simp_rw [heq]
  exact tsum_posSemidef (fun a => (localOp₁ C₁ hcp).branch_psd a ρ hρ)
    ((localOp₁ C₁ hcp).branch_summable ρ)

/-- `oneSidedPost` of the sequential composition `C₁; D₁` is the composite of the
    `oneSidedPost` maps of `C₁` and `D₁`. -/
theorem oneSidedPost_qbind {γ : Type} (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ) (b b' : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    oneSidedPost (QComp.qbind C₁ fun _ => D₁) b' ρ =
      oneSidedPost D₁ b' (oneSidedPost C₁ b ρ) := by
  refine eq_of_extractBlock_eq fun i₂ j₂ => ?_
  rw [extractBlock_oneSidedPost, extractBlock_oneSidedPost, extractBlock_oneSidedPost]
  refine tsum_congr fun c => ?_
  exact ((LinearMap.toContinuousLinearMap (D₁.branch c)).map_tsum
    (C₁.branch_summable _)).symm

/-- **One-sided sequence rule**: if `{Φ} C₁ ~ pure b {Θ}` and `{Θ} D₁ ~ pure b' {Ψ}`, and
    every branch of `C₁` is completely positive, then
    `{Φ} (C₁; D₁) ~ pure b' {Ψ}`, where `C₁; D₁` is `qbind C₁ (fun _ => D₁)`. -/
theorem qrhl_seq_one_sided_left {γ : Type}
    {Φ Θ Ψ : BipartitePred d₁ d₂} (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ) (b b' : β)
    (hcp : ∀ a, IsCPMap (C₁.branch a))
    (h₁ : qrHoare Φ C₁ (QComp.qpure b) Θ)
    (h₂ : qrHoare Θ D₁ (QComp.qpure b') Ψ) :
    qrHoare Φ (QComp.qbind C₁ fun _ => D₁) (QComp.qpure b') Ψ := by
  intro ρ hρ hΦ
  have hmid := h₁ ρ hρ hΦ
  rw [tsum_jointBranch_qpure_right] at hmid
  have hfin := h₂ _ (oneSidedPost_psd C₁ b hcp ρ hρ) hmid
  rw [tsum_jointBranch_qpure_right] at hfin
  rw [tsum_jointBranch_qpure_right, oneSidedPost_qbind C₁ D₁ b b']
  exact hfin

/-! ## Unitary Rules -/

/-- Joint branch for a unitary channel has a single non-zero term and acts by
    conjugation with the tensor product unitary `U₁ ⊗ₖ U₂`. -/
theorem jointBranch_unitaryChannel
    (U₁ : Matrix.unitaryGroup (Fin d₁) ℂ)
    (U₂ : Matrix.unitaryGroup (Fin d₂) ℂ)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointBranch (unitaryChannel U₁) (unitaryChannel U₂) () () ρ =
      (U₁ : Matrix _ _ ℂ) ⊗ₖ (U₂ : Matrix _ _ ℂ) * ρ *
        ((U₁ : Matrix _ _ ℂ) ⊗ₖ (U₂ : Matrix _ _ ℂ))ᴴ := by
  -- Entry-wise proof: expand to sums, reindex flat sums to product sums, close by ring
  rw [conjTranspose_kronecker]
  ext i j
  set e := finProdEquiv d₁ d₂
  simp only [jointBranch, unitaryChannel, conjugate_apply, Matrix.of_apply,
    extractBlock_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, kronecker_apply]
  -- Reindex flat sums over Fin (d₁*d₂) to product sums over Fin d₁ × Fin d₂
  have hri : ∀ (f : Fin (d₁ * d₂) → ℂ),
      ∑ x, f x = ∑ p : Fin d₁ × Fin d₂, f (e p) := fun f => (e.sum_comp f).symm
  rw [hri]; simp_rw [hri]
  simp only [e, Equiv.symm_apply_apply]
  -- Split product sums: ∑ (k₁, k₂) → ∑ k₂ ∑ k₁
  simp_rw [Fintype.sum_prod_type_right]
  congr 1; funext k₂
  -- Distribute multiplications into sums on LHS, then swap sum order
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; funext k₁
  simp only [mul_assoc]
  exact Finset.sum_congr (ι := Fin d₂) (M := ℂ) rfl (fun l₂ _ => by
    rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l₁ _ => by
      ring))

/-- The post-state of `unitaryChannel U₁ ~ unitaryChannel U₂` summed over outcome pairs is
    the conjugation of `ρ` by `U₁ ⊗ₖ U₂`. -/
theorem tsum_jointBranch_unitaryChannel
    (U₁ : Matrix.unitaryGroup (Fin d₁) ℂ)
    (U₂ : Matrix.unitaryGroup (Fin d₂) ℂ)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑' (p : Unit × Unit), jointBranch (unitaryChannel U₁) (unitaryChannel U₂) p.1 p.2 ρ =
      (U₁ : Matrix _ _ ℂ) ⊗ₖ (U₂ : Matrix _ _ ℂ) * ρ *
        ((U₁ : Matrix _ _ ℂ) ⊗ₖ (U₂ : Matrix _ _ ℂ))ᴴ := by
  rw [tsum_eq_single ((), ()) (fun ⟨a, b⟩ h =>
    absurd (Prod.ext (Subsingleton.elim a ()) (Subsingleton.elim b ())) h)]
  exact jointBranch_unitaryChannel U₁ U₂ ρ

/-- The weakest precondition of `Ψ` under `unitaryChannel U₁ ~ unitaryChannel U₂`:
    the predicate that holds of `ρ` exactly when `Ψ` holds of its conjugation by
    `U₁ ⊗ₖ U₂`. -/
def BipartitePred.conjPre
    (U₁ : Matrix.unitaryGroup (Fin d₁) ℂ)
    (U₂ : Matrix.unitaryGroup (Fin d₂) ℂ)
    (Ψ : BipartitePred d₁ d₂) : BipartitePred d₁ d₂ :=
  fun ρ => Ψ ((U₁ : Matrix _ _ ℂ) ⊗ₖ (U₂ : Matrix _ _ ℂ) * ρ *
    ((U₁ : Matrix _ _ ℂ) ⊗ₖ (U₂ : Matrix _ _ ℂ))ᴴ)

/-- The image of `Φ` under conjugation by `U₁ ⊗ₖ U₂`: the predicate that holds of `σ`
    exactly when `σ` is the conjugation of a PSD state satisfying `Φ`. -/
def BipartitePred.conjImage
    (U₁ : Matrix.unitaryGroup (Fin d₁) ℂ)
    (U₂ : Matrix.unitaryGroup (Fin d₂) ℂ)
    (Φ : BipartitePred d₁ d₂) : BipartitePred d₁ d₂ :=
  fun σ => ∃ ρ, ρ.PosSemidef ∧ Φ ρ ∧
    σ = (U₁ : Matrix _ _ ℂ) ⊗ₖ (U₂ : Matrix _ _ ℂ) * ρ *
      ((U₁ : Matrix _ _ ℂ) ⊗ₖ (U₂ : Matrix _ _ ℂ))ᴴ

/-- **Unitary-Unitary rule, weakest-precondition form**:
    `{conjPre U₁ U₂ Ψ} U₁ ~ U₂ {Ψ}`. -/
theorem qrhl_unitary_wp
    (U₁ : Matrix.unitaryGroup (Fin d₁) ℂ)
    (U₂ : Matrix.unitaryGroup (Fin d₂) ℂ)
    (Ψ : BipartitePred d₁ d₂) :
    qrHoare (BipartitePred.conjPre U₁ U₂ Ψ) (unitaryChannel U₁) (unitaryChannel U₂) Ψ := by
  intro ρ _hρ hΦ
  rw [tsum_jointBranch_unitaryChannel]
  exact hΦ

/-- **Unitary-Unitary rule, strongest-postcondition form**:
    `{Φ} U₁ ~ U₂ {conjImage U₁ U₂ Φ}`. -/
theorem qrhl_unitary
    (U₁ : Matrix.unitaryGroup (Fin d₁) ℂ)
    (U₂ : Matrix.unitaryGroup (Fin d₂) ℂ)
    (Φ : BipartitePred d₁ d₂) :
    qrHoare Φ (unitaryChannel U₁) (unitaryChannel U₂) (BipartitePred.conjImage U₁ U₂ Φ) := by
  intro ρ hρ hΦ
  rw [tsum_jointBranch_unitaryChannel]
  exact ⟨ρ, hρ, hΦ, rfl⟩

/-! ## Quantum Indistinguishability via qRHL -/

/-- **Quantum indistinguishability (induced / Helstrom distance).** Two programs
    are ε-indistinguishable if no distinguisher `D` and input `ρ` *on the
    program's own dimension* `d₁` separate them by more than ε.

    `ρ` carries no reference register. The diamond-norm version, which adds a
    reference register and satisfies a frame rule, is `qIndistDiamond` in
    `CatCryptCore.Crypto.UCMonad.QIndistDiamond`. -/
def qIndist (C₁ C₂ : QComp d₁ α) (ε : ℝ≥0∞) : Prop :=
  ∀ (D : α → QComp d₁ Bool) (ρ : DensityMatrix d₁),
    absDiff (prTrue_Q (QComp.qbind C₁ D) ρ) (prTrue_Q (QComp.qbind C₂ D) ρ) ≤ ε

/-- qIndist is reflexive. -/
theorem qIndist_refl (C : QComp d₁ α) : qIndist C C 0 := by
  intro D ρ; simp [absDiff]

/-- qIndist is symmetric. -/
theorem qIndist_symm {C₁ C₂ : QComp d₁ α} {ε : ℝ≥0∞}
    (h : qIndist C₁ C₂ ε) : qIndist C₂ C₁ ε := by
  intro D ρ
  have := h D ρ
  simp only [absDiff] at this ⊢
  rw [sup_comm]
  exact this

/-- qIndist satisfies triangle inequality. -/
theorem qIndist_triangle {C₁ C₂ C₃ : QComp d₁ α} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : qIndist C₁ C₂ ε₁) (h₂ : qIndist C₂ C₃ ε₂) :
    qIndist C₁ C₃ (ε₁ + ε₂) := by
  intro D ρ
  calc absDiff (prTrue_Q (QComp.qbind C₁ D) ρ) (prTrue_Q (QComp.qbind C₃ D) ρ)
      ≤ absDiff (prTrue_Q (QComp.qbind C₁ D) ρ) (prTrue_Q (QComp.qbind C₂ D) ρ) +
        absDiff (prTrue_Q (QComp.qbind C₂ D) ρ) (prTrue_Q (QComp.qbind C₃ D) ρ) :=
        absDiff_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add (h₁ D ρ) (h₂ D ρ)

end CatCrypt.Quantum.QRHL

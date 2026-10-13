/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.Instrument
public import CatCryptCore.Quantum.CPMap
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Tensor Products for QComp

Defines bipartite quantum registers via tensor products on `QComp (d₁ * d₂)`.

## Main Definitions

* `finProdEquiv` — `Fin d₁ × Fin d₂ ≃ Fin (d₁ * d₂)` for matrix indexing
* `kronecker` — Kronecker (tensor) product of matrices
* `tensorPure` — tensor of pure states: `qpure a ⊗ qpure b = qpure (a, b)`
* `extractBlock` — extract (i₂, j₂)-block from bipartite matrix
* `localOp₁` — apply QComp on first register only
* `localOp₂` — apply QComp on second register only

## Mathematical Background

The tensor product of `ℂ^d₁` and `ℂ^d₂` is `ℂ^(d₁·d₂)`. We represent
matrices on this space as `Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ`,
using the equivalence `Fin d₁ × Fin d₂ ≃ Fin (d₁ * d₂)` to decompose indices.

The Kronecker product `A ⊗ B` satisfies:
- `(A ⊗ B)_{(i₁,i₂),(j₁,j₂)} = A_{i₁,j₁} · B_{i₂,j₂}`
- `tr(A ⊗ B) = tr(A) · tr(B)`
- `(A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD)` (mixed-product property)
- `(A ± C) ⊗ B = A ⊗ B ± C ⊗ B` (`kronecker_add_left`, `kronecker_sub_left`)
- `(A ⊗ B)ᴴ (A ⊗ B) = I` for isometries `A`, `B`
  (`kronecker_conjTranspose_mul_self`)

## References

* Watrous — The Theory of Quantum Information, Chapter 2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum

noncomputable section

namespace CatCrypt.Quantum.TensorProduct

variable {d₁ d₂ : ℕ} {α β : Type}

/-! ## Index Equivalence -/

/-- Canonical equivalence `Fin d₁ × Fin d₂ ≃ Fin (d₁ * d₂)`.

    Maps `(i, j)` to `i * d₂ + j`, which is the standard row-major ordering. -/
def finProdEquiv (d₁ d₂ : ℕ) : Fin d₁ × Fin d₂ ≃ Fin (d₁ * d₂) :=
  finProdFinEquiv

/-! ## Kronecker Product -/

/-- Kronecker (tensor) product of matrices.

    `(kronecker A B)_{(i₁,i₂),(j₁,j₂)} = A_{i₁,j₁} · B_{i₂,j₂}`

    Uses `finProdEquiv` to map composite indices to `Fin (d₁ * d₂)`. -/
def kronecker
    (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ :=
  Matrix.of fun i j =>
    let ⟨i₁, i₂⟩ := (finProdEquiv d₁ d₂).symm i
    let ⟨j₁, j₂⟩ := (finProdEquiv d₁ d₂).symm j
    A i₁ j₁ * B i₂ j₂

infixl:70 " ⊗ₖ " => kronecker

/-- Kronecker product entry decomposition. -/
@[grind =]
theorem kronecker_apply (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (i j : Fin (d₁ * d₂)) :
    (A ⊗ₖ B) i j =
      A ((finProdEquiv d₁ d₂).symm i).1 ((finProdEquiv d₁ d₂).symm j).1 *
      B ((finProdEquiv d₁ d₂).symm i).2 ((finProdEquiv d₁ d₂).symm j).2 := by
  simp [kronecker, Matrix.of_apply]

/-! ## Kronecker Product Properties -/

/-- Kronecker product with identity on the left. -/
@[grind =]
theorem kronecker_one_left (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    (1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ B = Matrix.of fun i j =>
      let ⟨i₁, i₂⟩ := (finProdEquiv d₁ d₂).symm i
      let ⟨j₁, j₂⟩ := (finProdEquiv d₁ d₂).symm j
      if i₁ = j₁ then B i₂ j₂ else 0 := by
  ext i j
  simp [kronecker_apply, Matrix.one_apply]

/-- Kronecker product with identity on the right. -/
@[grind =]
theorem kronecker_one_right (A : Matrix (Fin d₁) (Fin d₁) ℂ) :
    A ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ) = Matrix.of fun i j =>
      let ⟨i₁, i₂⟩ := (finProdEquiv d₁ d₂).symm i
      let ⟨j₁, j₂⟩ := (finProdEquiv d₁ d₂).symm j
      if i₂ = j₂ then A i₁ j₁ else 0 := by
  ext i j
  simp [kronecker_apply, Matrix.one_apply]

/-- Trace of Kronecker product = product of traces. -/
@[grind =]
theorem trace_kronecker (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    (A ⊗ₖ B).trace = A.trace * B.trace := by
  simp only [Matrix.trace, Matrix.diag, kronecker_apply]
  rw [Fintype.sum_equiv (finProdEquiv d₁ d₂).symm _
    (fun p => A p.1 p.1 * B p.2 p.2) (fun _ => rfl)]
  rw [Fintype.sum_prod_type (fun p : Fin d₁ × Fin d₂ => A p.1 p.1 * B p.2 p.2)]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- Conjugate transpose distributes over Kronecker product. -/
@[grind =]
theorem conjTranspose_kronecker (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext i j
  simp only [kronecker_apply, conjTranspose_apply]
  exact star_mul' _ _

/-- Mixed product property of Kronecker product. -/
@[grind =]
theorem kronecker_mul_kronecker (A C : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B D : Matrix (Fin d₂) (Fin d₂) ℂ) :
    (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) := by
  ext i j
  simp only [Matrix.mul_apply]
  -- LHS: ∑ k, (A ⊗ₖ B) i k * (C ⊗ₖ D) k j
  -- RHS: ((A*C) ⊗ₖ (B*D)) i j
  simp only [kronecker_apply]
  -- Reindex sum via finProdEquiv
  set ip := (finProdEquiv d₁ d₂).symm i
  set jp := (finProdEquiv d₁ d₂).symm j
  -- Rearrange and split
  calc ∑ k, A ip.1 ((finProdEquiv d₁ d₂).symm k).1 *
      B ip.2 ((finProdEquiv d₁ d₂).symm k).2 *
      (C ((finProdEquiv d₁ d₂).symm k).1 jp.1 *
       D ((finProdEquiv d₁ d₂).symm k).2 jp.2)
      = ∑ p : Fin d₁ × Fin d₂,
          (A ip.1 p.1 * C p.1 jp.1) * (B ip.2 p.2 * D p.2 jp.2) := by
        rw [← (finProdEquiv d₁ d₂).symm.sum_comp]
        congr 1; ext k; ring
    _ = (∑ k₁, A ip.1 k₁ * C k₁ jp.1) * (∑ k₂, B ip.2 k₂ * D k₂ jp.2) := by
        rw [Fintype.sum_prod_type_right]
        rw [show ∑ y : Fin d₂, ∑ x : Fin d₁,
          A ip.1 x * C x jp.1 * (B ip.2 y * D y jp.2) =
          ∑ y : Fin d₂, (∑ x : Fin d₁, A ip.1 x * C x jp.1) *
            (B ip.2 y * D y jp.2) from
          Finset.sum_congr rfl (fun y _ => (Finset.sum_mul ..).symm)]
        rw [← Finset.mul_sum, mul_comm]
    _ = (A * C) ip.1 jp.1 * (B * D) ip.2 jp.2 := rfl

/-- Kronecker product I ⊗ₖ I = I. -/
@[grind =]
theorem kronecker_one_one :
    (1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ) =
    (1 : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) := by
  ext i j
  simp only [kronecker_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have : ¬(((finProdEquiv d₁ d₂).symm i).1 = ((finProdEquiv d₁ d₂).symm j).1 ∧
      ((finProdEquiv d₁ d₂).symm i).2 = ((finProdEquiv d₁ d₂).symm j).2) := by
      intro ⟨h1, h2⟩
      apply h
      exact (finProdEquiv d₁ d₂).symm.injective (Prod.ext h1 h2)
    rcases not_and_or.mp this with h1 | h2
    · simp [h, h1]
    · simp [h, h2]

/-- The Kronecker product is additive in its first argument. -/
theorem kronecker_add_left (A C : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    (A + C) ⊗ₖ B = A ⊗ₖ B + C ⊗ₖ B := by
  ext i j
  simp [kronecker_apply, add_mul]

/-- The Kronecker product is subtractive in its first argument. -/
theorem kronecker_sub_left (A C : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    (A - C) ⊗ₖ B = A ⊗ₖ B - C ⊗ₖ B := by
  ext i j
  simp [kronecker_apply, sub_mul]

/-- A scalar moves across the Kronecker product: `(c A) ⊗ B = A ⊗ (c B)`. -/
theorem smul_kronecker_eq_kronecker_smul (c : ℂ) (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) : (c • A) ⊗ₖ B = A ⊗ₖ (c • B) := by
  ext i j
  simp only [kronecker_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Kronecker products of isometries are isometries. -/
theorem kronecker_conjTranspose_mul_self {A : Matrix (Fin d₁) (Fin d₁) ℂ}
    {B : Matrix (Fin d₂) (Fin d₂) ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := by
  rw [conjTranspose_kronecker, kronecker_mul_kronecker, hA, hB, kronecker_one_one]

/-! ## Tensor Pure States -/

/-- The tensor of two pure QComp values.

    Maps `(a, b)` to the branch that applies both pure branches. -/
def tensorPure (a : α) (b : β) : QComp (d₁ * d₂) (α × β) where
  branch := fun ⟨a', b'⟩ =>
    if a' = a ∧ b' = b then LinearMap.id else 0
  branch_psd := fun ⟨a', b'⟩ ρ hρ => by
    simp only; split_ifs with h
    · exact hρ
    · exact Matrix.PosSemidef.zero
  branch_summable := fun ρ => by
    apply summable_of_ne_finset_zero (s := {(a, b)})
    intro ⟨a', b'⟩ hab
    simp only [Finset.mem_singleton, Prod.mk.injEq, not_and] at hab
    simp only
    split_ifs with h
    · exact absurd (hab h.1) (not_not.mpr h.2)
    · rfl
  branch_stp := fun ρ _ => by
    have : (fun p : α × β => ((if p.1 = a ∧ p.2 = b then
        (LinearMap.id : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ →ₗ[ℂ] _)
        else 0) ρ).trace) =
        (fun p : α × β => if p.1 = a ∧ p.2 = b then ρ.trace else 0) := by
      funext ⟨a', b'⟩; split_ifs <;> simp
    simp_rw [this]
    rw [tsum_eq_single (a, b) (fun ⟨a', b'⟩ h => by simp [show ¬(a' = a ∧ b' = b) from by
      intro ⟨ha, hb⟩; exact h (Prod.ext ha hb)])]
    simp

/-! ## Block Extraction -/

/-- Extract the `(i₂, j₂)`-block from a bipartite matrix.

    `(extractBlock ρ i₂ j₂)_{i₁,j₁} = ρ_{(i₁,i₂),(j₁,j₂)}`

    This views the `(d₁·d₂) × (d₁·d₂)` matrix as a `d₂ × d₂` grid of
    `d₁ × d₁` blocks. -/
def extractBlock
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₂ j₂ : Fin d₂) : Matrix (Fin d₁) (Fin d₁) ℂ :=
  Matrix.of fun i₁ j₁ =>
    ρ (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv d₁ d₂ (j₁, j₂))

@[grind =]
theorem extractBlock_apply
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₂ j₂ : Fin d₂) (i₁ j₁ : Fin d₁) :
    extractBlock ρ i₂ j₂ i₁ j₁ =
      ρ (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv d₁ d₂ (j₁, j₂)) := by
  simp [extractBlock, Matrix.of_apply]

@[grind =]
theorem extractBlock_add
    (ρ₁ ρ₂ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₂ j₂ : Fin d₂) :
    extractBlock (ρ₁ + ρ₂) i₂ j₂ = extractBlock ρ₁ i₂ j₂ + extractBlock ρ₂ i₂ j₂ := by
  ext i₁ j₁; simp [extractBlock_apply, Matrix.add_apply]

@[grind =]
theorem extractBlock_smul
    (c : ℂ) (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₂ j₂ : Fin d₂) :
    extractBlock (c • ρ) i₂ j₂ = c • extractBlock ρ i₂ j₂ := by
  ext i₁ j₁; simp [extractBlock_apply, Matrix.smul_apply]

/-- Kronecker product block extraction: `extractBlock (A ⊗ₖ B) i₂ j₂ = B i₂ j₂ • A`. -/
@[grind =]
theorem extractBlock_kronecker
    (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (i₂ j₂ : Fin d₂) :
    extractBlock (A ⊗ₖ B) i₂ j₂ = B i₂ j₂ • A := by
  ext i₁ j₁
  simp [extractBlock_apply, kronecker_apply, Matrix.smul_apply, mul_comm]

/-! ## Helpers for Local Operations -/

/-- Diagonal blocks of a PSD matrix are PSD. -/
theorem extractBlock_diag_psd
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (hρ : ρ.PosSemidef) (k : Fin d₂) :
    (extractBlock ρ k k).PosSemidef :=
  hρ.submatrix (fun i₁ => finProdEquiv d₁ d₂ (i₁, k))

/-- Diagonal block traces sum to total trace. -/
theorem sum_extractBlock_diag_trace
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑ k : Fin d₂, (extractBlock ρ k k).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, extractBlock_apply]
  -- ∑ k, ∑ i₁, ρ (e (i₁,k)) (e (i₁,k)) = ∑ i, ρ i i
  -- Swap sums: ∑ k, ∑ i₁ → ∑ i₁, ∑ k, then fold as product sum
  rw [Finset.sum_comm,
    ← Fintype.sum_prod_type
      (fun p : Fin d₁ × Fin d₂ =>
        ρ (finProdEquiv d₁ d₂ p) (finProdEquiv d₁ d₂ p))]
  exact Fintype.sum_equiv (finProdEquiv d₁ d₂) _ _ (fun _ => rfl)

/-- Second-register diagonal blocks of a PSD matrix are PSD. -/
private theorem extractBlock₂_diag_psd
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (hρ : ρ.PosSemidef) (k : Fin d₁) :
    (Matrix.of fun i₂ j₂ =>
      ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂))).PosSemidef :=
  hρ.submatrix (fun i₂ => finProdEquiv d₁ d₂ (k, i₂))

/-- Second-register diagonal block traces sum to total trace. -/
private theorem sum_extractBlock₂_diag_trace
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ∑ k : Fin d₁, (Matrix.of fun i₂ j₂ =>
      ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂))).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  -- ∑ k : Fin d₁, ∑ i₂ : Fin d₂, ρ (e (k,i₂)) (e (k,i₂)) = ∑ i, ρ i i
  rw [← Fintype.sum_prod_type
    (fun p : Fin d₁ × Fin d₂ =>
      ρ (finProdEquiv d₁ d₂ p) (finProdEquiv d₁ d₂ p))]
  exact Fintype.sum_equiv (finProdEquiv d₁ d₂) _ _ (fun _ => rfl)

/-! ## Local Operations -/

/-- The raw function underlying `localOp₁.branch a`. -/
def localOp₁_fun (op : QComp d₁ α) (a : α)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ :=
  Matrix.of fun i j =>
    let ⟨i₁, i₂⟩ := (finProdEquiv d₁ d₂).symm i
    let ⟨j₁, j₂⟩ := (finProdEquiv d₁ d₂).symm j
    (op.branch a (extractBlock ρ i₂ j₂)) i₁ j₁

/-- Trace of `localOp₁.branch a ρ` decomposes into diagonal block traces. -/
theorem trace_localOp₁_fun (op : QComp d₁ α) (a : α)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    (localOp₁_fun op a ρ).trace =
      ∑ k : Fin d₂, (op.branch a (extractBlock ρ k k)).trace := by
  simp only [localOp₁_fun, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Fintype.sum_equiv (finProdEquiv d₁ d₂).symm _
    (fun p : Fin d₁ × Fin d₂ =>
      (op.branch a (extractBlock ρ p.2 p.2)) p.1 p.1)
    (fun _ => rfl),
    Fintype.sum_prod_type, Finset.sum_comm]

/-- The raw function underlying `localOp₂.branch b`. -/
def localOp₂_fun (op : QComp d₂ β) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ :=
  Matrix.of fun i j =>
    let ⟨i₁, i₂⟩ := (finProdEquiv d₁ d₂).symm i
    let ⟨j₁, j₂⟩ := (finProdEquiv d₁ d₂).symm j
    (op.branch b (Matrix.of fun i₂' j₂' =>
      ρ (finProdEquiv d₁ d₂ (i₁, i₂')) (finProdEquiv d₁ d₂ (j₁, j₂')))) i₂ j₂

/-- Trace of `localOp₂.branch b ρ` decomposes into diagonal block traces. -/
private theorem trace_localOp₂_fun (op : QComp d₂ β) (b : β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    (localOp₂_fun op b ρ).trace =
      ∑ k : Fin d₁, (op.branch b (Matrix.of fun i₂ j₂ =>
        ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂)))).trace := by
  simp only [localOp₂_fun, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Fintype.sum_equiv (finProdEquiv d₁ d₂).symm _
    (fun p : Fin d₁ × Fin d₂ =>
      (op.branch b (of fun i₂' j₂' =>
        ρ (finProdEquiv d₁ d₂ (p.1, i₂')) (finProdEquiv d₁ d₂ (p.1, j₂')))) p.2 p.2)
    (fun _ => rfl),
    Fintype.sum_prod_type]

/-- Apply a QComp operation on the first register of a bipartite system.

    The branch `a` acts as `E_a ⊗ id` on the joint state:
    `[(E_a ⊗ id)(ρ)]_{(i₁,i₂),(j₁,j₂)} = (E_a(ρ^{i₂,j₂}))_{i₁,j₁}`
    where `ρ^{i₂,j₂}` is the `(i₂,j₂)`-block (a `d₁ × d₁` submatrix).

    Requires each branch to be completely positive (CP), since positivity alone
    does not suffice for tensor products (the transpose map is a counterexample). -/
def localOp₁ (op : QComp d₁ α) (hcp : ∀ a, IsCPMap (op.branch a)) :
    QComp (d₁ * d₂) α where
  branch a := {
    toFun := localOp₁_fun op a
    map_add' := fun ρ₁ ρ₂ => by
      ext i j
      simp only [localOp₁_fun, Matrix.of_apply, Matrix.add_apply]
      rw [extractBlock_add]
      simp [map_add]
    map_smul' := fun c ρ => by
      ext i j
      simp only [localOp₁_fun, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
      rw [extractBlock_smul]
      simp [map_smul]
  }
  branch_psd := fun a ρ hρ => by
    let g : Fin d₂ × Fin d₁ ≃ Fin (d₁ * d₂) :=
      (Equiv.prodComm (Fin d₂) (Fin d₁)).trans (finProdEquiv d₁ d₂)
    exact (hcp a d₂ (ρ.submatrix g g) (hρ.submatrix g)).submatrix (⇑g.symm)
  branch_summable := fun ρ => by
    apply Pi.summable.mpr; intro i
    apply Pi.summable.mpr; intro j
    simp only [LinearMap.coe_mk, AddHom.coe_mk, localOp₁_fun, Matrix.of_apply]
    exact Pi.summable.mp (Pi.summable.mp (op.branch_summable
      (extractBlock ρ ((finProdEquiv d₁ d₂).symm i).2
        ((finProdEquiv d₁ d₂).symm j).2))
      ((finProdEquiv d₁ d₂).symm i).1) ((finProdEquiv d₁ d₂).symm j).1
  branch_stp := fun ρ hρ => by
    show (∑' a, (localOp₁_fun op a ρ).trace).re ≤ ρ.trace.re
    simp_rw [trace_localOp₁_fun]
    have h_summ : ∀ k : Fin d₂,
        Summable (fun a => (op.branch a (extractBlock ρ k k)).trace) := by
      intro k
      simp only [Matrix.trace, Matrix.diag]
      exact (hasSum_sum (fun i _ =>
        (Pi.summable.mp (Pi.summable.mp
          (op.branch_summable (extractBlock ρ k k)) i) i).hasSum)).summable
    rw [Summable.tsum_finsetSum (fun k _ => h_summ k)]
    calc (∑ k : Fin d₂, ∑' a, (op.branch a (extractBlock ρ k k)).trace).re
        = ∑ k : Fin d₂, (∑' a, (op.branch a (extractBlock ρ k k)).trace).re :=
          map_sum Complex.reCLM _ _
      _ ≤ ∑ k : Fin d₂, (extractBlock ρ k k).trace.re :=
          Finset.sum_le_sum (fun k _ => op.branch_stp _ (extractBlock_diag_psd ρ hρ k))
      _ = (∑ k : Fin d₂, (extractBlock ρ k k).trace).re :=
          (map_sum Complex.reCLM _ _).symm
      _ = ρ.trace.re := by rw [sum_extractBlock_diag_trace]

/-- Apply a QComp operation on the second register of a bipartite system.

    The branch `b` acts as `id ⊗ E_b` on the joint state. We extract
    `(i₁,j₁)`-blocks (each a `d₂ × d₂` matrix) and apply `E_b`.

    Requires each branch to be completely positive (CP). -/
def localOp₂ (op : QComp d₂ β) (hcp : ∀ b, IsCPMap (op.branch b)) :
    QComp (d₁ * d₂) β where
  branch b := {
    toFun := localOp₂_fun op b
    map_add' := fun ρ₁ ρ₂ => by
      ext i j; simp only [localOp₂_fun, Matrix.of_apply, Matrix.add_apply]
      set i₁ := ((finProdEquiv d₁ d₂).symm i).1
      set j₁ := ((finProdEquiv d₁ d₂).symm j).1
      set M := fun (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) =>
        Matrix.of fun i₂' j₂' => ρ (finProdEquiv d₁ d₂ (i₁, i₂')) (finProdEquiv d₁ d₂ (j₁, j₂'))
      show (op.branch b (M (ρ₁ + ρ₂))) _ _ = (op.branch b (M ρ₁)) _ _ + (op.branch b (M ρ₂)) _ _
      have : M (ρ₁ + ρ₂) = M ρ₁ + M ρ₂ := by ext; simp [M, Matrix.of_apply, Matrix.add_apply]
      rw [this, map_add, Matrix.add_apply]
    map_smul' := fun c ρ => by
      ext i j; simp only [localOp₂_fun, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
      set i₁ := ((finProdEquiv d₁ d₂).symm i).1
      set j₁ := ((finProdEquiv d₁ d₂).symm j).1
      set M := fun (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) =>
        Matrix.of fun i₂' j₂' => ρ (finProdEquiv d₁ d₂ (i₁, i₂')) (finProdEquiv d₁ d₂ (j₁, j₂'))
      show (op.branch b (M (c • ρ))) _ _ = c • (op.branch b (M ρ)) _ _
      have : M (c • ρ) = c • M ρ := by ext; simp [M, Matrix.of_apply, Matrix.smul_apply]
      rw [this, map_smul, Matrix.smul_apply]
  }
  branch_psd := fun b ρ hρ => by
    let e := finProdEquiv d₁ d₂
    exact (hcp b d₁ (ρ.submatrix e e) (hρ.submatrix e)).submatrix (⇑e.symm)
  branch_summable := fun ρ => by
    apply Pi.summable.mpr; intro i
    apply Pi.summable.mpr; intro j
    simp only [LinearMap.coe_mk, AddHom.coe_mk, localOp₂_fun, Matrix.of_apply]
    set i₁ := ((finProdEquiv d₁ d₂).symm i).1
    set j₁ := ((finProdEquiv d₁ d₂).symm j).1
    have h := op.branch_summable (Matrix.of fun i₂' j₂' =>
      ρ (finProdEquiv d₁ d₂ (i₁, i₂')) (finProdEquiv d₁ d₂ (j₁, j₂')))
    exact Pi.summable.mp (Pi.summable.mp h
      ((finProdEquiv d₁ d₂).symm i).2) ((finProdEquiv d₁ d₂).symm j).2
  branch_stp := fun ρ hρ => by
    show (∑' b, (localOp₂_fun op b ρ).trace).re ≤ ρ.trace.re
    simp_rw [trace_localOp₂_fun]
    have h_summ : ∀ k : Fin d₁,
        Summable (fun b => (op.branch b (Matrix.of fun i₂ j₂ =>
          ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂)))).trace) := by
      intro k
      simp only [Matrix.trace, Matrix.diag]
      exact (hasSum_sum (fun i _ =>
        (Pi.summable.mp (Pi.summable.mp
          (op.branch_summable (Matrix.of fun i₂ j₂ =>
            ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂)))) i) i).hasSum)).summable
    rw [Summable.tsum_finsetSum (fun k _ => h_summ k)]
    calc (∑ k : Fin d₁, ∑' b, (op.branch b (Matrix.of fun i₂ j₂ =>
            ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂)))).trace).re
        = ∑ k : Fin d₁, (∑' b, (op.branch b (Matrix.of fun i₂ j₂ =>
            ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂)))).trace).re :=
          map_sum Complex.reCLM _ _
      _ ≤ ∑ k : Fin d₁, (Matrix.of fun i₂ j₂ =>
            ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂))).trace.re :=
          Finset.sum_le_sum (fun k _ => op.branch_stp _ (extractBlock₂_diag_psd ρ hρ k))
      _ = (∑ k : Fin d₁, (Matrix.of fun i₂ j₂ =>
            ρ (finProdEquiv d₁ d₂ (k, i₂)) (finProdEquiv d₁ d₂ (k, j₂))).trace).re :=
          (map_sum Complex.reCLM _ _).symm
      _ = ρ.trace.re := by rw [sum_extractBlock₂_diag_trace]

/-! ## Local Operations on Kronecker States -/

/-- Local operation on first register of a Kronecker product applies
    the operation to the first factor. -/
theorem localOp₁_kronecker (op : QComp d₁ α) (hcp : ∀ a, IsCPMap (op.branch a))
    (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    ∀ a, (localOp₁ (d₂ := d₂) op hcp).branch a (A ⊗ₖ B) =
      (op.branch a A) ⊗ₖ B := by
  intro a; ext i j
  simp only [localOp₁, localOp₁_fun, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  rw [extractBlock_kronecker]
  simp only [map_smul, Matrix.smul_apply, kronecker_apply, smul_eq_mul]
  exact mul_comm _ _

/-! ## Kronecker Linearity over Finite Sums -/

variable {ι : Type} in
/-- Kronecker distributes over finite sums on the left:
    `∑ᵢ (Aᵢ ⊗ₖ B) = (∑ᵢ Aᵢ) ⊗ₖ B`. -/
theorem kronecker_finset_sum_left [Fintype ι]
    (A : ι → Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    ∑ i, A i ⊗ₖ B = (∑ i, A i) ⊗ₖ B := by
  ext p q
  simp only [kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

variable {ι : Type} in
/-- Kronecker distributes over finite sums on the right:
    `∑ᵢ (A ⊗ₖ Bᵢ) = A ⊗ₖ (∑ᵢ Bᵢ)`. -/
theorem kronecker_finset_sum_right [Fintype ι]
    (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : ι → Matrix (Fin d₂) (Fin d₂) ℂ) :
    ∑ i, A ⊗ₖ B i = A ⊗ₖ (∑ i, B i) := by
  ext p q
  simp only [kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

/-! ## Trace of (E ⊗ I) · localOp₁ -/

/-- Trace of `(E ⊗ₖ I) * localOp₁.branch a ρ` decomposes into diagonal block traces.

    `tr((E ⊗ I) * localOp₁(C).branch(a)(ρ)) = ∑_k tr(E * C.branch(a)(extractBlock ρ k k))` -/
theorem trace_kronecker_one_mul_localOp₁ (op : QComp d₁ α)
    (hcp : ∀ a, IsCPMap (op.branch a))
    (E : Matrix (Fin d₁) (Fin d₁) ℂ)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (a : α) :
    ((E ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) *
      (localOp₁ op hcp).branch a ρ).trace =
    ∑ k : Fin d₂, (E * op.branch a (extractBlock ρ k k)).trace := by
  -- Unfold LHS only, keeping RHS as-is
  conv_lhs =>
    rw [show (localOp₁ op hcp).branch a ρ = localOp₁_fun op a ρ from rfl]
  -- Now use the trace decomposition: tr(M) = ∑ p, M (e p) (e p) via finProdEquiv
  simp only [Matrix.trace, Matrix.diag]
  -- LHS: ∑ i, ∑ j, (E ⊗ₖ I) i j * (localOp₁_fun op a ρ) j i
  -- Reindex outer sum via finProdEquiv
  conv_lhs =>
    rw [show ∑ i : Fin (d₁ * d₂), _ =
      ∑ p : Fin d₁ × Fin d₂, ∑ j,
        (E ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) (finProdEquiv d₁ d₂ p) j *
        (localOp₁_fun op a ρ) j (finProdEquiv d₁ d₂ p) from
      (Fintype.sum_equiv (finProdEquiv d₁ d₂) _ _ (fun _ => rfl)).symm]
    rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  congr 1; ext k₂
  -- RHS: ∑ k₁, ∑ j₁, E k₁ j₁ * (op.branch a (extractBlock ρ k₂ k₂)) j₁ k₁
  -- LHS: ∑ k₁, ∑ j, (E ⊗ₖ I)_{(k₁,k₂),j} * localOp₁_fun_{j,(k₁,k₂)}
  congr 1; ext k₁
  -- Reindex inner sum via finProdEquiv
  rw [show ∑ j : Fin (d₁ * d₂), _ =
    ∑ p : Fin d₁ × Fin d₂,
      (E ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ))
        (finProdEquiv d₁ d₂ (k₁, k₂)) (finProdEquiv d₁ d₂ p) *
      (localOp₁_fun op a ρ) (finProdEquiv d₁ d₂ p)
        (finProdEquiv d₁ d₂ (k₁, k₂)) from
    (Fintype.sum_equiv (finProdEquiv d₁ d₂) _ _ (fun _ => rfl)).symm]
  rw [Fintype.sum_prod_type]
  -- Unfold kronecker and localOp₁_fun entries, simplify Equiv round-trips
  simp only [kronecker_apply, Matrix.one_apply, localOp₁_fun, Matrix.of_apply,
    Equiv.symm_apply_apply]
  -- Collapse δ sums
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.mul_apply]

/-- Trace of `(E ⊗ₖ I) * ρ` decomposes into diagonal block traces. -/
theorem trace_kronecker_one_mul (E : Matrix (Fin d₁) (Fin d₁) ℂ)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    ((E ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) * ρ).trace =
    ∑ k : Fin d₂, (E * extractBlock ρ k k).trace := by
  simp only [Matrix.trace, Matrix.diag]
  conv_lhs =>
    rw [show ∑ i : Fin (d₁ * d₂), _ =
      ∑ p : Fin d₁ × Fin d₂, ∑ j,
        (E ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) (finProdEquiv d₁ d₂ p) j *
        ρ j (finProdEquiv d₁ d₂ p) from
      (Fintype.sum_equiv (finProdEquiv d₁ d₂) _ _ (fun _ => rfl)).symm]
    rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  congr 1; ext k₂; congr 1; ext k₁
  rw [show ∑ j : Fin (d₁ * d₂), _ =
    ∑ p : Fin d₁ × Fin d₂,
      (E ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ))
        (finProdEquiv d₁ d₂ (k₁, k₂)) (finProdEquiv d₁ d₂ p) *
      ρ (finProdEquiv d₁ d₂ p) (finProdEquiv d₁ d₂ (k₁, k₂)) from
    (Fintype.sum_equiv (finProdEquiv d₁ d₂) _ _ (fun _ => rfl)).symm]
  rw [Fintype.sum_prod_type]
  simp only [kronecker_apply, Matrix.one_apply, extractBlock, Matrix.of_apply,
    Equiv.symm_apply_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.mul_apply]

/-! ## First-Register-Fixed Block Extraction

This is the mirror of `extractBlock`: it fixes the FIRST register and returns
the second-register slice. Together with `trace_one_kronecker_mul` below it
plays the role of the "left" companion to `extractBlock` /
`trace_kronecker_one_mul`, letting us decompose `tr((1 ⊗ M) * ρ)` in the same
way the existing API decomposes `tr((E ⊗ 1) * ρ)`. -/

/-- Extract the `(i₁, j₁)`-block from a bipartite matrix, fixing the **first**
register and returning the second-register slice.

`(extractBlock₁ ρ i₁ j₁)_{i₂,j₂} = ρ_{(i₁,i₂),(j₁,j₂)}`

Mirror of `extractBlock` (which fixes the second register). -/
def extractBlock₁
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₁ j₁ : Fin d₁) : Matrix (Fin d₂) (Fin d₂) ℂ :=
  Matrix.of fun i₂ j₂ =>
    ρ (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv d₁ d₂ (j₁, j₂))

@[grind =]
theorem extractBlock₁_apply
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ)
    (i₁ j₁ : Fin d₁) (i₂ j₂ : Fin d₂) :
    extractBlock₁ ρ i₁ j₁ i₂ j₂ =
      ρ (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv d₁ d₂ (j₁, j₂)) := by
  simp [extractBlock₁, Matrix.of_apply]

/-- Kronecker product first-register block:
    `extractBlock₁ (A ⊗ₖ B) i₁ j₁ = A i₁ j₁ • B`. -/
@[grind =]
theorem extractBlock₁_kronecker
    (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (i₁ j₁ : Fin d₁) :
    extractBlock₁ (A ⊗ₖ B) i₁ j₁ = A i₁ j₁ • B := by
  ext i₂ j₂
  simp [extractBlock₁_apply, kronecker_apply, Matrix.smul_apply]

/-- Trace of `(1 ⊗ₖ M) * ρ` decomposes into diagonal first-register block traces.

    Mirror of `trace_kronecker_one_mul`. Lets you peel off a `(1 : Matrix (Fin d₁)
    (Fin d₁) ℂ)` on the LEFT of a Kronecker product when computing traces. -/
theorem trace_one_kronecker_mul (M : Matrix (Fin d₂) (Fin d₂) ℂ)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    (((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ M) * ρ).trace =
    ∑ k : Fin d₁, (M * extractBlock₁ ρ k k).trace := by
  simp only [Matrix.trace, Matrix.diag]
  conv_lhs =>
    rw [show ∑ i : Fin (d₁ * d₂), _ =
      ∑ p : Fin d₁ × Fin d₂, ∑ j,
        ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ M) (finProdEquiv d₁ d₂ p) j *
        ρ j (finProdEquiv d₁ d₂ p) from
      (Fintype.sum_equiv (finProdEquiv d₁ d₂) _ _ (fun _ => rfl)).symm]
    rw [Fintype.sum_prod_type]
  congr 1; ext k₁; congr 1; ext k₂
  rw [show ∑ j : Fin (d₁ * d₂), _ =
    ∑ p : Fin d₁ × Fin d₂,
      ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ M)
        (finProdEquiv d₁ d₂ (k₁, k₂)) (finProdEquiv d₁ d₂ p) *
      ρ (finProdEquiv d₁ d₂ p) (finProdEquiv d₁ d₂ (k₁, k₂)) from
    (Fintype.sum_equiv (finProdEquiv d₁ d₂) _ _ (fun _ => rfl)).symm]
  rw [Fintype.sum_prod_type]
  simp only [kronecker_apply, Matrix.one_apply, extractBlock₁, Matrix.of_apply,
    Equiv.symm_apply_apply,
    ite_mul, one_mul, zero_mul,
    Matrix.mul_apply]
  -- Collapse the surviving indicators. Outer indicator is `if k₁ = x` —
  -- swap sums, then collapse for each fixed x_1.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x_1 _ => ?_)
  rw [Fintype.sum_ite_eq k₁
    (fun x : Fin d₁ => M k₂ x_1 *
      ρ (finProdEquiv d₁ d₂ (x, x_1)) (finProdEquiv d₁ d₂ (k₁, k₂)))]

end CatCrypt.Quantum.TensorProduct

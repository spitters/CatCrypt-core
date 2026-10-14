/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.TensorProduct

/-!
# Functoriality of `localOp₁`

`localOp₁` applies a channel on register 1 of a bipartite system (acting as
`E ⊗ id` on the joint state). This file proves the lemmas needed to push
distinguishers through the reference extension used by the diamond norm:

* `extractBlock_localOp₁` — extracting a block after `localOp₁` is the channel
  applied to the extracted block.
* `localOp₁_qbind` — `localOp₁` commutes with Kleisli composition (`qbind`):
  applying-on-register-1 is functorial over sequencing.
* `prTrue_Q_localOp₁_kronecker` — on a product input state `ρ ⊗ σ`, the
  acceptance probability of `localOp₁ X` equals that of `X` on `ρ` scaled by
  `tr σ` (so `= prTrue_Q X ρ` when `σ` is a state).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.TensorProduct

open CatCrypt.Quantum
open scoped Matrix ComplexOrder ENNReal
open Matrix

variable {d₁ d₂ : ℕ} {α β : Type}

/-- Extracting the `(i₂, j₂)` block of `localOp₁ A` applied to `ρ` is `A`
applied to the `(i₂, j₂)` block of `ρ`. -/
theorem extractBlock_localOp₁ (A : QComp d₁ α) (hcp : ∀ a, IsCPMap (A.branch a))
    (a : α) (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i₂ j₂ : Fin d₂) :
    extractBlock ((localOp₁ (d₂ := d₂) A hcp).branch a ρ) i₂ j₂
      = A.branch a (extractBlock ρ i₂ j₂) := by
  ext i₁ j₁
  simp [extractBlock_apply, localOp₁, localOp₁_fun]

/-- Entrywise commutation of a (matrix-valued) `tsum`: the `(i,j)` entry of a
summable matrix series is the series of the `(i,j)` entries. Goes through the
`Pi.hasSum` structure of `Matrix` (which the bare `tsum_apply` cannot, since
`Matrix` is not a literal `Pi` at the application site). -/
theorem matrix_tsum_entry {n : ℕ} (N : α → Matrix (Fin n) (Fin n) ℂ)
    (hN : Summable N) (i j : Fin n) :
    (∑' a, N a) i j = ∑' a, N a i j :=
  (Pi.hasSum.mp (Pi.hasSum.mp hN.hasSum i) j).tsum_eq.symm

/-- Entry-apply form of `localOp₁` (proven while `localOp₁`/`localOp₁_fun` are
reducible, so callers can seal them with `local irreducible` and use this lemma
via `rw` instead of unfolding). -/
theorem localOp₁_branch_entry (A : QComp d₁ α) (hcp : ∀ a, IsCPMap (A.branch a))
    (a : α) (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (i j : Fin (d₁ * d₂)) :
    (localOp₁ (d₂ := d₂) A hcp).branch a ρ i j
      = (A.branch a (extractBlock ρ ((finProdEquiv d₁ d₂).symm i).2
            ((finProdEquiv d₁ d₂).symm j).2))
          ((finProdEquiv d₁ d₂).symm i).1 ((finProdEquiv d₁ d₂).symm j).1 := by
  simp [localOp₁, localOp₁_fun]

/-- `qbind`'s branch applied to a matrix, as a named lemma. -/
theorem qbind_branch_apply {d : ℕ} {γ δ : Type} (I : QComp d γ) (g : γ → QComp d δ)
    (c : δ) (M : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qbind I g).branch c M = ∑' a, (g a).branch c (I.branch a M) := rfl

attribute [local irreducible] localOp₁ localOp₁_fun QComp.qbind

-- The `local irreducible` lever curbs `whnf` descent into the block structure
-- during the summability `defeq`s; a heartbeat headroom bump is kept as well.
set_option maxHeartbeats 3200000 in
/-- `localOp₁` commutes with Kleisli composition (`qbind`): applying a channel on
register 1 is functorial over sequencing. -/
theorem localOp₁_qbind (A : QComp d₁ α) (f : α → QComp d₁ β)
    (hcpA : ∀ a, IsCPMap (A.branch a)) (hcpf : ∀ a b, IsCPMap ((f a).branch b))
    (hcpAf : ∀ b, IsCPMap ((QComp.qbind A f).branch b)) :
    localOp₁ (d₂ := d₂) (QComp.qbind A f) hcpAf
      = QComp.qbind (localOp₁ A hcpA) (fun a => localOp₁ (f a) (hcpf a)) := by
  apply QComp.ext_fun
  intro b ρ
  ext i j
  set i₁ := ((finProdEquiv d₁ d₂).symm i).1 with hi₁
  set i₂ := ((finProdEquiv d₁ d₂).symm i).2 with hi₂
  set j₁ := ((finProdEquiv d₁ d₂).symm j).1 with hj₁
  set j₂ := ((finProdEquiv d₁ d₂).symm j).2 with hj₂
  set M := extractBlock ρ i₂ j₂ with hM
  have hinj : Function.Injective (fun a : α => (a, b)) :=
    fun a a' h => (Prod.mk.injEq _ _ _ _).mp h |>.1
  have hsumm : Summable (fun a => (f a).branch b (A.branch a M)) :=
    Pi.summable.mpr fun p => Pi.summable.mpr fun q =>
      ((Pi.summable.mp (Pi.summable.mp (A.bind_uncurry_summable f M) p) q)).comp_injective hinj
  have hsumm' : Summable
      (fun a => (localOp₁ (f a) (hcpf a)).branch b ((localOp₁ A hcpA).branch a ρ)) :=
    Pi.summable.mpr fun p => Pi.summable.mpr fun q =>
      ((Pi.summable.mp (Pi.summable.mp ((localOp₁ A hcpA).bind_uncurry_summable
        (fun a => localOp₁ (f a) (hcpf a)) ρ) p) q)).comp_injective hinj
  -- LHS: localOp₁ of qbind, entry form → qbind sum → entrywise tsum.
  rw [localOp₁_branch_entry (QComp.qbind A f) hcpAf b ρ i j, ← hi₁, ← hi₂, ← hj₁, ← hj₂,
      ← hM, qbind_branch_apply, matrix_tsum_entry _ hsumm i₁ j₁]
  -- RHS: qbind sum → entrywise tsum → per-summand entry form + extractBlock_localOp₁.
  rw [qbind_branch_apply, matrix_tsum_entry _ hsumm' i j]
  refine tsum_congr (fun a => ?_)
  rw [localOp₁_branch_entry (f a) (hcpf a) b ((localOp₁ A hcpA).branch a ρ) i j,
      ← hi₁, ← hi₂, ← hj₁, ← hj₂, extractBlock_localOp₁ A hcpA a ρ i₂ j₂]

/-- On a product input `ρ ⊗ₖ σ`, the trace of a `localOp₁`-branch is the trace
of the register-1 channel scaled by `tr σ`. (So `= (X.branch a ρ).trace` when
`σ` is a state.) -/
theorem trace_localOp₁_branch_kronecker (X : QComp d₁ α)
    (hcp : ∀ a, IsCPMap (X.branch a)) (a : α)
    (ρ : Matrix (Fin d₁) (Fin d₁) ℂ) (σ : Matrix (Fin d₂) (Fin d₂) ℂ) :
    ((localOp₁ (d₂ := d₂) X hcp).branch a (ρ ⊗ₖ σ)).trace
      = (X.branch a ρ).trace * σ.trace := by
  rw [localOp₁_kronecker X hcp ρ σ a, trace_kronecker]

end CatCrypt.Quantum.TensorProduct

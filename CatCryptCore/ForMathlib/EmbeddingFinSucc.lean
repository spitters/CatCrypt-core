/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Sums over injective sequences

An injective sequence `Fin (k + 1) ↪ β` is an injective sequence `e : Fin k ↪ β` preceded by
an element outside the range of `e` (`Equiv.embeddingFinSucc`). This file records the
corresponding decomposition of a sum over `Fin (k + 1) ↪ β`, which is the sequential
description of drawing without replacement.

## Main results

* `Fintype.sum_embedding_fin_succ`:
  `∑ e' : Fin (k+1) ↪ β, F e' = ∑ e : Fin k ↪ β, ∑ x ∈ (univ.map e)ᶜ, F (Fin.cons x e)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Fintype

/-- A sum over the injective sequences of length `k + 1` decomposes as a sum over the
injective sequences `e` of length `k` and the elements `x` outside the range of `e`, the
sequence of length `k + 1` being `Fin.cons x e`. -/
theorem sum_embedding_fin_succ {β M : Type*} [Fintype β] [DecidableEq β] [AddCommMonoid M]
    {k : ℕ} (F : (Fin (k + 1) → β) → M) :
    ∑ e : Fin (k + 1) ↪ β, F e =
      ∑ e : Fin k ↪ β, ∑ x ∈ (Finset.univ.map e)ᶜ, F (Fin.cons x e) := by
  classical
  rw [← (Equiv.embeddingFinSucc k β).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Equiv.coe_embeddingFinSucc_symm]
  exact (Finset.sum_subtype (p := fun x => x ∉ Set.range e) _ (by simp)
    (fun x => F (Fin.cons x e))).symm

end Fintype

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.Code

/-!
# Dead uniform samples

A uniform sample whose result is not used can be removed: `SDistr.uniform α` has mass one, so
binding it to a constant continuation gives the continuation.

## Main results

* `CatCrypt.Relational.dead_sample` — `(SPComp.sample α).bind (fun _ => k) = k`
* `SPComp.sample_bind_sum`, `SPComp.sample_bind_sum_split` — the sum of independent uniform
  summands in an additive group is uniform, and independent of the summands off one index
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

/-- Dead sample: a uniform sample whose result is not used can be removed,
    `let _ ← sample α; k` = `k`. -/
@[simp] theorem dead_sample {α β : Type} [Fintype α] [Nonempty α] (k : SPComp β) :
    (SPComp.sample α).bind (fun _ => k) = k := by
  funext h
  simp only [SPComp.bind_def, SPComp.sample]
  rw [SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  exact SDistr.uniform_bind_const (k h)

end CatCrypt.Relational

namespace CatCrypt.Core.SPComp

/-- Sampling a vector of an additive group and passing on its sum and its entries off `j₀` is
sampling the sum and the entries off `j₀` independently. -/
theorem sample_bind_sum_split {ι Z β : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup Z]
    [Fintype Z] [Nonempty Z] (j₀ : ι) (F : Z → ({j // j ≠ j₀} → Z) → SPComp β) :
    SPComp.bind (SPComp.sample (ι → Z)) (fun ss => F (∑ j, ss j) (fun r => ss r)) =
      SPComp.bind (SPComp.sample Z) fun s =>
        SPComp.bind (SPComp.sample ({j // j ≠ j₀} → Z)) (F s) := by
  rw [← SPComp.sample_bind_equiv (Equiv.piSplitAt j₀ (fun _ => Z)).symm, SPComp.sample_prod_eq]
  have hsum : ∀ (z : Z) (r : {j // j ≠ j₀} → Z),
      ∑ j, (Equiv.piSplitAt j₀ (fun _ => Z)).symm (z, r) j = z + ∑ j, r j := by
    intro z r
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀]
    simp only [Equiv.piSplitAt_symm_apply, dite_true, add_right_inj]
    exact Finset.sum_congr rfl fun x _ => by simp [x.2]
  have hrest : ∀ (z : Z) (r : {j // j ≠ j₀} → Z),
      (fun i : {j // j ≠ j₀} => (Equiv.piSplitAt j₀ (fun _ => Z)).symm (z, r) i) = r := by
    intro z r
    funext i
    simp [i.2]
  simp only [SPComp.bind_assoc, SPComp.pure_bind, hsum, hrest]
  rw [SPComp.isPure_bind_comm _ _ _ (SPComp.sample_isPure _) (SPComp.sample_isPure _)]
  have h2 : ∀ r : {j // j ≠ j₀} → Z,
      SPComp.bind (SPComp.sample Z) (fun z => F (z + ∑ j, r j) r) =
        SPComp.bind (SPComp.sample Z) (fun s => F s r) := fun r =>
    SPComp.sample_bind_equiv (Equiv.addRight _) (fun s => F s r)
  simp only [h2]
  exact SPComp.isPure_bind_comm _ _ _ (SPComp.sample_isPure _) (SPComp.sample_isPure _)

/-- The sum of independent uniform summands in an additive group, one of them at index `j₀`, is
uniform. -/
theorem sample_bind_sum {ι Z β : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup Z]
    [Fintype Z] [Nonempty Z] (j₀ : ι) (F : Z → SPComp β) :
    SPComp.bind (SPComp.sample (ι → Z)) (fun ss => F (∑ j, ss j)) =
      SPComp.bind (SPComp.sample Z) F := by
  have h := sample_bind_sum_split j₀ (fun s (_ : {j // j ≠ j₀} → Z) => F s)
  rw [h]
  exact congrArg _ (funext fun s => CatCrypt.Relational.dead_sample (F s))

end CatCrypt.Core.SPComp

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.CodeSequence
public import CatCryptCore.Core.SPTree
public import CatCryptCore.Core.SPTreeTimedOps

/-!
# Computation trees and costed forms of `SPComp.seqFin`

The computation tree `SPComp.seqFin.tree` of the sequence `SPComp.seqFin n β g` of a family of
computation trees, its compile equation, its costed form and the erasure and time theorems of
the costed form. `derive_reduction` reflects a call `SPComp.seqFin n β g` (and `SPComp.seqVec`,
which unfolds to it) as the call of `SPComp.seqFin.tree` at the trees of the components, closed
by `SPComp.seqFin.compile_tree`; `derive_timed` prices it by `SPComp.seqFin.tree.timed`, whose
costed components are the costed forms of the components, with their step costs as the cost
companion; `derive_time_bound` bounds it by `SPComp.seqFin.tree.timeBound_timed`.

## Main definitions

* `SPComp.seqFin.tree` - the tree of a sequence of trees
* `SPComp.seqFin.tree.timed` - its costed form: each position costs one unit, the step cost
  of its tree and the time of the costed tree

## Main results

* `SPComp.seqFin.compile_tree` - the tree compiles to the sequence of the compiled trees
* `SPComp.seqFin.tree.erase_timed` - erasure of the costed form
* `SPComp.seqFin.tree.stepTime_timed_le` - the time is at most `∑ j, (1 + t j)` for bounds
  `t j` on the step cost and time of the tree at `j`
* `SPComp.seqFin.tree.timeBound_timed` - under uniform bounds `c` and `T`, the time is at
  most `n * (1 + (c + T))`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Core

namespace SPComp

/-- The computation tree of `seqFin n β g` for a family of trees `g`. -/
def seqFin.tree : (n : ℕ) → (β : Fin n → Type) → ((j : Fin n) → SPTree (β j)) →
    SPTree ((j : Fin n) → β j)
  | 0, _, _ => .ret fun j => j.elim0
  | n + 1, _, g =>
    (g 0).bind fun x => (seqFin.tree n _ fun j => g j.succ).bind fun xs => .ret (Fin.cons x xs)

/-- The tree of a sequence compiles to the sequence of the compiled trees. -/
theorem seqFin.compile_tree : ∀ (n : ℕ) (β : Fin n → Type) (g : (j : Fin n) → SPTree (β j)),
    (seqFin.tree n β g).compile = seqFin n β fun j => (g j).compile
  | 0, _, _ => rfl
  | n + 1, β, g => by
    simp only [seqFin.tree, seqFin_succ, SPTree.compile_bind, SPTree.compile_ret,
      seqFin.compile_tree n]

/-- The costed form of `seqFin.tree`: each position costs one unit, the step cost `gCost j` of
its tree and the time of the costed tree `g j`. -/
noncomputable def seqFin.tree.timed : (n : ℕ) → (β : Fin n → Type) →
    ((j : Fin n) → SPTree.Timed (β j)) → (Fin n → ℕ) → ℕ × SPTree.Timed ((j : Fin n) → β j)
  | 0, _, _, _ => (0, .ret fun j => j.elim0)
  | n + 1, _, g, gCost =>
    SPTree.Timed.delay (1 + gCost 0) ((g 0).bind fun x =>
      SPTree.Timed.delay (seqFin.tree.timed n _ (fun j => g j.succ) fun j => gCost j.succ).1
        ((seqFin.tree.timed n _ (fun j => g j.succ) fun j => gCost j.succ).2.bind
          fun xs => (0, .ret (Fin.cons x xs))))

/-- Erasure of the costed form of `seqFin.tree`. -/
theorem seqFin.tree.erase_timed : ∀ (n : ℕ) (β : Fin n → Type)
    (g : (j : Fin n) → SPTree.Timed (β j)) (gCost : Fin n → ℕ),
    (seqFin.tree.timed n β g gCost).2.erase = seqFin.tree n β fun j => (g j).erase
  | 0, _, _, _ => SPTree.Timed.erase_ret _
  | n + 1, β, g, gCost => by
    simp only [seqFin.tree.timed, seqFin.tree, SPTree.Timed.delay, SPTree.Timed.erase_bind,
      seqFin.tree.erase_timed n, SPTree.Timed.erase_ret]

/-- The time of a costed sequence is at most the sum over its positions of one plus a bound
`t j` on the step cost and the time of the tree at `j`. -/
theorem seqFin.tree.stepTime_timed_le : ∀ (n : ℕ) (β : Fin n → Type)
    (g : (j : Fin n) → SPTree.Timed (β j)) (gCost : Fin n → ℕ) (t : Fin n → ℕ),
    (∀ j, gCost j + (g j).time ≤ t j) →
    SPTree.Timed.stepTime (seqFin.tree.timed n β g gCost) ≤ ∑ j, (1 + t j)
  | 0, _, _, _, _, _ => by
    simp only [seqFin.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.time_ret]; omega
  | n + 1, β, g, gCost, t, h => by
    have ih := seqFin.tree.stepTime_timed_le n (fun j => β j.succ) (fun j => g j.succ)
      (fun j => gCost j.succ) (fun j => t j.succ) (fun j => h j.succ)
    let R := seqFin.tree.timed n _ (fun j => g j.succ) fun j => gCost j.succ
    have hb := SPTree.Timed.stepTime_bind_le (g 0)
      (fun x => SPTree.Timed.delay R.1 (R.2.bind fun xs =>
        ((0 : ℕ), SPTree.Timed.ret (Fin.cons x xs : (j : Fin (n + 1)) → β j))))
      (∑ j : Fin n, (1 + t j.succ)) fun x => by
        rw [SPTree.Timed.stepTime_delay]
        have := SPTree.Timed.stepTime_bind_le R.2
          (fun xs => ((0 : ℕ), SPTree.Timed.ret (Fin.cons x xs : (j : Fin (n + 1)) → β j))) 0
          (fun xs => by simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]; omega)
        simp only [SPTree.Timed.stepTime, R] at this ih ⊢
        omega
    rw [seqFin.tree.timed, SPTree.Timed.stepTime_delay, Fin.sum_univ_succ]
    have := h 0
    grind

/-- The time of a costed sequence of `n` trees, each of step cost at most `c` and time at most
`T`, is at most `n * (1 + (c + T))`. -/
theorem seqFin.tree.timeBound_timed (n : ℕ) (β : Fin n → Type)
    (g : (j : Fin n) → SPTree.Timed (β j)) (gCost : Fin n → ℕ) (c T : ℕ)
    (hc : ∀ j, gCost j ≤ c) (hT : ∀ j, (g j).time ≤ T) :
    SPTree.Timed.stepTime (seqFin.tree.timed n β g gCost) ≤ n * (1 + (c + T)) := by
  have := seqFin.tree.stepTime_timed_le n β g gCost (fun _ => c + T)
    fun j => Nat.add_le_add (hc j) (hT j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this

end SPComp

end CatCrypt.Core

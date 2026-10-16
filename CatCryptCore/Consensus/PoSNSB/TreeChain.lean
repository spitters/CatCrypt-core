/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Model

/-!
# PoS-NSB: valid chains and block trees

This file ports the facts about valid chains and block trees of `Properties/TreeChain.v`
of PoS-NSB (Thomsen and Spitters, CSF 2021) that the chain-growth proof uses, together with
the comparison lemmas for selected chains of `Properties/CG.v` (`subset_leq_chains`,
`leq_time_leq_chains`, `subset_leq_time_leq_chains`).

## Main results

* `valid_chain_starts_gb`: a valid chain contains the genesis block.
* `gb_in_all`: every block tree contains the genesis block.
* `all_build`: the blocks of `build_tree bp` are the genesis block and the blocks of `bp`.
* `valid_chain_ext`: a correct block linked to the head of a valid chain, with a larger
  slot, extends it to a valid chain.
* `subset_leq_time_leq_chains`: under the longest-chain rule, the selected chain of a tree
  with more blocks at a later slot is at least as long.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters

variable {Tx Hash Party : Type} [Parameters Party] [BlockParameters Tx Hash Party]

/-- The order `lt_slots` is transitive. -/
theorem lt_slots_trans {a b c : Block Tx Hash Party} (h1 : lt_slots a b) (h2 : lt_slots b c) :
    lt_slots a c :=
  Nat.lt_trans h2 h1

/-- A properly linked chain contains the genesis block. -/
theorem properly_linked_gb {c : Chain Tx Hash Party} (hl : properly_linked c) :
    GenesisBlock ∈ c := by
  induction c with
  | nil => exact hl.elim
  | cons b bs ih =>
    match bs, hl, ih with
    | [], hl, _ => simp [properly_linked] at hl; simp [hl]
    | b' :: bs', hl, ih => exact List.mem_cons_of_mem _ (ih hl.2)

/-- A valid chain contains the genesis block. -/
theorem valid_chain_starts_gb {c : Chain Tx Hash Party} (h : valid_chain c) :
    GenesisBlock ∈ c :=
  properly_linked_gb h.2.1

/-- A valid chain is nonempty. -/
theorem valid_chain_ne_nil {c : Chain Tx Hash Party} (h : valid_chain c) : c ≠ [] := by
  rintro rfl; exact h.2.1

/-- Extending a valid chain by a correct block that is linked to its head and has a larger
slot gives a valid chain. -/
theorem valid_chain_ext {b b' : Block Tx Hash Party} {c : Chain Tx Hash Party}
    (hc : valid_chain (b' :: c)) (hb : correct_block b) (hl : linked b b')
    (hs : lt_slots b b') : valid_chain (b :: b' :: c) := by
  obtain ⟨hcor, hpl, hdec⟩ := hc
  refine ⟨?_, ⟨hl, hpl⟩, ?_⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · exact hcor x hx
  · refine List.Pairwise.cons ?_ hdec
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hs
    · exact lt_slots_trans hs (List.rel_of_pairwise_cons hdec hx)

/-- A properly linked chain stays properly linked when its head is removed, unless it
becomes empty. -/
theorem properly_linked_tail {b : Block Tx Hash Party} {c : Chain Tx Hash Party}
    (h : properly_linked (b :: c)) (hc : c ≠ []) : properly_linked c := by
  cases c with
  | nil => exact absurd rfl hc
  | cons b' c => exact h.2

/-- A nonempty suffix of a valid chain is valid (`valid_chain_short_l`). -/
theorem valid_chain_short_l {c1 c2 : Chain Tx Hash Party} {b : Block Tx Hash Party}
    (h : valid_chain (c1 ++ b :: c2)) : valid_chain (b :: c2) := by
  obtain ⟨hcor, hpl, hdec⟩ := h
  refine ⟨fun x hx => hcor x (List.mem_append_right _ hx), ?_,
    (List.pairwise_append.1 hdec).2.1⟩
  induction c1 with
  | nil => exact hpl
  | cons x c1 ih =>
    exact ih (fun y hy => hcor y (List.mem_cons_of_mem _ hy))
      (properly_linked_tail hpl (by simp)) (List.pairwise_cons.1 hdec).2

/-- The tail of a valid chain is valid, unless it is empty. -/
theorem valid_chain_tail {b : Block Tx Hash Party} {c : Chain Tx Hash Party}
    (h : valid_chain (b :: c)) (hc : c ≠ []) : valid_chain c := by
  obtain ⟨b', c', rfl⟩ := List.exists_cons_of_ne_nil hc
  exact valid_chain_short_l (c1 := [b]) h

/-- In a valid chain, the genesis block is the last block: a valid chain that starts with
the genesis block is the chain of the genesis block alone. -/
theorem valid_chain_gb_head {c : Chain Tx Hash Party} (h : valid_chain (GenesisBlock :: c)) :
    c = [] := by
  by_contra hc
  have hgb := valid_chain_starts_gb (valid_chain_tail h hc)
  have := List.rel_of_pairwise_cons h.2.2 hgb
  exact lt_irrefl _ this

/-- A valid chain of one block is the chain of the genesis block. -/
theorem valid_chain_single {b : Block Tx Hash Party} (h : valid_chain [b]) :
    b = GenesisBlock :=
  h.2.1

/-- A valid chain whose blocks have slots at most the slot of the genesis block is the chain
of the genesis block alone. -/
theorem valid_chain_le_gb {c : Chain Tx Hash Party} (h : valid_chain c)
    (hs : ∀ b ∈ c, b.sl ≤ (GenesisBlock : Block Tx Hash Party).sl) : c = [GenesisBlock] := by
  obtain ⟨b, c', rfl⟩ := List.exists_cons_of_ne_nil (valid_chain_ne_nil h)
  by_cases hc : c' = []
  · subst hc; rw [valid_chain_single h]
  · have hgb := valid_chain_starts_gb (valid_chain_tail h hc)
    have h1 : lt_slots b GenesisBlock := List.rel_of_pairwise_cons h.2.2 hgb
    have h2 := hs b List.mem_cons_self
    simp only [lt_slots] at h1
    omega

/-- The blocks of a selected chain have slots at most the slot of the selection
(`best_chain_time`). -/
theorem best_chain_time (tT : TreeType Tx Hash Party) (t : tT.T) (s : Slot) :
    ∀ b ∈ tT.bestChain s t, b.sl ≤ s := fun b hb => by
  have := tT.best_chain_in_all s t b hb
  simp only [List.mem_filter, decide_eq_true_eq] at this
  exact this.2

/-- Every block tree contains the genesis block. -/
theorem gb_in_all (tT : TreeType Tx Hash Party) (t : tT.T) :
    GenesisBlock ∈ tT.allBlocks t := by
  have h := tT.best_chain_in_all 0 t _ (valid_chain_starts_gb (tT.best_chain_valid t 0))
  exact (List.mem_filter.1 h).1

/-- The tree obtained by adding the blocks of a pool to the initial tree. -/
def build_tree (tT : TreeType Tx Hash Party) (bp : BlockPool Tx Hash Party) : tT.T :=
  bp.foldr (fun b t => tT.extendTree t b) tT.tree0

/-- The blocks of `build_tree bp` are the genesis block and the blocks of `bp`. -/
theorem all_build (tT : TreeType Tx Hash Party) (bp : BlockPool Tx Hash Party)
    (b : Block Tx Hash Party) :
    b ∈ tT.allBlocks (build_tree tT bp) ↔ b ∈ GenesisBlock :: bp := by
  induction bp with
  | nil => simpa [build_tree] using tT.all_tree0 b
  | cons b' bp ih =>
    have := tT.all_extend (build_tree tT bp) b' b
    simp only [build_tree, List.foldr_cons] at this ⊢
    rw [this]
    simp only [build_tree] at ih
    simp only [List.mem_append, ih, List.mem_cons, List.not_mem_nil, or_false]
    tauto

/-- Under the longest-chain rule for `tT'`: if every block of `t` is a block of `t'` and
`s ≤ s'`, the chain selected in `t` at slot `s` is at most as long as the chain selected in
`t'` at slot `s'`. -/
theorem subset_leq_time_leq_chains {tT tT' : TreeType Tx Hash Party}
    (hL : tT'.LongestChainRule) {t : tT.T} {t' : tT'.T} {s s' : Slot}
    (hsub : ∀ b, b ∈ tT.allBlocks t → b ∈ tT'.allBlocks t') (hs : s ≤ s') :
    (tT.bestChain s t).length ≤ (tT'.bestChain s' t').length := by
  refine hL _ s' t' (tT.best_chain_valid t s) fun b hb => ?_
  have := tT.best_chain_in_all s t b hb
  simp only [List.mem_filter, decide_eq_true_eq] at this ⊢
  exact ⟨hsub b this.1, this.2.trans hs⟩

/-- Under the longest-chain rule, a tree with more blocks selects a chain at least as
long. -/
theorem subset_leq_chains {tT tT' : TreeType Tx Hash Party}
    (hL : tT'.LongestChainRule) {t : tT.T} {t' : tT'.T} (s : Slot)
    (hsub : ∀ b, b ∈ tT.allBlocks t → b ∈ tT'.allBlocks t') :
    (tT.bestChain s t).length ≤ (tT'.bestChain s t').length :=
  subset_leq_time_leq_chains hL hsub le_rfl

/-- Under the longest-chain rule, the selected chain of a tree grows with the slot. -/
theorem leq_time_leq_chains {tT : TreeType Tx Hash Party} (hL : tT.LongestChainRule)
    (t : tT.T) {s s' : Slot} (hs : s ≤ s') :
    (tT.bestChain s t).length ≤ (tT.bestChain s' t).length :=
  subset_leq_time_leq_chains hL (fun _ h => h) hs

end CatCryptCore.Consensus.PoSNSB

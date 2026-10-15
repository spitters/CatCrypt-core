/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Invariants

/-!
# PoS-NSB: chain growth

This file ports the chain-growth theorem of `Properties/CG.v` of PoS-NSB (Thomsen and
Spitters, *Formalizing Nakamoto-style proof of stake*, CSF 2021). The honest tree chain of a
state is the chain that the chain-selection rule picks in the tree of all blocks held by
honest parties. Chain growth says that between two states of an execution, the honest tree
chain grows by at least the number of slots in between that have an honest slot leader.

The slot condition is a parameter: `chain_growth_gen` counts the slots satisfying any
predicate `Q` on slots that implies an honest slot leader, and `chain_growth_charString`
counts the slots whose letter in the characteristic string satisfies a pattern `P` that
implies at least one honest leader. The Coq statement `chain_growth` is the instance
`Q = lucky_slot`.

The theorems assume, as in the Coq development:
* `hu`: the initial parties are distinct (`PartiesUniq`);
* `hL`: the tree type `Tree` of the honest tree follows the longest-chain rule;
* `hLmap`: the tree type of every party follows the longest-chain rule (in Coq this is part
  of every tree type).

The Coq axioms `NonEmptyHonestParties`, `HonestGB`, `GenesisSlot` and `GenesisWin` are not
needed for chain growth.

## Main results

* `extending_own_chain`: an honest slot leader extends its own best chain by one block.
* `chain_growth_lucky_slot`: across a slot with an honest leader, the honest tree chain
  grows by at least one block.
* `slot_in_between`: an execution passes through the start of every slot in between.
* `chain_growth_gen`, `chain_growth`, `chain_growth_charString`: chain growth.
* `chain_growth_parties`: chain growth for the chains of two honest parties.

## Proof structure

The proof follows the Coq development. The final induction differs: instead of locating the
first slot with an honest leader (`first_lucky_slot`, `world_in_between`), it inducts on the
number of slots between the two states and splits off the first slot.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-! ## Slots with an honest leader -/

/-- Some party of `ps` is an honest leader of slot `sl`. -/
def lucky_slot_gen (ps : List Party) (sl : Slot) : Bool :=
  ps.any (fun p => Winner p sl && is_honest p)

/-- Some initial party is an honest leader of slot `sl`. -/
def lucky_slot (sl : Slot) : Bool := lucky_slot_gen (InitParties : List Party) sl

/-- The current slot of `N` has an honest leader. -/
def lucky_slot_w (N : GlobalState Tx Hash Party AdvState) : Bool :=
  lucky_slot_gen (InitParties : List Party) N.t_now

/-- The slots `a, a + 1, …, b - 1`. -/
def nat_range (a b : ℕ) : List ℕ := List.range' a (b - a)

/-- The slots in `[a, b)` that satisfy `P`. -/
def p_slots_range (P : Slot → Bool) (a b : ℕ) : List Slot := (nat_range a b).filter P

/-- The slots in `[a, b)` with an honest leader. -/
def lucky_slots_range (a b : ℕ) : List Slot := p_slots_range (lucky_slot (Party := Party)) a b

/-- The slots with an honest leader from the slot of `N` up to the slot of `N'`, excluded. -/
def lucky_slots_worlds (N N' : GlobalState Tx Hash Party AdvState) : List Slot :=
  lucky_slots_range (Party := Party) N.t_now N'.t_now

/-- The honest tree chain: the chain selected in the honest tree at the previous slot. -/
def honest_tree_chain (Tree : TreeType Tx Hash Party) (N : GlobalState Tx Hash Party AdvState) :
    Chain Tx Hash Party :=
  Tree.bestChain (N.t_now - 1) (honest_tree Tree N)

theorem lucky_slot_iff_charString [Fintype Party] (sl : Slot) :
    lucky_slot (Party := Party) sl = true ↔ 0 < (charString (Party := Party) sl).honest := by
  simp [lucky_slot, lucky_slot_gen, charString, List.countP_pos_iff]

/-! ## Growth of the honest tree chain -/

/-- The honest tree chain does not shrink along an execution
(`monotone_growth_honest_chain`). -/
theorem monotone_growth_honest_chain {Tree : TreeType Tx Hash Party} (hL : Tree.LongestChainRule)
    {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') :
    (honest_tree_chain Tree N).length ≤ (honest_tree_chain Tree N').length := by
  have := monotone_time h
  exact subset_leq_time_leq_chains hL (monotone_honest_tree Tree h) (by omega)

/-- An honest slot leader of slot `sl > 0` extends its best chain at slot `sl - 1` by one
block: the best chain of its new tree at slot `sl` is longer (`extending_own_chain`). -/
theorem extending_own_chain {l : LocalState Tx Hash Party} (hL : l.tT.LongestChainRule)
    {sl : Slot} (ht : 0 < sl) (hw : Winner l.pk sl = true) (txs : Tx) :
    (l.tT.bestChain (sl - 1) l.tree).length <
      ((honest_bake sl txs l).2.tT.bestChain sl (honest_bake sl txs l).2.tree).length := by
  rw [honest_bake_eq, if_pos hw]
  simp only [extend_tree_l]
  set c := l.tT.bestChain (sl - 1) l.tree with hc
  have hval := l.tT.best_chain_valid l.tree (sl - 1)
  rw [← hc] at hval
  obtain ⟨b, c', hbc⟩ : ∃ b c', c = b :: c' := by
    cases h : c with
    | nil => exact absurd h (valid_chain_ne_nil hval)
    | cons b c' => exact ⟨b, c', rfl⟩
  set nb : Block Tx Hash Party := ⟨sl, txs, HashB (c.headD GenesisBlock), l.pk⟩ with hnb
  have hin : ∀ x ∈ c, x ∈ l.tT.allBlocks l.tree ∧ x.sl ≤ sl - 1 := fun x hx => by
    have := l.tT.best_chain_in_all (sl - 1) l.tree x hx
    simpa using this
  have hbsl := (hin b (by simp [hbc])).2
  have hvalid : valid_chain (nb :: c) := by
    rw [hbc] at hval ⊢
    refine valid_chain_ext hval hw ?_ ?_
    · simp [linked, hnb, hbc]
    · simp only [lt_slots, hnb]; omega
  have := hL (nb :: c) sl (l.tT.extendTree l.tree nb) hvalid fun x hx => by
    simp only [List.mem_filter, decide_eq_true_eq]
    rw [l.tT.all_extend]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨by simp, le_rfl⟩
    · exact ⟨List.mem_append_left _ (hin x hx).1, by have := (hin x hx).2; omega⟩
  simp only [List.length_cons] at this
  omega

/-- The longest-chain rule for the tree type of a local state of a reachable state. -/
theorem Inv.longest {N : GlobalState Tx Hash Party AdvState} (hN : Inv N)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    {p : Party} {l : LocalState Tx Hash Party} (hl : N.state_map p = some l) :
    l.tT.LongestChainRule :=
  (hN.tT p l hl) ▸ hLmap p

theorem honest_tree_perm_step {Tree : TreeType Tx Hash Party} (hL : Tree.LongestChainRule)
    {M N : GlobalState Tx Hash Party AdvState} (h : M ⤳ N) (hph : phase N = phase M) (s : Slot) :
    (Tree.bestChain s (honest_tree Tree M)).length ≤ (Tree.bestChain s (honest_tree Tree N)).length :=
  subset_leq_chains hL s fun b hb =>
    (honest_tree_preservation Tree (Relation.ReflTransGen.single h) hph b).1 hb

/-- Across the delivery and baking of a slot with an honest leader, the chain selected in
the honest tree grows by at least one block (`chain_growth_lucky_slot_ready_baked`). -/
theorem chain_growth_lucky_slot_ready_baked (hu : (InitParties : List Party).Nodup)
    {Tree : TreeType Tx Hash Party} (hL : Tree.LongestChainRule)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    {N_R N_B : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N_R) (hRB : N_R ⇓ N_B)
    (ht : N_B.t_now = N_R.t_now) (hready : N_R.progress = .Ready)
    (hbaked : N_B.progress = .Baked) (hlucky : lucky_slot_w N_R = true) :
    (Tree.bestChain (N_R.t_now - 1) (honest_tree Tree N_R)).length <
      (Tree.bestChain N_B.t_now (honest_tree Tree N_B)).length := by
  induction hRB with
  | refl => simp [hready] at hbaked
  | tail hRM hs ih =>
    rename_i M N2
    have hR' := Relation.ReflTransGen.trans hR hRM
    have hN := reachable_inv hR'
    cases hs with
    | Bake hp =>
      have hF := bakes_step_facts M M.exec_order
      have htM : M.t_now = N_R.t_now := by rw [← hF.time]; exact ht
      obtain ⟨p, hpI, hpw⟩ := List.any_eq_true.1 hlucky
      simp only [Bool.and_eq_true] at hpw
      obtain ⟨hw, hh⟩ := hpw
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 ((hN.state_init p).2 hpI)
      have hpo := hN.mem_order hk
      have hLk := hN.longest hLmap hk
      have h1 : (Tree.bestChain (N_R.t_now - 1) (honest_tree Tree N_R)).length ≤
          (k.tT.bestChain (M.t_now - 1) k.tree).length := by
        rw [htM]
        exact subset_leq_chains hLk _ (honest_tree_subset hu Tree hR hready hRM hp htM hh hk)
      have hpk : k.pk = p := hN.pk p k hk
      have h2 := extending_own_chain (txs := TxSelection (Hash := Hash) (AdvState := AdvState)
        M.t_now p) hLk (sl := M.t_now) hN.time (by rw [hpk, htM]; exact hw)
      have hown := bakes_own M (uniq_exec_order hu hN) hpo hh hk
      refine lt_of_lt_of_le (lt_of_le_of_lt h1 h2) (subset_leq_time_leq_chains hL ?_ ?_)
      · intro b hb
        rw [mem_honest_tree]
        exact Or.inr ⟨p, by simpa [hF.order] using hpo, hh, _, hown, hb⟩
      · exact le_of_eq hF.time.symm
    | Deliver hp => simp at hbaked
    | NextRound hp => simp at hbaked
    | PermParties ps hps =>
      exact lt_of_lt_of_le (ih ht hbaked) (honest_tree_perm_step hL (.PermParties _ ps hps) rfl _)
    | PermMsgs mb hmb =>
      exact lt_of_lt_of_le (ih ht hbaked) (honest_tree_perm_step hL (.PermMsgs _ mb hmb) rfl _)

/-- Across a slot with an honest leader, from the start of the slot to the start of the next
slot, the honest tree chain grows by at least one block (`chain_growth_lucky_slot`). -/
theorem chain_growth_lucky_slot (hu : (InitParties : List Party).Nodup)
    {Tree : TreeType Tx Hash Party} (hL : Tree.LongestChainRule)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    {N_R N_R' : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N_R) (hRR : N_R ⇓ N_R')
    (ht : N_R'.t_now = N_R.t_now + 1) (hready : N_R.progress = .Ready)
    (hready' : N_R'.progress = .Ready) (hlucky : lucky_slot_w N_R = true) :
    (honest_tree_chain Tree N_R).length < (honest_tree_chain Tree N_R').length := by
  induction hRR with
  | refl => omega
  | tail hRM hs ih =>
    rename_i M N2
    cases hs with
    | NextRound hp =>
      simp only [inc_round, round_tick] at ht
      have h1 := chain_growth_lucky_slot_ready_baked hu hL hLmap hR hRM (by omega) hready hp
        hlucky (Tree := Tree)
      have h2 : (Tree.bestChain M.t_now (honest_tree Tree M)).length ≤
          (honest_tree_chain Tree { inc_round (round_tick M) with progress := .Ready }).length :=
        subset_leq_time_leq_chains hL (fun b hb => by
          rw [mem_honest_tree] at hb ⊢; simpa [inc_round, round_tick] using hb)
          (by simp [inc_round, round_tick])
      exact lt_of_lt_of_le h1 h2
    | Deliver hp => simp at hready'
    | Bake hp => simp at hready'
    | PermParties ps hps =>
      exact lt_of_lt_of_le (ih ht hready')
        (honest_tree_perm_step hL (.PermParties _ ps hps) rfl _)
    | PermMsgs mb hmb =>
      exact lt_of_lt_of_le (ih ht hready')
        (honest_tree_perm_step hL (.PermMsgs _ mb hmb) rfl _)

/-! ## Intermediate states -/

/-- An execution passes through every phase in between (each step advances the phase by at
most one). -/
theorem phase_in_between {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') (k : ℕ)
    (hk : phase N ≤ k) (hk' : k ≤ phase N') :
    ∃ M, phase M = k ∧ N ⇓ M ∧ M ⇓ N' := by
  induction h with
  | refl => exact ⟨N, by omega, .refl, .refl⟩
  | tail hNM hs ih =>
    rename_i M N2
    rcases step_phase hs with h | ⟨h, -⟩
    · by_cases hkM : k ≤ phase M
      · obtain ⟨M', h1, h2, h3⟩ := ih hkM
        exact ⟨M', h1, h2, h3.tail hs⟩
      · exact ⟨N2, by omega, hNM.tail hs, .refl⟩
    · obtain ⟨M', h1, h2, h3⟩ := ih (by omega)
      exact ⟨M', h1, h2, h3.tail hs⟩

theorem phase_ready {M : GlobalState Tx Hash Party AdvState} {sl : Slot} (h : phase M = 3 * sl) :
    M.progress = .Ready ∧ M.t_now = sl := by
  unfold phase at h
  split at h
  · rename_i hp; exact ⟨hp, by omega⟩
  all_goals omega

theorem phase_delivered {M : GlobalState Tx Hash Party AdvState} {sl : Slot}
    (h : phase M = 3 * sl + 1) : M.progress = .Delivered ∧ M.t_now = sl := by
  unfold phase at h
  split at h
  · omega
  · rename_i hp; exact ⟨hp, by omega⟩
  · omega

/-- An execution from the start of a slot passes through the start of every later slot up to
its end (`slot_in_between`). -/
theorem slot_in_between {N N' : GlobalState Tx Hash Party AdvState}
    (hready : N.progress = .Ready) (h : N ⇓ N') {sl : Slot} (h1 : N.t_now ≤ sl)
    (h2 : sl ≤ N'.t_now) :
    ∃ N'', N''.progress = .Ready ∧ N''.t_now = sl ∧ N ⇓ N'' ∧ N'' ⇓ N' := by
  have e : phase N = 3 * N.t_now := by simp [phase, hready]
  obtain ⟨M, hM, h3, h4⟩ := phase_in_between h (3 * sl) (by omega) (by have := le_phase N'; omega)
  obtain ⟨hp, ht⟩ := phase_ready hM
  exact ⟨M, hp, ht, h3, h4⟩

/-- The honest tree at the start of a slot is contained in the tree of every honest party in
every state of a later slot (`honest_tree_subset_ext`). -/
theorem honest_tree_subset_ext (hu : (InitParties : List Party).Nodup) (Tree : TreeType Tx Hash Party)
    {N N' : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N)
    (hready : N.progress = .Ready) (h : N ⇓ N') (ht : N.t_now < N'.t_now) {p : Party}
    (hh : is_honest p = true) {l : LocalState Tx Hash Party} (hl : N'.state_map p = some l) :
    ∀ b ∈ Tree.allBlocks (honest_tree Tree N), b ∈ l.blocks := by
  have e : phase N = 3 * N.t_now := by simp [phase, hready]
  obtain ⟨M, hM, h3, h4⟩ := phase_in_between h (3 * N.t_now + 1) (by omega)
    (by have := le_phase N'; omega)
  obtain ⟨hp, htM⟩ := phase_delivered hM
  obtain ⟨k, hk, hsub⟩ := (monotone_tree h4).1 p l hl
  intro b hb
  exact hsub b (honest_tree_subset hu Tree hR hready h3 hp htM hh hk b hb)

/-! ## Chain growth -/

theorem nat_range_succ (a d : ℕ) : nat_range a (a + (d + 1)) = a :: nat_range (a + 1) (a + 1 + d) := by
  simp only [nat_range]
  rw [show a + (d + 1) - a = d + 1 by omega, show a + 1 + d - (a + 1) = d by omega]
  rfl

/-- Chain growth for a slot condition `Q` that implies an honest leader: from a reachable
state at the start of a slot to any later state, the honest tree chain grows by at least the
number of slots in between that satisfy `Q`. -/
theorem chain_growth_gen (hu : (InitParties : List Party).Nodup)
    {Tree : TreeType Tx Hash Party} (hL : Tree.LongestChainRule)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (Q : Slot → Bool) (hQ : ∀ sl, Q sl = true → lucky_slot (Party := Party) sl = true)
    (w : ℕ) {N N' : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (h : N ⇓ N')
    (hready : N.progress = .Ready) (hw : w ≤ (p_slots_range Q N.t_now N'.t_now).length) :
    (honest_tree_chain Tree N).length + w ≤ (honest_tree_chain Tree N').length := by
  obtain ⟨d, hd⟩ : ∃ d, N'.t_now = N.t_now + d := ⟨N'.t_now - N.t_now, by
    have := monotone_time h; omega⟩
  induction d generalizing N w with
  | zero =>
    have : w = 0 := by simpa [p_slots_range, nat_range, hd] using hw
    subst this
    simpa using monotone_growth_honest_chain hL h
  | succ d ih =>
    obtain ⟨M, hMr, hMt, hNM, hMN'⟩ := slot_in_between hready h (sl := N.t_now + 1) (by omega)
      (by omega)
    have hRM := Relation.ReflTransGen.trans hR hNM
    have ih' := ih (hRM) hMN' hMr (w := w - (if Q N.t_now then 1 else 0))
    have hrange : p_slots_range Q N.t_now N'.t_now =
        (if Q N.t_now then [N.t_now] else []) ++ p_slots_range Q M.t_now N'.t_now := by
      rw [p_slots_range, p_slots_range, hd, nat_range_succ, hMt,
        show N.t_now + (d + 1) = N.t_now + 1 + d by omega]
      by_cases hq : Q N.t_now <;> simp [hq]
    rw [hrange, List.length_append] at hw
    by_cases hq : Q N.t_now
    · simp only [hq, if_true, List.length_singleton] at hw ih'
      have h1 := chain_growth_lucky_slot hu hL hLmap hR hNM hMt hready hMr (hQ _ hq)
        (Tree := Tree)
      have h2 := ih' (by omega) (by omega)
      omega
    · simp only [hq, Bool.false_eq_true, if_false, List.length_nil, Nat.sub_zero] at hw ih'
      have h1 := monotone_growth_honest_chain hL hNM (Tree := Tree)
      have h2 := ih' (by omega) (by omega)
      omega

/-- Chain growth (`chain_growth` of `Properties/CG.v`): from a reachable state at the start of
a slot to any later state, the honest tree chain grows by at least the number of slots in
between that have an honest leader. -/
theorem chain_growth (hu : (InitParties : List Party).Nodup)
    {Tree : TreeType Tx Hash Party} (hL : Tree.LongestChainRule)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (w : ℕ) {N N' : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (h : N ⇓ N')
    (hready : N.progress = .Ready) (hw : w ≤ (lucky_slots_worlds N N').length) :
    (honest_tree_chain Tree N).length + w ≤ (honest_tree_chain Tree N').length :=
  chain_growth_gen hu hL hLmap lucky_slot (fun _ h => h) w hR h hready hw

/-- Chain growth over the characteristic string: for a slot pattern `P` on letters of the
characteristic string that implies at least one honest leader, the honest tree chain grows
by at least the number of slots in between whose letter satisfies `P`. -/
theorem chain_growth_charString [Fintype Party] (hu : (InitParties : List Party).Nodup)
    {Tree : TreeType Tx Hash Party} (hL : Tree.LongestChainRule)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (P : SlotLetter → Bool) (hP : ∀ x, P x = true → 0 < x.honest)
    (w : ℕ) {N N' : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (h : N ⇓ N')
    (hready : N.progress = .Ready)
    (hw : w ≤ (p_slots_range (fun sl => P (charString (Party := Party) sl)) N.t_now N'.t_now).length) :
    (honest_tree_chain Tree N).length + w ≤ (honest_tree_chain Tree N').length :=
  chain_growth_gen hu hL hLmap _ (fun sl h => (lucky_slot_iff_charString sl).2 (hP _ h)) w hR h
    hready hw

/-- Chain growth for honest parties (`chain_growth_parties`): if honest `p1` holds `l1` at the
start of a slot and honest `p2` holds `l2` in a later slot, the best chain of `p2` at the slot
before its current one exceeds the best chain of `p1` at the slot before its current one by
at least the number of slots with an honest leader from the slot of the first state up to,
excluded, the slot before the second. -/
theorem chain_growth_parties (hu : (InitParties : List Party).Nodup)
    {Tree : TreeType Tx Hash Party} (hL : Tree.LongestChainRule)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (w : ℕ) {N N' : GlobalState Tx Hash Party AdvState} {p1 p2 : Party}
    {l1 l2 : LocalState Tx Hash Party} (hR : N0 AdvState ⇓ N) (h : N ⇓ N')
    (ht : N.t_now < N'.t_now) (hready : N.progress = .Ready)
    (hh1 : is_honest p1 = true) (hh2 : is_honest p2 = true)
    (hl1 : N.state_map p1 = some l1) (hl2 : N'.state_map p2 = some l2)
    (hw : w ≤ (lucky_slots_range (Party := Party) N.t_now (N'.t_now - 1)).length) :
    (l1.tT.bestChain (N.t_now - 1) l1.tree).length + w ≤
      (l2.tT.bestChain (N'.t_now - 1) l2.tree).length := by
  have hN := reachable_inv hR
  have hN' := reachable_inv (hR.trans h)
  obtain ⟨N2, hp2, ht2, h12, h23⟩ := slot_in_between hready h (sl := N'.t_now - 1) (by omega)
    (by omega)
  have hR2 := hR.trans h12
  have h1 : (l1.tT.bestChain (N.t_now - 1) l1.tree).length ≤
      (honest_tree_chain Tree N).length :=
    subset_leq_chains hL _ fun b hb => (mem_honest_tree Tree N b).2
      (Or.inr ⟨p1, hN.mem_order hl1, hh1, l1, hl1, hb⟩)
  have h2 := chain_growth hu hL hLmap w hR h12 hready (Tree := Tree)
    (by simpa [lucky_slots_worlds, ht2] using hw)
  have h3 : (honest_tree_chain Tree N2).length ≤ (l2.tT.bestChain (N'.t_now - 1) l2.tree).length :=
    subset_leq_time_leq_chains (hN'.longest hLmap hl2)
      (honest_tree_subset_ext hu Tree hR2 hp2 h23 (by omega) hh2 hl2) (by omega)
  omega

end CatCryptCore.Consensus.PoSNSB

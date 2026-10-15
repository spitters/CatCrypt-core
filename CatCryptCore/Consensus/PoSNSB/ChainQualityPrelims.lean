/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.ChainGrowth

/-!
# PoS-NSB: preliminaries of chain quality

This file ports the first part of `Properties/CQ.v` of PoS-NSB (Thomsen and Spitters,
*Formalizing Nakamoto-style proof of stake*, CSF 2021), together with the definitions
`block_history`, `honest_block` and `honest_subset` of `Properties/CG.v`: the forging-freedom
assumption on the adversary, the history of broadcast blocks, and the facts about honest
blocks in the history that the chain-quality proof uses.

The adversary cannot forge the signature of an honest party. As in the Coq development, this
is the hypothesis `forging_free N`: whenever, on the way to `N`, the adversary sends messages
for a corrupt party, the honest blocks among them were already broadcast.

## Main results

* `no_premature_honest_blocks`, `no_premature_honest_blocks_R`,
  `no_premature_honest_blocks_D`: an honest block in the history has a slot at most the
  current slot, and smaller than the current slot outside the baking phase.
* `honest_block_preserved_phase`, `honest_blocks_below_slot_preserved`: honest blocks of a
  past slot that are in the history of a later state were already in the history.
* `reachable_hist_inv`: in a reachable state, every message in transit has been broadcast
  and every block of a local tree is the genesis block or a broadcast block
  (`buff_history_subset`, `honest_tree_hist_gb_subset`).
* `eq_head_eq_chains`: without hash collisions, two valid chains of broadcast blocks with the
  same head are equal.
* `bc_ext_max_increase`: under the longest-chain rule, adding a block of slot `t` lengthens
  the chain selected at slot `t` by at most one block over the chain selected at `t - 1`.

## Departures from the Coq development

* `honest_subset s1 s2` states that every honest block of `s1` is in `s2`, which is
  equivalent to the Coq inclusion of the honest blocks of `s1` in the honest blocks of `s2`.
* The Coq lemma `honest_blocks_below_slot_preserved` is derived from
  `honest_block_preserved_phase`, which also covers the honest blocks of the current slot
  once the baking phase is over; the backward reasoning of `honest_block_state` in
  `Properties/CQ.v` is replaced by this lemma (see `ChainQuality.lean`).
* `buff_history_subset` and `not_gb_honest_tree_history_subset` are fields of the
  invariant `HistInv`, which covers the trees of all parties, not only the honest tree.
* `eq_head_eq_chains` and `bc_ext_max_increase` do not use the axiom `GenesisSlot`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-! ## Honest blocks and the block history (`Properties/CG.v`) -/

/-- The blocks of all messages broadcast so far. -/
def block_history (N : GlobalState Tx Hash Party AdvState) : List (Block Tx Hash Party) :=
  N.history.map get_block

/-- A block baked by an honest party. -/
def honest_block (b : Block Tx Hash Party) : Bool := is_honest b.bid

/-- A block baked by a corrupt party. -/
def corrupt_block (b : Block Tx Hash Party) : Bool := is_corrupt b.bid

/-- The honest blocks of a chain. -/
def honest_blocks (c : Chain Tx Hash Party) : Chain Tx Hash Party := c.filter honest_block

/-- Every honest block of `s1` is in `s2`. -/
def honest_subset (s1 s2 : List (Block Tx Hash Party)) : Prop :=
  ∀ b ∈ s1, honest_block b = true → b ∈ s2

/-- The honest blocks of the history. -/
def honest_block_hist (N : GlobalState Tx Hash Party AdvState) : List (Block Tx Hash Party) :=
  (block_history N).filter honest_block

/-- The genesis block followed by the block history. -/
def block_hist_gb (N : GlobalState Tx Hash Party AdvState) : List (Block Tx Hash Party) :=
  GenesisBlock :: block_history N

/-- The hash function is injective on the genesis block and the broadcast blocks. -/
def collision_free (N : GlobalState Tx Hash Party AdvState) : Prop :=
  ∀ b ∈ block_hist_gb N, ∀ b' ∈ block_hist_gb N, HashB b = HashB b' → b = b'

/-! ## Forging freedom -/

/-- The states from which `N2` is reached by part of a delivery phase followed by an
execution. -/
inductive DeliverySteps : GlobalState Tx Hash Party AdvState → GlobalState Tx Hash Party AdvState →
    Prop where
  | RefineStepR {N1 N2 : GlobalState Tx Hash Party AdvState} : N1 ⇓ N2 → DeliverySteps N1 N2
  | ProgressR {N1 N2 : GlobalState Tx Hash Party AdvState} :
      DeliverySteps { N1 with progress := .Delivered } N2 → DeliverySteps N1 N2
  | RcvStep {N1 N2 : GlobalState Tx Hash Party AdvState} (p : Party) :
      DeliverySteps (party_rcv_step_world p N1) N2 → DeliverySteps N1 N2

/-- The states from which `N2` is reached by part of a baking phase followed by an
execution. -/
inductive BakingSteps : GlobalState Tx Hash Party AdvState → GlobalState Tx Hash Party AdvState →
    Prop where
  | RefineStepB {N1 N2 : GlobalState Tx Hash Party AdvState} : N1 ⇓ N2 → BakingSteps N1 N2
  | ProgressB {N1 N2 : GlobalState Tx Hash Party AdvState} :
      BakingSteps { N1 with progress := .Baked } N2 → BakingSteps N1 N2
  | BakeStep {N1 N2 : GlobalState Tx Hash Party AdvState} (p : Party) :
      BakingSteps (party_bake_step_world p N1) N2 → BakingSteps N1 N2

theorem delivery_steps_refl (N : GlobalState Tx Hash Party AdvState) : DeliverySteps N N :=
  .RefineStepR .refl

theorem baking_steps_refl (N : GlobalState Tx Hash Party AdvState) : BakingSteps N N :=
  .RefineStepB .refl

/-- On the way to `N2`, the adversarial baking steps send only honest blocks that were already
broadcast. -/
def baking_free (N2 : GlobalState Tx Hash Party AdvState) : Prop :=
  ∀ N1, BakingSteps N1 N2 →
    honest_subset
      ((AdversarialBake N1.t_now N1.history N1.msg_buff N1.adv_state).1.map
        (fun mp => get_block mp.1))
      (block_history N1)

/-- On the way to `N2`, the adversarial receiving steps send only honest blocks that were
already broadcast. -/
def delivery_free (N2 : GlobalState Tx Hash Party AdvState) : Prop :=
  ∀ N1, DeliverySteps N1 N2 → ∀ p : Party,
    honest_subset
      ((AdversarialRcv (fetch_msgs p N1).1 (fetch_msgs p N1).2.t_now (fetch_msgs p N1).2.history
        (fetch_msgs p N1).2.msg_buff (fetch_msgs p N1).2.adv_state).1.map
          (fun mp => get_block mp.1))
      (block_history (fetch_msgs p N1).2)

/-- The adversary cannot forge honest blocks on the way to `N`. -/
def forging_free (N : GlobalState Tx Hash Party AdvState) : Prop :=
  delivery_free N ∧ baking_free N

theorem DeliverySteps.big_step {N1 N2 N3 : GlobalState Tx Hash Party AdvState}
    (h : DeliverySteps N1 N2) (h' : N2 ⇓ N3) : DeliverySteps N1 N3 := by
  induction h with
  | RefineStepR h => exact .RefineStepR (h.trans h')
  | ProgressR _ ih => exact .ProgressR (ih h')
  | RcvStep p _ ih => exact .RcvStep p (ih h')

theorem BakingSteps.big_step {N1 N2 N3 : GlobalState Tx Hash Party AdvState}
    (h : BakingSteps N1 N2) (h' : N2 ⇓ N3) : BakingSteps N1 N3 := by
  induction h with
  | RefineStepB h => exact .RefineStepB (h.trans h')
  | ProgressB _ ih => exact .ProgressB (ih h')
  | BakeStep p _ ih => exact .BakeStep p (ih h')

theorem baking_free_prev {N1 N2 : GlobalState Tx Hash Party AdvState} (h : N1 ⇓ N2)
    (hf : baking_free N2) : baking_free N1 :=
  fun N' hB => hf N' (hB.big_step h)

theorem delivery_free_prev {N1 N2 : GlobalState Tx Hash Party AdvState} (h : N1 ⇓ N2)
    (hf : delivery_free N2) : delivery_free N1 :=
  fun N' hD => hf N' (hD.big_step h)

/-- Forging freedom holds in every earlier state of an execution (`forging_free_prev`). -/
theorem forging_free_prev {N1 N2 : GlobalState Tx Hash Party AdvState} (h : N1 ⇓ N2)
    (hf : forging_free N2) : forging_free N1 :=
  ⟨delivery_free_prev h hf.1, baking_free_prev h hf.2⟩

/-! ## The history under party steps -/

section History

variable (N : GlobalState Tx Hash Party AdvState)

@[simp] theorem flood_msgs_history (msgs : Messages Tx Hash Party) :
    (flood_msgs msgs N).history = msgs ++ N.history := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs, flood_msg] using ih

@[simp] theorem flood_msgs_adv_history (msgs : List (Message Tx Hash Party × DelayMap Party)) :
    (flood_msgs_adv msgs N).history = msgs.map Prod.fst ++ N.history := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs_adv, flood_msg_adv] using ih

/-- The messages broadcast by a receiving step are those of the adversary, for a corrupt
party with a local state. -/
theorem rcv_history (p : Party) (m : Message Tx Hash Party) :
    m ∈ (party_rcv_step_world p N).history ↔ m ∈ N.history ∨
      ((N.state_map p).isSome ∧ is_corrupt p = true ∧
        m ∈ (AdversarialRcv (fetch_msgs p N).1 (fetch_msgs p N).2.t_now
          (fetch_msgs p N).2.history (fetch_msgs p N).2.msg_buff
          (fetch_msgs p N).2.adv_state).1.map Prod.fst) := by
  unfold party_rcv_step_world
  cases hl : N.state_map p with
  | none => simp
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false, flood_msgs_adv_history,
        List.mem_append, Option.isSome_some, true_and]
      rw [or_comm]
      rfl
    · simp [hc, upd_local, fetch_msgs, rmv_zero_msgs]

/-- The messages broadcast by a baking step: the honest protocol for an honest party, the
adversary for a corrupt one. -/
theorem bake_history (p : Party) (m : Message Tx Hash Party) :
    m ∈ (party_bake_step_world p N).history ↔ m ∈ N.history ∨
      ∃ l, N.state_map p = some l ∧
        ((is_corrupt p = false ∧
          m ∈ (honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p)
            l).1) ∨
         (is_corrupt p = true ∧
          m ∈ (AdversarialBake N.t_now N.history N.msg_buff N.adv_state).1.map Prod.fst)) := by
  unfold party_bake_step_world
  cases hl : N.state_map p with
  | none => simp
  | some l =>
    by_cases hc : is_corrupt p
    · simp [hc, or_comm]
    · simp [hc, upd_local, or_comm]

theorem rcv_history_mono (p : Party) :
    ∀ m ∈ N.history, m ∈ (party_rcv_step_world p N).history :=
  fun m hm => (rcv_history N p m).2 (Or.inl hm)

theorem bake_history_mono (p : Party) :
    ∀ m ∈ N.history, m ∈ (party_bake_step_world p N).history :=
  fun m hm => (bake_history N p m).2 (Or.inl hm)

theorem rcvs_history_mono (ps : List Party) :
    ∀ m ∈ N.history, m ∈ (ps.foldr party_rcv_step_world N).history := by
  induction ps with
  | nil => exact fun _ h => h
  | cons p ps ih => exact fun m hm => rcv_history_mono _ p m (ih m hm)

theorem bakes_history_mono (ps : List Party) :
    ∀ m ∈ N.history, m ∈ (ps.foldr party_bake_step_world N).history := by
  induction ps with
  | nil => exact fun _ h => h
  | cons p ps ih => exact fun m hm => bake_history_mono _ p m (ih m hm)

end History

/-- The history only grows along an execution (`history_monotone`). -/
theorem history_monotone {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') :
    ∀ m ∈ N.history, m ∈ N'.history := by
  induction h with
  | refl => exact fun _ h => h
  | tail _ hs ih =>
    intro m hm
    have hm := ih m hm
    cases hs with
    | Deliver hp => exact rcvs_history_mono _ _ m hm
    | Bake hp => exact bakes_history_mono _ _ m hm
    | NextRound hp => exact hm
    | PermParties ps hps => exact hm
    | PermMsgs mb hmb => exact hm

/-- The block history only grows along an execution (`block_history_monotone`). -/
theorem block_history_monotone {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') :
    ∀ b ∈ block_history N, b ∈ block_history N' := by
  intro b hb
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
  exact List.mem_map_of_mem (history_monotone h m hm)

theorem block_hist_gb_monotone {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') :
    ∀ b ∈ block_hist_gb N, b ∈ block_hist_gb N' := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (block_history_monotone h b hb)

/-- Collision freedom holds in every earlier state of an execution (`coll_free_big_step`). -/
theorem collision_free_prev {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N')
    (hcf : collision_free N') : collision_free N :=
  fun b hb b' hb' => hcf b (block_hist_gb_monotone h b hb) b' (block_hist_gb_monotone h b' hb')

/-! ## New honest blocks -/

section NewBlocks

variable (N : GlobalState Tx Hash Party AdvState)

/-- If the adversary does not forge, a receiving step broadcasts no new honest block. -/
theorem rcv_honest_history (p : Party)
    (hdf : honest_subset
      ((AdversarialRcv (fetch_msgs p N).1 (fetch_msgs p N).2.t_now (fetch_msgs p N).2.history
        (fetch_msgs p N).2.msg_buff (fetch_msgs p N).2.adv_state).1.map
          (fun mp => get_block mp.1))
      (block_history (fetch_msgs p N).2)) :
    ∀ b ∈ block_history (party_rcv_step_world p N), honest_block b = true →
      b ∈ block_history N := by
  intro b hb hh
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
  rcases (rcv_history N p m).1 hm with hm | ⟨-, -, hm⟩
  · exact List.mem_map_of_mem hm
  · obtain ⟨mp, hmp, rfl⟩ := List.mem_map.1 hm
    exact hdf _ (List.mem_map_of_mem hmp) hh

/-- The block baked by an honest party with local state `l` in slot `t`. -/
def honest_new_block (t : Slot) (p : Party) (l : LocalState Tx Hash Party) : Block Tx Hash Party :=
  ⟨t, TxSelection (Hash := Hash) (AdvState := AdvState) t p,
    HashB ((l.tT.bestChain (t - 1) l.tree).headD GenesisBlock), l.pk⟩

/-- If the adversary does not forge, the only new honest block of a baking step is the block
baked by the party itself, if it is honest and wins the slot. -/
theorem bake_honest_history (p : Party)
    (hbf : honest_subset
      ((AdversarialBake N.t_now N.history N.msg_buff N.adv_state).1.map
        (fun mp => get_block mp.1))
      (block_history N)) :
    ∀ b ∈ block_history (party_bake_step_world p N), honest_block b = true →
      b ∈ block_history N ∨ (is_honest p = true ∧ ∃ l, N.state_map p = some l ∧
        Winner l.pk N.t_now = true ∧ b = honest_new_block (AdvState := AdvState) N.t_now p l) := by
  intro b hb hh
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
  rcases (bake_history N p m).1 hm with hm | ⟨l, hl, ⟨hc, hm⟩ | ⟨-, hm⟩⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · right
    refine ⟨by rw [honest_not_corrupt, hc]; rfl, l, hl, ?_⟩
    rw [honest_bake_eq] at hm
    by_cases hw : Winner l.pk N.t_now = true
    · simp only [hw, if_true, List.mem_singleton] at hm
      exact ⟨hw, by subst hm; rfl⟩
    · simp [hw] at hm
  · obtain ⟨mp, hmp, rfl⟩ := List.mem_map.1 hm
    exact Or.inl (hbf _ (List.mem_map_of_mem hmp) hh)

/-- If the adversary does not forge along part of a delivery phase, no new honest block is
broadcast. -/
theorem rcvs_honest_history {X : GlobalState Tx Hash Party AdvState} (hdf : delivery_free X)
    (ps : List Party) (hD : DeliverySteps (ps.foldr party_rcv_step_world N) X) :
    ∀ b ∈ block_history (ps.foldr party_rcv_step_world N), honest_block b = true →
      b ∈ block_history N := by
  induction ps with
  | nil => exact fun _ h _ => h
  | cons p ps ih =>
    have hD' : DeliverySteps (ps.foldr party_rcv_step_world N) X := .RcvStep p hD
    intro b hb hh
    exact ih hD' b (rcv_honest_history _ p (hdf _ hD' p) b hb hh) hh

/-- If the adversary does not forge along part of a baking phase, every new honest block is
the block baked by an honest party of the phase that wins the slot. -/
theorem bakes_honest_history {X : GlobalState Tx Hash Party AdvState} (hbf : baking_free X)
    (ps : List Party) (hB : BakingSteps (ps.foldr party_bake_step_world N) X) :
    ∀ b ∈ block_history (ps.foldr party_bake_step_world N), honest_block b = true →
      b ∈ block_history N ∨ ∃ pre q qs, ps = pre ++ q :: qs ∧ is_honest q = true ∧
        ∃ l, (qs.foldr party_bake_step_world N).state_map q = some l ∧
          Winner l.pk N.t_now = true ∧ b = honest_new_block (AdvState := AdvState) N.t_now q l := by
  induction ps with
  | nil => exact fun _ h _ => Or.inl h
  | cons p ps ih =>
    have hB' : BakingSteps (ps.foldr party_bake_step_world N) X := .BakeStep p hB
    intro b hb hh
    have ht := (bakes_step_facts N ps).time
    rcases bake_honest_history _ p (hbf _ hB') b hb hh with hb' | ⟨hhp, l, hl, hw, rfl⟩
    · rcases ih hB' b hb' hh with h | ⟨pre, q, qs, rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p :: pre, q, qs, rfl, h⟩
    · rw [ht] at hw ⊢
      exact Or.inr ⟨[], p, ps, rfl, hhp, l, hl, hw, rfl⟩

end NewBlocks

/-! ## Honest blocks of the history -/

/-- In a reachable state without forging, honest blocks of the history have a slot at most
the current slot, and smaller than the current slot outside the baking phase. -/
theorem honest_hist_slots {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N)
    (hff : forging_free N) :
    ∀ b ∈ block_history N, honest_block b = true →
      b.sl ≤ N.t_now ∧ (N.progress ≠ .Baked → b.sl < N.t_now) := by
  induction hR with
  | refl => simp [block_history, N0]
  | tail hRM hs ih =>
    rename_i M N2
    have hffM := forging_free_prev (Relation.ReflTransGen.single hs) hff
    have ih := ih hffM
    intro b hb hh
    cases hs with
    | Deliver hp =>
      have hb' := rcvs_honest_history M hff.1 M.exec_order (.ProgressR (.RefineStepR .refl)) b
        hb hh
      have := (rcvs_step_facts M M.exec_order).time
      have := (ih b hb' hh).2 (by simp [hp])
      simp only at this ⊢
      omega
    | Bake hp =>
      have ht := (bakes_step_facts M M.exec_order).time
      rcases bakes_honest_history M hff.2 M.exec_order (.ProgressB (.RefineStepB .refl)) b hb hh
        with hb' | ⟨_, _, _, _, _, _, _, _, rfl⟩
      · have := (ih b hb' hh).2 (by simp [hp])
        simp only [ht]
        exact ⟨by omega, fun h => absurd rfl h⟩
      · simp only [ht, honest_new_block]
        exact ⟨le_rfl, fun h => absurd rfl h⟩
    | NextRound hp =>
      have := (ih b hb hh).1
      simp only [inc_round, round_tick]
      omega
    | PermParties ps hps => exact ih b hb hh
    | PermMsgs mb hmb => exact ih b hb hh

/-- Honest blocks of the history have a slot at most the current slot
(`no_premature_honest_blocks`). -/
theorem no_premature_honest_blocks {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N)
    (hff : forging_free N) : ∀ b ∈ honest_block_hist N, b.sl ≤ N.t_now := by
  intro b hb
  obtain ⟨hb, hh⟩ := List.mem_filter.1 hb
  exact (honest_hist_slots hR hff b hb hh).1

/-- At the start of a slot, honest blocks of the history have a smaller slot
(`no_premature_honest_blocks_R`). -/
theorem no_premature_honest_blocks_R {N : GlobalState Tx Hash Party AdvState}
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hp : N.progress = .Ready) :
    ∀ b ∈ honest_block_hist N, b.sl < N.t_now := by
  intro b hb
  obtain ⟨hb, hh⟩ := List.mem_filter.1 hb
  exact (honest_hist_slots hR hff b hb hh).2 (by simp [hp])

/-- After the delivery phase, honest blocks of the history have a smaller slot
(`no_premature_honest_blocks_D`). -/
theorem no_premature_honest_blocks_D {N : GlobalState Tx Hash Party AdvState}
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hp : N.progress = .Delivered) :
    ∀ b ∈ honest_block_hist N, b.sl < N.t_now := by
  intro b hb
  obtain ⟨hb, hh⟩ := List.mem_filter.1 hb
  exact (honest_hist_slots hR hff b hb hh).2 (by simp [hp])

/-- Without forging, an honest block of slot `s` in the history of a later state was already
in the history of every state after the baking phase of slot `s`. -/
theorem honest_block_preserved_phase {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N')
    (hff : forging_free N') :
    ∀ b ∈ block_history N', honest_block b = true → 3 * b.sl + 2 ≤ phase N →
      b ∈ block_history N := by
  induction h with
  | refl => exact fun _ h _ _ => h
  | tail hNM hs ih =>
    rename_i M N2
    have hffM := forging_free_prev (Relation.ReflTransGen.single hs) hff
    have hph := monotone_phase hNM
    intro b hb hh hle
    refine ih hffM b ?_ hh hle
    cases hs with
    | Deliver hp =>
      exact rcvs_honest_history M hff.1 M.exec_order (.ProgressR (.RefineStepR .refl)) b hb hh
    | Bake hp =>
      rcases bakes_honest_history M hff.2 M.exec_order (.ProgressB (.RefineStepB .refl)) b hb hh
        with hb' | ⟨_, _, _, _, _, _, _, _, rfl⟩
      · exact hb'
      · exfalso
        simp only [phase, hp, honest_new_block] at hph hle
        omega
    | NextRound hp => exact hb
    | PermParties ps hps => exact hb
    | PermMsgs mb hmb => exact hb

/-- Without forging, the honest blocks of the history with a slot before the current one do
not change along an execution (`honest_blocks_below_slot_preserved`). -/
theorem honest_blocks_below_slot_preserved {N N' : GlobalState Tx Hash Party AdvState}
    (h : N ⇓ N') (hff : forging_free N') :
    (honest_block_hist N).filter (fun b => decide (b.sl < N.t_now)) =i
      (honest_block_hist N').filter (fun b => decide (b.sl < N.t_now)) := by
  intro b
  simp only [honest_block_hist, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hb, hh⟩, hs⟩
    exact ⟨⟨block_history_monotone h b hb, hh⟩, hs⟩
  · rintro ⟨⟨hb, hh⟩, hs⟩
    refine ⟨⟨honest_block_preserved_phase h hff b hb hh ?_, hh⟩, hs⟩
    have := le_phase N
    omega

/-! ## Messages in transit and local trees -/

/-- The invariant of the history: every message in transit has been broadcast, and every
block of a local tree is the genesis block or a broadcast block. -/
structure HistInv (N : GlobalState Tx Hash Party AdvState) : Prop where
  buff : ∀ mt ∈ N.msg_buff, mt.msg ∈ N.history
  state : ∀ p l, N.state_map p = some l → ∀ b ∈ l.blocks, b ∈ block_hist_gb N

theorem hist_inv_N0 : HistInv (N0 AdvState : GlobalState Tx Hash Party AdvState) where
  buff := by simp [N0]
  state := fun p l h b hb => by
    simp only [N0] at h
    split at h
    · cases h
      have := ((TreeTypeMap (AdvState := AdvState) p).all_tree0 b).1 hb
      simp only [List.mem_singleton] at this
      simp [block_hist_gb, this]
    · cases h

theorem mem_block_hist_gb_of {N N' : GlobalState Tx Hash Party AdvState}
    (h : ∀ m ∈ N.history, m ∈ N'.history) :
    ∀ b ∈ block_hist_gb N, b ∈ block_hist_gb N' := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact List.mem_cons_self
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (h m hm))

theorem HistInv.rcv {N : GlobalState Tx Hash Party AdvState} (hN : HistInv N) (p : Party) :
    HistInv (party_rcv_step_world p N) := by
  have hmono := rcv_history_mono N p
  unfold party_rcv_step_world
  cases hl : N.state_map p with
  | none => exact hN
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
      refine ⟨fun mt hmt => ?_, fun q k hk b hb => ?_⟩
      · simp only [flood_msgs_adv_history, List.mem_append, List.mem_map]
        rcases (mem_flood_msgs_adv _ _ mt).1 hmt with hmt | ⟨mφ, hmφ, r, -, rfl⟩
        · simp only [fetch_msgs, rmv_zero_msgs, List.mem_filter] at hmt
          exact Or.inr (hN.buff mt hmt.1)
        · exact Or.inl ⟨mφ, hmφ, rfl⟩
      · simp only [flood_msgs_adv_state_map, fetch_msgs, rmv_zero_msgs] at hk
        refine mem_block_hist_gb_of (N := N) (fun m hm => ?_) b (hN.state q k hk b hb)
        simp only [flood_msgs_adv_history, List.mem_append]
        exact Or.inr hm
    · simp only [hc, Bool.not_false, if_true]
      refine ⟨fun mt hmt => ?_, fun q k hk b hb => ?_⟩
      · simp only [upd_local, fetch_msgs, rmv_zero_msgs, List.mem_filter] at hmt ⊢
        exact hN.buff mt hmt.1
      · simp only [upd_local, fetch_msgs, rmv_zero_msgs] at hk ⊢
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self, Option.some.injEq] at hk
          subst hk
          simp only [honest_rcv, process_msgs, State.modify] at hb
          rcases List.mem_append.1 ((foldr_process_msg_blocks _ l b).1 hb) with hb | hb
          · exact hN.state q l hl b hb
          · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
            obtain ⟨mt, hmt, rfl⟩ := List.mem_map.1 hm
            simp only [collect_zero_pairs, List.mem_filter] at hmt
            exact List.mem_cons_of_mem _ (List.mem_map_of_mem (hN.buff mt hmt.1))
        · rw [Function.update_of_ne hq] at hk
          exact hN.state q k hk b hb

theorem HistInv.bake {N : GlobalState Tx Hash Party AdvState} (hN : HistInv N) (p : Party) :
    HistInv (party_bake_step_world p N) := by
  unfold party_bake_step_world
  cases hl : N.state_map p with
  | none => exact hN
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
      refine ⟨fun mt hmt => ?_, fun q k hk b hb => ?_⟩
      · simp only [flood_msgs_adv_history, List.mem_append, List.mem_map]
        rcases (mem_flood_msgs_adv _ _ mt).1 hmt with hmt | ⟨mφ, hmφ, r, -, rfl⟩
        · exact Or.inr (hN.buff mt hmt)
        · exact Or.inl ⟨mφ, hmφ, rfl⟩
      · simp only [flood_msgs_adv_state_map] at hk
        refine mem_block_hist_gb_of (N := N) (fun m hm => ?_) b (hN.state q k hk b hb)
        simp only [flood_msgs_adv_history, List.mem_append]
        exact Or.inr hm
    · simp only [hc, Bool.not_false, if_true]
      refine ⟨fun mt hmt => ?_, fun q k hk b hb => ?_⟩
      · rcases (mem_flood_msgs _ _ mt).1 hmt with hmt | ⟨m, hm, r, -, rfl⟩
        · simp only [upd_local] at hmt
          simp only [flood_msgs_history, upd_local, List.mem_append]
          exact Or.inr (hN.buff mt hmt)
        · simp only [flood_msgs_history, upd_local, List.mem_append]
          exact Or.inl hm
      · simp only [flood_msgs_state_map, upd_local] at hk
        have hmono : ∀ m ∈ N.history, m ∈ (flood_msgs
            (honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p)
              l).1 (upd_local p
            (honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p)
              l).2 N)).history := fun m hm => by
          simp only [flood_msgs_history, upd_local, List.mem_append]; exact Or.inr hm
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self, Option.some.injEq] at hk
          subst hk
          rcases List.mem_append.1 ((honest_bake_blocks _ _ l b).1 hb) with hb | hb
          · exact mem_block_hist_gb_of hmono b (hN.state q l hl b hb)
          · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
            refine List.mem_cons_of_mem _ (List.mem_map_of_mem ?_)
            simp only [flood_msgs_history, upd_local, List.mem_append]
            exact Or.inl hm
        · rw [Function.update_of_ne hq] at hk
          exact mem_block_hist_gb_of hmono b (hN.state q k hk b hb)

theorem HistInv.rcvs {N : GlobalState Tx Hash Party AdvState} (hN : HistInv N)
    (ps : List Party) : HistInv (ps.foldr party_rcv_step_world N) := by
  induction ps with
  | nil => exact hN
  | cons p ps ih => exact ih.rcv p

theorem HistInv.bakes {N : GlobalState Tx Hash Party AdvState} (hN : HistInv N)
    (ps : List Party) : HistInv (ps.foldr party_bake_step_world N) := by
  induction ps with
  | nil => exact hN
  | cons p ps ih => exact ih.bake p

theorem HistInv.step {N N' : GlobalState Tx Hash Party AdvState} (hN : HistInv N)
    (h : N ⤳ N') : HistInv N' := by
  cases h with
  | Deliver hp => exact ⟨(hN.rcvs _).buff, (hN.rcvs _).state⟩
  | Bake hp => exact ⟨(hN.bakes _).buff, (hN.bakes _).state⟩
  | NextRound hp =>
    refine ⟨fun mt hmt => ?_, hN.state⟩
    simp only [inc_round, round_tick, List.mem_map] at hmt
    obtain ⟨mt', hmt', rfl⟩ := hmt
    exact hN.buff mt' hmt'
  | PermParties ps hps => exact ⟨hN.buff, hN.state⟩
  | PermMsgs mb hmb => exact ⟨fun mt hmt => hN.buff mt (hmb.mem_iff.2 hmt), hN.state⟩

/-- Every reachable state satisfies `HistInv`. -/
theorem reachable_hist_inv {N : GlobalState Tx Hash Party AdvState} (h : N0 AdvState ⇓ N) :
    HistInv N := by
  induction h with
  | refl => exact hist_inv_N0
  | tail _ hs ih => exact ih.step hs

/-- In a reachable state, every message in transit has been broadcast
(`buff_history_subset`). -/
theorem buff_history_subset {N : GlobalState Tx Hash Party AdvState} (h : N0 AdvState ⇓ N) :
    ∀ m ∈ N.msg_buff.map MessageTuple.msg, m ∈ N.history := by
  intro m hm
  obtain ⟨mt, hmt, rfl⟩ := List.mem_map.1 hm
  exact (reachable_hist_inv h).buff mt hmt

/-- In a reachable state, every block of the honest tree is the genesis block or a broadcast
block (`honest_tree_hist_gb_subset`). -/
theorem honest_tree_hist_gb_subset (Tree : TreeType Tx Hash Party)
    {N : GlobalState Tx Hash Party AdvState} (h : N0 AdvState ⇓ N) :
    ∀ b ∈ Tree.allBlocks (honest_tree Tree N), b ∈ block_hist_gb N := by
  intro b hb
  rcases (mem_honest_tree Tree N b).1 hb with rfl | ⟨p, -, -, l, hl, hb⟩
  · exact List.mem_cons_self
  · exact (reachable_hist_inv h).state p l hl b hb

/-! ## Chains of broadcast blocks -/

/-- Without hash collisions among the blocks of `H`, two valid chains of blocks of `H` with
the same head are equal. -/
theorem eq_head_eq_chains_gen {H : List (Block Tx Hash Party)}
    (hcf : ∀ b ∈ H, ∀ b' ∈ H, HashB b = HashB b' → b = b') :
    ∀ (c c' : Chain Tx Hash Party) (b : Block Tx Hash Party), valid_chain (b :: c) →
      valid_chain (b :: c') → (∀ x ∈ c, x ∈ H) → (∀ x ∈ c', x ∈ H) → c = c' := by
  intro c
  induction c with
  | nil =>
    intro c' b hv hv' _ _
    rw [valid_chain_single hv] at hv'
    exact (valid_chain_gb_head hv').symm
  | cons x xs ih =>
    intro c' b hv hv' hs hs'
    cases c' with
    | nil =>
      rw [valid_chain_single hv'] at hv
      exact absurd (valid_chain_gb_head hv) (by simp)
    | cons y ys =>
      have hx : HashB x = HashB y := hv.2.1.1.symm.trans hv'.2.1.1
      have hxy := hcf x (hs x List.mem_cons_self) y (hs' y List.mem_cons_self) hx
      subst hxy
      rw [ih ys x (valid_chain_tail hv (by simp)) (valid_chain_tail hv' (by simp))
        (fun z hz => hs z (List.mem_cons_of_mem _ hz))
        (fun z hz => hs' z (List.mem_cons_of_mem _ hz))]

/-- Without hash collisions, two valid chains of broadcast blocks with the same head are equal
(`eq_head_eq_chains`). -/
theorem eq_head_eq_chains {N : GlobalState Tx Hash Party AdvState} (hcf : collision_free N)
    {c c' : Chain Tx Hash Party} {b : Block Tx Hash Party} (hv : valid_chain (b :: c))
    (hv' : valid_chain (b :: c')) (hs : ∀ x ∈ c, x ∈ block_hist_gb N)
    (hs' : ∀ x ∈ c', x ∈ block_hist_gb N) : c = c' :=
  eq_head_eq_chains_gen hcf c c' b hv hv' hs hs'

/-- Under the longest-chain rule, adding a block of slot `t` to a tree lengthens the chain
selected at slot `t` by at most one block over the chain selected at slot `t - 1`
(`bc_ext_max_increase`). -/
theorem bc_ext_max_increase {tT : TreeType Tx Hash Party} (hL : tT.LongestChainRule)
    (tree : tT.T) (t : Slot) (b : Block Tx Hash Party) (hsl : b.sl = t) :
    (tT.bestChain t (tT.extendTree tree b)).length ≤ (tT.bestChain (t - 1) tree).length + 1 := by
  have hv := tT.best_chain_valid (tT.extendTree tree b) t
  obtain ⟨b', rest, hbc⟩ := List.exists_cons_of_ne_nil (valid_chain_ne_nil hv)
  rw [hbc] at hv ⊢
  by_cases hr : rest = []
  · subst hr; simp
  have hin := tT.best_chain_in_all t (tT.extendTree tree b)
  rw [hbc] at hin
  have hb' := hin b' List.mem_cons_self
  simp only [List.mem_filter, decide_eq_true_eq] at hb'
  have := hL rest (t - 1) tree (valid_chain_tail hv hr) fun x hx => by
    have hx' := hin x (List.mem_cons_of_mem _ hx)
    have hlt : lt_slots b' x := List.rel_of_pairwise_cons hv.2.2 hx
    simp only [List.mem_filter, decide_eq_true_eq, lt_slots] at hx' hlt ⊢
    rw [tT.all_extend, List.mem_append, List.mem_singleton] at hx'
    rcases hx'.1 with h | rfl
    · exact ⟨h, by omega⟩
    · omega
  simp only [List.length_cons]
  omega

end CatCryptCore.Consensus.PoSNSB

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.TreeChain

/-!
# PoS-NSB: party steps and invariants of reachable states

This file ports the first part of the preliminaries of the chain-growth proof in
`Properties/CG.v` of PoS-NSB (Thomsen and Spitters, CSF 2021): the definitions `has_state`,
`honest_parties`, `blocks`, `honest_tree` and `tbd`, the effect of broadcasts and party steps
on the global state, and invariants of the states reachable from `N0`.

## Main results

* `bake_step_facts`, `rcv_step_facts`, `bakes_step_facts`, `rcvs_step_facts`: a sequence of
  party steps keeps the execution order, slot and progress, adds messages only for parties
  of the execution order with delay `1` or `2`, keeps messages with nonzero delay, adds the
  same blocks in transit for every party of the execution order, and keeps every local state
  with its key and tree type while its tree grows (`StepFacts`).
* `reachable_inv`: every reachable state satisfies `Inv`: the execution order is a
  permutation of `InitParties`, exactly the initial parties have a local state, each local
  state carries its party's key and tree type, every message is addressed to an initial
  party with delay at most `2`, outside the `Ready` phase no message has delay `0`, and in
  the `Ready` phase no message has delay `2`.

Where the Coq development proves each of these facts by a separate induction over
executions, they are collected here in the invariant `Inv`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-- Two lists have the same members. -/
def MemEq {α : Type*} (a b : List α) : Prop := ∀ x, x ∈ a ↔ x ∈ b

@[inherit_doc] infix:50 " =i " => MemEq

/-! ## Basic definitions of `Properties/CG.v` -/

/-- The party `p` has local state `l` in `N`. -/
def has_state (p : Party) (N : GlobalState Tx Hash Party AdvState)
    (l : LocalState Tx Hash Party) : Prop :=
  N.state_map p = some l

/-- The honest parties of the execution order. -/
def honest_parties (N : GlobalState Tx Hash Party AdvState) : List Party :=
  N.exec_order.filter is_honest

/-- The blocks in the tree of `p`. -/
def blocks (p : Party) (N : GlobalState Tx Hash Party AdvState) : BlockPool Tx Hash Party :=
  match N.state_map p with
  | some l => l.blocks
  | none => []

/-- The honest tree: the tree of type `Tree` holding the blocks of all honest parties. -/
def honest_tree (Tree : TreeType Tx Hash Party) (N : GlobalState Tx Hash Party AdvState) :
    Tree.T :=
  build_tree Tree ((honest_parties N).map (fun p => blocks p N)).flatten

/-- The blocks to be delivered to `p` in `n` rounds. -/
def tbd (n : ℕ) (p : Party) (N : GlobalState Tx Hash Party AdvState) :
    List (Block Tx Hash Party) :=
  (N.msg_buff.filter (fun mt => mt.cd == n && decide (mt.rcv = p))).map
    (fun mt => get_block mt.msg)

theorem honest_not_corrupt (p : Party) : is_honest p = !is_corrupt p := by
  unfold is_honest is_corrupt; cases CorruptionStatus p <;> rfl

theorem mem_tbd {n : ℕ} {p : Party} {N : GlobalState Tx Hash Party AdvState}
    {b : Block Tx Hash Party} :
    b ∈ tbd n p N ↔ ∃ mt ∈ N.msg_buff, mt.cd = n ∧ mt.rcv = p ∧ get_block mt.msg = b := by
  simp [tbd, and_assoc]

theorem mem_honest_tree (Tree : TreeType Tx Hash Party) (N : GlobalState Tx Hash Party AdvState)
    (b : Block Tx Hash Party) :
    b ∈ Tree.allBlocks (honest_tree Tree N) ↔ b = GenesisBlock ∨
      ∃ p ∈ N.exec_order, is_honest p = true ∧ ∃ l, N.state_map p = some l ∧ b ∈ l.blocks := by
  rw [honest_tree, all_build]
  simp only [List.mem_cons, List.mem_flatten, List.mem_map, honest_parties, List.mem_filter]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨_, ⟨p, ⟨hp, hh⟩, rfl⟩, hb⟩
    refine ⟨p, hp, hh, ?_⟩
    unfold blocks at hb
    cases h : N.state_map p with
    | none => simp [h] at hb
    | some l => exact ⟨l, rfl, by simpa [h] using hb⟩
  · rintro ⟨p, hp, hh, l, hl, hb⟩
    exact ⟨_, ⟨p, ⟨hp, hh⟩, rfl⟩, by simpa [blocks, hl] using hb⟩

/-! ## Broadcast -/

section Flood

variable (N : GlobalState Tx Hash Party AdvState)

@[simp] theorem flood_msgs_exec_order (msgs : Messages Tx Hash Party) :
    (flood_msgs msgs N).exec_order = N.exec_order := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs, flood_msg] using ih

@[simp] theorem flood_msgs_t_now (msgs : Messages Tx Hash Party) :
    (flood_msgs msgs N).t_now = N.t_now := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs, flood_msg] using ih

@[simp] theorem flood_msgs_state_map (msgs : Messages Tx Hash Party) :
    (flood_msgs msgs N).state_map = N.state_map := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs, flood_msg] using ih

@[simp] theorem flood_msgs_progress (msgs : Messages Tx Hash Party) :
    (flood_msgs msgs N).progress = N.progress := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs, flood_msg] using ih

theorem mem_flood_msgs (msgs : Messages Tx Hash Party) (mt : MessageTuple Tx Hash Party) :
    mt ∈ (flood_msgs msgs N).msg_buff ↔
      mt ∈ N.msg_buff ∨ ∃ m ∈ msgs, ∃ r ∈ N.exec_order, mt = ⟨m, r, 1⟩ := by
  induction msgs with
  | nil => simp [flood_msgs]
  | cons m ms ih =>
    have e : (flood_msgs (m :: ms) N).msg_buff =
        (flood_msgs ms N).exec_order.map (fun r => ⟨m, r, 1⟩) ++ (flood_msgs ms N).msg_buff :=
      rfl
    rw [e, List.mem_append, ih, flood_msgs_exec_order]
    simp only [List.mem_map, List.mem_cons]
    constructor
    · rintro (⟨r, hr, rfl⟩ | h | ⟨m', hm', r, hr, rfl⟩)
      · exact Or.inr ⟨m, Or.inl rfl, r, hr, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨m', Or.inr hm', r, hr, rfl⟩
    · rintro (h | ⟨m', rfl | hm', r, hr, rfl⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨r, hr, rfl⟩
      · exact Or.inr (Or.inr ⟨m', hm', r, hr, rfl⟩)

@[simp] theorem flood_msgs_adv_exec_order (msgs : List (Message Tx Hash Party × DelayMap Party)) :
    (flood_msgs_adv msgs N).exec_order = N.exec_order := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs_adv, flood_msg_adv] using ih

@[simp] theorem flood_msgs_adv_t_now (msgs : List (Message Tx Hash Party × DelayMap Party)) :
    (flood_msgs_adv msgs N).t_now = N.t_now := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs_adv, flood_msg_adv] using ih

@[simp] theorem flood_msgs_adv_state_map (msgs : List (Message Tx Hash Party × DelayMap Party)) :
    (flood_msgs_adv msgs N).state_map = N.state_map := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs_adv, flood_msg_adv] using ih

@[simp] theorem flood_msgs_adv_progress (msgs : List (Message Tx Hash Party × DelayMap Party)) :
    (flood_msgs_adv msgs N).progress = N.progress := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simpa [flood_msgs_adv, flood_msg_adv] using ih

theorem mem_flood_msgs_adv (msgs : List (Message Tx Hash Party × DelayMap Party))
    (mt : MessageTuple Tx Hash Party) :
    mt ∈ (flood_msgs_adv msgs N).msg_buff ↔
      mt ∈ N.msg_buff ∨ ∃ mφ ∈ msgs, ∃ r ∈ N.exec_order, mt = ⟨mφ.1, r, (mφ.2 r).1⟩ := by
  induction msgs with
  | nil => simp [flood_msgs_adv]
  | cons m ms ih =>
    have e : (flood_msgs_adv (m :: ms) N).msg_buff =
        (flood_msgs_adv ms N).exec_order.map (fun r => ⟨m.1, r, (m.2 r).1⟩) ++
          (flood_msgs_adv ms N).msg_buff :=
      rfl
    rw [e, List.mem_append, ih, flood_msgs_adv_exec_order]
    simp only [List.mem_map, List.mem_cons]
    constructor
    · rintro (⟨r, hr, rfl⟩ | h | ⟨m', hm', r, hr, rfl⟩)
      · exact Or.inr ⟨m, Or.inl rfl, r, hr, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨m', Or.inr hm', r, hr, rfl⟩
    · rintro (h | ⟨m', rfl | hm', r, hr, rfl⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨r, hr, rfl⟩
      · exact Or.inr (Or.inr ⟨m', hm', r, hr, rfl⟩)

end Flood

/-! ## Party steps -/

section Steps

variable (N : GlobalState Tx Hash Party AdvState)

/-- The constant delay map with delay one round. -/
def delay1 : DelayMap Party := fun _ => ⟨1, Or.inl rfl⟩

/-- The local state of `p` after its own baking step. -/
def bake_local (p : Party) : Option (LocalState Tx Hash Party) :=
  match N.state_map p with
  | some l => if is_corrupt p then some l else
      some (honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p) l).2
  | none => none

/-- The local state of `p` after its own receiving step. -/
def rcv_local (p : Party) : Option (LocalState Tx Hash Party) :=
  match N.state_map p with
  | some l => if is_corrupt p then some l else
      some (((collect_zero_pairs p N).map MessageTuple.msg).foldr process_msg l)
  | none => none

@[simp] theorem bake_exec_order (p : Party) :
    (party_bake_step_world p N).exec_order = N.exec_order := by
  unfold party_bake_step_world
  split
  · split <;> simp [upd_local]
  · rfl

@[simp] theorem bake_t_now (p : Party) : (party_bake_step_world p N).t_now = N.t_now := by
  unfold party_bake_step_world
  split
  · split <;> simp [upd_local]
  · rfl

@[simp] theorem bake_progress (p : Party) :
    (party_bake_step_world p N).progress = N.progress := by
  unfold party_bake_step_world
  split
  · split <;> simp [upd_local]
  · rfl

theorem bake_state_map (p : Party) :
    (party_bake_step_world p N).state_map = Function.update N.state_map p (bake_local N p) := by
  unfold party_bake_step_world bake_local
  cases hl : N.state_map p with
  | none => simp [← hl]
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, ite_true]
      simp [← hl]
    · simp [hc, upd_local]

theorem bake_buff (p : Party) : ∃ new : List (Message Tx Hash Party × DelayMap Party),
    ∀ mt, mt ∈ (party_bake_step_world p N).msg_buff ↔
      mt ∈ N.msg_buff ∨ ∃ mφ ∈ new, ∃ r ∈ N.exec_order, mt = ⟨mφ.1, r, (mφ.2 r).1⟩ := by
  unfold party_bake_step_world
  cases hl : N.state_map p with
  | none => exact ⟨[], by simp⟩
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true]
      exact ⟨_, fun mt => mem_flood_msgs_adv N _ mt⟩
    · refine ⟨(honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p)
        l).1.map (fun m => (m, delay1)), fun mt => ?_⟩
      simp only [hc, Bool.not_false, ite_true]
      rw [mem_flood_msgs]
      simp [upd_local, delay1]

@[simp] theorem rcv_exec_order (p : Party) :
    (party_rcv_step_world p N).exec_order = N.exec_order := by
  unfold party_rcv_step_world
  split
  · split <;> simp [upd_local, fetch_msgs, rmv_zero_msgs]
  · rfl

@[simp] theorem rcv_t_now (p : Party) : (party_rcv_step_world p N).t_now = N.t_now := by
  unfold party_rcv_step_world
  split
  · split <;> simp [upd_local, fetch_msgs, rmv_zero_msgs]
  · rfl

@[simp] theorem rcv_progress (p : Party) :
    (party_rcv_step_world p N).progress = N.progress := by
  unfold party_rcv_step_world
  split
  · split <;> simp [upd_local, fetch_msgs, rmv_zero_msgs]
  · rfl

theorem rcv_state_map (p : Party) :
    (party_rcv_step_world p N).state_map = Function.update N.state_map p (rcv_local N p) := by
  unfold party_rcv_step_world rcv_local
  cases hl : N.state_map p with
  | none => simp [← hl]
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true, ite_true]
      simp [← hl, fetch_msgs, rmv_zero_msgs]
    · simp [hc, upd_local, fetch_msgs, rmv_zero_msgs, honest_rcv, process_msgs, State.modify]

theorem rcv_buff (p : Party) : ∃ new : List (Message Tx Hash Party × DelayMap Party),
    ∀ mt, mt ∈ (party_rcv_step_world p N).msg_buff ↔
      (mt ∈ N.msg_buff ∧ ¬ (mt.cd = 0 ∧ mt.rcv = p ∧ (N.state_map p).isSome)) ∨
        ∃ mφ ∈ new, ∃ r ∈ N.exec_order, mt = ⟨mφ.1, r, (mφ.2 r).1⟩ := by
  unfold party_rcv_step_world
  cases hl : N.state_map p with
  | none => exact ⟨[], by simp⟩
  | some l =>
    by_cases hc : is_corrupt p
    · simp only [hc, Bool.not_true]
      refine ⟨(AdversarialRcv (fetch_msgs p N).1 (fetch_msgs p N).2.t_now
        (fetch_msgs p N).2.history (fetch_msgs p N).2.msg_buff (fetch_msgs p N).2.adv_state).1,
        fun mt => ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      rw [mem_flood_msgs_adv]
      simp only [fetch_msgs, rmv_zero_msgs, List.mem_filter, Option.isSome_some]
      by_cases h0 : mt.cd = 0 <;> simp [h0]
    · refine ⟨[], fun mt => ?_⟩
      simp only [hc, Bool.not_false, ite_true]
      simp only [upd_local, fetch_msgs, rmv_zero_msgs, List.mem_filter, Option.isSome_some]
      by_cases h0 : mt.cd = 0 <;> simp [h0]

end Steps

/-! ## Local states under the honest protocol -/

section Local

theorem honest_bake_eq (sl : Slot) (txs : Tx) (l : LocalState Tx Hash Party) :
    honest_bake sl txs l =
      if Winner l.pk sl then
        let nb : Block Tx Hash Party :=
          ⟨sl, txs, HashB ((l.tT.bestChain (sl - 1) l.tree).headD GenesisBlock), l.pk⟩
        ([Message.BlockMsg nb], extend_tree_l l nb)
      else ([], l) := by
  by_cases hw : Winner l.pk sl = true <;>
    simp [honest_bake, hw, State.bind, State.get, State.modify, State.pure]

theorem honest_bake_pk (sl : Slot) (txs : Tx) (l : LocalState Tx Hash Party) :
    (honest_bake sl txs l).2.pk = l.pk := by
  rw [honest_bake_eq]; split <;> rfl

theorem honest_bake_tT (sl : Slot) (txs : Tx) (l : LocalState Tx Hash Party) :
    (honest_bake sl txs l).2.tT = l.tT := by
  rw [honest_bake_eq]; split <;> rfl

theorem honest_bake_blocks (sl : Slot) (txs : Tx) (l : LocalState Tx Hash Party) :
    (honest_bake sl txs l).2.blocks =i l.blocks ++ (honest_bake sl txs l).1.map get_block := by
  intro b
  rw [honest_bake_eq]
  split
  · exact l.tT.all_extend _ _ _
  · simp

theorem foldr_process_msg_pk (msgs : Messages Tx Hash Party) (l : LocalState Tx Hash Party) :
    (msgs.foldr process_msg l).pk = l.pk ∧ (msgs.foldr process_msg l).tT = l.tT := by
  induction msgs with
  | nil => exact ⟨rfl, rfl⟩
  | cons m ms ih => cases m; exact ih

theorem foldr_process_msg_blocks (msgs : Messages Tx Hash Party) (l : LocalState Tx Hash Party) :
    (msgs.foldr process_msg l).blocks =i l.blocks ++ msgs.map get_block := by
  induction msgs with
  | nil => intro b; simp
  | cons m ms ih =>
    intro b
    cases m with
    | BlockMsg b' =>
      have h := (ms.foldr process_msg l).tT.all_extend (ms.foldr process_msg l).tree b' b
      simp only [List.foldr_cons, process_msg, extend_tree_l, LocalState.blocks] at h ⊢
      rw [h, List.mem_append, ih b]
      simp only [List.mem_append, List.mem_map, List.mem_cons, LocalState.blocks]
      aesop

end Local

/-! ## Facts shared by all party steps -/

/-- The blocks to be delivered in one or two rounds. -/
def tbd12 (p : Party) (N : GlobalState Tx Hash Party AdvState) : List (Block Tx Hash Party) :=
  tbd 1 p N ++ tbd 2 p N

theorem mem_tbd12 {p : Party} {N : GlobalState Tx Hash Party AdvState}
    {b : Block Tx Hash Party} :
    b ∈ tbd12 p N ↔ ∃ mt ∈ N.msg_buff, (mt.cd = 1 ∨ mt.cd = 2) ∧ mt.rcv = p ∧
      get_block mt.msg = b := by
  simp only [tbd12, List.mem_append, mem_tbd]
  constructor
  · rintro (⟨mt, h, h1, h2, h3⟩ | ⟨mt, h, h1, h2, h3⟩)
    · exact ⟨mt, h, Or.inl h1, h2, h3⟩
    · exact ⟨mt, h, Or.inr h1, h2, h3⟩
  · rintro ⟨mt, h, h1 | h1, h2, h3⟩
    · exact Or.inl ⟨mt, h, h1, h2, h3⟩
    · exact Or.inr ⟨mt, h, h1, h2, h3⟩

/-- The facts that hold between a global state and the state after any sequence of party
steps: execution order, slot and progress are unchanged, new messages go to parties of the
execution order with delay `1` or `2`, messages with nonzero delay stay, every party of the
execution order gains the same blocks to be delivered in one or two rounds, and local states
keep their key and tree type while their trees only grow. -/
structure StepFacts (N N' : GlobalState Tx Hash Party AdvState) : Prop where
  order : N'.exec_order = N.exec_order
  time : N'.t_now = N.t_now
  prog : N'.progress = N.progress
  new_buff : ∀ mt ∈ N'.msg_buff, mt ∈ N.msg_buff ∨
    (mt.rcv ∈ N.exec_order ∧ (mt.cd = 1 ∨ mt.cd = 2))
  keep : ∀ mt ∈ N.msg_buff, mt.cd ≠ 0 → mt ∈ N'.msg_buff
  tbd12_eq : ∃ X : List (Block Tx Hash Party), ∀ r ∈ N.exec_order, tbd12 r N' =i tbd12 r N ++ X
  state_back : ∀ q l', N'.state_map q = some l' → ∃ l, N.state_map q = some l ∧
    l'.pk = l.pk ∧ l'.tT = l.tT ∧ ∀ b ∈ l.blocks, b ∈ l'.blocks
  state_fwd : ∀ q l, N.state_map q = some l → ∃ l', N'.state_map q = some l'

theorem StepFacts.refl (N : GlobalState Tx Hash Party AdvState) : StepFacts N N where
  order := rfl
  time := rfl
  prog := rfl
  new_buff := fun _ h => Or.inl h
  keep := fun _ h _ => h
  tbd12_eq := ⟨[], fun _ _ _ => by simp⟩
  state_back := fun _ l h => ⟨l, h, rfl, rfl, fun _ hb => hb⟩
  state_fwd := fun _ l h => ⟨l, h⟩

theorem StepFacts.trans {N1 N2 N3 : GlobalState Tx Hash Party AdvState}
    (h1 : StepFacts N1 N2) (h2 : StepFacts N2 N3) : StepFacts N1 N3 where
  order := h2.order.trans h1.order
  time := h2.time.trans h1.time
  prog := h2.prog.trans h1.prog
  new_buff := fun mt hmt => by
    rcases h2.new_buff mt hmt with h | ⟨hr, hc⟩
    · exact h1.new_buff mt h
    · exact Or.inr ⟨h1.order ▸ hr, hc⟩
  keep := fun mt hmt hc => h2.keep mt (h1.keep mt hmt hc) hc
  tbd12_eq := by
    obtain ⟨X1, hX1⟩ := h1.tbd12_eq
    obtain ⟨X2, hX2⟩ := h2.tbd12_eq
    refine ⟨X1 ++ X2, fun r hr b => ?_⟩
    rw [hX2 r (h1.order ▸ hr) b, List.mem_append, hX1 r hr b]
    simp [or_assoc]
  state_back := fun q l3 h => by
    obtain ⟨l2, h2', hpk2, htT2, hsub2⟩ := h2.state_back q l3 h
    obtain ⟨l1, h1', hpk1, htT1, hsub1⟩ := h1.state_back q l2 h2'
    exact ⟨l1, h1', hpk2.trans hpk1, htT2.trans htT1, fun b hb => hsub2 b (hsub1 b hb)⟩
  state_fwd := fun q l h => by
    obtain ⟨l2, h2'⟩ := h1.state_fwd q l h
    exact h2.state_fwd q l2 h2'

section StepFactsSteps

variable (N : GlobalState Tx Hash Party AdvState)

/-- The blocks to be delivered in one or two rounds after adding the messages `new`,
broadcast to the execution order. -/
theorem tbd12_broadcast {N' : GlobalState Tx Hash Party AdvState}
    (new : List (Message Tx Hash Party × DelayMap Party)) (keep : MessageTuple Tx Hash Party → Prop)
    (hkeep : ∀ mt, mt.cd ≠ 0 → keep mt)
    (hb : ∀ mt, mt ∈ N'.msg_buff ↔ (mt ∈ N.msg_buff ∧ keep mt) ∨
      ∃ mφ ∈ new, ∃ r ∈ N.exec_order, mt = ⟨mφ.1, r, (mφ.2 r).1⟩) :
    ∀ r ∈ N.exec_order, tbd12 r N' =i tbd12 r N ++ new.map (fun mφ => get_block mφ.1) := by
  intro r hr b
  rw [List.mem_append, mem_tbd12, mem_tbd12]
  simp only [hb, List.mem_map]
  constructor
  · rintro ⟨mt, ⟨hmt, _⟩ | ⟨mφ, hmφ, r', hr', rfl⟩, hcd, hrcv, hblk⟩
    · exact Or.inl ⟨mt, hmt, hcd, hrcv, hblk⟩
    · exact Or.inr ⟨mφ, hmφ, hblk⟩
  · rintro (⟨mt, hmt, hcd, hrcv, hblk⟩ | ⟨mφ, hmφ, rfl⟩)
    · exact ⟨mt, Or.inl ⟨hmt, hkeep mt (by rcases hcd with h | h <;> simp [h])⟩, hcd, hrcv,
        hblk⟩
    · refine ⟨⟨mφ.1, r, (mφ.2 r).1⟩, Or.inr ⟨mφ, hmφ, r, hr, rfl⟩, ?_, rfl, rfl⟩
      exact (mφ.2 r).2

theorem bake_step_facts (p : Party) : StepFacts N (party_bake_step_world p N) := by
  obtain ⟨new, hnew⟩ := bake_buff N p
  refine ⟨by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro mt hmt
    rcases (hnew mt).1 hmt with h | ⟨mφ, _, r, hr, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨hr, (mφ.2 r).2⟩
  · intro mt hmt _
    exact (hnew mt).2 (Or.inl hmt)
  · exact ⟨_, tbd12_broadcast N new (fun _ => True) (fun _ _ => trivial)
      (fun mt => by rw [hnew]; simp)⟩
  · intro q l' h
    rw [bake_state_map] at h
    by_cases hq : q = p
    · subst hq
      rw [Function.update_self] at h
      unfold bake_local at h
      cases hl : N.state_map q with
      | none => simp [hl] at h
      | some l =>
        rw [hl] at h
        by_cases hc : is_corrupt q
        · simp only [hc, ite_true, Option.some.injEq] at h
          subst h
          exact ⟨_, rfl, rfl, rfl, fun _ hb => hb⟩
        · simp only [hc, Bool.false_eq_true, ite_false, Option.some.injEq] at h
          subst h
          refine ⟨l, rfl, honest_bake_pk _ _ _, honest_bake_tT _ _ _, fun b hb => ?_⟩
          exact (honest_bake_blocks _ _ _ b).2 (List.mem_append_left _ hb)
    · rw [Function.update_of_ne hq] at h
      exact ⟨l', h, rfl, rfl, fun _ hb => hb⟩
  · intro q l h
    rw [bake_state_map]
    by_cases hq : q = p
    · subst hq
      rw [Function.update_self]
      unfold bake_local
      rw [h]
      by_cases hc : is_corrupt q <;> simp [hc]
    · rw [Function.update_of_ne hq]
      exact ⟨l, h⟩

theorem rcv_step_facts (p : Party) : StepFacts N (party_rcv_step_world p N) := by
  obtain ⟨new, hnew⟩ := rcv_buff N p
  refine ⟨by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro mt hmt
    rcases (hnew mt).1 hmt with h | ⟨mφ, _, r, hr, rfl⟩
    · exact Or.inl h.1
    · exact Or.inr ⟨hr, (mφ.2 r).2⟩
  · intro mt hmt hc
    exact (hnew mt).2 (Or.inl ⟨hmt, fun h => hc h.1⟩)
  · exact ⟨_, tbd12_broadcast N new (fun mt => ¬ (mt.cd = 0 ∧ mt.rcv = p ∧
      (N.state_map p).isSome)) (fun mt hc h => hc h.1) hnew⟩
  · intro q l' h
    rw [rcv_state_map] at h
    by_cases hq : q = p
    · subst hq
      rw [Function.update_self] at h
      unfold rcv_local at h
      cases hl : N.state_map q with
      | none => simp [hl] at h
      | some l =>
        rw [hl] at h
        by_cases hc : is_corrupt q
        · simp only [hc, ite_true, Option.some.injEq] at h
          subst h
          exact ⟨_, rfl, rfl, rfl, fun _ hb => hb⟩
        · simp only [hc, Bool.false_eq_true, ite_false, Option.some.injEq] at h
          subst h
          obtain ⟨hpk, htT⟩ := foldr_process_msg_pk ((collect_zero_pairs q N).map
            MessageTuple.msg) l
          refine ⟨l, rfl, hpk, htT, fun b hb => ?_⟩
          exact (foldr_process_msg_blocks _ _ b).2 (List.mem_append_left _ hb)
    · rw [Function.update_of_ne hq] at h
      exact ⟨l', h, rfl, rfl, fun _ hb => hb⟩
  · intro q l h
    rw [rcv_state_map]
    by_cases hq : q = p
    · subst hq
      rw [Function.update_self]
      unfold rcv_local
      rw [h]
      by_cases hc : is_corrupt q <;> simp [hc]
    · rw [Function.update_of_ne hq]
      exact ⟨l, h⟩

theorem bakes_step_facts (ps : List Party) :
    StepFacts N (ps.foldr party_bake_step_world N) := by
  induction ps with
  | nil => exact StepFacts.refl N
  | cons q qs ih => exact ih.trans (bake_step_facts _ q)

theorem rcvs_step_facts (ps : List Party) :
    StepFacts N (ps.foldr party_rcv_step_world N) := by
  induction ps with
  | nil => exact StepFacts.refl N
  | cons q qs ih => exact ih.trans (rcv_step_facts _ q)

/-- After every party of `ps` with a local state has received, no message with delay `0` is
addressed to a party of `ps`. -/
theorem rcvs_zero (ps : List Party) (hs : ∀ q ∈ ps, (N.state_map q).isSome) :
    ∀ mt ∈ (ps.foldr party_rcv_step_world N).msg_buff, mt.cd = 0 → mt.rcv ∉ ps := by
  induction ps with
  | nil => simp
  | cons q qs ih =>
    intro mt hmt hcd
    obtain ⟨new, hnew⟩ := rcv_buff (qs.foldr party_rcv_step_world N) q
    simp only [List.foldr_cons] at hmt
    rcases (hnew mt).1 hmt with ⟨hmt', hnot⟩ | ⟨mφ, _, r, _, rfl⟩
    · have hq : ((qs.foldr party_rcv_step_world N).state_map q).isSome := by
        obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (hs q List.mem_cons_self)
        obtain ⟨l', hl'⟩ := (rcvs_step_facts N qs).state_fwd q l hl
        simp [hl']
      have h1 : mt.rcv ≠ q := fun h => hnot ⟨hcd, h, hq⟩
      have h2 := ih (fun q' hq' => hs q' (List.mem_cons_of_mem _ hq')) mt hmt' hcd
      simp [h1, h2]
    · have h0 : (mφ.2 r).1 = 0 := hcd
      rcases (mφ.2 r).2 with h | h <;> omega

end StepFactsSteps

/-! ## Invariants of reachable states -/

/-- The invariant of reachable states. It collects the facts that `Properties/CG.v` proves
separately by induction over executions (`perm_exec_order0`, `has_state_initP`,
`pk_preserved`, `only_msgs_for_init`, `all_msgs_leq_than_2_delayed`, `all_msgs_delivered`,
`tbd2_at_ready_is_nil`, `lt_0_time`), together with the tree type of each local state. -/
structure Inv (N : GlobalState Tx Hash Party AdvState) : Prop where
  perm : N.exec_order.Perm (InitParties : List Party)
  state_init : ∀ p, (N.state_map p).isSome ↔ p ∈ (InitParties : List Party)
  pk : ∀ p l, N.state_map p = some l → l.pk = p
  tT : ∀ p l, N.state_map p = some l → l.tT = TreeTypeMap (AdvState := AdvState) p
  rcv_init : ∀ mt ∈ N.msg_buff, mt.rcv ∈ (InitParties : List Party)
  cd_le : ∀ mt ∈ N.msg_buff, mt.cd ≤ 2
  not_ready : N.progress ≠ .Ready → ∀ mt ∈ N.msg_buff, mt.cd ≠ 0
  ready : N.progress = .Ready → ∀ mt ∈ N.msg_buff, mt.cd ≤ 1
  time : 0 < N.t_now

theorem inv_N0 : Inv (N0 AdvState : GlobalState Tx Hash Party AdvState) where
  perm := List.Perm.refl _
  state_init := fun p => by by_cases h : p ∈ (InitParties : List Party) <;> simp [N0, h]
  pk := fun p l h => by
    by_cases hp : p ∈ (InitParties : List Party) <;> simp [N0, hp] at h
    subst h; rfl
  tT := fun p l h => by
    by_cases hp : p ∈ (InitParties : List Party) <;> simp [N0, hp] at h
    subst h; rfl
  rcv_init := by simp [N0]
  cd_le := by simp [N0]
  not_ready := by simp [N0]
  ready := by simp [N0]
  time := by simp [N0]

theorem Inv.state_some {N : GlobalState Tx Hash Party AdvState} (hN : Inv N) {p : Party}
    (hp : p ∈ N.exec_order) : ∃ l, N.state_map p = some l :=
  Option.isSome_iff_exists.1 ((hN.state_init p).2 (hN.perm.mem_iff.1 hp))

theorem Inv.mem_order {N : GlobalState Tx Hash Party AdvState} (hN : Inv N) {p : Party}
    {l : LocalState Tx Hash Party} (h : N.state_map p = some l) : p ∈ N.exec_order :=
  hN.perm.mem_iff.2 ((hN.state_init p).1 (by simp [h]))

theorem Inv.of_step_facts {N N1 : GlobalState Tx Hash Party AdvState} (hN : Inv N)
    (hF : StepFacts N N1) (P : Progress)
    (hnr : P ≠ .Ready → ∀ mt ∈ N1.msg_buff, mt.cd ≠ 0)
    (hr : P = .Ready → ∀ mt ∈ N1.msg_buff, mt.cd ≤ 1) : Inv { N1 with progress := P } where
  perm := hF.order ▸ hN.perm
  state_init := fun p => by
    rw [← hN.state_init p]
    constructor
    · intro h
      obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨l, hl, -⟩ := hF.state_back p l' hl'
      simp [hl]
    · intro h
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨l', hl'⟩ := hF.state_fwd p l hl
      simp [hl']
  pk := fun p l' h => by
    obtain ⟨l, hl, hpk, -⟩ := hF.state_back p l' h
    exact hpk.trans (hN.pk p l hl)
  tT := fun p l' h => by
    obtain ⟨l, hl, -, htT, -⟩ := hF.state_back p l' h
    exact htT.trans (hN.tT p l hl)
  rcv_init := fun mt hmt => by
    rcases hF.new_buff mt hmt with h | ⟨h, -⟩
    · exact hN.rcv_init mt h
    · exact hN.perm.mem_iff.1 h
  cd_le := fun mt hmt => by
    rcases hF.new_buff mt hmt with h | ⟨-, h | h⟩
    · exact hN.cd_le mt h
    all_goals omega
  not_ready := hnr
  ready := hr
  time := hF.time ▸ hN.time

theorem Inv.step {N N' : GlobalState Tx Hash Party AdvState} (hN : Inv N) (h : N ⤳ N') :
    Inv N' := by
  cases h with
  | Deliver hp =>
    have hF := rcvs_step_facts N N.exec_order
    refine hN.of_step_facts hF _ ?_ (by simp)
    intro _ mt hmt hcd
    have hs : ∀ q ∈ N.exec_order, (N.state_map q).isSome := fun q hq => by
      obtain ⟨l, hl⟩ := hN.state_some hq
      simp [hl]
    have h1 := rcvs_zero N N.exec_order hs mt hmt hcd
    rcases hF.new_buff mt hmt with h | ⟨h, -⟩
    · exact h1 (hN.perm.mem_iff.2 (hN.rcv_init mt h))
    · exact h1 h
  | Bake hp =>
    have hF := bakes_step_facts N N.exec_order
    refine hN.of_step_facts hF _ ?_ (by simp)
    intro _ mt hmt
    rcases hF.new_buff mt hmt with h | ⟨-, h | h⟩
    · exact hN.not_ready (by simp [hp]) mt h
    all_goals omega
  | NextRound hp =>
    refine ⟨hN.perm, hN.state_init, hN.pk, hN.tT, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [inc_round, round_tick, List.mem_map]
      rintro _ ⟨mt, hmt, rfl⟩
      exact hN.rcv_init mt hmt
    · simp only [inc_round, round_tick, List.mem_map]
      rintro _ ⟨mt, hmt, rfl⟩
      have := hN.cd_le mt hmt
      simp only; omega
    · intro h; simp at h
    · simp only [inc_round, round_tick, List.mem_map]
      rintro _ _ ⟨mt, hmt, rfl⟩
      have := hN.cd_le mt hmt
      simp only; omega
    · simp only [inc_round]; omega
  | PermParties ps hps =>
    exact ⟨hps.symm.trans hN.perm, hN.state_init, hN.pk, hN.tT, hN.rcv_init, hN.cd_le,
      hN.not_ready, hN.ready, hN.time⟩
  | PermMsgs mb hmb =>
    refine ⟨hN.perm, hN.state_init, hN.pk, hN.tT, fun mt h => hN.rcv_init mt (hmb.mem_iff.2 h),
      fun mt h => hN.cd_le mt (hmb.mem_iff.2 h), fun hp mt h => hN.not_ready hp mt (hmb.mem_iff.2 h),
      fun hp mt h => hN.ready hp mt (hmb.mem_iff.2 h), hN.time⟩

/-- Every state reachable from `N0` satisfies the invariant `Inv`. -/
theorem reachable_inv {N : GlobalState Tx Hash Party AdvState} (h : N0 AdvState ⇓ N) : Inv N := by
  induction h with
  | refl => exact inv_N0
  | tail _ hs ih => exact ih.step hs

/-- In a reachable state the execution order has no duplicates (`uniq_exec_order`). -/
theorem uniq_exec_order (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hN : Inv N) : N.exec_order.Nodup :=
  hN.perm.nodup_iff.2 hu


end CatCryptCore.Consensus.PoSNSB

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Steps

/-!
# PoS-NSB: invariants of reachable states and the flow of honest blocks

This file ports the second part of the preliminaries of the chain-growth proof in
`Properties/CG.v` of PoS-NSB (Thomsen and Spitters, CSF 2021): the steps of a single party
within a round, the blocks `tbd n p N` to be delivered to `p` in `n` rounds, and the lemmas
that relate the trees of honest parties.

## Main results

* `rcvs_own`, `bakes_own`, `bakes_own_msgs`: within a round, an honest party's state after
  all parties acted is its state after its own step, and the block it bakes reaches every
  party of the execution order with delay `1`.
* `block_equality_inv`: in a reachable state, the blocks of two honest parties together with
  the blocks in transit to them coincide.
* `at_ready_subset`: in a reachable `Ready` state, the tree of an honest party is contained
  in the tree of any other honest party together with the blocks delivered to it now.
* `honest_tree_subset`: the honest tree at the start of a round is contained in the tree of
  every honest party once the round's messages are delivered.
* `monotone_honest_tree`: the honest tree only grows along an execution.

The proofs follow the Coq development and use the invariant `Inv` of `Steps.lean` for the
facts about message delays that the Coq development proves by separate inductions. Phases
(three per slot) replace the lemmas `zero_time_progress_delivered` and
`zero_time_progress_baked`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-! ## The steps of a single party within a round -/

section SingleParty

variable (N : GlobalState Tx Hash Party AdvState)

theorem rcv_state_ne {p q : Party} (h : q ≠ p) :
    (party_rcv_step_world q N).state_map p = N.state_map p := by
  rw [rcv_state_map, Function.update_of_ne h.symm]

theorem bake_state_ne {p q : Party} (h : q ≠ p) :
    (party_bake_step_world q N).state_map p = N.state_map p := by
  rw [bake_state_map, Function.update_of_ne h.symm]

theorem rcv_tbd0_ne {p q : Party} (h : q ≠ p) :
    tbd 0 p (party_rcv_step_world q N) =i tbd 0 p N := by
  obtain ⟨new, hnew⟩ := rcv_buff N q
  intro b
  simp only [mem_tbd, hnew]
  constructor
  · rintro ⟨mt, ⟨hmt, -⟩ | ⟨mφ, -, r, -, rfl⟩, hcd, hrcv, hblk⟩
    · exact ⟨mt, hmt, hcd, hrcv, hblk⟩
    · have h0 : (mφ.2 r).1 = 0 := hcd
      rcases (mφ.2 r).2 with h' | h' <;> omega
  · rintro ⟨mt, hmt, hcd, hrcv, hblk⟩
    refine ⟨mt, Or.inl ⟨hmt, fun ⟨_, h', _⟩ => h (h'.symm.trans hrcv)⟩, hcd, hrcv, hblk⟩

theorem rcvs_state_notin {p : Party} {ps : List Party} (hp : p ∉ ps) :
    (ps.foldr party_rcv_step_world N).state_map p = N.state_map p ∧
      tbd 0 p (ps.foldr party_rcv_step_world N) =i tbd 0 p N := by
  induction ps with
  | nil => exact ⟨rfl, fun _ => Iff.rfl⟩
  | cons q qs ih =>
    have hq : q ≠ p := fun h => hp (h ▸ List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := ih (fun h => hp (List.mem_cons_of_mem _ h))
    refine ⟨(rcv_state_ne _ hq).trans ih1, fun b => (rcv_tbd0_ne _ hq b).trans (ih2 b)⟩

theorem bakes_state_notin {p : Party} {ps : List Party} (hp : p ∉ ps) :
    (ps.foldr party_bake_step_world N).state_map p = N.state_map p := by
  induction ps with
  | nil => rfl
  | cons q qs ih =>
    have hq : q ≠ p := fun h => hp (h ▸ List.mem_cons_self)
    exact (bake_state_ne _ hq).trans (ih (fun h => hp (List.mem_cons_of_mem _ h)))

/-- The receiving step of an honest party adds the blocks delivered to it
(`delivery_blocktree`). -/
theorem delivery_blocktree {p : Party} {l : LocalState Tx Hash Party}
    (hh : is_honest p = true) (hl : N.state_map p = some l) :
    ∃ l', (party_rcv_step_world p N).state_map p = some l' ∧ l'.blocks =i l.blocks ++ tbd 0 p N := by
  rw [rcv_state_map, Function.update_self]
  have hc : is_corrupt p = false := by
    have := honest_not_corrupt p; rw [hh] at this; simpa using this.symm
  refine ⟨((collect_zero_pairs p N).map MessageTuple.msg).foldr process_msg l,
    by simp [rcv_local, hl, hc], fun b => ?_⟩
  rw [foldr_process_msg_blocks]
  simp [tbd, collect_zero_pairs, List.map_map, Function.comp_def]

/-- Within the receiving phase, the state of an honest party `p` after all parties of `ps`
received is its state after its own receiving step (`single_party_rcv_step_state`). -/
theorem rcvs_own {p : Party} {l : LocalState Tx Hash Party} {ps : List Party} (hu : ps.Nodup)
    (hp : p ∈ ps) (hh : is_honest p = true) (hl : N.state_map p = some l) :
    ∃ l', (ps.foldr party_rcv_step_world N).state_map p = some l' ∧
      l'.blocks =i l.blocks ++ tbd 0 p N := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rw [List.nodup_cons] at hu
    simp only [List.foldr_cons]
    by_cases hq : q = p
    · subst hq
      obtain ⟨h1, h2⟩ := rcvs_state_notin N hu.1
      obtain ⟨l', hl', hb⟩ := delivery_blocktree _ hh (h1.trans hl)
      refine ⟨l', hl', fun b => ?_⟩
      rw [hb b, List.mem_append, List.mem_append, h2 b]
    · obtain ⟨l', hl', hb⟩ := ih hu.2 ((List.mem_cons.1 hp).resolve_left (Ne.symm hq))
      exact ⟨l', (rcv_state_ne _ hq).trans hl', hb⟩

/-- Within the baking phase, the state of an honest party `p` after all parties of `ps` baked
is its state after its own baking step (`single_party_bake_step_state`). -/
theorem bakes_own {p : Party} {l : LocalState Tx Hash Party} {ps : List Party} (hu : ps.Nodup)
    (hp : p ∈ ps) (hh : is_honest p = true) (hl : N.state_map p = some l) :
    (ps.foldr party_bake_step_world N).state_map p =
      some (honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p) l).2 := by
  have hc : is_corrupt p = false := by
    have := honest_not_corrupt p; rw [hh] at this; simpa using this.symm
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rw [List.nodup_cons] at hu
    simp only [List.foldr_cons]
    by_cases hq : q = p
    · subst hq
      rw [bake_state_map, Function.update_self]
      simp [bake_local, bakes_state_notin N hu.1, hl, hc,
        (bakes_step_facts N qs).time]
    · rw [bake_state_ne _ hq]
      exact ih hu.2 ((List.mem_cons.1 hp).resolve_left (Ne.symm hq))

theorem bake_own_msgs {p : Party} {l : LocalState Tx Hash Party}
    (hh : is_honest p = true) (hl : N.state_map p = some l) :
    ∀ m ∈ (honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p) l).1,
      ∀ r ∈ N.exec_order, (⟨m, r, 1⟩ : MessageTuple Tx Hash Party) ∈
        (party_bake_step_world p N).msg_buff := by
  have hc : is_corrupt p = false := by
    have := honest_not_corrupt p; rw [hh] at this; simpa using this.symm
  intro m hm r hr
  unfold party_bake_step_world
  simp only [hl, hc, Bool.not_false, ite_true]
  rw [mem_flood_msgs]
  exact Or.inr ⟨m, hm, r, by simpa [upd_local] using hr, rfl⟩

/-- The messages an honest party sends in its baking step reach every party of the
execution order with delay `1` by the end of the baking phase. -/
theorem bakes_own_msgs {p : Party} {l : LocalState Tx Hash Party} {ps : List Party}
    (hu : ps.Nodup) (hp : p ∈ ps) (hh : is_honest p = true) (hl : N.state_map p = some l) :
    ∀ m ∈ (honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p) l).1,
      ∀ r ∈ N.exec_order, (⟨m, r, 1⟩ : MessageTuple Tx Hash Party) ∈
        (ps.foldr party_bake_step_world N).msg_buff := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rw [List.nodup_cons] at hu
    simp only [List.foldr_cons]
    intro m hm r hr
    by_cases hq : q = p
    · subst hq
      have hF := bakes_step_facts N qs
      have := bake_own_msgs (qs.foldr party_bake_step_world N) hh
        ((bakes_state_notin N hu.1).trans hl)
      rw [hF.time] at this
      exact this m hm r (hF.order ▸ hr)
    · exact (bake_step_facts _ q).keep _
        (ih hu.2 ((List.mem_cons.1 hp).resolve_left (Ne.symm hq)) m hm r hr) one_ne_zero

end SingleParty

/-! ## Blocks in transit -/

theorem tbd0_nil {N : GlobalState Tx Hash Party AdvState} (hN : Inv N)
    (hp : N.progress ≠ .Ready) (p : Party) : ∀ b, b ∉ tbd 0 p N := by
  intro b hb
  obtain ⟨mt, hmt, hcd, -⟩ := mem_tbd.1 hb
  exact hN.not_ready hp mt hmt hcd

theorem tbd2_nil {N : GlobalState Tx Hash Party AdvState} (hN : Inv N)
    (hp : N.progress = .Ready) (p : Party) : ∀ b, b ∉ tbd 2 p N := by
  intro b hb
  obtain ⟨mt, hmt, hcd, -⟩ := mem_tbd.1 hb
  have := hN.ready hp mt hmt
  omega

theorem tbd_perm {N : GlobalState Tx Hash Party AdvState} {mb : MessagePool Tx Hash Party}
    (h : N.msg_buff.Perm mb) (n : ℕ) (p : Party) :
    tbd n p { N with msg_buff := mb } =i tbd n p N := by
  intro b
  simp only [mem_tbd]
  exact exists_congr fun mt => and_congr_left' h.mem_iff.symm

/-- After the round tick, the blocks to be delivered in `n` rounds are those that were to be
delivered in `n + 1` rounds (`inc_tbd_dec`). -/
theorem tbd_next_round {N : GlobalState Tx Hash Party AdvState} (hN : Inv N)
    (hp : N.progress = .Baked) (n : ℕ) (p : Party) :
    tbd n p { inc_round (round_tick N) with progress := .Ready } =i tbd (n + 1) p N := by
  intro b
  simp only [mem_tbd, inc_round, round_tick, List.mem_map]
  constructor
  · rintro ⟨_, ⟨mt, hmt, rfl⟩, hcd, hrcv, hblk⟩
    have := hN.not_ready (by simp [hp]) mt hmt
    exact ⟨mt, hmt, by simp only at hcd; omega, hrcv, hblk⟩
  · rintro ⟨mt, hmt, hcd, hrcv, hblk⟩
    exact ⟨_, ⟨mt, hmt, rfl⟩, by simp only; omega, hrcv, hblk⟩

@[simp] theorem tbd_upd_progress (n : ℕ) (p : Party) (N : GlobalState Tx Hash Party AdvState)
    (P : Progress) : tbd n p { N with progress := P } = tbd n p N := rfl

@[simp] theorem tbd12_upd_progress (p : Party) (N : GlobalState Tx Hash Party AdvState)
    (P : Progress) : tbd12 p { N with progress := P } = tbd12 p N := rfl

/-- The view of honest party `p` with state `l`: its blocks and the blocks in transit to
it. -/
def view (p : Party) (l : LocalState Tx Hash Party) (N : GlobalState Tx Hash Party AdvState) :
    List (Block Tx Hash Party) :=
  l.blocks ++ tbd 0 p N ++ tbd12 p N

/-- In a reachable state, any two honest parties have the same blocks once the blocks in
transit to them are counted (`block_equality_inv`). -/
theorem block_equality_inv (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) :
    ∀ p p' l l', is_honest p = true → is_honest p' = true → N.state_map p = some l →
      N.state_map p' = some l' → view p l N =i view p' l' N := by
  induction hR with
  | refl =>
    intro p p' l l' _ _ hl hl' b
    have e : ∀ q (k : LocalState Tx Hash Party),
        (N0 AdvState : GlobalState Tx Hash Party AdvState).state_map q = some k →
          (b ∈ view q k (N0 AdvState) ↔ b = GenesisBlock) := by
      intro q k hk
      by_cases hq : q ∈ (InitParties : List Party) <;> simp [N0, hq] at hk
      subst hk
      simp [view, tbd12, tbd, N0, init_local, LocalState.blocks,
        (TreeTypeMap (AdvState := AdvState) q).all_tree0]
    rw [e p l hl, e p' l' hl']
  | tail hR' hs ih =>
    rename_i N1 N2
    have hN := reachable_inv hR'
    have hN2 := hN.step hs
    cases hs with
    | Deliver hp =>
      intro p p' l l' hh hh' hl hl'
      have hF := rcvs_step_facts N1 N1.exec_order
      have key : ∀ q k, is_honest q = true →
          (N1.exec_order.foldr party_rcv_step_world N1).state_map q = some k → ∃ k₀,
          N1.state_map q = some k₀ ∧ view q k { N1.exec_order.foldr party_rcv_step_world N1 with
            progress := .Delivered } =i view q k₀ N1 ++ hF.tbd12_eq.choose := by
        intro q k hq hk
        obtain ⟨k₀, hk₀, -⟩ := hF.state_back q k hk
        obtain ⟨k', hk', hb⟩ := rcvs_own N1 (uniq_exec_order hu hN) (hN.mem_order hk₀) hq hk₀
        have : k' = k := Option.some.inj (hk'.symm.trans hk)
        subst this
        refine ⟨k₀, hk₀, fun b => ?_⟩
        have h0 := tbd0_nil hN2 (by simp) q b
        have h12 := hF.tbd12_eq.choose_spec q (hN.mem_order hk₀) b
        simp only [view, List.mem_append] at h0 h12 ⊢
        simp only [tbd_upd_progress, tbd12_upd_progress] at h0 ⊢
        rw [hb b, List.mem_append, h12]
        tauto
      obtain ⟨k, hk, e⟩ := key p l hh hl
      obtain ⟨k', hk', e'⟩ := key p' l' hh' hl'
      intro b
      rw [e b, e' b, List.mem_append, List.mem_append, ih p p' k k' hh hh' hk hk' b]
    | Bake hp =>
      intro p p' l l' hh hh' hl hl'
      have hF := bakes_step_facts N1 N1.exec_order
      have hnr1 : N1.progress ≠ .Ready := by simp [hp]
      have key : ∀ q k, is_honest q = true →
          (N1.exec_order.foldr party_bake_step_world N1).state_map q = some k → ∃ k₀,
          N1.state_map q = some k₀ ∧ view q k { N1.exec_order.foldr party_bake_step_world N1 with
            progress := .Baked } =i view q k₀ N1 ++ hF.tbd12_eq.choose := by
        intro q k hq hk
        obtain ⟨k₀, hk₀, -⟩ := hF.state_back q k hk
        have hqo := hN.mem_order hk₀
        have hown := bakes_own N1 (uniq_exec_order hu hN) hqo hq hk₀
        have : (honest_bake N1.t_now (TxSelection (Hash := Hash) (AdvState := AdvState)
            N1.t_now q) k₀).2 = k := Option.some.inj (hown.symm.trans hk)
        subst this
        have hmsgs := bakes_own_msgs N1 (uniq_exec_order hu hN) hqo hq hk₀
        refine ⟨k₀, hk₀, fun b => ?_⟩
        have h0 := tbd0_nil hN2 (by simp) q b
        have h0' := tbd0_nil hN hnr1 q b
        have h12 := hF.tbd12_eq.choose_spec q hqo b
        have hY : b ∈ (honest_bake N1.t_now (TxSelection (Hash := Hash) (AdvState := AdvState)
            N1.t_now q) k₀).1.map get_block →
            b ∈ tbd12 q (List.foldr party_bake_step_world N1 N1.exec_order) := by
          rw [List.mem_map]
          rintro ⟨m, hm, rfl⟩
          exact mem_tbd12.2 ⟨_, hmsgs m hm q hqo, Or.inl rfl, rfl, rfl⟩
        simp only [view, List.mem_append] at h0 h0' h12 hY ⊢
        simp only [tbd_upd_progress, tbd12_upd_progress] at h0 ⊢
        rw [honest_bake_blocks _ _ _ b, List.mem_append]
        tauto
      obtain ⟨k, hk, e⟩ := key p l hh hl
      obtain ⟨k', hk', e'⟩ := key p' l' hh' hl'
      intro b
      rw [e b, e' b, List.mem_append, List.mem_append, ih p p' k k' hh hh' hk hk' b]
    | NextRound hp =>
      intro p p' l l' hh hh' hl hl'
      have key : ∀ q k, N1.state_map q = some k →
          view q k { inc_round (round_tick N1) with progress := .Ready } =i view q k N1 := by
        intro q k _ b
        have h0 := tbd_next_round hN hp 0 q b
        have h1 := tbd_next_round hN hp 1 q b
        have h2 := tbd_next_round hN hp 2 q b
        have h0' := tbd0_nil hN (by simp [hp]) q b
        have h3 : b ∉ tbd 3 q N1 := by
          intro hb
          obtain ⟨mt, hmt, hcd, -⟩ := mem_tbd.1 hb
          have := hN.cd_le mt hmt
          omega
        simp only [view, tbd12, List.mem_append] at h0 h1 h2 h0' ⊢
        rw [h0, h1, h2]
        tauto
      intro b
      rw [key p l hl b, key p' l' hl' b]
      exact ih p p' l l' hh hh' hl hl' b
    | PermParties ps hps =>
      exact ih
    | PermMsgs mb hmb =>
      intro p p' l l' hh hh' hl hl' b
      have e : ∀ q k, view q k { N1 with msg_buff := mb } =i view q k N1 := by
        intro q k b
        simp only [view, tbd12, List.mem_append]
        rw [tbd_perm hmb 0 q b, tbd_perm hmb 1 q b, tbd_perm hmb 2 q b]
      rw [e p l b, e p' l' b]
      exact ih p p' l l' hh hh' hl hl' b

/-! ## Trees of honest parties within a round -/

theorem mem_tbd1_keep {N N' : GlobalState Tx Hash Party AdvState} (hF : StepFacts N N')
    {p : Party} {b : Block Tx Hash Party} (hb : b ∈ tbd 1 p N) : b ∈ tbd 1 p N' := by
  obtain ⟨mt, hmt, hcd, hrcv, hblk⟩ := mem_tbd.1 hb
  exact mem_tbd.2 ⟨mt, hF.keep mt hmt (by omega), hcd, hrcv, hblk⟩

/-- After delivery, the tree of an honest party is contained in the tree of any other honest
party together with the blocks to be delivered to it in one round (`at_delivered_subset`). -/
theorem at_delivered_subset (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) :
    N.progress = .Delivered → ∀ p p' l l', is_honest p = true → is_honest p' = true →
      N.state_map p = some l → N.state_map p' = some l' →
        ∀ b ∈ l.blocks, b ∈ l'.blocks ++ tbd 1 p' N := by
  induction hR with
  | refl => intro h; simp [N0] at h
  | tail hR' hs ih =>
    rename_i N1 N2
    have hN := reachable_inv hR'
    cases hs with
    | Deliver hp =>
      intro _ p p' l l' hh hh' hl hl' b hb
      have hF := rcvs_step_facts N1 N1.exec_order
      obtain ⟨k, hk, -⟩ := hF.state_back p l hl
      obtain ⟨k', hk', -⟩ := hF.state_back p' l' hl'
      obtain ⟨m, hm, hmb⟩ := rcvs_own N1 (uniq_exec_order hu hN) (hN.mem_order hk) hh hk
      obtain ⟨m', hm', hmb'⟩ := rcvs_own N1 (uniq_exec_order hu hN) (hN.mem_order hk') hh' hk'
      have e1 : m = l := Option.some.inj (hm.symm.trans hl)
      have e2 : m' = l' := Option.some.inj (hm'.symm.trans hl')
      subst e1 e2
      have heq := block_equality_inv hu hR' p p' k k' hh hh' hk hk' b
      have h2 := tbd2_nil hN hp p' b
      have hb' := (hmb b).1 hb
      simp only [view, tbd12, List.mem_append] at heq hb'
      rw [List.mem_append, hmb' b, List.mem_append, tbd_upd_progress]
      have h1 : b ∈ tbd 1 p' N1 → b ∈ tbd 1 p'
          (N1.exec_order.foldr party_rcv_step_world N1) := mem_tbd1_keep hF
      tauto
    | Bake hp => intro h; simp at h
    | NextRound hp => intro h; simp at h
    | PermParties ps hps => exact ih
    | PermMsgs mb hmb =>
      intro hD p p' l l' hh hh' hl hl' b hb
      have := ih hD p p' l l' hh hh' hl hl' b hb
      rw [List.mem_append] at this ⊢
      rwa [tbd_perm hmb 1 p' b]

/-- After baking, the tree of an honest party is contained in the tree of any other honest
party together with the blocks to be delivered to it in one round (`at_bake_subset`). -/
theorem at_bake_subset (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) :
    N.progress = .Baked → ∀ p p' l l', is_honest p = true → is_honest p' = true →
      N.state_map p = some l → N.state_map p' = some l' →
        ∀ b ∈ l.blocks, b ∈ l'.blocks ++ tbd 1 p' N := by
  induction hR with
  | refl => intro h; simp [N0] at h
  | tail hR' hs ih =>
    rename_i N1 N2
    have hN := reachable_inv hR'
    cases hs with
    | Bake hp =>
      intro _ p p' l l' hh hh' hl hl' b hb
      have hF := bakes_step_facts N1 N1.exec_order
      obtain ⟨k, hk, -⟩ := hF.state_back p l hl
      obtain ⟨k', hk', -⟩ := hF.state_back p' l' hl'
      have hpo := hN.mem_order hk
      have hpo' := hN.mem_order hk'
      have hown := bakes_own N1 (uniq_exec_order hu hN) hpo hh hk
      have hown' := bakes_own N1 (uniq_exec_order hu hN) hpo' hh' hk'
      have e1 := Option.some.inj (hown.symm.trans hl)
      have e2 := Option.some.inj (hown'.symm.trans hl')
      subst e1 e2
      have hmsgs := bakes_own_msgs N1 (uniq_exec_order hu hN) hpo hh hk
      rw [List.mem_append, tbd_upd_progress]
      rcases List.mem_append.1 ((honest_bake_blocks _ _ _ b).1 hb) with hb | hb
      · rcases List.mem_append.1 (at_delivered_subset hu hR' hp p p' k k' hh hh' hk hk' b hb)
          with h | h
        · exact Or.inl ((honest_bake_blocks _ _ _ b).2 (List.mem_append_left _ h))
        · exact Or.inr (mem_tbd1_keep hF h)
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
        exact Or.inr (mem_tbd.2 ⟨_, hmsgs m hm p' hpo', rfl, rfl, rfl⟩)
    | Deliver hp => intro h; simp at h
    | NextRound hp => intro h; simp at h
    | PermParties ps hps => exact ih
    | PermMsgs mb hmb =>
      intro hD p p' l l' hh hh' hl hl' b hb
      have := ih hD p p' l l' hh hh' hl hl' b hb
      rw [List.mem_append] at this ⊢
      rwa [tbd_perm hmb 1 p' b]

/-- At the start of a round, the tree of an honest party is contained in the tree of any
other honest party together with the blocks delivered to it in this round
(`at_ready_subset`). -/
theorem at_ready_subset (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) :
    N.progress = .Ready → ∀ p p' l l', is_honest p = true → is_honest p' = true →
      N.state_map p = some l → N.state_map p' = some l' →
        ∀ b ∈ l.blocks, b ∈ l'.blocks ++ tbd 0 p' N := by
  induction hR with
  | refl =>
    intro _ p p' l l' _ _ hl hl' b hb
    have e : ∀ q (k : LocalState Tx Hash Party),
        (N0 AdvState : GlobalState Tx Hash Party AdvState).state_map q = some k →
          (b ∈ k.blocks ↔ b = GenesisBlock) := by
      intro q k hk
      by_cases hq : q ∈ (InitParties : List Party) <;> simp [N0, hq] at hk
      subst hk
      simp [init_local, LocalState.blocks, (TreeTypeMap (AdvState := AdvState) q).all_tree0]
    exact List.mem_append_left _ ((e p' l' hl').2 ((e p l hl).1 hb))
  | tail hR' hs ih =>
    rename_i N1 N2
    have hN := reachable_inv hR'
    cases hs with
    | NextRound hp =>
      intro _ p p' l l' hh hh' hl hl' b hb
      have := at_bake_subset hu hR' hp p p' l l' hh hh' hl hl' b hb
      rw [List.mem_append] at this ⊢
      rwa [tbd_next_round hN hp 0 p' b]
    | Deliver hp => intro h; simp at h
    | Bake hp => intro h; simp at h
    | PermParties ps hps => exact ih
    | PermMsgs mb hmb =>
      intro hD p p' l l' hh hh' hl hl' b hb
      have := ih hD p p' l l' hh hh' hl hl' b hb
      rw [List.mem_append] at this ⊢
      rwa [tbd_perm hmb 0 p' b]

/-! ## Phases, time and monotonicity -/

/-- The phase of a state: three phases per slot. -/
def phase (N : GlobalState Tx Hash Party AdvState) : ℕ :=
  3 * N.t_now + match N.progress with
    | .Ready => 0
    | .Delivered => 1
    | .Baked => 2

theorem phase_lt (N : GlobalState Tx Hash Party AdvState) : phase N < 3 * N.t_now + 3 := by
  unfold phase; split <;> omega

theorem le_phase (N : GlobalState Tx Hash Party AdvState) : 3 * N.t_now ≤ phase N := by
  unfold phase; split <;> omega

/-- A step either advances the phase by one, or keeps the phase, the local states, the slot,
the progress and the execution order up to permutation. -/
theorem step_phase {N N' : GlobalState Tx Hash Party AdvState} (h : N ⤳ N') :
    phase N' = phase N + 1 ∨ (phase N' = phase N ∧ N'.state_map = N.state_map ∧
      N'.exec_order.Perm N.exec_order ∧ N'.t_now = N.t_now ∧ N'.progress = N.progress) := by
  cases h with
  | Deliver hp =>
    left
    have := (rcvs_step_facts N N.exec_order).time
    simp only [phase, hp, this]
  | Bake hp =>
    left
    have := (bakes_step_facts N N.exec_order).time
    simp only [phase, hp, this]
  | NextRound hp =>
    left
    simp only [phase, hp, inc_round, round_tick]
    omega
  | PermParties ps hps => exact Or.inr ⟨rfl, rfl, hps.symm, rfl, rfl⟩
  | PermMsgs mb hmb => exact Or.inr ⟨rfl, rfl, List.Perm.refl _, rfl, rfl⟩

theorem monotone_phase {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') :
    phase N ≤ phase N' := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => rcases step_phase hs with h | h <;> omega

/-- Time does not decrease along an execution (`monotone_time`). -/
theorem monotone_time {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') :
    N.t_now ≤ N'.t_now := by
  have h1 := monotone_phase h
  have h2 := le_phase N
  have h3 := phase_lt N'
  omega

/-- Along an execution that does not change the phase, only permutations happen: the local
states are unchanged and the execution order is permuted. -/
theorem same_phase {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N')
    (hph : phase N' = phase N) :
    N'.state_map = N.state_map ∧ N'.exec_order.Perm N.exec_order := by
  induction h with
  | refl => exact ⟨rfl, List.Perm.refl _⟩
  | tail hNM hs ih =>
    have := monotone_phase hNM
    rcases step_phase hs with h | ⟨h1, h2, h3, -⟩
    · omega
    · obtain ⟨ih1, ih2⟩ := ih (by omega)
      exact ⟨h2.trans ih1, h3.trans ih2⟩

/-- Along an execution, local states persist and their trees only grow
(`monotone_tree`, `exists_state_pres_big_step`). -/
theorem monotone_tree {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') :
    (∀ p l', N'.state_map p = some l' → ∃ l, N.state_map p = some l ∧
      ∀ b ∈ l.blocks, b ∈ l'.blocks) ∧
    (∀ p l, N.state_map p = some l → ∃ l', N'.state_map p = some l') ∧
    N'.exec_order.Perm N.exec_order := by
  induction h with
  | refl => exact ⟨fun p l h => ⟨l, h, fun _ hb => hb⟩, fun p l h => ⟨l, h⟩, List.Perm.refl _⟩
  | tail _ hs ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have step : ∀ {M M' : GlobalState Tx Hash Party AdvState}, M ⤳ M' →
        (∀ p l', M'.state_map p = some l' → ∃ l, M.state_map p = some l ∧
          ∀ b ∈ l.blocks, b ∈ l'.blocks) ∧
        (∀ p l, M.state_map p = some l → ∃ l', M'.state_map p = some l') ∧
        M'.exec_order.Perm M.exec_order := by
      intro M M' hs
      cases hs with
      | Deliver hp =>
        have hF := rcvs_step_facts M M.exec_order
        exact ⟨fun p l' h => let ⟨l, hl, _, _, hsub⟩ := hF.state_back p l' h; ⟨l, hl, hsub⟩,
          hF.state_fwd, List.Perm.of_eq hF.order⟩
      | Bake hp =>
        have hF := bakes_step_facts M M.exec_order
        exact ⟨fun p l' h => let ⟨l, hl, _, _, hsub⟩ := hF.state_back p l' h; ⟨l, hl, hsub⟩,
          hF.state_fwd, List.Perm.of_eq hF.order⟩
      | NextRound hp =>
        exact ⟨fun p l h => ⟨l, h, fun _ hb => hb⟩, fun p l h => ⟨l, h⟩, List.Perm.refl _⟩
      | PermParties ps hps =>
        exact ⟨fun p l h => ⟨l, h, fun _ hb => hb⟩, fun p l h => ⟨l, h⟩, hps.symm⟩
      | PermMsgs mb hmb =>
        exact ⟨fun p l h => ⟨l, h, fun _ hb => hb⟩, fun p l h => ⟨l, h⟩, List.Perm.refl _⟩
    obtain ⟨s1, s2, s3⟩ := step hs
    refine ⟨fun p l3 h3 => ?_, fun p l h => ?_, s3.trans ih3⟩
    · obtain ⟨l2, h2, hsub2⟩ := s1 p l3 h3
      obtain ⟨l1, h1, hsub1⟩ := ih1 p l2 h2
      exact ⟨l1, h1, fun b hb => hsub2 b (hsub1 b hb)⟩
    · obtain ⟨l2, h2⟩ := ih2 p l h
      exact s2 p l2 h2

/-- The honest tree only grows along an execution (`monotone_honest_tree`). -/
theorem monotone_honest_tree (Tree : TreeType Tx Hash Party)
    {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') :
    ∀ b ∈ Tree.allBlocks (honest_tree Tree N), b ∈ Tree.allBlocks (honest_tree Tree N') := by
  obtain ⟨h1, h2, h3⟩ := monotone_tree h
  intro b hb
  rw [mem_honest_tree] at hb ⊢
  rcases hb with hb | ⟨p, hp, hh, l, hl, hb⟩
  · exact Or.inl hb
  · obtain ⟨l', hl'⟩ := h2 p l hl
    obtain ⟨l₀, hl₀, hsub⟩ := h1 p l' hl'
    have : l₀ = l := Option.some.inj (hl₀.symm.trans hl)
    subst this
    exact Or.inr ⟨p, h3.mem_iff.2 hp, hh, l', hl', hsub b hb⟩

/-- The honest tree is the same in two states of the same phase along an execution
(`honest_tree_preservation`). -/
theorem honest_tree_preservation (Tree : TreeType Tx Hash Party)
    {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') (hph : phase N' = phase N) :
    Tree.allBlocks (honest_tree Tree N) =i Tree.allBlocks (honest_tree Tree N') := by
  obtain ⟨h1, h2⟩ := same_phase h hph
  intro b
  rw [mem_honest_tree, mem_honest_tree, h1]
  simp only [h2.mem_iff]

/-- The honest tree at the start of a round is contained in the tree of every honest party
once the messages of the round are delivered (`honest_tree_subset`). -/
theorem honest_tree_subset (hu : (InitParties : List Party).Nodup) (Tree : TreeType Tx Hash Party)
    {N N' : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N)
    (hready : N.progress = .Ready) (hNN' : N ⇓ N') (hdel : N'.progress = .Delivered)
    (ht : N'.t_now = N.t_now) {p : Party} (hh : is_honest p = true) {l : LocalState Tx Hash Party}
    (hl : N'.state_map p = some l) :
    ∀ b ∈ Tree.allBlocks (honest_tree Tree N), b ∈ l.blocks := by
  induction hNN' generalizing l with
  | refl => simp [hready] at hdel
  | tail hNM hs ih =>
    rename_i M N2
    cases hs with
    | Deliver hp =>
      have hRM := Relation.ReflTransGen.trans hR hNM
      have hN := reachable_inv hRM
      have htM := (rcvs_step_facts M M.exec_order).time
      simp only at ht htM
      have hph : phase M = phase N := by
        simp only [phase, hp, hready]; omega
      intro b hb
      rw [honest_tree_preservation Tree hNM hph, mem_honest_tree] at hb
      have hF := rcvs_step_facts M M.exec_order
      obtain ⟨k, hk, -⟩ := hF.state_back p l hl
      obtain ⟨m, hm, hmb⟩ := rcvs_own M (uniq_exec_order hu hN) (hN.mem_order hk) hh hk
      have : m = l := Option.some.inj (hm.symm.trans hl)
      subst this
      rcases hb with rfl | ⟨p', _, hh', l', hl', hb⟩
      · exact gb_in_all _ _
      · exact (hmb b).2 (at_ready_subset hu hRM hp p' p l' k hh' hh hl' hk b hb)
    | Bake hp => simp at hdel
    | NextRound hp => simp at hdel
    | PermParties ps hps => exact ih hdel ht hl
    | PermMsgs mb hmb => exact ih hdel ht hl

end CatCryptCore.Consensus.PoSNSB

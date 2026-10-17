/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.ChainQuality

/-!
# PoS-NSB: preliminaries of common prefix

This file ports the first part of `Properties/CP.v` of PoS-NSB (Thomsen and Spitters,
*Formalizing Nakamoto-style proof of stake*, CSF 2021), with the facts about suffixes and the
longest common suffix `lcs` of `Properties/SsrFacts.v` that common prefix uses: super slots
and super blocks, the chain `cfb b bp` that ends in a block `b` and its length `pos b N`, and
the facts about the positions of honest blocks that the common-prefix proof uses.

A super slot is a slot with exactly one honest leader among the initial parties. The position
of a block is the length of the valid chain from the block down to the genesis block through
broadcast blocks. Honest blocks of later slots have higher positions (`hb_pos_gt_hb`), and no
other honest block has the position of an honest block of a super slot
(`no_honest_pos_share_sb`).

## Main results

* `lcs_suffix`, `lcsP`: `lcs s1 s2` is the longest common suffix of `s1` and `s2`.
* `prune_time_suffix`, `prune_suffix_trans`: the blocks of a chain up to a slot form a suffix.
* `cfb_valid_chain'`, `pos_eq`: without hash collisions, `cfb b bp` is the valid chain from `b`
  through blocks of `bp`, and the position of a block of a valid chain of broadcast blocks is
  its height in the chain.
* `reachable_hb_inv`: every honest block of the history lies, together with a valid chain
  below it, in the tree of an honest party.
* `honest_block_baked`: every honest block of the history was baked by an honest leader of its
  slot on top of its best chain.
* `honest_block_cfb_valid`, `hb_pos_gt_hb`, `hb_pos_gt_hb_gb`, `no_honest_pos_share_sb`,
  `super_block_exists`.

## Departures from the Coq development

* `cfb b bp` is defined as `b` followed by a valid chain through the genesis block and the
  blocks of `bp`, if there is one, and as the empty chain otherwise. The Coq function `cfb`
  computes this chain by well-founded recursion; without hash collisions on the genesis block
  and `bp` the two agree (`cfb_valid_chain'`, the Coq lemma of the same name). The Coq lemmas
  about the recursion (`perm_cfb`, `undup_cfb`, `cfb_mem`, `cfb_non_empty_subset`,
  `cfb_valid_subset`, `cfb_map_iota`) are replaced by `cfb_valid_chain'`, `pos_eq` and
  `pos_of_mem_chain`. The Coq lemma `cfb_gb` (`cfb GenesisBlock bp = [GenesisBlock]`) uses
  the Coq axiom `GenesisWin`; `cfb_gb_length_le` states the bound on the length that the proofs need.
* The suffix order `⪯` is `List.IsSuffix` (`<:+`).
* The Coq lemmas `one_super_block`, `super_slots_blocks` and `unique_sb_pos` count the super
  blocks of the history. The common-prefix proof in `CommonPrefix.lean` instead maps every
  super slot to the position of a super block of that slot (`super_block_exists`); these
  positions are distinct by `hb_pos_gt_hb`.
* The proofs of `hb_pos_gt_hb` and `no_honest_pos_share_sb` locate the baking step of a block
  with `honest_block_baked` instead of reasoning backwards step by step.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution

/-! ## Suffixes and the longest common suffix (`Properties/SsrFacts.v`) -/

section Lists

variable {T : Type}

/-- The longest common suffix of `s1` and `s2`: the longest suffix of `s1` that is a suffix
of `s2`. -/
noncomputable def lcs : List T → List T → List T
  | [], _ => []
  | x :: xs, s2 =>
    @dite _ (x :: xs <:+ s2) (Classical.propDecidable _) (fun _ => x :: xs) (fun _ => lcs xs s2)

/-- `lcs s1 s2` is a suffix of `s1` and of `s2` (`lcs_suffix`). -/
theorem lcs_suffix (s1 s2 : List T) : lcs s1 s2 <:+ s1 ∧ lcs s1 s2 <:+ s2 := by
  induction s1 with
  | nil => simp [lcs]
  | cons x xs ih =>
    unfold lcs
    by_cases h : x :: xs <:+ s2
    · rw [dif_pos h]; exact ⟨List.suffix_refl _, h⟩
    · rw [dif_neg h]; exact ⟨ih.1.trans (List.suffix_cons _ _), ih.2⟩

/-- Every common suffix of `s1` and `s2` is a suffix of `lcs s1 s2` (`lcsP`). -/
theorem lcsP {s s1 s2 : List T} (h1 : s <:+ s1) (h2 : s <:+ s2) : s <:+ lcs s1 s2 := by
  induction s1 with
  | nil => simp only [List.suffix_nil] at h1; subst h1; exact List.nil_suffix
  | cons x xs ih =>
    unfold lcs
    by_cases h : x :: xs <:+ s2
    · rw [dif_pos h]; exact h1
    · rw [dif_neg h]
      rcases List.suffix_cons_iff.1 h1 with rfl | h1
      · exact absurd h2 h
      · exact ih h1

end Lists

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-! ## Pruning a chain at a slot -/

/-- The blocks of `c` with a slot at most `t`. -/
def prune_time (t : Slot) (c : Chain Tx Hash Party) : Chain Tx Hash Party :=
  c.filter (fun b => decide (b.sl ≤ t))

/-- The blocks of a chain with strictly decreasing slots up to a slot form a suffix of the
chain (`prune_time_suffix`). -/
theorem prune_time_suffix (k : Slot) {c : Chain Tx Hash Party} (hd : decreasing_slots c) :
    prune_time k c <:+ c := by
  induction c with
  | nil => simp [prune_time]
  | cons x xs ih =>
    have hxs := List.pairwise_cons.1 hd
    by_cases hx : x.sl ≤ k
    · have : prune_time k (x :: xs) = x :: xs := by
        refine List.filter_eq_self.2 fun y hy => ?_
        rcases List.mem_cons.1 hy with rfl | hy
        · simpa using hx
        · have := hxs.1 y hy
          simp only [lt_slots] at this
          simp only [decide_eq_true_eq]
          omega
      rw [this]
    · have : prune_time k (x :: xs) = prune_time k xs := by
        simp [prune_time, hx]
      rw [this]
      exact (ih hxs.2).trans (List.suffix_cons _ _)

/-- Suffixes after pruning compose (`prune_suffix_trans`). -/
theorem prune_suffix_trans (k : Slot) {c1 c2 c3 : Chain Tx Hash Party}
    (h1 : prune_time k c1 <:+ c2) (h2 : prune_time k c2 <:+ c3) : prune_time k c1 <:+ c3 := by
  refine List.IsSuffix.trans ?_ h2
  have := h1.filter (fun b => decide (b.sl ≤ k))
  simpa [prune_time, List.filter_filter] using this

/-! ## Super slots -/

/-- A super slot: exactly one initial party is an honest leader of the slot. -/
def super_slot (sl : Slot) : Bool :=
  decide ((InitParties : List Party).countP (fun p => Winner p sl && is_honest p) = 1)

/-- The super slots in `[a, b)`. -/
def super_slots_range (a b : ℕ) : List Slot := p_slots_range (super_slot (Party := Party)) a b

/-- An honest block of a super slot. -/
def super_block (b : Block Tx Hash Party) : Bool := honest_block b && super_slot (Party := Party) b.sl

theorem super_slot_iff_charString [Fintype Party] (sl : Slot) :
    super_slot (Party := Party) sl = true ↔ (charString (Party := Party) sl).honest = 1 := by
  simp [super_slot, charString]

/-- A super slot has an honest initial leader. -/
theorem super_slot_lucky {sl : Slot} (h : super_slot (Party := Party) sl = true) :
    lucky_slot (Party := Party) sl = true := by
  simp only [super_slot, decide_eq_true_eq] at h
  have : 0 < (InitParties : List Party).countP (fun p => Winner p sl && is_honest p) := by omega
  simpa [lucky_slot, lucky_slot_gen, List.countP_pos_iff] using this

/-- In a super slot, two honest initial leaders are equal. -/
theorem super_slot_unique (hu : (InitParties : List Party).Nodup) {sl : Slot}
    (h : super_slot (Party := Party) sl = true) {p q : Party} (hp : p ∈ (InitParties : List Party))
    (hq : q ∈ (InitParties : List Party)) (hwp : Winner p sl = true) (hwq : Winner q sl = true)
    (hhp : is_honest p = true) (hhq : is_honest q = true) : p = q := by
  by_contra hne
  simp only [super_slot, decide_eq_true_eq, List.countP_eq_length_filter] at h
  have hnd : ((InitParties : List Party).filter (fun p => Winner p sl && is_honest p)).Nodup :=
    hu.filter _
  have hsub : [p, q] ⊆ (InitParties : List Party).filter (fun p => Winner p sl && is_honest p) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact List.mem_filter.2 ⟨hp, by simp [hwp, hhp]⟩
    · exact List.mem_filter.2 ⟨hq, by simp [hwq, hhq]⟩
  have hpq : [p, q].Nodup := List.nodup_cons.2 ⟨by simpa using hne, List.nodup_singleton _⟩
  have := (hpq.subperm hsub).length_le
  simp only [List.length_cons, List.length_nil] at this
  omega

/-! ## The chain from a block -/

/-- The chain from `b`: `b` followed by a valid chain through the genesis block and the blocks
of `bp`, if there is one, and the empty chain otherwise. -/
noncomputable def cfb (b : Block Tx Hash Party) (bp : List (Block Tx Hash Party)) :
    Chain Tx Hash Party :=
  @dite _ (∃ c, valid_chain (b :: c) ∧ ∀ x ∈ c, x ∈ GenesisBlock :: bp)
    (Classical.propDecidable _) (fun h => b :: h.choose) (fun _ => [])

/-- The position of `b` in `N`: the length of the chain from `b` through broadcast blocks. -/
noncomputable def pos (b : Block Tx Hash Party) (N : GlobalState Tx Hash Party AdvState) : ℕ :=
  (cfb b (block_history N)).length

/-- The honest blocks of the history and the genesis block. -/
def honest_block_hist_gb (N : GlobalState Tx Hash Party AdvState) : List (Block Tx Hash Party) :=
  (block_hist_gb N).filter honest_block

/-- Without hash collisions on the genesis block and `bp`, the chain from `b` is every valid
chain from `b` through the genesis block and blocks of `bp` (`cfb_valid_chain'`). -/
theorem cfb_valid_chain' {b : Block Tx Hash Party} {bp : List (Block Tx Hash Party)}
    {c : Chain Tx Hash Party}
    (hinj : ∀ x ∈ GenesisBlock :: bp, ∀ y ∈ GenesisBlock :: bp, HashB x = HashB y → x = y)
    (hv : valid_chain (b :: c)) (hs : ∀ x ∈ c, x ∈ GenesisBlock :: bp) : cfb b bp = b :: c := by
  have h : ∃ c, valid_chain (b :: c) ∧ ∀ x ∈ c, x ∈ GenesisBlock :: bp := ⟨c, hv, hs⟩
  unfold cfb
  rw [dif_pos h]
  congr 1
  exact eq_head_eq_chains_gen hinj _ _ b h.choose_spec.1 hv h.choose_spec.2 hs

/-- The chain from the genesis block has at most one block, the genesis block (`cfb_gb`). -/
theorem cfb_gb_length_le (bp : List (Block Tx Hash Party)) :
    (cfb GenesisBlock bp).length ≤ 1 := by
  unfold cfb
  split
  · rename_i h
    rw [valid_chain_gb_head h.choose_spec.1]
    simp
  · simp

/-- The chain from a block is a chain of the block, the genesis block and blocks of the pool
(`cfb_subset`). -/
theorem cfb_subset (b : Block Tx Hash Party) (bp : List (Block Tx Hash Party)) :
    ∀ x ∈ cfb b bp, x ∈ GenesisBlock :: b :: bp := by
  intro x hx
  unfold cfb at hx
  split at hx
  · rename_i h
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · rcases List.mem_cons.1 (h.choose_spec.2 x hx) with rfl | hx
      · simp
      · simp [hx]
  · simp at hx

/-- Without hash collisions, the position of `b` is the length of every valid chain from `b`
through broadcast blocks. -/
theorem pos_eq {N : GlobalState Tx Hash Party AdvState} (hcf : collision_free N)
    {b : Block Tx Hash Party} {c : Chain Tx Hash Party} (hv : valid_chain (b :: c))
    (hs : ∀ x ∈ c, x ∈ block_hist_gb N) : pos b N = c.length + 1 := by
  unfold pos
  rw [cfb_valid_chain' hcf hv hs]
  rfl

/-- Without hash collisions, the position of a block of a valid chain of broadcast blocks is
its height in the chain. -/
theorem pos_of_mem_chain {N : GlobalState Tx Hash Party AdvState} (hcf : collision_free N)
    {d e : Chain Tx Hash Party} {x : Block Tx Hash Party} (hv : valid_chain (d ++ x :: e))
    (hs : ∀ y ∈ d ++ x :: e, y ∈ block_hist_gb N) : pos x N = e.length + 1 :=
  pos_eq hcf (valid_chain_short_l hv) fun y hy => hs y (by simp [hy])

/-! ## Honest blocks of the history -/

/-- The block baked by an honest leader on top of its best chain extends that chain to a valid
chain. -/
theorem honest_new_block_valid {t : Slot} {q : Party} {lq : LocalState Tx Hash Party}
    (ht : 0 < t) (hw : Winner lq.pk t = true) :
    valid_chain (honest_new_block (AdvState := AdvState) t q lq ::
      lq.tT.bestChain (t - 1) lq.tree) := by
  have hCv := lq.tT.best_chain_valid lq.tree (t - 1)
  obtain ⟨c0, cs, hC⟩ := List.exists_cons_of_ne_nil (valid_chain_ne_nil hCv)
  have hc0 : c0.sl ≤ t - 1 := best_chain_time _ _ _ c0 (by rw [hC]; simp)
  rw [hC] at hCv ⊢
  refine valid_chain_ext hCv hw ?_ ?_
  · show HashB ((lq.tT.bestChain (t - 1) lq.tree).headD GenesisBlock) = HashB c0
    rw [hC]; rfl
  · show c0.sl < t
    omega

/-- Every honest block of the history has a positive slot and lies, together with a valid
chain below it, in the tree of an honest party. -/
def HBInv (N : GlobalState Tx Hash Party AdvState) : Prop :=
  ∀ b ∈ block_history N, honest_block b = true → 0 < b.sl ∧
    ∃ q l c, N.state_map q = some l ∧ is_honest q = true ∧ valid_chain (b :: c) ∧
      ∀ x ∈ b :: c, x ∈ l.blocks

/-- Local states persist along an execution and keep their blocks. -/
theorem state_persist {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') {q : Party}
    {l : LocalState Tx Hash Party} (hl : N.state_map q = some l) :
    ∃ l', N'.state_map q = some l' ∧ ∀ x ∈ l.blocks, x ∈ l'.blocks := by
  obtain ⟨h1, h2, -⟩ := monotone_tree h
  obtain ⟨l', hl'⟩ := h2 q l hl
  obtain ⟨l₀, hl₀, hsub⟩ := h1 q l' hl'
  have : l₀ = l := Option.some.inj (hl₀.symm.trans hl)
  subst this
  exact ⟨l', hl', hsub⟩

theorem HBInv.persist {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') {b : Block Tx Hash Party}
    (hb : 0 < b.sl ∧ ∃ q l c, N.state_map q = some l ∧ is_honest q = true ∧
      valid_chain (b :: c) ∧ ∀ x ∈ b :: c, x ∈ l.blocks) :
    0 < b.sl ∧ ∃ q l c, N'.state_map q = some l ∧ is_honest q = true ∧
      valid_chain (b :: c) ∧ ∀ x ∈ b :: c, x ∈ l.blocks := by
  obtain ⟨hsl, q, l, c, hl, hq, hv, hx⟩ := hb
  obtain ⟨l', hl', hsub⟩ := state_persist h hl
  exact ⟨hsl, q, l', c, hl', hq, hv, fun x h => hsub x (hx x h)⟩

/-- Without forging, every reachable state satisfies `HBInv`. -/
theorem reachable_hb_inv (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (hff : forging_free N) :
    HBInv N := by
  induction hR with
  | refl => simp [HBInv, block_history, N0]
  | tail hRM hs ih =>
    rename_i M N2
    have hffM := forging_free_prev (Relation.ReflTransGen.single hs) hff
    have ih := ih hffM
    have hM := reachable_inv hRM
    have hstep : M ⇓ N2 := Relation.ReflTransGen.single hs
    intro b hb hh
    cases hs with
    | Deliver hp =>
      exact HBInv.persist hstep (ih b (rcvs_honest_history M hff.1 M.exec_order
        (.ProgressR (.RefineStepR .refl)) b hb hh) hh)
    | Bake hp =>
      rcases bakes_honest_history M hff.2 M.exec_order (.ProgressB (.RefineStepB .refl)) b hb hh
        with hb' | ⟨pre, q, qs, hord, hhq, lq, hlq, hw, rfl⟩
      · exact HBInv.persist hstep (ih _ hb' hh)
      · have hnd := uniq_exec_order hu hM
        have hqo : q ∈ M.exec_order := by rw [hord]; simp
        have hqs : q ∉ qs := by
          rw [hord] at hnd
          exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
        have hlqM : M.state_map q = some lq := (bakes_state_notin M hqs).symm.trans hlq
        have hown := bakes_own M (uniq_exec_order hu hM) hqo hhq hlqM
        rw [honest_bake_eq, if_pos hw] at hown
        refine ⟨by simp [honest_new_block]; exact hM.time, q, _, _, hown, hhq,
          honest_new_block_valid hM.time hw, fun x hx => ?_⟩
        show x ∈ lq.tT.allBlocks (lq.tT.extendTree lq.tree _)
        rw [lq.tT.all_extend]
        rcases List.mem_cons.1 hx with rfl | hx
        · simp [honest_new_block]
        · have := lq.tT.best_chain_in_all _ _ x hx
          simp only [List.mem_filter] at this
          exact List.mem_append_left _ this.1
    | NextRound hp => exact ih b hb hh
    | PermParties ps hps => exact ih b hb hh
    | PermMsgs mb hmb => exact ih b hb hh

/-- Without hash collisions, the chain from an honest block of the history is a valid chain
through the genesis block and broadcast blocks. -/
theorem honest_hist_valid {N : GlobalState Tx Hash Party AdvState} (hHB : HBInv N)
    (hH : HistInv N) (hcf : collision_free N) {b : Block Tx Hash Party}
    (hb : b ∈ block_history N) (hh : honest_block b = true) :
    ∃ c, cfb b (block_history N) = b :: c ∧ valid_chain (b :: c) ∧
      ∀ x ∈ c, x ∈ block_hist_gb N := by
  obtain ⟨-, q, l, c, hl, -, hv, hx⟩ := hHB b hb hh
  have hs : ∀ x ∈ c, x ∈ block_hist_gb N :=
    fun x h => hH.state q l hl x (hx x (List.mem_cons_of_mem _ h))
  exact ⟨c, cfb_valid_chain' hcf hv hs, hv, hs⟩

/-- The chain from an honest block of the history is valid (`honest_block_cfb_valid`). -/
theorem honest_block_cfb_valid (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (hff : forging_free N)
    (hcf : collision_free N) {b : Block Tx Hash Party} (hb : b ∈ honest_block_hist N) :
    valid_chain (cfb b (block_history N)) := by
  obtain ⟨hb, hh⟩ := List.mem_filter.1 hb
  obtain ⟨c, hc, hv, -⟩ :=
    honest_hist_valid (reachable_hb_inv hu hR hff) (reachable_hist_inv hR) hcf hb hh
  rw [hc]; exact hv

/-! ## The baking step of an honest block -/

/-- The honest blocks broadcast in a baking phase by an honest leader. -/
theorem bakes_own_history (N : GlobalState Tx Hash Party AdvState) {p : Party}
    {l : LocalState Tx Hash Party} {ps : List Party} (hu : ps.Nodup) (hp : p ∈ ps)
    (hh : is_honest p = true) (hl : N.state_map p = some l) :
    ∀ m ∈ (honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p) l).1,
      m ∈ (ps.foldr party_bake_step_world N).history := by
  have hc : is_corrupt p = false := by
    have := honest_not_corrupt p; rw [hh] at this; simpa using this.symm
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rw [List.nodup_cons] at hu
    simp only [List.foldr_cons]
    intro m hm
    by_cases hq : q = p
    · subst hq
      have ht := (bakes_step_facts N qs).time
      refine (bake_history _ q m).2 (Or.inr ⟨l, (bakes_state_notin N hu.1).trans hl,
        Or.inl ⟨hc, ?_⟩⟩)
      rw [ht]; exact hm
    · exact bake_history_mono _ q m (ih hu.2 ((List.mem_cons.1 hp).resolve_left (Ne.symm hq)) m hm)

/-- A reachable state passes through the baking step of every slot `t ≥ 1` that it has
completed. -/
theorem bake_crossing {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) {t : Slot}
    (ht1 : 1 ≤ t) (ht : 3 * t + 2 ≤ phase N) :
    ∃ A, N0 AdvState ⇓ A ∧ A.progress = .Delivered ∧ A.t_now = t ∧
      ({ A.exec_order.foldr party_bake_step_world A with progress := .Baked } :
        GlobalState Tx Hash Party AdvState) ⇓ N := by
  have h0 : phase (N0 AdvState : GlobalState Tx Hash Party AdvState) = 3 := by simp [phase, N0]
  obtain ⟨A, B, h0A, hAB, hBN, hphA, hphB⟩ := phase_cross hR (3 * t + 2) (by omega) ht
  have hstep := step_phase hAB
  cases hAB with
  | Bake hp =>
    refine ⟨A, h0A, hp, ?_, hBN⟩
    have : phase A = 3 * A.t_now + 1 := by simp [phase, hp]
    omega
  | Deliver hp =>
    exfalso
    have : phase A = 3 * A.t_now := by simp [phase, hp]
    omega
  | NextRound hp =>
    exfalso
    have : phase A = 3 * A.t_now + 2 := by simp [phase, hp]
    omega
  | PermParties ps hps => exfalso; simp only [phase] at hphA hphB; omega
  | PermMsgs mb hmb => exfalso; simp only [phase] at hphA hphB; omega

/-- Without forging, the honest blocks of slot `t` in the history are the blocks baked in the
baking step of slot `t` by honest leaders on top of their best chains. -/
theorem bake_step_honest (hu : (InitParties : List Party).Nodup)
    {A N : GlobalState Tx Hash Party AdvState} (hRA : N0 AdvState ⇓ A)
    (hp : A.progress = .Delivered)
    (hBN : ({ A.exec_order.foldr party_bake_step_world A with progress := .Baked } :
        GlobalState Tx Hash Party AdvState) ⇓ N) (hff : forging_free N) :
    ∀ b ∈ block_history N, honest_block b = true → b.sl = A.t_now →
      ∃ q lq, q ∈ A.exec_order ∧ is_honest q = true ∧ A.state_map q = some lq ∧
        Winner lq.pk A.t_now = true ∧ b = honest_new_block (AdvState := AdvState) A.t_now q lq := by
  intro b hb hh hsl
  have hA := reachable_inv hRA
  have hphB : phase ({ A.exec_order.foldr party_bake_step_world A with progress := .Baked } :
      GlobalState Tx Hash Party AdvState) = 3 * A.t_now + 2 := by
    simp [phase, (bakes_step_facts A A.exec_order).time]
  have hbF : b ∈ block_history (A.exec_order.foldr party_bake_step_world A) :=
    honest_block_preserved_phase hBN hff b hb hh (by omega)
  have hAN : A ⇓ N := (Relation.ReflTransGen.single (SingleStep.Bake A hp)).trans hBN
  rcases bakes_honest_history A hff.2 A.exec_order (.ProgressB (.RefineStepB hBN)) b hbF hh
    with hbA | ⟨pre, q, qs, hord, hhq, lq, hlq, hw, hbq⟩
  · exfalso
    have := no_premature_honest_blocks_D hRA (forging_free_prev hAN hff) hp b
      (List.mem_filter.2 ⟨hbA, hh⟩)
    omega
  have hnd := uniq_exec_order hu hA
  have hqo : q ∈ A.exec_order := by rw [hord]; simp
  have hqs : q ∉ qs := by
    rw [hord] at hnd
    exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  exact ⟨q, lq, hqo, hhq, (bakes_state_notin A hqs).symm.trans hlq, hw, hbq⟩

/-- Without forging, every honest block of the history was baked in the baking step of its slot
by an honest leader on top of its best chain. -/
theorem honest_block_baked (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (hff : forging_free N)
    {b : Block Tx Hash Party} (hb : b ∈ block_history N) (hh : honest_block b = true) :
    ∃ A, N0 AdvState ⇓ A ∧ A.progress = .Delivered ∧ A.t_now = b.sl ∧
      ({ A.exec_order.foldr party_bake_step_world A with progress := .Baked } :
        GlobalState Tx Hash Party AdvState) ⇓ N ∧
      ∃ q lq, q ∈ A.exec_order ∧ is_honest q = true ∧ A.state_map q = some lq ∧
        Winner lq.pk A.t_now = true ∧ b = honest_new_block (AdvState := AdvState) A.t_now q lq := by
  have hpos := (reachable_hb_inv hu hR hff b hb hh).1
  have hsl := honest_hist_slots hR hff b hb hh
  have hph : 3 * b.sl + 2 ≤ phase N := by
    by_cases hB : N.progress = .Baked
    · have : phase N = 3 * N.t_now + 2 := by simp [phase, hB]
      omega
    · have := hsl.2 hB
      have := le_phase N
      omega
  obtain ⟨A, hRA, hp, hAt, hBN⟩ := bake_crossing hR hpos hph
  exact ⟨A, hRA, hp, hAt, hBN, bake_step_honest hu hRA hp hBN hff b hb hh hAt.symm⟩

/-! ## Positions of honest blocks -/

/-- An honest block of the history and the chain below it are, at the start of every later slot,
in the tree of every honest party once the messages of the slot are delivered. -/
theorem honest_chain_delivered (hu : (InitParties : List Party).Nodup)
    {R A : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ R) (hRA : R ⇓ A)
    (hready : R.progress = .Ready) (hp : A.progress = .Delivered) (ht : R.t_now ≤ A.t_now)
    (hff : forging_free R) {q : Party} {lq : LocalState Tx Hash Party}
    (hq : is_honest q = true) (hlq : A.state_map q = some lq)
    {b : Block Tx Hash Party} (hb : b ∈ block_history R) (hh : honest_block b = true) :
    ∃ c, valid_chain (b :: c) ∧ ∀ x ∈ b :: c, x ∈ lq.blocks ∧ x ∈ block_hist_gb R := by
  obtain ⟨-, q', l', c, hl', hq', hv, hx⟩ := reachable_hb_inv hu hR hff b hb hh
  have hR' := reachable_inv hR
  have hH := reachable_hist_inv hR
  have hsub : ∀ x ∈ lq.tT.allBlocks (honest_tree lq.tT R), x ∈ lq.blocks := by
    rcases Nat.lt_or_ge R.t_now A.t_now with hlt | hge
    · exact honest_tree_subset_ext hu lq.tT hR hready hRA hlt hq hlq
    · exact honest_tree_subset hu lq.tT hR hready hRA hp (by omega) hq hlq
  refine ⟨c, hv, fun x hx' => ⟨hsub x ?_, hH.state q' l' hl' x (hx x hx')⟩⟩
  exact (mem_honest_tree lq.tT R x).2 (Or.inr ⟨q', hR'.mem_order hl', hq', l', hl', hx x hx'⟩)

/-- Honest blocks of earlier slots have smaller positions (`hb_pos_gt_hb`); the genesis block
counts as an honest block of the history (`hb_pos_gt_hb_gb`). -/
theorem hb_pos_gt_hb_gb (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (hff : forging_free N)
    (hcf : collision_free N) {b b' : Block Tx Hash Party} (hb : b ∈ honest_block_hist N)
    (hb' : b' = GenesisBlock ∨ b' ∈ honest_block_hist N) (hsl : b'.sl < b.sl) :
    pos b' N < pos b N := by
  obtain ⟨hbN, hh⟩ := List.mem_filter.1 hb
  obtain ⟨A, hRA, hp, hAt, hBN, q, lq, hqo, hhq, hlq, hw, hbq⟩ := honest_block_baked hu hR hff hbN hh
  have hA := reachable_inv hRA
  have hHA := reachable_hist_inv hRA
  have hAN : A ⇓ N := (Relation.ReflTransGen.single (SingleStep.Bake A hp)).trans hBN
  have hAt0 := hA.time
  have hLq := hA.longest hLmap hlq
  -- the position of `b`
  have hvb := honest_new_block_valid (AdvState := AdvState) (q := q) hAt0 hw
  rw [← hbq] at hvb
  have hCs : ∀ x ∈ lq.tT.bestChain (A.t_now - 1) lq.tree, x ∈ block_hist_gb N := by
    intro x hx
    have := lq.tT.best_chain_in_all _ _ x hx
    simp only [List.mem_filter] at this
    exact block_hist_gb_monotone hAN x (hHA.state q lq hlq x this.1)
  rw [pos_eq hcf hvb hCs]
  rcases hb' with rfl | hb'
  · -- the genesis block
    unfold pos
    have := cfb_gb_length_le (block_history N)
    have := List.length_pos_of_ne_nil
      (valid_chain_ne_nil (lq.tT.best_chain_valid lq.tree (A.t_now - 1)))
    omega
  obtain ⟨hb'N, hh'⟩ := List.mem_filter.1 hb'
  have hffA := forging_free_prev hAN hff
  have hb'A : b' ∈ block_history A :=
    honest_block_preserved_phase hAN hff b' hb'N hh' (by simp [phase, hp]; omega)
  obtain ⟨R, hpR, htR, h0R, hRA'⟩ := slot_in_between (N := N0 AdvState) rfl hRA
    (sl := b'.sl + 1) (by simp [N0]) (by omega)
  have hffR := forging_free_prev hRA' hffA
  have hb'R : b' ∈ block_history R :=
    honest_block_preserved_phase hRA' hffA b' hb'A hh' (by simp [phase, hpR]; omega)
  obtain ⟨c', hv', hx'⟩ := honest_chain_delivered hu h0R hRA' hpR hp (by omega) hffR hhq hlq
    hb'R hh'
  have hRN := hRA'.trans hAN
  rw [pos_eq hcf hv' fun x hx => block_hist_gb_monotone hRN x (hx' x (List.mem_cons_of_mem _ hx)).2]
  have := hLq (b' :: c') (A.t_now - 1) lq.tree hv' fun x hx => by
    simp only [List.mem_filter, decide_eq_true_eq]
    refine ⟨(hx' x hx).1, ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := List.rel_of_pairwise_cons hv'.2.2 hx
      simp only [lt_slots] at this
      omega
  simp only [List.length_cons] at this ⊢
  omega

/-- Honest blocks of earlier slots have smaller positions (`hb_pos_gt_hb`). -/
theorem hb_pos_gt_hb (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (hff : forging_free N)
    (hcf : collision_free N) {b b' : Block Tx Hash Party} (hb : b ∈ honest_block_hist N)
    (hb' : b' ∈ honest_block_hist N) (hsl : b'.sl < b.sl) : pos b' N < pos b N :=
  hb_pos_gt_hb_gb hu hLmap hR hff hcf hb (Or.inr hb') hsl

/-- No honest block other than a super block has the position of the super block
(`no_honest_pos_share_sb`). -/
theorem no_honest_pos_share_sb (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) (hff : forging_free N)
    (hcf : collision_free N) {b b' : Block Tx Hash Party} (hb : b ∈ block_history N)
    (hsb : super_block (Party := Party) b = true) (hb' : b' ∈ honest_block_hist N)
    (hpos : pos b' N = pos b N) : b' = b := by
  simp only [super_block, Bool.and_eq_true] at hsb
  have hbh : b ∈ honest_block_hist N := List.mem_filter.2 ⟨hb, hsb.1⟩
  rcases Nat.lt_trichotomy b'.sl b.sl with hlt | heq | hgt
  · have := hb_pos_gt_hb hu hLmap hR hff hcf hbh hb' hlt; omega
  · obtain ⟨A, hRA, hp, hAt, hBN, q, lq, hqo, hhq, hlq, hw, hbq⟩ :=
      honest_block_baked hu hR hff hb hsb.1
    obtain ⟨hb'N, hh'⟩ := List.mem_filter.1 hb'
    obtain ⟨q', lq', hqo', hhq', hlq', hw', hbq'⟩ :=
      bake_step_honest hu hRA hp hBN hff b' hb'N hh' (by omega)
    have hA := reachable_inv hRA
    have hpk := hA.pk q lq hlq
    have hpk' := hA.pk q' lq' hlq'
    have hqq : q' = q := by
      refine super_slot_unique hu (sl := b.sl) hsb.2 (hA.perm.mem_iff.1 hqo')
        (hA.perm.mem_iff.1 hqo) ?_ ?_ hhq' hhq
      · rw [← hAt, ← hpk']; exact hw'
      · rw [← hAt, ← hpk]; exact hw
    subst hqq
    have : lq' = lq := Option.some.inj (hlq'.symm.trans hlq)
    subst this
    rw [hbq, hbq']
  · have := hb_pos_gt_hb hu hLmap hR hff hcf hb' hbh hgt; omega

/-- Every super slot `s ≥ 1` that a reachable state has completed has a super block of slot `s`
in the history. -/
theorem super_block_exists (hu : (InitParties : List Party).Nodup)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N) {s : Slot} (hs1 : 1 ≤ s)
    (hs : s < N.t_now) (hss : super_slot (Party := Party) s = true) :
    ∃ sb ∈ block_history N, super_block (Party := Party) sb = true ∧ sb.sl = s := by
  have hph : 3 * s + 2 ≤ phase N := by have := le_phase N; omega
  obtain ⟨A, hRA, hp, hAt, hBN⟩ := bake_crossing hR hs1 hph
  have hA := reachable_inv hRA
  have hl := super_slot_lucky hss
  obtain ⟨p, hpI, hpw⟩ := List.any_eq_true.1 hl
  simp only [Bool.and_eq_true] at hpw
  obtain ⟨lp, hlp⟩ := Option.isSome_iff_exists.1 ((hA.state_init p).2 hpI)
  have hpo := hA.mem_order hlp
  have hpk := hA.pk p lp hlp
  have hw : Winner lp.pk A.t_now = true := by rw [hpk, hAt]; exact hpw.1
  have hhist := bakes_own_history A (uniq_exec_order hu hA) hpo hpw.2 hlp
  rw [honest_bake_eq, if_pos hw] at hhist
  have hmem := hhist _ List.mem_cons_self
  have hBN' := history_monotone hBN
  refine ⟨honest_new_block (AdvState := AdvState) A.t_now p lp,
    List.mem_map_of_mem (f := get_block) (hBN' _ hmem), ?_, by simp [honest_new_block, hAt]⟩
  simp only [super_block, honest_block, honest_new_block, hpk, hpw.2, Bool.true_and]
  rw [hAt]; exact hss

end CatCryptCore.Consensus.PoSNSB

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.CommonPrefixPrelims

/-!
# PoS-NSB: common prefix

This file ports the common-prefix theorem of `Properties/CP.v` of PoS-NSB (Thomsen and
Spitters, *Formalizing Nakamoto-style proof of stake*, CSF 2021). Timed common prefix says:
for an honest party `p1` in a state `N1` and an honest party `p2` in a later state `N2`, the
blocks of slots at most `k` of the chain of `p1` form a suffix of the chain of `p2`, unless for
some slot `t1 ≤ k` and some slot `t2` between the two states the super slots in
`[t1 + 1, t2 - 1)` are at most twice as many as the adversarial slots in `[t1 + 1, t2 + 1)`.

The slot conditions are parameters: `timed_common_prefix_gen` counts the slots satisfying a
predicate `Q` that implies a super slot against the slots satisfying a predicate `A` that holds
whenever some party is a corrupt leader. `timed_common_prefix_charString` reads both conditions
off the characteristic string. The Coq statements `timed_common_prefix` and
`timed_common_prefix'` are the instance `Q = super_slot`, `A = adv_slot`.

The theorems assume, as in the Coq development:
* `hu`: the initial parties are distinct (`PartiesUniq`);
* `hLmap`: the tree type of every party follows the longest-chain rule;
* `hGB`: the genesis block is an honest block (`HonestGB`);
* `hff`, `hcf`: the adversary does not forge honest blocks and there are no hash collisions
  among broadcast blocks.
The Coq axiom `GenesisSlot` is not used.

## Main results

* `cp_lemma_gen_inc`: if a valid chain `c` of broadcast blocks is at least as long as the chain
  of an honest party, then below the head of their longest common suffix there is a slot `t`
  such that the super slots after `t` are at most twice as many as the adversarial slots after
  `t`.
* `cp_prune_gen_inc`, `cp_prune_gen_inc_r`, `common_prefix_lemma_parties`: common prefix in
  one state.
* `timed_common_prefix_gen`, `timed_common_prefix`, `timed_common_prefix'`,
  `timed_common_prefix_charString`: timed common prefix.

## Proof structure

The proof of `cp_lemma_gen_inc` follows the Coq development: below the head of the longest
common suffix, take the first honest block `b'`; every super slot after `sl b'` has a super
block whose position lies above `b'` and at most at the length of the chain of the honest
party; at that position one of the two chains holds a corrupt block, or the common suffix holds
a corrupt block. Instead of counting the super blocks of the history (`super_slots_blocks`,
`unique_sb_pos`), every super slot is mapped to the position of a super block of that slot
(`super_block_exists`); these positions are distinct by `hb_pos_gt_hb`. The induction of
`timed_common_prefix` follows the Coq proof, with the per-step argument in each case.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-! ## Lists -/

/-- Every position `1 ≤ k ≤ |L|`, counted from the end, holds an element of `L`. -/
theorem exists_at_height {β : Type} (L : List β) (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ L.length) :
    ∃ d x e, L = d ++ x :: e ∧ e.length + 1 = k := by
  obtain ⟨x, e, he⟩ : ∃ x e, L.drop (L.length - k) = x :: e :=
    List.exists_cons_of_ne_nil fun h => by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_nil] at this
      omega
  refine ⟨L.take (L.length - k), x, e, by rw [← he, List.take_append_drop], ?_⟩
  have := congrArg List.length he
  simp only [List.length_drop, List.length_cons] at this
  omega

/-- An element whose suffix is longer than a suffix `V` of the list lies before `V`. -/
theorem mem_left_of_height {β : Type} {U V d e : List β} {x : β} (h : d ++ x :: e = U ++ V)
    (hl : V.length < (x :: e).length) : x ∈ U := by
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, h2⟩ | ⟨c', rfl, h2⟩
  · cases a' with
    | nil => simp only [List.nil_append] at h2; subst h2; omega
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h2
      rw [h2.1]; simp
  · subst h2; simp at hl; omega

/-- A valid chain ends with the genesis block (`suffix_gb_vc`). -/
theorem valid_chain_suffix_gb {c : Chain Tx Hash Party} (h : valid_chain c) :
    [GenesisBlock] <:+ c := by
  induction c with
  | nil => exact absurd h (fun h => valid_chain_ne_nil h rfl)
  | cons x xs ih =>
    by_cases hxs : xs = []
    · subst hxs; rw [valid_chain_single h]
    · exact (ih (valid_chain_tail h hxs)).trans (List.suffix_cons _ _)

/-- Below a common suffix whose head has a larger slot than `k`, pruning a chain at `k` gives
a suffix of the common suffix. -/
theorem prune_lcs {L cs pre : Chain Tx Hash Party} (hL : pre ++ cs = L) (hd : decreasing_slots L)
    (k : Slot) (hk : k < (cs.headD GenesisBlock).sl) (hne : cs ≠ []) : prune_time k L <:+ cs := by
  obtain ⟨b, cs', rfl⟩ := List.exists_cons_of_ne_nil hne
  subst hL
  have hpre : prune_time k pre = [] := by
    simp only [prune_time, List.filter_eq_nil_iff, decide_eq_true_eq, not_le]
    intro x hx
    have := (List.pairwise_append.1 hd).2.2 x hx b List.mem_cons_self
    simp only [lt_slots] at this
    simp only [List.headD_cons] at hk
    omega
  have : prune_time k (pre ++ b :: cs') = prune_time k (b :: cs') := by
    simp only [prune_time, List.filter_append] at hpre ⊢
    rw [hpre, List.nil_append]
  rw [this]
  exact prune_time_suffix k (List.pairwise_append.1 hd).2.1

/-- A larger end of a range does not remove slots (`p_slots_size_leq_addr`). -/
theorem p_slots_range_mono_right (P : Slot → Bool) (a b b' : ℕ) (h : b ≤ b') :
    (p_slots_range P a b).length ≤ (p_slots_range P a b').length := by
  induction b', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    refine ih.trans ?_
    by_cases hab : a ≤ n
    · have e : nat_range a (n + 1) = nat_range a n ++ [n] := by
        simp only [nat_range]
        rw [show n + 1 - a = (n - a) + 1 by omega, List.range'_concat]
        congr 2
        omega
      rw [p_slots_range, p_slots_range, e, List.filter_append, List.length_append]
      omega
    · simp [p_slots_range, nat_range, show n - a = 0 by omega]

/-- A larger end of a range does not remove slots (`p_slots_size_leq_addr`). -/
theorem p_slots_size_leq_addr (P : Slot → Bool) (a b c : ℕ) :
    (p_slots_range P a b).length ≤ (p_slots_range P a (b + c)).length :=
  p_slots_range_mono_right P a b (b + c) (by omega)

/-- A stronger slot condition selects fewer slots. -/
theorem p_slots_range_mono_pred {P P' : Slot → Bool} (h : ∀ sl, P sl = true → P' sl = true)
    (a b : ℕ) : (p_slots_range P a b).length ≤ (p_slots_range P' a b).length := by
  simp only [p_slots_range, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun x _ hx => h x hx

/-! ## Common prefix in one state -/

/-- If a valid chain `c` of broadcast blocks with slots at most `t_now N - 1 + a` is at least as
long as the chain of an honest party `p1`, then there is a slot `t`, at most the slot of the
head of their longest common suffix, such that the super slots in `[t + 1, t_now N - 1)` are at
most twice as many as the slots in `[t + 1, t_now N + a)` satisfying `A`
(`cp_lemma_gen_inc`). -/
theorem cp_lemma_gen_inc (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    (a : ℕ) {N : GlobalState Tx Hash Party AdvState} {p1 : Party} {l1 : LocalState Tx Hash Party}
    {c : Chain Tx Hash Party}
    (hsub : ∀ x ∈ c, x ∈ block_hist_gb N ∧ x.sl ≤ N.t_now - 1 + a) (hvc : valid_chain c)
    (hlen : (l1.tT.bestChain (N.t_now - 1) l1.tree).length ≤ c.length)
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hh1 : is_honest p1 = true) (hl1 : N.state_map p1 = some l1) :
    ∃ t, t ≤ ((lcs (l1.tT.bestChain (N.t_now - 1) l1.tree) c).headD GenesisBlock).sl ∧
      (super_slots_range (Party := Party) (t + 1) (N.t_now - 1)).length ≤
        2 * (p_slots_range A (t + 1) (N.t_now + a)).length := by
  set bc1 := l1.tT.bestChain (N.t_now - 1) l1.tree with hbc1
  have hN := reachable_inv hR
  have hH := reachable_hist_inv hR
  have htN := hN.time
  have hv1 : valid_chain bc1 := l1.tT.best_chain_valid _ _
  have hbt1 : ∀ x ∈ bc1, x.sl ≤ N.t_now - 1 := best_chain_time _ _ _
  have hsub1 : ∀ x ∈ bc1, x ∈ block_hist_gb N := fun x hx => by
    have := l1.tT.best_chain_in_all _ _ x hx
    simp only [List.mem_filter] at this
    exact hH.state p1 l1 hl1 x this.1
  have hsubc : ∀ y ∈ c, y ∈ block_hist_gb N := fun y hy => (hsub y hy).1
  obtain ⟨⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := lcs_suffix bc1 c
  set cs := lcs bc1 c with hcs
  have hgb : [GenesisBlock] <:+ cs := lcsP (valid_chain_suffix_gb hv1) (valid_chain_suffix_gb hvc)
  have hgbcs : GenesisBlock ∈ cs := hgb.subset (List.mem_singleton_self _)
  obtain ⟨cs1, b', cs2, hcs_eq, hhb', hcs1⟩ := findo_split honest_block cs ⟨_, hgbcs, hGB⟩
  have hL1 : bc1 = (c1 ++ cs1) ++ b' :: cs2 := by rw [← hc1, hcs_eq]; simp
  have hL2 : c = (c2 ++ cs1) ++ b' :: cs2 := by rw [← hc2, hcs_eq]; simp
  have hp1 := hv1.2.2
  rw [hL1] at hp1
  have hab1 : ∀ x ∈ c1 ++ cs1, b'.sl < x.sl :=
    fun x hx => (List.pairwise_append.1 hp1).2.2 x hx b' List.mem_cons_self
  have hpc := hvc.2.2
  rw [hL2] at hpc
  have hab2 : ∀ x ∈ c2 ++ cs1, b'.sl < x.sl :=
    fun x hx => (List.pairwise_append.1 hpc).2.2 x hx b' List.mem_cons_self
  refine ⟨b'.sl, ?_, ?_⟩
  · rw [hcs_eq]
    cases cs1 with
    | nil => simp
    | cons y ys =>
      simp only [List.cons_append, List.headD_cons]
      exact le_of_lt (hab1 y (by simp))
  -- the corrupt blocks above `b'`
  have hnh1 : (c1 ++ cs1).filter (fun b => !honest_block b) =
      c1.filter (fun b => !honest_block b) ++ cs1 := by
    rw [List.filter_append, (List.filter_eq_self (l := cs1)).2 (fun x hx => by simp [hcs1 x hx])]
  have hA1 := limit_adv_bp_gen A hA (b'.sl + 1) (N.t_now + a) (c1 ++ cs1)
    (fun x hx => ⟨hab1 x hx, by
      have := hbt1 x (by rw [hL1]; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)
      omega⟩)
    (fun x hx => hv1.1 x (by rw [hL1]; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto))
    (List.pairwise_append.1 hp1).1
  have hA2 := limit_adv_bp_gen A hA (b'.sl + 1) (N.t_now + a) c2
    (fun x hx => ⟨hab2 x (by simp [hx]), by have := (hsub x (by rw [hL2]; simp [hx])).2; omega⟩)
    (fun x hx => hvc.1 x (by rw [hL2]; simp [hx]))
    (List.pairwise_append.1 (List.pairwise_append.1 hpc).1).1
  rw [hnh1, List.length_append] at hA1
  suffices hS : (super_slots_range (Party := Party) (b'.sl + 1) (N.t_now - 1)).length ≤
      cs1.length + (c1.filter (fun b => !honest_block b)).length +
        (c2.filter (fun b => !honest_block b)).length by
    omega
  -- every super slot after `sl b'` has a super block
  set S := super_slots_range (Party := Party) (b'.sl + 1) (N.t_now - 1) with hSdef
  have hSmem : ∀ s ∈ S, b'.sl + 1 ≤ s ∧ s < N.t_now - 1 ∧ super_slot (Party := Party) s = true := by
    intro s hs
    simp only [hSdef, super_slots_range, p_slots_range, nat_range, List.mem_filter,
      List.mem_range'_1] at hs
    exact ⟨hs.1.1, by omega, hs.2⟩
  have hex : ∀ s ∈ S, ∃ sb ∈ block_history N, super_block (Party := Party) sb = true ∧ sb.sl = s :=
    fun s hs => super_block_exists hu hR (by have := hSmem s hs; omega)
      (by have := hSmem s hs; omega) (hSmem s hs).2.2
  have : Nonempty (Block Tx Hash Party) := ⟨GenesisBlock⟩
  choose! g hg using hex
  have hgh : ∀ s ∈ S, g s ∈ honest_block_hist N := fun s hs => by
    obtain ⟨h1, h2, -⟩ := hg s hs
    simp only [super_block, Bool.and_eq_true] at h2
    exact List.mem_filter.2 ⟨h1, h2.1⟩
  have hSnd : S.Nodup := List.Nodup.filter _ List.nodup_range'
  have hinj : ∀ s ∈ S, ∀ s' ∈ S, pos (g s) N = pos (g s') N → s = s' := by
    intro s hs s' hs' he
    rcases Nat.lt_trichotomy s s' with h | h | h
    · have := hb_pos_gt_hb hu hLmap hR hff hcf (hgh s' hs') (hgh s hs)
        (by rw [(hg s hs).2.2, (hg s' hs').2.2]; exact h)
      omega
    · exact h
    · have := hb_pos_gt_hb hu hLmap hR hff hcf (hgh s hs) (hgh s' hs')
        (by rw [(hg s hs).2.2, (hg s' hs').2.2]; exact h)
      omega
  have hmapnd : (S.map fun s => pos (g s) N).Nodup := List.Nodup.map_on hinj hSnd
  suffices hclaim : ∀ s ∈ S, pos (g s) N ∈ cs1.map (fun x => pos x N) ++
      (c1.filter (fun b => !honest_block b)).map (fun x => pos x N) ++
      (c2.filter (fun b => !honest_block b)).map (fun x => pos x N) by
    have := (hmapnd.subperm fun y hy => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
      exact hclaim s hs).length_le
    simp only [List.length_map, List.length_append] at this
    omega
  intro s hs
  obtain ⟨hsbN, hsb, hsbs⟩ := hg s hs
  obtain ⟨hs1, hs2, -⟩ := hSmem s hs
  have hsbh := hgh s hs
  -- the position of the super block is above `b'`
  have hposb' : pos b' N = cs2.length + 1 :=
    pos_of_mem_chain hcf (d := c1 ++ cs1) (by rw [← hL1]; exact hv1) (by rw [← hL1]; exact hsub1)
  have hb'gb : b' = GenesisBlock ∨ b' ∈ honest_block_hist N := by
    rcases List.mem_cons.1 (hsub1 b' (by rw [hL1]; simp)) with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.2 ⟨h, hhb'⟩)
  have hk1 : pos b' N < pos (g s) N :=
    hb_pos_gt_hb_gb hu hLmap hR hff hcf hsbh hb'gb (by rw [hsbs]; omega)
  -- the position of the super block is at most the length of the chain of `p1`
  have hN0t : (N0 AdvState : GlobalState Tx Hash Party AdvState).t_now = 1 := rfl
  obtain ⟨R, hpR, htR, h0R, hRN⟩ := slot_in_between (N := N0 AdvState) rfl hR
    (sl := N.t_now - 1) (by omega) (by omega)
  have hffR := forging_free_prev hRN hff
  have hsbR : g s ∈ block_history R :=
    honest_block_preserved_phase hRN hff _ hsbN (List.mem_filter.1 hsbh).2
      (by simp [phase, hpR, htR]; omega)
  obtain ⟨-, q', l', csb, hl', hq', hvsb, hxsb⟩ :=
    reachable_hb_inv hu h0R hffR _ hsbR (List.mem_filter.1 hsbh).2
  have hR' := reachable_inv h0R
  have hHR := reachable_hist_inv h0R
  have hsubR := honest_tree_subset_ext hu l1.tT h0R hpR hRN (by omega) hh1 hl1
  have hin1 : ∀ x ∈ g s :: csb, x ∈ l1.blocks := fun x hx =>
    hsubR x ((mem_honest_tree l1.tT R x).2
      (Or.inr ⟨q', hR'.mem_order hl', hq', l', hl', hxsb x hx⟩))
  have hpossb : pos (g s) N = csb.length + 1 :=
    pos_eq hcf hvsb fun x hx => block_hist_gb_monotone hRN x
      (hHR.state q' l' hl' x (hxsb x (List.mem_cons_of_mem _ hx)))
  have hk2 : pos (g s) N ≤ bc1.length := by
    rw [hpossb]
    have := (hN.longest hLmap hl1) (g s :: csb) (N.t_now - 1) l1.tree hvsb fun x hx => by
      simp only [List.mem_filter, decide_eq_true_eq]
      refine ⟨hin1 x hx, ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := List.rel_of_pairwise_cons hvsb.2.2 hx
        simp only [lt_slots] at this
        omega
    simpa using this
  -- the blocks at the position of the super block
  have hp1' : (c1 ++ cs).Pairwise lt_slots := by rw [hc1]; exact hv1.2.2
  have hpc' : (c2 ++ cs).Pairwise lt_slots := by rw [hc2]; exact hvc.2.2
  by_cases hkcs : pos (g s) N ≤ cs.length
  · obtain ⟨d, x, e, hde, hek⟩ := exists_at_height cs (pos (g s) N) (by omega) hkcs
    have hxcs1 : x ∈ cs1 := mem_left_of_height (hde.symm.trans hcs_eq) (by simp; omega)
    have hbc : bc1 = (c1 ++ d) ++ x :: e := by rw [← hc1, hde]; simp
    have hposx : pos x N = pos (g s) N := by
      rw [pos_of_mem_chain hcf (by rw [← hbc]; exact hv1) (by rw [← hbc]; exact hsub1)]
      omega
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨x, hxcs1, hposx⟩))
  · push Not at hkcs
    obtain ⟨d1, x1, e1, hde1, hek1⟩ := exists_at_height bc1 (pos (g s) N) (by omega) hk2
    obtain ⟨d2, x2, e2, hde2, hek2⟩ := exists_at_height c (pos (g s) N) (by omega) (by omega)
    have hx1 : x1 ∈ c1 := mem_left_of_height (hde1.symm.trans hc1.symm) (by simp; omega)
    have hx2 : x2 ∈ c2 := mem_left_of_height (hde2.symm.trans hc2.symm) (by simp; omega)
    have hposx1 : pos x1 N = pos (g s) N := by
      rw [pos_of_mem_chain hcf (by rw [← hde1]; exact hv1) (by rw [← hde1]; exact hsub1)]
      omega
    have hposx2 : pos x2 N = pos (g s) N := by
      rw [pos_of_mem_chain hcf (by rw [← hde2]; exact hvc) (by rw [← hde2]; exact hsubc)]
      omega
    by_cases hh1x : honest_block x1 = true
    · by_cases hh2x : honest_block x2 = true
      · exfalso
        have hx1gb : x1 ≠ GenesisBlock := fun h => by
          have := (List.pairwise_append.1 hp1').2.2 x1 hx1 _ hgbcs
          rw [h] at this
          exact lt_irrefl _ this
        have hx2gb : x2 ≠ GenesisBlock := fun h => by
          have := (List.pairwise_append.1 hpc').2.2 x2 hx2 _ hgbcs
          rw [h] at this
          exact lt_irrefl _ this
        have hx1N : x1 ∈ block_history N :=
          (List.mem_cons.1 (hsub1 x1 (by rw [hde1]; simp))).resolve_left hx1gb
        have hx2N : x2 ∈ block_history N :=
          (List.mem_cons.1 (hsubc x2 (by rw [hde2]; simp))).resolve_left hx2gb
        have e1' := no_honest_pos_share_sb hu hLmap hR hff hcf hsbN hsb
          (List.mem_filter.2 ⟨hx1N, hh1x⟩) hposx1
        have e2' := no_honest_pos_share_sb hu hLmap hR hff hcf hsbN hsb
          (List.mem_filter.2 ⟨hx2N, hh2x⟩) hposx2
        have hv1' : valid_chain (x1 :: e1) := by
          have := hv1; rw [hde1] at this; exact valid_chain_short_l this
        have hv2' : valid_chain (x1 :: e2) := by
          have := hvc; rw [hde2] at this; rw [e1', ← e2']; exact valid_chain_short_l this
        have hee := eq_head_eq_chains hcf hv1' hv2'
          (fun y hy => hsub1 y (by rw [hde1]; simp [hy]))
          (fun y hy => hsubc y (by rw [hde2]; simp [hy]))
        have hsuf : x1 :: e1 <:+ cs :=
          lcsP ⟨d1, hde1.symm⟩ ⟨d2, by rw [hee, e1', ← e2']; exact hde2.symm⟩
        have := hsuf.length_le
        simp only [List.length_cons] at this
        omega
      · exact List.mem_append_right _ (List.mem_map.2
          ⟨x2, List.mem_filter.2 ⟨hx2, by simpa using hh2x⟩, hposx2⟩)
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2
        ⟨x1, List.mem_filter.2 ⟨hx1, by simpa using hh1x⟩, hposx1⟩))

/-- Common prefix against a chain `c` as in `cp_lemma_gen_inc`: the blocks of slots at most `k`
of the chain of `p1` form a suffix of `c`, or the condition of `cp_lemma_gen_inc` holds for
some slot `t ≤ k` (`cp_prune_gen_inc`). -/
theorem cp_prune_gen_inc (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    (a : ℕ) {N : GlobalState Tx Hash Party AdvState} {p1 : Party} {l1 : LocalState Tx Hash Party}
    {c : Chain Tx Hash Party}
    (hsub : ∀ x ∈ c, x ∈ block_hist_gb N ∧ x.sl ≤ N.t_now - 1 + a) (hvc : valid_chain c)
    (hlen : (l1.tT.bestChain (N.t_now - 1) l1.tree).length ≤ c.length)
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hh1 : is_honest p1 = true) (hl1 : N.state_map p1 = some l1) (k : Slot) :
    prune_time k (l1.tT.bestChain (N.t_now - 1) l1.tree) <:+ c ∨
      ∃ t, t ≤ k ∧ (super_slots_range (Party := Party) (t + 1) (N.t_now - 1)).length ≤
        2 * (p_slots_range A (t + 1) (N.t_now + a)).length := by
  have hv1 := l1.tT.best_chain_valid l1.tree (N.t_now - 1)
  by_cases hk : ((lcs (l1.tT.bestChain (N.t_now - 1) l1.tree) c).headD GenesisBlock).sl ≤ k
  · obtain ⟨t, ht, h⟩ := cp_lemma_gen_inc hu hLmap hGB A hA a hsub hvc hlen hR hff hcf hh1 hl1
    exact Or.inr ⟨t, ht.trans hk, h⟩
  · left
    obtain ⟨⟨c1, hc1⟩, hc2⟩ := lcs_suffix (l1.tT.bestChain (N.t_now - 1) l1.tree) c
    have hne : lcs (l1.tT.bestChain (N.t_now - 1) l1.tree) c ≠ [] := fun h => by
      have := lcsP (valid_chain_suffix_gb hv1) (valid_chain_suffix_gb hvc)
      rw [h] at this
      simp at this
    exact (prune_lcs hc1 hv1.2.2 k (by omega) hne).trans hc2

/-- The same as `cp_prune_gen_inc` with the roles of the two chains swapped
(`cp_prune_gen_inc_r`). -/
theorem cp_prune_gen_inc_r (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    (a : ℕ) {N : GlobalState Tx Hash Party AdvState} {p1 : Party} {l1 : LocalState Tx Hash Party}
    {c : Chain Tx Hash Party}
    (hsub : ∀ x ∈ c, x ∈ block_hist_gb N ∧ x.sl ≤ N.t_now - 1 + a) (hvc : valid_chain c)
    (hlen : (l1.tT.bestChain (N.t_now - 1) l1.tree).length ≤ c.length)
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hh1 : is_honest p1 = true) (hl1 : N.state_map p1 = some l1) (k : Slot) :
    prune_time k c <:+ l1.tT.bestChain (N.t_now - 1) l1.tree ∨
      ∃ t, t ≤ k ∧ (super_slots_range (Party := Party) (t + 1) (N.t_now - 1)).length ≤
        2 * (p_slots_range A (t + 1) (N.t_now + a)).length := by
  have hv1 := l1.tT.best_chain_valid l1.tree (N.t_now - 1)
  by_cases hk : ((lcs (l1.tT.bestChain (N.t_now - 1) l1.tree) c).headD GenesisBlock).sl ≤ k
  · obtain ⟨t, ht, h⟩ := cp_lemma_gen_inc hu hLmap hGB A hA a hsub hvc hlen hR hff hcf hh1 hl1
    exact Or.inr ⟨t, ht.trans hk, h⟩
  · left
    obtain ⟨hc1, ⟨c2, hc2⟩⟩ := lcs_suffix (l1.tT.bestChain (N.t_now - 1) l1.tree) c
    have hne : lcs (l1.tT.bestChain (N.t_now - 1) l1.tree) c ≠ [] := fun h => by
      have := lcsP (valid_chain_suffix_gb hv1) (valid_chain_suffix_gb hvc)
      rw [h] at this
      simp at this
    exact (prune_lcs hc2 hvc.2.2 k (by omega) hne).trans hc1

/-- Common prefix for two honest parties in the same state (`common_prefix_lemma_parties`): the
blocks of slots at most `k` of the chain of `p1` form a suffix of the chain of `p2`, or for some
slot `t ≤ k` the super slots in `[t + 1, t_now N - 1)` are at most twice as many as the slots in
`[t + 1, t_now N)` satisfying `A`. -/
theorem common_prefix_lemma_parties (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    {N : GlobalState Tx Hash Party AdvState} {p1 p2 : Party} {l1 l2 : LocalState Tx Hash Party}
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hh1 : is_honest p1 = true) (hh2 : is_honest p2 = true)
    (hl1 : N.state_map p1 = some l1) (hl2 : N.state_map p2 = some l2) (k : Slot) :
    prune_time k (l1.tT.bestChain (N.t_now - 1) l1.tree) <:+
        l2.tT.bestChain (N.t_now - 1) l2.tree ∨
      ∃ t, t ≤ k ∧ (super_slots_range (Party := Party) (t + 1) (N.t_now - 1)).length ≤
        2 * (p_slots_range A (t + 1) N.t_now).length := by
  have hH := reachable_hist_inv hR
  have hsub : ∀ {p : Party} {l : LocalState Tx Hash Party}, N.state_map p = some l →
      ∀ x ∈ l.tT.bestChain (N.t_now - 1) l.tree, x ∈ block_hist_gb N ∧ x.sl ≤ N.t_now - 1 + 0 :=
    fun {p l} hl x hx => by
      have := l.tT.best_chain_in_all _ _ x hx
      simp only [List.mem_filter, decide_eq_true_eq] at this
      exact ⟨hH.state p l hl x this.1, by omega⟩
  rcases le_total (l1.tT.bestChain (N.t_now - 1) l1.tree).length
      (l2.tT.bestChain (N.t_now - 1) l2.tree).length with h | h
  · simpa using cp_prune_gen_inc hu hLmap hGB A hA 0 (hsub hl2) (l2.tT.best_chain_valid _ _) h hR
      hff hcf hh1 hl1 k
  · simpa using cp_prune_gen_inc_r hu hLmap hGB A hA 0 (hsub hl1) (l1.tT.best_chain_valid _ _) h
      hR hff hcf hh2 hl2 k

/-! ## Timed common prefix -/

/-- Timed common prefix for super slots and adversarial slots given by `A`. -/
theorem timed_common_prefix_super (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    (k : Slot) {N1 N2 : GlobalState Tx Hash Party AdvState} (h01 : N0 AdvState ⇓ N1)
    (h12 : N1 ⇓ N2) (hff : forging_free N2) (hcf : collision_free N2)
    {p1 p2 : Party} {l1 : LocalState Tx Hash Party}
    (hh1 : is_honest p1 = true) (hh2 : is_honest p2 = true) (hl1 : N1.state_map p1 = some l1) :
    ∀ {l2 : LocalState Tx Hash Party}, N2.state_map p2 = some l2 →
      prune_time k (l1.tT.bestChain (N1.t_now - 1) l1.tree) <:+
          l2.tT.bestChain (N2.t_now - 1) l2.tree ∨
        ∃ t1 t2, t1 ≤ k ∧ N1.t_now ≤ t2 ∧ t2 ≤ N2.t_now ∧
          (super_slots_range (Party := Party) (t1 + 1) (t2 - 1)).length ≤
            2 * (p_slots_range A (t1 + 1) (t2 + 1)).length := by
  induction h12 with
  | refl =>
    intro l2 hl2
    rcases common_prefix_lemma_parties hu hLmap hGB A hA h01 hff hcf hh1 hh2 hl1 hl2 k with
      h | ⟨t, htk, hb⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, N1.t_now, htk, le_rfl, le_rfl,
        hb.trans (by have := p_slots_size_leq_addr A (t + 1) N1.t_now 1; omega)⟩
  | tail h1M hs ih =>
    rename_i M N2
    intro l2 hl2
    have hstep : M ⇓ N2 := Relation.ReflTransGen.single hs
    have hffM := forging_free_prev hstep hff
    have hcfM := collision_free_prev hstep hcf
    have hRM := h01.trans h1M
    have hM := reachable_inv hRM
    have hHM := reachable_hist_inv hRM
    have htM := hM.time
    obtain ⟨l2M, hlM, -⟩ := (monotone_tree hstep).1 p2 l2 hl2
    have hLM := hM.longest hLmap hlM
    have hsubM : ∀ x ∈ l2M.blocks, x ∈ block_hist_gb M := hHM.state p2 l2M hlM
    rcases ih hffM hcfM hlM with h | ⟨t1, t2, h1, h2, h3, h4⟩
    swap
    · exact Or.inr ⟨t1, t2, h1, h2, h3.trans (monotone_time hstep), h4⟩
    have key : prune_time k (l2M.tT.bestChain (M.t_now - 1) l2M.tree) <:+
          l2.tT.bestChain (N2.t_now - 1) l2.tree ∨
        ∃ t, t ≤ k ∧ (super_slots_range (Party := Party) (t + 1) (M.t_now - 1)).length ≤
          2 * (p_slots_range A (t + 1) (M.t_now + 1)).length := by
      cases hs with
      | Deliver hp =>
        have hF := rcvs_step_facts M M.exec_order
        obtain ⟨l', hl', hbl⟩ := rcvs_own M (uniq_exec_order hu hM) (hM.mem_order hlM) hh2 hlM
        have hl2' : l2 = l' := Option.some.inj (hl2.symm.trans hl')
        subst hl2'
        obtain ⟨l0, hl0, -, htT, -⟩ := hF.state_back p2 l2 hl'
        have : l0 = l2M := Option.some.inj (hl0.symm.trans hlM)
        subst this
        have hL2 : l2.tT.LongestChainRule := by rw [htT]; exact hLM
        simp only [hF.time]
        refine cp_prune_gen_inc hu hLmap hGB A hA 1 (fun x hx => ?_) (l2.tT.best_chain_valid _ _)
          (subset_leq_chains hL2 _ fun b hb => (hbl b).2 (List.mem_append_left _ hb))
          hRM hffM hcfM hh2 hlM k
        have := l2.tT.best_chain_in_all _ _ x hx
        simp only [List.mem_filter, decide_eq_true_eq] at this
        refine ⟨?_, by omega⟩
        rcases List.mem_append.1 ((hbl x).1 this.1) with h | h
        · exact hsubM x h
        · obtain ⟨mt, hmt, -, -, rfl⟩ := mem_tbd.1 h
          exact List.mem_cons_of_mem _ (List.mem_map_of_mem (hHM.buff mt hmt))
      | Bake hp =>
        have hF := bakes_step_facts M M.exec_order
        have hown := bakes_own M (uniq_exec_order hu hM) (hM.mem_order hlM) hh2 hlM
        have hl2' : l2 = (honest_bake M.t_now (TxSelection (Hash := Hash) (AdvState := AdvState)
            M.t_now p2) l2M).2 := Option.some.inj (hl2.symm.trans hown)
        subst hl2'
        have htT := honest_bake_tT M.t_now (TxSelection (Hash := Hash) (AdvState := AdvState)
          M.t_now p2) l2M
        have hL2 : (honest_bake M.t_now (TxSelection (Hash := Hash) (AdvState := AdvState)
            M.t_now p2) l2M).2.tT.LongestChainRule := by rw [htT]; exact hLM
        have hbl := honest_bake_blocks M.t_now (TxSelection (Hash := Hash) (AdvState := AdvState)
          M.t_now p2) l2M
        simp only [hF.time]
        refine cp_prune_gen_inc hu hLmap hGB A hA 1 (fun x hx => ?_) (TreeType.best_chain_valid _ _ _)
          (subset_leq_chains hL2 _ fun b hb => (hbl b).2 (List.mem_append_left _ hb))
          hRM hffM hcfM hh2 hlM k
        have := TreeType.best_chain_in_all _ _ _ x hx
        simp only [List.mem_filter, decide_eq_true_eq] at this
        refine ⟨?_, by omega⟩
        rcases List.mem_append.1 ((hbl x).1 this.1) with h | h
        · exact hsubM x h
        · exfalso
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
          rw [honest_bake_eq] at hm
          split at hm
          · simp only [List.mem_singleton] at hm
            subst hm
            simp only [get_block] at this
            omega
          · simp at hm
      | NextRound hp =>
        have hl2' : l2 = l2M := Option.some.inj (hl2.symm.trans hlM)
        subst hl2'
        simp only [inc_round, round_tick, Nat.add_sub_cancel]
        refine cp_prune_gen_inc hu hLmap hGB A hA 1 (fun x hx => ?_) (l2.tT.best_chain_valid _ _)
          (leq_time_leq_chains hLM l2.tree (by omega)) hRM hffM hcfM hh2 hlM k
        have := l2.tT.best_chain_in_all _ _ x hx
        simp only [List.mem_filter, decide_eq_true_eq] at this
        exact ⟨hsubM x this.1, by omega⟩
      | PermParties ps hps =>
        have hl2' : l2 = l2M := Option.some.inj (hl2.symm.trans hlM)
        subst hl2'
        exact Or.inl (prune_time_suffix k (l2.tT.best_chain_valid _ _).2.2)
      | PermMsgs mb hmb =>
        have hl2' : l2 = l2M := Option.some.inj (hl2.symm.trans hlM)
        subst hl2'
        exact Or.inl (prune_time_suffix k (l2.tT.best_chain_valid _ _).2.2)
    rcases key with h' | ⟨t, htk, hb⟩
    · exact Or.inl (prune_suffix_trans k h h')
    · exact Or.inr ⟨t, M.t_now, htk, monotone_time h1M, monotone_time hstep, hb⟩

/-- Timed common prefix for slot conditions `Q`, implying a super slot, and `A`, implied by a
corrupt leader: for an honest party `p1` with state `l1` in a reachable state `N1` and an honest
party `p2` with state `l2` in a later state `N2`, the blocks of slots at most `k` of the chain of
`p1` form a suffix of the chain of `p2`, or for some slot `t1 ≤ k` and some slot `t2` between
the slots of `N1` and `N2` the slots in `[t1 + 1, t2 - 1)` satisfying `Q` are at most twice as
many as the slots in `[t1 + 1, t2 + 1)` satisfying `A`. -/
theorem timed_common_prefix_gen (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (Q : Slot → Bool) (hQ : ∀ sl, Q sl = true → super_slot (Party := Party) sl = true)
    (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    (k : Slot) {N1 N2 : GlobalState Tx Hash Party AdvState} (h01 : N0 AdvState ⇓ N1)
    (h12 : N1 ⇓ N2) (hff : forging_free N2) (hcf : collision_free N2)
    {p1 p2 : Party} {l1 l2 : LocalState Tx Hash Party}
    (hh1 : is_honest p1 = true) (hh2 : is_honest p2 = true) (hl1 : N1.state_map p1 = some l1)
    (hl2 : N2.state_map p2 = some l2) :
    prune_time k (l1.tT.bestChain (N1.t_now - 1) l1.tree) <:+
        l2.tT.bestChain (N2.t_now - 1) l2.tree ∨
      ∃ t1 t2, t1 ≤ k ∧ N1.t_now ≤ t2 ∧ t2 ≤ N2.t_now ∧
        (p_slots_range Q (t1 + 1) (t2 - 1)).length ≤
          2 * (p_slots_range A (t1 + 1) (t2 + 1)).length := by
  rcases timed_common_prefix_super hu hLmap hGB A hA k h01 h12 hff hcf hh1 hh2 hl1 hl2 with
    h | ⟨t1, t2, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨t1, t2, h1, h2, h3, (p_slots_range_mono_pred hQ _ _).trans h4⟩

/-- Timed common prefix (`timed_common_prefix` of `Properties/CP.v`): for an honest party `p1`
with state `l1` in a reachable state `N1` and an honest party `p2` with state `l2` in a later
state `N2`, the blocks of slots at most `k` of the chain of `p1` form a suffix of the chain of
`p2`, or for some slot `t1 ≤ k` and some slot `t2` between the slots of `N1` and `N2` the super
slots in `[t1 + 1, t2 - 1)` are at most twice as many as the slots in `[t1 + 1, t2 + 1)` with a
corrupt leader. -/
theorem timed_common_prefix [Fintype Party] (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (k : Slot) {N1 N2 : GlobalState Tx Hash Party AdvState} (h01 : N0 AdvState ⇓ N1)
    (h12 : N1 ⇓ N2) (hff : forging_free N2) (hcf : collision_free N2)
    {p1 p2 : Party} {l1 l2 : LocalState Tx Hash Party}
    (hh1 : is_honest p1 = true) (hh2 : is_honest p2 = true) (hl1 : N1.state_map p1 = some l1)
    (hl2 : N2.state_map p2 = some l2) :
    prune_time k (l1.tT.bestChain (N1.t_now - 1) l1.tree) <:+
        l2.tT.bestChain (N2.t_now - 1) l2.tree ∨
      ∃ t1 t2, t1 ≤ k ∧ N1.t_now ≤ t2 ∧ t2 ≤ N2.t_now ∧
        (super_slots_range (Party := Party) (t1 + 1) (t2 - 1)).length ≤
          2 * (adv_slots_range (Party := Party) (t1 + 1) (t2 + 1)).length :=
  timed_common_prefix_super hu hLmap hGB _ (fun p _ hw hc => decide_eq_true ⟨p, hw, hc⟩) k h01
    h12 hff hcf hh1 hh2 hl1 hl2

/-- Timed common prefix, rephrased (`timed_common_prefix'` of `Properties/CP.v`): if for every
slot `t1 ≤ k` and every slot `t2` between the slots of `N1` and `N2` the super slots in
`[t1 + 1, t2 - 1)` are more than twice as many as the slots in `[t1 + 1, t2 + 1)` with a corrupt
leader, the blocks of slots at most `k` of the chain of an honest party in `N1` form a suffix of
the chain of every honest party in `N2`. -/
theorem timed_common_prefix' [Fintype Party] (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (k : Slot) {N1 N2 : GlobalState Tx Hash Party AdvState} (h01 : N0 AdvState ⇓ N1)
    (h12 : N1 ⇓ N2)
    (hadv : ∀ t1 t2, t1 ≤ k → N1.t_now ≤ t2 → t2 ≤ N2.t_now →
      2 * (adv_slots_range (Party := Party) (t1 + 1) (t2 + 1)).length <
        (super_slots_range (Party := Party) (t1 + 1) (t2 - 1)).length)
    (hff : forging_free N2) (hcf : collision_free N2)
    {p1 p2 : Party} {l1 l2 : LocalState Tx Hash Party}
    (hh1 : is_honest p1 = true) (hh2 : is_honest p2 = true) (hl1 : N1.state_map p1 = some l1)
    (hl2 : N2.state_map p2 = some l2) :
    prune_time k (l1.tT.bestChain (N1.t_now - 1) l1.tree) <:+
      l2.tT.bestChain (N2.t_now - 1) l2.tree := by
  rcases timed_common_prefix hu hLmap hGB k h01 h12 hff hcf hh1 hh2 hl1 hl2 with
    h | ⟨t1, t2, h1, h2, h3, h4⟩
  · exact h
  · exact absurd h4 (not_le.2 (hadv t1 t2 h1 h2 h3))

/-- Timed common prefix over the characteristic string: for a pattern `Ps` of letters that
implies exactly one honest leader and a pattern `Pa` that holds at every letter with a corrupt
leader, the blocks of slots at most `k` of the chain of an honest party in `N1` form a suffix
of the chain of every honest party in a later state `N2`, or for some slot `t1 ≤ k` and some
slot `t2` between the slots of `N1` and `N2` the slots in `[t1 + 1, t2 - 1)` whose letter
satisfies `Ps` are at most twice as many as the slots in `[t1 + 1, t2 + 1)` whose letter
satisfies `Pa`. -/
theorem timed_common_prefix_charString [Fintype Party] (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (Ps Pa : SlotLetter → Bool) (hPs : ∀ x, Ps x = true → x.honest = 1)
    (hPa : ∀ x, x.adversarial = true → Pa x = true)
    (k : Slot) {N1 N2 : GlobalState Tx Hash Party AdvState} (h01 : N0 AdvState ⇓ N1)
    (h12 : N1 ⇓ N2) (hff : forging_free N2) (hcf : collision_free N2)
    {p1 p2 : Party} {l1 l2 : LocalState Tx Hash Party}
    (hh1 : is_honest p1 = true) (hh2 : is_honest p2 = true) (hl1 : N1.state_map p1 = some l1)
    (hl2 : N2.state_map p2 = some l2) :
    prune_time k (l1.tT.bestChain (N1.t_now - 1) l1.tree) <:+
        l2.tT.bestChain (N2.t_now - 1) l2.tree ∨
      ∃ t1 t2, t1 ≤ k ∧ N1.t_now ≤ t2 ∧ t2 ≤ N2.t_now ∧
        (p_slots_range (fun sl => Ps (charString (Party := Party) sl)) (t1 + 1) (t2 - 1)).length ≤
          2 * (p_slots_range (fun sl => Pa (charString (Party := Party) sl)) (t1 + 1)
            (t2 + 1)).length :=
  timed_common_prefix_gen hu hLmap hGB _ (fun sl h => (super_slot_iff_charString sl).2 (hPs _ h)) _
    (fun p sl hw hc => hPa _ (by simp only [charString]; exact decide_eq_true ⟨p, hw, hc⟩))
    k h01 h12 hff hcf hh1 hh2 hl1 hl2

end CatCryptCore.Consensus.PoSNSB

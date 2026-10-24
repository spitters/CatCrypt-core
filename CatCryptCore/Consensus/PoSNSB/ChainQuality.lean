/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.ChainQualityPrelims

/-!
# PoS-NSB: chain quality

This file ports the chain-quality theorem of `Properties/CQ.v` of PoS-NSB (Thomsen and
Spitters, *Formalizing Nakamoto-style proof of stake*, CSF 2021). Chain quality bounds from
below the number of honest blocks in every fragment of the chain held by an honest party: if
in every long enough interval of slots the slots with an honest leader outnumber the slots
with an adversarial leader by `w`, a fragment `b_j :: c ++ [b_i]` of the chain contains at
least `w - 1` honest blocks.

The slot conditions are parameters: `chain_quality_gen` counts the slots satisfying a
predicate `Q` that implies an honest leader against the slots satisfying a predicate `A` that
holds whenever some party, initial or not, is a corrupt leader. `chain_quality_charString`
reads both conditions off the characteristic string. The Coq statement `chain_quality` is the
instance `Q = lucky_slot`, `A = adv_slot`.

The theorems assume, as in the Coq development:
* `hu`: the initial parties are distinct (`PartiesUniq`);
* `hLmap`: the tree type of every party follows the longest-chain rule;
* `hGB`: the genesis block is an honest block (`HonestGB`);
* `hff`, `hcf`: the adversary does not forge honest blocks and there are no hash collisions
  among broadcast blocks.

## Main results

* `honest_block_state`, `honest_block_state_ext`: if an honest block `b` lies on the chain
  of an honest party, then at the start of slot `sl b + 1` some honest party holds a chain of
  exactly the length of the part of the chain from `b` on.
* `limit_adv_bp_gen`, `limit_adv_bp`: a valid chain with slots in `[s, e)` has at most as many
  corrupt blocks as there are adversarial slots in `[s, e)`.
* `chain_quality_gen`, `chain_quality`, `chain_quality_charString`: chain quality.

## Departures from the Coq development

* `honest_block_state_ext` takes the hypothesis `b ≠ GenesisBlock`, which the Coq proof
  derives from the axiom `GenesisSlot`; in `chain_quality` it follows from the position of
  the block in the chain. No statement of this file uses `GenesisSlot`.
* `honest_block_state_ext` does not assume that the party holding the chain is honest: the
  blocks of every local tree are broadcast blocks or the genesis block (`HistInv`).
* The proof of `honest_block_state_ext` does not reason backwards step by step from the start
  of slot `sl b + 1`. It locates the baking step of slot `sl b` with `phase_cross` and
  identifies the baker of `b` with `bakes_honest_history`.
* The adversarial slots of `chain_quality_gen` are any predicate `A` that holds at every slot
  with a corrupt leader; `adv_slot` is the Coq choice, over all parties of the finite type
  `Party`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-! ## Fragments and adversarial slots -/

/-- `s2` is a fragment of `s`: `s = s1 ++ s2 ++ s3` for some `s1` and `s3`. -/
def fragment {T : Type} (s2 s : List T) : Prop := ∃ s1 s3, s1 ++ s2 ++ s3 = s

/-- Some party of `ps` is a corrupt leader of slot `sl`. -/
def adv_slot_gen (ps : List Party) (sl : Slot) : Bool :=
  ps.any (fun p => Winner p sl && is_corrupt p)

/-- Some party is a corrupt leader of slot `sl`. -/
def adv_slot [Fintype Party] (sl : Slot) : Bool :=
  decide (∃ p : Party, Winner p sl = true ∧ is_corrupt p = true)

/-- Some initial party is a corrupt leader of the current slot of `N`. -/
def adv_slot_w (N : GlobalState Tx Hash Party AdvState) : Bool :=
  adv_slot_gen (InitParties : List Party) N.t_now

/-- The slots in `[a, b)` with a corrupt leader. -/
def adv_slots_range [Fintype Party] (a b : ℕ) : List Slot :=
  p_slots_range (adv_slot (Party := Party)) a b

/-- The slots with a corrupt leader from the slot of `N` up to the slot of `N'`, excluded. -/
def adv_slots_worlds [Fintype Party] (N N' : GlobalState Tx Hash Party AdvState) : List Slot :=
  adv_slots_range (Party := Party) N.t_now N'.t_now

/-- In `[a, b)`, the slots satisfying `Q` outnumber the slots satisfying `A` by at least `w`. -/
def honest_advantage_range_gen (Q A : Slot → Bool) (w a b : ℕ) : Prop :=
  (p_slots_range A a b).length + w ≤ (p_slots_range Q a b).length

/-- Every interval of at least `d` slots has an advantage of `w` of `Q` over `A`. -/
def honest_advantage_ranges_gt_gen (Q A : Slot → Bool) (w d : ℕ) : Prop :=
  ∀ a b, d ≤ b - a → honest_advantage_range_gen Q A w a b

/-- In `[a, b)`, the slots with an honest leader outnumber the slots with a corrupt leader by
at least `w`. -/
def honest_advantage_range [Fintype Party] (w a b : ℕ) : Prop :=
  honest_advantage_range_gen (lucky_slot (Party := Party)) (adv_slot (Party := Party)) w a b

/-- Every interval of at least `d` slots has an honest advantage of `w`. -/
def honest_advantage_ranges_gt [Fintype Party] (w d : ℕ) : Prop :=
  ∀ a b, d ≤ b - a → honest_advantage_range (Party := Party) w a b

theorem adv_slot_eq_charString [Fintype Party] (sl : Slot) :
    adv_slot (Party := Party) sl = (charString (Party := Party) sl).adversarial := rfl

/-- One more slot adds at most one slot to a range. -/
theorem p_slots_range_succ_le (P : Slot → Bool) (a b : ℕ) :
    (p_slots_range P a (b + 1)).length ≤ (p_slots_range P a b).length + 1 := by
  by_cases hab : a ≤ b
  · have e : nat_range a (b + 1) = nat_range a b ++ [b] := by
      simp only [nat_range]
      rw [show b + 1 - a = (b - a) + 1 by omega, List.range'_concat]
      congr 2
      omega
    rw [p_slots_range, p_slots_range, e, List.filter_append, List.length_append]
    have : ([b].filter P).length ≤ 1 := (List.length_filter_le _ _).trans (by simp)
    omega
  · simp [p_slots_range, nat_range, show b + 1 - a = 0 by omega]

/-! ## Lists -/

/-- A list with an element satisfying `P` splits at the first such element (`findoP`). -/
theorem findo_split {β : Type} (P : β → Bool) :
    ∀ L : List β, (∃ x ∈ L, P x = true) →
      ∃ L1 x L2, L = L1 ++ x :: L2 ∧ P x = true ∧ ∀ y ∈ L1, P y = false
  | [], h => by simp at h
  | x :: xs, h => by
    by_cases hx : P x = true
    · exact ⟨[], x, xs, rfl, hx, by simp⟩
    · obtain ⟨y, hy, hPy⟩ := h
      have hy' : y ∈ xs := by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd hPy hx
        · exact hy
      obtain ⟨L1, z, L2, rfl, hz, hL1⟩ := findo_split P xs ⟨y, hy', hPy⟩
      refine ⟨x :: L1, z, L2, rfl, hz, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · simpa using hx
      · exact hL1 y hy

/-- A list with an element satisfying `P` splits at the last such element (`rfindoP`). -/
theorem rfindo_split {β : Type} (P : β → Bool) :
    ∀ L : List β, (∃ x ∈ L, P x = true) →
      ∃ L1 x L2, L = L1 ++ x :: L2 ∧ P x = true ∧ ∀ y ∈ L2, P y = false
  | [], h => by simp at h
  | x :: xs, h => by
    by_cases hxs : ∃ y ∈ xs, P y = true
    · obtain ⟨L1, z, L2, rfl, hz, hL2⟩ := rfindo_split P xs hxs
      exact ⟨x :: L1, z, L2, rfl, hz, hL2⟩
    · push Not at hxs
      have hx : P x = true := by
        obtain ⟨y, hy, hPy⟩ := h
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hPy
        · exact absurd hPy (hxs y hy)
      exact ⟨[], x, xs, rfl, hx, fun y hy => by simpa using hxs y hy⟩

/-- The last element of `L ++ [b]` lies in every suffix `x :: L2`. -/
theorem mem_of_append_singleton {β : Type} {L L1 L2 : List β} {b x : β}
    (h : L ++ [b] = L1 ++ x :: L2) : b ∈ x :: L2 := by
  rcases List.eq_nil_or_concat L2 with rfl | ⟨L2', z, rfl⟩
  · have := (List.append_inj' h rfl).2
    simp only [List.cons.injEq, and_true] at this
    simp [this]
  · rw [List.concat_eq_append, ← List.cons_append, ← List.append_assoc] at h
    have := (List.append_inj' h rfl).2
    simp only [List.cons.injEq, and_true] at this
    simp [this]

/-- A relation that holds pairwise on `L1 ++ x :: (L2 ++ y :: L3)` relates `x` to `y`, and
`x` to every element of `L2` and every element of `L2` to `y`; it holds pairwise on `L2`. -/
theorem pairwise_mid {β : Type} {R : β → β → Prop} {L1 L2 L3 : List β} {x y : β}
    (h : (L1 ++ x :: (L2 ++ y :: L3)).Pairwise R) :
    R x y ∧ (∀ z ∈ L2, R x z ∧ R z y) ∧ L2.Pairwise R := by
  rw [List.pairwise_append] at h
  obtain ⟨-, h2, -⟩ := h
  rw [List.pairwise_cons, List.pairwise_append] at h2
  obtain ⟨hx, h2, -, hz⟩ := h2
  exact ⟨hx y (by simp), fun z hz' => ⟨hx z (by simp [hz']), hz z hz' y (by simp)⟩, h2⟩

/-! ## Phases -/

/-- An execution that reaches phase `k` contains a step from phase `k - 1` to phase `k`. -/
theorem phase_cross {N N' : GlobalState Tx Hash Party AdvState} (h : N ⇓ N') (k : ℕ)
    (hk : phase N < k) (hk' : k ≤ phase N') :
    ∃ A B, N ⇓ A ∧ A ⤳ B ∧ B ⇓ N' ∧ phase A + 1 = k ∧ phase B = k := by
  induction h with
  | refl => omega
  | tail hNM hs ih =>
    rename_i M N2
    by_cases hkM : k ≤ phase M
    · obtain ⟨A, B, h1, h2, h3, h4, h5⟩ := ih hkM
      exact ⟨A, B, h1, h2, h3.tail hs, h4, h5⟩
    · rcases step_phase hs with h | ⟨h, -⟩
      · exact ⟨M, N2, hNM, hs, .refl, by omega, by omega⟩
      · omega

/-- From the end of a baking phase up to the start of the next slot, the history and the local
states do not change. -/
theorem baked_next {X Y : GlobalState Tx Hash Party AdvState} (h : X ⇓ Y)
    (hX : X.progress = .Baked) (hph : phase Y ≤ phase X + 1) :
    Y.history = X.history ∧ Y.state_map = X.state_map := by
  have hphX : phase X = 3 * X.t_now + 2 := by simp [phase, hX]
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail hXM hs ih =>
    rename_i M Y'
    have hm := monotone_phase hXM
    have hle : phase M ≤ phase Y' := by rcases step_phase hs with h | h <;> omega
    cases hs with
    | Deliver hp =>
      exfalso
      have : phase M = 3 * M.t_now := by simp [phase, hp]
      have e := (rcvs_step_facts M M.exec_order).time
      simp only [phase, hX, e] at hph
      omega
    | Bake hp =>
      exfalso
      have : phase M = 3 * M.t_now + 1 := by simp [phase, hp]
      have e := (bakes_step_facts M M.exec_order).time
      simp only [phase, hX, e] at hph
      omega
    | NextRound hp => exact ih (by omega)
    | PermParties ps hps => exact ih (by omega)
    | PermMsgs mb hmb => exact ih (by omega)

/-! ## The state in which an honest block was baked -/

/-- An honest block `b`, other than the genesis block, on the chain of a party, with a
slot not before the start `M` of a slot: at the start of slot `sl b + 1`, after `M`, the baker
of `b` is an honest party whose chain is exactly as long as the part of the chain from `b` on
(`honest_block_state_ext`). -/
theorem honest_block_state_ext (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    {M N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ M) (hMN : M ⇓ N)
    (hff : forging_free N) (hcf : collision_free N) (hready : M.progress = .Ready)
    {p : Party} {l : LocalState Tx Hash Party} (hl : N.state_map p = some l) {bsH bsT : Chain Tx Hash Party} {b : Block Tx Hash Party}
    (hb : honest_block b = true) (hgb : b ≠ GenesisBlock) (hsl : M.t_now ≤ b.sl)
    (hc : bsH ++ b :: bsT = l.tT.bestChain (N.t_now - 1) l.tree) :
    ∃ N2 p', M ⇓ N2 ∧ N2 ⇓ N ∧ N2.t_now = b.sl + 1 ∧ N2.progress = .Ready ∧
      is_honest p' = true ∧ ∃ l', N2.state_map p' = some l' ∧
        (l'.tT.bestChain (N2.t_now - 1) l'.tree).length = (b :: bsT).length := by
  have hRN := hR.trans hMN
  have hN := reachable_inv hRN
  have hH := reachable_hist_inv hRN
  have hbmem : b ∈ l.tT.bestChain (N.t_now - 1) l.tree := by rw [← hc]; simp
  have hball := l.tT.best_chain_in_all _ _ b hbmem
  simp only [List.mem_filter, decide_eq_true_eq] at hball
  have htN := hN.time
  have hbN : b ∈ block_history N := by
    rcases List.mem_cons.1 (hH.state p l hl b hball.1) with h | h
    · exact absurd h hgb
    · exact h
  obtain ⟨N2, hp2, ht2, hMN2, hN2N⟩ := slot_in_between hready hMN (sl := b.sl + 1) (by omega)
    (by omega)
  have hph2 : phase N2 = 3 * (b.sl + 1) := by simp [phase, hp2, ht2]
  have hphM : phase M = 3 * M.t_now := by simp [phase, hready]
  obtain ⟨A, B, hMA, hAB, hBN2, hphA, hphB⟩ :=
    phase_cross hMN2 (3 * b.sl + 2) (by omega) (by omega)
  have hRA := hR.trans hMA
  have hA := reachable_inv hRA
  have hHA := reachable_hist_inv hRA
  have hBN := hBN2.trans hN2N
  have hAN := (Relation.ReflTransGen.single hAB).trans hBN
  have hffA := forging_free_prev hAN hff
  have hstep := step_phase hAB
  cases hAB with
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
  | Bake hp =>
    have hAt : A.t_now = b.sl := by
      have : phase A = 3 * A.t_now + 1 := by simp [phase, hp]
      omega
    have hbF : b ∈ block_history (A.exec_order.foldr party_bake_step_world A) :=
      honest_block_preserved_phase hBN hff b hbN hb (by omega)
    rcases bakes_honest_history A hff.2 A.exec_order (.ProgressB (.RefineStepB hBN)) b hbF hb
      with hbA | ⟨pre, q, qs, hord, hhq, lq, hlq, hw, hbq⟩
    · exfalso
      have := no_premature_honest_blocks_D hRA hffA hp b (List.mem_filter.2 ⟨hbA, hb⟩)
      omega
    have hnd := uniq_exec_order hu hA
    have hqo : q ∈ A.exec_order := by rw [hord]; simp
    have hqs : q ∉ qs := by
      rw [hord] at hnd
      exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
    have hlqA : A.state_map q = some lq := (bakes_state_notin A hqs).symm.trans hlq
    have hown := bakes_own A hnd hqo hhq hlqA
    have hbake : (honest_bake A.t_now (TxSelection (Hash := Hash) (AdvState := AdvState)
        A.t_now q) lq).2 = extend_tree_l lq b := by
      rw [honest_bake_eq, ite_eq_left hw, hbq]
      rfl
    obtain ⟨-, hst⟩ := baked_next hBN2 rfl (by omega)
    have hl' : N2.state_map q = some (extend_tree_l lq b) := by
      rw [hst, ← hbake]
      exact hown
    refine ⟨N2, q, hMN2, hN2N, ht2, hp2, hhq, extend_tree_l lq b, hl', ?_⟩
    have hbsl : b.sl = A.t_now := by rw [hbq]; rfl
    have hbbid : b.bid = lq.pk := by rw [hbq]; rfl
    have hbpred : b.pred = HashB ((lq.tT.bestChain (A.t_now - 1) lq.tree).headD GenesisBlock) := by
      rw [hbq]; rfl
    simp only [extend_tree_l]
    rw [ht2, Nat.add_sub_cancel, hbsl]
    have hAt0 := hA.time
    have hCv := lq.tT.best_chain_valid lq.tree (A.t_now - 1)
    obtain ⟨c0, cs, hC⟩ := List.exists_cons_of_ne_nil (valid_chain_ne_nil hCv)
    have hc0 : c0.sl ≤ A.t_now - 1 := best_chain_time _ _ _ c0 (by rw [hC]; simp)
    have hvbC : valid_chain (b :: lq.tT.bestChain (A.t_now - 1) lq.tree) := by
      rw [hC] at hCv ⊢
      refine valid_chain_ext hCv ?_ ?_ ?_
      · show Winner b.bid b.sl = true
        rw [hbbid, hbsl]; exact hw
      · show b.pred = HashB c0
        rw [hbpred, hC]; rfl
      · show c0.sl < b.sl
        omega
    have hvbT : valid_chain (b :: bsT) := by
      have := l.tT.best_chain_valid l.tree (N.t_now - 1)
      rw [← hc] at this
      exact valid_chain_short_l this
    have hCsub : ∀ x ∈ lq.tT.bestChain (A.t_now - 1) lq.tree, x ∈ block_hist_gb N := by
      intro x hx
      have := lq.tT.best_chain_in_all _ _ x hx
      simp only [List.mem_filter] at this
      exact block_hist_gb_monotone hAN x (hHA.state q lq hlqA x this.1)
    have hTsub : ∀ x ∈ bsT, x ∈ block_hist_gb N := by
      intro x hx
      have := l.tT.best_chain_in_all _ _ x (by rw [← hc]; simp [hx])
      simp only [List.mem_filter] at this
      exact hH.state p l hl x this.1
    have hCT := eq_head_eq_chains hcf hvbC hvbT hCsub hTsub
    have hLq := hA.longest hLmap hlqA
    have hup := bc_ext_max_increase hLq lq.tree A.t_now b hbsl
    have hlow := hLq (b :: bsT) A.t_now (lq.tT.extendTree lq.tree b) hvbT fun x hx => by
      simp only [List.mem_filter, decide_eq_true_eq]
      rw [lq.tT.all_extend]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by simp, by omega⟩
      · rw [← hCT] at hx
        have := lq.tT.best_chain_in_all _ _ x hx
        simp only [List.mem_filter, decide_eq_true_eq] at this
        exact ⟨List.mem_append_left _ this.1, by omega⟩
    rw [hCT] at hup
    simp only [List.length_cons] at hlow ⊢
    omega

/-- An honest block `b` on the chain of an honest party: at the start of slot `sl b + 1` some
honest party holds a chain exactly as long as the part of the chain from `b` on
(`honest_block_state`). -/
theorem honest_block_state (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    {N : GlobalState Tx Hash Party AdvState} (hR : N0 AdvState ⇓ N)
    (hff : forging_free N) (hcf : collision_free N)
    {p : Party} {l : LocalState Tx Hash Party} (hh : is_honest p = true)
    (hl : N.state_map p = some l) {bsH bsT : Chain Tx Hash Party} {b : Block Tx Hash Party}
    (hb : honest_block b = true)
    (hc : bsH ++ b :: bsT = l.tT.bestChain (N.t_now - 1) l.tree) :
    ∃ N' p', N0 AdvState ⇓ N' ∧ N' ⇓ N ∧ N'.t_now = b.sl + 1 ∧ N'.progress = .Ready ∧
      is_honest p' = true ∧ ∃ l', N'.state_map p' = some l' ∧
        (l'.tT.bestChain (N'.t_now - 1) l'.tree).length = (b :: bsT).length := by
  have hv : valid_chain (b :: bsT) := by
    have := l.tT.best_chain_valid l.tree (N.t_now - 1)
    rw [← hc] at this
    exact valid_chain_short_l this
  by_cases hgb : b = GenesisBlock
  · subst hgb
    have hT := valid_chain_gb_head hv
    subst hT
    have hN := reachable_inv hR
    have hbmem : GenesisBlock ∈ l.tT.bestChain (N.t_now - 1) l.tree := by rw [← hc]; simp
    have hsl := best_chain_time _ _ _ _ hbmem
    have htN := hN.time
    obtain ⟨N2, hp2, ht2, h02, h2N⟩ := slot_in_between (N := N0 AdvState) rfl hR
      (sl := (GenesisBlock : Block Tx Hash Party).sl + 1) (by simp [N0]) (by omega)
    have hN2 := reachable_inv h02
    have hpI := (hN.state_init p).1 (by simp [hl])
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 ((hN2.state_init p).2 hpI)
    refine ⟨N2, p, h02, h2N, ht2, hp2, hh, l', hl', ?_⟩
    rw [ht2, Nat.add_sub_cancel,
      valid_chain_le_gb (l'.tT.best_chain_valid _ _) (best_chain_time _ _ _)]
  · have hN0 : (N0 AdvState : GlobalState Tx Hash Party AdvState).t_now ≤ b.sl := by
      have hT : bsT ≠ [] := fun h => hgb (by subst h; exact valid_chain_single hv)
      have hgbT := valid_chain_starts_gb (valid_chain_tail hv hT)
      have := List.rel_of_pairwise_cons hv.2.2 hgbT
      simp only [lt_slots] at this
      simp only [N0]
      omega
    exact honest_block_state_ext hu hLmap .refl hR hff hcf rfl hl hb hgb hN0 hc

/-! ## Corrupt blocks -/

/-- A chain of correct blocks with strictly decreasing slots in `[s, e)` has at most as many
corrupt blocks as there are slots in `[s, e)` satisfying `A`, if `A` holds at every slot with
a corrupt leader. -/
theorem limit_adv_bp_gen (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    (s e : ℕ) (bs : Chain Tx Hash Party) (hr : ∀ b ∈ bs, s ≤ b.sl ∧ b.sl < e)
    (hc : correct_blocks bs) (hd : decreasing_slots bs) :
    (bs.filter (fun b => !honest_block b)).length ≤ (p_slots_range A s e).length := by
  have hDp : (bs.filter (fun b => !honest_block b)).Pairwise lt_slots := hd.filter _
  have hnd : ((bs.filter (fun b => !honest_block b)).map Block.sl).Nodup :=
    List.pairwise_map.2 (hDp.imp fun h => Nat.ne_of_gt h)
  have hsub : (bs.filter (fun b => !honest_block b)).map Block.sl ⊆ p_slots_range A s e := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hb, hhb⟩ := List.mem_filter.1 hb
    simp only [p_slots_range, nat_range, List.mem_filter, List.mem_range'_1]
    refine ⟨by have := hr b hb; omega, hA b.bid b.sl (hc b hb) ?_⟩
    simpa [honest_block, honest_not_corrupt] using hhb
  simpa using (hnd.subperm hsub).length_le

/-- A chain of correct blocks with strictly decreasing slots in `[s, e)` has at most as many
corrupt blocks as there are slots with a corrupt leader in `[s, e)` (`limit_adv_bp`). -/
theorem limit_adv_bp [Fintype Party] (s e : ℕ) (bs : Chain Tx Hash Party)
    (hr : ∀ b ∈ bs, s ≤ b.sl ∧ b.sl < e) (hc : correct_blocks bs) (hd : decreasing_slots bs) :
    (bs.filter (fun b => !honest_block b)).length ≤ (adv_slots_range (Party := Party) s e).length :=
  limit_adv_bp_gen _ (fun p _ hw hc => decide_eq_true ⟨p, hw, hc⟩) s e bs hr hc hd

/-- If a chain as in `limit_adv_bp_gen` is longer than the number of slots satisfying `A` by
`w`, it has at least `w` honest blocks. -/
theorem limit_adv_bp_imply_honesty_gen (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    (s e : ℕ) (bs : Chain Tx Hash Party) (w : ℕ) (hr : ∀ b ∈ bs, s ≤ b.sl ∧ b.sl < e)
    (hc : correct_blocks bs) (hd : decreasing_slots bs)
    (hw : (p_slots_range A s e).length + w ≤ bs.length) :
    w ≤ (honest_blocks bs).length := by
  have h1 := limit_adv_bp_gen A hA s e bs hr hc hd
  have h2 := List.length_eq_length_filter_add (l := bs) honest_block
  simp only [honest_blocks]
  omega

/-- A chain as in `limit_adv_bp` that is longer than the number of slots with a corrupt leader
by `w` has at least `w` honest blocks (`limit_adv_bp_imply_honesty`). -/
theorem limit_adv_bp_imply_honesty [Fintype Party] (s e : ℕ) (bs : Chain Tx Hash Party) (w : ℕ)
    (hr : ∀ b ∈ bs, s ≤ b.sl ∧ b.sl < e) (hc : correct_blocks bs) (hd : decreasing_slots bs)
    (hw : (adv_slots_range (Party := Party) s e).length + w ≤ bs.length) :
    w ≤ (honest_blocks bs).length :=
  limit_adv_bp_imply_honesty_gen _ (fun p _ hw hc => decide_eq_true ⟨p, hw, hc⟩) s e bs w hr hc
    hd hw

/-! ## Chain quality -/

/-- Chain quality for slot conditions `Q`, implying an honest leader, and `A`, implied by a
corrupt leader: if every interval of at least `sl b_j - (sl b_i + 1)` slots has an advantage of
`w` of `Q` over `A`, a fragment `b_j :: c ++ [b_i]` of the chain of an honest party contains
at least `w - 1` honest blocks. -/
theorem chain_quality_gen (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (Q : Slot → Bool) (hQ : ∀ sl, Q sl = true → lucky_slot (Party := Party) sl = true)
    (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    {N : GlobalState Tx Hash Party AdvState} {p : Party} {l : LocalState Tx Hash Party}
    {b_j b_i : Block Tx Hash Party} {c : Chain Tx Hash Party} {w : ℕ}
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hl : N.state_map p = some l) (hh : is_honest p = true)
    (hfrag : fragment ([b_j] ++ c ++ [b_i]) (l.tT.bestChain (N.t_now - 1) l.tree))
    (hadv : honest_advantage_ranges_gt_gen Q A w (b_j.sl - (b_i.sl + 1))) :
    w - 1 ≤ (honest_blocks ([b_j] ++ c ++ [b_i])).length := by
  obtain ⟨c1, c2, hbc⟩ := hfrag
  have hN := reachable_inv hR
  have htN := hN.time
  have hL := hN.longest hLmap hl
  have hv := l.tT.best_chain_valid l.tree (N.t_now - 1)
  have hbt := best_chain_time l.tT l.tree (N.t_now - 1)
  rcases Nat.eq_zero_or_pos w with rfl | hw0
  · simp
  have hbc1 : l.tT.bestChain (N.t_now - 1) l.tree = c1 ++ b_j :: (c ++ b_i :: c2) := by
    rw [← hbc]; simp
  have hvi : valid_chain (b_i :: c2) := by
    rw [hbc1, show c1 ++ b_j :: (c ++ b_i :: c2) = (c1 ++ b_j :: c) ++ b_i :: c2 by simp] at hv
    exact valid_chain_short_l hv
  -- the first honest block from `b_i` on
  obtain ⟨c21, b_i', c22, hsplit_i, hhi', hc21⟩ :=
    findo_split honest_block (b_i :: c2) ⟨GenesisBlock, valid_chain_starts_gb hvi, hGB⟩
  have hbc2 : l.tT.bestChain (N.t_now - 1) l.tree = (c1 ++ b_j :: (c ++ c21)) ++ b_i' :: c22 := by
    rw [hbc1, hsplit_i]; simp
  have hpw := hv.2.2
  rw [hbc2] at hpw
  have hXi : ∀ x ∈ c1 ++ b_j :: (c ++ c21), b_i'.sl < x.sl :=
    fun x hx => (List.pairwise_append.1 hpw).2.2 x hx b_i' List.mem_cons_self
  have hii : b_i'.sl ≤ b_i.sl := by
    have : b_i' ∈ b_i :: c2 := by rw [hsplit_i]; simp
    rcases List.mem_cons.1 this with h | h
    · rw [h]
    · exact le_of_lt (List.rel_of_pairwise_cons hvi.2.2 h)
  have hbcmem : ∀ x ∈ c1 ++ b_j :: (c ++ c21), x ∈ l.tT.bestChain (N.t_now - 1) l.tree := by
    intro x hx; rw [hbc2]; exact List.mem_append_left _ hx
  have hc21f : c21.filter honest_block = [] :=
    List.filter_eq_nil_iff.2 fun x hx => by simp [hc21 x hx]
  obtain ⟨Ni, pi, hRi, hiN, hti, hpi, hhpi, li, hli, hleni⟩ :=
    honest_block_state hu hLmap hR hff hcf hh hl hhi' hbc2.symm
  by_cases hfront : ∃ x ∈ c1 ++ [b_j], honest_block x = true
  · -- the last honest block up to `b_j`
    obtain ⟨c11, b_j', c12, hsplit_j, hhj', hc12⟩ := rfindo_split honest_block _ hfront
    have hbc3 : l.tT.bestChain (N.t_now - 1) l.tree =
        c11 ++ b_j' :: ((c12 ++ c ++ c21) ++ b_i' :: c22) := by
      rw [hbc2, show c1 ++ b_j :: (c ++ c21) = (c1 ++ [b_j]) ++ (c ++ c21) by simp, hsplit_j]
      simp
    have hpw3 := hv.2.2
    rw [hbc3] at hpw3
    obtain ⟨hji, hY, hYd⟩ := pairwise_mid hpw3
    simp only [lt_slots] at hji hY
    have hjj : b_j.sl ≤ b_j'.sl := by
      rcases List.mem_cons.1 (mem_of_append_singleton hsplit_j) with h | h
      · rw [h]
      · exact le_of_lt (hY b_j (by simp [h])).1
    have hgbj : b_j' ≠ GenesisBlock := by
      intro h
      have hvj : valid_chain (b_j' :: ((c12 ++ c ++ c21) ++ b_i' :: c22)) := by
        have := hv; rw [hbc3] at this; exact valid_chain_short_l this
      rw [h] at hvj
      exact absurd (valid_chain_gb_head hvj) (by simp)
    obtain ⟨Nj, pj, hij, hjN, htj, hpj, hhpj, lj, hlj, hlenj⟩ :=
      honest_block_state_ext hu hLmap hRi hiN hff hcf hpi hl hhj' hgbj (by omega) hbc3.symm
    have hadv' := hadv (b_i'.sl + 1) b_j'.sl (by omega)
    unfold honest_advantage_range_gen at hadv'
    have hcg := chain_growth_parties_gen hu hL hLmap Q hQ
      ((p_slots_range A (b_i'.sl + 1) b_j'.sl).length + w) hRi hij (by omega) hpi hhpi hhpj hli
      hlj (by rw [hti, htj, Nat.add_sub_cancel]; omega)
    rw [hleni, hlenj] at hcg
    simp only [List.length_cons, List.length_append] at hcg
    have hYh := limit_adv_bp_imply_honesty_gen A hA (b_i'.sl + 1) b_j'.sl (c12 ++ c ++ c21)
      (w - 1) (fun y hy => by have := hY y hy; omega)
      (fun y hy => hv.1 y (by
        rw [hbc3]; simp only [List.mem_append, List.mem_cons] at hy ⊢; tauto))
      hYd (by simp only [List.length_append]; omega)
    have hc12f : c12.filter honest_block = [] :=
      List.filter_eq_nil_iff.2 fun x hx => by simp [hc12 x hx]
    simp only [honest_blocks, List.filter_append, hc12f, hc21f, List.nil_append,
      List.append_nil, List.length_append] at hYh ⊢
    omega
  · push Not at hfront
    have hc1f : (c1 ++ [b_j]).filter honest_block = [] :=
      List.filter_eq_nil_iff.2 fun x hx => by simpa using hfront x hx
    have hbjN : b_j.sl ≤ N.t_now - 1 := hbt b_j (by rw [hbc1]; simp)
    have hij : b_i'.sl < b_j.sl := hXi b_j (by simp)
    have hadv' := hadv (b_i'.sl + 1) (N.t_now - 1) (by omega)
    unfold honest_advantage_range_gen at hadv'
    have hcg := chain_growth_parties_gen hu hL hLmap Q hQ
      ((p_slots_range A (b_i'.sl + 1) (N.t_now - 1)).length + w) hRi hiN (by omega) hpi hhpi hh
      hli hl (by rw [hti]; omega)
    rw [hleni, hbc2] at hcg
    simp only [List.length_cons, List.length_append] at hcg
    have hsucc := p_slots_range_succ_le A (b_i'.sl + 1) (N.t_now - 1)
    rw [Nat.sub_add_cancel htN] at hsucc
    have hXh := limit_adv_bp_imply_honesty_gen A hA (b_i'.sl + 1) N.t_now
      (c1 ++ b_j :: (c ++ c21)) (w - 1)
      (fun x hx => ⟨by have := hXi x hx; omega, by have := hbt x (hbcmem x hx); omega⟩)
      (fun x hx => hv.1 x (hbcmem x hx))
      (List.pairwise_append.1 hpw).1 (by simp only [List.length_append, List.length_cons]; omega)
    rw [show c1 ++ b_j :: (c ++ c21) = (c1 ++ [b_j]) ++ (c ++ c21) by simp] at hXh
    simp only [honest_blocks, List.filter_append, hc1f, hc21f, List.nil_append,
      List.append_nil, List.length_append] at hXh ⊢
    omega

/-- Chain quality (`chain_quality` of `Properties/CQ.v`): if every interval of at least
`sl b_j - (sl b_i + 1)` slots has `w` more slots with an honest leader than slots with a
corrupt leader, a fragment `b_j :: c ++ [b_i]` of the chain of an honest party contains at
least `w - 1` honest blocks. -/
theorem chain_quality [Fintype Party] (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    {N : GlobalState Tx Hash Party AdvState} {p : Party} {l : LocalState Tx Hash Party}
    {b_j b_i : Block Tx Hash Party} {c : Chain Tx Hash Party} {w : ℕ}
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hl : N.state_map p = some l) (hh : is_honest p = true)
    (hfrag : fragment ([b_j] ++ c ++ [b_i]) (l.tT.bestChain (N.t_now - 1) l.tree))
    (hadv : honest_advantage_ranges_gt (Party := Party) w (b_j.sl - (b_i.sl + 1))) :
    w - 1 ≤ (honest_blocks ([b_j] ++ c ++ [b_i])).length :=
  chain_quality_gen hu hLmap hGB lucky_slot (fun _ h => h) adv_slot
    (fun p _ hw hc => decide_eq_true ⟨p, hw, hc⟩) hR hff hcf hl hh hfrag hadv

/-- Chain quality over the characteristic string: for a pattern `Ph` of letters that implies
at least one honest leader and a pattern `Pa` that holds at every letter with a corrupt
leader, if every interval of at least `sl b_j - (sl b_i + 1)` slots has `w` more slots whose
letter satisfies `Ph` than slots whose letter satisfies `Pa`, a fragment `b_j :: c ++ [b_i]` of
the chain of an honest party contains at least `w - 1` honest blocks. -/
theorem chain_quality_charString [Fintype Party] (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (Ph Pa : SlotLetter → Bool) (hPh : ∀ x, Ph x = true → 0 < x.honest)
    (hPa : ∀ x, x.adversarial = true → Pa x = true)
    {N : GlobalState Tx Hash Party AdvState} {p : Party} {l : LocalState Tx Hash Party}
    {b_j b_i : Block Tx Hash Party} {c : Chain Tx Hash Party} {w : ℕ}
    (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hl : N.state_map p = some l) (hh : is_honest p = true)
    (hfrag : fragment ([b_j] ++ c ++ [b_i]) (l.tT.bestChain (N.t_now - 1) l.tree))
    (hadv : honest_advantage_ranges_gt_gen (fun sl => Ph (charString (Party := Party) sl))
      (fun sl => Pa (charString (Party := Party) sl)) w (b_j.sl - (b_i.sl + 1))) :
    w - 1 ≤ (honest_blocks ([b_j] ++ c ++ [b_i])).length :=
  chain_quality_gen hu hLmap hGB _ (fun sl h => (lucky_slot_iff_charString sl).2 (hPh _ h)) _
    (fun p sl hw hc => hPa _ (by simp only [charString]; exact decide_eq_true ⟨p, hw, hc⟩))
    hR hff hcf hl hh hfrag hadv

end CatCryptCore.Consensus.PoSNSB

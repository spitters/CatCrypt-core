/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.ChainQuality

/-!
# PoS-NSB: an honest block near the tip

If in every interval of at least `d` slots the slots with an honest leader outnumber the slots
with an adversarial leader by `w ≥ 2`, the chain held by an honest party at slot `t` contains an
honest block of slot greater than `t - d - 2`.

The result is not in the PoS-NSB development of `Properties/CQ.v` (Thomsen and Spitters,
*Formalizing Nakamoto-style proof of stake*, CSF 2021). Its proof is the second case of the
proof of `chain_quality` there (`chain_quality_gen`, the case without an honest block up to
`b_j`), applied to the whole chain: the blocks above the newest honest block `b` are corrupt
blocks with distinct slots in `[sl b + 1, t)`, while chain growth from slot `sl b + 1` adds at
least one block per slot of `[sl b + 1, t - 1)` with an honest leader.

As in `ChainQuality.lean`, `honest_tip_gen` counts the slots satisfying a predicate `Q` that
implies an honest leader against the slots satisfying a predicate `A` that holds whenever some
party is a corrupt leader; `honest_tip` is the instance `Q = lucky_slot`, `A = adv_slot`.

## Main results

* `honest_tip_gen`, `honest_tip`: the chain of an honest party at slot `t` contains an honest
  block `b` with `t < sl b + d + 2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-- An honest block near the tip, for slot conditions `Q`, implying an honest leader, and `A`,
implied by a corrupt leader: if every interval of at least `d` slots has an advantage of
`w ≥ 2` of `Q` over `A`, the chain of an honest party at slot `t` contains an honest block `b`
with `t < sl b + d + 2`. -/
theorem honest_tip_gen (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    (Q : Slot → Bool) (hQ : ∀ sl, Q sl = true → lucky_slot (Party := Party) sl = true)
    (A : Slot → Bool)
    (hA : ∀ (p : Party) sl, Winner p sl = true → is_corrupt p = true → A sl = true)
    {N : GlobalState Tx Hash Party AdvState} {p : Party} {l : LocalState Tx Hash Party}
    {w d : ℕ} (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hl : N.state_map p = some l) (hh : is_honest p = true) (hw : 2 ≤ w)
    (hadv : honest_advantage_ranges_gt_gen Q A w d) :
    ∃ b ∈ l.tT.bestChain (N.t_now - 1) l.tree, honest_block b = true ∧
      N.t_now < b.sl + d + 2 := by
  have hN := reachable_inv hR
  have htN := hN.time
  have hL := hN.longest hLmap hl
  have hv := l.tT.best_chain_valid l.tree (N.t_now - 1)
  have hbt := best_chain_time l.tT l.tree (N.t_now - 1)
  -- the newest honest block of the chain
  obtain ⟨X, b, Y, hsplit, hhb, hX⟩ := findo_split honest_block
    (l.tT.bestChain (N.t_now - 1) l.tree) ⟨GenesisBlock, valid_chain_starts_gb hv, hGB⟩
  refine ⟨b, by rw [hsplit]; simp, hhb, ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨Ni, pi, hRi, hiN, hti, hpi, hhpi, li, hli, hleni⟩ :=
    honest_block_state hu hLmap hR hff hcf hh hl hhb hsplit.symm
  have hadv' := hadv (b.sl + 1) (N.t_now - 1) (by omega)
  unfold honest_advantage_range_gen at hadv'
  have hcg := chain_growth_parties_gen hu hL hLmap Q hQ
    (p_slots_range Q (b.sl + 1) (N.t_now - 1)).length hRi hiN (by omega) hpi hhpi hh hli hl
    (by rw [hti])
  rw [hleni, hsplit] at hcg
  simp only [List.length_cons, List.length_append] at hcg
  have hpw := hv.2.2
  rw [hsplit] at hpw
  have hXmem : ∀ x ∈ X, x ∈ l.tT.bestChain (N.t_now - 1) l.tree := by
    intro x hx; rw [hsplit]; exact List.mem_append_left _ hx
  have hXlim := limit_adv_bp_gen A hA (b.sl + 1) N.t_now X
    (fun x hx => ⟨by
        have := (List.pairwise_append.1 hpw).2.2 x hx b List.mem_cons_self
        simp only [lt_slots] at this
        omega,
      by have := hbt x (hXmem x hx); omega⟩)
    (fun x hx => hv.1 x (hXmem x hx)) (List.pairwise_append.1 hpw).1
  rw [List.filter_eq_self.2 fun x hx => by simp [hX x hx]] at hXlim
  have hsucc := p_slots_range_succ_le A (b.sl + 1) (N.t_now - 1)
  rw [Nat.sub_add_cancel htN] at hsucc
  omega

/-- An honest block near the tip: if every interval of at least `d` slots has `w ≥ 2` more
slots with an honest leader than slots with a corrupt leader, the chain of an honest party at
slot `t` contains an honest block `b` with `t < sl b + d + 2`. -/
theorem honest_tip [Fintype Party] (hu : (InitParties : List Party).Nodup)
    (hLmap : ∀ p : Party, (TreeTypeMap (Tx := Tx) (Hash := Hash) (AdvState := AdvState) p).LongestChainRule)
    (hGB : honest_block (GenesisBlock : Block Tx Hash Party) = true)
    {N : GlobalState Tx Hash Party AdvState} {p : Party} {l : LocalState Tx Hash Party}
    {w d : ℕ} (hR : N0 AdvState ⇓ N) (hff : forging_free N) (hcf : collision_free N)
    (hl : N.state_map p = some l) (hh : is_honest p = true) (hw : 2 ≤ w)
    (hadv : honest_advantage_ranges_gt (Party := Party) w d) :
    ∃ b ∈ l.tT.bestChain (N.t_now - 1) l.tree, honest_block b = true ∧
      N.t_now < b.sl + d + 2 :=
  honest_tip_gen hu hLmap hGB lucky_slot (fun _ h => h) adv_slot
    (fun p _ hw hc => decide_eq_true ⟨p, hw, hc⟩) hR hff hcf hl hh hw hadv

end CatCryptCore.Consensus.PoSNSB

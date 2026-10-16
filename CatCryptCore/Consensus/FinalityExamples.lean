/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.Finality
public import CatCryptCore.Consensus.FFGExamples

/-!
# Finality layers: concrete examples

This file shows that the hypotheses of the finality-layer theorems of
`CatCryptCore.Consensus.Finality` are satisfiable.

## Main results

* `Examples.ffg_nonvacuous`, `Examples.kDeep_nonvacuous`: concrete traces on which all
  hypotheses of the FFG and `k`-deep theorems hold and some block is finalized.
* `Examples.ffg_agreement_fails_doubleVotes`: with half of the stake slashable, FFG
  finalizes two conflicting checkpoints, so the stake bound cannot be dropped.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.Finality

open FFG

/-! ### Concrete instances: the hypotheses are satisfiable -/

namespace Examples

open FFG.Examples

/-! #### FFG over a chain -/

/-- Four honest validators that select the chain `[1, 0]` (block `1` on genesis `0` of
`forkTree`) at all times. -/
def ffgTrace : ChainTrace (Fin 4) (Fin 3) where
  honest _ := True
  chain _ _ := [1, 0]

/-- The slot of a block of `forkTree`: its number. -/
def blockSlot : Fin 3 → ℕ := fun b => b.val

/-- Every party sees all votes of `honestVotes` at all times. -/
def ffgSeen : ℕ → Fin 4 → Finset (Vote (Fin 4) (Fin 3)) := fun _ _ => honestVotes

theorem ffgTrace_chainsInTree : ffgTrace.ChainsInTree forkTree := by
  intro _ _ _
  simp [ffgTrace, forkTree]

/-- The votes of `honestVotes` name epoch-boundary checkpoints of `[1, 0]`, with epochs of one
slot. -/
theorem honestVotes_onChain : HonestVotesOnChain ffgTrace blockSlot 1 honestVotes := by
  intro x hx _
  exact ⟨0, (show ∀ x ∈ honestVotes, IsCheckpointOf blockSlot 1 [1, 0] x.source ∧
    IsCheckpointOf blockSlot 1 [1, 0] x.target by decide) x hx⟩

/-- Every block finalized by `honestVotes` is block `0` or block `1`. -/
theorem honestVotes_justified_block {c : Checkpoint (Fin 3)}
    (hc : Justified forkTree unitStake honestVotes c) : c.block = 0 ∨ c.block = 1 := by
  cases hc with
  | genesis => exact Or.inl rfl
  | @link s _ _ hl =>
    obtain ⟨v, hv⟩ : (voters honestVotes s c).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have := hl.2.2
      rw [he, totalStake_unitStake] at this
      simp [stake] at this
    have hmem := mem_voters.1 hv
    have key : ∀ x ∈ honestVotes, x.target.block = 1 := by decide
    exact Or.inr (key _ hmem)

/-- FFG over the chain `[1, 0]`, with `honestVotes`, is a finality layer, and it finalizes the
checkpoint `(1, 1)`. All hypotheses of `ffg_positionRespecting` and
`ffg_finalized_isCheckpoint` hold: every party sees only cast votes, the slashable stake is
`0 < 4 / 3`, all four validators are honest with stake `4 > 4 / 3`, and honest votes name
epoch-boundary checkpoints of their chains. -/
theorem ffg_nonvacuous :
    ffgTrace.ChainsInTree forkTree ∧ HonestVotesOnChain ffgTrace blockSlot 1 honestVotes ∧
      (∀ t p, ffgSeen t p ⊆ honestVotes) ∧
      3 * stake unitStake (slashable honestVotes) < totalStake unitStake ∧
      totalStake unitStake < 3 * stake unitStake Finset.univ ∧
      ffgFinalization forkTree unitStake ffgSeen 0 0 1 1 ∧
      IsCheckpointOf blockSlot 1 (ffgTrace.chain 0 0) ⟨1, 1⟩ ∧
      FinalityLayer forkTree ffgTrace (ffgFinalization forkTree unitStake ffgSeen) := by
  have hseen : ∀ t p, ffgSeen t p ⊆ honestVotes := fun _ _ => subset_rfl
  have hS : 3 * stake unitStake (slashable honestVotes) < totalStake unitStake := by
    rw [honestVotes_slashable]; decide
  have hP := ffg_positionRespecting (T := forkTree) ffgTrace hseen hS
  refine ⟨ffgTrace_chainsInTree, honestVotes_onChain, hseen, hS, by decide,
    honestVotes_finalized, by decide, hP, hP.chainForming, hP.agreement, ?_⟩
  intro p t t' b i _ _ hb
  rcases honestVotes_justified_block hb.1 with h | h <;> simp_all [ffgTrace]

/-- Without the bound on the slashable stake agreement fails: with the votes `doubleVotes`,
whose slashable validators hold half of the stake, the conflicting checkpoints `(1, 1)` and
`(2, 1)` are both finalized. -/
theorem ffg_agreement_fails_doubleVotes :
    ¬ Agreement forkTree ffgTrace (ffgFinalization forkTree unitStake fun _ _ => doubleVotes) := by
  intro h
  rcases h 0 0 0 0 1 2 1 1 trivial trivial doubleVotes_finalized_conflicting.1
      doubleVotes_finalized_conflicting.2.1 with h' | h'
  · exact forkTree_conflicting.1 h'
  · exact forkTree_conflicting.2 h'

/-! #### Finality by depth on a growing chain -/

/-- The chain `[n, n - 1, …, 0]`. -/
def line : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (n + 1) :: line n

theorem length_line (n : ℕ) : (line n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [line, ih]

theorem mem_line {n b : ℕ} : b ∈ line n ↔ b ≤ n := by
  induction n with
  | zero => simp [line]
  | succ n ih => simp only [line, List.mem_cons, ih]; omega

theorem line_suffix {n m : ℕ} (h : n ≤ m) : line n <:+ line m := by
  induction m, h using Nat.le_induction with
  | base => exact List.suffix_refl _
  | succ m _ ih => exact ih.trans (List.suffix_cons _ _)

theorem drop_line {n i : ℕ} (h : i ≤ n) : (line n).drop i = line (n - i) := by
  induction i generalizing n with
  | zero => rfl
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [line, List.drop_succ_cons]
    rw [ih (by omega)]
    congr 1
    omega

/-- The block tree on `ℕ` ordered by `≤`: a single chain. -/
def lineTree : BlockTree ℕ where
  anc a b := a ≤ b
  genesis := 0
  anc_refl := Nat.le_refl
  anc_trans := Nat.le_trans

/-- One honest party whose chain at time `t` is `[t, …, 0]`. -/
def lineTrace : ChainTrace Unit ℕ where
  honest _ := True
  chain t _ := line t

/-- Blocks with an even number count as honest. -/
def evenBlock (b : ℕ) : Bool := b % 2 == 0

theorem lineTrace_chainsInTree : lineTrace.ChainsInTree lineTree := by
  intro _ t _
  induction t with
  | zero => simp [lineTrace, line]
  | succ n ih =>
    simp only [lineTrace, line, List.pairwise_cons] at ih ⊢
    exact ⟨fun b hb => by have := mem_line.1 hb; simp only [lineTree]; omega, ih⟩

theorem lineTrace_commonPrefix (k : ℕ) : lineTrace.CommonPrefix k :=
  fun _ _ _ _ _ _ h => (List.drop_suffix _ _).trans (line_suffix h)

theorem lineTrace_chainGrowth (s : ℕ) : lineTrace.ChainGrowth s s := by
  intro _ _ t t' _ _ h
  simp only [lineTrace, length_line]
  omega

/-- Every two consecutive blocks of `[t, …, 0]` contain an even one. -/
theorem lineTrace_chainQuality : lineTrace.ChainQuality evenBlock 2 1 := by
  intro _ t i _ h
  simp only [lineTrace, length_line] at h ⊢
  rw [drop_line (by omega)]
  obtain ⟨m, hm⟩ : ∃ m, t - i = m + 1 := ⟨t - i - 1, by omega⟩
  rw [hm]
  cases m with
  | zero => simp [line, evenBlock]
  | succ m =>
    simp only [line, List.take_succ_cons, List.take_zero, List.countP_cons, List.countP_nil,
      evenBlock]
    rcases Nat.mod_two_eq_zero_or_one (m + 1) with h2 | h2 <;> simp [h2, Nat.add_mod]

/-- `kDeep_of_traceGuard` applies to `lineTrace` with common prefix `2`, chain growth `(1, 1)`
and chain quality `(evenBlock, 2, 1)`, and at time `5` the block `3` is final at height `3`. -/
theorem kDeep_nonvacuous :
    lineTrace.TraceGuard lineTree 2 1 1 evenBlock 2 1 ∧ kDeep 2 lineTrace 5 () 3 3 ∧
      FinalityLayer lineTree lineTrace (kDeep 2 lineTrace) :=
  have hG : lineTrace.TraceGuard lineTree 2 1 1 evenBlock 2 1 :=
    ⟨lineTrace_chainsInTree, lineTrace_commonPrefix 2, lineTrace_chainGrowth 1,
      lineTrace_chainQuality⟩
  ⟨hG, ⟨[2, 1, 0], by decide, rfl⟩, (kDeep_of_traceGuard hG).1⟩

end Examples

end CatCryptCore.Consensus.Finality

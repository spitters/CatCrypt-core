/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Casper FFG: accountable safety

This file models the Casper FFG finality gadget with a static validator set
(Buterin and Griffith, *Casper the Friendly Finality Gadget*; Buterin et al.,
*Combining GHOST and Casper*, arXiv:2003.03052) and proves accountable safety:
if two checkpoints on conflicting blocks are both finalized, then the validators
that violate one of the two slashing conditions hold at least one third of the
total stake.

Validators form a `Fintype V` with natural-number stake `w : V → ℕ`. Blocks carry
an ancestor relation `BlockTree.anc` that is reflexive and transitive; the proofs
use no further property of the block tree, so the results hold in particular for
the ancestor order of a rooted tree. A checkpoint is a block with an epoch, a vote
is a validator together with a source and a target checkpoint, and the votes cast
are a `Finset`. Supermajority thresholds are stated without division:
`3 * stake S ≥ 2 * W`.

## Main results

* `quorum_intersection`: two sets of stake at least `2/3 · W` intersect in stake at
  least `W/3`.
* `justified_epoch_zero`: the only justified checkpoint at epoch `0` is genesis.
* `slashable_of_justified_same_epoch`: two distinct justified checkpoints at the
  same epoch force `3 * stake slashable ≥ W`; `slashable_of_justified_conflicting`
  specializes this to conflicting blocks.
* `anc_of_kFinalized_of_justified`: if fewer than `W/3` of the stake is slashable,
  every justified checkpoint at an epoch not below that of a `k`-finalized
  checkpoint descends from it.
* `accountable_safety_kFinalized`: accountable safety for `k`-finalization (Gasper,
  Definition 4.3), with possibly different `k` for the two checkpoints.
* `accountable_safety`: accountable safety for finalization with `k = 1`.

The slashable set `slashable w votes` is an explicit `Finset`: the validators with
two distinct votes of equal target epoch (condition E1) or with a vote surrounding
another of their votes (condition E2).
-/

@[expose] public section

namespace CatCryptCore.Consensus.FFG

/-- An ancestor relation on blocks with a distinguished genesis block. The relation
`anc a b` reads "`a` is an ancestor of `b`" and includes `a = b`. -/
structure BlockTree (B : Type*) where
  /-- `anc a b`: block `a` is an ancestor of (or equal to) block `b`. -/
  anc : B → B → Prop
  /-- The genesis block. -/
  genesis : B
  anc_refl : ∀ b, anc b b
  anc_trans : ∀ {a b c}, anc a b → anc b c → anc a c

/-- Two blocks conflict when neither is an ancestor of the other. -/
def BlockTree.Conflicting {B : Type*} (T : BlockTree B) (a b : B) : Prop :=
  ¬ T.anc a b ∧ ¬ T.anc b a

theorem BlockTree.Conflicting.ne {B : Type*} {T : BlockTree B} {a b : B}
    (h : T.Conflicting a b) : a ≠ b := by
  rintro rfl
  exact h.1 (T.anc_refl a)

theorem BlockTree.Conflicting.symm {B : Type*} {T : BlockTree B} {a b : B}
    (h : T.Conflicting a b) : T.Conflicting b a :=
  ⟨h.2, h.1⟩

/-- A checkpoint: a block together with an epoch number. -/
structure Checkpoint (B : Type*) where
  block : B
  epoch : ℕ
  deriving DecidableEq

/-- A vote of `validator` for the link from `source` to `target`. -/
structure Vote (V B : Type*) where
  validator : V
  source : Checkpoint B
  target : Checkpoint B
  deriving DecidableEq

variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B]

/-! ### Stake -/

/-- The stake held by a set of validators. -/
def stake (w : V → ℕ) (S : Finset V) : ℕ := ∑ v ∈ S, w v

/-- The total stake `W`. -/
def totalStake (w : V → ℕ) : ℕ := stake w Finset.univ

omit [Fintype V] [DecidableEq V] in
theorem stake_mono (w : V → ℕ) {S T : Finset V} (h : S ⊆ T) : stake w S ≤ stake w T :=
  Finset.sum_le_sum_of_subset h

omit [DecidableEq V] in
theorem stake_le_totalStake (w : V → ℕ) (S : Finset V) : stake w S ≤ totalStake w :=
  stake_mono w (Finset.subset_univ S)

/-- Quorum intersection: two sets that each hold at least two thirds of the total
stake intersect in a set holding at least one third of it. -/
theorem quorum_intersection (w : V → ℕ) {S T : Finset V}
    (hS : 2 * totalStake w ≤ 3 * stake w S) (hT : 2 * totalStake w ≤ 3 * stake w T) :
    totalStake w ≤ 3 * stake w (S ∩ T) := by
  have hu : stake w (S ∪ T) + stake w (S ∩ T) = stake w S + stake w T :=
    Finset.sum_union_inter
  have hle := stake_le_totalStake w (S ∪ T)
  omega

/-! ### Votes, links and slashing conditions -/

/-- The validators that voted for the link `s → t`. -/
def voters (votes : Finset (Vote V B)) (s t : Checkpoint B) : Finset V :=
  Finset.univ.filter fun v => (⟨v, s, t⟩ : Vote V B) ∈ votes

theorem mem_voters {votes : Finset (Vote V B)} {s t : Checkpoint B} {v : V} :
    v ∈ voters votes s t ↔ (⟨v, s, t⟩ : Vote V B) ∈ votes := by
  simp [voters]

/-- A supermajority link `s → t`: the source epoch is below the target epoch, the
source block is an ancestor of the target block, and the validators voting for
`s → t` hold at least two thirds of the total stake. -/
def SupermajorityLink (T : BlockTree B) (w : V → ℕ) (votes : Finset (Vote V B))
    (s t : Checkpoint B) : Prop :=
  s.epoch < t.epoch ∧ T.anc s.block t.block ∧
    2 * totalStake w ≤ 3 * stake w (voters votes s t)

/-- Slashing condition E1 (double vote): `v` cast two distinct votes with the same
target epoch. -/
def DoubleVote (votes : Finset (Vote V B)) (v : V) : Prop :=
  ∃ x ∈ votes, ∃ y ∈ votes, x.validator = v ∧ y.validator = v ∧ x ≠ y ∧
    x.target.epoch = y.target.epoch

/-- Slashing condition E2 (surround vote): `v` cast votes `s₁ → t₁` and `s₂ → t₂`
with `s₁.epoch < s₂.epoch < t₂.epoch < t₁.epoch`. -/
def SurroundVote (votes : Finset (Vote V B)) (v : V) : Prop :=
  ∃ x ∈ votes, ∃ y ∈ votes, x.validator = v ∧ y.validator = v ∧
    x.source.epoch < y.source.epoch ∧ y.source.epoch < y.target.epoch ∧
    y.target.epoch < x.target.epoch

instance (votes : Finset (Vote V B)) (v : V) : Decidable (DoubleVote votes v) := by
  unfold DoubleVote; infer_instance

instance (votes : Finset (Vote V B)) (v : V) : Decidable (SurroundVote votes v) := by
  unfold SurroundVote; infer_instance

/-- The slashable validators: those violating condition E1 or condition E2. -/
def slashable (votes : Finset (Vote V B)) : Finset V :=
  Finset.univ.filter fun v => DoubleVote votes v ∨ SurroundVote votes v

theorem mem_slashable {votes : Finset (Vote V B)} {v : V} :
    v ∈ slashable votes ↔ DoubleVote votes v ∨ SurroundVote votes v := by
  simp [slashable]

/-- Two links with distinct targets of equal epoch: every validator voting for both
violates E1. -/
theorem voters_inter_subset_slashable_of_double {votes : Finset (Vote V B)}
    {s₁ t₁ s₂ t₂ : Checkpoint B} (hne : t₁ ≠ t₂) (he : t₁.epoch = t₂.epoch) :
    voters votes s₁ t₁ ∩ voters votes s₂ t₂ ⊆ slashable votes := by
  intro v hv
  rw [Finset.mem_inter, mem_voters, mem_voters] at hv
  refine mem_slashable.2 (Or.inl ⟨_, hv.1, _, hv.2, rfl, rfl, ?_, he⟩)
  intro h
  exact hne (congrArg Vote.target h)

/-- Two links where `s₁ → t₁` surrounds `s₂ → t₂`: every validator voting for both
violates E2. -/
theorem voters_inter_subset_slashable_of_surround {votes : Finset (Vote V B)}
    {s₁ t₁ s₂ t₂ : Checkpoint B} (h₁ : s₁.epoch < s₂.epoch) (h₂ : s₂.epoch < t₂.epoch)
    (h₃ : t₂.epoch < t₁.epoch) :
    voters votes s₁ t₁ ∩ voters votes s₂ t₂ ⊆ slashable votes := by
  intro v hv
  rw [Finset.mem_inter, mem_voters, mem_voters] at hv
  exact mem_slashable.2 (Or.inr ⟨_, hv.1, _, hv.2, rfl, rfl, h₁, h₂, h₃⟩)

/-- If the voters of two supermajority links all lie in a set `S` of validators, then
`S` holds at least a third of the total stake. -/
theorem stake_of_links_inter_subset {T : BlockTree B} {w : V → ℕ}
    {votes : Finset (Vote V B)} {s₁ t₁ s₂ t₂ : Checkpoint B} {S : Finset V}
    (h₁ : SupermajorityLink T w votes s₁ t₁) (h₂ : SupermajorityLink T w votes s₂ t₂)
    (hS : voters votes s₁ t₁ ∩ voters votes s₂ t₂ ⊆ S) :
    3 * stake w S ≥ totalStake w :=
  le_trans (quorum_intersection w h₁.2.2 h₂.2.2) (Nat.mul_le_mul_left 3 (stake_mono w hS))

/-! ### Justification and finalization -/

/-- The genesis checkpoint: the genesis block at epoch `0`. -/
def genesisCheckpoint (T : BlockTree B) : Checkpoint B := ⟨T.genesis, 0⟩

/-- Justified checkpoints: genesis is justified, and the target of a supermajority
link from a justified checkpoint is justified. -/
inductive Justified (T : BlockTree B) (w : V → ℕ) (votes : Finset (Vote V B)) :
    Checkpoint B → Prop
  | genesis : Justified T w votes (genesisCheckpoint T)
  | link {s t : Checkpoint B} :
      Justified T w votes s → SupermajorityLink T w votes s t → Justified T w votes t

/-- The only justified checkpoint at epoch `0` is the genesis checkpoint. -/
theorem justified_epoch_zero {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
    {c : Checkpoint B} (hc : Justified T w votes c) (h0 : c.epoch = 0) :
    c = genesisCheckpoint T := by
  cases hc with
  | genesis => rfl
  | link _ hl => have := hl.1; omega

/-- Two distinct justified checkpoints at the same epoch force the slashable
validators to hold at least a third of the total stake. -/
theorem slashable_of_justified_same_epoch {T : BlockTree B} {w : V → ℕ}
    {votes : Finset (Vote V B)} {c₁ c₂ : Checkpoint B}
    (h₁ : Justified T w votes c₁) (h₂ : Justified T w votes c₂)
    (he : c₁.epoch = c₂.epoch) (hne : c₁ ≠ c₂) :
    3 * stake w (slashable votes) ≥ totalStake w := by
  cases h₁ with
  | genesis =>
    exact absurd (justified_epoch_zero h₂ he.symm).symm hne
  | link _ hl₁ =>
    cases h₂ with
    | genesis =>
      exact absurd (justified_epoch_zero (Justified.link ‹_› hl₁) he) hne
    | link _ hl₂ =>
      exact stake_of_links_inter_subset hl₁ hl₂
        (voters_inter_subset_slashable_of_double hne he)

/-- Justified checkpoints at the same epoch on conflicting blocks force the slashable
validators to hold at least a third of the total stake. -/
theorem slashable_of_justified_conflicting {T : BlockTree B} {w : V → ℕ}
    {votes : Finset (Vote V B)} {c₁ c₂ : Checkpoint B}
    (h₁ : Justified T w votes c₁) (h₂ : Justified T w votes c₂)
    (he : c₁.epoch = c₂.epoch) (hc : T.Conflicting c₁.block c₂.block) :
    3 * stake w (slashable votes) ≥ totalStake w :=
  slashable_of_justified_same_epoch h₁ h₂ he fun h => hc.ne (congrArg Checkpoint.block h)

/-- `k`-finalization (Gasper, Definition 4.3): there are checkpoints `C 0 = c, …, C k`
at the consecutive epochs `c.epoch, …, c.epoch + k`, the blocks of `C 0, …, C (k-1)`
descend from `c.block`, the checkpoints `C 0, …, C (k-1)` are justified, and there
is a supermajority link `C 0 → C k`. -/
def KFinalized (T : BlockTree B) (w : V → ℕ) (votes : Finset (Vote V B)) (k : ℕ)
    (c : Checkpoint B) : Prop :=
  1 ≤ k ∧ ∃ C : ℕ → Checkpoint B, C 0 = c ∧
    (∀ i ≤ k, (C i).epoch = c.epoch + i) ∧
    (∀ i < k, T.anc c.block (C i).block) ∧
    (∀ i < k, Justified T w votes (C i)) ∧
    SupermajorityLink T w votes (C 0) (C k)

/-- Finalization with `k = 1`: `c` is justified and there is a supermajority link
from `c` to a checkpoint at the next epoch. -/
def Finalized (T : BlockTree B) (w : V → ℕ) (votes : Finset (Vote V B))
    (c : Checkpoint B) : Prop :=
  Justified T w votes c ∧
    ∃ c' : Checkpoint B, c'.epoch = c.epoch + 1 ∧ SupermajorityLink T w votes c c'

theorem KFinalized.justified {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
    {k : ℕ} {c : Checkpoint B} (h : KFinalized T w votes k c) : Justified T w votes c := by
  obtain ⟨hk, C, h0, -, -, hJ, -⟩ := h
  exact h0 ▸ hJ 0 hk

theorem Finalized.kFinalized {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
    {c : Checkpoint B} (h : Finalized T w votes c) : KFinalized T w votes 1 c := by
  obtain ⟨hJ, c', he, hl⟩ := h
  refine ⟨le_rfl, fun i => if i = 0 then c else c', rfl, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl <;> simp [he]
  · intro i hi
    obtain rfl : i = 0 := by omega
    simpa using T.anc_refl c.block
  · intro i hi
    obtain rfl : i = 0 := by omega
    simpa using hJ
  · simpa using hl

/-! ### Accountable safety -/

/-- If the slashable validators hold less than a third of the total stake, then every
justified checkpoint at an epoch not below that of a `k`-finalized checkpoint `f`
descends from `f`. -/
theorem anc_of_kFinalized_of_justified {T : BlockTree B} {w : V → ℕ}
    {votes : Finset (Vote V B)} {k : ℕ} {f c : Checkpoint B}
    (hf : KFinalized T w votes k f) (hc : Justified T w votes c) (hle : f.epoch ≤ c.epoch)
    (hH : 3 * stake w (slashable votes) < totalStake w) :
    T.anc f.block c.block := by
  obtain ⟨hk, C, h0, hCe, hCa, hCJ, hCl⟩ := hf
  have hJk : Justified T w votes (C k) := Justified.link (hCJ 0 hk) hCl
  have hAk : T.anc f.block (C k).block := h0 ▸ hCl.2.1
  induction hc with
  | genesis =>
    have hf0 : f.epoch = 0 := by simpa [genesisCheckpoint] using hle
    have := justified_epoch_zero (h0 ▸ hCJ 0 hk) hf0
    rw [this]
    exact T.anc_refl _
  | @link s t hs hl ih =>
    by_cases hwin : t.epoch ≤ f.epoch + k
    · -- `t` lies at the epoch of some `C i`; the two checkpoints coincide.
      obtain ⟨i, hi⟩ : ∃ i, i = t.epoch - f.epoch := ⟨_, rfl⟩
      have hCi : (C i).epoch = t.epoch := by rw [hCe i (by omega)]; omega
      have hJi : Justified T w votes (C i) := by
        rcases Nat.lt_or_eq_of_le (show i ≤ k by omega) with h | h
        · exact hCJ i h
        · exact h ▸ hJk
      have hAi : T.anc f.block (C i).block := by
        rcases Nat.lt_or_eq_of_le (show i ≤ k by omega) with h | h
        · exact hCa i h
        · exact h ▸ hAk
      by_cases heq : C i = t
      · exact heq ▸ hAi
      · exact absurd (slashable_of_justified_same_epoch hJi (Justified.link hs hl) hCi heq)
          (by omega)
    · by_cases hsf : s.epoch < f.epoch
      · -- The link `s → t` surrounds the link `C 0 → C k`.
        have hC0 : (C 0).epoch = f.epoch := by rw [h0]
        have hCk : (C k).epoch = f.epoch + k := hCe k le_rfl
        have := stake_of_links_inter_subset hl hCl
          (voters_inter_subset_slashable_of_surround (by omega) (by omega) (by omega))
        omega
      · exact T.anc_trans (ih (by omega)) hl.2.1

/-- Accountable safety for `k`-finalization: if two checkpoints on conflicting blocks
are `k₁`- and `k₂`-finalized, then the slashable validators hold at least a third of
the total stake. -/
theorem accountable_safety_kFinalized {T : BlockTree B} {w : V → ℕ}
    {votes : Finset (Vote V B)} {k₁ k₂ : ℕ} {f₁ f₂ : Checkpoint B}
    (h₁ : KFinalized T w votes k₁ f₁) (h₂ : KFinalized T w votes k₂ f₂)
    (hc : T.Conflicting f₁.block f₂.block) :
    3 * stake w (slashable votes) ≥ totalStake w := by
  by_contra hH
  rw [not_le] at hH
  rcases le_total f₁.epoch f₂.epoch with h | h
  · exact hc.1 (anc_of_kFinalized_of_justified h₁ h₂.justified h hH)
  · exact hc.2 (anc_of_kFinalized_of_justified h₂ h₁.justified h hH)

/-- Accountable safety (Casper FFG, Theorem 1; Gasper, Theorem 4.4 with `k = 1`): if
two checkpoints on conflicting blocks are finalized, then the validators violating
slashing condition E1 or E2 hold at least a third of the total stake. -/
theorem accountable_safety {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
    {f₁ f₂ : Checkpoint B} (h₁ : Finalized T w votes f₁) (h₂ : Finalized T w votes f₂)
    (hc : T.Conflicting f₁.block f₂.block) :
    3 * stake w (slashable votes) ≥ totalStake w :=
  accountable_safety_kFinalized h₁.kFinalized h₂.kFinalized hc

end CatCryptCore.Consensus.FFG

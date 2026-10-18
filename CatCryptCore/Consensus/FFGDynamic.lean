/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.FFG

/-!
# Casper FFG with a dynamic validator set: accountable safety up to churn

`CatCryptCore.Consensus.FFG` proves accountable safety of Casper FFG for a fixed validator
set. This file treats a validator set that changes between epochs through deposits and
withdrawals (Buterin and Griffith, *Casper the Friendly Finality Gadget*, dynamic validator
sets; Buterin et al., *Combining GHOST and Casper*, arXiv:2003.03052, §4).

## Model

A *schedule* `σ : ℕ → V → ℕ` assigns to every epoch `e` a weighted set of validators:
`σ e v` is the stake of `v` in the set active at epoch `e`, and `σ e v = 0` means that `v` is
not active at `e`. As in Gasper, a link `s → t` is a supermajority link when its voters hold
at least two thirds of the stake of the set active at the *source* epoch `s.epoch`
(`DSupermajorityLink`). Dynamic justification `DJustified`, `k`-finalization `DKFinalized` and
finalization `DFinalized` are the definitions of `FFG.lean` with this link. Votes, the
slashing conditions E1 and E2 and the slashable set `slashable votes` are those of `FFG.lean`
unchanged.

## Churn

For a horizon `E` the file defines, per validator, the minimum `stableWeight σ E v` and the
maximum `maxWeight σ E v` of its stake over the epochs `0, …, E`. The *churn* of `σ` up to `E`
is `churn σ E = ∑ v, (maxWeight σ E v - stableWeight σ E v)`: the total stake that is not
held throughout the epochs `0, …, E`. When stake is moved only by validators entering and
leaving, a validator that is present in some but not all of these epochs contributes its stake,
so for `E = 1` the churn is the stake of the symmetric difference of the two sets. The churn
is bounded by the sum of the per-epoch changes, `churn_le_pathChurn`, where the change from `e`
to `e + 1` is the `ℓ¹` distance `stepChurn σ e` between `σ e` and `σ (e + 1)`.

The horizon used below is the larger of the epochs of the two finalized checkpoints. For
justification from genesis the churn is taken over all epochs from `0` to that horizon: the
justification chains of the two checkpoints may contain links from any earlier source epoch,
and the voters of such a link are weighed by the set of that epoch.

## Windows from an anchor

`DJustifiedFrom T σ votes a` is justification from an anchor checkpoint `a` instead of genesis
(for instance a checkpoint that both parties already regard as final); `DKFinalizedFrom` and
`DFinalizedFrom` are the finalization notions built on it, and `DJustified` is the case of the
genesis anchor (`DJustified.from_genesis`). Every link of a justification chain from `a` has its
source epoch at least `e₀ = a.epoch`, so the lower envelope is needed only on the window
`e₀, …, E` (`EnvelopeOn`), and the churn is that of the shifted schedule `e ↦ σ (e₀ + e)` up
to `E - e₀`.

## Main results

* `quorum_intersection_envelope`: if `ρ ≤ σ₁, σ₂` pointwise and the totals of `σ₁` and `σ₂`
  exceed that of `ρ` by at most `D`, a `σ₁`-supermajority and a `σ₂`-supermajority meet in
  `ρ`-stake at least `(W_ρ - 2D)/3`.
* `accountable_safety_envelope`: for any lower envelope `ρ` of the sets active at the epochs
  `0, …, E` with excess at most `D`, two finalized checkpoints on conflicting blocks at epochs
  at most `E` force `W_ρ ≤ 3 · stake_ρ(slashable) + 2D` (also for `k`-finalization,
  `accountable_safety_kFinalized_envelope`).
* `accountable_safety_envelope_from`, `accountable_safety_kFinalized_envelope_from`: the same
  for checkpoints finalized from an anchor `a`, with an envelope on the epochs `a.epoch, …, E`
  only.
* `accountable_safety_dynamic_from` (headline, windowed): for checkpoints finalized from an
  anchor of epoch `e₀` and `E` the larger finalized epoch,
  `W_stable ≤ 3 · stake_stable(slashable) + 2 · churn σ' (E - e₀)`, where `σ' e = σ (e₀ + e)`
  and `stable = stableWeight σ' (E - e₀)`.
* `accountable_safety_dynamic` (headline, from genesis, the case `e₀ = 0`): with `E` the
  larger finalized epoch, `W_stable ≤ 3 · stake_stable(slashable) + 2 · churn σ E`, where
  `stable = stableWeight σ E`.
* `accountable_safety_dynamic_epoch`: for every epoch `e ≤ E`,
  `W_{σ e} ≤ 3 · stake_{σ e}(slashable) + 3 · churn σ E`, i.e. the slashable validators hold at
  least one third of the stake active at `e` minus the churn.
* `accountable_safety_of_churn_eq_zero`: with zero churn the fixed-set bound
  `W_{σ e} ≤ 3 · stake_{σ e}(slashable)` holds at every epoch `e ≤ E`, and
  `accountable_safety_const` recovers `FFG.accountable_safety` from the dynamic theorem through
  `dFinalized_const_iff`.

A concrete instance with non-zero churn is in `CatCryptCore.Consensus.FFGDynamicExamples`.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.FFGDynamic

open CatCryptCore.Consensus.FFG

/-- A validator-set schedule: `σ e v` is the stake of validator `v` in the weighted set
active at epoch `e`; `σ e v = 0` means that `v` is not active at `e`. -/
abbrev Schedule (V : Type*) := ℕ → V → ℕ

variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B]

/-! ### Quorum intersection across weightings -/

/-- A `σ`-supermajority `A` is a `ρ`-quorum up to the excess of `σ` over `ρ`: if `ρ ≤ σ`
pointwise and `A` holds two thirds of the `σ`-stake, then `3 W_ρ ≤ 3 ρ(A) + W_σ`. -/
theorem quorum_transfer {σ ρ : V → ℕ} {A : Finset V} (hle : ∀ v, ρ v ≤ σ v)
    (hA : 2 * totalStake σ ≤ 3 * stake σ A) :
    3 * totalStake ρ ≤ 3 * stake ρ A + totalStake σ := by
  have hσ : stake σ (Finset.univ \ A) + stake σ A = totalStake σ :=
    Finset.sum_sdiff (Finset.subset_univ A)
  have hρ : stake ρ (Finset.univ \ A) + stake ρ A = totalStake ρ :=
    Finset.sum_sdiff (Finset.subset_univ A)
  have hc : stake ρ (Finset.univ \ A) ≤ stake σ (Finset.univ \ A) :=
    Finset.sum_le_sum fun v _ => hle v
  omega

/-- Quorum intersection across two weightings. If `ρ ≤ σ₁` and `ρ ≤ σ₂` pointwise, the totals
of `σ₁` and `σ₂` exceed the total of `ρ` by at most `D`, `A` holds two thirds of the
`σ₁`-stake and `B` two thirds of the `σ₂`-stake, then `W_ρ ≤ 3 ρ(A ∩ B) + 2D`. -/
theorem quorum_intersection_envelope {σ₁ σ₂ ρ : V → ℕ} {D : ℕ} {A B : Finset V}
    (h₁ : ∀ v, ρ v ≤ σ₁ v) (h₂ : ∀ v, ρ v ≤ σ₂ v)
    (hD₁ : totalStake σ₁ ≤ totalStake ρ + D) (hD₂ : totalStake σ₂ ≤ totalStake ρ + D)
    (hA : 2 * totalStake σ₁ ≤ 3 * stake σ₁ A) (hB : 2 * totalStake σ₂ ≤ 3 * stake σ₂ B) :
    totalStake ρ ≤ 3 * stake ρ (A ∩ B) + 2 * D := by
  have hu : stake ρ (A ∪ B) + stake ρ (A ∩ B) = stake ρ A + stake ρ B :=
    Finset.sum_union_inter
  have hle := stake_le_totalStake ρ (A ∪ B)
  have := quorum_transfer h₁ hA
  have := quorum_transfer h₂ hB
  omega

/-! ### Dynamic justification and finalization -/

/-- A supermajority link `s → t` for the schedule `σ` (Gasper, §4): the source epoch is
below the target epoch, the source block is an ancestor of the target block, and the voters
of `s → t` hold at least two thirds of the stake of the set `σ s.epoch` active at the source
epoch. -/
def DSupermajorityLink (T : BlockTree B) (σ : Schedule V) (votes : Finset (Vote V B))
    (s t : Checkpoint B) : Prop :=
  SupermajorityLink T (σ s.epoch) votes s t

/-- Justified checkpoints for the schedule `σ`: genesis is justified, and the target of a
`σ`-supermajority link from a justified checkpoint is justified. -/
inductive DJustified (T : BlockTree B) (σ : Schedule V) (votes : Finset (Vote V B)) :
    Checkpoint B → Prop
  | genesis : DJustified T σ votes (genesisCheckpoint T)
  | link {s t : Checkpoint B} :
      DJustified T σ votes s → DSupermajorityLink T σ votes s t → DJustified T σ votes t

/-- `k`-finalization for the schedule `σ` (Gasper, Definition 4.3): checkpoints
`C 0 = c, …, C k` at the epochs `c.epoch, …, c.epoch + k`, the blocks of `C 0, …, C (k-1)`
descend from `c.block`, `C 0, …, C (k-1)` are justified, and `C 0 → C k` is a
`σ`-supermajority link. -/
def DKFinalized (T : BlockTree B) (σ : Schedule V) (votes : Finset (Vote V B)) (k : ℕ)
    (c : Checkpoint B) : Prop :=
  1 ≤ k ∧ ∃ C : ℕ → Checkpoint B, C 0 = c ∧
    (∀ i ≤ k, (C i).epoch = c.epoch + i) ∧
    (∀ i < k, T.anc c.block (C i).block) ∧
    (∀ i < k, DJustified T σ votes (C i)) ∧
    DSupermajorityLink T σ votes (C 0) (C k)

/-- Finalization for the schedule `σ`: `c` is justified and there is a `σ`-supermajority link
from `c` to a checkpoint at the next epoch. -/
def DFinalized (T : BlockTree B) (σ : Schedule V) (votes : Finset (Vote V B))
    (c : Checkpoint B) : Prop :=
  DJustified T σ votes c ∧
    ∃ c' : Checkpoint B, c'.epoch = c.epoch + 1 ∧ DSupermajorityLink T σ votes c c'

theorem DKFinalized.justified {T : BlockTree B} {σ : Schedule V} {votes : Finset (Vote V B)}
    {k : ℕ} {c : Checkpoint B} (h : DKFinalized T σ votes k c) : DJustified T σ votes c := by
  obtain ⟨hk, C, h0, -, -, hJ, -⟩ := h
  exact h0 ▸ hJ 0 hk

theorem DFinalized.kFinalized {T : BlockTree B} {σ : Schedule V} {votes : Finset (Vote V B)}
    {c : Checkpoint B} (h : DFinalized T σ votes c) : DKFinalized T σ votes 1 c := by
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

/-- The only justified checkpoint at epoch `0` is the genesis checkpoint. -/
theorem dJustified_epoch_zero {T : BlockTree B} {σ : Schedule V} {votes : Finset (Vote V B)}
    {c : Checkpoint B} (hc : DJustified T σ votes c) (h0 : c.epoch = 0) :
    c = genesisCheckpoint T := by
  cases hc with
  | genesis => rfl
  | link _ hl => have := hl.1; omega

/-! ### Justification from an anchor -/

/-- Checkpoints justified from the anchor `a` for the schedule `σ`: `a` is justified from `a`,
and the target of a `σ`-supermajority link from a checkpoint justified from `a` is justified
from `a`. -/
inductive DJustifiedFrom (T : BlockTree B) (σ : Schedule V) (votes : Finset (Vote V B))
    (a : Checkpoint B) : Checkpoint B → Prop
  | anchor : DJustifiedFrom T σ votes a a
  | link {s t : Checkpoint B} :
      DJustifiedFrom T σ votes a s → DSupermajorityLink T σ votes s t →
        DJustifiedFrom T σ votes a t

/-- `k`-finalization from the anchor `a`: `DKFinalized` with justification from `a`. -/
def DKFinalizedFrom (T : BlockTree B) (σ : Schedule V) (votes : Finset (Vote V B))
    (a : Checkpoint B) (k : ℕ) (c : Checkpoint B) : Prop :=
  1 ≤ k ∧ ∃ C : ℕ → Checkpoint B, C 0 = c ∧
    (∀ i ≤ k, (C i).epoch = c.epoch + i) ∧
    (∀ i < k, T.anc c.block (C i).block) ∧
    (∀ i < k, DJustifiedFrom T σ votes a (C i)) ∧
    DSupermajorityLink T σ votes (C 0) (C k)

/-- Finalization from the anchor `a`: `c` is justified from `a` and there is a
`σ`-supermajority link from `c` to a checkpoint at the next epoch. -/
def DFinalizedFrom (T : BlockTree B) (σ : Schedule V) (votes : Finset (Vote V B))
    (a c : Checkpoint B) : Prop :=
  DJustifiedFrom T σ votes a c ∧
    ∃ c' : Checkpoint B, c'.epoch = c.epoch + 1 ∧ DSupermajorityLink T σ votes c c'

section From

variable {T : BlockTree B} {σ : Schedule V} {votes : Finset (Vote V B)} {a : Checkpoint B}

/-- A checkpoint justified from `a` has epoch at least `a.epoch`. -/
theorem DJustifiedFrom.epoch_le {c : Checkpoint B} (h : DJustifiedFrom T σ votes a c) :
    a.epoch ≤ c.epoch := by
  induction h with
  | anchor => exact le_rfl
  | link _ hl ih => have := hl.1; omega

/-- The only checkpoint justified from `a` at epoch `a.epoch` is `a`. -/
theorem DJustifiedFrom.eq_anchor {c : Checkpoint B} (h : DJustifiedFrom T σ votes a c)
    (he : c.epoch = a.epoch) : c = a := by
  cases h with
  | anchor => rfl
  | link hs hl => have := hl.1; have := hs.epoch_le; omega

theorem DKFinalizedFrom.justified {k : ℕ} {c : Checkpoint B}
    (h : DKFinalizedFrom T σ votes a k c) : DJustifiedFrom T σ votes a c := by
  obtain ⟨hk, C, h0, -, -, hJ, -⟩ := h
  exact h0 ▸ hJ 0 hk

theorem DFinalizedFrom.kFinalized {c : Checkpoint B} (h : DFinalizedFrom T σ votes a c) :
    DKFinalizedFrom T σ votes a 1 c := by
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

/-- Justification from genesis is justification from the genesis anchor. -/
theorem DJustified.from_genesis {c : Checkpoint B} (h : DJustified T σ votes c) :
    DJustifiedFrom T σ votes (genesisCheckpoint T) c := by
  induction h with
  | genesis => exact DJustifiedFrom.anchor
  | link _ hl ih => exact DJustifiedFrom.link ih hl

theorem DKFinalized.from_genesis {k : ℕ} {c : Checkpoint B} (h : DKFinalized T σ votes k c) :
    DKFinalizedFrom T σ votes (genesisCheckpoint T) k c := by
  obtain ⟨hk, C, h0, hCe, hCa, hCJ, hCl⟩ := h
  exact ⟨hk, C, h0, hCe, hCa, fun i hi => (hCJ i hi).from_genesis, hCl⟩

theorem DFinalized.from_genesis {c : Checkpoint B} (h : DFinalized T σ votes c) :
    DFinalizedFrom T σ votes (genesisCheckpoint T) c :=
  ⟨h.1.from_genesis, h.2⟩

end From

/-! ### Constant schedules -/

/-- For a constant schedule, dynamic justification is the justification of `FFG.lean`. -/
theorem dJustified_const_iff {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
    {c : Checkpoint B} : DJustified T (fun _ => w) votes c ↔ Justified T w votes c := by
  constructor
  · intro h
    induction h with
    | genesis => exact Justified.genesis
    | link _ hl ih => exact Justified.link ih hl
  · intro h
    induction h with
    | genesis => exact DJustified.genesis
    | link _ hl ih => exact DJustified.link ih hl

/-- For a constant schedule, dynamic finalization is the finalization of `FFG.lean`. -/
theorem dFinalized_const_iff {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
    {c : Checkpoint B} : DFinalized T (fun _ => w) votes c ↔ Finalized T w votes c := by
  unfold DFinalized Finalized DSupermajorityLink
  rw [dJustified_const_iff]

/-! ### Lower envelopes -/

/-- `ρ` is a lower envelope of the sets active at the epochs `0, …, E` with excess at most
`D`: for every `e ≤ E`, `ρ ≤ σ e` pointwise and `W_{σ e} ≤ W_ρ + D`. -/
def Envelope (σ : Schedule V) (ρ : V → ℕ) (D E : ℕ) : Prop :=
  ∀ e ≤ E, (∀ v, ρ v ≤ σ e v) ∧ totalStake (σ e) ≤ totalStake ρ + D

/-- `ρ` is a lower envelope of the sets active at the epochs `e₀, …, E` with excess at most
`D`: for every `e` with `e₀ ≤ e ≤ E`, `ρ ≤ σ e` pointwise and `W_{σ e} ≤ W_ρ + D`. -/
def EnvelopeOn (σ : Schedule V) (ρ : V → ℕ) (D e₀ E : ℕ) : Prop :=
  ∀ e, e₀ ≤ e → e ≤ E → (∀ v, ρ v ≤ σ e v) ∧ totalStake (σ e) ≤ totalStake ρ + D

omit [DecidableEq V] in
/-- A lower envelope on `0, …, E` is a lower envelope on every window `e₀, …, E`. -/
theorem Envelope.on {σ : Schedule V} {ρ : V → ℕ} {D E : ℕ} (h : Envelope σ ρ D E) (e₀ : ℕ) :
    EnvelopeOn σ ρ D e₀ E :=
  fun e _ he => h e he

/-- If the voters of two `σ`-supermajority links with source epochs in `e₀, …, E` all lie in
`S`, then `W_ρ ≤ 3 ρ(S) + 2D` for every lower envelope `ρ` on `e₀, …, E` with excess `D`. -/
theorem stake_of_dlinks_inter_subset {T : BlockTree B} {σ : Schedule V} {ρ : V → ℕ}
    {D e₀ E : ℕ} {votes : Finset (Vote V B)} {s₁ t₁ s₂ t₂ : Checkpoint B} {S : Finset V}
    (hρ : EnvelopeOn σ ρ D e₀ E) (hs₁ : e₀ ≤ s₁.epoch) (hs₁E : s₁.epoch ≤ E)
    (hs₂ : e₀ ≤ s₂.epoch) (hs₂E : s₂.epoch ≤ E)
    (h₁ : DSupermajorityLink T σ votes s₁ t₁) (h₂ : DSupermajorityLink T σ votes s₂ t₂)
    (hS : voters votes s₁ t₁ ∩ voters votes s₂ t₂ ⊆ S) :
    totalStake ρ ≤ 3 * stake ρ S + 2 * D := by
  have h := quorum_intersection_envelope (hρ _ hs₁ hs₁E).1 (hρ _ hs₂ hs₂E).1
    (hρ _ hs₁ hs₁E).2 (hρ _ hs₂ hs₂E).2 h₁.2.2 h₂.2.2
  have := stake_mono ρ hS
  omega

/-- Two distinct checkpoints justified from the anchor `a` at the same epoch `e ≤ E` force
`W_ρ ≤ 3 ρ(slashable) + 2D` for every lower envelope `ρ` on `a.epoch, …, E` with excess
`D`. -/
theorem slashable_of_dJustifiedFrom_same_epoch {T : BlockTree B} {σ : Schedule V}
    {ρ : V → ℕ} {D E : ℕ} {votes : Finset (Vote V B)} {a c₁ c₂ : Checkpoint B}
    (hρ : EnvelopeOn σ ρ D a.epoch E)
    (h₁ : DJustifiedFrom T σ votes a c₁) (h₂ : DJustifiedFrom T σ votes a c₂)
    (he : c₁.epoch = c₂.epoch) (hE : c₁.epoch ≤ E) (hne : c₁ ≠ c₂) :
    totalStake ρ ≤ 3 * stake ρ (slashable votes) + 2 * D := by
  cases h₁ with
  | anchor =>
    exact absurd (h₂.eq_anchor he.symm).symm hne
  | link hs₁ hl₁ =>
    cases h₂ with
    | anchor =>
      exact absurd ((DJustifiedFrom.link hs₁ hl₁).eq_anchor he) hne
    | link hs₂ hl₂ =>
      have := hl₁.1
      have := hl₂.1
      exact stake_of_dlinks_inter_subset hρ hs₁.epoch_le (by omega) hs₂.epoch_le (by omega)
        hl₁ hl₂ (voters_inter_subset_slashable_of_double hne he)

/-- Two distinct justified checkpoints at the same epoch `e ≤ E` force
`W_ρ ≤ 3 ρ(slashable) + 2D` for every lower envelope `ρ` on `0, …, E` with excess `D`. -/
theorem slashable_of_dJustified_same_epoch {T : BlockTree B} {σ : Schedule V} {ρ : V → ℕ}
    {D E : ℕ} {votes : Finset (Vote V B)} {c₁ c₂ : Checkpoint B} (hρ : Envelope σ ρ D E)
    (h₁ : DJustified T σ votes c₁) (h₂ : DJustified T σ votes c₂)
    (he : c₁.epoch = c₂.epoch) (hE : c₁.epoch ≤ E) (hne : c₁ ≠ c₂) :
    totalStake ρ ≤ 3 * stake ρ (slashable votes) + 2 * D :=
  slashable_of_dJustifiedFrom_same_epoch (hρ.on _) h₁.from_genesis h₂.from_genesis he hE hne

/-! ### Accountable safety up to an envelope -/

/-- If `3 ρ(slashable) + 2D < W_ρ` for a lower envelope `ρ` on `a.epoch, …, E` with excess
`D`, then every checkpoint `c` justified from the anchor `a` with `f.epoch ≤ c.epoch ≤ E`
descends from the checkpoint `f` that is `k`-finalized from `a`. -/
theorem anc_of_dKFinalizedFrom_of_dJustifiedFrom {T : BlockTree B} {σ : Schedule V}
    {ρ : V → ℕ} {D E : ℕ} {votes : Finset (Vote V B)} {k : ℕ} {a f c : Checkpoint B}
    (hρ : EnvelopeOn σ ρ D a.epoch E) (hf : DKFinalizedFrom T σ votes a k f)
    (hc : DJustifiedFrom T σ votes a c)
    (hle : f.epoch ≤ c.epoch) (hcE : c.epoch ≤ E)
    (hH : 3 * stake ρ (slashable votes) + 2 * D < totalStake ρ) :
    T.anc f.block c.block := by
  have hfa : a.epoch ≤ f.epoch := hf.justified.epoch_le
  obtain ⟨hk, C, h0, hCe, hCa, hCJ, hCl⟩ := hf
  have hJk : DJustifiedFrom T σ votes a (C k) := DJustifiedFrom.link (hCJ 0 hk) hCl
  have hAk : T.anc f.block (C k).block := h0 ▸ hCl.2.1
  induction hc with
  | anchor =>
    have := (h0 ▸ hCJ 0 hk : DJustifiedFrom T σ votes a f).eq_anchor (by omega)
    rw [this]
    exact T.anc_refl _
  | @link s t hs hl ih =>
    by_cases hwin : t.epoch ≤ f.epoch + k
    · -- `t` lies at the epoch of some `C i`; the two checkpoints coincide.
      obtain ⟨i, hi⟩ : ∃ i, i = t.epoch - f.epoch := ⟨_, rfl⟩
      have hCi : (C i).epoch = t.epoch := by rw [hCe i (by omega)]; omega
      have hJi : DJustifiedFrom T σ votes a (C i) := by
        rcases Nat.lt_or_eq_of_le (show i ≤ k by omega) with h | h
        · exact hCJ i h
        · exact h ▸ hJk
      have hAi : T.anc f.block (C i).block := by
        rcases Nat.lt_or_eq_of_le (show i ≤ k by omega) with h | h
        · exact hCa i h
        · exact h ▸ hAk
      by_cases heq : C i = t
      · exact heq ▸ hAi
      · have := slashable_of_dJustifiedFrom_same_epoch hρ hJi (DJustifiedFrom.link hs hl) hCi
          (by omega) heq
        omega
    · by_cases hsf : s.epoch < f.epoch
      · -- The link `s → t` surrounds the link `C 0 → C k`.
        have hC0 : (C 0).epoch = f.epoch := by rw [h0]
        have hCk : (C k).epoch = f.epoch + k := hCe k le_rfl
        have := stake_of_dlinks_inter_subset hρ hs.epoch_le (by omega) (by omega) (by omega)
          hl hCl (voters_inter_subset_slashable_of_surround (by omega) (by omega) (by omega))
        omega
      · have := hl.1
        exact T.anc_trans (ih (by omega) (by omega)) hl.2.1

/-- If `3 ρ(slashable) + 2D < W_ρ` for a lower envelope `ρ` on `0, …, E` with excess `D`,
then every justified checkpoint `c` with `f.epoch ≤ c.epoch ≤ E` descends from the
`k`-finalized checkpoint `f`. -/
theorem anc_of_dKFinalized_of_dJustified {T : BlockTree B} {σ : Schedule V} {ρ : V → ℕ}
    {D E : ℕ} {votes : Finset (Vote V B)} {k : ℕ} {f c : Checkpoint B}
    (hρ : Envelope σ ρ D E) (hf : DKFinalized T σ votes k f) (hc : DJustified T σ votes c)
    (hle : f.epoch ≤ c.epoch) (hcE : c.epoch ≤ E)
    (hH : 3 * stake ρ (slashable votes) + 2 * D < totalStake ρ) :
    T.anc f.block c.block :=
  anc_of_dKFinalizedFrom_of_dJustifiedFrom (hρ.on _) hf.from_genesis hc.from_genesis hle hcE hH

/-- Accountable safety up to an envelope on a window, for `k`-finalization from an anchor.
Let `ρ` be a lower envelope of the sets active at the epochs `a.epoch, …, E` with excess at
most `D`. If two checkpoints on conflicting blocks at epochs at most `E` are `k₁`- and
`k₂`-finalized from the anchor `a`, then `W_ρ ≤ 3 ρ(slashable) + 2D`. -/
theorem accountable_safety_kFinalized_envelope_from {T : BlockTree B} {σ : Schedule V}
    {ρ : V → ℕ} {D E : ℕ} {votes : Finset (Vote V B)} {k₁ k₂ : ℕ} {a f₁ f₂ : Checkpoint B}
    (hρ : EnvelopeOn σ ρ D a.epoch E) (h₁ : DKFinalizedFrom T σ votes a k₁ f₁)
    (h₂ : DKFinalizedFrom T σ votes a k₂ f₂) (hE₁ : f₁.epoch ≤ E) (hE₂ : f₂.epoch ≤ E)
    (hc : T.Conflicting f₁.block f₂.block) :
    totalStake ρ ≤ 3 * stake ρ (slashable votes) + 2 * D := by
  by_contra hH
  rw [not_le] at hH
  rcases le_total f₁.epoch f₂.epoch with h | h
  · exact hc.1 (anc_of_dKFinalizedFrom_of_dJustifiedFrom hρ h₁ h₂.justified h hE₂ hH)
  · exact hc.2 (anc_of_dKFinalizedFrom_of_dJustifiedFrom hρ h₂ h₁.justified h hE₁ hH)

/-- Accountable safety up to an envelope on a window, for finalization from an anchor `a`:
the case `k₁ = k₂ = 1` of `accountable_safety_kFinalized_envelope_from`. -/
theorem accountable_safety_envelope_from {T : BlockTree B} {σ : Schedule V} {ρ : V → ℕ}
    {D E : ℕ} {votes : Finset (Vote V B)} {a f₁ f₂ : Checkpoint B}
    (hρ : EnvelopeOn σ ρ D a.epoch E) (h₁ : DFinalizedFrom T σ votes a f₁)
    (h₂ : DFinalizedFrom T σ votes a f₂) (hE₁ : f₁.epoch ≤ E) (hE₂ : f₂.epoch ≤ E)
    (hc : T.Conflicting f₁.block f₂.block) :
    totalStake ρ ≤ 3 * stake ρ (slashable votes) + 2 * D :=
  accountable_safety_kFinalized_envelope_from hρ h₁.kFinalized h₂.kFinalized hE₁ hE₂ hc

/-- Accountable safety up to an envelope, for `k`-finalization. Let `ρ` be a lower envelope
of the sets active at the epochs `0, …, E` with excess at most `D`. If two checkpoints on
conflicting blocks at epochs at most `E` are `k₁`- and `k₂`-finalized, then
`W_ρ ≤ 3 ρ(slashable) + 2D`. -/
theorem accountable_safety_kFinalized_envelope {T : BlockTree B} {σ : Schedule V}
    {ρ : V → ℕ} {D E : ℕ} {votes : Finset (Vote V B)} {k₁ k₂ : ℕ} {f₁ f₂ : Checkpoint B}
    (hρ : Envelope σ ρ D E) (h₁ : DKFinalized T σ votes k₁ f₁)
    (h₂ : DKFinalized T σ votes k₂ f₂) (hE₁ : f₁.epoch ≤ E) (hE₂ : f₂.epoch ≤ E)
    (hc : T.Conflicting f₁.block f₂.block) :
    totalStake ρ ≤ 3 * stake ρ (slashable votes) + 2 * D :=
  accountable_safety_kFinalized_envelope_from (hρ.on _) h₁.from_genesis h₂.from_genesis hE₁ hE₂
    hc

/-- Accountable safety up to an envelope. Let `ρ` be a lower envelope of the sets active at
the epochs `0, …, E` with excess at most `D`. If two checkpoints on conflicting blocks at
epochs at most `E` are finalized, then `W_ρ ≤ 3 ρ(slashable) + 2D`. -/
theorem accountable_safety_envelope {T : BlockTree B} {σ : Schedule V} {ρ : V → ℕ}
    {D E : ℕ} {votes : Finset (Vote V B)} {f₁ f₂ : Checkpoint B} (hρ : Envelope σ ρ D E)
    (h₁ : DFinalized T σ votes f₁) (h₂ : DFinalized T σ votes f₂) (hE₁ : f₁.epoch ≤ E)
    (hE₂ : f₂.epoch ≤ E) (hc : T.Conflicting f₁.block f₂.block) :
    totalStake ρ ≤ 3 * stake ρ (slashable votes) + 2 * D :=
  accountable_safety_kFinalized_envelope hρ h₁.kFinalized h₂.kFinalized hE₁ hE₂ hc

/-! ### Churn -/

/-- `stableWeight σ E v`: the least stake of `v` over the epochs `0, …, E`, i.e. the stake of
`v` that is present throughout these epochs. -/
def stableWeight (σ : Schedule V) : ℕ → V → ℕ
  | 0, v => σ 0 v
  | E + 1, v => min (stableWeight σ E v) (σ (E + 1) v)

/-- `maxWeight σ E v`: the largest stake of `v` over the epochs `0, …, E`. -/
def maxWeight (σ : Schedule V) : ℕ → V → ℕ
  | 0, v => σ 0 v
  | E + 1, v => max (maxWeight σ E v) (σ (E + 1) v)

/-- The churn of `σ` up to epoch `E`: the total over validators of the difference between the
largest and the least stake over the epochs `0, …, E`. -/
def churn (σ : Schedule V) (E : ℕ) : ℕ :=
  ∑ v, (maxWeight σ E v - stableWeight σ E v)

/-- The change between the sets active at `e` and `e + 1`: the `ℓ¹` distance
`∑ v, |σ (e + 1) v - σ e v|`. For sets with fixed per-validator stake it is the stake of their
symmetric difference. -/
def stepChurn (σ : Schedule V) (e : ℕ) : ℕ :=
  ∑ v, ((σ (e + 1) v - σ e v) + (σ e v - σ (e + 1) v))

/-- The sum of the per-epoch changes from epoch `0` to epoch `E`. -/
def pathChurn (σ : Schedule V) (E : ℕ) : ℕ :=
  ∑ e ∈ Finset.range E, stepChurn σ e

omit [Fintype V] [DecidableEq V] in
theorem stableWeight_le {σ : Schedule V} {E e : ℕ} (h : e ≤ E) (v : V) :
    stableWeight σ E v ≤ σ e v := by
  induction E with
  | zero => obtain rfl : e = 0 := by omega
            exact le_rfl
  | succ E ih =>
    simp only [stableWeight]
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · have := ih (by omega)
      omega
    · omega

omit [Fintype V] [DecidableEq V] in
theorem le_maxWeight {σ : Schedule V} {E e : ℕ} (h : e ≤ E) (v : V) :
    σ e v ≤ maxWeight σ E v := by
  induction E with
  | zero => obtain rfl : e = 0 := by omega
            exact le_rfl
  | succ E ih =>
    simp only [maxWeight]
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · have := ih (by omega)
      omega
    · omega

omit [DecidableEq V] in
/-- The stable weight is a lower envelope of the sets active at the epochs `0, …, E`, with
excess at most the churn. -/
theorem envelope_stableWeight (σ : Schedule V) (E : ℕ) :
    Envelope σ (stableWeight σ E) (churn σ E) E := by
  intro e he
  refine ⟨stableWeight_le he, ?_⟩
  unfold totalStake stake churn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  have := stableWeight_le (σ := σ) he v
  have := le_maxWeight (σ := σ) he v
  omega

omit [DecidableEq V] in
/-- The churn up to `E` is at most the sum of the per-epoch changes up to `E`. -/
theorem churn_le_pathChurn (σ : Schedule V) (E : ℕ) : churn σ E ≤ pathChurn σ E := by
  induction E with
  | zero => simp [churn, pathChurn, stableWeight, maxWeight]
  | succ E ih =>
    rw [pathChurn, Finset.sum_range_succ, ← pathChurn]
    refine le_trans ?_ (Nat.add_le_add_right ih _)
    unfold churn stepChurn
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have := stableWeight_le (σ := σ) (le_refl E) v
    have := le_maxWeight (σ := σ) (le_refl E) v
    simp only [stableWeight, maxWeight]
    omega

omit [DecidableEq V] in
/-- The stable weight of the shifted schedule `e ↦ σ (e₀ + e)` up to `E - e₀` is a lower
envelope of the sets active at the epochs `e₀, …, E`, with excess at most its churn. -/
theorem envelopeOn_stableWeight_shift (σ : Schedule V) (e₀ E : ℕ) :
    EnvelopeOn σ (stableWeight (fun e => σ (e₀ + e)) (E - e₀))
      (churn (fun e => σ (e₀ + e)) (E - e₀)) e₀ E := by
  intro e h₀ hE
  have h := envelope_stableWeight (fun e => σ (e₀ + e)) (E - e₀) (e - e₀) (by omega)
  simp only [show e₀ + (e - e₀) = e by omega] at h
  exact h

/-! ### Accountable safety with churn -/

/-- Accountable safety with a dynamic validator set over a window (headline, windowed). Let
`σ` be a validator-set schedule, `a` an anchor checkpoint of epoch `e₀ = a.epoch`, let `f₁` and
`f₂` be checkpoints finalized from `a` on conflicting blocks, and let
`E = max f₁.epoch f₂.epoch`. With the shifted schedule `σ' e = σ (e₀ + e)`, the slashable
validators hold `stableWeight σ' (E - e₀)`-stake at least one third of the total stable stake
minus two thirds of the churn of the window:
`W_stable ≤ 3 · stake_stable(slashable) + 2 · churn σ' (E - e₀)`. -/
theorem accountable_safety_dynamic_from {T : BlockTree B} {σ : Schedule V}
    {votes : Finset (Vote V B)} {a f₁ f₂ : Checkpoint B} (h₁ : DFinalizedFrom T σ votes a f₁)
    (h₂ : DFinalizedFrom T σ votes a f₂) (hc : T.Conflicting f₁.block f₂.block) :
    totalStake (stableWeight (fun e => σ (a.epoch + e)) (max f₁.epoch f₂.epoch - a.epoch)) ≤
      3 * stake (stableWeight (fun e => σ (a.epoch + e)) (max f₁.epoch f₂.epoch - a.epoch))
          (slashable votes) +
        2 * churn (fun e => σ (a.epoch + e)) (max f₁.epoch f₂.epoch - a.epoch) :=
  accountable_safety_envelope_from (envelopeOn_stableWeight_shift σ a.epoch _) h₁ h₂
    (le_max_left _ _) (le_max_right _ _) hc

/-- Accountable safety with a dynamic validator set (headline). Let `σ` be a validator-set
schedule, let `f₁` and `f₂` be finalized checkpoints on conflicting blocks, and let
`E = max f₁.epoch f₂.epoch`. Then the slashable validators hold `stableWeight σ E`-stake at
least one third of the total stable stake minus two thirds of the churn:
`W_stable ≤ 3 · stake_stable(slashable) + 2 · churn σ E`. This is the case of the genesis
anchor of `accountable_safety_dynamic_from`. -/
theorem accountable_safety_dynamic {T : BlockTree B} {σ : Schedule V}
    {votes : Finset (Vote V B)} {f₁ f₂ : Checkpoint B} (h₁ : DFinalized T σ votes f₁)
    (h₂ : DFinalized T σ votes f₂) (hc : T.Conflicting f₁.block f₂.block) :
    totalStake (stableWeight σ (max f₁.epoch f₂.epoch)) ≤
      3 * stake (stableWeight σ (max f₁.epoch f₂.epoch)) (slashable votes) +
        2 * churn σ (max f₁.epoch f₂.epoch) := by
  simpa [genesisCheckpoint] using
    accountable_safety_dynamic_from h₁.from_genesis h₂.from_genesis hc

/-- Accountable safety with a dynamic validator set, measured in the set active at an epoch.
Let `f₁` and `f₂` be finalized checkpoints on conflicting blocks and `E = max f₁.epoch
f₂.epoch`. For every epoch `e ≤ E`, the slashable validators hold at least one third of the
stake of `σ e` minus the churn: `W_{σ e} ≤ 3 · stake_{σ e}(slashable) + 3 · churn σ E`. -/
theorem accountable_safety_dynamic_epoch {T : BlockTree B} {σ : Schedule V}
    {votes : Finset (Vote V B)} {f₁ f₂ : Checkpoint B} (h₁ : DFinalized T σ votes f₁)
    (h₂ : DFinalized T σ votes f₂) (hc : T.Conflicting f₁.block f₂.block) {e : ℕ}
    (he : e ≤ max f₁.epoch f₂.epoch) :
    totalStake (σ e) ≤
      3 * stake (σ e) (slashable votes) + 3 * churn σ (max f₁.epoch f₂.epoch) := by
  have h := accountable_safety_dynamic h₁ h₂ hc
  obtain ⟨hle, hD⟩ := envelope_stableWeight σ _ e he
  have hS : stake (stableWeight σ (max f₁.epoch f₂.epoch)) (slashable votes) ≤
      stake (σ e) (slashable votes) := Finset.sum_le_sum fun v _ => hle v
  omega

/-- Zero churn: if the churn up to `E = max f₁.epoch f₂.epoch` vanishes, two finalized
checkpoints on conflicting blocks force `W_{σ e} ≤ 3 · stake_{σ e}(slashable)` for every
`e ≤ E`, the bound of the fixed-set theorem `FFG.accountable_safety`. -/
theorem accountable_safety_of_churn_eq_zero {T : BlockTree B} {σ : Schedule V}
    {votes : Finset (Vote V B)} {f₁ f₂ : Checkpoint B} (h₁ : DFinalized T σ votes f₁)
    (h₂ : DFinalized T σ votes f₂) (hc : T.Conflicting f₁.block f₂.block)
    (h0 : churn σ (max f₁.epoch f₂.epoch) = 0) {e : ℕ} (he : e ≤ max f₁.epoch f₂.epoch) :
    3 * stake (σ e) (slashable votes) ≥ totalStake (σ e) := by
  have := accountable_safety_dynamic_epoch h₁ h₂ hc he
  omega

omit [DecidableEq V] in
/-- A constant schedule has zero churn. -/
theorem churn_const (w : V → ℕ) (E : ℕ) : churn (fun _ => w) E = 0 := by
  have hs : ∀ E, stableWeight (fun _ => w) E = w := by
    intro E
    induction E with
    | zero => rfl
    | succ E ih => funext v; simp [stableWeight, ih]
  have hm : ∀ E, maxWeight (fun _ => w) E = w := by
    intro E
    induction E with
    | zero => rfl
    | succ E ih => funext v; simp [maxWeight, ih]
  simp [churn, hs, hm]

/-- The fixed-set theorem as the zero-churn case: `FFG.accountable_safety`, derived from the
dynamic theorem for the constant schedule `fun _ => w`. -/
theorem accountable_safety_const {T : BlockTree B} {w : V → ℕ} {votes : Finset (Vote V B)}
    {f₁ f₂ : Checkpoint B} (h₁ : Finalized T w votes f₁) (h₂ : Finalized T w votes f₂)
    (hc : T.Conflicting f₁.block f₂.block) :
    3 * stake w (slashable votes) ≥ totalStake w :=
  accountable_safety_of_churn_eq_zero (σ := fun _ => w) (dFinalized_const_iff.2 h₁)
    (dFinalized_const_iff.2 h₂) hc (churn_const w _) (Nat.zero_le _)

end CatCryptCore.Consensus.FFGDynamic

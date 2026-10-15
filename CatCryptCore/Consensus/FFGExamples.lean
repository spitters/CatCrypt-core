/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.FFG

/-!
# Casper FFG: concrete examples

This file shows that the hypotheses of `accountable_safety` are satisfiable and that its
conclusion is not trivially true. The block tree `forkTree` has the genesis block `0` and two
children `1` and `2`, which conflict. There are four validators of stake `1`, so `W = 4` and
the bound `3 * stake ≥ W` means stake at least `2`.

## Main results

* `doubleVotes_finalized_conflicting`, `doubleVotes_slashable`: a vote set in which the
  conflicting checkpoints `(1, 1)` and `(2, 1)` are finalized; its slashable set is `{1, 2}`
  (condition E1), of stake `2`.
* `surroundVotes_finalized_conflicting`, `surroundVotes_slashable`: a vote set in which
  `(1, 1)` and `(2, 3)` are finalized; its slashable set is `{1, 2}` (condition E2 only), of
  stake `2`.
* `honestVotes_finalized`, `honestVotes_slashable`: a vote set in which `(1, 1)` is finalized
  and the slashable set is empty.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.FFG.Examples

/-- The block tree with genesis `0` and two children `1` and `2`. -/
def forkTree : BlockTree (Fin 3) where
  anc a b := a = b ∨ a = 0
  genesis := 0
  anc_refl _ := Or.inl rfl
  anc_trans := by
    rintro a b c (rfl | rfl) (rfl | rfl) <;> simp

instance (a b : Fin 3) : Decidable (forkTree.anc a b) := by
  unfold forkTree; infer_instance

instance (votes : Finset (Vote (Fin 4) (Fin 3))) (s t : Checkpoint (Fin 3)) (w : Fin 4 → ℕ) :
    Decidable (SupermajorityLink forkTree w votes s t) := by
  unfold SupermajorityLink; infer_instance

theorem forkTree_conflicting : forkTree.Conflicting 1 2 := by
  unfold BlockTree.Conflicting; decide

/-- Four validators of stake `1`. -/
def unitStake : Fin 4 → ℕ := fun _ => 1

theorem totalStake_unitStake : totalStake unitStake = 4 := by decide

/-- The vote of validator `v` for the link `(b₁, e₁) → (b₂, e₂)`. -/
def vote (v : Fin 4) (b₁ : Fin 3) (e₁ : ℕ) (b₂ : Fin 3) (e₂ : ℕ) : Vote (Fin 4) (Fin 3) :=
  ⟨v, ⟨b₁, e₁⟩, ⟨b₂, e₂⟩⟩

/-- Validators `0, 1, 2` finalize `(1, 1)` and validators `1, 2, 3` finalize `(2, 1)`. -/
def doubleVotes : Finset (Vote (Fin 4) (Fin 3)) :=
  {vote 0 0 0 1 1, vote 1 0 0 1 1, vote 2 0 0 1 1,
   vote 0 1 1 1 2, vote 1 1 1 1 2, vote 2 1 1 1 2,
   vote 1 0 0 2 1, vote 2 0 0 2 1, vote 3 0 0 2 1,
   vote 1 2 1 2 2, vote 2 2 1 2 2, vote 3 2 1 2 2}

/-- Validators `0, 1, 2` finalize `(1, 1)`; validators `1, 2, 3` justify `(2, 3)` from
genesis, which surrounds the link `(1, 1) → (1, 2)`, and finalize it. -/
def surroundVotes : Finset (Vote (Fin 4) (Fin 3)) :=
  {vote 0 0 0 1 1, vote 1 0 0 1 1, vote 2 0 0 1 1,
   vote 0 1 1 1 2, vote 1 1 1 1 2, vote 2 1 1 1 2,
   vote 1 0 0 2 3, vote 2 0 0 2 3, vote 3 0 0 2 3,
   vote 1 2 3 2 4, vote 2 2 3 2 4, vote 3 2 3 2 4}

/-- All four validators finalize `(1, 1)`. -/
def honestVotes : Finset (Vote (Fin 4) (Fin 3)) :=
  {vote 0 0 0 1 1, vote 1 0 0 1 1, vote 2 0 0 1 1, vote 3 0 0 1 1,
   vote 0 1 1 1 2, vote 1 1 1 1 2, vote 2 1 1 1 2, vote 3 1 1 1 2}

/-- A checkpoint `c` with a supermajority link from genesis to `c` and one from `c` to a
checkpoint at the next epoch is finalized. -/
theorem finalized_of_links {votes : Finset (Vote (Fin 4) (Fin 3))} {c c' : Checkpoint (Fin 3)}
    (h₁ : SupermajorityLink forkTree unitStake votes (genesisCheckpoint forkTree) c)
    (he : c'.epoch = c.epoch + 1) (h₂ : SupermajorityLink forkTree unitStake votes c c') :
    Finalized forkTree unitStake votes c :=
  ⟨Justified.link Justified.genesis h₁, c', he, h₂⟩

theorem doubleVotes_finalized_conflicting :
    Finalized forkTree unitStake doubleVotes ⟨1, 1⟩ ∧
      Finalized forkTree unitStake doubleVotes ⟨2, 1⟩ ∧
      forkTree.Conflicting (⟨1, 1⟩ : Checkpoint (Fin 3)).block
        (⟨2, 1⟩ : Checkpoint (Fin 3)).block :=
  ⟨finalized_of_links (c' := ⟨1, 2⟩) (by decide) rfl (by decide),
    finalized_of_links (c' := ⟨2, 2⟩) (by decide) rfl (by decide), forkTree_conflicting⟩

/-- The slashable set of `doubleVotes` is `{1, 2}`; its stake `2` meets the bound
`3 * stake ≥ W = 4` of `accountable_safety`. -/
theorem doubleVotes_slashable :
    slashable doubleVotes = {1, 2} ∧ stake unitStake (slashable doubleVotes) = 2 ∧
      3 * stake unitStake (slashable doubleVotes) ≥ totalStake unitStake := by
  decide

/-- `accountable_safety` applies to `doubleVotes`: its hypotheses are satisfiable. -/
theorem accountable_safety_doubleVotes :
    3 * stake unitStake (slashable doubleVotes) ≥ totalStake unitStake :=
  accountable_safety doubleVotes_finalized_conflicting.1 doubleVotes_finalized_conflicting.2.1
    doubleVotes_finalized_conflicting.2.2

/-- In `doubleVotes` no validator violates E2: the slashing comes from E1 alone. -/
theorem doubleVotes_no_surround : ∀ v, ¬ SurroundVote doubleVotes v := by decide

theorem surroundVotes_finalized_conflicting :
    Finalized forkTree unitStake surroundVotes ⟨1, 1⟩ ∧
      Finalized forkTree unitStake surroundVotes ⟨2, 3⟩ ∧
      forkTree.Conflicting (⟨1, 1⟩ : Checkpoint (Fin 3)).block
        (⟨2, 3⟩ : Checkpoint (Fin 3)).block :=
  ⟨finalized_of_links (c' := ⟨1, 2⟩) (by decide) rfl (by decide),
    finalized_of_links (c' := ⟨2, 4⟩) (by decide) rfl (by decide), forkTree_conflicting⟩

/-- The slashable set of `surroundVotes` is `{1, 2}`, of stake `2`. -/
theorem surroundVotes_slashable :
    slashable surroundVotes = {1, 2} ∧ stake unitStake (slashable surroundVotes) = 2 ∧
      3 * stake unitStake (slashable surroundVotes) ≥ totalStake unitStake := by
  decide

/-- In `surroundVotes` no validator violates E1: the slashing comes from E2 alone. -/
theorem surroundVotes_no_double : ∀ v, ¬ DoubleVote surroundVotes v := by decide

theorem honestVotes_finalized : Finalized forkTree unitStake honestVotes ⟨1, 1⟩ :=
  finalized_of_links (c' := ⟨1, 2⟩) (by decide) rfl (by decide)

/-- The slashable set of `honestVotes` is empty. -/
theorem honestVotes_slashable : slashable honestVotes = ∅ := by decide

/-- `plausible_liveness` applies to `honestVotes` with all four validators honest, the
justified checkpoint `(1, 1)` and the descendant choice `d b e = b`: the added votes finalize
the checkpoint `(1, 3)` and no validator becomes slashable. -/
theorem honestVotes_liveness :
    livenessTarget (fun b _ => b) honestVotes ⟨1, 1⟩ = ⟨1, 3⟩ ∧
      Finalized forkTree unitStake
        (honestVotes ∪ livenessVotes Finset.univ (fun b _ => b) honestVotes ⟨1, 1⟩) ⟨1, 3⟩ ∧
      slashable (honestVotes ∪ livenessVotes Finset.univ (fun b _ => b) honestVotes ⟨1, 1⟩) =
        ∅ := by
  have ht : livenessTarget (fun b _ => b) honestVotes ⟨1, 1⟩ = ⟨1, 3⟩ := by decide
  have h := plausible_liveness (T := forkTree) (w := unitStake) (H := Finset.univ)
    (fun b _ => b) (fun b _ => forkTree.anc_refl b) (by decide)
    honestVotes_finalized.1 (by decide) (by simp [honestVotes_slashable])
  rw [ht, Finset.inter_univ] at h
  exact ⟨ht, h.2.2.2.1, h.2.2.2.2⟩

end CatCryptCore.Consensus.FFG.Examples

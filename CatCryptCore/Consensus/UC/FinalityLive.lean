/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.FinalityGadget
public import CatCryptCore.Consensus.FinalityUpdated

@[expose] public section
set_option autoImplicit false

/-!
# Finality liveness of the FFG gadget as a trace property

This file proves that a run of the FFG finality gadget (`CatCryptCore.Consensus.UC.FinalityGadget`)
whose honest validators follow the liveness schedule of `CatCryptCore.Consensus.FinalityUpdated`
reports to `F_FinTree` a tree trace satisfying `TreeTrace.UpdatedWithin`: from round
`2 E + σ + d + Δ` on, every honest party has a final block whose slot is at most
`3 E + 2 σ + d + Δ - 1` rounds behind the current round. The property is checked on the
prefixes of the trace (`stable_updatedWithin`).

## Hypotheses

* `LiveHyp c σ X` on the positions `X = posTT c G`: every window of `σ` slots ending at or
  before the current round contains the slot of a block of every honest position; slots
  decrease strictly along positions; the genesis block, of slot `0`, is on every honest position;
  positions are chains of the block tree; the round starts at `0` and advances by at most `1`
  per step (`TreeTrace.RoundStep`).
* The gadget votes on the positions pruned by depth `d`: `c.cut v p` consists of the blocks of
  `v.pos p` of slot at most `v.round - d` (`slotCut` of `UC.Stack`).
* Round `r` of the honest schedule starts at the first time of round `2 E + σ + d + r (2 E)`
  (`roundTime`), where the cast votes contain the votes `roundVotes` of round `r`, read off
  the pruned position of the validator `v₀ ∈ H`.
* The adversarial validators hold less than a third of the stake, `1 ≤ E` and `1 ≤ Δ`.

## Method

`Finality.finality_updated_start` is applied to the trace of pruned positions
(`prunedTrace`), whose clock is the round minus `d` up to the time `t` under consideration and
advances by one per step after it (`liveNow`), so that every round of the schedule has a phase
(`liveRho`). The pruned positions have slot common prefix with parameter `0`, by the
settledness of the run (`Run.settled`). The gadget delivers every vote cast `Δ` rounds ago,
which is synchrony with `GST = 0`. Accountable safety makes the finalized block of each epoch
unique, so it is in the final list. The lag `3 E + σ + Δ` of `finality_updated_start` in
pruned slots becomes `3 E + σ + d + Δ` in rounds, and `σ - 1` more since the final block has
slot within `σ` below the epoch boundary.

## Main results

* `schedule_congr`, `roundVotes_congr`: the schedule up to round `r` depends only on the
  descendant functions of the rounds before `r`.
* `slotCommonPrefix_pruned`: the pruned positions of a run have slot common prefix `0`.
* `Run.updatedWithin_of_schedule`: finality liveness, `UpdatedWithin` on `finTT`.
-/

namespace CatCryptCore.Consensus.UC.FFGGadget

open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.Finality FFG

/-! ## Lists with decreasing slots -/

section Lists

variable {B : Type} {slot : B → ℕ}

/-- The blocks of slot at most `s` of a list with strictly decreasing slots form a suffix of
it. -/
theorem filter_slot_suffix {C : List B} (hC : C.Pairwise fun b b' => slot b' < slot b) (s : ℕ) :
    C.filter (fun b => decide (slot b ≤ s)) <:+ C := by
  induction C with
  | nil => exact List.suffix_refl _
  | cons a C ih =>
    rw [List.pairwise_cons] at hC
    by_cases ha : slot a ≤ s
    · have e : (a :: C).filter (fun b => decide (slot b ≤ s)) = a :: C := by
        refine List.filter_eq_self.2 fun b hb => ?_
        rcases List.mem_cons.1 hb with rfl | hb
        · simpa using ha
        · have := hC.1 b hb
          simp only [decide_eq_true_eq]
          omega
      rw [e]
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      exact (ih hC.2).trans (List.suffix_cons a C)

/-- In a list with strictly decreasing slots containing a block `g` of slot `0`, `g` is the
only block of slot `0`. -/
theorem filter_slot_zero {C : List B} (hC : C.Pairwise fun b b' => slot b' < slot b) {g : B}
    (hg : g ∈ C) (hs : slot g = 0) : C.filter (fun b => decide (slot b ≤ 0)) = [g] := by
  induction C with
  | nil => simp at hg
  | cons a C ih =>
    rw [List.pairwise_cons] at hC
    rcases List.mem_cons.1 hg with rfl | hg
    · rw [List.filter_cons_of_pos (by simp [hs]), List.filter_eq_nil_iff.2]
      intro b hb
      have := hC.1 b hb
      simp only [decide_eq_true_eq]
      omega
    · have := hC.1 g hg
      rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; omega)]
      exact ih hC.2 hg

/-- In a list with strictly decreasing slots, the newest block of slot at most `s` has a slot
at least that of every block of slot at most `s`. -/
theorem slot_le_of_find? {C : List B} (hC : C.Pairwise fun b b' => slot b' < slot b) {s : ℕ}
    {b b' : B} (h : C.find? (fun x => decide (slot x ≤ s)) = some b) (hb' : b' ∈ C)
    (hs : slot b' ≤ s) : slot b' ≤ slot b := by
  induction C with
  | nil => simp at hb'
  | cons a C ih =>
    rw [List.pairwise_cons] at hC
    by_cases ha : slot a ≤ s
    · simp only [List.find?_cons, ha, decide_true, Option.some.injEq] at h
      subst h
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact le_rfl
      · exact (hC.1 b' hb').le
    · simp only [List.find?_cons, ha, decide_false] at h
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact absurd hs ha
      · exact ih hC.2 h hb'

/-- On a list with strictly decreasing slots that contains the genesis block of slot `0`, the
genesis checkpoint is the epoch-boundary checkpoint of epoch `0`. -/
theorem isCheckpointOf_genesis {T : BlockTree B} {C : List B}
    (hC : C.Pairwise fun b b' => slot b' < slot b) (hg : T.genesis ∈ C) (hs : slot T.genesis = 0)
    (E : ℕ) : IsCheckpointOf slot E C (genesisCheckpoint T) := by
  show C.find? (fun b => decide (slot b ≤ 0 * E)) = some T.genesis
  rw [Nat.zero_mul, ← List.head?_filter, filter_slot_zero hC hg hs]
  rfl

end Lists

/-! ## The schedule depends only on earlier rounds -/

section Congr

variable {V B : Type} [DecidableEq V] [DecidableEq B] {H : Finset V} {D D' : ℕ → B → ℕ → B}
  {pre : Finset (Vote V B)} {j₀ : Checkpoint B}

/-- The state of the schedule after `r` rounds depends only on the descendant functions of
the rounds before `r`. -/
theorem schedule_congr {r : ℕ} (hD : ∀ r' < r, D r' = D' r') :
    schedule H D pre j₀ r = schedule H D' pre j₀ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h1 := ih fun r' hr' => hD r' (by omega)
    have h2 := hD r (by omega)
    simp only [schedule_succ, roundVotes, h1, h2]

/-- The votes of round `r` depend only on the descendant functions of the rounds up to `r`. -/
theorem roundVotes_congr {r : ℕ} (hD : ∀ r' ≤ r, D r' = D' r') :
    roundVotes H D pre j₀ r = roundVotes H D' pre j₀ r := by
  simp only [roundVotes, schedule_congr (fun r' hr' => hD r' hr'.le), hD r le_rfl]

end Congr

/-! ## Pruned positions and the clock -/

section Clock

variable {Party Blk : Type}

/-- The positions pruned by depth `d`: the blocks of the position of `p` at `t` of slot at most
the round minus `d`. -/
def prunedTrace (sl : Blk → ℕ) (d : ℕ) (X : TreeTrace Party Blk) : ChainTrace Party Blk :=
  ⟨X.honest, fun t p => ((X.st t).pos p).filter fun b => decide (sl b ≤ (X.st t).round - d)⟩

/-- The clock of the pruned positions with horizon `hz`: the round minus `d` up to `hz`, and
one more per step after `hz`. -/
def liveNow (X : TreeTrace Party Blk) (d hz j : ℕ) : ℕ :=
  (X.st (min j hz)).round - d + (j - hz)

theorem le_liveNow (X : TreeTrace Party Blk) (d hz k : ℕ) : k ≤ liveNow X d hz (hz + k) := by
  unfold liveNow
  omega

theorem liveNow_of_le (X : TreeTrace Party Blk) (d : ℕ) {hz j : ℕ} (hj : j ≤ hz) :
    liveNow X d hz j = (X.st j).round - d := by
  unfold liveNow
  rw [min_eq_left hj]
  omega

theorem liveNow_mono {X : TreeTrace Party Blk} (hm : X.RoundsMonotone) (d hz : ℕ) :
    Monotone (liveNow X d hz) := by
  intro j j' hjj
  have := hm (min j hz) (min j' hz) (min_le_min_right hz hjj)
  unfold liveNow
  omega

theorem liveNow_succ {X : TreeTrace Party Blk} (hs : X.RoundStep) (d hz j : ℕ) :
    liveNow X d hz (j + 1) ≤ liveNow X d hz j + 1 := by
  unfold liveNow
  rcases Nat.lt_or_ge j hz with h | h
  · rw [min_eq_left (show j + 1 ≤ hz by omega), min_eq_left h.le]
    have := hs j
    omega
  · rw [min_eq_right (show hz ≤ j + 1 by omega), min_eq_right h]
    omega

/-- The phase of round `r` of the schedule for the clock `liveNow X d hz`: the first phase whose
clock is at least `τ₀ + r (2 E)`. -/
def liveRho (X : TreeTrace Party Blk) (d hz τ₀ E r : ℕ) : ℕ :=
  Nat.find (⟨hz + (τ₀ + r * (2 * E)), le_liveNow X d hz _⟩ :
    ∃ j, τ₀ + r * (2 * E) ≤ liveNow X d hz j)

theorem liveRho_spec (X : TreeTrace Party Blk) (d hz τ₀ E r : ℕ) :
    τ₀ + r * (2 * E) ≤ liveNow X d hz (liveRho X d hz τ₀ E r) :=
  Nat.find_spec (⟨hz + (τ₀ + r * (2 * E)), le_liveNow X d hz _⟩ :
    ∃ j, τ₀ + r * (2 * E) ≤ liveNow X d hz j)

theorem liveRho_mono (X : TreeTrace Party Blk) (d hz τ₀ E : ℕ) {r r' : ℕ} (hr : r ≤ r') :
    liveRho X d hz τ₀ E r ≤ liveRho X d hz τ₀ E r' :=
  Nat.find_mono fun _ hj => le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hr) _) hj

/-- If the round starts at `0` and advances by at most `1` per step, the clock at the phase of
round `r` is exactly `τ₀ + r (2 E)`, for `0 < τ₀`. -/
theorem liveNow_liveRho {X : TreeTrace Party Blk} (hs : X.RoundStep) (h0 : (X.st 0).round = 0)
    (d hz : ℕ) {τ₀ : ℕ} (hτ₀ : 0 < τ₀) (E r : ℕ) :
    liveNow X d hz (liveRho X d hz τ₀ E r) = τ₀ + r * (2 * E) := by
  refine le_antisymm ?_ (liveRho_spec X d hz τ₀ E r)
  by_cases hz0 : liveRho X d hz τ₀ E r = 0
  · have := liveRho_spec X d hz τ₀ E r
    rw [hz0] at this
    unfold liveNow at this
    rw [Nat.zero_min, h0] at this
    omega
  · obtain ⟨k, hk⟩ : ∃ k, liveRho X d hz τ₀ E r = k + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hz0).symm⟩
    have hmin : ¬ τ₀ + r * (2 * E) ≤ liveNow X d hz k :=
      Nat.find_min (⟨hz + (τ₀ + r * (2 * E)), le_liveNow X d hz _⟩ :
        ∃ j, τ₀ + r * (2 * E) ≤ liveNow X d hz j) (show k < liveRho X d hz τ₀ E r by omega)
    have := liveNow_succ hs d hz k
    rw [hk]
    omega

open Classical in
/-- The first time whose round is at least `R` (`0` if there is none). -/
noncomputable def roundTime (X : TreeTrace Party Blk) (R : ℕ) : ℕ :=
  if h : ∃ t, R ≤ (X.st t).round then Nat.find h else 0

/-- Within the horizon, the phase of round `r` is the first time of round `τ₀ + d + r (2 E)`. -/
theorem liveRho_eq_roundTime (X : TreeTrace Party Blk) {d hz τ₀ : ℕ} (hτ₀ : 0 < τ₀) {E r : ℕ}
    (hr : liveRho X d hz τ₀ E r ≤ hz) :
    liveRho X d hz τ₀ E r = roundTime X (τ₀ + d + r * (2 * E)) := by
  have hspec := liveRho_spec X d hz τ₀ E r
  rw [liveNow_of_le X d hr] at hspec
  have hex : ∃ t, τ₀ + d + r * (2 * E) ≤ (X.st t).round :=
    ⟨liveRho X d hz τ₀ E r, by omega⟩
  classical
  unfold roundTime
  rw [dif_pos hex]
  have h1 := Nat.find_spec hex
  have h2 : Nat.find hex ≤ liveRho X d hz τ₀ E r := Nat.find_min' hex (by omega)
  refine le_antisymm ?_ h2
  unfold liveRho
  refine Nat.find_min' _ ?_
  rw [liveNow_of_le X d (h2.trans hr)]
  omega

end Clock

/-! ## Finality liveness -/

section Live

variable {Party Blk : Type} [Fintype Party] [DecidableEq Party] [DecidableEq Blk]

/-- The hypotheses of finality liveness on the positions `X`, with chain-growth window `σ`:

* `growth`: every window `(a, a + σ]` of slots with `a + σ` at most the current round contains
  the slot of a block of every honest position;
* `decreasing`: slots decrease strictly along honest positions;
* `genesis_mem`, `genesis_slot`: the genesis block, of slot `0`, is on every honest position;
* `inTree`: honest positions are chains of the block tree;
* `round_zero`, `round_step`: the round starts at `0` and advances by at most `1` per step. -/
structure LiveHyp (c : Cfg Party Blk) (σ : ℕ) (X : TreeTrace Party Blk) : Prop where
  growth : ∀ p t a, X.honest p → a + σ ≤ (X.st t).round →
    ∃ b ∈ (X.st t).pos p, a < c.slot b ∧ c.slot b ≤ a + σ
  decreasing : ∀ p t, X.honest p → ((X.st t).pos p).Pairwise fun b b' => c.slot b' < c.slot b
  genesis_mem : ∀ p t, X.honest p → c.T.genesis ∈ (X.st t).pos p
  genesis_slot : c.slot c.T.genesis = 0
  inTree : X.chains.ChainsInTree c.T
  round_zero : (X.st 0).round = 0
  round_step : X.RoundStep

variable {c : Cfg Party Blk} {G : ℕ → GCore Party Blk} {σ d : ℕ}

/-- **Slot common prefix of the pruned positions.** If the gadget votes on the positions
pruned by depth `d` and the run is settled, the pruned positions have slot common prefix with
parameter `0` for every horizon. -/
theorem slotCommonPrefix_pruned (h : Run c G) (hL : LiveHyp c σ (posTT c G))
    (hcut : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round))
    (hz : ℕ) :
    (prunedTrace c.slot d (posTT c G)).SlotCommonPrefix (liveNow (posTT c G) d hz) c.slot 0 hz := by
  intro p q j j' s hp hq hjj hj' hs
  rw [liveNow_of_le _ d (hjj.trans hj')] at hs
  have hr := h.rounds j j' hjj
  have e1 : ((prunedTrace c.slot d (posTT c G)).chain j p).filter
        (fun b => decide (c.slot b ≤ s)) =
      (((posTT c G).st j).pos p).filter (fun b => decide (c.slot b ≤ s)) := by
    simp only [prunedTrace, List.filter_filter]
    refine List.filter_congr fun b _ => ?_
    simp only [← Bool.decide_and, decide_eq_decide]
    exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  have e2 : ((prunedTrace c.slot d (posTT c G)).chain j' q).filter
        (fun b => decide (c.slot b ≤ s)) =
      (((posTT c G).st j').pos q).filter (fun b => decide (c.slot b ≤ s)) := by
    simp only [prunedTrace, List.filter_filter]
    refine List.filter_congr fun b _ => ?_
    simp only [← Bool.decide_and, decide_eq_decide]
    exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  rw [e1]
  refine List.IsSuffix.trans ?_
    (filter_slot_suffix ((hL.decreasing q j' hq).filter _) s)
  change _ <:+ List.filter (fun b => decide (c.slot b ≤ s))
    ((prunedTrace c.slot d (posTT c G)).chain j' q)
  rw [e2]
  by_cases hd : d ≤ ((posTT c G).st j).round
  · have hset := h.settled p q j j' hp hq hjj
    rw [hcut] at hset
    have := hset.filter (fun b => decide (c.slot b ≤ s))
    rw [List.filter_filter] at this
    rwa [List.filter_congr fun b _ => ?_] at this
    simp only [← Bool.decide_and, decide_eq_decide]
    exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  · obtain rfl : s = 0 := by omega
    rw [filter_slot_zero (hL.decreasing p j hp) (hL.genesis_mem p j hp) hL.genesis_slot,
      filter_slot_zero (hL.decreasing q j' hq) (hL.genesis_mem q j' hq) hL.genesis_slot]

/-- **Finality liveness of the FFG gadget.** Let the adversarial validators hold less than a
third of the stake, `1 ≤ E`, `1 ≤ Δ`, let the positions of the run `G` satisfy `LiveHyp` with
window `σ`, and let the gadget vote on the positions pruned by depth `d`. Let `v₀ ∈ H` and
suppose that, for every round `r` of the honest schedule that the run reaches, the votes cast
by the first time of round `2 E + σ + d + r (2 E)` contain the votes `roundVotes` of round
`r`, from the empty history and the genesis checkpoint, with the epoch-boundary blocks read off
the pruned position of `v₀` at the first times of the rounds. Then from round `2 E + σ + d + Δ`
on every honest party has a final block at most `3 E + 2 σ + d + Δ - 1` rounds behind the
current round. -/
theorem Run.updatedWithin_of_schedule (h : Run c G)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) (hE : 1 ≤ c.E) (hΔ : 1 ≤ c.Δ)
    (hL : LiveHyp c σ (posTT c G))
    (hcut : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round))
    {v₀ : Party} (hv₀ : v₀ ∈ c.H)
    (hcast : ∀ r t, 2 * c.E + σ + d + r * (2 * c.E) ≤ ((posTT c G).st t).round →
      roundVotes c.H (roundExt c.T (prunedTrace c.slot d (posTT c G)) c.slot c.E v₀
          fun r' => roundTime (posTT c G) (2 * c.E + σ + d + r' * (2 * c.E)))
          ∅ (genesisCheckpoint c.T) r ⊆
        (G (roundTime (posTT c G) (2 * c.E + σ + d + r * (2 * c.E)))).votes) :
    (finTT c G).UpdatedWithin c.slot (2 * c.E + σ + d + c.Δ) (3 * c.E + 2 * σ + d + c.Δ - 1) := by
  intro p t hp hτ
  change 2 * c.E + σ + d + c.Δ ≤ (G t).view.round at hτ
  have hW : 0 < totalStake c.w := by omega
  have hτ₀ : 0 < 2 * c.E + σ := by omega
  set X := posTT c G with hX
  let Xp := prunedTrace c.slot d X
  let now := liveNow X d t
  let ρ := liveRho X d t (2 * c.E + σ) c.E
  let cast : ℕ → Finset (Vote Party Blk) := fun j => (G (min j t)).votes
  let seen : ℕ → Party → Finset (Vote Party Blk) :=
    fun j q => if j ≤ t then (G j).seen q else (G t).votes
  have hdecP : ∀ j q, X.honest q → (Xp.chain j q).Pairwise fun b b' => c.slot b' < c.slot b :=
    fun j q hq => (hL.decreasing q j hq).filter _
  have hgenP : ∀ j q, X.honest q → c.T.genesis ∈ Xp.chain j q := fun j q hq =>
    List.mem_filter.2 ⟨hL.genesis_mem q j hq, by simp [hL.genesis_slot]⟩
  have hchain : SlotChainHyp c.T Xp now c.slot 0 σ t :=
    { now_mono := liveNow_mono h.rounds d t
      inTree := fun j q hq _ => (hL.inTree q j hq).filter _
      decreasing := fun j q hq _ => hdecP j q hq
      genesis_mem := fun j q hq _ => hgenP j q hq
      genesis_slot := hL.genesis_slot
      commonPrefix := slotCommonPrefix_pruned h hL hcut t
      growth := by
        intro q j a hq hj ha
        change a + σ ≤ liveNow X d t j at ha
        rw [liveNow_of_le X d hj] at ha
        obtain ⟨b, hb, h1, h2⟩ := hL.growth q j a hq (by omega)
        exact ⟨b, List.mem_filter.2 ⟨hb, by simp only [decide_eq_true_eq]; omega⟩, h1, h2⟩ }
  have hEp : livenessEpoch (∅ : Finset (Vote Party Blk)) (genesisCheckpoint c.T) = 1 := by
    simp [livenessEpoch, genesisCheckpoint]
  have hU : UpdatedHyp c.T c.w Xp now c.slot c.E σ 0 c.Δ 0 t c.H v₀ ∅ (genesisCheckpoint c.T)
      (2 * c.E + σ) ρ cast seen :=
    { epoch_pos := hE
      delay_pos := hΔ
      honest := fun v hv => hv
      mem_v₀ := hv₀
      quorum := by
        have := Finset.sum_sdiff (Finset.subset_univ c.H) (f := c.w)
        unfold totalStake stake at hA ⊢
        omega
      pre_justified := Justified.genesis
      pre_sources := by simp
      pre_unslashable := by
        ext v
        simp [mem_slashable, DoubleVote, SurroundVote]
      pre_onChain := fun _ v hv =>
        isCheckpointOf_genesis (hdecP _ v hv) (hgenP _ v hv) hL.genesis_slot c.E
      pre_cast := by simp
      start := by rw [hEp]; omega
      gst := Nat.zero_le _
      round_slot := fun r => liveNow_liveRho hL.round_step hL.round_zero d t hτ₀ c.E r
      round_cast := by
        intro r hr
        have hρ := liveRho_eq_roundTime X hτ₀ (d := d) (E := c.E) hr
        have hspec := liveRho_spec X d t (2 * c.E + σ) c.E r
        rw [liveNow_of_le X d hr] at hspec
        rw [roundVotes_congr (D' := roundExt c.T Xp c.slot c.E v₀
          fun r' => roundTime X (2 * c.E + σ + d + r' * (2 * c.E))) fun r' hr' => by
            unfold roundExt
            rw [show ρ r' = roundTime X (2 * c.E + σ + d + r' * (2 * c.E)) from
              liveRho_eq_roundTime X hτ₀ ((liveRho_mono X d t _ c.E hr').trans hr)]]
        change _ ⊆ (G (min (ρ r) t)).votes
        rw [min_eq_left hr]
        change _ ⊆ (G (liveRho X d t (2 * c.E + σ) c.E r)).votes
        rw [hρ]
        exact hcast r (ρ r) (by omega)
      sync := by
        intro q j t' x hq hjt hx hnow
        change max (liveNow X d t j) 0 + c.Δ ≤ liveNow X d t t' at hnow
        change x ∈ (if t' ≤ t then (G t').seen q else (G t).votes)
        split_ifs with ht'
        · have hj : j ≤ t := hjt.trans ht'
          change x ∈ (G (min j t)).votes at hx
          rw [min_eq_left hj] at hx
          rw [liveNow_of_le X d hj, liveNow_of_le X d ht'] at hnow
          change max ((G j).view.round - d) 0 + c.Δ ≤ (G t').view.round - d at hnow
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
          have hyr := h.cast_round j y hy
          exact h.overdue_seen t' y (h.cast_mono hjt hy) (by omega) q
        · exact h.votes_mono (min_le_right _ _) hx
      chain := hchain }
  have hτ' : 2 * c.E + σ + c.Δ ≤ now t := by
    change _ ≤ liveNow X d t t
    rw [liveNow_of_le X d le_rfl]
    change _ ≤ (G t).view.round - d
    omega
  obtain ⟨⟨b, e⟩, hfin, hck, hlag⟩ :=
    finality_updated_start hU (by rw [hEp]; ring) hp le_rfl hτ'
  change (Xp.chain t p).find? (fun x => decide (c.slot x ≤ e * c.E)) = some b at hck
  change Finalized c.T c.w (if t ≤ t then (G t).seen p else (G t).votes) ⟨b, e⟩ at hfin
  rw [if_pos le_rfl] at hfin
  have hfinV := Finalized.mono (h.seen_subset t p) hfin
  have hmem : b ∈ finList c ((G t).seen p) := mem_finList hW hfin fun b' hb' =>
    h.finalized_unique hA hfinV (Finalized.mono (h.seen_subset t p) hb')
  refine ⟨b, hmem, ?_⟩
  change liveNow X d t t ≤ e * c.E + (3 * c.E + σ + 0 + c.Δ) at hlag
  rw [liveNow_of_le X d le_rfl] at hlag
  change (G t).view.round - d ≤ e * c.E + (3 * c.E + σ + 0 + c.Δ) at hlag
  have key : min (e * c.E) ((G t).view.round - d) < c.slot b + σ := by
    by_cases hm : σ ≤ min (e * c.E) ((G t).view.round - d)
    · obtain ⟨b', hb', h1, h2⟩ := hchain.growth p t (min (e * c.E) ((G t).view.round - d) - σ)
        hp le_rfl (by
          change _ ≤ liveNow X d t t
          rw [liveNow_of_le X d le_rfl]
          change _ ≤ (G t).view.round - d
          omega)
      have := slot_le_of_find? (hdecP t p hp) hck hb' (by omega)
      omega
    · omega
  change (G t).view.round ≤ c.slot b + (3 * c.E + 2 * σ + d + c.Δ - 1)
  omega

end Live

end CatCryptCore.Consensus.UC.FFGGadget

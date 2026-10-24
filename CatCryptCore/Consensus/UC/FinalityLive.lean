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
* `Run.updatedHyp`: the hypotheses `Finality.UpdatedHyp` on the pruned positions of a run.
* `Run.updatedWithin_of_schedule`: finality liveness, `UpdatedWithin` on `finTT`, for a run
  whose cast votes contain the votes of the schedule.
* `Run.sched_inv`: the gadget performs round `r` of the schedule at the first time of round
  `c.start + r (2 E)`, with the descendant functions `gadgetExt`.
* `Run.updatedWithin` (headline): finality liveness of every run of the gadget, which casts
  the schedule itself, with `c.start = 2 E + σ + d` and `c.v₀ ∈ H`.
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
  rw [dite_eq_left hex]
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
`TreeTrace.LiveTrace` for the block tree and the slots of the gadget. -/
abbrev LiveHyp (c : Cfg Party Blk) (σ : ℕ) (X : TreeTrace Party Blk) : Prop :=
  X.LiveTrace c.T c.slot σ

omit [Fintype Party] [DecidableEq Party] [DecidableEq Blk] in
/-- `TreeTrace.LiveTrace` reads only rounds and positions. -/
theorem posOnly_liveTrace (T : BlockTree Blk) (sl : Blk → ℕ) (σ : ℕ) :
    PosOnly (Party := Party) (fun X => X.LiveTrace T sl σ) := fun _ _ h =>
  { growth := h.growth
    decreasing := h.decreasing
    genesis_mem := h.genesis_mem
    genesis_slot := h.genesis_slot
    inTree := h.inTree
    round_zero := h.round_zero
    round_step := h.round_step }

omit [Fintype Party] [DecidableEq Party] [DecidableEq Blk] in
/-- The liveness hypotheses read only rounds and positions. -/
theorem posOnly_liveHyp (c : Cfg Party Blk) (σ : ℕ) : PosOnly (LiveHyp c σ) :=
  posOnly_liveTrace c.T c.slot σ

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

/-- The hypotheses of Δ-updatedness (`Finality.UpdatedHyp`) for the pruned positions of a run
up to the horizon `t`, for every vote record `cast`, `seen` in which the votes of each round
of the schedule are cast at its phase (`hrc`) and delivered within `Δ` (`hsync`). -/
theorem Run.updatedHyp (h : Run c G)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) (hE : 1 ≤ c.E) (hΔ : 1 ≤ c.Δ)
    (hL : LiveHyp c σ (posTT c G))
    (hcut : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round))
    {v₀ : Party} (hv₀ : v₀ ∈ c.H) (t : ℕ)
    {cast : ℕ → Finset (Vote Party Blk)} {seen : ℕ → Party → Finset (Vote Party Blk)}
    (hrc : ∀ r, liveRho (posTT c G) d t (2 * c.E + σ) c.E r ≤ t →
      roundVotes c.H (roundExt c.T (prunedTrace c.slot d (posTT c G)) c.slot c.E v₀
          (liveRho (posTT c G) d t (2 * c.E + σ) c.E)) ∅ (genesisCheckpoint c.T) r ⊆
        cast (liveRho (posTT c G) d t (2 * c.E + σ) c.E r))
    (hsync : ∀ p j t' x, (prunedTrace c.slot d (posTT c G)).honest p → j ≤ t' → x ∈ cast j →
      max (liveNow (posTT c G) d t j) 0 + c.Δ ≤ liveNow (posTT c G) d t t' → x ∈ seen t' p) :
    UpdatedHyp c.T c.w (prunedTrace c.slot d (posTT c G)) (liveNow (posTT c G) d t) c.slot c.E
      σ 0 c.Δ 0 t c.H v₀ ∅ (genesisCheckpoint c.T) (2 * c.E + σ)
      (liveRho (posTT c G) d t (2 * c.E + σ) c.E) cast seen := by
  have hτ₀ : 0 < 2 * c.E + σ := by omega
  set X := posTT c G with hX
  let Xp := prunedTrace c.slot d X
  let now := liveNow X d t
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
  exact
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
      round_cast := hrc
      sync := hsync
      chain := hchain }

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
  have hEp : livenessEpoch (∅ : Finset (Vote Party Blk)) (genesisCheckpoint c.T) = 1 := by
    simp [livenessEpoch, genesisCheckpoint]
  have hU : UpdatedHyp c.T c.w Xp now c.slot c.E σ 0 c.Δ 0 t c.H v₀ ∅ (genesisCheckpoint c.T)
      (2 * c.E + σ) ρ cast seen := by
    refine h.updatedHyp hA hE hΔ hL hcut hv₀ t ?_ ?_
    · intro r hr
      rw [← hX] at hr ⊢
      have hρ := liveRho_eq_roundTime X hτ₀ (d := d) (E := c.E) hr
      have hspec := liveRho_spec X d t (2 * c.E + σ) c.E r
      rw [liveNow_of_le X d hr] at hspec
      rw [roundVotes_congr (D' := roundExt c.T Xp c.slot c.E v₀
        fun r' => roundTime X (2 * c.E + σ + d + r' * (2 * c.E))) fun r' hr' => by
          unfold roundExt
          rw [liveRho_eq_roundTime X hτ₀ ((liveRho_mono X d t _ c.E hr').trans hr)]]
      change _ ⊆ (G (min (liveRho X d t (2 * c.E + σ) c.E r) t)).votes
      rw [min_eq_left hr, hρ]
      exact hcast r (liveRho X d t (2 * c.E + σ) c.E r) (by omega)
    · intro q j t' x hq hjt hx hnow
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
  have hchain := hU.chain
  have hτ' : 2 * c.E + σ + c.Δ ≤ now t := by
    change _ ≤ liveNow X d t t
    rw [liveNow_of_le X d le_rfl]
    change _ ≤ (G t).view.round - d
    omega
  obtain ⟨⟨b, e⟩, hfin, hck, hlag⟩ :=
    finality_updated_start hU (by rw [hEp]; ring) hp le_rfl hτ'
  change (Xp.chain t p).find? (fun x => decide (c.slot x ≤ e * c.E)) = some b at hck
  change Finalized c.T c.w (if t ≤ t then (G t).seen p else (G t).votes) ⟨b, e⟩ at hfin
  rw [ite_eq_left le_rfl] at hfin
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

/-! ## The schedule of the gadget -/

section Schedule

variable {Party Blk : Type} [Fintype Party] [DecidableEq Party] [DecidableEq Blk]

omit [Fintype Party] in
/-- The votes of the schedule only grow with the number of rounds. -/
theorem schedule_fst_mono {H : Finset Party} {D : ℕ → Blk → ℕ → Blk}
    {pre : Finset (Vote Party Blk)} {j₀ : Checkpoint Blk} {r r' : ℕ} (hr : r ≤ r') :
    (schedule H D pre j₀ r).1 ⊆ (schedule H D pre j₀ r').1 := by
  induction r', hr using Nat.le_induction with
  | base => exact subset_rfl
  | succ r' _ ih => rw [schedule_succ]; exact ih.trans Finset.subset_union_left

omit [Fintype Party] in
theorem roundVotes_subset_schedule {H : Finset Party} {D : ℕ → Blk → ℕ → Blk}
    {pre : Finset (Vote Party Blk)} {j₀ : Checkpoint Blk} {r r' : ℕ} (hr : r < r') :
    roundVotes H D pre j₀ r ⊆ (schedule H D pre j₀ r').1 := by
  refine (?_ : _ ⊆ (schedule H D pre j₀ (r + 1)).1).trans (schedule_fst_mono hr)
  rw [schedule_succ]
  exact Finset.subset_union_right

omit [Fintype Party] [DecidableEq Party] [DecidableEq Blk] in
/-- If the round starts at `0` and advances by at most `1` per step, the clock `liveNow` is at
most the time. -/
theorem liveNow_le {X : TreeTrace Party Blk} (hs : X.RoundStep) (h0 : (X.st 0).round = 0)
    (d hz j : ℕ) : liveNow X d hz j ≤ j := by
  induction j with
  | zero => simp [liveNow, h0]
  | succ j ih => have := liveNow_succ hs d hz j; omega

omit [Fintype Party] [DecidableEq Party] [DecidableEq Blk] in
/-- The first time of round `R` is `t` if the round at `t` is at least `R` and below `R` at
every earlier time. -/
theorem roundTime_eq {X : TreeTrace Party Blk} {R t : ℕ} (hle : R ≤ (X.st t).round)
    (hlt : ∀ t' < t, (X.st t').round < R) : roundTime X R = t := by
  classical
  have hex : ∃ t, R ≤ (X.st t).round := ⟨t, hle⟩
  unfold roundTime
  rw [dite_eq_left hex]
  refine le_antisymm (Nat.find_min' hex hle) ?_
  by_contra hc
  have := hlt _ (not_le.1 hc)
  have := Nat.find_spec hex
  omega

variable {c : Cfg Party Blk} {G : ℕ → GCore Party Blk} {σ d : ℕ}

/-- The descendant functions of the schedule cast by the gadget: in round `r`, the
epoch-boundary blocks of the pruned position of `c.v₀` at the first time of round
`c.start + r (2 E)`. -/
noncomputable def gadgetExt (c : Cfg Party Blk) (d : ℕ) (G : ℕ → GCore Party Blk) :
    ℕ → Blk → ℕ → Blk :=
  roundExt c.T (prunedTrace c.slot d (posTT c G)) c.slot c.E c.v₀
    fun r => roundTime (posTT c G) (c.start + r * (2 * c.E))

omit [Fintype Party] [DecidableEq Party] [DecidableEq Blk] in
/-- On views of round at least `d`, the pruned positions of the gadget are those of
`prunedTrace`. -/
theorem cut_eq_prunedTrace
    (hcut : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round))
    {t : ℕ} (hd : d ≤ (G t).view.round) (p : Party) :
    c.cut (G t).view p = (prunedTrace c.slot d (posTT c G)).chain t p := by
  rw [hcut]
  refine List.filter_congr fun b _ => ?_
  change decide (c.slot b + d ≤ (G t).view.round) = decide (c.slot b ≤ (G t).view.round - d)
  simp only [decide_eq_decide]
  omega

/-- **The gadget follows the schedule.** If the round starts at `0` and advances by at most `1`
per step, `1 ≤ E`, `d ≤ c.start` and `1 ≤ c.start`, then at every time `t` the gadget has
performed exactly the rounds `r` with `c.start + r (2 E)` at most the current round, and its
schedule state is `Finality.schedule` after these rounds with the descendant functions
`gadgetExt`. -/
theorem Run.sched_inv (h : Run c G) (hs : (posTT c G).RoundStep)
    (h0 : ((posTT c G).st 0).round = 0) (hE : 1 ≤ c.E) (hd : d ≤ c.start) (h1 : 1 ≤ c.start)
    (hcut : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round))
    (t : ℕ) :
    (∀ r, r < (G t).nr ↔ c.start + r * (2 * c.E) ≤ (G t).view.round) ∧
      (G t).sch = schedule c.H (gadgetExt c d G) ∅ (genesisCheckpoint c.T) (G t).nr := by
  have hmul : ∀ {r r' : ℕ}, r < r' → r * (2 * c.E) + 2 ≤ r' * (2 * c.E) := fun {r r'} hr => by
    have := Nat.mul_le_mul_right (2 * c.E) (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul] at this
    omega
  induction t with
  | zero =>
    refine ⟨fun r => ?_, by rw [h.init_sch, h.init_nr]; rfl⟩
    rw [h.init_nr]
    change r < 0 ↔ _ ≤ ((posTT c G).st 0).round
    rw [h0]
    omega
  | succ t ih =>
    obtain ⟨ihn, ihs⟩ := ih
    have hst := hs t
    change (G (t + 1)).view.round ≤ (G t).view.round + 1 at hst
    have hmono := h.round_succ t
    rcases h.step t with e | ⟨a, v, e⟩
    · rw [e]; exact ⟨ihn, ihs⟩
    · have hv : (G (t + 1)).view = v := by rw [e, gstep_view]
      rw [hv] at hst hmono
      rw [e, gstep_nr, gstep_sch, gstep_view]
      have hnot : ¬ c.start + (G t).nr * (2 * c.E) ≤ (G t).view.round := fun hc =>
        lt_irrefl _ ((ihn _).2 hc)
      rcases (hround_spec c { G t with view := v }).2.2 with ⟨-, hn, hsch, hlt⟩ |
          ⟨hle, -, hn, hsch⟩
      · dsimp only at hn hsch hlt
        rw [hn, hsch]
        refine ⟨fun r => ⟨fun hr => ((ihn r).1 hr).trans hmono, fun hr => ?_⟩, ihs⟩
        by_contra hc
        rcases Nat.lt_or_ge (G t).nr r with hlt' | hge
        · have := hmul hlt'; omega
        · have : r = (G t).nr := by omega
          subst this; omega
      · dsimp only at hn hsch hle
        rw [hn, hsch]
        refine ⟨fun r => ⟨fun hr => ?_, fun hr => ?_⟩, ?_⟩
        · rcases Nat.lt_or_ge r (G t).nr with hlt' | hge
          · exact ((ihn r).1 hlt').trans hmono
          · have : r = (G t).nr := by omega
            subst this; exact hle
        · by_contra hc
          have := hmul (show (G t).nr < r by omega)
          omega
        · -- the honest round is round `nr` of the schedule
          have hT : roundTime (posTT c G) (c.start + (G t).nr * (2 * c.E)) = t + 1 := by
            refine roundTime_eq (by change _ ≤ (G (t + 1)).view.round; rw [hv]; exact hle)
              fun t' ht' => ?_
            have := h.rounds t' t (by omega)
            change (G t').view.round ≤ (G t).view.round at this
            change (G t').view.round < _
            omega
          have hext : schedExt c v = gadgetExt c d G (G t).nr := by
            unfold schedExt gadgetExt roundExt
            dsimp only
            rw [hT, ← hv, cut_eq_prunedTrace hcut (by rw [hv]; omega)]
          rw [schedule_succ, ← ihs]
          change ((G t).sch.1 ∪ livenessVotes c.H (schedExt c v) (G t).sch.1 (G t).sch.2,
              livenessTarget (schedExt c v) (G t).sch.1 (G t).sch.2) = _
          rw [hext, roundVotes, ← ihs]

/-- **Finality liveness of the FFG gadget, with the schedule cast by the gadget.** Let the
adversarial validators hold less than a third of the stake, `1 ≤ E`, `1 ≤ Δ`, let the positions
of the run `G` satisfy `LiveHyp` with window `σ`, let the gadget vote on the positions pruned
by depth `d`, let the validator of the schedule satisfy `c.v₀ ∈ H`, and let the schedule start
at round `c.start = 2 E + σ + d`. Then from round `2 E + σ + d + Δ` on every honest party has a
final block at most `3 E + 2 σ + d + Δ - 1` rounds behind the current round. The hypothesis
`hcast` of `Run.updatedWithin_of_schedule` holds since every vote of round `r` of the schedule
satisfies the honest voting rule at the first time of round `c.start + r (2 E)`: its
checkpoints are settled epoch boundaries (`UpdatedHyp.onChain`, `boundary_settled`) and the
schedule makes no honest validator slashable (`schedule_spec`). -/
theorem Run.updatedWithin (h : Run c G)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) (hE : 1 ≤ c.E) (hΔ : 1 ≤ c.Δ)
    (hL : LiveHyp c σ (posTT c G))
    (hcut : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round))
    (hv₀ : c.v₀ ∈ c.H) (hstart : c.start = 2 * c.E + σ + d) :
    (finTT c G).UpdatedWithin c.slot (2 * c.E + σ + d + c.Δ) (3 * c.E + 2 * σ + d + c.Δ - 1) := by
  have hd : d ≤ c.start := by omega
  have h1 : 1 ≤ c.start := by omega
  have hτ₀ : 0 < 2 * c.E + σ := by omega
  have hmul : ∀ {r r' : ℕ}, r < r' → r * (2 * c.E) + 2 ≤ r' * (2 * c.E) := fun {r r'} hr => by
    have := Nat.mul_le_mul_right (2 * c.E) (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul] at this
    omega
  have hquorum : 2 * totalStake c.w ≤ 3 * stake c.w c.H := by
    have := Finset.sum_sdiff (Finset.subset_univ c.H) (f := c.w)
    unfold totalStake stake at hA ⊢
    omega
  have hunsl : slashable (∅ : Finset (Vote Party Blk)) ∩ c.H = ∅ := by
    ext v
    simp [mem_slashable, DoubleVote, SurroundVote]
  have hinv := h.sched_inv hL.round_step hL.round_zero hE hd h1 hcut
  refine h.updatedWithin_of_schedule hA hE hΔ hL hcut hv₀ fun r t ht => ?_
  rw [← hstart] at ht ⊢
  change roundVotes c.H (gadgetExt c d G) ∅ (genesisCheckpoint c.T) r ⊆ _
  obtain ⟨T, hTdef⟩ : ∃ T, T = roundTime (posTT c G) (c.start + r * (2 * c.E)) := ⟨_, rfl⟩
  rw [← hTdef]
  have hex : ∃ t, c.start + r * (2 * c.E) ≤ ((posTT c G).st t).round := ⟨t, ht⟩
  have hTle : c.start + r * (2 * c.E) ≤ (G T).view.round := by
    rw [hTdef]; unfold roundTime; rw [dite_eq_left hex]; exact Nat.find_spec hex
  have hTmin : ∀ t' < T, (G t').view.round < c.start + r * (2 * c.E) := by
    intro t' ht'
    rw [hTdef] at ht'; unfold roundTime at ht'; rw [dite_eq_left hex] at ht'
    exact not_le.1 (Nat.find_min hex ht')
  have hT0' : T ≠ 0 := by
    intro h0
    rw [h0] at hTle
    have := hL.round_zero
    change (G 0).view.round = 0 at this
    omega
  obtain ⟨t₀, hT0⟩ : ∃ t₀, T = t₀ + 1 := ⟨T - 1, by omega⟩
  have hlt₀ := hTmin t₀ (by omega)
  rw [hT0] at hTle
  obtain ⟨ihn, ihs⟩ := hinv t₀
  have hnot : ¬ c.start + (G t₀).nr * (2 * c.E) ≤ (G t₀).view.round := fun hc =>
    lt_irrefl _ ((ihn _).2 hc)
  have hst : (G (t₀ + 1)).view.round ≤ (G t₀).view.round + 1 := hL.round_step t₀
  have hnr : (G t₀).nr = r := by
    refine le_antisymm (by by_contra hc; have := (ihn r).1 (by omega); omega) ?_
    by_contra hc
    have := hmul (show (G t₀).nr < r by omega)
    omega
  rcases h.step t₀ with e | ⟨a, v, e⟩
  · rw [e] at hTle; omega
  have hv : (G (t₀ + 1)).view = v := by rw [e, gstep_view]
  rw [hv] at hTle hst
  rcases (hround_spec c { G t₀ with view := v }).2.2 with ⟨-, -, -, hlt⟩ | ⟨-, hc, -, -⟩
  · dsimp only at hlt; rw [hnr] at hlt; omega
  dsimp only at hc
  have hext : schedExt c v = gadgetExt c d G r := by
    unfold schedExt gadgetExt roundExt
    dsimp only
    rw [← hTdef, hT0, ← hv, cut_eq_prunedTrace hcut (by rw [hv]; omega)]
  have hB : schedVotes c { G t₀ with view := v } =
      roundVotes c.H (gadgetExt c d G) ∅ (genesisCheckpoint c.T) r := by
    unfold schedVotes roundVotes
    dsimp only
    rw [hext, ihs, hnr]
  -- the schedule after `t₀ + 1` steps through `UpdatedHyp`, with the votes of the schedule
  let Xp := prunedTrace c.slot d (posTT c G)
  let ρ := liveRho (posTT c G) d (t₀ + 1) (2 * c.E + σ) c.E
  let D' := roundExt c.T Xp c.slot c.E c.v₀ ρ
  let cast' : ℕ → Finset (Vote Party Blk) := fun j =>
    (schedule c.H D' ∅ (genesisCheckpoint c.T) (j + 1)).1
  have hleρ : ∀ r', r' ≤ ρ r' := fun r' => by
    have h₁ := liveNow_liveRho hL.round_step hL.round_zero d (t₀ + 1) hτ₀ c.E r'
    have h₂ := liveNow_le hL.round_step hL.round_zero d (t₀ + 1) (ρ r')
    have h₃ : r' ≤ r' * (2 * c.E) := Nat.le_mul_of_pos_right r' (by omega)
    change liveNow _ d (t₀ + 1) (ρ r') = _ at h₁
    omega
  have hU' := h.updatedHyp hA hE hΔ hL hcut hv₀ (t₀ + 1) (cast := cast')
    (seen := fun j _ => cast' j)
    (fun r' _ => roundVotes_subset_schedule (Nat.lt_succ_of_le (hleρ r')))
    (fun _ j t' _ _ hjt hx _ => schedule_fst_mono (by omega) hx)
  have hρr : ρ r ≤ t₀ + 1 := by
    refine Nat.find_min' _ ?_
    rw [liveNow_of_le _ d le_rfl]
    change _ ≤ (G (t₀ + 1)).view.round - d
    rw [hv]
    omega
  have hρT : ρ r = t₀ + 1 := by
    change liveRho (posTT c G) d (t₀ + 1) (2 * c.E + σ) c.E r = _
    rw [liveRho_eq_roundTime _ hτ₀ hρr, ← hstart, ← hTdef, hT0]
  have hDD : ∀ r' ≤ r, D' r' = gadgetExt c d G r' := fun r' hr' => by
    change roundExt c.T Xp c.slot c.E c.v₀
      (liveRho (posTT c G) d (t₀ + 1) (2 * c.E + σ) c.E) r' = _
    unfold gadgetExt roundExt
    rw [liveRho_eq_roundTime _ hτ₀ ((liveRho_mono _ d _ _ c.E hr').trans hρr), hstart]
  have hok : ∀ x ∈ roundVotes c.H (gadgetExt c d G) ∅ (genesisCheckpoint c.T) r,
      HonestOK c v ((G t₀).votes ∪ schedVotes c { G t₀ with view := v }) x := by
    intro x hx
    have hxD' : x ∈ roundVotes c.H D' ∅ (genesisCheckpoint c.T) r := by
      rwa [roundVotes_congr hDD]
    obtain ⟨hxH, hst'⟩ := mem_livenessVotes hxD'
    refine ⟨hxH, ?_⟩
    have hon : IsCheckpointOf c.slot c.E (Xp.chain (ρ r) x.validator) x.source ∧
        IsCheckpointOf c.slot c.E (Xp.chain (ρ r) x.validator) x.target := by
      obtain ⟨hT', hN'⟩ := hU'.round_blocks hρr (hU'.onChain r hρr c.v₀ hv₀)
      have hset : ∀ e, e ≤ roundEpoch c.H D' ∅ (genesisCheckpoint c.T) r + 1 →
          epochBoundary c.slot c.E (Xp.chain (ρ r) x.validator) e =
            some (boundaryBlock c.slot c.E c.T.genesis (Xp.chain (ρ r) c.v₀) e) := fun e hle =>
        boundary_settled hU'.chain (hU'.honest _ hv₀) (hU'.honest _ hxH) le_rfl hρr
          (hU'.settled_le r hle)
      rcases hst' with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · rw [hs, ht, hT']
        exact ⟨hU'.onChain r hρr _ hxH, hset _ (Nat.le_succ _)⟩
      · rw [hs, ht, hT', hN']
        exact ⟨hset _ (Nat.le_succ _), hset _ le_rfl⟩
    have hcutT := cut_eq_prunedTrace (G := G) hcut (t := t₀ + 1) (by rw [hv]; omega)
      x.validator
    rw [hv] at hcutT
    rw [hρT, ← hcutT] at hon
    refine ⟨hon.1, hon.2, ?_⟩
    rw [Finset.insert_eq_of_mem (Finset.mem_union_right _ (hB ▸ hx))]
    intro hsl
    have hS := (schedule_spec (T := c.T) (w := c.w) (D := gadgetExt c d G)
      (fun _ b e => anc_extendTo c.T _ b e) hquorum ⟨c.v₀, hv₀⟩ Justified.genesis (by simp)
      hunsl (r + 1)).2.2.1
    have hmem : x.validator ∈
        slashable (schedule c.H (gadgetExt c d G) ∅ (genesisCheckpoint c.T) (r + 1)).1 ∩ c.H := by
      refine Finset.mem_inter.2 ⟨mem_slashable_of_validator (fun y hy hyv => ?_) hsl, hxH⟩
      rcases Finset.mem_union.1 hy with hy | hy
      · have := h.honest_mem_sch t₀ y hy (hyv ▸ hxH)
        rw [ihs, hnr] at this
        exact schedule_fst_mono (Nat.le_succ r) this
      · rw [hB] at hy
        exact roundVotes_subset_schedule (Nat.lt_succ_self r) hy
    rw [hS] at hmem
    simp at hmem
  intro x hx
  have hxB : x ∈ honestCast c { G t₀ with view := v } := by
    classical
    unfold honestCast
    exact Finset.mem_filter.2 ⟨hB ▸ hx, hok x hx⟩
  have hxh : x ∈ (hround c { G t₀ with view := v }).votes := by
    unfold GCore.votes
    rw [hc]
    exact Finset.mem_image.2 ⟨(x, v.round), Finset.mem_union_right _
      (Finset.mem_image_of_mem _ hxB), rfl⟩
  rw [hT0, e]
  rcases gstep_votes c (G t₀) a v with h' | ⟨y, h', -⟩
  · rw [h']; exact hxh
  · rw [h']; exact Finset.mem_insert_of_mem hxh

end Schedule


end CatCryptCore.Consensus.UC.FFGGadget

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.ChainGrowth
public import CatCryptCore.Consensus.PoSNSB.ChainQuality
public import CatCryptCore.Consensus.PoSNSB.CommonPrefix
public import CatCryptCore.Prob.Concentration

/-!
# PoS-NSB: probability of the slot conditions

The theorems `chain_growth_gen`, `chain_quality_gen` and `timed_common_prefix_gen` of the
PoS-NSB port hold for every execution whose lottery satisfies conditions on the numbers of
slots with an honest and with an adversarial leader in intervals of slots. This file bounds
the probability that a random lottery violates these conditions.

## The random lottery

Each slot `0, …, W - 1` is independently of one of three kinds (`SlotKind`): it has an honest
leader, an adversarial leader, or no leader, drawn from a fixed distribution
`ν : PMF SlotKind` with `pH = ν honest` and `pA = ν adversarial`. The slots `W, …, n - 1` and
all later slots are honest (`slotDist`, `kindAt`). The executions considered in
`CatCryptCore/Consensus/PoSNSB/Prob.lean` end before slot `W`, so the later slots only serve
to state the condition of `chain_quality_gen`, which quantifies over all intervals of slots.
A lottery map `lot : SlotKind → Party → Bool` turns the string of kinds into the lottery
`Winner p sl = lot (kindAt κ sl) p` for `sl ≠ 0` (`lotteryParams`); the genesis slot `0` is led
as an honest slot, so that the genesis block can be a correct block for every string. The hypotheses `LotteryHyp` say that
an honest slot has exactly one honest initial leader and that a corrupt party leads only
adversarial slots.

## The slot conditions

For a window of length `d`, the bad events are:
* `CGBad`: some interval `[a, b)` with `a + d ≤ b ≤ n` has fewer than `(pH - ε) (b - a)`
  honest slots;
* `CQBad`: some such interval has fewer than `#adversarial + w` honest slots;
* `CPBad`: some such interval has fewer than `2 #adversarial + 3` honest slots.

## Main results

* `interval_tail`: for a score `s : SlotKind → [0, 1]` with `s honest = 1`, the probability
  that the scores of an interval `[a, b)` sum to at most `(b - a) E[s] - Δ` is at most
  `exp (-2 Δ² / (b - a))`, by Hoeffding's inequality for the `b - a` coordinates of the
  interval (Mathlib's `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`).
* `prob_interval_dev_le`: for deviations `Δ = (b - a) c - r` that grow with the interval, the
  probability that some interval of at least `d` slots deviates is at most
  `(n + 1)² exp (-2 (d c - r)² / d)`; the tail of an interval of `L ≥ d` slots is at most that of
  one of `d` slots (`exp_tail_le`).
* `prob_CGBad_le`, `prob_CQBad_le`, `prob_CPBad_le`: each bad event has probability at most
  `(n + 1)²` times such a tail (union bound over the intervals).
* `prob_slotBad_le`: the union of the three bad events has probability at most `slotBound`.
* `honest_advantage_of_not_CQBad`, `super_of_kind`, `lucky_of_kind`, `adv_of_winner`: the
  slot conditions of the deterministic theorems follow from the complements of the bad events.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters Corruption
open CatCrypt.Prob
open scoped ENNReal

/-! ## Slot kinds and the lottery -/

/-- The kind of a slot: an honest leader, an adversarial leader, or no leader. -/
inductive SlotKind where
  | honest
  | adversarial
  | empty
  deriving DecidableEq

instance : Fintype SlotKind :=
  ⟨{.honest, .adversarial, .empty}, fun x => by cases x <;> simp⟩

/-- The kind of slot `sl` under the string `κ`: `κ sl` for `sl < n`, honest from `n` on. -/
def kindAt {n : ℕ} (κ : Fin n → SlotKind) (sl : ℕ) : SlotKind :=
  if h : sl < n then κ ⟨sl, h⟩ else .honest

theorem kindAt_fin {n : ℕ} (κ : Fin n → SlotKind) (i : Fin n) : kindAt κ i = κ i := by
  simp [kindAt]

/-- The lottery read off a string of slot kinds: party `p` leads slot `sl ≠ 0` when
`lot (kindAt κ sl) p`; the genesis slot `0` is led as an honest slot. -/
abbrev lotteryParams {Party : Type} (IP : List Party) (lot : SlotKind → Party → Bool) {n : ℕ}
    (κ : Fin n → SlotKind) : Parameters Party :=
  ⟨IP, fun p sl => if sl = 0 then lot .honest p else lot (kindAt κ sl) p⟩

/-- Hypotheses on a lottery map: an honest slot has exactly one honest leader among the
initial parties, and a corrupt party leads only adversarial slots. -/
structure LotteryHyp {Party : Type} [Corruption Party] (IP : List Party)
    (lot : SlotKind → Party → Bool) : Prop where
  honest_one : IP.countP (fun p => lot .honest p && is_honest p) = 1
  corrupt_adv : ∀ k p, lot k p = true → is_corrupt p = true → k = .adversarial

/-- The slots of honest kind. -/
def honestKind {n : ℕ} (κ : Fin n → SlotKind) (sl : ℕ) : Bool := decide (kindAt κ sl = .honest)

/-- The slots of adversarial kind. -/
def advKind {n : ℕ} (κ : Fin n → SlotKind) (sl : ℕ) : Bool :=
  decide (kindAt κ sl = .adversarial)

section Lottery

variable {Party : Type} [Corruption Party] [DecidableEq Party] {IP : List Party}
  {lot : SlotKind → Party → Bool}
  {n : ℕ} (κ : Fin n → SlotKind)

/-- A slot of honest kind is a super slot of the lottery `lotteryParams IP lot κ`. -/
theorem super_of_kind (hL : LotteryHyp IP lot) (sl : ℕ) (h : honestKind κ sl = true) :
    letI := lotteryParams IP lot κ
    super_slot (Party := Party) sl = true := by
  simp only [honestKind, decide_eq_true_eq] at h
  simp only [super_slot, Parameters.Winner, Parameters.InitParties, h, ite_self, decide_eq_true_eq]
  exact hL.honest_one

/-- A slot of honest kind has an honest initial leader. -/
theorem lucky_of_kind (hL : LotteryHyp IP lot) (sl : ℕ) (h : honestKind κ sl = true) :
    letI := lotteryParams IP lot κ
    lucky_slot (Party := Party) sl = true :=
  letI := lotteryParams IP lot κ
  super_slot_lucky (super_of_kind κ hL sl h)

/-- A slot led by a corrupt party is of adversarial kind. -/
theorem adv_of_winner (hL : LotteryHyp IP lot) (p : Party) (sl : ℕ)
    (hw : (lotteryParams IP lot κ).Winner p sl = true) (hc : is_corrupt p = true) :
    advKind κ sl = true := by
  simp only [advKind, decide_eq_true_eq]
  simp only [Parameters.Winner] at hw
  split_ifs at hw
  · exact absurd (hL.corrupt_adv _ p hw hc) (by decide)
  · exact hL.corrupt_adv _ p hw hc

end Lottery

/-! ## Counting slots -/

/-- The number of slots of kind `k` in `[a, b)` among the first `n` slots. -/
def cnt {n : ℕ} (κ : Fin n → SlotKind) (k : SlotKind) (a b : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b ∧ κ i = k).card

/-- For `b ≤ n`, the slots of kind `k` in `[a, b)` listed by `p_slots_range` are `cnt κ k a b`
many. -/
theorem p_slots_range_kind {n : ℕ} (κ : Fin n → SlotKind) (k : SlotKind) (a b : ℕ)
    (hb : b ≤ n) :
    (p_slots_range (fun sl => decide (kindAt κ sl = k)) a b).length = cnt κ k a b := by
  induction b with
  | zero => simp [p_slots_range, nat_range, cnt]
  | succ b ih =>
    have ih := ih (by omega)
    have hsplit : cnt κ k a (b + 1) =
        cnt κ k a b + if a ≤ b ∧ kindAt κ b = k then 1 else 0 := by
      simp only [cnt, Finset.card_filter]
      rw [show (if a ≤ b ∧ kindAt κ b = k then 1 else 0) =
          ∑ i : Fin n, if (i : ℕ) = b ∧ a ≤ b ∧ kindAt κ b = k then 1 else 0 by
        rw [Finset.sum_eq_single ⟨b, by omega⟩]
        · simp
        · intro i _ hi
          have : (i : ℕ) ≠ b := fun h => hi (Fin.ext h)
          simp [this]
        · simp]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← kindAt_fin κ i]
      by_cases hib : (i : ℕ) = b
      · rw [hib]; by_cases h1 : a ≤ b <;> by_cases h2 : kindAt κ b = k <;> simp [h1, h2]
      · have : (i : ℕ) < b + 1 ↔ (i : ℕ) < b := by omega
        simp [this, hib]
    rw [hsplit, ← ih]
    by_cases hab : a ≤ b
    · have e : nat_range a (b + 1) = nat_range a b ++ [b] := by
        simp only [nat_range]
        rw [show b + 1 - a = (b - a) + 1 by omega, List.range'_concat]
        congr 2
        omega
      rw [p_slots_range, p_slots_range, e, List.filter_append, List.length_append]
      by_cases h2 : kindAt κ b = k <;> simp [h2, hab]
    · simp [p_slots_range, nat_range, show b + 1 - a = 0 by omega, show b - a = 0 by omega, hab]

/-- The number of slots in `[a, b)` among the first `n`, for `b ≤ n`. -/
theorem card_interval {n : ℕ} (a b : ℕ) (hb : b ≤ n) :
    (Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b).card = b - a := by
  have : (Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b).map Fin.valEmbedding =
      Finset.Ico a b := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, h, rfl⟩; exact h
    · intro h; exact ⟨⟨j, by omega⟩, h, rfl⟩
  rw [← Finset.card_map, this, Nat.card_Ico]

/-! ## Scores -/

/-- The score `α [k = honest] + β [k = adversarial] + γ` of a slot kind. -/
def score (α β γ : ℝ) (k : SlotKind) : ℝ :=
  α * (if k = .honest then 1 else 0) + β * (if k = .adversarial then 1 else 0) + γ

/-- The sum of the scores of the slots in `[a, b)` is `α #honest + β #adversarial + γ (b - a)`. -/
theorem sum_score {n : ℕ} (κ : Fin n → SlotKind) (α β γ : ℝ) (a b : ℕ) (hb : b ≤ n) :
    ∑ i : Fin n, (if a ≤ (i : ℕ) ∧ (i : ℕ) < b then score α β γ (κ i) else 0) =
      α * cnt κ .honest a b + β * cnt κ .adversarial a b + γ * ((b - a : ℕ) : ℝ) := by
  have hpt : ∀ i : Fin n, (if a ≤ (i : ℕ) ∧ (i : ℕ) < b then score α β γ (κ i) else 0) =
      α * (if a ≤ (i : ℕ) ∧ (i : ℕ) < b ∧ κ i = .honest then 1 else 0) +
      β * (if a ≤ (i : ℕ) ∧ (i : ℕ) < b ∧ κ i = .adversarial then 1 else 0) +
      γ * (if a ≤ (i : ℕ) ∧ (i : ℕ) < b then 1 else 0) := by
    intro i
    by_cases h : a ≤ (i : ℕ) ∧ (i : ℕ) < b
    · simp [h, score]
    · have h' : ¬(a ≤ (i : ℕ) ∧ (i : ℕ) < b) := h
      simp only [h', if_false]
      rw [if_neg (fun h'' => h ⟨h''.1, h''.2.1⟩), if_neg (fun h'' => h ⟨h''.1, h''.2.1⟩)]
      ring
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, cnt,
    card_interval a b hb]

/-- The expected score under `ν` is `α pH + β pA + γ`. -/
theorem expect_score (ν : PMF SlotKind) (α β γ : ℝ) :
    expect ν (score α β γ) =
      α * (ν .honest).toReal + β * (ν .adversarial).toReal + γ := by
  have hsum : (ν .honest).toReal + (ν .adversarial).toReal + (ν .empty).toReal = 1 := by
    have h := ν.tsum_coe
    rw [tsum_fintype] at h
    have h2 : (∑ k : SlotKind, ν k) = ν .honest + ν .adversarial + ν .empty := by
      rw [show (Finset.univ : Finset SlotKind) = {.honest, .adversarial, .empty} from rfl]
      simp [add_assoc]
    rw [h2] at h
    have := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_add (by simp [ENNReal.add_eq_top, PMF.apply_ne_top]) (PMF.apply_ne_top _ _),
      ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), ENNReal.toReal_one] at this
  simp only [expect]
  rw [show (Finset.univ : Finset SlotKind) = {.honest, .adversarial, .empty} from rfl]
  simp [score]
  linear_combination γ * hsum

/-! ## The distribution of the lottery -/

/-- An outer measure of a distribution is at most one. -/
theorem toOuterMeasure_le_one {α : Type*} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 :=
  (MeasureTheory.OuterMeasure.mono _ (Set.subset_univ s)).trans
    ((PMF.toOuterMeasure_apply_eq_one_iff p Set.univ).2 fun _ _ => trivial).le

/-- The distribution of slot `i`: `ν` for `i < W`, honest from `W` on. -/
noncomputable def slotDist (ν : PMF SlotKind) (W : ℕ) {n : ℕ} (i : Fin n) : PMF SlotKind :=
  if (i : ℕ) < W then ν else PMF.pure .honest

/-- The distribution of the string of the first `n` slot kinds: independent draws from
`slotDist ν W`. -/
noncomputable def kindDist (ν : PMF SlotKind) (W n : ℕ) : PMF (Fin n → SlotKind) :=
  PMF.piFin (slotDist ν W)

private theorem expect_ite (p : PMF SlotKind) (c : Prop) [Decidable c] (s : SlotKind → ℝ) :
    expect p (fun x => if c then s x else 0) = if c then expect p s else 0 := by
  by_cases h : c <;> simp [h, expect]

private theorem expect_pure (k : SlotKind) (s : SlotKind → ℝ) :
    expect (PMF.pure k) s = s k := by
  simp only [expect, PMF.pure_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- **Tail bound for one interval.** For a score `s` with values in `[0, 1]` and `s honest = 1`,
and an interval `[a, b)` with `b ≤ n`, the probability that the scores of the slots in
`[a, b)` sum to at most `(b - a) E_ν[s] - Δ` is at most `exp (-2 Δ² / (b - a))`.
Proved from Hoeffding's inequality `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` for the
`b - a` coordinates of the interval, each `1/4`-sub-Gaussian by Hoeffding's lemma. -/
theorem interval_tail (ν : PMF SlotKind) (W n : ℕ) (s : SlotKind → ℝ)
    (hs : ∀ k, s k ∈ Set.Icc (0 : ℝ) 1) (hsH : s .honest = 1) {a b : ℕ} (hb : b ≤ n)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    (kindDist ν W n).toOuterMeasure {κ | (∑ i : Fin n,
        (if a ≤ (i : ℕ) ∧ (i : ℕ) < b then s (κ i) else 0)) + Δ ≤
          ((b - a : ℕ) : ℝ) * expect ν s}
      ≤ ENNReal.ofReal (Real.exp (-2 * Δ ^ 2 / ((b - a : ℕ) : ℝ))) := by
  let : MeasurableSpace SlotKind := ⊤
  have : DiscreteMeasurableSpace SlotKind := ⟨fun _ => trivial⟩
  have hμ : expect ν s ≤ 1 := by
    simp only [expect]
    calc ∑ a, (ν a).toReal * s a ≤ ∑ a, (ν a).toReal * 1 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hs k).2 ENNReal.toReal_nonneg
      _ = 1 := by
          simp only [mul_one]
          have h := ν.tsum_coe
          rw [tsum_fintype] at h
          rw [← ENNReal.toReal_sum (fun k _ => PMF.apply_ne_top _ _), h, ENNReal.toReal_one]
  set S : Finset (Fin n) := Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b
  set p := slotDist ν W (n := n)
  set X : Fin n → SlotKind → ℝ := fun i x => expect (p i) s - s x
  have hX : ∀ i, ProbabilityTheory.HasSubgaussianMGF (fun v : Fin n → SlotKind => X i (v i))
      ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2) (PMF.piFin p).toMeasure := fun i => by
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := (PMF.piFin p).toMeasure)
      (X := fun v : Fin n → SlotKind => -s (v i)) (a := -1) (b := 0)
      (measurable_of_countable _).aemeasurable
      (MeasureTheory.ae_of_all _ fun v => ⟨by linarith [(hs (v i)).2], by linarith [(hs (v i)).1]⟩)
    rw [PMF.integral_comp_eval_piFin p (fun x => -s x)] at h
    refine h.congr (MeasureTheory.ae_of_all _ fun v => ?_)
    simp only [X, expect, mul_neg, Finset.sum_neg_distrib]
    ring
  have h := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (PMF.iIndepFun_piFin p X) (s := S) (fun i _ => hX i) hΔ
  have hE : ((b - a : ℕ) : ℝ) * expect ν s ≤ ∑ i ∈ S, expect (p i) s := by
    have h1 : ∀ i ∈ S, expect ν s ≤ expect (p i) s := by
      intro i _
      simp only [p, slotDist]; split_ifs
      · exact le_rfl
      · rw [expect_pure, hsH]; exact hμ
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum h1)
    rw [Finset.sum_const, nsmul_eq_mul, card_interval a b hb]
  have hsum : ∀ κ : Fin n → SlotKind, (∑ i : Fin n,
      (if a ≤ (i : ℕ) ∧ (i : ℕ) < b then s (κ i) else 0)) = ∑ i ∈ S, s (κ i) := fun κ => by
    rw [Finset.sum_filter]
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure, ← MeasureTheory.ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (le_trans (MeasureTheory.measureReal_mono ?_) (h.trans ?_))
  · intro κ hκ
    simp only [Set.mem_ofPred_eq] at hκ ⊢
    rw [hsum] at hκ
    simp only [X, Finset.sum_sub_distrib]
    linarith
  · refine le_of_eq (congrArg Real.exp ?_)
    simp only [Finset.sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast]
    norm_num
    rw [show S.card = b - a from card_interval a b hb]
    ring

/-! ## Union bound over the intervals -/

/-- If each event `B a b` with `a, b ≤ n` has probability at most `c`, the event that some
`B a b` with `a, b ≤ n` occurs has probability at most `(n + 1)² c`. -/
theorem prob_exists_interval_le {n : ℕ} (μ : PMF (Fin n → SlotKind))
    (B : ℕ → ℕ → Set (Fin n → SlotKind)) (c : ℝ≥0∞)
    (h : ∀ a b, a ≤ n → b ≤ n → μ.toOuterMeasure (B a b) ≤ c) :
    μ.toOuterMeasure {κ | ∃ a b, a ≤ n ∧ b ≤ n ∧ κ ∈ B a b} ≤ ((n + 1) ^ 2 : ℕ) * c := by
  have hsub : {κ | ∃ a b, a ≤ n ∧ b ≤ n ∧ κ ∈ B a b} ⊆
      ⋃ a ∈ Finset.range (n + 1), ⋃ b ∈ Finset.range (n + 1), B a b := by
    rintro κ ⟨a, b, ha, hb, hκ⟩
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨a, by omega, b, by omega, hκ⟩
  refine (MeasureTheory.OuterMeasure.mono _ hsub).trans ?_
  refine (MeasureTheory.measure_biUnion_finset_le (μ := μ.toOuterMeasure) _ _).trans ?_
  calc ∑ a ∈ Finset.range (n + 1), μ.toOuterMeasure (⋃ b ∈ Finset.range (n + 1), B a b)
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), μ.toOuterMeasure (B a b) :=
        Finset.sum_le_sum fun a _ =>
          MeasureTheory.measure_biUnion_finset_le (μ := μ.toOuterMeasure) _ _
    _ ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), c := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => h a b ?_ ?_
        · have := Finset.mem_range.1 ha; omega
        · have := Finset.mem_range.1 hb; omega
    _ = ((n + 1) ^ 2 : ℕ) * c := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ## The bad events -/

/-- The probability `ν honest` of an honest slot. -/
noncomputable def pH (ν : PMF SlotKind) : ℝ := (ν .honest).toReal

/-- The probability `ν adversarial` of an adversarial slot. -/
noncomputable def pA (ν : PMF SlotKind) : ℝ := (ν .adversarial).toReal

/-- Chain-growth condition violated: some interval `[a, b)` with `a + d ≤ b ≤ n` has fewer
than `(pH - ε) (b - a)` honest slots. -/
def CGBad (ν : PMF SlotKind) (n d : ℕ) (ε : ℝ) (κ : Fin n → SlotKind) : Prop :=
  ∃ a b, b ≤ n ∧ a + d ≤ b ∧ (cnt κ .honest a b : ℝ) < (pH ν - ε) * ((b - a : ℕ) : ℝ)

/-- Chain-quality condition violated: some interval `[a, b)` with `a + d ≤ b ≤ n` has fewer
honest slots than adversarial slots plus `w`. -/
def CQBad (n d w : ℕ) (κ : Fin n → SlotKind) : Prop :=
  ∃ a b, b ≤ n ∧ a + d ≤ b ∧ cnt κ .honest a b < cnt κ .adversarial a b + w

/-- Common-prefix condition violated: some interval `[a, b)` with `a + d ≤ b ≤ n` has fewer
honest slots than twice its adversarial slots plus `3`. -/
def CPBad (n d : ℕ) (κ : Fin n → SlotKind) : Prop :=
  ∃ a b, b ≤ n ∧ a + d ≤ b ∧ cnt κ .honest a b < 2 * cnt κ .adversarial a b + 3

private theorem score_mem (α β γ : ℝ) (hH : α + γ ∈ Set.Icc (0 : ℝ) 1)
    (hA : β + γ ∈ Set.Icc (0 : ℝ) 1) (hE : γ ∈ Set.Icc (0 : ℝ) 1) (k : SlotKind) :
    score α β γ k ∈ Set.Icc (0 : ℝ) 1 := by
  cases k <;> simpa [score] using ‹_›

/-- The Hoeffding tail of an interval of `L ≥ d` slots is at most that of an interval of `d`
slots, for deviations `L c - r` with `0 ≤ c` and `0 ≤ r ≤ d c`:
`exp (-2 (L c - r)² / L) ≤ exp (-2 (d c - r)² / d)`. -/
theorem exp_tail_le {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) {d L : ℕ} (hrd : r ≤ d * c)
    (hdL : d ≤ L) :
    Real.exp (-2 * ((L : ℝ) * c - r) ^ 2 / L) ≤ Real.exp (-2 * ((d : ℝ) * c - r) ^ 2 / d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero, div_zero, Real.exp_zero, Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ((L : ℝ) * c - r)])
      (Nat.cast_nonneg _)
  · refine Real.exp_le_exp.2 ?_
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hL' : (d : ℝ) ≤ L := by exact_mod_cast hdL
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le hd' hL'
    rw [div_le_div_iff₀ hL0 hd']
    have hy : 0 ≤ (d : ℝ) * c - r := by linarith
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hL') hd'.le) (mul_nonneg hy hc),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hL') hy) hr,
      mul_nonneg (mul_nonneg (sq_nonneg ((L : ℝ) - d)) hd'.le) (sq_nonneg c)]

/-- **Union bound for deviations growing with the interval.** For a score `s` with values in
`[0, 1]` and `s honest = 1`, and `0 ≤ c`, `0 ≤ r ≤ d c`, the probability that some interval
`[a, b)` with `a + d ≤ b ≤ n` has scores summing to at most `(b - a) E_ν[s] - ((b - a) c - r)`
is at most `(n + 1)² exp (-2 (d c - r)² / d)`. -/
theorem prob_interval_dev_le (ν : PMF SlotKind) (W n d : ℕ) (s : SlotKind → ℝ)
    (hs : ∀ k, s k ∈ Set.Icc (0 : ℝ) 1) (hsH : s .honest = 1) {c r : ℝ} (hc : 0 ≤ c)
    (hr : 0 ≤ r) (hrd : r ≤ d * c) :
    (kindDist ν W n).toOuterMeasure {κ | ∃ a b, b ≤ n ∧ a + d ≤ b ∧
        (∑ i : Fin n, (if a ≤ (i : ℕ) ∧ (i : ℕ) < b then s (κ i) else 0)) +
          (((b - a : ℕ) : ℝ) * c - r) ≤ ((b - a : ℕ) : ℝ) * expect ν s} ≤
      ((n + 1) ^ 2 : ℕ) * ENNReal.ofReal (Real.exp (-2 * ((d : ℝ) * c - r) ^ 2 / d)) := by
  refine le_trans (MeasureTheory.OuterMeasure.mono _ ?_) (prob_exists_interval_le _
    (fun a b => {κ | a + d ≤ b ∧
      (∑ i : Fin n, (if a ≤ (i : ℕ) ∧ (i : ℕ) < b then s (κ i) else 0)) +
        (((b - a : ℕ) : ℝ) * c - r) ≤ ((b - a : ℕ) : ℝ) * expect ν s}) _ fun a b _ hb => ?_)
  · rintro κ ⟨a, b, hb, hab, h⟩
    exact ⟨a, b, by omega, hb, hab, h⟩
  · by_cases hab : a + d ≤ b
    · have hdL : d ≤ b - a := by omega
      have hΔ : 0 ≤ ((b - a : ℕ) : ℝ) * c - r := by
        have : (d : ℝ) * c ≤ ((b - a : ℕ) : ℝ) * c :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hdL) hc
        linarith
      exact le_trans (MeasureTheory.OuterMeasure.mono _ fun κ hκ => hκ.2)
        ((interval_tail ν W n s hs hsH hb hΔ).trans
          (ENNReal.ofReal_le_ofReal (exp_tail_le hc hr hrd hdL)))
    · simp [hab]

/-- **Chain-growth condition.** For `ε ≥ 0`, the lottery violates the chain-growth condition
with probability at most `(n + 1)² exp (-2 (ε d)² / d)`. -/
theorem prob_CGBad_le (ν : PMF SlotKind) (W n d : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (kindDist ν W n).toOuterMeasure {κ | CGBad ν n d ε κ} ≤
      ((n + 1) ^ 2 : ℕ) * ENNReal.ofReal (Real.exp (-2 * (ε * d) ^ 2 / d)) := by
  have hs := score_mem 1 0 0 (by norm_num) (by norm_num) (by norm_num)
  rw [show (ε * d) ^ 2 = ((d : ℝ) * ε - 0) ^ 2 by ring]
  refine le_trans (MeasureTheory.OuterMeasure.mono _ ?_) (prob_interval_dev_le ν W n d
    (score 1 0 0) hs (by simp [score]) hε le_rfl (by positivity))
  rintro κ ⟨a, b, hb, hab, hbad⟩
  refine ⟨a, b, hb, hab, ?_⟩
  rw [sum_score κ 1 0 0 a b hb, expect_score]
  simp only [pH] at hbad
  nlinarith

/-- **Chain-quality condition.** If `pA ≤ pH` and `w ≤ d (pH - pA)`, the lottery violates the
chain-quality condition with probability at most
`(n + 1)² exp (-2 ((d (pH - pA) - w) / 2)² / d)`. -/
theorem prob_CQBad_le (ν : PMF SlotKind) (W n d w : ℕ) (hδ : pA ν ≤ pH ν)
    (hw : (w : ℝ) ≤ d * (pH ν - pA ν)) :
    (kindDist ν W n).toOuterMeasure {κ | CQBad n d w κ} ≤
      ((n + 1) ^ 2 : ℕ) * ENNReal.ofReal
        (Real.exp (-2 * ((d * (pH ν - pA ν) - w) / 2) ^ 2 / d)) := by
  have hs := score_mem (1 / 2) (-1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  rw [show ((d * (pH ν - pA ν) - w) / 2) ^ 2 = ((d : ℝ) * ((pH ν - pA ν) / 2) - w / 2) ^ 2 by
    ring]
  refine le_trans (MeasureTheory.OuterMeasure.mono _ ?_) (prob_interval_dev_le ν W n d
    (score (1 / 2) (-1 / 2) (1 / 2)) hs (by simp [score]; norm_num) (by linarith)
    (by positivity) (by linarith))
  rintro κ ⟨a, b, hb, hab, hbad⟩
  refine ⟨a, b, hb, hab, ?_⟩
  rw [sum_score κ _ _ _ a b hb, expect_score]
  have hbad' : (cnt κ .honest a b : ℝ) + 1 ≤ cnt κ .adversarial a b + w := by
    exact_mod_cast hbad
  simp only [pH, pA] at *
  nlinarith

/-- **Common-prefix condition.** If `2 pA ≤ pH` and `3 ≤ d (pH - 2 pA)`, the lottery violates
the common-prefix condition with probability at most
`(n + 1)² exp (-2 ((d (pH - 2 pA) - 3) / 3)² / d)`. -/
theorem prob_CPBad_le (ν : PMF SlotKind) (W n d : ℕ) (hγ : 2 * pA ν ≤ pH ν)
    (h3 : (3 : ℝ) ≤ d * (pH ν - 2 * pA ν)) :
    (kindDist ν W n).toOuterMeasure {κ | CPBad n d κ} ≤
      ((n + 1) ^ 2 : ℕ) * ENNReal.ofReal
        (Real.exp (-2 * ((d * (pH ν - 2 * pA ν) - 3) / 3) ^ 2 / d)) := by
  have hs := score_mem (1 / 3) (-2 / 3) (2 / 3) (by norm_num) (by norm_num) (by norm_num)
  rw [show ((d * (pH ν - 2 * pA ν) - 3) / 3) ^ 2 = ((d : ℝ) * ((pH ν - 2 * pA ν) / 3) - 1) ^ 2 by
    ring]
  refine le_trans (MeasureTheory.OuterMeasure.mono _ ?_) (prob_interval_dev_le ν W n d
    (score (1 / 3) (-2 / 3) (2 / 3)) hs (by simp [score]; norm_num) (by linarith)
    zero_le_one (by linarith))
  rintro κ ⟨a, b, hb, hab, hbad⟩
  refine ⟨a, b, hb, hab, ?_⟩
  rw [sum_score κ _ _ _ a b hb, expect_score]
  have hbad' : (cnt κ .honest a b : ℝ) + 1 ≤ 2 * cnt κ .adversarial a b + 3 := by
    exact_mod_cast hbad
  simp only [pH, pA] at *
  nlinarith

/-- The bound on the probability that the lottery violates one of the three slot
conditions: three Hoeffding tails for intervals of `d` slots, each multiplied by the number
`(n + 1)²` of intervals. -/
noncomputable def slotBound (ν : PMF SlotKind) (n d w : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ((n + 1) ^ 2 : ℕ) * ENNReal.ofReal (Real.exp (-2 * (ε * d) ^ 2 / d)) +
  ((n + 1) ^ 2 : ℕ) * ENNReal.ofReal (Real.exp (-2 * ((d * (pH ν - pA ν) - w) / 2) ^ 2 / d)) +
  ((n + 1) ^ 2 : ℕ) * ENNReal.ofReal (Real.exp (-2 * ((d * (pH ν - 2 * pA ν) - 3) / 3) ^ 2 / d))

/-- The event that the lottery violates one of the slot conditions. -/
def SlotBad (ν : PMF SlotKind) (n d w : ℕ) (ε : ℝ) (κ : Fin n → SlotKind) : Prop :=
  CGBad ν n d ε κ ∨ CQBad n d w κ ∨ CPBad n d κ

/-- **Slot conditions (part 1).** Under `0 ≤ ε`, `2 pA ≤ pH`, `w ≤ d (pH - pA)` and
`3 ≤ d (pH - 2 pA)`, a lottery string of `n` slots, independent with distribution `ν` on the
first `W` slots, violates one of the three slot conditions with probability at most
`slotBound ν n d w ε`. -/
theorem prob_slotBad_le (ν : PMF SlotKind) (W n d w : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hγ : 2 * pA ν ≤ pH ν) (hw : (w : ℝ) ≤ d * (pH ν - pA ν))
    (h3 : (3 : ℝ) ≤ d * (pH ν - 2 * pA ν)) :
    (kindDist ν W n).toOuterMeasure {κ | SlotBad ν n d w ε κ} ≤ slotBound ν n d w ε := by
  have hδ : pA ν ≤ pH ν := by
    have : 0 ≤ pA ν := ENNReal.toReal_nonneg
    linarith
  have e : {κ | SlotBad ν n d w ε κ} =
      ({κ | CGBad ν n d ε κ} ∪ {κ | CQBad n d w κ}) ∪ {κ | CPBad n d κ} := by
    ext κ; simp [SlotBad, or_assoc]
  rw [e]
  refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ (prob_CPBad_le ν W n d hγ h3))
  exact (MeasureTheory.measure_union_le _ _).trans
    (add_le_add (prob_CGBad_le ν W n d hε) (prob_CQBad_le ν W n d w hδ hw))


/-! ## From the complements of the bad events to the slot conditions -/

/-- A range of slots splits at an intermediate slot. -/
theorem p_slots_range_split (P : ℕ → Bool) {a m b : ℕ} (h1 : a ≤ m) (h2 : m ≤ b) :
    (p_slots_range P a b).length = (p_slots_range P a m).length + (p_slots_range P m b).length := by
  have e : nat_range a b = nat_range a m ++ nat_range m b := by
    simp only [nat_range]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h2
    rw [show a + k + l - a = k + l by omega, show a + k - a = k by omega,
      show a + k + l - (a + k) = l by omega, List.range'_append_1]
  rw [p_slots_range, e, List.filter_append, List.length_append]
  rfl

/-- If every slot of `[a, b)` satisfies `P`, the range has `b - a` slots. -/
theorem p_slots_range_all (P : ℕ → Bool) (a b : ℕ) (h : ∀ sl, a ≤ sl → sl < b → P sl = true) :
    (p_slots_range P a b).length = b - a := by
  rw [p_slots_range, List.filter_eq_self.2, nat_range, List.length_range']
  intro sl hsl
  rw [nat_range, List.mem_range'_1] at hsl
  exact h sl hsl.1 (by omega)

/-- If no slot of `[a, b)` satisfies `P`, the range is empty. -/
theorem p_slots_range_none (P : ℕ → Bool) (a b : ℕ) (h : ∀ sl, a ≤ sl → sl < b → P sl = false) :
    (p_slots_range P a b).length = 0 := by
  rw [p_slots_range, List.filter_eq_nil_iff.2, List.length_nil]
  intro sl hsl
  rw [nat_range, List.mem_range'_1] at hsl
  simp [h sl hsl.1 (by omega)]

theorem honest_count {n : ℕ} (κ : Fin n → SlotKind) (a b : ℕ) (hb : b ≤ n) :
    (p_slots_range (honestKind κ) a b).length = cnt κ .honest a b :=
  p_slots_range_kind κ .honest a b hb

theorem adv_count {n : ℕ} (κ : Fin n → SlotKind) (a b : ℕ) (hb : b ≤ n) :
    (p_slots_range (advKind κ) a b).length = cnt κ .adversarial a b :=
  p_slots_range_kind κ .adversarial a b hb

/-- A string that is honest from slot `W` on. -/
def PaddedFrom {n : ℕ} (W : ℕ) (κ : Fin n → SlotKind) : Prop :=
  ∀ i : Fin n, W ≤ (i : ℕ) → κ i = .honest

theorem kindAt_of_padded {n W : ℕ} {κ : Fin n → SlotKind} (hκ : PaddedFrom W κ) (sl : ℕ)
    (h : W ≤ sl) : kindAt κ sl = .honest := by
  unfold kindAt
  split_ifs with h'
  · exact hκ _ h
  · rfl

/-- **Chain-quality condition over all intervals.** If the string is honest from slot `W` on,
`W + d ≤ n`, `1 ≤ d ≤ d'` and `w ≤ d`, and no interval within the first `n` slots violates the
chain-quality condition, then every interval of at least `d'` slots of `ℕ` has `w` more honest
than adversarial slots. -/
theorem honest_advantage_of_not_CQBad {n W d d' w : ℕ} {κ : Fin n → SlotKind}
    (hκ : PaddedFrom W κ) (hWn : W + d ≤ n) (hd : 1 ≤ d) (hdd : d ≤ d') (hwd : w ≤ d)
    (hbad : ¬CQBad n d w κ) :
    honest_advantage_ranges_gt_gen (honestKind κ) (advKind κ) w d' := by
  intro a b hab
  have hab' : a + d ≤ b := by omega
  unfold honest_advantage_range_gen
  have hin : ∀ a' b', b' ≤ n → a' + d ≤ b' →
      cnt κ .adversarial a' b' + w ≤ cnt κ .honest a' b' := by
    intro a' b' hb' hab''
    by_contra hc
    exact hbad ⟨a', b', hb', hab'', by omega⟩
  have hpadH : ∀ m, W ≤ m → (p_slots_range (honestKind κ) m b).length = b - m := fun m hm =>
    p_slots_range_all _ _ _ fun sl h1 _ => by
      simp [honestKind, kindAt_of_padded hκ sl (by omega)]
  have hpadA : ∀ m, W ≤ m → (p_slots_range (advKind κ) m b).length = 0 := fun m hm =>
    p_slots_range_none _ _ _ fun sl h1 _ => by
      simp [advKind, kindAt_of_padded hκ sl (by omega)]
  by_cases hb : b ≤ n
  · rw [honest_count κ a b hb, adv_count κ a b hb]
    exact hin a b hb hab'
  · by_cases han : a + d ≤ n
    · rw [p_slots_range_split _ (by omega : a ≤ n) (by omega : n ≤ b),
        p_slots_range_split (honestKind κ) (by omega : a ≤ n) (by omega : n ≤ b),
        honest_count κ a n le_rfl, adv_count κ a n le_rfl, hpadH n (by omega),
        hpadA n (by omega)]
      have := hin a n le_rfl han
      omega
    · rw [hpadH a (by omega), hpadA a (by omega)]
      omega

end CatCryptCore.Consensus.PoSNSB

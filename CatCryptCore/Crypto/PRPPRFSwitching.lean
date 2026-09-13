/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversary
public import CatCryptCore.Crypto.SwitchingLemma

/-!
# Adaptive PRF and PRP games and the PRP/PRF switching lemma

The adversary is an `OracleAdv D R Bool` asking adaptive queries in `D` and
receiving answers in `R`. The real game samples a key `k` once and answers with
`F k`. The ideal PRF game answers with a lazily sampled random function and the
ideal PRP game with a lazily sampled random injection (sampling without
replacement, a random permutation when `D = R`); both keep the table of answered
queries as oracle state. Each game is an `SPComp Bool` that leaves the heap
unchanged, and the advantages are `Advantage` on these games.

## Main definitions

* `rfOracle`, `rpOracle` — lazily sampled random function and random injection
* `realGame F A`, `rfGame A`, `rpGame A` — the real, PRF-ideal and PRP-ideal games
* `PRF_q_Advantage F A`, `PRP_q_Advantage P A`, `RF_RP_Advantage A` — the
  adaptive PRF, PRP and random-function/random-injection advantages

## Main results

* `RF_RP_Advantage_le` — for an adversary with query bound `q`,
  `RF_RP_Advantage A ≤ q(q-1)/2 / |R|`
* `PRF_q_Advantage_le` — for an adversary with query bound `q`,
  `PRF_q_Advantage P A ≤ PRP_q_Advantage P A + q(q-1)/2 / |R|`
* `PRF_q_Advantage_of_isQueryBound_zero`, `PRP_q_Advantage_of_isQueryBound_zero`,
  `RF_RP_Advantage_of_isQueryBound_zero` — all advantages vanish without queries
* `switching_bound_le_one` — the bound is at most one when `q(q-1) ≤ 2|R|`

## Proof

The random injection is written in resampling form (`rpFlagOracle`): a fresh
query samples a uniform answer and, when the answer repeats a recorded one,
resamples from the unused answers (`uniform_bind_resample`). Both oracles carry
a flag set on such a repetition. The flagged oracles agree on every transition
that leaves the flag cleared, so their runs agree on every outcome with the flag
cleared (`OracleAdv.run_apply_flag_false_eq`). The flag is set with probability
at most `q(q-1)/2 / |R|` (`run_rfFlagOracle_flag_le`). The flagged games write
the final flag to the heap location `flagLoc`, which is the form consumed by
`SwitchingLemma.switching_from_birthday`.
-/

@[expose] public section

namespace CatCrypt.Crypto.PRPPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Unary CatCrypt.Crypto.SwitchingLemma
open scoped ENNReal

variable {D R : Type} [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R]

/-- The answers recorded in a lazy-sampling table. -/
def usedAnswers (t : List (D × R)) : Finset R := (t.map Prod.snd).toFinset

omit [DecidableEq D] [Fintype R] [Nonempty R] in
theorem card_usedAnswers_le (t : List (D × R)) : (usedAnswers t).card ≤ t.length := by
  unfold usedAnswers
  exact (List.toFinset_card_le _).trans (by simp)

/-- Uniform distribution on the complement of `u`, and on all of `R` when the
complement is empty. -/
noncomputable def freshDist (u : Finset R) : PMF R :=
  if h : uᶜ.Nonempty then PMF.uniformOfFinset uᶜ h else PMF.uniformOfFintype R

/-- Sampling uniformly from `R` and resampling from the complement of `u` when
the sample lies in `u` is sampling from `freshDist u`. -/
theorem uniform_bind_resample (u : Finset R) :
    (PMF.uniformOfFintype R).bind (fun r => if r ∈ u then freshDist u else PMF.pure r) =
      freshDist u := by
  by_cases hc : uᶜ.Nonempty
  · ext x
    simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, freshDist, dif_pos hc, tsum_fintype,
      ← Finset.mul_sum, apply_ite (fun p : PMF R => p x), PMF.uniformOfFinset_apply,
      PMF.pure_apply, Finset.mem_compl]
    by_cases hx : x ∈ u
    · rw [if_neg (by simpa using hx), Finset.sum_eq_zero, mul_zero]
      intro i _
      by_cases hi : i ∈ u
      · simp [hi]
      · simp only [hi, if_false]
        rw [if_neg (by rintro rfl; exact hi hx)]
    · have hcu : uᶜ.card + u.card = Fintype.card R := by
        rw [Finset.card_compl]; have := Finset.card_le_univ u; omega
      have hc0 : (uᶜ.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.card_pos.ne'
      have hN0 : (Fintype.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [if_pos (by simpa using hx), Finset.sum_ite]
      simp only [Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [Finset.sum_eq_single_of_mem x, if_pos rfl, nsmul_eq_mul,
        ← ENNReal.mul_inv_cancel hc0 (ENNReal.natCast_ne_top _), ← add_mul, ← Nat.cast_add,
        add_comm u.card, hcu, ← mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top _),
        one_mul]
      · simpa using hx
      · exact fun b _ hb => if_neg (Ne.symm hb)
  · have hall : ∀ r, r ∈ u := by
      intro r; by_contra hr
      exact hc ⟨r, Finset.mem_compl.mpr hr⟩
    simp only [hall, if_true, PMF.bind_const]

/-! ## Lazily sampled oracles -/

/-- Lazily sampled random function with the table as state: a recorded query
returns its recorded answer; a fresh query samples a uniform answer and
records it. -/
noncomputable def rfOracle (t : List (D × R)) (d : D) : PMF (R × List (D × R)) :=
  match List.lookup d t with
  | some r => PMF.pure (r, t)
  | none => (PMF.uniformOfFintype R).map fun r => (r, (d, r) :: t)

/-- Lazily sampled random injection (a random permutation when `D = R`) with
the table as state: a recorded query returns its recorded answer; a fresh query
samples uniformly without replacement from the answers not yet recorded, and
records it. -/
noncomputable def rpOracle (t : List (D × R)) (d : D) : PMF (R × List (D × R)) :=
  match List.lookup d t with
  | some r => PMF.pure (r, t)
  | none => (freshDist (usedAnswers t)).map fun r => (r, (d, r) :: t)

/-- `rfOracle` with a flag, set when a fresh answer repeats a recorded answer. -/
noncomputable def rfFlagOracle (s : List (D × R) × Bool) (d : D) :
    PMF (R × (List (D × R) × Bool)) :=
  match List.lookup d s.1 with
  | some r => PMF.pure (r, s)
  | none => (PMF.uniformOfFintype R).map fun r =>
      (r, ((d, r) :: s.1, s.2 || decide (r ∈ usedAnswers s.1)))

/-- `rpOracle` in resampling form with a flag: a fresh query samples a uniform
answer; when it repeats a recorded answer the flag is set and the answer is
resampled from `freshDist`. -/
noncomputable def rpFlagOracle (s : List (D × R) × Bool) (d : D) :
    PMF (R × (List (D × R) × Bool)) :=
  match List.lookup d s.1 with
  | some r => PMF.pure (r, s)
  | none => (PMF.uniformOfFintype R).bind fun r =>
      if r ∈ usedAnswers s.1 then
        (freshDist (usedAnswers s.1)).map fun r' => (r', ((d, r') :: s.1, true))
      else PMF.pure (r, ((d, r) :: s.1, s.2))

theorem rfFlagOracle_map (s : List (D × R) × Bool) (d : D) :
    (rfFlagOracle s d).map (Prod.map id Prod.fst) = rfOracle s.1 d := by
  unfold rfFlagOracle rfOracle
  cases List.lookup d s.1 with
  | some r => simp [PMF.pure_map]
  | none => simp [PMF.map_comp, Function.comp_def]

theorem rpFlagOracle_map (s : List (D × R) × Bool) (d : D) :
    (rpFlagOracle s d).map (Prod.map id Prod.fst) = rpOracle s.1 d := by
  unfold rpFlagOracle rpOracle
  cases List.lookup d s.1 with
  | some r => simp [PMF.pure_map]
  | none =>
    simp only
    conv_rhs => rw [← uniform_bind_resample]
    rw [PMF.map_bind, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    split_ifs
    · simp [PMF.map_comp, Function.comp_def]
    · simp [PMF.pure_map]

theorem rfFlagOracle_apply_true_false (t : List (D × R)) (d : D) (r : R) (t' : List (D × R)) :
    rfFlagOracle (t, true) d (r, (t', false)) = 0 := by
  unfold rfFlagOracle
  cases List.lookup d t with
  | some r₀ => simp [PMF.pure_apply]
  | none => simp [PMF.map_apply]

theorem rpFlagOracle_apply_true_false (t : List (D × R)) (d : D) (r : R) (t' : List (D × R)) :
    rpFlagOracle (t, true) d (r, (t', false)) = 0 := by
  unfold rpFlagOracle
  cases List.lookup d t with
  | some r₀ => simp [PMF.pure_apply]
  | none =>
    simp only [PMF.bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun r₀ => ?_
    split_ifs <;> simp [PMF.map_apply, PMF.pure_apply]

theorem rfFlagOracle_apply_false_eq (s : List (D × R) × Bool) (d : D) (r : R)
    (t' : List (D × R)) :
    rfFlagOracle s d (r, (t', false)) = rpFlagOracle s d (r, (t', false)) := by
  unfold rfFlagOracle rpFlagOracle
  cases List.lookup d s.1 with
  | some r₀ => rfl
  | none =>
    simp only
    rw [← PMF.bind_pure_comp, PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun r₀ => ?_
    congr 1
    split_ifs with h
    · simp [PMF.map_apply, PMF.pure_apply, h]
    · simp [PMF.pure_apply, h]

/-! ## The collision probability -/

variable {α : Type}

/-- Birthday bound for the flagged random function: from a table with `m`
entries and the flag cleared, an adversary asking at most `n` queries sets the
flag with probability at most `(∑ i < n, (m + i)) / |R|`. -/
theorem run_rfFlagOracle_flag_le (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBound n)
    (t : List (D × R)) :
    (OracleAdv.run rfFlagOracle A (t, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ((∑ i ∈ Finset.range n, (t.length + i) : ℕ) : ℝ≥0∞) / Fintype.card R := by
  induction A generalizing n t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run rfFlagOracle (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b * (((∑ i ∈ Finset.range n, (t.length + i) : ℕ) : ℝ≥0∞) /
            Fintype.card R) :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b n (hA b) t
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n =>
    have hk : ∀ r, (k r).IsQueryBound n := hA
    set N : ℝ≥0∞ := (Fintype.card R : ℝ≥0∞)
    rw [OracleAdv.run_query]
    unfold rfFlagOracle
    cases hlook : List.lookup d t with
    | some r =>
      simp only [PMF.pure_bind]
      refine (ih r n (hk r) t).trans (ENNReal.div_le_div_right (Nat.cast_le.mpr
        (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ n)))) _)
    | none =>
      simp only [PMF.bind_map, Function.comp_def, Bool.false_or]
      rw [PMF.toOuterMeasure_bind_apply, tsum_fintype]
      simp only [PMF.uniformOfFintype_apply]
      set B : ℝ≥0∞ := ((∑ i ∈ Finset.range n, ((t.length + 1) + i) : ℕ) : ℝ≥0∞) / N
      have hterm : ∀ r, (OracleAdv.run rfFlagOracle (k r)
          ((d, r) :: t, decide (r ∈ usedAnswers t))).toOuterMeasure {x | x.2.2 = true} ≤
          (if r ∈ usedAnswers t then 1 else 0) + B := by
        intro r
        by_cases hr : r ∈ usedAnswers t
        · simp only [hr, decide_true, if_true]
          exact ((MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
            ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))).trans le_self_add
        · simp only [hr, decide_false, if_false, zero_add]
          have h := ih r n (hk r) ((d, r) :: t)
          rwa [List.length_cons] at h
      have hN0 : N ≠ 0 := by simp [N, Fintype.card_ne_zero]
      have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
      calc ∑ r, N⁻¹ * (OracleAdv.run rfFlagOracle (k r)
            ((d, r) :: t, decide (r ∈ usedAnswers t))).toOuterMeasure {x | x.2.2 = true}
          ≤ ∑ r, N⁻¹ * ((if r ∈ usedAnswers t then 1 else 0) + B) :=
            Finset.sum_le_sum fun r _ => by gcongr; exact hterm r
        _ = (usedAnswers t).card / N + B := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul, mul_add, ← mul_assoc,
              ENNReal.inv_mul_cancel hN0 hNt, one_mul]
            simp only [ENNReal.div_eq_inv_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
        _ ≤ t.length / N + B := by
            gcongr
            exact_mod_cast card_usedAnswers_le t
        _ = _ := by
            rw [ENNReal.div_add_div_same, Finset.sum_range_succ']
            congr 1
            push_cast
            rw [add_zero, add_comm]
            congr 1
            exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Games -/

/-- The heap-independent game returning a sample of `p` and leaving the heap
unchanged. -/
noncomputable def pmfGame (p : PMF Bool) : SPComp Bool := fun h => p.map fun b => some (b, h)

/-- The keyed oracle `F k` with no state. -/
noncomputable def keyedOracle {K : Type} (F : K → D → R) (k : K) : Unit → D → PMF (R × Unit) :=
  fun _ d => PMF.pure (F k d, ())

variable {K : Type} [Fintype K] [Nonempty K]

/-- Real game: sample a key once, then run `A` against `F k`. -/
noncomputable def realGame (F : K → D → R) (A : OracleAdv D R Bool) : SPComp Bool :=
  pmfGame ((PMF.uniformOfFintype K).bind fun k =>
    (OracleAdv.run (keyedOracle F k) A ()).map Prod.fst)

/-- Ideal PRF game: run `A` against the lazily sampled random function. -/
noncomputable def rfGame (A : OracleAdv D R Bool) : SPComp Bool :=
  pmfGame ((OracleAdv.run rfOracle A []).map Prod.fst)

/-- Ideal PRP game: run `A` against the lazily sampled random injection
(sampling without replacement). -/
noncomputable def rpGame (A : OracleAdv D R Bool) : SPComp Bool :=
  pmfGame ((OracleAdv.run rpOracle A []).map Prod.fst)

/-- Adaptive PRF advantage of `A` against the keyed function `F`. -/
noncomputable def PRF_q_Advantage (F : K → D → R) (A : OracleAdv D R Bool) : ℝ≥0∞ :=
  Advantage (realGame F A) (rfGame A)

/-- Adaptive PRP advantage of `A` against the keyed function `P`. -/
noncomputable def PRP_q_Advantage (P : K → D → R) (A : OracleAdv D R Bool) : ℝ≥0∞ :=
  Advantage (realGame P A) (rpGame A)

/-- Advantage of `A` in distinguishing the lazy random function from the lazy
random injection. -/
noncomputable def RF_RP_Advantage (A : OracleAdv D R Bool) : ℝ≥0∞ :=
  Advantage (rfGame A) (rpGame A)

/-! ## Flagged games -/

/-- The heap location recording the collision flag at the end of a flagged
game. -/
abbrev flagLoc : Location := ⟨0, Bool⟩

/-- Run `A` against a flagged oracle from the empty table and write the final
flag to `flagLoc`. -/
noncomputable def flagGame (O : List (D × R) × Bool → D → PMF (R × (List (D × R) × Bool)))
    (A : OracleAdv D R Bool) : SPComp Bool :=
  fun h => (OracleAdv.run O A ([], false)).map fun x => some (x.1, h.set flagLoc x.2.2)

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R] in
open Classical in
/-- Summing a pushforward along `some ∘ f` over the outcomes satisfying `P` is
the probability of the preimage. -/
theorem tsum_ite_map_some {β γ : Type} (p : PMF β) (f : β → γ) (P : γ → Prop) :
    (∑' y, if P y then (p.map fun x => some (f x)) (some y) else 0) =
      p.toOuterMeasure {x | P (f x)} := by
  classical
  simp only [PMF.map_apply, Option.some.injEq, PMF.toOuterMeasure_apply]
  have h : ∀ y, (if P y then ∑' x, (if y = f x then p x else 0) else 0) =
      ∑' x, (if P y ∧ y = f x then p x else 0) := by
    intro y; split_ifs with hy <;> simp [hy]
  simp only [h]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (f x) (fun y hy => if_neg fun h' => hy h'.2)]
  simp [Set.indicator]

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R] in
theorem prTrue_pmfGame_map {β : Type} (p : PMF β) (g : β → Bool) (h₀ : Heap) :
    prTrue (pmfGame (p.map g)) h₀ = p.toOuterMeasure {x | g x = true} := by
  rw [prTrue_eq_prEventComp]
  unfold prEventComp prEvent pmfGame
  simp only [PMF.map_comp, Function.comp_def]
  convert tsum_ite_map_some p (fun x => (g x, h₀)) (fun y => y.1 = true)

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R] in
theorem prTrue_flagGame (O : List (D × R) × Bool → D → PMF (R × (List (D × R) × Bool)))
    (A : OracleAdv D R Bool) (h₀ : Heap) :
    prTrue (flagGame O A) h₀ = (OracleAdv.run O A ([], false)).toOuterMeasure {x | x.1 = true} := by
  rw [prTrue_eq_prEventComp]
  unfold prEventComp prEvent flagGame
  convert tsum_ite_map_some _ (fun x : Bool × (List (D × R) × Bool) =>
    (x.1, h₀.set flagLoc x.2.2)) (fun y => y.1 = true)

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R] in
theorem prEventComp_flagGame (O : List (D × R) × Bool → D → PMF (R × (List (D × R) × Bool)))
    (A : OracleAdv D R Bool) :
    prEventComp (flagGame O A) Heap.empty (fun _ h' => h'.get flagLoc = true) =
      (OracleAdv.run O A ([], false)).toOuterMeasure {x | x.2.2 = true} := by
  unfold prEventComp prEvent flagGame
  have := tsum_ite_map_some (OracleAdv.run O A ([], false))
    (fun x : Bool × (List (D × R) × Bool) => (x.1, Heap.empty.set flagLoc x.2.2))
    (fun y => y.2.get flagLoc = true)
  simpa using this

theorem rfGame_eq (A : OracleAdv D R Bool) :
    prTrue (rfGame A) Heap.empty = prTrue (flagGame rfFlagOracle A) Heap.empty := by
  rw [prTrue_flagGame, rfGame, ← OracleAdv.run_map_state rfFlagOracle rfOracle Prod.fst
    rfFlagOracle_map A ([], false), PMF.map_comp, prTrue_pmfGame_map]
  rfl

theorem rpGame_eq (A : OracleAdv D R Bool) :
    prTrue (rpGame A) Heap.empty = prTrue (flagGame rpFlagOracle A) Heap.empty := by
  rw [prTrue_flagGame, rpGame, ← OracleAdv.run_map_state rpFlagOracle rpOracle Prod.fst
    rpFlagOracle_map A ([], false), PMF.map_comp, prTrue_pmfGame_map]
  rfl

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R] in
theorem isLossless_flagGame (O : List (D × R) × Bool → D → PMF (R × (List (D × R) × Bool)))
    (A : OracleAdv D R Bool) : isLossless (flagGame O A) := by
  intro h
  simp [SDistr.mass, flagGame, PMF.map_apply]

theorem RF_RP_Advantage_eq_flagGame (A : OracleAdv D R Bool) :
    RF_RP_Advantage A = Advantage (flagGame rfFlagOracle A) (flagGame rpFlagOracle A) := by
  simp only [RF_RP_Advantage, Advantage, rfGame_eq, rpGame_eq]

/-! ## The switching lemma -/

/-- **PRP/PRF switching lemma.** An adversary asking at most `q` adaptive
queries distinguishes the lazy random function from the lazy random injection
with advantage at most `q(q-1)/2 / |R|`. -/
theorem RF_RP_Advantage_le (A : OracleAdv D R Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    RF_RP_Advantage A ≤ ↑(q * (q - 1) / 2) / ↑(Fintype.card R) := by
  rw [RF_RP_Advantage_eq_flagGame]
  refine switching_from_birthday _ _ (fun h => h.get flagLoc = true) q (Fintype.card R)
    ?_ (isLossless_flagGame _ A) ?_
  · intro b h' hbad
    simp only [flagGame, PMF.map_apply]
    refine tsum_congr fun x => ?_
    obtain ⟨a, t, fl⟩ := x
    cases fl with
    | false =>
      rw [OracleAdv.run_apply_flag_false_eq rfFlagOracle rpFlagOracle
        rfFlagOracle_apply_true_false rpFlagOracle_apply_true_false rfFlagOracle_apply_false_eq]
    | true =>
      have hne : some (b, h') ≠ some (a, Heap.empty.set flagLoc true) := by
        rintro h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact hbad (h.2 ▸ Heap.get_set_same _ _ _)
      simp only [hne, if_false]
  · rw [prEventComp_flagGame]
    refine (run_rfFlagOracle_flag_le A q hA []).trans_eq ?_
    simp [CatCrypt.Prob.BirthdayBound.gauss_sum_nat]

/-- **PRF advantage from PRP advantage.** For every adversary asking at most
`q` adaptive queries, the PRF advantage of a keyed function is at most its PRP
advantage plus `q(q-1)/2 / |R|`. -/
theorem PRF_q_Advantage_le (P : K → D → R) (A : OracleAdv D R Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    PRF_q_Advantage P A ≤ PRP_q_Advantage P A + ↑(q * (q - 1) / 2) / ↑(Fintype.card R) :=
  prf_prp_composition (realGame P A) (rpGame A) (rfGame A) _ q (Fintype.card R) le_rfl
    ((max_comm _ _).trans_le (RF_RP_Advantage_le A q hA))

/-! ## Sanity facts -/

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R] in
/-- Without queries, the real game and any ideal game over a table oracle have
the same output distribution. -/
theorem realGame_eq_of_isQueryBound_zero {S : Type} (F : K → D → R)
    (O : S → D → PMF (R × S)) (s : S) {A : OracleAdv D R Bool} (hA : A.IsQueryBound 0) :
    realGame F A = pmfGame ((OracleAdv.run O A s).map Prod.fst) := by
  unfold realGame
  simp only [OracleAdv.run_map_fst_of_isQueryBound_zero _ O hA () s, PMF.bind_const]

omit [DecidableEq R] in
/-- With no queries, the PRF advantage is zero. -/
theorem PRF_q_Advantage_of_isQueryBound_zero (F : K → D → R) {A : OracleAdv D R Bool}
    (hA : A.IsQueryBound 0) : PRF_q_Advantage F A = 0 := by
  simp [PRF_q_Advantage, rfGame, realGame_eq_of_isQueryBound_zero F rfOracle [] hA, Advantage]

/-- With no queries, the PRP advantage is zero. -/
theorem PRP_q_Advantage_of_isQueryBound_zero (P : K → D → R) {A : OracleAdv D R Bool}
    (hA : A.IsQueryBound 0) : PRP_q_Advantage P A = 0 := by
  simp [PRP_q_Advantage, rpGame, realGame_eq_of_isQueryBound_zero P rpOracle [] hA, Advantage]

/-- With no queries, the random function and the random injection are
indistinguishable. -/
theorem RF_RP_Advantage_of_isQueryBound_zero {A : OracleAdv D R Bool}
    (hA : A.IsQueryBound 0) : RF_RP_Advantage A = 0 :=
  nonpos_iff_eq_zero.mp ((RF_RP_Advantage_le A 0 hA).trans_eq (by simp))

omit [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R] in
/-- The two-query adversary that queries `d₁` and `d₂` and outputs whether the
answers coincide asks at most two queries. -/
theorem isQueryBound_two_query (d₁ d₂ : D) (g : R → R → Bool) :
    (OracleAdv.query d₁ fun r₁ => OracleAdv.query d₂ fun r₂ =>
      OracleAdv.ret (g r₁ r₂)).IsQueryBound 2 :=
  fun _ _ => trivial

omit [DecidableEq R] [Nonempty R] in
/-- The switching bound is at most one when `q(q-1) ≤ 2|R|`. -/
theorem switching_bound_le_one (q : ℕ) (hq : q * (q - 1) ≤ 2 * Fintype.card R) :
    (↑(q * (q - 1) / 2) / ↑(Fintype.card R) : ℝ≥0∞) ≤ 1 := by
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast Nat.div_le_of_le_mul (by omega)

end CatCrypt.Crypto.PRPPRF

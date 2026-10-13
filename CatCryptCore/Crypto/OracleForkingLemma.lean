/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversary
public import CatCryptCore.Crypto.GeneralForkingLemma
public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# Forking lemma for adaptive oracle adversaries

An adaptive adversary `A : OracleAdv D R α` runs against a stateful oracle
`O : S → D → Step R S Ch`. A transition is either an arbitrary distribution
(`Step.plain`) or a uniform draw from the finite set `Ch` followed by a
deterministic answer and next state (`Step.fresh`). The fresh draws are the
points at which the run can be forked; in a random-oracle game they are the
lazily sampled hash values.

A counter `ctr : S → ℕ` numbers the fresh draws: plain transitions keep it and
fresh transitions increment it. A predicate `hit c y` on final outputs states
that the output `y` is accepting and refers to the draw numbered `c`; at most
one `c` holds for each `y`, and `c < ctr y.2`.

`forkRun` runs the adversary once. At every fresh draw it records the draw
`e₁`, and when the output of the rest of the run refers to that draw, it runs
the rest of the run a second time from the same state with a fresh draw `e₂`
and returns both outputs. This is the forking algorithm of Bellare and Neven:
the fork point is the draw named by the first output.

## Main definitions

* `Step`, `Step.toPMF`, `toOracle` — oracle transitions with explicit fresh draws
* `forkRun` — the forking run
* `accProb c A s` — probability that the output refers to draw `c`
* `forkSucc c r`, `forkProb c A s` — both outputs refer to draw `c` and the two
  draws differ
* `IsQueryBound₂ A h q` — every path of `A` asks at most `h` queries of the left
  kind and `q` of the right kind

## Main results

* `forkRun_map_fst` — the first output of `forkRun` is distributed as the run
* `accProb_sq_sub_le_forkProb` — `acc_c² − acc_c/|Ch| ≤ fork_c`
* `sum_accProb_sq_div_sub_le` — for `Q` indices,
  `(∑ acc_c)²/Q − (∑ acc_c)/|Ch| ≤ ∑ fork_c`
* `sum_forkProb_le` — the fork events for distinct indices are disjoint, so their
  sum is bounded by any event they imply on the support
* `exists_fresh_of_mem_support_forkRun` — a forked pair comes from one fresh
  transition, and both final states are reachable from its two answers
* `sum_fin_toOuterMeasure_eq` — disjoint events whose union is `W` on the support
  have probabilities summing to that of `W`
* `tsum_mul_sq_div_sub_le` — Jensen's inequality for `x ↦ x²/Q − x/N` under
  sub-probability weights

## References

* M. Bellare, G. Neven, *Multi-signatures in the plain public-key model and a
  general forking lemma*, CCS 2006, Lemma 1.
* D. Pointcheval, J. Stern, *Security arguments for digital signatures and blind
  signatures*, J. Cryptology 13(3), 2000.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleForking

open CatCrypt.Crypto
open scoped ENNReal

/-- One transition of a stateful oracle: an arbitrary distribution on answers
and next states, or a uniform draw from `Ch` mapped to an answer and next state. -/
inductive Step (R S Ch : Type) : Type
  /-- A transition given by an arbitrary distribution. -/
  | plain (p : PMF (R × S))
  /-- A uniform draw from `Ch` followed by the deterministic map `f`. -/
  | fresh (f : Ch → R × S)

variable {D R S Ch α : Type} [Fintype Ch] [Nonempty Ch]

/-- The distribution of a transition. -/
noncomputable def Step.toPMF : Step R S Ch → PMF (R × S)
  | .plain p => p
  | .fresh f => (PMF.uniformOfFintype Ch).map f

/-- The stateful oracle given by the transitions `O`. -/
noncomputable def toOracle (O : S → D → Step R S Ch) : S → D → PMF (R × S) :=
  fun s d => (O s d).toPMF

section Fork

variable (O : S → D → Step R S Ch) (ctr : S → ℕ) (hit : ℕ → α × S → Bool)

/-- The forking run. At a fresh draw `e₁` in state `s`, the rest of the run is
run with `e₁`; when its output `y₁` satisfies `hit (ctr s) y₁`, the rest of the
run is run again from `s` with a fresh draw `e₂`, and the result records `y₁`
together with the second output `y₂` and the two draws. -/
noncomputable def forkRun :
    OracleAdv D R α → S → PMF ((α × S) × Option ((α × S) × Ch × Ch))
  | .ret a, s => PMF.pure ((a, s), none)
  | .rand p k, s => p.bind fun b => forkRun (k b) s
  | .query d k, s =>
    match O s d with
    | .plain p => p.bind fun x => forkRun (k x.1) x.2
    | .fresh f => (PMF.uniformOfFintype Ch).bind fun e₁ =>
        (forkRun (k (f e₁).1) (f e₁).2).bind fun r =>
          if hit (ctr s) r.1 then
            (PMF.uniformOfFintype Ch).bind fun e₂ =>
              (OracleAdv.run (toOracle O) (k (f e₂).1) (f e₂).2).map fun y₂ =>
                (r.1, some (y₂, e₁, e₂))
          else PMF.pure r

/-- The forking run succeeds at index `c`: both outputs refer to draw `c` and
the two draws differ. -/
def forkSucc [DecidableEq Ch] (c : ℕ) (r : (α × S) × Option ((α × S) × Ch × Ch)) : Bool :=
  match r.2 with
  | some (y₂, e₁, e₂) => hit c r.1 && hit c y₂ && decide (e₁ ≠ e₂)
  | none => false

/-- Probability that the output of the run refers to draw `c`. -/
noncomputable def accProb (c : ℕ) (A : OracleAdv D R α) (s : S) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle O) A s).toOuterMeasure {y | hit c y = true}

/-- Probability that the forking run succeeds at index `c`. -/
noncomputable def forkProb [DecidableEq Ch] (c : ℕ) (A : OracleAdv D R α) (s : S) : ℝ≥0∞ :=
  (forkRun O ctr hit A s).toOuterMeasure {r | forkSucc hit c r = true}

/-- The first output of the forking run is distributed as the run. -/
theorem forkRun_map_fst (A : OracleAdv D R α) (s : S) :
    (forkRun O ctr hit A s).map Prod.fst = OracleAdv.run (toOracle O) A s := by
  induction A generalizing s with
  | ret a => simp [forkRun, PMF.pure_map]
  | rand p k ih => simp only [forkRun, OracleAdv.run_rand, PMF.map_bind, ih]
  | query d k ih =>
    rw [OracleAdv.run_query]
    cases h : O s d with
    | plain p => simp only [forkRun, toOracle, h, Step.toPMF, PMF.map_bind, ih]
    | fresh f =>
      simp only [forkRun, toOracle, h, Step.toPMF, PMF.map_bind, PMF.bind_map]
      congr 1; funext e₁
      have hc : ∀ r : (α × S) × Option ((α × S) × Ch × Ch),
          PMF.map Prod.fst (if hit (ctr s) r.1 = true then
            (PMF.uniformOfFintype Ch).bind fun e₂ =>
              PMF.map (fun y₂ => (r.1, some (y₂, e₁, e₂)))
                (OracleAdv.run (toOracle O) (k (f e₂).1) (f e₂).2)
            else PMF.pure r) = PMF.pure r.1 := by
        intro r
        split_ifs
        · have hconst : ∀ {β : Type} (q : PMF β) (b : α × S),
              q.map (fun _ => b) = PMF.pure b := fun q b => PMF.map_const q b
          simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, hconst, PMF.bind_const]
        · simp [PMF.pure_map]
      simp only [hc, Function.comp_apply]
      rw [← ih]
      exact PMF.bind_pure_comp _ _

end Fork

/-! ## Inequalities -/

omit [Fintype Ch] [Nonempty Ch] in
theorem toOuterMeasure_le_one {β : Type} (p : PMF β) (s : Set β) : p.toOuterMeasure s ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
    ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))

omit [Fintype Ch] [Nonempty Ch] in
/-- Jensen's inequality for `x ↦ x² − x/N` under sub-probability weights, for
values in `[0, 1]`. -/
theorem tsum_mul_sq_sub_le {ι : Type} (w f : ι → ℝ≥0∞) (hw : ∑' i, w i ≤ 1)
    (hf : ∀ i, f i ≤ 1) (N : ℝ≥0∞) :
    (∑' i, w i * f i) ^ 2 - (∑' i, w i * f i) / N ≤ ∑' i, w i * (f i ^ 2 - f i / N) := by
  rw [tsub_le_iff_right]
  calc (∑' i, w i * f i) ^ 2 ≤ ∑' i, w i * f i ^ 2 := ForkingLemma.jensen_sub_pmf_sq w f hw hf
    _ ≤ ∑' i, (w i * (f i ^ 2 - f i / N) + w i * (f i / N)) :=
        ENNReal.tsum_le_tsum fun i => by rw [← mul_add]; gcongr; exact le_tsub_add
    _ = ∑' i, w i * (f i ^ 2 - f i / N) + (∑' i, w i * f i) / N := by
        rw [ENNReal.tsum_add]; congr 1
        simp only [div_eq_mul_inv, ← mul_assoc]
        exact ENNReal.tsum_mul_right

omit [Nonempty Ch] in
/-- Counting pairs of distinct draws: for `a : Ch → [0, 1]` with mean `ā`,
`ā² − ā/|Ch|` is at most the mean of `a e₁ · a e₂` over pairs with `e₁ ≠ e₂`. -/
theorem sq_sub_le_sum_offDiag [DecidableEq Ch] (a : Ch → ℝ≥0∞) (ha : ∀ e, a e ≤ 1) :
    (∑ e, (Fintype.card Ch : ℝ≥0∞)⁻¹ * a e) ^ 2 -
        (∑ e, (Fintype.card Ch : ℝ≥0∞)⁻¹ * a e) / Fintype.card Ch ≤
      ∑ e₁, (Fintype.card Ch : ℝ≥0∞)⁻¹ *
        (a e₁ * ∑ e₂, (Fintype.card Ch : ℝ≥0∞)⁻¹ * (if e₁ ≠ e₂ then a e₂ else 0)) := by
  set N : ℝ≥0∞ := (Fintype.card Ch : ℝ≥0∞)
  set T := ∑ e, a e
  have hsum : ∑ e, N⁻¹ * a e = N⁻¹ * T := by rw [Finset.mul_sum]
  have hrhs : ∑ e₁, N⁻¹ * (a e₁ * ∑ e₂, N⁻¹ * (if e₁ ≠ e₂ then a e₂ else 0)) =
      N⁻¹ * N⁻¹ * ∑ e₁, ∑ e₂, (if e₁ ≠ e₂ then a e₁ * a e₂ else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e₂ _ => ?_
    split_ifs <;> ring
  have hsq : T ^ 2 ≤ T + ∑ e₁, ∑ e₂, (if e₁ ≠ e₂ then a e₁ * a e₂ else 0) := by
    have hsplit : T ^ 2 = ∑ e₁, (a e₁ * a e₁ +
        ∑ e₂, (if e₁ ≠ e₂ then a e₁ * a e₂ else 0)) := by
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e₁ _ => ?_
      rw [Finset.mul_sum]
      have : ∀ e₂, a e₁ * a e₂ = (if e₁ = e₂ then a e₁ * a e₂ else 0) +
          (if e₁ ≠ e₂ then a e₁ * a e₂ else 0) := by
        intro e₂; by_cases h : e₁ = e₂ <;> simp [h]
      rw [Finset.sum_congr rfl fun e₂ _ => this e₂, Finset.sum_add_distrib,
        Finset.sum_ite_eq]
      simp
    rw [hsplit, Finset.sum_add_distrib]
    refine add_le_add_left (Finset.sum_le_sum fun e₁ _ => ?_) _
    calc a e₁ * a e₁ ≤ a e₁ * 1 := by gcongr; exact ha e₁
      _ = a e₁ := mul_one _
  rw [hsum, hrhs, tsub_le_iff_right]
  calc (N⁻¹ * T) ^ 2 = N⁻¹ * N⁻¹ * T ^ 2 := by ring
    _ ≤ N⁻¹ * N⁻¹ * (T + ∑ e₁, ∑ e₂, (if e₁ ≠ e₂ then a e₁ * a e₂ else 0)) := by gcongr
    _ = _ := by rw [mul_add, add_comm]; simp only [div_eq_mul_inv]; ring

/-! ## The forking bound -/

section ForkBound

variable [DecidableEq Ch] (O : S → D → Step R S Ch) (ctr : S → ℕ) (hit : ℕ → α × S → Bool)

omit [Fintype Ch] [Nonempty Ch] in
theorem hit_of_forkSucc {c : ℕ} {r : (α × S) × Option ((α × S) × Ch × Ch)}
    (h : forkSucc hit c r = true) : hit c r.1 = true := by
  unfold forkSucc at h
  rcases hr : r.2 with _ | ⟨y₂, e₁, e₂⟩ <;> simp_all

/-- **Forking lemma at one index.** When plain transitions keep the counter,
fresh transitions increment it, outputs refer only to earlier draws, and every
output refers to at most one draw, then for every index `c` at or above the
current counter, `acc_c² − acc_c/|Ch| ≤ fork_c`. -/
theorem accProb_sq_sub_le_forkProb
    (hplain : ∀ s d p, O s d = .plain p → ∀ x ∈ p.support, ctr x.2 = ctr s)
    (hfresh : ∀ s d f, O s d = .fresh f → ∀ e, ctr (f e).2 = ctr s + 1)
    (hlt : ∀ c y, hit c y = true → c < ctr y.2)
    (hdisj : ∀ c c' y, hit c y = true → hit c' y = true → c = c')
    (A : OracleAdv D R α) (s : S) (c : ℕ) (hc : ctr s ≤ c) :
    accProb O hit c A s ^ 2 - accProb O hit c A s / Fintype.card Ch ≤
      forkProb O ctr hit c A s := by
  induction A generalizing s with
  | ret a =>
    have h0 : accProb O hit c (.ret a) s = 0 := by
      simp only [accProb, OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq]
      rw [if_neg]
      intro h
      exact absurd (hlt c _ h) (not_lt.mpr hc)
    simp [h0]
  | rand p k ih =>
    simp only [accProb, forkProb, OracleAdv.run_rand, forkRun, PMF.toOuterMeasure_bind_apply]
    exact (tsum_mul_sq_sub_le _ _ (le_of_eq p.tsum_coe) (fun _ => toOuterMeasure_le_one _ _)
      _).trans (ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b s hc) _)
  | query d k ih =>
    cases h : O s d with
    | plain p =>
      simp only [accProb, forkProb, OracleAdv.run_query, toOracle, h, Step.toPMF, forkRun,
        PMF.toOuterMeasure_bind_apply]
      refine (tsum_mul_sq_sub_le _ _ (le_of_eq p.tsum_coe) (fun _ => toOuterMeasure_le_one _ _)
        _).trans (ENNReal.tsum_le_tsum fun x => ?_)
      by_cases hx : x ∈ p.support
      · exact mul_le_mul_right (ih x.1 x.2 ((hplain s d p h x hx).trans_le hc)) _
      · simp [(PMF.apply_eq_zero_iff p x).mpr hx]
    | fresh f =>
      simp only [forkProb, forkRun, h, PMF.toOuterMeasure_bind_apply]
      set u := PMF.uniformOfFintype Ch
      set a : Ch → ℝ≥0∞ := fun e => accProb O hit c (k (f e).1) (f e).2 with ha_def
      have hacc : accProb O hit c (.query d k) s = ∑' e, u e * a e := by
        simp only [accProb, OracleAdv.run_query, toOracle, h, Step.toPMF, PMF.bind_map,
          PMF.toOuterMeasure_bind_apply, Function.comp_apply, a]
        rfl
      rw [hacc]
      rcases Nat.lt_or_eq_of_le hc with hlt' | heq
      · -- the index lies beyond this draw: the fork happens later
        have hinner : ∀ e₁, (∑' r, forkRun O ctr hit (k (f e₁).1) (f e₁).2 r *
            (if hit (ctr s) r.1 = true then
              u.bind fun e₂ =>
                (OracleAdv.run (toOracle O) (k (f e₂).1) (f e₂).2).map fun y₂ =>
                  (r.1, some (y₂, e₁, e₂))
            else PMF.pure r).toOuterMeasure {r | forkSucc hit c r = true}) =
            forkProb O ctr hit c (k (f e₁).1) (f e₁).2 := by
          intro e₁
          unfold forkProb
          conv_rhs => rw [← PMF.bind_pure (forkRun O ctr hit (k (f e₁).1) (f e₁).2),
            PMF.toOuterMeasure_bind_apply]
          refine tsum_congr fun r => ?_
          congr 1
          by_cases hh : hit (ctr s) r.1 = true
          · have hc1 : hit c r.1 = false := by
              by_contra hne
              exact absurd (hdisj _ _ _ (Bool.not_eq_false _ ▸ hne) hh) hlt'.ne'
            have hS : ∀ e₂ : Ch, (fun y₂ => (r.1, some (y₂, e₁, e₂))) ⁻¹'
                {r : (α × S) × Option ((α × S) × Ch × Ch) | forkSucc hit c r = true} = ∅ := by
              intro e₂
              ext y
              simp [forkSucc, hc1]
            have hr : forkSucc hit c r = false := by
              by_contra hne
              rw [hit_of_forkSucc hit (Bool.not_eq_false _ ▸ hne)] at hc1
              exact Bool.noConfusion hc1
            simp only [hh, if_true, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
              hS, MeasureTheory.measure_empty, mul_zero, tsum_zero,
              PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, hr]
            simp
          · rw [if_neg hh]
        simp_rw [hinner]
        refine (tsum_mul_sq_sub_le _ _ (le_of_eq u.tsum_coe) (fun _ => toOuterMeasure_le_one _ _)
          _).trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right (ih _ _ ?_) _)
        rw [hfresh s d f h e]
        exact hlt'
      · -- the index is this draw
        subst heq
        set B : Ch → ℝ≥0∞ := fun e₁ => ∑' e₂, u e₂ * (if e₁ ≠ e₂ then a e₂ else 0) with hB
        have hinner : ∀ e₁, (∑' r, forkRun O ctr hit (k (f e₁).1) (f e₁).2 r *
            (if hit (ctr s) r.1 = true then
              u.bind fun e₂ =>
                (OracleAdv.run (toOracle O) (k (f e₂).1) (f e₂).2).map fun y₂ =>
                  (r.1, some (y₂, e₁, e₂))
            else PMF.pure r).toOuterMeasure {r | forkSucc hit (ctr s) r = true}) =
            a e₁ * B e₁ := by
          intro e₁
          have hpt : ∀ r : (α × S) × Option ((α × S) × Ch × Ch),
              (if hit (ctr s) r.1 = true then
                u.bind fun e₂ =>
                  (OracleAdv.run (toOracle O) (k (f e₂).1) (f e₂).2).map fun y₂ =>
                    (r.1, some (y₂, e₁, e₂))
              else PMF.pure r).toOuterMeasure {r | forkSucc hit (ctr s) r = true} =
                (if hit (ctr s) r.1 = true then 1 else 0) * B e₁ := by
            intro r
            by_cases hh : hit (ctr s) r.1 = true
            · simp only [hh, if_true, one_mul, PMF.toOuterMeasure_bind_apply,
                PMF.toOuterMeasure_map_apply, B]
              refine tsum_congr fun e₂ => ?_
              congr 1
              by_cases he : e₁ = e₂
              · subst he
                simp [forkSucc]
              · simp only [ne_eq, he, not_false_eq_true, if_true, a, accProb]
                congr 1
                ext y
                simp [forkSucc, hh, he]
            · have hr : forkSucc hit (ctr s) r = false := by
                by_contra hne
                exact hh (hit_of_forkSucc hit (Bool.not_eq_false _ ▸ hne))
              simp [hh, hr, PMF.toOuterMeasure_pure_apply]
          simp only [hpt]
          have hmeas : (∑' r, forkRun O ctr hit (k (f e₁).1) (f e₁).2 r *
              (if hit (ctr s) r.1 = true then 1 else 0)) = a e₁ := by
            simp only [a, accProb]
            rw [← forkRun_map_fst O ctr hit, PMF.toOuterMeasure_map_apply,
              PMF.toOuterMeasure_apply]
            refine tsum_congr fun r => ?_
            simp [Set.indicator_apply]
          rw [← hmeas, ← ENNReal.tsum_mul_right]
          exact tsum_congr fun r => (mul_assoc _ _ _).symm
        simp_rw [hinner]
        have hu : ∀ e, u e = (Fintype.card Ch : ℝ≥0∞)⁻¹ := PMF.uniformOfFintype_apply
        have ha1 : ∀ e, a e ≤ 1 := fun _ => toOuterMeasure_le_one _ _
        simp only [tsum_fintype, hu, B]
        exact sq_sub_le_sum_offDiag a ha1

/-- **Forking lemma** (Bellare–Neven). Starting from counter `0`, the fork
events over `Q` indices have total probability at least
`(∑ acc_c)²/Q − (∑ acc_c)/|Ch|`. -/
theorem sum_accProb_sq_div_sub_le
    (hplain : ∀ s d p, O s d = .plain p → ∀ x ∈ p.support, ctr x.2 = ctr s)
    (hfresh : ∀ s d f, O s d = .fresh f → ∀ e, ctr (f e).2 = ctr s + 1)
    (hlt : ∀ c y, hit c y = true → c < ctr y.2)
    (hdisj : ∀ c c' y, hit c y = true → hit c' y = true → c = c')
    (Q : ℕ) (hQ : 0 < Q) (A : OracleAdv D R α) (s : S) (hs : ctr s = 0) :
    (∑ c : Fin Q, accProb O hit c A s) ^ 2 / Q -
        (∑ c : Fin Q, accProb O hit c A s) / Fintype.card Ch ≤
      ∑ c : Fin Q, forkProb O ctr hit c A s :=
  GeneralForkingLemma.bellare_neven_aggregation hQ _ _ _ fun c =>
    accProb_sq_sub_le_forkProb O ctr hit hplain hfresh hlt hdisj A s c (hs ▸ Nat.zero_le _)

/-- The forking bound `u ↦ u·(u/Q − 1/N)` is monotone, and at a finite `y` it
equals `y²/Q − y/N`. A reduction with a signing-simulation loss transports the
bound from the simulated advantage `y` to any lower bound `x` on it. -/
theorem mul_div_tsub_le_sq_div_tsub {x y Q N : ℝ≥0∞} (hxy : x ≤ y) (hy : y ≠ ⊤) :
    x * (x / Q - 1 / N) ≤ y ^ 2 / Q - y / N := by
  calc x * (x / Q - 1 / N) ≤ y * (y / Q - 1 / N) := by gcongr
    _ = y ^ 2 / Q - y / N := by
      rw [ENNReal.mul_sub (fun _ _ => hy), pow_two, mul_div_assoc, mul_one_div]

/-- The fork events at distinct indices are disjoint, so the sum of their
probabilities is at most the probability of any event they imply on the
support of the forking run. -/
theorem sum_forkProb_le
    (hdisj : ∀ c c' y, hit c y = true → hit c' y = true → c = c')
    (Q : ℕ) (A : OracleAdv D R α) (s : S) (W : (α × S) × Option ((α × S) × Ch × Ch) → Prop)
    (hW : ∀ r ∈ (forkRun O ctr hit A s).support, ∀ c : Fin Q, forkSucc hit c r = true → W r) :
    ∑ c : Fin Q, forkProb O ctr hit c A s ≤ (forkRun O ctr hit A s).toOuterMeasure {r | W r} := by
  classical
  simp only [forkProb, PMF.toOuterMeasure_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun r => ?_
  by_cases hr : r ∈ (forkRun O ctr hit A s).support
  · by_cases hex : ∃ c : Fin Q, forkSucc hit c r = true
    · obtain ⟨c, hc⟩ := hex
      rw [Finset.sum_eq_single c]
      · simp [hc, hW r hr c hc]
      · intro c' _ hne
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        rw [if_neg]
        intro hc'
        exact hne (Fin.ext (hdisj _ _ _ (hit_of_forkSucc hit hc') (hit_of_forkSucc hit hc)))
      · simp
    · simp only [not_exists, Bool.not_eq_true] at hex
      simp [Set.indicator_apply, hex]
  · simp [Set.indicator_apply, (PMF.apply_eq_zero_iff _ _).mpr hr]

end ForkBound

/-! ## Support invariants -/

section Support

omit [Fintype Ch] [Nonempty Ch] in
/-- A reflexive and transitive relation that holds between the state before and
after every oracle transition holds between the initial and the final state of
every run. -/
theorem run_support_rel (O' : S → D → PMF (R × S)) (Rel : S → S → Prop)
    (hrefl : ∀ s, Rel s s) (htrans : ∀ s₁ s₂ s₃, Rel s₁ s₂ → Rel s₂ s₃ → Rel s₁ s₃)
    (hstep : ∀ s d x, x ∈ (O' s d).support → Rel s x.2)
    (A : OracleAdv D R α) (s : S) (y : α × S) (hy : y ∈ (OracleAdv.run O' A s).support) :
    Rel s y.2 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hrefl s
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    exact htrans _ _ _ (hstep s d x hx) (ih _ _ hy)

variable (O : S → D → Step R S Ch) (ctr : S → ℕ) (hit : ℕ → α × S → Bool)

/-- A forked pair comes from one fresh transition `f` in a state `s₀` whose
counter is the index named by the first output, and a relation preserved by all
transitions holds from the next state after each of the two draws to the
corresponding final state. -/
theorem exists_fresh_of_mem_support_forkRun (Rel : S → S → Prop)
    (hrefl : ∀ s, Rel s s) (htrans : ∀ s₁ s₂ s₃, Rel s₁ s₂ → Rel s₂ s₃ → Rel s₁ s₃)
    (hstep : ∀ s d x, x ∈ (toOracle O s d).support → Rel s x.2)
    (A : OracleAdv D R α) (s : S) (r : (α × S) × Option ((α × S) × Ch × Ch))
    (y₂ : α × S) (e₁ e₂ : Ch)
    (hr : r ∈ (forkRun O ctr hit A s).support) (h2 : r.2 = some (y₂, e₁, e₂)) :
    ∃ s₀ d₀ f, O s₀ d₀ = .fresh f ∧ hit (ctr s₀) r.1 = true ∧
      Rel (f e₁).2 r.1.2 ∧ Rel (f e₂).2 y₂.2 := by
  induction A generalizing s r with
  | ret a =>
    simp only [forkRun, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp at h2
  | rand p k ih =>
    simp only [forkRun, PMF.mem_support_bind_iff] at hr
    obtain ⟨b, _, hb⟩ := hr
    exact ih b s r hb h2
  | query d k ih =>
    cases h : O s d with
    | plain p =>
      simp only [forkRun, h, PMF.mem_support_bind_iff] at hr
      obtain ⟨x, _, hx⟩ := hr
      exact ih _ _ r hx h2
    | fresh f =>
      simp only [forkRun, h, PMF.mem_support_bind_iff] at hr
      obtain ⟨e, _, r', hr', hr⟩ := hr
      split_ifs at hr with hh
      · rw [PMF.mem_support_bind_iff] at hr
        obtain ⟨e', _, hr⟩ := hr
        rw [PMF.mem_support_map_iff] at hr
        obtain ⟨y, hy, rfl⟩ := hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        refine ⟨s, d, f, h, hh, ?_, ?_⟩
        · have hmem : r'.1 ∈ (OracleAdv.run (toOracle O) (k (f e).1) (f e).2).support := by
            rw [← forkRun_map_fst O ctr hit]
            exact (PMF.mem_support_map_iff _ _ _).mpr ⟨r', hr', rfl⟩
          exact run_support_rel _ Rel hrefl htrans hstep _ _ _ hmem
        · exact run_support_rel _ Rel hrefl htrans hstep _ _ _ hy
      · rw [PMF.support_pure, Set.mem_singleton_iff] at hr
        rw [hr] at h2 ⊢
        exact ih _ _ r' hr' h2

end Support

/-! ## Query bounds for two kinds of queries -/

/-- `IsQueryBound₂ A h q`: every path of `A` asks at most `h` queries in `D₁` and
at most `q` queries in `D₂`. -/
def IsQueryBound₂ {D₁ D₂ R α : Type} : OracleAdv (D₁ ⊕ D₂) R α → ℕ → ℕ → Prop
  | .ret _, _, _ => True
  | .rand _ k, h, q => ∀ b, IsQueryBound₂ (k b) h q
  | .query (.inl _) _, 0, _ => False
  | .query (.inl _) k, h + 1, q => ∀ r, IsQueryBound₂ (k r) h q
  | .query (.inr _) _, _, 0 => False
  | .query (.inr _) k, h, q + 1 => ∀ r, IsQueryBound₂ (k r) h q

/-! ## Probability bounds -/

/-- The game that samples its output bit from `p` succeeds with probability
`p true`, written as the measure of `{b | b = true}`. -/
theorem prTrue_pmfGame (p : PMF Bool) :
    prTrue (PRPPRF.pmfGame p) CatCrypt.Core.Heap.empty = p.toOuterMeasure {b | b = true} := by
  have h := PRPPRF.prTrue_pmfGame_map p id CatCrypt.Core.Heap.empty
  rwa [PMF.map_id] at h

/-- For events `E c` indexed by `c < Q` that are pairwise disjoint and whose union
is `W` on the support, the probabilities of the `E c` sum to that of `W`. -/
theorem sum_fin_toOuterMeasure_eq {β : Type} (p : PMF β) (Q : ℕ) (E : ℕ → β → Bool)
    (W : β → Bool) (hdisj : ∀ c c' y, E c y = true → E c' y = true → c = c')
    (hW : ∀ y ∈ p.support, W y = true ↔ ∃ c : Fin Q, E c y = true) :
    ∑ c : Fin Q, p.toOuterMeasure {y | E c y = true} = p.toOuterMeasure {y | W y = true} := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun y => ?_
  by_cases hy : y ∈ p.support
  · by_cases hex : ∃ c : Fin Q, E c y = true
    · obtain ⟨c, hc⟩ := hex
      rw [Finset.sum_eq_single c]
      · simp [hc, (hW y hy).mpr ⟨c, hc⟩]
      · intro c' _ hne
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        rw [if_neg]
        intro hc'
        exact hne (Fin.ext (hdisj _ _ _ hc' hc))
      · simp
    · have hWf : ¬ W y = true := fun h => hex ((hW y hy).mp h)
      simp only [not_exists, Bool.not_eq_true] at hex hWf
      simp [hex, hWf]
  · simp [Set.indicator_apply, (PMF.apply_eq_zero_iff _ _).mpr hy]

/-- Jensen's inequality for `x ↦ x²/Q − x/N` under sub-probability weights, for
values in `[0, 1]`. -/
theorem tsum_mul_sq_div_sub_le {ι : Type} (w f : ι → ℝ≥0∞) (hw : ∑' i, w i ≤ 1)
    (hf : ∀ i, f i ≤ 1) (Q N : ℝ≥0∞) :
    (∑' i, w i * f i) ^ 2 / Q - (∑' i, w i * f i) / N ≤
      ∑' i, w i * (f i ^ 2 / Q - f i / N) := by
  rw [tsub_le_iff_right]
  calc (∑' i, w i * f i) ^ 2 / Q ≤ (∑' i, w i * f i ^ 2) / Q := by
        gcongr
        exact ForkingLemma.jensen_sub_pmf_sq w f hw hf
    _ = ∑' i, w i * (f i ^ 2 / Q) := by
        simp only [div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_assoc]
    _ ≤ ∑' i, (w i * (f i ^ 2 / Q - f i / N) + w i * (f i / N)) :=
        ENNReal.tsum_le_tsum fun i => by rw [← mul_add]; gcongr; exact le_tsub_add
    _ = ∑' i, w i * (f i ^ 2 / Q - f i / N) + (∑' i, w i * f i) / N := by
        rw [ENNReal.tsum_add]
        congr 1
        simp only [div_eq_mul_inv, ← mul_assoc]
        exact ENNReal.tsum_mul_right

end CatCrypt.Crypto.OracleForking

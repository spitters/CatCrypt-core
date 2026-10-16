/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Game
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag

/-!
# Fiat–Shamir in the random-oracle model: statistical HVZK

The signing-oracle simulation hop of `FiatShamirROM.Game` for a Σ-protocol whose
honest-verifier zero knowledge holds up to a statistical distance `δ`: for every
generated pair and challenge, every test with values in `[0, 1]` has expectation
under the honest transcript at most its expectation under the simulated
transcript plus `δ`. A Σ-protocol whose response may abort (for example a
response type `Option _`, with `none` for a rejected attempt) is an instance,
with the aborting transcripts part of the distance.

## Main definitions

* `Sigma.StatHVZK δ` — statistical HVZK with distance `δ`
* `Sigma.hvzkDist` — the least such distance, as a supremum over generated
  pairs, challenges and tests
* `Sigma.commitDist` — the largest probability of a commitment value, as a
  supremum over generated pairs

## Main results

* `Sigma.PerfectHVZK.statHVZK` — perfect HVZK is statistical HVZK with distance
  `0`
* `Sigma.statHVZK_hvzkDist`, `Sigma.commitBound_commitDist`
* `run_real_le_sim` — on the outcomes with the flag cleared, a test of the real
  run is at most the same test of the simulated run plus `q·δ`, for a run with at
  most `q` signing queries
* `eufcmaAdvantage_le_simAdvantage_stat` — the EUF-CMA advantage is at most the
  simulated-game advantage plus `qS·δ + qS·(qH + 1 + qS)·γ`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open CatCrypt.Crypto.Constructions.ECBCPRF (tsum_bind_mul tsum_pure_mul)
open scoped ENNReal

/-- Expectation of `g` under the image of `p` by `f`. -/
theorem tsum_map_mul' {α β : Type} (p : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    ∑' y, (p.map f) y * g y = ∑' a, p a * g (f a) := by
  rw [PMF.map, tsum_bind_mul]
  exact tsum_congr fun a => congrArg _ (tsum_pure_mul (f a) g)

namespace Sigma

variable (P : Sigma)

/-- **Statistical honest-verifier zero knowledge** with distance `δ`. For every
generated pair, every challenge `e` and every test `g` with values in `[0, 1]`,
the expectation of `g` on the honest transcript `(commit, respond e)` under
uniform prover randomness is at most its expectation on the simulator output
under uniform simulator randomness, plus `δ`. -/
def StatHVZK (δ : ℝ≥0∞) : Prop :=
  ∀ x w, (x, w) ∈ P.gen.support → ∀ e (g : P.Com × P.Resp → ℝ≥0∞), (∀ y, g y ≤ 1) →
    ∑' r, PMF.uniformOfFintype P.Rand r * g (P.commit x w r, P.respond x w r e) ≤
      ∑' s, PMF.uniformOfFintype P.SimRand s * g (P.simulate x e s) + δ

/-- The HVZK distance of `P`: the supremum, over generated pairs, challenges and
tests with values in `[0, 1]`, of the expectation of the test on the honest
transcript minus its expectation on the simulated transcript. -/
noncomputable def hvzkDist : ℝ≥0∞ :=
  ⨆ (x : P.Stmt) (w : P.Wit) (_ : (x, w) ∈ P.gen.support) (e : P.Ch)
    (g : P.Com × P.Resp → ℝ≥0∞) (_ : ∀ y, g y ≤ 1),
    (∑' r, PMF.uniformOfFintype P.Rand r * g (P.commit x w r, P.respond x w r e)) -
      ∑' s, PMF.uniformOfFintype P.SimRand s * g (P.simulate x e s)

theorem statHVZK_hvzkDist : P.StatHVZK P.hvzkDist := by
  intro x w hxw e g hg
  rw [← tsub_le_iff_left]
  unfold hvzkDist
  refine le_iSup_of_le x ?_
  refine le_iSup_of_le w ?_
  refine le_iSup_of_le hxw ?_
  refine le_iSup_of_le e ?_
  refine le_iSup_of_le g ?_
  exact le_iSup_of_le hg le_rfl

/-- The commitment distance of `P`: the supremum, over generated pairs and
commitment values, of the probability of the value under uniform prover
randomness. -/
noncomputable def commitDist : ℝ≥0∞ :=
  ⨆ (x : P.Stmt) (w : P.Wit) (_ : (x, w) ∈ P.gen.support) (a : P.Com),
    (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | P.commit x w r = a}

theorem commitBound_commitDist : P.CommitBound P.commitDist := fun x w hxw a =>
  le_iSup_of_le x <| le_iSup_of_le w <| le_iSup_of_le hxw <| le_iSup_of_le a le_rfl

variable {P}

/-- Perfect HVZK is statistical HVZK with distance `0`. -/
theorem PerfectHVZK.statHVZK (h : P.PerfectHVZK) : P.StatHVZK 0 := by
  intro x w hxw e g _
  have := congrArg (fun p : PMF (P.Com × P.Resp) => ∑' y, p y * g y) (h x w hxw e)
  simp only [tsum_map_mul'] at this
  rw [this, add_zero]

end Sigma

section Stat

variable {P : Sigma} {M : Type} [DecidableEq M]

/-- The test `g` on outcomes with the flag cleared, `0` on the others. -/
def offFlag {β σ : Type} (g : β × (σ × Bool) → ℝ≥0∞) (y : β × (σ × Bool)) : ℝ≥0∞ :=
  if y.2.2 = true then 0 else g y

theorem offFlag_le {β σ : Type} (g : β × (σ × Bool) → ℝ≥0∞) (y : β × (σ × Bool)) :
    offFlag g y ≤ g y := by
  unfold offFlag; split_ifs <;> simp

/-- On an outcome with the flag cleared, the real signing answer from `(e, r)`
is the answer built by `signOutOf` from the honest transcript. -/
theorem offFlag_realSignOut_le (g : Answer P × (Tables P M × Bool) → ℝ≥0∞) (x : P.Stmt)
    (w : P.Wit) (t : Tables P M) (b : Bool) (m : M) (e : P.Ch) (r : P.Rand) :
    offFlag g (realSignOut x w t b m e r) ≤
      offFlag g (signOutOf t b m (P.commit x w r, P.respond x w r e) e) := by
  unfold realSignOut signOutOf
  cases t.lookup (P.commit x w r, m) with
  | some e' => simp [offFlag]
  | none => exact le_rfl

/-- **One transition.** On the outcomes with the flag cleared, a test of one real
transition is at most the same test of one simulated transition, plus `δ` for a
signing query. -/
theorem realStep_le_simStep {δ : ℝ≥0∞} (hZK : P.StatHVZK δ) (xw : P.Stmt × P.Wit)
    (hxw : xw ∈ P.gen.support) (s : Tables P M × Bool) (d : Query P M)
    (G : Answer P × (Tables P M × Bool) → ℝ≥0∞) (hG : ∀ y, G y ≤ 1) :
    ∑' o, toOracle (realStep xw) s d o * offFlag G o ≤
      ∑' o, toOracle (simStep xw.1) s d o * G o + (if d.isRight then δ else 0) := by
  cases d with
  | inl k =>
    refine (ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offFlag_le G o) _).trans ?_
    simp only [Sum.isRight_inl, Bool.false_eq_true, if_false, add_zero]
    exact le_rfl
  | inr m =>
    simp only [toOracle, realStep, simStep, Step.toPMF, sampleCh, tsum_bind_mul,
      tsum_map_mul', Sum.isRight_inr, if_true]
    have hstep : ∀ e, ∑' r, PMF.uniformOfFintype P.Rand r *
          offFlag G (realSignOut xw.1 xw.2 s.1 s.2 m e r) ≤
        ∑' z, PMF.uniformOfFintype P.SimRand z * G (simSignOut xw.1 s.1 s.2 m e z) + δ := by
      intro e
      refine (ENNReal.tsum_le_tsum fun r =>
        mul_le_mul_right (offFlag_realSignOut_le G xw.1 xw.2 s.1 s.2 m e r) _).trans ?_
      refine (hZK xw.1 xw.2 hxw e (fun az => offFlag G (signOutOf s.1 s.2 m az e))
        (fun y => (offFlag_le G _).trans (hG _))).trans ?_
      gcongr with z
      exact offFlag_le G _
    calc ∑' e, PMF.uniformOfFintype P.Ch e * ∑' r, PMF.uniformOfFintype P.Rand r *
          offFlag G (realSignOut xw.1 xw.2 s.1 s.2 m e r)
        ≤ ∑' e, PMF.uniformOfFintype P.Ch e * (∑' z, PMF.uniformOfFintype P.SimRand z *
            G (simSignOut xw.1 s.1 s.2 m e z) + δ) :=
          ENNReal.tsum_le_tsum fun e => mul_le_mul_right (hstep e) _
      _ = _ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

variable {α : Type}

/-- A real run started with the flag set gives every test of `offFlag` the value
`0`. -/
theorem run_real_offFlag_true (xw : P.Stmt × P.Wit) (A : OracleAdv (Query P M) (Answer P) α)
    (t : Tables P M) (g : α × (Tables P M × Bool) → ℝ≥0∞) :
    ∑' y, OracleAdv.run (toOracle (realStep xw)) A (t, true) y * offFlag g y = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun y => ?_
  obtain ⟨a, t', fl⟩ := y
  cases fl with
  | true => simp [offFlag]
  | false =>
    rw [OracleAdv.run_flag_apply_false_of_true _ (fun t d r t' =>
      (PMF.apply_eq_zero_iff _ _).mpr fun hx => Bool.noConfusion (realStep_flag xw t d _ hx)),
      zero_mul]

omit [DecidableEq M] in
/-- A query bound on `query d k` bounds every continuation: one hash query or
one signing query fewer. -/
theorem isQueryBound₂_query_cases {D₁ D₂ R : Type} (d : D₁ ⊕ D₂) (k : R → OracleAdv (D₁ ⊕ D₂) R α)
    (h q : ℕ) (hA : IsQueryBound₂ (.query d k) h q) :
    ∃ h' q', q' + (if d.isRight then 1 else 0) = q ∧ ∀ r, IsQueryBound₂ (k r) h' q' := by
  cases d with
  | inl key =>
    cases h with
    | zero => exact hA.elim
    | succ h => exact ⟨h, q, rfl, hA⟩
  | inr m =>
    cases q with
    | zero => exact hA.elim
    | succ q => exact ⟨h, q, rfl, hA⟩

omit [DecidableEq M] in
theorem ite_add_mul_eq (b : Bool) (q' : ℕ) (δ : ℝ≥0∞) :
    (if b then δ else 0) + (q' : ℝ≥0∞) * δ = ((q' + if b then 1 else 0 : ℕ) : ℝ≥0∞) * δ := by
  cases b <;> simp [add_mul, add_comm]

/-- **Statistical hop for runs.** For a generated pair and a run with at most `h`
hash and `q` signing queries, a test `g` with values in `[0, 1]` on the real
outcomes with the flag cleared is at most the test on the simulated run plus
`q·δ`. -/
theorem run_real_le_sim {δ : ℝ≥0∞} (hZK : P.StatHVZK δ) (xw : P.Stmt × P.Wit)
    (hxw : xw ∈ P.gen.support) (A : OracleAdv (Query P M) (Answer P) α) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : Tables P M × Bool)
    (g : α × (Tables P M × Bool) → ℝ≥0∞) (hg : ∀ y, g y ≤ 1) :
    ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y * offFlag g y ≤
      ∑' y, OracleAdv.run (toOracle (simStep xw.1)) A s y * g y + q * δ := by
  induction A generalizing h q s with
  | ret a =>
    simp only [OracleAdv.run_ret, tsum_pure_mul]
    exact (offFlag_le g _).trans le_self_add
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    calc _ ≤ ∑' b, p b * (∑' y, OracleAdv.run (toOracle (simStep xw.1)) (k b) s y * g y +
            q * δ) := ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b h q (hA b) s) _
      _ = _ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    -- the value of the rest of the simulated run, a test with values in `[0, 1]`
    set Y : Answer P × (Tables P M × Bool) → ℝ≥0∞ := fun o =>
      ∑' y, OracleAdv.run (toOracle (simStep xw.1)) (k o.1) o.2 y * g y with hY
    have hY1 : ∀ o, Y o ≤ 1 := fun o =>
      (ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right' (hg y)).trans
        (le_of_eq (PMF.tsum_coe _))
    obtain ⟨h', q', hq', hk⟩ := isQueryBound₂_query_cases d k h q hA
    have hpt : ∀ o : Answer P × (Tables P M × Bool),
        ∑' y, OracleAdv.run (toOracle (realStep xw)) (k o.1) o.2 y * offFlag g y ≤
          offFlag Y o + q' * δ := by
      rintro ⟨r, t, fl⟩
      cases fl with
      | true =>
        rw [run_real_offFlag_true]
        exact zero_le
      | false => exact ih r h' q' (hk r) (t, false)
    calc _ ≤ ∑' o, toOracle (realStep xw) s d o * (offFlag Y o + q' * δ) :=
          ENNReal.tsum_le_tsum fun o => mul_le_mul_right (hpt o) _
      _ = ∑' o, toOracle (realStep xw) s d o * offFlag Y o + q' * δ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ ∑' o, toOracle (simStep xw.1) s d o * Y o + (if d.isRight then δ else 0) + q' * δ :=
          add_le_add (realStep_le_simStep hZK xw hxw s d Y hY1) le_rfl
      _ = _ := by rw [add_assoc, ← hq', ite_add_mul_eq]

/-- The probability of an event as the expectation of its indicator. -/
theorem toOuterMeasure_eq_tsum_ite {β : Type} (p : PMF β) (E : β → Bool) :
    p.toOuterMeasure {y | E y = true} = ∑' y, p y * (if E y = true then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun y => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]

/-- Winning in the real run has probability at most winning in the simulated run,
plus `q·δ`, plus the probability that the real run sets the flag. -/
theorem run_real_wins_le_stat {δ : ℝ≥0∞} (hZK : P.StatHVZK δ) (xw : P.Stmt × P.Wit)
    (hxw : xw ∈ P.gen.support) (A : OracleAdv (Query P M) (Answer P) (Forgery P M)) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : Tables P M × Bool) (x : P.Stmt) :
    (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure {y | wins x y = true} ≤
      (OracleAdv.run (toOracle (simStep xw.1)) A s).toOuterMeasure {y | wins x y = true} +
        q * δ +
      (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure {y | y.2.2 = true} := by
  set g : Forgery P M × (Tables P M × Bool) → ℝ≥0∞ := fun y => if wins x y = true then 1 else 0
  have hg : ∀ y, g y ≤ 1 := fun y => by simp only [g]; split_ifs <;> simp
  rw [toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
  calc _ ≤ ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y *
          (offFlag g y + if y.2.2 = true then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun y => mul_le_mul_right ?_ _
        simp only [offFlag, g]
        split_ifs <;> simp
    _ = ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y * offFlag g y +
          ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y *
            (if y.2.2 = true then 1 else 0) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add]
    _ ≤ _ := add_le_add (run_real_le_sim hZK xw hxw A h q hA s g hg) le_rfl

/-- **Signing-oracle simulation with statistical HVZK.** For a Σ-protocol with
statistical HVZK distance `δ` and commitment bound `γ`, and every adversary with
at most `qH` hash and `qS` signing queries, the EUF-CMA advantage is at most the
advantage in the game whose signing oracle is simulated from the statement by
programming the random oracle, plus `qS·δ + qS·(qH + 1 + qS)·γ`. -/
theorem eufcmaAdvantage_le_simAdvantage_stat {δ : ℝ≥0∞} (hZK : P.StatHVZK δ) {γ : ℝ≥0∞}
    (hγ : P.CommitBound γ) {qH qS : ℕ} (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤
      simAdvantage A + (qS * δ + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ) := by
  unfold eufcmaAdvantage simAdvantage eufcmaGame simGame
  rw [prTrue_gameDist, prTrue_gameDist]
  set B : ℝ≥0∞ := qS * δ + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ with hBdef
  calc _ ≤ ∑' xw, P.gen xw *
          ((OracleAdv.run (toOracle (simStep xw.1)) (withVerify (A.run xw.1))
            (Tables.empty, false)).toOuterMeasure {y | wins xw.1 y = true} + B) := by
        refine ENNReal.tsum_le_tsum fun xw => ?_
        by_cases hxw : xw ∈ P.gen.support
        · have hB := isQueryBound₂_withVerify _ qH qS (A.isQueryBound xw.1)
          refine mul_le_mul_right ?_ _
          refine (run_real_wins_le_stat hZK xw hxw _ (qH + 1) qS hB _ _).trans ?_
          rw [hBdef, add_assoc]
          refine add_le_add le_rfl (add_le_add le_rfl ?_)
          refine (run_real_flag_le hγ xw hxw _ (qH + 1) qS hB Tables.empty).trans
            (le_of_eq ?_)
          simp [Tables.empty]
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]
    _ = _ := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Stat

end CatCrypt.Crypto.FiatShamirROM

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Game
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag

/-!
# Fiat–Shamir in the random-oracle model: the signing-oracle simulation

The signing-oracle simulation hop of `FiatShamirROM.Game` for a Σ-protocol whose
honest-verifier zero knowledge holds up to a statistical distance: at a pair
`(x, w)`, for every challenge, every test with values in `[0, 1]` that does not
read the commitment of a rejected transcript has expectation under the honest
transcript at most its expectation under the simulated transcript plus `δ`. The
tests are restricted in this way because the signing oracle answers a rejected
attempt without its commitment. The distances may depend on the pair; the bound
on the EUF-CMA advantage is then an expectation over the generator.

## Main definitions

* `Sigma.RejectBlind g` — the test `g` does not read the commitment of a rejected
  transcript
* `Sigma.StatHVZKAt x w δ`, `Sigma.StatHVZK δ` — statistical HVZK with distance
  `δ` at one pair and at every generated pair
* `Sigma.hvzkDistAt x w`, `Sigma.hvzkDist` — the least such distances
* `Sigma.commitDistAt x w`, `Sigma.commitDist` — the largest probability of a
  commitment value at one pair and over the generated pairs
* `Sigma.hvzkDistOn E x w` — the HVZK distance at `(x, w)` on the transcripts
  whose response satisfies `E`

## Main results

* `Sigma.PerfectHVZK.statHVZK` — perfect HVZK is statistical HVZK with distance
  `0`
* `run_real_le_sim` — on the outcomes with the flag cleared, a test of the real
  run is at most the same test of the simulated run plus `q·δ`, for a run with at
  most `q` signing queries
* `eufcmaAdvantage_le_simAdvantage_perKey` — the EUF-CMA advantage is at most the
  simulated-game advantage plus the expectation over generated pairs of
  `qS·δ(x, w) + qS·(qH + 1 + qS)·γ(x, w)`
* `eufcmaAdvantage_le_simAdvantage_dist` — the same with the distances
  `hvzkDistAt` and `commitDistAt`
* `eufcmaAdvantage_le_simAdvantage_stat`, `eufcmaAdvantage_le_simAdvantage` —
  the bounds `qS·δ + qS·(qH + 1 + qS)·γ` and, for perfect HVZK,
  `qS·(qH + 1 + qS)·γ`
* `Sigma.hvzkDistAt_le_on_add_on` — the HVZK distance at a pair is at most its
  part on an event plus its part on the complement;
  `Sigma.hvzkDistOn_eq_zero_of_eq` — the part on an event is `0` when the honest
  and simulated transcripts in the event have equal probabilities;
  `Sigma.hvzkDistOn_reject_eq_zero` — the part on the rejected transcripts is `0`
  when rejected responses are constant and accepted transcripts match
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

/-- The test `g` on transcripts does not read the commitment of a rejected
transcript. -/
def RejectBlind (g : P.Com × P.Resp → ℝ≥0∞) : Prop :=
  ∀ a a' z, P.accept z = false → g (a, z) = g (a', z)

/-- **Statistical honest-verifier zero knowledge at one pair** with distance `δ`.
For the pair `(x, w)`, every challenge `e` and every test `g` with values in
`[0, 1]` that does not read the commitment of a rejected transcript, the
expectation of `g` on the honest transcript `(commit, respond e)` under uniform
prover randomness is at most its expectation on the simulator output under
uniform simulator randomness, plus `δ`. -/
def StatHVZKAt (x : P.Stmt) (w : P.Wit) (δ : ℝ≥0∞) : Prop :=
  ∀ e (g : P.Com × P.Resp → ℝ≥0∞), (∀ y, g y ≤ 1) → P.RejectBlind g →
    ∑' r, PMF.uniformOfFintype P.Rand r * g (P.commit x w r, P.respond x w r e) ≤
      ∑' s, PMF.uniformOfFintype P.SimRand s * g (P.simulate x e s) + δ

/-- **Statistical honest-verifier zero knowledge** with distance `δ` at every
generated pair. -/
def StatHVZK (δ : ℝ≥0∞) : Prop :=
  ∀ x w, (x, w) ∈ P.gen.support → P.StatHVZKAt x w δ

/-- The HVZK distance of `P` at the pair `(x, w)`: the supremum, over challenges
and tests with values in `[0, 1]` that do not read the commitment of a rejected
transcript, of the expectation of the test on the honest transcript minus its
expectation on the simulated transcript. -/
noncomputable def hvzkDistAt (x : P.Stmt) (w : P.Wit) : ℝ≥0∞ :=
  ⨆ (e : P.Ch) (g : P.Com × P.Resp → ℝ≥0∞) (_ : ∀ y, g y ≤ 1) (_ : P.RejectBlind g),
    (∑' r, PMF.uniformOfFintype P.Rand r * g (P.commit x w r, P.respond x w r e)) -
      ∑' s, PMF.uniformOfFintype P.SimRand s * g (P.simulate x e s)

/-- The HVZK distance of `P`: the supremum of `hvzkDistAt` over generated
pairs. -/
noncomputable def hvzkDist : ℝ≥0∞ :=
  ⨆ (x : P.Stmt) (w : P.Wit) (_ : (x, w) ∈ P.gen.support), P.hvzkDistAt x w

theorem statHVZKAt_hvzkDistAt (x : P.Stmt) (w : P.Wit) :
    P.StatHVZKAt x w (P.hvzkDistAt x w) := by
  intro e g hg hb
  rw [← tsub_le_iff_left]
  exact le_iSup_of_le e <| le_iSup_of_le g <| le_iSup_of_le hg <| le_iSup_of_le hb le_rfl

theorem statHVZK_hvzkDist : P.StatHVZK P.hvzkDist := by
  intro x w hxw e g hg hb
  refine (P.statHVZKAt_hvzkDistAt x w e g hg hb).trans (add_le_add le_rfl ?_)
  exact le_iSup_of_le x <| le_iSup_of_le w <| le_iSup_of_le hxw le_rfl

/-- The commitment distance of `P` at the pair `(x, w)`: the largest probability
of a commitment value under uniform prover randomness. -/
noncomputable def commitDistAt (x : P.Stmt) (w : P.Wit) : ℝ≥0∞ :=
  ⨆ (a : P.Com), (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | P.commit x w r = a}

/-- The commitment distance of `P`: the supremum of `commitDistAt` over generated
pairs. -/
noncomputable def commitDist : ℝ≥0∞ :=
  ⨆ (x : P.Stmt) (w : P.Wit) (_ : (x, w) ∈ P.gen.support) (a : P.Com),
    (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | P.commit x w r = a}

theorem commitBoundAt_commitDistAt (x : P.Stmt) (w : P.Wit) :
    P.CommitBoundAt x w (P.commitDistAt x w) := fun a => le_iSup_of_le a le_rfl

theorem commitBound_commitDist : P.CommitBound P.commitDist := fun x w hxw a =>
  le_iSup_of_le x <| le_iSup_of_le w <| le_iSup_of_le hxw <| le_iSup_of_le a le_rfl

variable {P}

/-- Perfect HVZK is statistical HVZK with distance `0`. -/
theorem PerfectHVZK.statHVZK (h : P.PerfectHVZK) : P.StatHVZK 0 := by
  intro x w hxw e g _ _
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

/-- The outcome `y` with the entries of rejected attempts replaced by `l`. -/
def setRej {β : Type} (l : List ((P.Com × M) × P.Ch)) (y : β × (Tables P M × Bool)) :
    β × (Tables P M × Bool) :=
  (y.1, ({ y.2.1 with rej := l }, y.2.2))

/-- The test `g` does not read the entries of rejected attempts. -/
def RejInsensitive {β : Type} (g : β × (Tables P M × Bool) → ℝ≥0∞) : Prop :=
  ∀ y l, g (setRej l y) = g y

/-- The test on transcripts that one signing step induces from the test `G` on
its outcomes: on an accepted transcript the test of the outcome of `signOutOf`
with the flag cleared, on a rejected one the test of the answer `none`. -/
def signTest (G : Answer P × (Tables P M × Bool) → ℝ≥0∞) (t : Tables P M) (b : Bool)
    (m : M) (e : P.Ch) (az : P.Com × P.Resp) : ℝ≥0∞ :=
  if P.accept az.2 then offFlag G (signOutOf t b m az e)
  else G (.inr none, ({ t with signed := t.signed ++ [m] }, b))

theorem signTest_rejectBlind (G : Answer P × (Tables P M × Bool) → ℝ≥0∞) (t : Tables P M)
    (b : Bool) (m : M) (e : P.Ch) : P.RejectBlind (signTest G t b m e) := by
  intro a a' z hz
  simp [signTest, hz]

theorem signTest_le_one (G : Answer P × (Tables P M × Bool) → ℝ≥0∞) (hG : ∀ y, G y ≤ 1)
    (t : Tables P M) (b : Bool) (m : M) (e : P.Ch) (az : P.Com × P.Resp) :
    signTest G t b m e az ≤ 1 := by
  unfold signTest
  split_ifs
  · exact (offFlag_le G _).trans (hG _)
  · exact hG _

/-- On an outcome with the flag cleared, the real signing answer from `(e, r)` is
bounded by the test of the honest transcript. -/
theorem offFlag_realSignOut_le (G : Answer P × (Tables P M × Bool) → ℝ≥0∞)
    (hG : RejInsensitive G) (x : P.Stmt) (w : P.Wit) (t : Tables P M) (b : Bool) (m : M)
    (e : P.Ch) (r : P.Rand) :
    offFlag G (realSignOut x w t b m e r) ≤
      signTest G t b m e (P.commit x w r, P.respond x w r e) := by
  unfold realSignOut
  split
  · simp [offFlag]
  · next hl =>
    have hl' : t.lookup (P.commit x w r, m) = none := by
      unfold Tables.lookupAll at hl
      cases h : t.lookup (P.commit x w r, m) with
      | none => rfl
      | some _ => simp [h] at hl
    unfold signTest
    split_ifs with hacc
    · unfold signOutOf
      rw [hl']
    · exact (offFlag_le G _).trans (le_of_eq (hG (.inr none,
        ({ t with signed := t.signed ++ [m] }, b)) (t.rej ++ [((P.commit x w r, m), e)])))

theorem signTest_le_simSignOut (G : Answer P × (Tables P M × Bool) → ℝ≥0∞) (x : P.Stmt)
    (t : Tables P M) (b : Bool) (m : M) (e : P.Ch) (s : P.SimRand) :
    signTest G t b m e (P.simulate x e s) ≤ G (simSignOut x t b m e s) := by
  unfold signTest simSignOut
  split_ifs
  · exact offFlag_le G _
  · exact le_rfl

/-- **One transition.** For a pair with statistical HVZK distance `δ` and a test
`G` with values in `[0, 1]` that does not read the entries of rejected attempts,
on the outcomes with the flag cleared a test of one real transition is at most the
same test of one simulated transition, plus `δ` for a signing query. -/
theorem realStep_le_simStep {δ : ℝ≥0∞} (xw : P.Stmt × P.Wit) (hZK : P.StatHVZKAt xw.1 xw.2 δ)
    (s : Tables P M × Bool) (d : Query P M)
    (G : Answer P × (Tables P M × Bool) → ℝ≥0∞) (hG : ∀ y, G y ≤ 1) (hGr : RejInsensitive G) :
    ∑' o, toOracle (realStep xw) s d o * offFlag G o ≤
      ∑' o, toOracle (simStep xw.1) s d o * G o + (if d.isRight then δ else 0) := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [Sum.isRight_inl, Bool.false_eq_true, if_false, add_zero]
    simp only [toOracle, realStep, simStep, realHashStep, hashStep]
    cases t.lookup k with
    | some e => exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offFlag_le G o) _
    | none =>
      cases lookupIn t.rej k with
      | some e =>
        simp only [Step.toPMF]
        rw [tsum_pure_mul]
        simp [offFlag]
      | none => exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offFlag_le G o) _
  | inr m =>
    simp only [toOracle, realStep, simStep, Step.toPMF, sampleCh, tsum_bind_mul,
      tsum_map_mul', Sum.isRight_inr, if_true]
    have hstep : ∀ e, ∑' r, PMF.uniformOfFintype P.Rand r *
          offFlag G (realSignOut xw.1 xw.2 t b m e r) ≤
        ∑' z, PMF.uniformOfFintype P.SimRand z * G (simSignOut xw.1 t b m e z) + δ := by
      intro e
      refine (ENNReal.tsum_le_tsum fun r =>
        mul_le_mul_right (offFlag_realSignOut_le G hGr xw.1 xw.2 t b m e r) _).trans ?_
      refine (hZK e (signTest G t b m e) (signTest_le_one G hG t b m e)
        (signTest_rejectBlind G t b m e)).trans ?_
      gcongr with z
      exact signTest_le_simSignOut G xw.1 t b m e z
    calc ∑' e, PMF.uniformOfFintype P.Ch e * ∑' r, PMF.uniformOfFintype P.Rand r *
          offFlag G (realSignOut xw.1 xw.2 t b m e r)
        ≤ ∑' e, PMF.uniformOfFintype P.Ch e * (∑' z, PMF.uniformOfFintype P.SimRand z *
            G (simSignOut xw.1 t b m e z) + δ) :=
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

/-- A simulated transition does not read the entries of rejected attempts and
keeps them. -/
theorem simStep_setRej (x₀ : P.Stmt) (l : List ((P.Com × M) × P.Ch)) (s : Tables P M × Bool)
    (d : Query P M) :
    (toOracle (simStep x₀) s d).map (Prod.map id fun s' => ({ s'.1 with rej := l }, s'.2)) =
      toOracle (simStep x₀) ({ s.1 with rej := l }, s.2) d := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [toOracle, simStep, hashStep]
    rw [show ({ t with rej := l } : Tables P M).lookup k = t.lookup k from rfl]
    cases t.lookup k with
    | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
    | none => simp only [Step.toPMF, PMF.map_comp]; rfl
  | inr m =>
    simp only [toOracle, simStep, Step.toPMF, sampleCh, PMF.map_bind, PMF.map_comp]
    refine congrArg _ (funext fun e => congrArg _ (funext fun z => ?_))
    simp only [Function.comp_apply]
    unfold simSignOut signOutOf
    rw [show ({ t with rej := l } : Tables P M).lookup ((P.simulate x₀ e z).1, m) =
      t.lookup ((P.simulate x₀ e z).1, m) from rfl]
    split_ifs
    · cases t.lookup ((P.simulate x₀ e z).1, m) <;> rfl
    · rfl

/-- The expectation of a test under a simulated run does not depend on the
entries of rejected attempts when the test does not read them. -/
theorem tsum_run_sim_setRej (x₀ : P.Stmt) (A : OracleAdv (Query P M) (Answer P) α)
    (g : α × (Tables P M × Bool) → ℝ≥0∞) (hg : RejInsensitive g) (s : Tables P M × Bool)
    (l : List ((P.Com × M) × P.Ch)) :
    ∑' y, OracleAdv.run (toOracle (simStep x₀)) A ({ s.1 with rej := l }, s.2) y * g y =
      ∑' y, OracleAdv.run (toOracle (simStep x₀)) A s y * g y := by
  have hm := OracleAdv.run_map_state _ _
    (fun s' : Tables P M × Bool => ({ s'.1 with rej := l }, s'.2)) (simStep_setRej x₀ l) A s
  refine (congrArg (fun p : PMF (α × (Tables P M × Bool)) => ∑' y, p y * g y) hm).symm.trans ?_
  dsimp only
  rw [tsum_map_mul']
  exact tsum_congr fun y => congrArg _ (hg y l)

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

/-- **Statistical hop for runs.** For a pair with statistical HVZK distance `δ`
and a run with at most `h` hash and `q` signing queries, a test `g` with values in
`[0, 1]` that does not read the entries of rejected attempts, on the real outcomes
with the flag cleared, is at most the test on the simulated run plus `q·δ`. -/
theorem run_real_le_sim {δ : ℝ≥0∞} (xw : P.Stmt × P.Wit) (hZK : P.StatHVZKAt xw.1 xw.2 δ)
    (A : OracleAdv (Query P M) (Answer P) α) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : Tables P M × Bool)
    (g : α × (Tables P M × Bool) → ℝ≥0∞) (hg : ∀ y, g y ≤ 1) (hgr : RejInsensitive g) :
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
    have hYr : RejInsensitive Y := fun o l =>
      tsum_run_sim_setRej xw.1 (k o.1) g hgr o.2 l
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
          add_le_add (realStep_le_simStep xw hZK s d Y hY1 hYr) le_rfl
      _ = _ := by rw [add_assoc, ← hq', ite_add_mul_eq]

/-- The probability of an event as the expectation of its indicator. -/
theorem toOuterMeasure_eq_tsum_ite {β : Type} (p : PMF β) (E : β → Bool) :
    p.toOuterMeasure {y | E y = true} = ∑' y, p y * (if E y = true then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun y => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]

/-- Winning in the real run has probability at most winning in the simulated run,
plus `q·δ`, plus the probability that the real run sets the flag. -/
theorem run_real_wins_le_stat {δ : ℝ≥0∞} (xw : P.Stmt × P.Wit) (hZK : P.StatHVZKAt xw.1 xw.2 δ)
    (A : OracleAdv (Query P M) (Answer P) (Forgery P M)) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : Tables P M × Bool) (x : P.Stmt) :
    (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure {y | wins x y = true} ≤
      (OracleAdv.run (toOracle (simStep xw.1)) A s).toOuterMeasure {y | wins x y = true} +
        q * δ +
      (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure {y | y.2.2 = true} := by
  set g : Forgery P M × (Tables P M × Bool) → ℝ≥0∞ := fun y => if wins x y = true then 1 else 0
  have hg : ∀ y, g y ≤ 1 := fun y => by simp only [g]; split_ifs <;> simp
  have hgr : RejInsensitive g := fun _ _ => rfl
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
    _ ≤ _ := add_le_add (run_real_le_sim xw hZK A h q hA s g hg hgr) le_rfl

/-- **Signing-oracle simulation with distances depending on the pair.** For a
Σ-protocol whose generated pairs `(x, w)` have statistical HVZK distance
`δ (x, w)` and commitment bound `γ (x, w)`, and every adversary with at most `qH`
hash and `qS` signing queries, the EUF-CMA advantage is at most the advantage in
the game whose signing oracle is simulated from the statement by programming the
random oracle, plus the expectation over the generator of
`qS·δ(x, w) + qS·(qH + 1 + qS)·γ(x, w)`. -/
theorem eufcmaAdvantage_le_simAdvantage_perKey {δ γ : P.Stmt × P.Wit → ℝ≥0∞}
    (hZK : ∀ xw ∈ P.gen.support, P.StatHVZKAt xw.1 xw.2 (δ xw))
    (hγ : ∀ xw ∈ P.gen.support, P.CommitBoundAt xw.1 xw.2 (γ xw)) {qH qS : ℕ}
    (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A +
      ∑' xw, P.gen xw * (qS * δ xw + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ xw) := by
  unfold eufcmaAdvantage simAdvantage eufcmaGame simGame
  rw [prTrue_gameDist, prTrue_gameDist, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun xw => ?_
  rw [← mul_add]
  by_cases hxw : xw ∈ P.gen.support
  · have hB := isQueryBound₂_withVerify _ qH qS (A.isQueryBound xw.1)
    refine mul_le_mul_right ?_ _
    refine (run_real_wins_le_stat xw (hZK xw hxw) _ (qH + 1) qS hB _ _).trans ?_
    rw [add_assoc]
    refine add_le_add le_rfl (add_le_add le_rfl ?_)
    refine (run_real_flag_le xw (hγ xw hxw) _ (qH + 1) qS hB Tables.empty rfl).trans
      (le_of_eq ?_)
    simp [Tables.empty]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]

/-- **Signing-oracle simulation at the distances of the pairs.** For every
Σ-protocol and every adversary with at most `qH` hash and `qS` signing queries,
the EUF-CMA advantage is at most the simulated-game advantage plus the
expectation over the generator of
`qS·hvzkDistAt x w + qS·(qH + 1 + qS)·commitDistAt x w`. -/
theorem eufcmaAdvantage_le_simAdvantage_dist {qH qS : ℕ} (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A +
      ∑' xw, P.gen xw * (qS * P.hvzkDistAt xw.1 xw.2 +
        ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * P.commitDistAt xw.1 xw.2) :=
  eufcmaAdvantage_le_simAdvantage_perKey (δ := fun xw => P.hvzkDistAt xw.1 xw.2)
    (γ := fun xw => P.commitDistAt xw.1 xw.2)
    (fun xw _ => P.statHVZKAt_hvzkDistAt xw.1 xw.2)
    (fun xw _ => P.commitBoundAt_commitDistAt xw.1 xw.2) A

/-- **Signing-oracle simulation with statistical HVZK.** For a Σ-protocol with
statistical HVZK distance `δ` and commitment bound `γ`, and every adversary with
at most `qH` hash and `qS` signing queries, the EUF-CMA advantage is at most the
advantage in the game whose signing oracle is simulated from the statement by
programming the random oracle, plus `qS·δ + qS·(qH + 1 + qS)·γ`. -/
theorem eufcmaAdvantage_le_simAdvantage_stat {δ : ℝ≥0∞} (hZK : P.StatHVZK δ) {γ : ℝ≥0∞}
    (hγ : P.CommitBound γ) {qH qS : ℕ} (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤
      simAdvantage A + (qS * δ + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ) := by
  refine (eufcmaAdvantage_le_simAdvantage_perKey (δ := fun _ => δ) (γ := fun _ => γ)
    (fun xw hxw => hZK xw.1 xw.2 hxw) (fun xw hxw => hγ xw.1 xw.2 hxw) A).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Signing-oracle simulation.** For a Σ-protocol with perfect HVZK and
commitment bound `γ`, and every adversary with at most `qH` hash queries and `qS`
signing queries, the EUF-CMA advantage is at most the advantage in the game whose
signing oracle is simulated from the statement by programming the random oracle,
plus `qS·(qH + 1 + qS)·γ`. -/
theorem eufcmaAdvantage_le_simAdvantage (hZK : P.PerfectHVZK) {γ : ℝ≥0∞}
    (hγ : P.CommitBound γ) {qH qS : ℕ} (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ := by
  simpa using eufcmaAdvantage_le_simAdvantage_stat hZK.statHVZK hγ A

end Stat

/-! ## Distances at one generated pair -/

namespace Sigma

variable (P : Sigma)

/-- The HVZK distance of `P` at `(x, w)` on the transcripts whose response
satisfies `E`: the supremum, over challenges and tests with values in `[0, 1]`
that do not read the commitment of a rejected transcript, of the expectation of
the test restricted to those transcripts on the honest side minus the same
expectation on the simulated side. -/
noncomputable def hvzkDistOn (E : P.Resp → Bool) (x : P.Stmt) (w : P.Wit) : ℝ≥0∞ :=
  ⨆ (e : P.Ch) (g : P.Com × P.Resp → ℝ≥0∞) (_ : ∀ y, g y ≤ 1) (_ : P.RejectBlind g),
    (∑' r, PMF.uniformOfFintype P.Rand r *
        (if E (P.respond x w r e) then g (P.commit x w r, P.respond x w r e) else 0)) -
      ∑' s, PMF.uniformOfFintype P.SimRand s *
        (if E (P.simulate x e s).2 then g (P.simulate x e s) else 0)

/-- **Splitting the HVZK distance by an event on the response.** The distance at
`(x, w)` is at most the distance on the transcripts whose response satisfies `E`
plus the distance on the others. -/
theorem hvzkDistAt_le_on_add_on (E : P.Resp → Bool) (x : P.Stmt) (w : P.Wit) :
    P.hvzkDistAt x w ≤ P.hvzkDistOn E x w + P.hvzkDistOn (fun z => !E z) x w := by
  refine iSup_le fun e => iSup_le fun g => iSup_le fun hg => iSup_le fun hb => ?_
  have hsplit : ∀ {β : Type} [Fintype β] [Nonempty β] (F : β → P.Com × P.Resp),
      ∑' b, PMF.uniformOfFintype β b * g (F b) =
        (∑' b, PMF.uniformOfFintype β b * (if E (F b).2 then g (F b) else 0)) +
          ∑' b, PMF.uniformOfFintype β b * (if (!E (F b).2) then g (F b) else 0) := by
    intro β _ _ F
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun b => ?_
    rw [← mul_add]
    cases E (F b).2 <;> simp
  rw [hsplit (fun r => (P.commit x w r, P.respond x w r e)), hsplit (P.simulate x e)]
  refine add_tsub_add_le_tsub_add_tsub.trans (add_le_add ?_ ?_)
  · exact le_iSup_of_le e <| le_iSup_of_le g <| le_iSup_of_le hg <| le_iSup_of_le hb le_rfl
  · exact le_iSup_of_le e <| le_iSup_of_le g <| le_iSup_of_le hg <| le_iSup_of_le hb le_rfl

/-- **Matching transcripts have distance zero.** If, for every challenge, every
transcript whose response satisfies `E` has the same probability on the honest
and the simulated side, the distance on those transcripts is `0`. -/
theorem hvzkDistOn_eq_zero_of_eq (E : P.Resp → Bool) (x : P.Stmt) (w : P.Wit)
    (h : ∀ e (t : P.Com × P.Resp), E t.2 = true →
      (PMF.uniformOfFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) t =
        (PMF.uniformOfFintype P.SimRand).map (P.simulate x e) t) :
    P.hvzkDistOn E x w = 0 := by
  refine le_antisymm (iSup_le fun e => iSup_le fun g => iSup_le fun _ => iSup_le fun _ => ?_)
    zero_le
  rw [tsub_le_iff_right, zero_add]
  have key := tsum_map_mul' (PMF.uniformOfFintype P.Rand)
    (fun r => (P.commit x w r, P.respond x w r e)) (fun t => if E t.2 then g t else 0)
  have key' := tsum_map_mul' (PMF.uniformOfFintype P.SimRand) (P.simulate x e)
    (fun t => if E t.2 then g t else 0)
  simp only at key key'
  rw [← key, ← key']
  refine le_of_eq (tsum_congr fun t => ?_)
  by_cases ht : E t.2 = true
  · rw [h e t ht]
  · simp [ht]

/-- **Rejected transcripts have distance zero when accepted ones match.** For a
Σ-protocol whose rejected responses are all equal to `z₀`, if at `(x, w)` every
accepted transcript has the same probability on the honest and the simulated
side, the HVZK distance on the rejected transcripts is `0`: a test that does not
read the commitment of a rejected transcript sees only the probability of
rejection, which is one minus the probability of acceptance on both sides. -/
theorem hvzkDistOn_reject_eq_zero (x : P.Stmt) (w : P.Wit)
    (z₀ : P.Resp) (hz₀ : ∀ z, P.accept z = false → z = z₀)
    (h : ∀ e (t : P.Com × P.Resp), P.accept t.2 = true →
      (PMF.uniformOfFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) t =
        (PMF.uniformOfFintype P.SimRand).map (P.simulate x e) t) :
    P.hvzkDistOn (fun z => !P.accept z) x w = 0 := by
  refine le_antisymm (iSup_le fun e => iSup_le fun g => iSup_le fun _ => iSup_le fun hb => ?_)
    zero_le
  rw [tsub_le_iff_right, zero_add]
  set a₀ : P.Com := (P.simulate x e (Classical.arbitrary _)).1
  set c : ℝ≥0∞ := g (a₀, z₀)
  have hg : ∀ t : P.Com × P.Resp, (if (!P.accept t.2) = true then g t else 0) =
      c * (if P.accept t.2 = true then 0 else 1) := by
    rintro ⟨a, z⟩
    cases hz : P.accept z
    · obtain rfl := hz₀ z hz
      simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false, mul_one]
      exact hb a a₀ _ hz
    · simp
  -- the probability of acceptance under the image of `p` by `F`
  have hacc : ∀ {β : Type} [Fintype β] [Nonempty β] (F : β → P.Com × P.Resp),
      ∑' b, PMF.uniformOfFintype β b * (if P.accept (F b).2 = true then 0 else 1) =
        1 - ∑' t, ((PMF.uniformOfFintype β).map F) t *
          (if P.accept t.2 = true then 1 else 0) := by
    intro β _ _ F
    rw [tsum_map_mul']
    refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top ?_) ?_
    · exact (ENNReal.tsum_le_tsum fun b => mul_le_of_le_one_right' (by split_ifs <;> simp)).trans
        (le_of_eq (PMF.tsum_coe _))
    · rw [← ENNReal.tsum_add]
      refine (tsum_congr fun b => ?_).trans (PMF.tsum_coe (PMF.uniformOfFintype β))
      rw [← mul_add]
      split_ifs <;> simp
  have hA : ∑' t, ((PMF.uniformOfFintype P.Rand).map
        (fun r => (P.commit x w r, P.respond x w r e))) t *
        (if P.accept t.2 = true then 1 else 0) =
      ∑' t, ((PMF.uniformOfFintype P.SimRand).map (P.simulate x e)) t *
        (if P.accept t.2 = true then 1 else 0) := by
    refine tsum_congr fun t => ?_
    by_cases ht : P.accept t.2 = true
    · rw [h e t ht]
    · simp [ht]
  have h1 := hacc (fun r => (P.commit x w r, P.respond x w r e))
  have h2 := hacc (P.simulate x e)
  simp only at h1 h2
  refine le_of_eq ?_
  calc (∑' r, PMF.uniformOfFintype P.Rand r * (if (!P.accept (P.respond x w r e)) = true then
          g (P.commit x w r, P.respond x w r e) else 0))
      = c * ∑' r, PMF.uniformOfFintype P.Rand r *
          (if P.accept (P.respond x w r e) = true then 0 else 1) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun r => (congrArg (PMF.uniformOfFintype P.Rand r * ·)
          (hg (P.commit x w r, P.respond x w r e))).trans (mul_left_comm _ _ _)
    _ = c * ∑' s, PMF.uniformOfFintype P.SimRand s *
          (if P.accept (P.simulate x e s).2 = true then 0 else 1) := by
        rw [h1, h2, hA]
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun s => ((congrArg (PMF.uniformOfFintype P.SimRand s * ·)
          (hg (P.simulate x e s))).trans (mul_left_comm _ _ _)).symm

/-- **The HVZK distance split by an event on the response.** `hvzkDist` is at
most the supremum, over generated pairs, of the distance on the transcripts whose
response satisfies `E` plus the distance on the others. -/
theorem hvzkDist_le_iSup_on_add_on (E : P.Resp → Bool) :
    P.hvzkDist ≤ ⨆ (x : P.Stmt) (w : P.Wit) (_ : (x, w) ∈ P.gen.support),
      (P.hvzkDistOn E x w + P.hvzkDistOn (fun z => !E z) x w) :=
  iSup_le fun x => iSup_le fun w => iSup_le fun hxw =>
    (P.hvzkDistAt_le_on_add_on E x w).trans
      (le_iSup_of_le x <| le_iSup_of_le w <| le_iSup_of_le hxw le_rfl)

end Sigma

end CatCrypt.Crypto.FiatShamirROM

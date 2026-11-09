/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.GodelFibrationWIter
public import CatCryptCore.Container.ExpectedDNOp
public import CatCryptCore.Unary.ExpectedCost
import all CatCryptCore.Unary.ExpectedCost
public import CatCryptCore.Crypto.FiatShamirROM.Reduction
public import CatCryptCore.Crypto.FiatShamirROM.Timed

/-!
# Expected cost of rewinding extractors as use counts of the weighted DN logic

A retry loop whose body costs at most `C` in expectation and succeeds with probability at least
`p` has expected cost at most `C / p` (`ecost_retryN_le_div`). The weighted derivation
`retryCollect` of the weighted DN logic assigns the attempt hypothesis the expected use count
`m * p⁻¹` for `m` successes (`WDeriv.wuseCount_retryCollect_of_zero`). The expected cost of the
retry loop is at most `C` times the use count of the derivation for one success, and the expected
cost of the threshold extractor `collectN` is at most `C` times the use count for `m` successes.

The forking instance: the attempt `FiatShamirROM.forkAttempt A price x` runs the rewinding
reduction `extractReduction A` once at flat price `price` and returns the witness when it
satisfies the relation. By the forking lemma (`winProb_sq_div_sub_le`) it succeeds with
probability at least `forkBound A x = acc² / (qH + 1) − acc / |Ch|`, where `acc` is the
probability that the simulated EUF-CMA game is won on `x`. The extractor that retries the attempt
until it succeeds has expected cost at most `price / forkBound A x`, which is the price times the
use count of `retryCollect` with one success at `p = forkBound A x`.

The price of an attempt is read from the costed tree: `timedCost` reads a query-free costed
adversary as a `CostComp` that charges one unit per sampling node and the step cost of each
continuation, so that its expected cost is at most the tree's time bound and its erasure is the
tree's output distribution. The attempt `forkAttemptTimed` is this reading of the costed
rewinding reduction `extractReduction.timed`; it erases to `forkAttempt`, and the extractor that
retries it has expected cost at most `B / forkBound A x` for the time bound `B` of
`extractReduction.timeBound_timed`.

## Main definitions

* `FiatShamirROM.forkAcc`, `FiatShamirROM.forkBound` — the winning probability of the simulated
  game and the forking lemma's lower bound on the success of one fork;
* `FiatShamirROM.checkW`, `FiatShamirROM.forkAttempt`, `FiatShamirROM.forkExtractor` — one
  priced fork that keeps a valid witness, and the retry loop over it;
* `FiatShamirROM.timedCost`, `FiatShamirROM.stepTimedCost` — the costed reading of a
  query-free costed adversary;
* `FiatShamirROM.forkAttemptTimed`, `FiatShamirROM.forkExtractorTimed` — the attempt read from
  the costed rewinding reduction, and the retry loop over it.

## Main results

* `DNLogic.WDeriv.ecost_retryN_le_mul_wuseCount` — the expected cost of a retry loop is at most
  `C` times the use count of `retryCollect` for one success;
* `DNLogic.WDeriv.ecost_collectN_le_mul_wuseCount` — the same for `m` successes;
* `FiatShamirROM.failProb_forkAttempt`, `FiatShamirROM.failProb_forkAttempt_le` — one fork fails
  with probability at most `1 − forkBound A x`;
* `FiatShamirROM.ecost_forkExtractor_le` — expected cost at most `price / forkBound A x`;
* `FiatShamirROM.ecost_forkExtractor_le_wuseCount` — the same bound as the price times the use
  count of `retryCollect` with one success at `p = forkBound A x`;
* `FiatShamirROM.forkExtractor_sound` — every witness the extractor returns satisfies the
  relation;
* `FiatShamirROM.forkExtractor_timed` — at the price of the time certificate of
  `extractReduction.timed`, the expected cost is at most that time divided by `forkBound A x`;
* `FiatShamirROM.ecost_timedCost_le`, `FiatShamirROM.erase_timedCost` — the costed reading
  costs at most the time bound and erases to the output distribution;
* `FiatShamirROM.erase_forkAttemptTimed` — the attempt read from the costed tree erases to
  `forkAttempt`;
* `FiatShamirROM.ecost_forkExtractorTimed_le_timeBound` — the extractor over the attempt read
  from the costed tree has expected cost at most `B / forkBound A x`.

## References

* M. Bellare, O. Goldreich, *On Defining Proofs of Knowledge*, CRYPTO 1992, §6.
* M. Bellare, G. Neven, *Multi-signatures in the plain public-key model and a general forking
  lemma*, CCS 2006.

Search words: rewinding extractor, expected running time, forking lemma, retry loop, use count,
weighted derivation, Fiat–Shamir, expected cost.
-/

set_option autoImplicit false

@[expose] public section

open scoped NNReal ENNReal

universe u

namespace CatCrypt.Container.DNLogic.WDeriv

open CatCrypt.Core CatCrypt.Unary

variable {I : Type u} {n : ℕ} {Γ : Fin n → Form I}

/-- **The retry loop as one success of `retryCollect`.** A retry loop whose body costs at most `C`
and fails with probability at most `1 - p` has expected cost at most `C` times the expected use
count of the attempt hypothesis in the derivation `retryCollect` with one success. -/
theorem ecost_retryN_le_mul_wuseCount {β : Type} (body : CostComp (Option β)) {C : ℝ≥0∞}
    {p : ℝ≥0} (hp1 : p ≤ 1) (hC : ∀ h, ecost body h ≤ C)
    (hfail : ∀ h, failProb body h ≤ 1 - (p : ℝ≥0∞)) (k : Fin n) {q : ℕ → I → Prop}
    {s : I → Prop} (f : (Γ k).wdn.WHom (Form.atom s).wdn) (hp : p ≠ 0)
    (hf : ∀ i w c, WMeasure.total (f.back i w c) ≤ p⁻¹)
    (hq : ∀ m i, q m i → s i → q (m + 1) i) (base : WDeriv Γ (Form.atom (q 0)))
    (h0 : base.wuseCount k = 0) (N : ℕ) (h : Heap) :
    ecost (retryN body N) h ≤ C * (retryCollect k f p hf hq base 1).wuseCount k := by
  rw [wuseCount_retryCollect_of_zero k f hp hf hq base h0 1, Nat.cast_one, one_mul,
    ← div_eq_mul_inv]
  exact ecost_retryN_le_div body (by exact_mod_cast hp1) hC hfail N h

/-- **The threshold extractor as `m` successes of `retryCollect`.** The extractor `collectN`
collecting `m` successes has expected cost at most `C` times the expected use count of the
attempt hypothesis in `retryCollect` with `m` successes. -/
theorem ecost_collectN_le_mul_wuseCount {β : Type} (body : CostComp (Option β)) {C : ℝ≥0∞}
    {p : ℝ≥0} (hp1 : p ≤ 1) (hC : ∀ h, ecost body h ≤ C)
    (hfail : ∀ h, failProb body h ≤ 1 - (p : ℝ≥0∞)) (k : Fin n) {q : ℕ → I → Prop}
    {s : I → Prop} (f : (Γ k).wdn.WHom (Form.atom s).wdn) (hp : p ≠ 0)
    (hf : ∀ i w c, WMeasure.total (f.back i w c) ≤ p⁻¹)
    (hq : ∀ m i, q m i → s i → q (m + 1) i) (base : WDeriv Γ (Form.atom (q 0)))
    (h0 : base.wuseCount k = 0) (N m : ℕ) (h : Heap) :
    ecost (collectN body N m) h ≤ C * (retryCollect k f p hf hq base m).wuseCount k := by
  rw [wuseCount_retryCollect_of_zero k f hp hf hq base h0 m]
  refine (ecost_collectN_le body (by exact_mod_cast hp1) hC hfail N m h).trans (le_of_eq ?_)
  rw [div_eq_mul_inv]
  ring

end CatCrypt.Container.DNLogic.WDeriv

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Unary
open CatCrypt.Container CatCrypt.Container.DNLogic CatCrypt.Crypto.OracleForking

variable {P : Sigma} {M : Type} [DecidableEq M] {qH qS : ℕ}

/-- The probability that the simulated EUF-CMA game of `A` is won on the statement `x`. -/
noncomputable def forkAcc (A : Adversary P M qH qS) (x : P.Stmt) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle (simStep (G := P.toProtocol M) x)) (withVerify x (A.run x))
    (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true}

/-- The forking lemma's lower bound `acc² / (qH + 1) − acc / |Ch|` on the probability that one
fork of `A` on `x` yields a witness. -/
noncomputable def forkBound (A : Adversary P M qH qS) (x : P.Stmt) : ℝ≥0∞ :=
  forkAcc A x ^ 2 / ((qH + 1 : ℕ) : ℝ≥0∞) - forkAcc A x / Fintype.card P.Ch

open Classical in
/-- The witness `w` when it satisfies the relation on `x`, and `none` otherwise. -/
noncomputable def checkW (x : P.Stmt) (w : P.Wit) : Option P.Wit :=
  if P.rel x w then some w else none

/-- One attempt of the rewinding extractor at flat price `price`: run the rewinding reduction
`extractReduction A` on `x` and keep its output when it is a witness for `x`. -/
noncomputable def forkAttempt (A : Adversary P M qH qS) (price : ℕ) (x : P.Stmt) :
    CostComp (Option P.Wit) :=
  CostComp.lift (liftPMF ((extractReduction A x).map (checkW x))) price

/-- The rewinding extractor: the attempt `forkAttempt A price x` retried at most `N` times,
until it returns a witness. -/
noncomputable def forkExtractor (A : Adversary P M qH qS) (price : ℕ) (x : P.Stmt) (N : ℕ) :
    CostComp (Option P.Wit) :=
  retryN (forkAttempt A price x) N

/-- The weakest preexpectation of a lifted probability mass function is its expectation. -/
theorem wpE_liftPMF {α : Type} (μ : PMF α) (post : α → Heap → ℝ≥0∞) (h : Heap) :
    wpE (liftPMF μ) post h = ∑' a, μ a * post a h := by
  have hl : liftPMF μ h = SDistr.bind (μ.map some) fun a => SDistr.pure (a, h) := by
    unfold liftPMF
    rw [sdistr_bind_map_some]
    rfl
  rw [wpE, hl]
  erw [OrderedMonadAlgebra.wp_bind, wp_sdistr_eq_tsum]
  refine tsum_congr fun a => ?_
  erw [OrderedMonadAlgebra.wp_pure]
  rw [PMF.map_apply, tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp

/-- One fork fails with the probability that the rewinding reduction outputs no witness. -/
theorem failProb_forkAttempt (A : Adversary P M qH qS) (price : ℕ) (x : P.Stmt) (h : Heap) :
    failProb (forkAttempt A price x) h =
      (extractReduction A x).toOuterMeasure {w | ¬ P.rel x w} := by
  simp only [failProb, forkAttempt, CostComp.lift, wpE_bind, wpE_pure, wpE_liftPMF]
  have e : (fun a : Option P.Wit => (PMF.map (checkW x) (extractReduction A x)) a *
      a.elim 1 fun _ => 0) =
      ({none} : Set (Option P.Wit)).indicator (PMF.map (checkW x) (extractReduction A x)) := by
    funext a
    cases a <;> simp
  rw [e, ← PMF.toOuterMeasure_apply, PMF.toOuterMeasure_map_apply]
  congr 1
  ext w
  simp [checkW]

/-- The probabilities of an event and of its complement add up to `1`. -/
theorem toOuterMeasure_compl_add {α : Type} (μ : PMF α) (S : α → Prop) :
    μ.toOuterMeasure {a | ¬ S a} + μ.toOuterMeasure {a | S a} = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add, ← μ.tsum_coe]
  refine tsum_congr fun a => ?_
  by_cases ha : S a <;> simp [Set.indicator, ha]

/-- The rewinding reduction outputs a witness with probability at least `forkBound A x`. -/
theorem forkBound_le_relProb (hSS : P.SpecialSound) (A : Adversary P M qH qS) (x : P.Stmt) :
    forkBound A x ≤ (extractReduction A x).toOuterMeasure {w | P.rel x w} := by
  rw [extractReduction, PMF.toOuterMeasure_map_apply]
  exact winProb_sq_div_sub_le hSS A x

/-- The forking bound is at most `1`. -/
theorem forkBound_le_one (hSS : P.SpecialSound) (A : Adversary P M qH qS) (x : P.Stmt) :
    forkBound A x ≤ 1 :=
  (forkBound_le_relProb hSS A x).trans
    ((toOuterMeasure_compl_add (extractReduction A x) (P.rel x)) ▸ le_add_self)

/-- **One fork fails with probability at most `1 − forkBound A x`.** -/
theorem failProb_forkAttempt_le (hSS : P.SpecialSound) (A : Adversary P M qH qS) (price : ℕ)
    (x : P.Stmt) (h : Heap) :
    failProb (forkAttempt A price x) h ≤ 1 - forkBound A x := by
  have hsum := toOuterMeasure_compl_add (extractReduction A x) (P.rel x)
  have hne : (extractReduction A x).toOuterMeasure {w | P.rel x w} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_add_self)
  rw [failProb_forkAttempt, ENNReal.eq_sub_of_add_eq hne hsum]
  exact tsub_le_tsub_left (forkBound_le_relProb hSS A x) 1


/-- **Expected cost of the rewinding extractor.** Retrying the fork until it yields a witness
costs at most `price / (acc² / (qH + 1) − acc / |Ch|)` in expectation, uniformly in the retry
budget. -/
theorem ecost_forkExtractor_le (hSS : P.SpecialSound) (A : Adversary P M qH qS) (price : ℕ)
    (x : P.Stmt) (N : ℕ) (h : Heap) :
    ecost (forkExtractor A price x N) h ≤ (price : ℝ≥0∞) / forkBound A x :=
  ecost_retryN_le_div _ (forkBound_le_one hSS A x) (fun h' => ecost_lift_le _ _ h')
    (failProb_forkAttempt_le hSS A price x) N h

/-- **The rewinding extractor's expected cost as a use count.** When the forking bound is
positive, the expected cost of the rewinding extractor is at most the price times the expected
use count of the attempt hypothesis in `retryCollect` with one success at
`p = forkBound A x`. -/
theorem ecost_forkExtractor_le_wuseCount (hSS : P.SpecialSound) (A : Adversary P M qH qS)
    (price : ℕ) (x : P.Stmt) (hpos : 0 < forkBound A x) {I : Type u} {n : ℕ}
    {Γ : Fin n → Form I} (k : Fin n) {q : ℕ → I → Prop} {s : I → Prop}
    (f : (Γ k).wdn.WHom (Form.atom s).wdn)
    (hf : ∀ i w c, WMeasure.total (f.back i w c) ≤ (forkBound A x).toNNReal⁻¹)
    (hq : ∀ m i, q m i → s i → q (m + 1) i) (base : WDeriv Γ (Form.atom (q 0)))
    (h0 : base.wuseCount k = 0) (N : ℕ) (h : Heap) :
    ecost (forkExtractor A price x N) h ≤
      price * (WDeriv.retryCollect k f (forkBound A x).toNNReal hf hq base 1).wuseCount k := by
  have hle := forkBound_le_one hSS A x
  have hne : forkBound A x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hcoe : ((forkBound A x).toNNReal : ℝ≥0∞) = forkBound A x := ENNReal.coe_toNNReal hne
  refine WDeriv.ecost_retryN_le_mul_wuseCount _ ?_ (fun h' => ecost_lift_le _ _ h') ?_ k f ?_
    hf hq base h0 N h
  · rw [← ENNReal.coe_le_coe, hcoe]
    exact hle
  · intro h'
    rw [hcoe]
    exact failProb_forkAttempt_le hSS A price x h'
  · exact (ENNReal.toNNReal_pos hpos.ne' hne).ne'

/-- **Soundness of the rewinding extractor.** Every witness the extractor returns with nonzero
probability satisfies the relation on `x`. -/
theorem forkExtractor_sound (A : Adversary P M qH qS) (price : ℕ) (x : P.Stmt) (N : ℕ)
    (h₀ : Heap) (w : P.Wit) (m : ℕ) (h' : Heap)
    (hne : (forkExtractor A price x N h₀) (some ((some w, m), h')) ≠ 0) : P.rel x w := by
  obtain ⟨h₁, m₁, h₂, hbody⟩ := retryN_support_some _ N h₀ w m h' hne
  unfold forkAttempt CostComp.lift at hbody
  obtain ⟨a, h₃, ha, hpa⟩ := spcomp_bind_support hbody
  have ha' : a = some w := by grind [spcomp_pure_support]
  subst ha'
  have hs := (PMF.mem_support_iff _ _).mpr ha
  simp only [liftPMF, PMF.support_map, Set.mem_image, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨a, ha₁, rfl, -⟩ := hs
  obtain ⟨w', -, hw'⟩ := ha₁
  grind [checkW]

/-- **The rewinding extractor at the certified time of one fork.** With `A'` a costed form of
`A` of time `T`, the costed rewinding reduction `extractReduction.timed` has the output
distribution of `extractReduction A` and time at most
`B = 2 * (T + (tV + V * (tV + 1)) + ((tH + tF + 1) * (qH + V) + (tS + 1) * qS)) + tExt`
(`extractReduction.timeBound_timed`), and the extractor that retries the fork at price `B` has
expected cost at most `B / forkBound A x`. -/
theorem forkExtractor_timed (hSS : P.SpecialSound) (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (vkeyCost : (P.toProtocol M).VkeyCost)
    (tV : ℕ) (hV : (P.toProtocol M).VerifyCostLe vkeyCost tV) (tH tS tF tExt : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : P.Stmt) :
    (∀ {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U),
        (OracleAdv.run O' (extractReduction.timed vkeyCost tH tS tF tExt A' x).2.erase u).map
          Prod.fst = extractReduction A x) ∧
      OracleAdv.Timed.StepTimeBound (extractReduction.timed vkeyCost tH tS tF tExt A' x)
        (2 * (T + (tV + (P.toProtocol M).V * (tV + 1)) +
          ((tH + tF + 1) * (qH + (P.toProtocol M).V) + (tS + 1) * qS)) + tExt) ∧
      ∀ (N : ℕ) (h : Heap),
        ecost (forkExtractor A (2 * (T + (tV + (P.toProtocol M).V * (tV + 1)) +
          ((tH + tF + 1) * (qH + (P.toProtocol M).V) + (tS + 1) * qS)) + tExt) x N) h ≤
        ((2 * (T + (tV + (P.toProtocol M).V * (tV + 1)) +
          ((tH + tF + 1) * (qH + (P.toProtocol M).V) + (tS + 1) * qS)) + tExt : ℕ) : ℝ≥0∞) /
          forkBound A x :=
  ⟨fun O' u => extractReduction.run_erase_timed A A' hA vkeyCost tH tS tF tExt O' u x,
    extractReduction.timeBound_timed A hA vkeyCost tV hV tH tS tF tExt hT x,
    fun N h => ecost_forkExtractor_le hSS A _ x N h⟩

/-! ## The attempt read from the costed tree -/

/-- The costed reading of a query-free costed adversary: a `rand` node samples at one unit and
charges the step cost of the continuation taken. -/
noncomputable def timedCost {R α : Type} : OracleAdv.Timed Empty R α → CostComp α
  | .ret a => CostComp.pure a
  | .rand p c k => CostComp.bind (CostComp.lift (liftPMF p) 1) fun b =>
      CostComp.bind (CostComp.charge (c b)) fun _ => timedCost (k b)
  | .query d _ _ => d.elim

/-- The costed reading of a step-prefixed query-free costed adversary: the step cost, then the
costed reading of the tree. -/
noncomputable def stepTimedCost {R α : Type} (x : ℕ × OracleAdv.Timed Empty R α) :
    CostComp α :=
  CostComp.bind (CostComp.charge x.1) fun _ => timedCost x.2

/-- The expected cost of the costed reading is at most a time bound of the tree. -/
theorem ecost_timedCost_le {R α : Type} (A : OracleAdv.Timed Empty R α) {n : ℕ}
    (hA : A.TimeBound n) (h : Heap) : ecost (timedCost A) h ≤ n := by
  induction A generalizing n h with
  | ret a => simp [timedCost]
  | rand p c k ih =>
    have h1 := hA.1
    rw [timedCost]
    refine (ecost_bind_le_add (C₁ := ((1 : ℕ) : ℝ≥0∞)) (C₂ := ((n - 1 : ℕ) : ℝ≥0∞))
      (fun h' => ecost_lift_le _ 1 h') (fun b h' => ?_) h).trans ?_
    · have hb := hA.2 b
      refine (ecost_bind_le_add (C₁ := ((c b : ℕ) : ℝ≥0∞))
        (C₂ := ((n - 1 - c b : ℕ) : ℝ≥0∞)) (fun h'' => (ecost_charge _ _).le)
        (fun _ h'' => ih b hb.2 h'') h').trans ?_
      rw [← Nat.cast_add]
      exact_mod_cast (by omega : c b + (n - 1 - c b) ≤ n - 1)
    · rw [← Nat.cast_add]
      exact_mod_cast (by omega : 1 + (n - 1) ≤ n)
  | query d c k ih => exact d.elim

/-- The expected cost of the costed reading of a step-prefixed tree is at most its step-time
bound. -/
theorem ecost_stepTimedCost_le {R α : Type} (x : ℕ × OracleAdv.Timed Empty R α) {n : ℕ}
    (hx : OracleAdv.Timed.StepTimeBound x n) (h : Heap) : ecost (stepTimedCost x) h ≤ n := by
  have h1 := hx.1
  refine (ecost_bind_le_add (C₁ := ((x.1 : ℕ) : ℝ≥0∞)) (C₂ := ((n - x.1 : ℕ) : ℝ≥0∞))
    (fun h' => (ecost_charge _ _).le) (fun _ h' => ecost_timedCost_le x.2 hx.2 h') h).trans ?_
  rw [← Nat.cast_add]
  exact_mod_cast (by omega : x.1 + (n - x.1) ≤ n)

/-- Erasing the charges of the costed reading gives the output distribution of the erased tree,
lifted to a computation that leaves the heap unchanged. -/
theorem erase_timedCost {R α U : Type} (O' : U → Empty → PMF (R × U)) (u : U)
    (A : OracleAdv.Timed Empty R α) :
    (timedCost A).erase = liftPMF ((OracleAdv.run O' A.erase u).map Prod.fst) := by
  induction A with
  | ret a =>
    rw [timedCost, erase_pure, OracleAdv.Timed.erase, OracleAdv.run_ret, PMF.pure_map,
      liftPMF_pure]
  | rand p c k ih =>
    rw [timedCost, erase_bind_lift, OracleAdv.Timed.erase, OracleAdv.run_rand, PMF.map_bind,
      ← liftPMF_bind_liftPMF]
    congr 1
    funext b
    rw [erase_bind, ← ih b]
    unfold CostComp.charge
    rw [SPComp.pure_bind]
  | query d c k ih => exact d.elim

/-- Erasing the charges of the costed reading of a step-prefixed tree is erasing those of the
tree. -/
theorem erase_stepTimedCost {R α : Type} (x : ℕ × OracleAdv.Timed Empty R α) :
    (stepTimedCost x).erase = (timedCost x.2).erase := by
  unfold stepTimedCost CostComp.charge
  rw [erase_bind, SPComp.pure_bind]

/-- The failure probability of a body depends only on its erasure. -/
theorem failProb_eq_wpE_erase {β : Type} (body : CostComp (Option β)) (h : Heap) :
    failProb body h = wpE body.erase (fun r _ => r.elim 1 fun _ => 0) h := by
  unfold failProb CostComp.erase
  rw [wpE_bind]
  simp only [wpE_pure]

/-- One attempt of the rewinding extractor read from the costed tree: the costed reading of
the costed rewinding reduction `extractReduction.timed`, keeping its output when it is a witness
for `x`. -/
noncomputable def forkAttemptTimed (vkeyCost : (P.toProtocol M).VkeyCost) (tH tS tF tExt : ℕ)
    (A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)) (x : P.Stmt) :
    CostComp (Option P.Wit) :=
  CostComp.bind (stepTimedCost (extractReduction.timed vkeyCost tH tS tF tExt A' x)) fun w =>
    CostComp.pure (checkW x w)

/-- The rewinding extractor whose attempt is read from the costed tree: the attempt
`forkAttemptTimed` retried at most `N` times, until it returns a witness. -/
noncomputable def forkExtractorTimed (vkeyCost : (P.toProtocol M).VkeyCost) (tH tS tF tExt : ℕ)
    (A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)) (x : P.Stmt) (N : ℕ) :
    CostComp (Option P.Wit) :=
  retryN (forkAttemptTimed vkeyCost tH tS tF tExt A' x) N

/-- The attempt read from the costed tree computes the attempt `forkAttempt A price x`: both
erase to the rewinding reduction followed by the witness check. -/
theorem erase_forkAttemptTimed (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (vkeyCost : (P.toProtocol M).VkeyCost)
    (tH tS tF tExt price : ℕ) (x : P.Stmt) :
    (forkAttemptTimed vkeyCost tH tS tF tExt A' x).erase = (forkAttempt A price x).erase := by
  have e : ∀ (c : CostComp P.Wit),
      SPComp.bind c (fun p => (CostComp.pure (checkW x p.1)).erase) =
        SPComp.bind c.erase fun a => SPComp.pure (checkW x a) := by
    intro c
    unfold CostComp.erase
    rw [SPComp.bind_assoc]
    simp only [CostComp.pure, SPComp.pure_bind]
  rw [forkAttemptTimed, erase_bind, e, erase_stepTimedCost,
    erase_timedCost (fun (_ : Unit) d => d.elim) (),
    extractReduction.run_erase_timed A A' hA vkeyCost tH tS tF tExt, liftPMF_bind_pure,
    forkAttempt, erase_lift]

/-- One attempt read from the costed tree fails with probability at most `1 − forkBound A x`. -/
theorem failProb_forkAttemptTimed_le (hSS : P.SpecialSound) (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (vkeyCost : (P.toProtocol M).VkeyCost)
    (tH tS tF tExt : ℕ) (x : P.Stmt) (h : Heap) :
    failProb (forkAttemptTimed vkeyCost tH tS tF tExt A' x) h ≤ 1 - forkBound A x := by
  rw [failProb_eq_wpE_erase, erase_forkAttemptTimed A hA vkeyCost tH tS tF tExt 0,
    ← failProb_eq_wpE_erase]
  exact failProb_forkAttempt_le hSS A 0 x h

/-- **Expected cost of one attempt read from the costed tree.** With `A'` a costed form of `A`
of time `T`, the attempt costs at most the time bound `B` of `extractReduction.timeBound_timed`
in expectation. -/
theorem ecost_forkAttemptTimed_le (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (vkeyCost : (P.toProtocol M).VkeyCost)
    (tV : ℕ) (hV : (P.toProtocol M).VerifyCostLe vkeyCost tV) (tH tS tF tExt : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : P.Stmt) (h : Heap) :
    ecost (forkAttemptTimed vkeyCost tH tS tF tExt A' x) h ≤
      ((2 * (T + (tV + (P.toProtocol M).V * (tV + 1)) +
        ((tH + tF + 1) * (qH + (P.toProtocol M).V) + (tS + 1) * qS)) + tExt : ℕ) : ℝ≥0∞) := by
  refine (ecost_bind_le_add (C₂ := 0)
    (fun h' => ecost_stepTimedCost_le _
      (extractReduction.timeBound_timed A hA vkeyCost tV hV tH tS tF tExt hT x) h')
    (fun _ h' => (ecost_pure _ h').le) h).trans ?_
  rw [add_zero]

/-- **Expected cost of the rewinding extractor from the costed tree.** With `A'` a costed form
of `A` of time `T`, the extractor whose attempt is read from the costed rewinding reduction
`extractReduction.timed` has expected cost at most `B / forkBound A x`, where
`B = 2 * (T + (tV + V * (tV + 1)) + ((tH + tF + 1) * (qH + V) + (tS + 1) * qS)) + tExt` is the
time bound of `extractReduction.timeBound_timed`, uniformly in the retry budget. -/
theorem ecost_forkExtractorTimed_le_timeBound (hSS : P.SpecialSound) (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (vkeyCost : (P.toProtocol M).VkeyCost)
    (tV : ℕ) (hV : (P.toProtocol M).VerifyCostLe vkeyCost tV) (tH tS tF tExt : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : P.Stmt) (N : ℕ) (h : Heap) :
    ecost (forkExtractorTimed vkeyCost tH tS tF tExt A' x N) h ≤
      ((2 * (T + (tV + (P.toProtocol M).V * (tV + 1)) +
        ((tH + tF + 1) * (qH + (P.toProtocol M).V) + (tS + 1) * qS)) + tExt : ℕ) : ℝ≥0∞) /
        forkBound A x :=
  ecost_retryN_le_div _ (forkBound_le_one hSS A x)
    (ecost_forkAttemptTimed_le A hA vkeyCost tV hV tH tS tF tExt hT x)
    (failProb_forkAttemptTimed_le hSS A hA vkeyCost tH tS tF tExt x) N h

end CatCrypt.Crypto.FiatShamirROM

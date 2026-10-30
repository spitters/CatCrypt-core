/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceBad

/-!
# The CPace square with its bad event split

**Ideal functionality.** `F_lePAKE (SPComp.sample K)` (`CatCryptCore.Crypto.PAKE.FPAKESys`), the
lazy-extraction PAKE functionality of Abdalla, Barbosa, Bradley, Jarecki, Katz and Xu
(CRYPTO 2020, Fig. 1).

**Real world.** `cpaceReal G`: CPace for the parties `0` and `1` of the protocol session `0`,
with `H1(pw) = g^{td pw}` for a table `td : Pw → Sˣ` sampled at the first activation and `H2` a
lazily sampled random function (`CatCryptCore.Crypto.PAKE.CPaceSquare`).

**Simulator.** `cpaceSim G`: it programs `H1` with its own table, sends `g^z` for a secret `z`
of each party, and on a delivered message calls `newKey`, `testPwd` with a password extracted
from an earlier `H2` query, or `registerTest`, followed by `lateTestPwd` at a later `H2` query
that extracts a password.

**Bound.** For an environment `Z` with oracle adversary `B = OProt.oracle.reduction Z`, the
distance is at most `cpaceBadBound G B`, the sum of
* the double-match experiment `dmExp G B`,
* the unqueried-match experiment `uqExp G B`,
* the passive-session experiment `psExp G B`,
* the probability `tdCollProb S Pw` that the table of `H1` is not injective, at most
  `|Pw|² / |Sˣ|` (`tdCollProb_le`), and
* the experiment `collStepExp G B` in which a new party's message occurs in an earlier input of
  `H2`.

## Main results

* `uniform_eq_apply_le`: two points of a uniform function into a group coincide with probability
  `1 / |U|`.
* `tdCollProb_le`: the birthday bound for the table of `H1`.
* `collExp_le`: the collision experiment splits into the collision of `H1` and `collStepExp`.
* `cpace_realizesSim`: CPace realizes `F_lePAKE` behind `cpaceSim` with bound `cpaceBadBound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceBound

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FPAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.PAKE.CPaceSquare
open CatCrypt.Crypto.PAKE.CPaceHops CatCrypt.Crypto.PAKE.CPaceBad CatCrypt.NonUniform
open scoped ENNReal

/-! ## Collisions of a uniform function -/

section Collision

variable {Pw U : Type} [Fintype Pw] [DecidableEq Pw] [Group U] [Fintype U]

/-- A function with equal values at `a ≠ b`, and a group element, describe every function: the
value at `b` is the value at `a` times the element. -/
def eqAtEquiv {a b : Pw} (hab : a ≠ b) : {f : Pw → U | f a = f b} × U ≃ (Pw → U) where
  toFun p := Function.update p.1.1 b (p.1.1 a * p.2)
  invFun g := (⟨Function.update g b (g a), by grind [Function.update_of_ne, Function.update_self]⟩,
    (g a)⁻¹ * g b)
  left_inv p := by
    obtain ⟨⟨f, hf⟩, c⟩ := p
    have hf' : f a = f b := hf
    refine Prod.ext (Subtype.ext (funext fun x => ?_)) ?_
    · by_cases hx : x = b
      · subst hx
        simp [Function.update_of_ne hab, hf']
      · simp [Function.update_of_ne hx]
    · simp [Function.update_of_ne hab]
  right_inv g := by
    funext x
    by_cases hx : x = b
    · subst hx
      simp [Function.update_of_ne hab]
    · simp [Function.update_of_ne hx]

/-- **Two points of a uniform function coincide with probability `1 / |U|`.** -/
theorem uniform_eq_apply_le {a b : Pw} (hab : a ≠ b) :
    (PMF.uniformFintype (Pw → U)).toOuterMeasure {f | f a = f b} ≤ (Fintype.card U : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.toOuterMeasure_uniformFintype_apply, ← Fintype.card_congr (eqAtEquiv (U := U) hab),
    Fintype.card_prod]
  have hu : (Fintype.card U : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ENNReal.div_le_of_le_mul ?_
  rw [Nat.cast_mul, mul_comm (_ : ℝ≥0∞) (Fintype.card U : ℝ≥0∞), ← mul_assoc,
    ENNReal.inv_mul_cancel hu (ENNReal.natCast_ne_top _), one_mul]

/-- **The birthday bound for a uniform function**: it is not injective with probability at most
`|Pw|² / |U|`. -/
theorem uniform_not_injective_le :
    (PMF.uniformFintype (Pw → U)).toOuterMeasure {f | ¬ Function.Injective f} ≤
      ((Fintype.card Pw ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card U := by
  have hsub : {f : Pw → U | ¬ Function.Injective f} ⊆
      ⋃ p ∈ (Finset.univ : Finset Pw).offDiag, {f | f p.1 = f p.2} := by
    intro f hf
    simp only [Function.Injective, Set.mem_ofPred_eq, not_forall] at hf
    obtain ⟨x, y, hxy, hne⟩ := hf
    simp only [Set.mem_iUnion, Finset.mem_offDiag, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨(x, y), hne, hxy⟩
  calc _ ≤ _ := MeasureTheory.measure_mono hsub
    _ ≤ ∑ p ∈ (Finset.univ : Finset Pw).offDiag,
        (PMF.uniformFintype (Pw → U)).toOuterMeasure {f | f p.1 = f p.2} :=
      MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ (Finset.univ : Finset Pw).offDiag, (Fintype.card U : ℝ≥0∞)⁻¹ :=
      Finset.sum_le_sum fun p hp => uniform_eq_apply_le (Finset.mem_offDiag.1 hp).2.2
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      gcongr
      rw [Finset.offDiag_card, Finset.card_univ, sq]
      exact Nat.sub_le _ _

end Collision

/-! ## The bound -/

section Bound

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

variable (S Pw) in
/-- The probability that the table of `H1` is not injective. -/
noncomputable def tdCollProb : ℝ≥0∞ :=
  (PMF.uniformFintype (Pw → Sˣ)).toOuterMeasure {td | TdColl td}

/-- **The new-message collision experiment.** -/
noncomputable def collStepExp (B : OracleAdv (OEv Pw W) (OOut W K) Bool) : PMF Bool :=
  flagExp G (fun _ s s' => CollStep G s s') B

/-- **The birthday bound for the table of `H1`.** -/
theorem tdCollProb_le :
    tdCollProb S Pw ≤ ((Fintype.card Pw ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card Sˣ := by
  classical
  exact uniform_not_injective_le

/-- **The collision experiment splits** into the collision of `H1` and the new-message
collision experiment. -/
theorem collExp_le (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    collExp G B true ≤ tdCollProb S Pw + collStepExp G B true := by
  classical
  unfold collExp collStepExp flagExp tdCollProb
  rw [PMF.bind_apply, PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun td => ?_
  simp only [map_flag_apply]
  by_cases h : TdColl td
  · rw [Set.indicator_of_mem h]
    calc _ ≤ PMF.uniformFintype (Pw → Sˣ) td * 1 := by
          gcongr
          exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
            ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
      _ ≤ _ := by rw [mul_one]; exact le_self_add
  · rw [Set.indicator_of_notMem h, zero_add]
    exact mul_le_mul_right ((congrArg (fun p => PMF.toOuterMeasure p _)
      (run_flagWhen_inst _ _ _ _ _ _)).trans_le <| (run_flagWhen_mono (jointSim G td)
      (fun s _ x => TdColl td ∨ CollStep G s.1 x.2.1) (fun s _ x => CollStep G s.1 x.2.1)
      (fun _ _ _ hb => Or.resolve_left hb h) B _).trans_eq
      (congrArg (fun p => PMF.toOuterMeasure p _) (run_flagWhen_inst _ _ _ _ _ _))) _

/-- The bound of the CPace square at the oracle adversary `B`. -/
noncomputable def cpaceBadBound (B : OracleAdv (OEv Pw W) (OOut W K) Bool) : ℝ≥0∞ :=
  dmExp G B true + uqExp G B true + psExp G B true + (tdCollProb S Pw + collStepExp G B true)

/-- **CPace realizes `F_lePAKE` behind `cpaceSim`** (genuine UC). For every environment `Z`,
the distance between the real CPace protocol and the simulator running with `F_lePAKE` is at
most `cpaceBadBound G B` at the oracle adversary `B = OProt.oracle.reduction Z`: the
probabilities of a double match, an unqueried match, a passive-session query, a collision of
`H1` and a new-message collision. -/
theorem cpace_realizesSim :
    RealizesSim (cpaceReal G (K := K)) (F_lePAKE (Pw := Pw) (SPComp.sample K)) (cpaceSim G)
      (fun _ Z => cpaceBadBound G ((OProt.oracle (Q := OEv Pw W) (A := OOut W K)).reduction Z)) :=
  fun ζ Z => (cpace_realizesSim_oracleGame G ζ Z).trans ((advantage_le_badGame G _).trans
    ((badGame_le G _).trans (by
      dsimp only [cpaceBadBound]
      gcongr
      exact collExp_le G _)))

end Bound

end CatCrypt.Crypto.PAKE.CPaceBound

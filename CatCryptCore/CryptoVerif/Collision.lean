/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.CryptoVerif.Event

/-!
# Collision elimination in CryptoVerif's `simplify`

CryptoVerif's `simplify` removes a test `g r = y` when `r` is a random value and `y` is
independent of `r`, at the cost of the probability that the test holds: the supremum over `y`
of the probability that `g r = y`, times the number of tests. Here the random value is the key
of a keyed game whose oracle answers the test; the other side of the transformation answers
`false`. Every query value is a function of the earlier answers, so it is independent of `r`
as long as every earlier test failed.

## Main results

* `collProb` — the collision probability `⨆ y, Pr[g r = y]`.
* `collReal`, `collIdeal` — the keyed game of the test and the game that answers `false`.
* `advantage_collReal_le` — the advantage of a `q`-query adversary between the two games is at
  most `q * collProb μ g`.
* `simplify_coll` — the rule: a game factored through the tests is indistinguishable from the
  game with the tests replaced by `false`, with bound the number of tests times `collProb μ g`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CryptoVerifLogic

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {α β : Type}

/-- The collision probability of `g` under `μ`: the supremum over `y` of the probability that
`g r = y`, for `r` drawn from `μ`. -/
noncomputable def collProb (μ : PMF α) (g : α → β) : ℝ≥0∞ :=
  ⨆ y, (μ.map g) y

/-- The probability of each value of `g r` is at most the collision probability. -/
theorem map_apply_le_collProb (μ : PMF α) (g : α → β) (y : β) :
    (μ.map g) y ≤ collProb μ g :=
  le_iSup (fun y => (μ.map g) y) y

variable [DecidableEq β]

/-- The keyed game of the test: the key is `r` drawn from `μ`, and the query `y` is answered by
whether `g r = y`. -/
noncomputable def collReal (μ : PMF α) (g : α → β) : KeyedGame β Bool where
  Key := α
  State := Unit
  keyDist := μ
  oracle r _ y := PMF.pure (decide (g r = y), ())
  init := ()

variable (β) in
/-- The keyed game in which the test always fails. -/
noncomputable def collIdeal : KeyedGame β Bool where
  Key := Unit
  State := Unit
  keyDist := PMF.pure ()
  oracle _ _ _ := PMF.pure (false, ())
  init := ()

/-- The probability that `B` outputs `true` against the test with the fixed `r`. -/
private noncomputable def accR (g : α → β) (r : α) (B : OracleAdv β Bool Bool) : ℝ≥0∞ :=
  (OracleAdv.run (fun (_ : Unit) y => PMF.pure (decide (g r = y), ())) B ()).map Prod.fst true

/-- The probability that `B` outputs `true` when every test fails. -/
private noncomputable def accI (B : OracleAdv β Bool Bool) : ℝ≥0∞ :=
  (OracleAdv.run (fun (_ : Unit) (_ : β) => PMF.pure (false, ())) B ()).map Prod.fst true

private theorem accR_query (g : α → β) (r : α) (d : β) (k : Bool → OracleAdv β Bool Bool) :
    accR g r (.query d k) = accR g r (k (decide (g r = d))) := by
  simp [accR, OracleAdv.run_query, PMF.pure_bind]

omit [DecidableEq β] in
private theorem accI_query (d : β) (k : Bool → OracleAdv β Bool Bool) :
    accI (.query d k) = accI (k false) := by
  simp [accI, OracleAdv.run_query, PMF.pure_bind]

private theorem accR_rand (g : α → β) (r : α) {γ : Type} (p : PMF γ)
    (k : γ → OracleAdv β Bool Bool) :
    accR g r (.rand p k) = ∑' b, p b * accR g r (k b) := by
  simp [accR, OracleAdv.run_rand, PMF.map_bind, PMF.bind_apply]

omit [DecidableEq β] in
private theorem accI_rand {γ : Type} (p : PMF γ) (k : γ → OracleAdv β Bool Bool) :
    accI (.rand p k) = ∑' b, p b * accI (k b) := by
  simp [accI, OracleAdv.run_rand, PMF.map_bind, PMF.bind_apply]

private theorem accR_le_one (g : α → β) (r : α) (B : OracleAdv β Bool Bool) : accR g r B ≤ 1 :=
  PMF.coe_le_one _ _

/-- An average over `r` of the event `g r = y` is the probability of `y` under the map. -/
private theorem tsum_ind (μ : PMF α) (g : α → β) (y : β) :
    (∑' r, μ r * if g r = y then (1 : ℝ≥0∞) else 0) = (μ.map g) y := by
  rw [PMF.map_apply]
  exact tsum_congr fun r => by
    by_cases h : g r = y
    · simp [h]
    · have : ¬ y = g r := fun h' => h h'.symm
      simp [h, this]

/-- Both comparisons between a `q`-query adversary against the test and against the failing
test, by induction on the adversary. -/
private theorem accR_accI_le (μ : PMF α) (g : α → β) (B : OracleAdv β Bool Bool) :
    ∀ q, B.IsQueryBound q →
      ((∑' r, μ r * accR g r B) ≤ accI B + q * collProb μ g) ∧
        (accI B ≤ (∑' r, μ r * accR g r B) + q * collProb μ g) := by
  induction B with
  | ret b =>
    intro q _
    have h1 : ∀ r, accR g r (.ret b : OracleAdv β Bool Bool) =
        accI (.ret b : OracleAdv β Bool Bool) := fun r => by simp [accR, accI]
    simp only [h1, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    exact ⟨le_self_add, le_self_add⟩
  | rand p k ih =>
    intro q hq
    have hswap : (∑' r, μ r * accR g r (.rand p k)) =
        ∑' b, p b * ∑' r, μ r * accR g r (k b) := by
      simp only [accR_rand, ← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      exact tsum_congr fun b => tsum_congr fun r => by ring
    have hscale : ∀ c : ℝ≥0∞, (∑' b, p b * c) = c := fun c => by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    constructor
    · rw [hswap, accI_rand, ← hscale (_ * _)]
      refine (ENNReal.tsum_le_tsum fun b => ?_ :
        _ ≤ ∑' b, p b * (accI (k b) + q * collProb μ g)).trans ?_
      · gcongr; exact (ih b q (hq b)).1
      simp only [mul_add, ENNReal.tsum_add, hscale]
      exact le_refl _
    · rw [hswap, accI_rand, ← hscale (_ * _)]
      refine (ENNReal.tsum_le_tsum fun b => ?_ :
        _ ≤ ∑' b, p b * ((∑' r, μ r * accR g r (k b)) + q * collProb μ g)).trans ?_
      · gcongr; exact (ih b q (hq b)).2
      simp only [mul_add, ENNReal.tsum_add, hscale]
      exact le_refl _
  | query d k ih =>
    intro q hq
    rcases q with _ | q
    · exact hq.elim
    obtain ⟨ih₁, ih₂⟩ := ih false q (hq false)
    have hstep₁ : ∀ r, accR g r (.query d k) ≤ accR g r (k false) +
        if g r = d then (1 : ℝ≥0∞) else 0 := fun r => by
      rw [accR_query]
      by_cases h : g r = d
      · simpa [h] using accR_le_one g r (k true) |>.trans le_add_self
      · simp [h]
    have hstep₂ : ∀ r, accR g r (k false) ≤ accR g r (.query d k) +
        if g r = d then (1 : ℝ≥0∞) else 0 := fun r => by
      rw [accR_query]
      by_cases h : g r = d
      · simpa [h] using accR_le_one g r (k false) |>.trans le_add_self
      · simp [h]
    have hsum₁ : (∑' r, μ r * accR g r (.query d k)) ≤
        (∑' r, μ r * accR g r (k false)) + (μ.map g) d := by
      rw [← tsum_ind μ g d, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun r => by
        rw [← mul_add]
        gcongr
        exact hstep₁ r
    have hsum₂ : (∑' r, μ r * accR g r (k false)) ≤
        (∑' r, μ r * accR g r (.query d k)) + (μ.map g) d := by
      rw [← tsum_ind μ g d, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun r => by
        rw [← mul_add]
        gcongr
        exact hstep₂ r
    have hp := map_apply_le_collProb μ g d
    have hcast : ((q + 1 : ℕ) : ℝ≥0∞) * collProb μ g = q * collProb μ g + collProb μ g := by
      push_cast; ring
    rw [accI_query, hcast]
    constructor
    · calc _ ≤ (∑' r, μ r * accR g r (k false)) + collProb μ g := hsum₁.trans (by gcongr)
        _ ≤ (accI (k false) + q * collProb μ g) + collProb μ g := by gcongr
        _ = _ := by ring
    · calc accI (k false) ≤ (∑' r, μ r * accR g r (k false)) + q * collProb μ g := ih₂
        _ ≤ ((∑' r, μ r * accR g r (.query d k)) + collProb μ g) + q * collProb μ g := by
            gcongr; exact hsum₂.trans (by gcongr)
        _ = _ := by ring

/-- **Collision bound.** For an adversary asking at most `q` tests, the advantage between the
test game and the failing game is at most `q` times the collision probability. -/
theorem advantage_collReal_le (μ : PMF α) (g : α → β) (B : OracleAdv β Bool Bool) (q : ℕ)
    (hq : B.IsQueryBound q) :
    KeyedGame.advantage (collReal μ g) (collIdeal β) B ≤ q * collProb μ g := by
  obtain ⟨h₁, h₂⟩ := accR_accI_le μ g B q hq
  have hL : (collReal μ g).accept B = ∑' r, μ r * accR g r B := by
    simp [KeyedGame.accept, collReal, PMF.bind_apply, accR]
  have hR : (collIdeal β).accept B = accI B := by
    simp [KeyedGame.accept, collIdeal, accI]
  rw [KeyedGame.advantage, hL, hR]
  exact max_le (tsub_le_iff_left.2 h₁) (tsub_le_iff_left.2 h₂)

variable {I : CvIface}

/-- **CryptoVerif's collision elimination.** If the game `G` is the protocol `P` over the test
game, `G'` is `P` over the failing game, and `P` asks at most `m ζ Z` tests in a run of `Z`,
then `G ≈ G'` with bound `m ζ Z * collProb μ g`. -/
theorem simplify_coll {τ : Type} {G G' : CvGame I} (P : OProt τ (CvCall I) (CvOut I) β Bool)
    (μ : PMF α) (g : α → β)
    (hL : Realizes G.sys (P.sys (collReal μ g)) fun _ _ => 0)
    (hR : Realizes (P.sys (collIdeal β)) G'.sys fun _ _ => 0)
    (m : (ζ : Type) → Env (Strat ζ (CvCall I) (CvOut I)) ζ → ℕ)
    (hm : ∀ ζ Z, (P.reduction Z).IsQueryBound (m ζ Z)) :
    Realizes G.sys G'.sys fun ζ Z => (m ζ Z : ℝ≥0∞) * collProb μ g :=
  fun ζ => ((hL.trans (Realizes.ofOracleGame P _ _)).trans hR ζ).mono fun Z => by
    simpa only [zero_add, add_zero] using advantage_collReal_le μ g (P.reduction Z) _ (hm ζ Z)

end CatCrypt.Crypto.CryptoVerifLogic

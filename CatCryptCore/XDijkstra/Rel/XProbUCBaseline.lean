/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.Rel.XRelQ0
public import CatCryptCore.Crypto.UCMonad.SDistrInstance
public import CatCryptCore.Relational.Approx


@[expose] public section
set_option autoImplicit false

/-!
# The probabilistic baseline rows: statistical UC on `SDistr`, perfect UC on `PMF`

The graded relational coupling `XRelTripleQ0` (`XRelQ0.lean`) reads, on the two
probabilistic carriers, as the two classical universal-composability regimes:

* **`SDistr` — statistical UC.** At the equality relation the grade-`ε` coupling
  `XRelTripleQ0 (T := SDistr) ε (· = ·) d₁ d₂` is the two-sided statistical-distance
  bound `tvMargin d₁ d₂ ≤ ε ∧ tvMargin d₂ d₁ ≤ ε` (`sdistr_uc_iff_tvMargin`); and it
  bounds the distinguishing advantage `sdistD (const d₁) (const d₂) ≤ ε`
  (`sdistr_uc_le_advantage`). The grade is Canetti's `ε`.

* **`PMF` — perfect UC.** The grade-`0` coupling `XRelTripleQ0 (T := PMF) 0 (· = ·) μ ν`
  holds iff the two distributions are equal (`pmf_uc_zero_iff_eq`): perfect UC is exact
  distribution equality.

* **`SDistr` at grade `0` — perfect statistical UC.** At `ε = 0` the statistical distance
  vanishes and the coupling collapses to equality of sub-distributions
  (`sdistr_uc_zero_iff_eq`).

## Principal declarations

* `advantage_le_tvMargin` — a distinguisher's `d₁`-average exceeds its `d₂`-average by at
  most the one-sided statistical distance `tvMargin d₁ d₂`.
* `sdistr_uc_iff_tvMargin` — the `SDistr` coupling at grade `ε` is the two-sided
  statistical-distance bound.
* `sdistr_uc_le_advantage` — the coupling at grade `ε` bounds the Kleisli distinguishing
  advantage `sdistD` by `ε`.
* `pmf_uc_zero_iff_eq` — the `PMF` grade-`0` coupling is distribution equality.
* `sdistr_uc_zero_iff_eq` — the `SDistr` grade-`0` coupling is sub-distribution equality.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob
open UCMonad.SDistrUC

/-! ## 1. `SDistr` is statistical UC

On the crypto sub-distribution monad the grade-`ε` coupling `XRelTripleQ0` at the equality
relation is `liftRApprox ε Eq` (`instRelQ0SDistr`), which the sub-coupling machinery
identifies with the two-sided statistical distance. That is the statistical-UC advantage:
the grade is the coupling error, and it bounds every distinguisher's advantage. -/

/-- **The `SDistr` coupling at grade `ε` is the two-sided statistical-distance bound.** At
the equality relation, `XRelTripleQ0 (T := SDistr) ε (· = ·) d₁ d₂` holds iff both
one-sided statistical distances are at most `ε`. The grade `ε` is the statistical distance
— Canetti's `ε` for statistical UC. -/
theorem sdistr_uc_iff_tvMargin {α : Type} {ε : ℝ≥0∞} {d₁ d₂ : SDistr α} :
    XRelTripleQ0 (T := SDistr) ε Eq d₁ d₂ ↔ tvMargin d₁ d₂ ≤ ε ∧ tvMargin d₂ d₁ ≤ ε :=
  ⟨tvMargin_le_of_liftRApprox_eq, fun ⟨hl, hr⟩ => liftRApprox_eq_of_tv hl hr⟩

/-- **A distinguisher-average bound from statistical distance.** For any `[0,1]`-valued
weight `v` (a distinguisher's acceptance probability), the `d₁`-average of `v` exceeds the
`d₂`-average by at most the one-sided statistical distance `tvMargin d₁ d₂`. -/
theorem advantage_le_tvMargin {α : Type} (d₁ d₂ : SDistr α) (v : α → ℝ≥0∞)
    (hv : ∀ a, v a ≤ 1) :
    (∑' a, d₁ (some a) * v a) ≤ (∑' a, d₂ (some a) * v a) + tvMargin d₁ d₂ := by
  have key : ∀ a, d₁ (some a) * v a
      ≤ d₂ (some a) * v a + (d₁ (some a) - d₂ (some a)) := by
    intro a
    calc d₁ (some a) * v a
        ≤ ((d₁ (some a) - d₂ (some a)) + d₂ (some a)) * v a := by
          gcongr
          exact le_tsub_add
      _ = (d₁ (some a) - d₂ (some a)) * v a + d₂ (some a) * v a := by rw [add_mul]
      _ ≤ (d₁ (some a) - d₂ (some a)) * 1 + d₂ (some a) * v a := by gcongr; exact hv a
      _ = d₂ (some a) * v a + (d₁ (some a) - d₂ (some a)) := by rw [mul_one, add_comm]
  calc (∑' a, d₁ (some a) * v a)
      ≤ ∑' a, (d₂ (some a) * v a + (d₁ (some a) - d₂ (some a))) := ENNReal.tsum_le_tsum key
    _ = (∑' a, d₂ (some a) * v a) + ∑' a, (d₁ (some a) - d₂ (some a)) := ENNReal.tsum_add
    _ = (∑' a, d₂ (some a) * v a) + tvMargin d₁ d₂ := rfl

/-- The Kleisli statistical distance of two constant arrows is the distinguisher supremum
of the acceptance-probability gaps of the two distributions. -/
theorem sdistD_const {α : Type} (d₁ d₂ : SDistr α) :
    sdistD (fun _ : Unit => d₁) (fun _ : Unit => d₂)
      = ⨆ D : α → SDistr Bool,
          absDiffD (prTrueD (SDistr.bind d₁ D)) (prTrueD (SDistr.bind d₂ D)) := by
  simp only [sdistD, iSup_const]

/-- The `true`-probability of `d >>= D` is the `d`-average of the distinguisher's
acceptance probability. -/
theorem prTrueD_bind {α : Type} (d : SDistr α) (D : α → SDistr Bool) :
    prTrueD (SDistr.bind d D) = ∑' a, d (some a) * (D a) (some true) := by
  simp only [prTrueD]
  rw [SDistr.bind_apply_some]

/-- **The `SDistr` coupling at grade `ε` bounds the distinguishing advantage.** From the
grade-`ε` equality coupling of `d₁`, `d₂`, the Kleisli statistical distance
`sdistD (const d₁) (const d₂)` — the supremum over distinguishers of the
acceptance-probability gap — is at most `ε`. This is statistical UC: the coupling error
bounds every adversary's advantage. -/
theorem sdistr_uc_le_advantage {α : Type} {ε : ℝ≥0∞} {d₁ d₂ : SDistr α}
    (h : XRelTripleQ0 (T := SDistr) ε Eq d₁ d₂) :
    sdistD (fun _ : Unit => d₁) (fun _ : Unit => d₂) ≤ ε := by
  obtain ⟨h12, h21⟩ := tvMargin_le_of_liftRApprox_eq h
  rw [sdistD_const]
  refine iSup_le fun D => ?_
  have hv : ∀ a, (D a) (some true) ≤ 1 := fun a => PMF.coe_le_one (D a) (some true)
  have key12 : prTrueD (SDistr.bind d₁ D) ≤ prTrueD (SDistr.bind d₂ D) + ε := by
    rw [prTrueD_bind, prTrueD_bind]
    have hadv := advantage_le_tvMargin d₁ d₂ (fun a => (D a) (some true)) hv
    exact le_trans hadv (by gcongr)
  have key21 : prTrueD (SDistr.bind d₂ D) ≤ prTrueD (SDistr.bind d₁ D) + ε := by
    rw [prTrueD_bind, prTrueD_bind]
    have hadv := advantage_le_tvMargin d₂ d₁ (fun a => (D a) (some true)) hv
    exact le_trans hadv (by gcongr)
  simp only [absDiffD]
  refine sup_le ?_ ?_
  · exact tsub_le_iff_right.mpr (le_trans key12 (le_of_eq (add_comm _ _)))
  · exact tsub_le_iff_right.mpr (le_trans key21 (le_of_eq (add_comm _ _)))

/-! ## 2. `PMF` is perfect UC

On Mathlib's probability monad the grade is carried vacuously and the coupling is the
qualitative `Couples`. A coupling of `μ` and `ν` for equality concentrates on the
diagonal, forcing `μ = ν`; conversely the diagonal coupling witnesses `Couples μ μ`. So
the grade-`0` coupling is exact distribution equality — perfect UC. -/

/-- **An equality coupling forces distribution equality.** A coupling of `μ` and `ν`
supported on the diagonal has equal marginals, so `μ = ν`. -/
theorem Couples_eq_imp_eq {α : Type} {μ ν : PMF α} (h : Couples μ ν (· = ·)) : μ = ν := by
  obtain ⟨κ, hκ⟩ := h
  rw [← hκ.marg_fst, ← hκ.marg_snd]
  refine PMF.ext fun x => ?_
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun p => ?_
  by_cases hp : κ p = 0
  · simp [hp]
  · have hpp : p.1 = p.2 := hκ.supp p (PMF.mem_support_iff κ p |>.mpr hp)
    rw [hpp]

/-- **Perfect UC on `PMF` is distribution equality.** The grade-`0` coupling
`XRelTripleQ0 (T := PMF) 0 (· = ·) μ ν` holds iff `μ = ν`. Perfect UC is exact equality of
the two distributions. -/
theorem pmf_uc_zero_iff_eq {α : Type} {μ ν : PMF α} :
    XRelTripleQ0 (T := PMF) 0 (· = ·) μ ν ↔ μ = ν := by
  rw [← couples_iff_xrelQ0_zero]
  exact ⟨Couples_eq_imp_eq, by rintro rfl; exact Couples_same μ⟩

/-! ## 3. `SDistr` at grade `0` — perfect statistical UC

At grade `0` both one-sided statistical distances vanish, so the two sub-distributions
agree on every outcome; total-mass-one forces agreement on the failure mass too. Grade-`0`
statistical UC is sub-distribution equality. -/

/-- One-sided statistical distance of a sub-distribution from itself is `0`. -/
private theorem tvMargin_self {α : Type} (d : SDistr α) : tvMargin d d = 0 := by
  simp only [tvMargin, tsub_self, tsum_zero]

/-- **Perfect statistical UC is sub-distribution equality.** The grade-`0` `SDistr`
coupling `XRelTripleQ0 (T := SDistr) 0 (· = ·) d₁ d₂` holds iff `d₁ = d₂` — the `ε = 0`
collapse of statistical UC, at which the statistical distance separates points. -/
theorem sdistr_uc_zero_iff_eq {α : Type} {d₁ d₂ : SDistr α} :
    XRelTripleQ0 (T := SDistr) 0 Eq d₁ d₂ ↔ d₁ = d₂ := by
  rw [sdistr_uc_iff_tvMargin]
  constructor
  · rintro ⟨h12, h21⟩
    refine SDistr.eq_of_some_eq fun a => ?_
    have z12 : ∑' a, (d₁ (some a) - d₂ (some a)) = 0 := nonpos_iff_eq_zero.mp h12
    have z21 : ∑' a, (d₂ (some a) - d₁ (some a)) = 0 := nonpos_iff_eq_zero.mp h21
    have le12 : d₁ (some a) ≤ d₂ (some a) :=
      tsub_eq_zero_iff_le.mp (ENNReal.tsum_eq_zero.mp z12 a)
    have le21 : d₂ (some a) ≤ d₁ (some a) :=
      tsub_eq_zero_iff_le.mp (ENNReal.tsum_eq_zero.mp z21 a)
    exact le_antisymm le12 le21
  · rintro rfl
    exact ⟨(tvMargin_self d₁).le, (tvMargin_self d₁).le⟩

end CatCrypt.XDijkstra

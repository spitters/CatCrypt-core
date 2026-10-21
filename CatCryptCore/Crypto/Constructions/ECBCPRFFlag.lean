/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# Flagged outcomes, oracle-run supports and uniform resampling

Probability lemmas of the ECBC-MAC PRF proof that do not mention block ciphers or
CBC chains.

## Main results

* `uniform_bind_update` — resampling one coordinate of a uniform function leaves
  it uniform
* `toOuterMeasure_flag_eq`, `toOuterMeasure_le_add_flag` — identical-until-bad on
  distributions over flagged outcomes
* `run_support_rel` — a reflexive, transitive relation preserved by every oracle
  transition holds between the initial and every reachable final state
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.ECBCPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

section Uniform

variable {D R : Type}

/-- Resampling one coordinate of a uniform function leaves it uniform. -/
theorem uniform_bind_update [DecidableEq D] [Fintype D] [Fintype R] [Nonempty R] (d : D) :
    (PMF.uniformOfFintype (D → R)).bind
        (fun f => (PMF.uniformOfFintype R).map (Function.update f d)) =
      PMF.uniformOfFintype (D → R) := by
  classical
  ext g
  simp only [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  have hcount : ∀ f : D → R, (∑ r : R, if g = Function.update f d r then
      ((Fintype.card R : ℝ≥0∞))⁻¹ else 0) =
      if g = Function.update f d (g d) then ((Fintype.card R : ℝ≥0∞))⁻¹ else 0 := by
    intro f
    rw [Finset.sum_eq_single (g d)]
    · intro r _ hr
      rw [if_neg]
      rintro rfl
      exact hr (by simp)
    · simp
  simp only [hcount, ← Finset.mul_sum]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun f : D → R => g = Function.update f d (g d)).card =
      Fintype.card R := by
    rw [← Finset.card_univ (α := R)]
    refine (Finset.card_image_of_injective _ (Function.update_injective g d)).symm.trans ?_ |>.symm
    congr 1
    ext f
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨s, rfl⟩; simp
    · intro h; exact ⟨f d, by rw [h]; simp⟩
  rw [hcard]
  have hN0 : (Fintype.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_comm (Fintype.card R : ℝ≥0∞), ENNReal.inv_mul_cancel hN0
    (ENNReal.natCast_ne_top _), mul_one]

end Uniform

/-! ## Flagged outcomes and supports -/

section Flag

theorem toOuterMeasure_eq_of_subset_false {α σ : Type} (p₁ p₂ : PMF (α × (σ × Bool)))
    (h : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false))) (S : Set (α × (σ × Bool)))
    (hS : ∀ x ∈ S, x.2.2 = false) : p₁.toOuterMeasure S = p₂.toOuterMeasure S := by
  simp only [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ S
  · obtain ⟨a, t, b⟩ := x
    have hb : b = false := hS _ hx
    subst hb
    simp only [Set.indicator_of_mem hx, h]
  · simp only [Set.indicator_of_notMem hx]

theorem toOuterMeasure_add_compl {α : Type} (p : PMF α) (S : Set α) :
    p.toOuterMeasure S + p.toOuterMeasure Sᶜ = 1 := by
  simp only [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add]
  simp only [Set.indicator_self_add_compl_apply, PMF.tsum_coe]

/-- Two distributions that agree on every outcome with the flag cleared give the
flag the same probability. -/
theorem toOuterMeasure_flag_eq {α σ : Type} (p₁ p₂ : PMF (α × (σ × Bool)))
    (h : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false))) :
    p₁.toOuterMeasure {x | x.2.2 = true} = p₂.toOuterMeasure {x | x.2.2 = true} := by
  have hG := toOuterMeasure_eq_of_subset_false p₁ p₂ h {x | x.2.2 = false} fun x hx => hx
  have hc : ({x | x.2.2 = false} : Set (α × (σ × Bool)))ᶜ = {x | x.2.2 = true} := by
    ext x; simp
  have h₁ := toOuterMeasure_add_compl p₁ {x | x.2.2 = false}
  have h₂ := toOuterMeasure_add_compl p₂ {x | x.2.2 = false}
  rw [hc] at h₁ h₂
  rw [hG] at h₁
  have hne : p₂.toOuterMeasure {x | x.2.2 = false} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (h₂ ▸ le_self_add)
  exact (ENNReal.add_right_inj hne).mp (h₁.trans h₂.symm)

/-- **Identical until bad, on probabilities.** For distributions that agree on
every outcome with the flag cleared, the probability of an output event under the
first is at most its probability under the second plus the flag probability. -/
theorem toOuterMeasure_le_add_flag {α σ : Type} (p₁ p₂ : PMF (α × (σ × Bool)))
    (h : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false))) (A : Set α) :
    p₁.toOuterMeasure {x | x.1 ∈ A} ≤
      p₂.toOuterMeasure {x | x.1 ∈ A} + p₂.toOuterMeasure {x | x.2.2 = true} := by
  refine (MeasureTheory.measure_le_inter_add_sdiff p₁.toOuterMeasure {x | x.1 ∈ A}
    {x | x.2.2 = false}).trans (add_le_add ?_ ?_)
  · rw [toOuterMeasure_eq_of_subset_false p₁ p₂ h _ fun x hx => hx.2]
    exact MeasureTheory.measure_mono Set.inter_subset_left
  · rw [← toOuterMeasure_flag_eq p₁ p₂ h]
    refine MeasureTheory.measure_mono fun x hx => ?_
    simpa using hx.2

variable {D R α : Type}

/-- A relation between oracle states that is reflexive, transitive and holds across
every oracle transition holds between the initial and every reachable final state. -/
theorem run_support_rel {S : Type} (O : S → D → PMF (R × S)) (Rel : S → S → Prop)
    (hrefl : ∀ s, Rel s s) (htrans : ∀ a b c, Rel a b → Rel b c → Rel a c)
    (hstep : ∀ s d x, x ∈ (O s d).support → Rel s x.2) (A : OracleAdv D R α) (s : S) :
    ∀ x ∈ (OracleAdv.run O A s).support, Rel s x.2 := by
  induction A generalizing s with
  | ret a =>
    intro x hx
    simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hrefl s
  | rand p k ih =>
    intro x hx
    simp only [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ih b s x hb
  | query d k ih =>
    intro x hx
    simp only [OracleAdv.run_query, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact htrans _ _ _ (hstep s d y hy) (ih y.1 y.2 x hxy)

theorem tsum_pure_mul {β : Type} (y : β) (g : β → ℝ≥0∞) :
    ∑' x, (PMF.pure y) x * g x = g y := by
  rw [tsum_eq_single y fun b hb => by simp [PMF.pure_apply, hb]]
  simp

end Flag

end CatCrypt.Crypto.Constructions.ECBCPRF

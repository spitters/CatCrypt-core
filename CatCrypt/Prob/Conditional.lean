/-
  Conditional probability framework for PMF with Bayesian inversion.

  Part A: PMF.prob and PMF.condProb — probability of sets, conditional probability
  Part B: Bayesian inversion in Kl(PMF) — posterior distribution, recovery equation
  Part C: Uniform conditioning — counting arguments for PMF.uniformOfFintype
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

open scoped ENNReal
open Set

/-! ## Part A: Probability of Sets and Conditional Probability -/

namespace PMF

variable {α β : Type*}

/-- Probability of a set under a PMF: `Pr_p[A] = ∑_a 𝟙_A(a) · p(a)`. -/
noncomputable def prob (p : PMF α) (A : Set α) : ℝ≥0∞ :=
  ∑' a, A.indicator p a

/-- Conditional probability: `Pr_p[A | B] = Pr_p[A ∩ B] / Pr_p[B]`. -/
noncomputable def condProb (p : PMF α) (A B : Set α) : ℝ≥0∞ :=
  p.prob (A ∩ B) / p.prob B

@[simp]
theorem prob_empty (p : PMF α) : p.prob ∅ = 0 := by
  simp [prob]

@[simp]
theorem prob_univ (p : PMF α) : p.prob univ = 1 := by
  show ∑' a, (univ : Set α).indicator (⇑p) a = 1
  simp [tsum_coe]

theorem prob_le_one (p : PMF α) (A : Set α) : p.prob A ≤ 1 := by
  calc p.prob A = ∑' a, A.indicator p a := rfl
    _ ≤ ∑' a, p a :=
        ENNReal.tsum_le_tsum (fun a => indicator_apply_le fun _ => le_rfl)
    _ = 1 := p.tsum_coe

theorem prob_ne_top (p : PMF α) (A : Set α) : p.prob A ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (p.prob_le_one A)

theorem prob_mono (p : PMF α) {A B : Set α} (h : A ⊆ B) :
    p.prob A ≤ p.prob B :=
  ENNReal.tsum_le_tsum
    (fun a => indicator_le_indicator_of_subset h (fun _ => zero_le _) a)

theorem prob_singleton (p : PMF α) (a : α) : p.prob {a} = p a := by
  show ∑' a', ({a} : Set α).indicator (⇑p) a' = p a
  rw [tsum_eq_single a]
  · simp [indicator]
  · intro a' ha'
    simp [indicator, ha']

theorem prob_inter_le_right (p : PMF α) (A B : Set α) :
    p.prob (A ∩ B) ≤ p.prob B :=
  p.prob_mono inter_subset_right

/-- `Pr[A | B] ≤ 1`. -/
theorem condProb_le_one (p : PMF α) (A B : Set α) :
    p.condProb A B ≤ 1 := by
  unfold condProb
  rcases eq_or_ne (p.prob B) 0 with hB | hB
  · have h0 : p.prob (A ∩ B) = 0 :=
      le_antisymm (hB ▸ p.prob_inter_le_right A B) (zero_le _)
    simp [h0]
  · exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact p.prob_inter_le_right A B)

/-- `Pr[A | B] · Pr[B] = Pr[A ∩ B]` (definition of conditional probability). -/
theorem condProb_mul (p : PMF α) (A B : Set α) :
    p.condProb A B * p.prob B = p.prob (A ∩ B) := by
  unfold condProb
  rcases eq_or_ne (p.prob B) 0 with hB | hB
  · have h0 : p.prob (A ∩ B) = 0 :=
      le_antisymm (hB ▸ p.prob_inter_le_right A B) (zero_le _)
    simp [hB, h0]
  · exact ENNReal.div_mul_cancel hB (p.prob_ne_top B)

/-- `Pr[B | B] = 1` when `Pr[B] ≠ 0`. -/
theorem condProb_self (p : PMF α) (B : Set α) (hB : p.prob B ≠ 0) :
    p.condProb B B = 1 := by
  simp [condProb, inter_self, ENNReal.div_self hB (p.prob_ne_top B)]

/-- Bayes' theorem: `Pr[A|B] · Pr[B] = Pr[B|A] · Pr[A]`. -/
theorem bayes_theorem (p : PMF α) (A B : Set α) :
    p.condProb A B * p.prob B = p.condProb B A * p.prob A := by
  rw [p.condProb_mul, p.condProb_mul, inter_comm]

/-- Law of total probability: `Pr[A] = Pr[A|B] · Pr[B] + Pr[A|Bᶜ] · Pr[Bᶜ]`. -/
theorem total_probability (p : PMF α) (A B : Set α) :
    p.condProb A B * p.prob B + p.condProb A Bᶜ * p.prob Bᶜ = p.prob A := by
  classical
  rw [p.condProb_mul, p.condProb_mul]
  show ∑' a, (A ∩ B).indicator (⇑p) a + ∑' a, (A ∩ Bᶜ).indicator (⇑p) a =
    ∑' a, A.indicator (⇑p) a
  rw [← ENNReal.tsum_add]
  congr 1; funext a
  simp only [indicator, mem_inter_iff, mem_compl_iff]
  by_cases ha : a ∈ A <;> by_cases hb : a ∈ B <;> simp [ha, hb]

/-! ## Part B: Bayesian Inversion -/

/-- Joint distribution from prior `π` and likelihood `f`:
    `joint(a, b) = π(a) · f(a)(b)`. -/
noncomputable def joint (π : PMF α) (f : α → PMF β) : PMF (α × β) :=
  ⟨fun ⟨a, b⟩ => π a * (f a) b, by
    rw [show (fun p : α × β => π p.1 * (f p.1) p.2) = (fun p => π p.1 * (f p.1) p.2) from rfl]
    have := ENNReal.summable.hasSum (f := fun p : α × β => π p.1 * (f p.1) p.2)
    rw [ENNReal.tsum_prod'] at this
    convert this using 1
    simp [ENNReal.tsum_mul_left, tsum_coe]⟩

/-- Marginal on `β`: `marginal(b) = ∑_a π(a) · f(a)(b)`. -/
noncomputable def marginalβ (π : PMF α) (f : α → PMF β) (b : β) : ℝ≥0∞ :=
  ∑' a, π a * (f a) b

@[simp]
theorem joint_apply (π : PMF α) (f : α → PMF β) (a : α) (b : β) :
    (π.joint f) (a, b) = π a * (f a) b := rfl

theorem marginalβ_eq_bind (π : PMF α) (f : α → PMF β) (b : β) :
    π.marginalβ f b = (π.bind f) b := by
  simp [marginalβ, bind_apply]

private theorem marginalβ_le_one (π : PMF α) (f : α → PMF β) (b : β) :
    π.marginalβ f b ≤ 1 := by
  calc ∑' a, π a * (f a) b
      ≤ ∑' a, π a * 1 :=
        ENNReal.tsum_le_tsum (fun a => by gcongr; exact coe_le_one (f a) b)
    _ = 1 := by simp [tsum_coe]

private theorem marginalβ_ne_top (π : PMF α) (f : α → PMF β) (b : β) :
    π.marginalβ f b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (marginalβ_le_one π f b)

end PMF

namespace CatCrypt.Prob

open PMF

variable {α β : Type*}

/-- Bayesian inversion: posterior distribution `P(a | b)`.
    Uses `PMF.normalize` on the un-normalized posterior `a ↦ π(a) · f(a)(b)`. -/
noncomputable def bayesInv (π : PMF α) (f : α → PMF β) (b : β)
    (hmarg : π.marginalβ f b ≠ 0) : PMF α :=
  PMF.normalize (fun a => π a * (f a) b)
    (by rwa [PMF.marginalβ] at hmarg)
    (PMF.marginalβ_ne_top π f b)

theorem bayesInv_apply (π : PMF α) (f : α → PMF β) (b : β)
    (hmarg : π.marginalβ f b ≠ 0) (a : α) :
    (bayesInv π f b hmarg) a = π a * (f a) b * (π.marginalβ f b)⁻¹ := by
  simp [bayesInv, PMF.normalize_apply, PMF.marginalβ]

/-- Recovery equation (discrete Bayes' theorem):
    `posterior(a) · marginal(b) = π(a) · f(a)(b)`. -/
theorem bayesInv_recovery (π : PMF α) (f : α → PMF β) (b : β)
    (hmarg : π.marginalβ f b ≠ 0) (a : α) :
    (bayesInv π f b hmarg) a * π.marginalβ f b = π a * (f a) b := by
  rw [bayesInv_apply, mul_assoc,
    ENNReal.inv_mul_cancel hmarg (PMF.marginalβ_ne_top π f b), mul_one]

/-- The marginal is the sum of joint over the first component. -/
theorem marginalβ_eq_tsum_joint (π : PMF α) (f : α → PMF β) (b : β) :
    π.marginalβ f b = ∑' a, (π.joint f) (a, b) := by
  simp [PMF.marginalβ, PMF.joint_apply]

/-! ## Part C: Uniform Conditioning -/

/-- For uniform distribution, `Pr[A] = |A| / |α|`. -/
theorem prob_uniform_eq [Fintype α] [Nonempty α] [DecidableEq α] (A : Finset α) :
    (PMF.uniformOfFintype α).prob (↑A) =
      (A.card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) := by
  show ∑' a, (↑A : Set α).indicator (⇑(PMF.uniformOfFintype α)) a = _
  trans ∑ a ∈ A, (PMF.uniformOfFintype α) a
  · rw [tsum_eq_sum (s := A)]
    · exact Finset.sum_congr rfl fun a ha =>
        indicator_of_mem (Finset.mem_coe.mpr ha) _
    · intro a ha; simp [ha]
  · simp [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- For uniform distribution on a finite type, conditional probability is
    `Pr[A | B] = |A ∩ B| / |B|`. -/
theorem condProb_uniform_eq [Fintype α] [Nonempty α] [DecidableEq α]
    (A B : Finset α) :
    (PMF.uniformOfFintype α).condProb (↑A) (↑B) =
      ((A ∩ B).card : ℝ≥0∞) / (B.card : ℝ≥0∞) := by
  simp only [PMF.condProb]
  rw [show (↑A : Set α) ∩ (↑B : Set α) = ↑(A ∩ B) from by ext; simp]
  rw [prob_uniform_eq, prob_uniform_eq]
  have hc0 : (Fintype.card α : ℝ≥0∞)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hc_top : (Fintype.card α : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Fintype.card_pos.ne'))
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact ENNReal.mul_div_mul_right _ _ hc0 hc_top

/-- For uniform distribution, probability of a single element given membership
    in `B` is `1 / |B|`. -/
theorem condProb_uniform_singleton [Fintype α] [Nonempty α] [DecidableEq α]
    (a : α) (B : Finset α) (ha : a ∈ B) :
    (PMF.uniformOfFintype α).condProb {↑a} (↑B) = (B.card : ℝ≥0∞)⁻¹ := by
  rw [show ({↑a} : Set α) = ↑({a} : Finset α) from by simp]
  rw [condProb_uniform_eq]
  simp [Finset.singleton_inter_of_mem ha]

end CatCrypt.Prob

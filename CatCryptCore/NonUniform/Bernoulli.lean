/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.CouplingRules
import CatCryptCore.NonUniform.UnaryRules

/-!
# Biased coins: a non-uniform coupling worked out

`bernoulli p` is the coin that comes up `true` with probability `p`. For `p ≠ 1/2`
it is not the uniform distribution on `Bool`, and no bijection of `Bool` carries
it to itself, so `liftR_uniform_bij` and `rHoare_bij_step` cannot relate two
differently-biased coins. Negation does carry `bernoulli p` to `bernoulli (1 - p)`,
which is a pushforward coupling: `rHoare_bernoulli_flip` turns it into a pRHL
sampling step, and `bernoulli_flip_program_eq` shows a `bernoulli p` sample can be
renamed as the negation of a `bernoulli (1 - p)` sample inside any program.

## Main results

* `bernoulli_apply_true`, `bernoulli_apply_false` — the two masses
* `bernoulli_ne_uniform`, `bernoulli_third_ne_uniform` — a coin whose two masses
  differ is not uniform
* `bernoulli_bind_not` — negation pushes `bernoulli p` to `bernoulli (1 - p)`
* `liftR_bernoulli_not` — the resulting coupling
* `rHoare_bernoulli_flip` — the pRHL sampling step
* `bernoulli_flip_program_eq` — the two programs are equal
* `prTrue_bernoulli_bind`, `prTrue_bernoulli` — the unary averaging rule applied
-/

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open scoped NNReal ENNReal

variable {γ δ : Type*}

/-! ## The distribution -/

/-- The coin that comes up `true` with probability `p`. -/
noncomputable def bernoulli (p : ℝ≥0) (hp : p ≤ 1) : SDistr Bool :=
  ofPMF (PMF.bernoulli p hp)

/-- The mass of a Bernoulli coin at a Boolean outcome. -/
theorem bernoulli_apply_some (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    bernoulli p hp (some b) = ((bif b then p else 1 - p : ℝ≥0) : ℝ≥0∞) := by
  rw [bernoulli, ofPMF_apply_some, PMF.bernoulli_apply]

@[simp]
theorem bernoulli_apply_true (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulli p hp (some true) = (p : ℝ≥0∞) := bernoulli_apply_some p hp true

@[simp]
theorem bernoulli_apply_false (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulli p hp (some false) = ((1 - p : ℝ≥0) : ℝ≥0∞) := bernoulli_apply_some p hp false

@[simp]
theorem mass_bernoulli (p : ℝ≥0) (hp : p ≤ 1) : SDistr.mass (bernoulli p hp) = 1 :=
  mass_ofPMF _

/-- `sampleFrom (bernoulli p)` never fails. -/
theorem isLossless_sampleFrom_bernoulli (p : ℝ≥0) (hp : p ≤ 1) :
    Unary.isLossless (sampleFrom (bernoulli p hp)) :=
  isLossless_sampleFrom _ (mass_bernoulli p hp)

/-- A Bernoulli coin can be uniform only if its two masses agree. -/
theorem bernoulli_ne_uniform (p : ℝ≥0) (hp : p ≤ 1)
    (hne : (p : ℝ≥0∞) ≠ ((1 - p : ℝ≥0) : ℝ≥0∞)) :
    bernoulli p hp ≠ SDistr.uniform Bool := fun heq =>
  hne (by rw [← bernoulli_apply_true p hp, ← bernoulli_apply_false p hp, heq,
    SDistr.uniform_apply_some, SDistr.uniform_apply_some])

/-! ## The coupling -/

/-- Negating a `bernoulli p` sample yields a `bernoulli (1 - p)` sample. -/
theorem bernoulli_bind_not (p : ℝ≥0) (hp : p ≤ 1) (hp' : 1 - p ≤ 1) :
    (bernoulli p hp).bind (fun b => SDistr.pure (!b)) = bernoulli (1 - p) hp' := by
  refine SDistr.eq_of_some_eq fun c => ?_
  simp only [SDistr.bind, PMF.bind_apply]
  rw [SDistr.tsum_option_eq_add, tsum_fintype, Fintype.sum_bool]
  cases c <;>
    simp [SDistr.pure_apply_some, bernoulli_apply_true, bernoulli_apply_false,
      tsub_tsub_cancel_of_le hp]

/-- `bernoulli p` and `bernoulli (1 - p)` are coupled by Boolean negation.

    Unlike the uniform bijection coupling, the two marginals here are *different*
    distributions: negation is a bijection of `Bool` that does not preserve
    `bernoulli p` unless `p = 1/2`. -/
theorem liftR_bernoulli_not (p : ℝ≥0) (hp : p ≤ 1) (hp' : 1 - p ≤ 1) :
    liftR (fun a b => (!a) = b) (bernoulli p hp) (bernoulli (1 - p) hp') :=
  liftR_pushforward (bernoulli_bind_not p hp hp')

/-! ## The pRHL step -/

/-- pRHL sampling step for two coins of complementary bias: a `bernoulli p`
    sample on the left is matched by the negated `bernoulli (1 - p)` sample on the
    right. -/
theorem rHoare_bernoulli_flip {Φ : RPre} {Ψ : RPost γ δ}
    (p : ℝ≥0) (hp : p ≤ 1) (hp' : 1 - p ≤ 1)
    {k₁ : Bool → SPComp γ} {k₂ : Bool → SPComp δ}
    (h : ∀ b, rHoare Φ (k₁ b) (k₂ (!b)) Ψ) :
    rHoare Φ (SPComp.bind (sampleFrom (bernoulli p hp)) k₁)
             (SPComp.bind (sampleFrom (bernoulli (1 - p) hp')) k₂) Ψ :=
  rHoare_coupling_step (liftR_bernoulli_not p hp hp') fun a b hab => hab ▸ h a

/-- Sampling `bernoulli p` and negating is sampling `bernoulli (1 - p)`, inside an
    arbitrary continuation. Derived from the coupling step at `eqPre`/`eqPost`. -/
theorem bernoulli_flip_program_eq {α : Type*}
    (p : ℝ≥0) (hp : p ≤ 1) (hp' : 1 - p ≤ 1) (k : Bool → SPComp α) :
    SPComp.bind (sampleFrom (bernoulli p hp)) (fun b => k (!b))
      = SPComp.bind (sampleFrom (bernoulli (1 - p) hp')) k :=
  funext fun h₀ => eq_of_rHoare_eqPost
    (rHoare_bernoulli_flip p hp hp' (fun b => rHoare_refl (k (!b)))) h₀

/-! ## The unary rule applied -/

/-- The success probability of a game that starts with a biased coin is the
    `p`-weighted average of the two branch probabilities. -/
theorem prTrue_bernoulli_bind (p : ℝ≥0) (hp : p ≤ 1) (k : Bool → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (sampleFrom (bernoulli p hp)) k) h₀
      = (p : ℝ≥0∞) * prTrue (k true) h₀ + ((1 - p : ℝ≥0) : ℝ≥0∞) * prTrue (k false) h₀ := by
  rw [prTrue_bind_sampleFrom, tsum_fintype, Fintype.sum_bool,
      bernoulli_apply_true, bernoulli_apply_false]

/-- A biased coin returns `true` with probability exactly `p`. -/
theorem prTrue_bernoulli (p : ℝ≥0) (hp : p ≤ 1) (h₀ : Heap) :
    prTrue (sampleFrom (bernoulli p hp)) h₀ = (p : ℝ≥0∞) := by
  rw [prTrue_sampleFrom, bernoulli_apply_true]

/-- Cross-check of the coupling against the unary rule: negating a `bernoulli p`
    coin is a `bernoulli (1 - p)` coin, both routes giving `1 - p`. -/
theorem prTrue_bernoulli_not (p : ℝ≥0) (hp : p ≤ 1) (hp' : 1 - p ≤ 1) (h₀ : Heap) :
    prTrue (SPComp.bind (sampleFrom (bernoulli p hp)) (fun b => SPComp.pure (!b))) h₀
      = ((1 - p : ℝ≥0) : ℝ≥0∞) := by
  rw [bernoulli_flip_program_eq p hp hp' SPComp.pure, SPComp.bind_pure]
  exact prTrue_bernoulli _ hp' h₀

/-! ## Satisfiability witness

The hypotheses of `rHoare_bernoulli_flip` are inhabited at a concretely
non-uniform bias: `p = 1/3` gives a coupling of the `1/3`-coin with the
`2/3`-coin, and `bernoulli_ne_uniform` shows the `1/3`-coin is not uniform, so the
step is not a disguised uniform one. -/

theorem one_third_le_one : (1 / 3 : ℝ≥0) ≤ 1 := by
  rw [div_le_one (by norm_num)]; norm_num

theorem one_sub_one_third_le_one : 1 - (1 / 3 : ℝ≥0) ≤ 1 := tsub_le_self

/-- `1/3 ≠ 2/3`, transported to `ℝ≥0∞`. -/
theorem coe_one_third_ne_coe_two_thirds :
    ((1 / 3 : ℝ≥0) : ℝ≥0∞) ≠ ((1 - 1 / 3 : ℝ≥0) : ℝ≥0∞) := by
  intro h
  have hr : ((1 / 3 : ℝ≥0) : ℝ) = ((1 - 1 / 3 : ℝ≥0) : ℝ) := congrArg _ (ENNReal.coe_inj.mp h)
  rw [NNReal.coe_sub one_third_le_one] at hr
  norm_num at hr

/-- The `1/3`-coin is not the uniform distribution on `Bool`. -/
theorem bernoulli_third_ne_uniform :
    bernoulli (1 / 3) one_third_le_one ≠ SDistr.uniform Bool :=
  bernoulli_ne_uniform _ one_third_le_one coe_one_third_ne_coe_two_thirds

/-- A concrete coupling of the `1/3`-coin with the `2/3`-coin. Its two marginals
    are distinct distributions, and the left one is not uniform
    (`bernoulli_third_ne_uniform`). -/
theorem liftR_bernoulli_third :
    liftR (fun a b => (!a) = b)
      (bernoulli (1 / 3) one_third_le_one)
      (bernoulli (1 - 1 / 3) one_sub_one_third_le_one) :=
  liftR_bernoulli_not _ one_third_le_one one_sub_one_third_le_one

/-- The two marginals of `liftR_bernoulli_third` differ. -/
theorem bernoulli_third_marginals_ne :
    bernoulli (1 / 3) one_third_le_one
      ≠ bernoulli (1 - 1 / 3) one_sub_one_third_le_one := fun heq =>
  coe_one_third_ne_coe_two_thirds (by
    rw [← bernoulli_apply_true (1 / 3) one_third_le_one,
      ← bernoulli_apply_true (1 - 1 / 3) one_sub_one_third_le_one, heq])

end CatCrypt.NonUniform

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.CouplingRules
import CatCryptCore.NonUniform.Product
import CatCryptCore.NonUniform.UnaryRules

/-!
# The centered binomial distribution and sign independence

`cbd η` is the difference of two independent `Binomial η 1/2` counts: the noise
distribution of ML-KEM, sampled over `ℤ`. It is not a uniform distribution, and
`ℤ` carries no `Fintype` instance, so `SPComp.sample` cannot name a program that
draws from it and `liftR_uniform_bij` cannot relate two such draws. `sampleFrom`
and `rHoare_coupling_step` can.

The relational content is that `cbd η` is symmetric under negation, so the sign
applied to a noise term is unobservable: `cbd_signed_indep` states that for a
secret sign `s`, the program `e ← cbd η; k ((-1)^s * e)` has the same behaviour
for both values of `s`.

## Main definitions

* `binom n` — the number of successes in `n` fair coin flips
* `cbd η` — the centered binomial distribution `Binomial η 1/2 - Binomial η 1/2`
* `signed s e` — `-e` when `s`, else `e`

## Main results

* `bind_apply_ne_zero` — a bind hits every value its two stages reach
* `mass_cbd`, `isLossless_sampleFrom_cbd` — `cbd η` is a total distribution
* `cbd_one_ne_pure` — `cbd 1` has at least two support points, so the example is
  not a point mass in disguise
* `cbd_symm` — `cbd η` is invariant under negation
* `rHoare_cbd_signed` — the pRHL sampling step from that invariance
* `cbd_signed_indep` — a secret sign on the noise term is unobservable
* `prTrue_cbd_bind` — the unary averaging rule at `cbd η`
-/

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open scoped ENNReal

variable {α β : Type*}

/-! ## Support of a bind -/

/-- A bind hits `b` whenever some intermediate `a` is in the support of `d` and
    `b` is in the support of `f a`. Converse of `SDistr.bind_support_witness`. -/
theorem bind_apply_ne_zero {d : SDistr α} {f : α → SDistr β} {a : α} {b : β}
    (ha : d (some a) ≠ 0) (hb : (f a) (some b) ≠ 0) : (d.bind f) (some b) ≠ 0 := by
  have hterm : d (some a) * (f a) (some b) ≤ (d.bind f) (some b) := by
    simpa only [SDistr.bind, PMF.bind_apply] using ENNReal.le_tsum (some a)
  exact fun h0 => mul_ne_zero ha hb (le_zero_iff.mp (h0 ▸ hterm))

/-! ## The distributions -/

/-- The number of successes in `n` fair coin flips. -/
noncomputable def binom : ℕ → SDistr ℕ
  | 0 => SDistr.pure 0
  | n + 1 => (binom n).bind fun k =>
      (SDistr.uniform Bool).bind fun b => SDistr.pure (k + if b then 1 else 0)

theorem binom_zero : binom 0 = SDistr.pure 0 := rfl

theorem binom_succ (n : ℕ) :
    binom (n + 1) = (binom n).bind fun k =>
      (SDistr.uniform Bool).bind fun b => SDistr.pure (k + if b then 1 else 0) := rfl

/-- The centered binomial distribution: the difference of two independent
    `binom η` counts. -/
noncomputable def cbd (η : ℕ) : SDistr ℤ :=
  (binom η).bind fun a => (binom η).bind fun b => SDistr.pure ((a : ℤ) - (b : ℤ))

@[simp]
theorem mass_binom (n : ℕ) : SDistr.mass (binom n) = 1 := by
  induction n with
  | zero => rw [binom_zero, SDistr.mass_pure]
  | succ n ih =>
    exact mass_bind_of_mass_one ih fun _ =>
      mass_bind_of_mass_one SDistr.mass_uniform fun _ => SDistr.mass_pure _

@[simp]
theorem mass_cbd (η : ℕ) : SDistr.mass (cbd η) = 1 :=
  mass_bind_of_mass_one (mass_binom η) fun _ =>
    mass_bind_of_mass_one (mass_binom η) fun _ => SDistr.mass_pure _

/-- Drawing centered binomial noise never fails. -/
theorem isLossless_sampleFrom_cbd (η : ℕ) : Unary.isLossless (sampleFrom (cbd η)) :=
  isLossless_sampleFrom _ (mass_cbd η)

/-! ## Non-degeneracy

`cbd 1` puts mass on both `0` and `1`, so it is not a point mass; and `ℤ` has no
uniform distribution, so the example is not a uniform draw under another name. -/

theorem binom_one_apply_zero : binom 1 (some 0) ≠ 0 := by
  rw [binom_succ, binom_zero, SDistr.pure_bind]
  exact bind_apply_ne_zero (a := false) (by simp [SDistr.uniform_apply_some]) (by simp)

theorem binom_one_apply_one : binom 1 (some 1) ≠ 0 := by
  rw [binom_succ, binom_zero, SDistr.pure_bind]
  exact bind_apply_ne_zero (a := true) (by simp [SDistr.uniform_apply_some]) (by simp)

theorem cbd_one_apply_zero : cbd 1 (some 0) ≠ 0 :=
  bind_apply_ne_zero (a := 0) binom_one_apply_zero
    (bind_apply_ne_zero (a := 0) binom_one_apply_zero (by simp))

theorem cbd_one_apply_one : cbd 1 (some 1) ≠ 0 :=
  bind_apply_ne_zero (a := 1) binom_one_apply_one
    (bind_apply_ne_zero (a := 0) binom_one_apply_zero (by simp))

/-- `cbd 1` is not a point mass: `0` and `1` are both in its support. -/
theorem cbd_one_ne_pure (z : ℤ) : cbd 1 ≠ SDistr.pure z := by
  intro heq
  have hz0 : z = 0 := (SDistr.mem_support_pure_iff z (0 : ℤ)).mp (heq ▸ cbd_one_apply_zero)
  have hz1 : z = 1 := (SDistr.mem_support_pure_iff z (1 : ℤ)).mp (heq ▸ cbd_one_apply_one)
  omega

/-! ## Symmetry under negation -/

/-- `cbd η` is invariant under negation: negating the difference of the two counts
    exchanges them, and the two counts are independent and identically
    distributed. -/
theorem cbd_symm (η : ℕ) : (cbd η).bind (fun z => SDistr.pure (-z)) = cbd η := by
  rw [cbd, SDistr.bind_assoc]
  have step : ∀ a : ℕ,
      ((binom η).bind fun b => SDistr.pure ((a : ℤ) - (b : ℤ))).bind
        (fun z => SDistr.pure (-z))
      = (binom η).bind fun b => SDistr.pure ((b : ℤ) - (a : ℤ)) := fun a => by
    simp only [SDistr.bind_assoc, SDistr.pure_bind, neg_sub]
  simp only [step]
  exact SDistr.bind_comm (binom η) (binom η) fun a b => SDistr.pure ((b : ℤ) - (a : ℤ))

/-- Apply a sign to a noise term: `signed true` negates, `signed false` is the
    identity. -/
def signed (s : Bool) (e : ℤ) : ℤ := if s then -e else e

/-- The pushforward of `cbd η` along either sign is `cbd η`. -/
theorem cbd_pushforward_signed (η : ℕ) (s : Bool) :
    (cbd η).bind (fun e => SDistr.pure (signed s e)) = cbd η := by
  cases s with
  | false => simpa [signed] using SDistr.bind_pure (cbd η)
  | true => simpa [signed] using cbd_symm η

/-- The coupling of `cbd η` with itself along a sign. -/
theorem liftR_cbd_signed (η : ℕ) (s : Bool) :
    liftR (fun a b => signed s a = b) (cbd η) (cbd η) :=
  liftR_pushforward (cbd_pushforward_signed η s)

/-! ## The pRHL step and sign independence -/

/-- pRHL sampling step for centered binomial noise under a sign: a draw on the
    left is matched by the sign-flipped draw on the right. -/
theorem rHoare_cbd_sign {γ δ : Type*} {Φ : RPre} {Ψ : RPost γ δ} (η : ℕ) (s : Bool)
    {k₁ : ℤ → SPComp γ} {k₂ : ℤ → SPComp δ}
    (h : ∀ e, rHoare Φ (k₁ e) (k₂ (signed s e)) Ψ) :
    rHoare Φ (SPComp.bind (sampleFrom (cbd η)) k₁)
             (SPComp.bind (sampleFrom (cbd η)) k₂) Ψ :=
  rHoare_coupling_step (liftR_cbd_signed η s) fun a b hab => hab ▸ h a

/-- Applying a sign to the noise term does not change the program. -/
theorem cbd_signed_eq (η : ℕ) (s : Bool) (k : ℤ → SPComp α) :
    SPComp.bind (sampleFrom (cbd η)) (fun e => k (signed s e))
      = SPComp.bind (sampleFrom (cbd η)) k :=
  funext fun h₀ => eq_of_rHoare_eqPost
    (rHoare_cbd_sign η s fun e => rHoare_refl (k (signed s e))) h₀

/-- The sign of a centered binomial noise term is unobservable: the program is
    the same for both secret signs. -/
theorem cbd_signed_indep (η : ℕ) (k : ℤ → SPComp α) (s₁ s₂ : Bool) :
    SPComp.bind (sampleFrom (cbd η)) (fun e => k (signed s₁ e))
      = SPComp.bind (sampleFrom (cbd η)) (fun e => k (signed s₂ e)) :=
  (cbd_signed_eq η s₁ k).trans (cbd_signed_eq η s₂ k).symm

/-! ## The unary rule at `cbd` -/

/-- Success probability of a Boolean game that starts with centered binomial
    noise, as the `cbd η`-average of the branch probabilities. -/
theorem prTrue_cbd_bind (η : ℕ) (k : ℤ → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (sampleFrom (cbd η)) k) h₀
      = ∑' e : ℤ, cbd η (some e) * prTrue (k e) h₀ :=
  prTrue_bind_sampleFrom (cbd η) k h₀

end CatCrypt.NonUniform

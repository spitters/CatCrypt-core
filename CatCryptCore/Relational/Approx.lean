/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.SpanLifting
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Crypto.BadEvent
public import CatCryptCore.Prob.Support

/-!
# ε-Graded Approximate Relational Hoare Logic (apRHL-style)

This file internalizes advantage-budget reasoning into the relational layer:
an `ℝ≥0∞`-graded judgment `rHoareApprox ε Φ c₁ c₂ Ψ` whose grades add under
sequential composition, together with an adequacy theorem landing in the
`Advantage`/`sdist` layer used by the cryptographic proofs.

## Formulation

The judgment is defined through an **approximate span lifting** of `SDistr`
in the style of Sato (LICS 2019), graded by statistical (total-variation)
distance — the additive grading relevant to cryptography, not the
multiplicative DP grading of the original apRHL of Barthe et al.

`liftRApprox ε R d₁ d₂` asks for a *sub-coupling*: a joint distribution whose
marginal sums are dominated by `d₁` and `d₂`, whose support respects `R`, and
whose pointwise marginal deficits sum to at most `ε` on each side
(`SubCoupling`). Compared with the "∃ ε-close intermediate program"
formulation, the sub-coupling witness lives over *pairs*, so the continuation
witness in the bind rule may depend on both sides of the pair — this is what
makes grade-additive sequential composition (`liftRApprox_bind`) go through.
The intermediate-program formulation does not compose in general: its bind
rule would need a right-side intermediate continuation depending only on the
right value, while the per-pair witnesses depend on both.

At grade `0` the sub-coupling marginals are exact and the judgment coincides
with the exact `rHoare` of `CatCrypt.Relational.Judgment`
(`rHoareApprox_zero_iff`), which is in turn the span lifting of
`CatCrypt.Relational.SpanLifting`.

## Main definitions

* `SubCoupling d₁ d₂ ε` — sub-coupling with marginal deficits ≤ `ε`
* `liftRApprox ε R d₁ d₂` — approximate span lifting of `R` at grade `ε`
* `rHoareApprox ε Φ c₁ c₂ Ψ` — the graded relational judgment
* `tvMargin d₁ d₂` — one-sided statistical distance `∑' a, (d₁ a - d₂ a)`

## Main results

* `liftRApprox_bind` / `rHoareApprox_bind` — grade-additive sequential
  composition: `ε₁` and `ε₂` compose to `ε₁ + ε₂`
* `rHoareApprox_zero_iff` — grade-0 embedding: `rHoare` ↔ `rHoareApprox 0`
* `rHoareApprox_conseq` — consequence rule, monotone in pre/post and grade
* `rHoareApprox_liftSDistr` — sample rule: distributions at statistical
  distance ≤ `ε` relate at grade `ε`
* `rHoareApprox_upto_bad` — identical-until-bad with `Pr[bad] ≤ ε` gives a
  grade-`ε` judgment (relational form of Shoup's fundamental lemma)
* `rHoareApprox_advantageA` / `rHoareApprox_sdist` — **adequacy**: a grade-`ε`
  judgment with equal-heap precondition and equality postcondition bounds
  every adversary's advantage (and the Kleisli statistical distance) by `ε`
* `rHoareApprox_trans_eq` — transitivity at equality post (game hopping
  inside the logic)
* `rHoareApprox_of_advantageA` / `rHoareApprox_of_sdist` — **completeness**
  (converse adequacy): a `∀`-adversary advantage bound *is* a grade-`ε`
  judgment, at the same constant; with the iffs
  `rHoareApprox_emptyPre_iff_advantageA` and `rHoareApprox_eqPre_iff_sdist`
* `rHoareApprox_chain` / `rHoareApprox_chain_of_pre` /
  `rHoareApprox_chain_const` — runtime-length graded hybrid chains: `n` hop
  judgments compose to grade `∑ i < n, δ i` (resp. `n * ε`)

## References

* T. Sato, *Approximate Span Liftings: Compositional Semantics of Relational
  Probabilistic Programs*, LICS 2019 — graded relational liftings with
  grade-additive composition.
* S. Katsumata, T. Sato, *Codensity Liftings of Monads*, CALCO 2015 — the
  exact (grade-0) relational liftings.
* G. Barthe, B. Köpf, F. Olmedo, S. Zanella Béguelin, *Probabilistic
  Relational Reasoning for Differential Privacy* (apRHL) — the proof-rule
  tradition; here graded additively (statistical distance) rather than
  multiplicatively (DP).
* V. Shoup, *Sequences of Games*, ePrint 2004/332 — the up-to-bad rule.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Prob

open scoped ENNReal

variable {α β γ δ : Type*}

/-! ## tsum helpers -/

/-- A sub-distribution with no failure mass has mass exactly 1 on `some`. -/
theorem SDistr.tsum_some_eq_one_of_none_zero {d : SDistr α} (h : d none = 0) :
    ∑' a, d (some a) = 1 := by
  have htot := d.tsum_coe
  rwa [SDistr.tsum_option_eq_add, h, zero_add] at htot

private theorem tsum_tsub_tsum_le {ι : Type*} (f g : ι → ℝ≥0∞) :
    (∑' i, f i) - (∑' i, g i) ≤ ∑' i, (f i - g i) := by
  rw [tsub_le_iff_right]
  calc ∑' i, f i
      ≤ ∑' i, ((f i - g i) + g i) := ENNReal.tsum_le_tsum fun i => le_tsub_add
    _ = (∑' i, (f i - g i)) + ∑' i, g i := ENNReal.tsum_add

private theorem mul_tsub_le' (a x y : ℝ≥0∞) : a * x - a * y ≤ a * (x - y) := by
  rw [tsub_le_iff_right, ← mul_add]
  exact mul_le_mul_right le_tsub_add a

theorem exists_ne_zero_of_tsum_ne_zero {ι : Type*} {f : ι → ℝ≥0∞}
    (h : ∑' i, f i ≠ 0) : ∃ i, f i ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (ENNReal.tsum_eq_zero.mpr hc)

/-! ## Approximate sub-couplings

A `SubCoupling d₁ d₂ ε` is the witness of Sato's approximate span lifting,
specialized to the statistical-distance grading: a joint sub-distribution on
pairs whose marginal sums are *dominated* by `d₁` and `d₂`, and whose total
marginal deficits are at most `ε` on each side. The deficit is the mass of
`d₁` (resp. `d₂`) that the witness fails to explain — exactly the mass that a
distinguisher can exploit, which is why adequacy bounds advantage by `ε`. -/

/-- An `ε`-approximate sub-coupling of `d₁` and `d₂`. -/
structure SubCoupling (d₁ : SDistr α) (d₂ : SDistr β) (ε : ℝ≥0∞) where
  /-- The joint witness distribution. -/
  joint : SDistr (α × β)
  /-- The left marginal sum is dominated by `d₁`. -/
  left_le : ∀ a, (∑' b, joint (some (a, b))) ≤ d₁ (some a)
  /-- The right marginal sum is dominated by `d₂`. -/
  right_le : ∀ b, (∑' a, joint (some (a, b))) ≤ d₂ (some b)
  /-- The total left marginal deficit is at most `ε`. -/
  left_deficit : (∑' a, (d₁ (some a) - ∑' b, joint (some (a, b)))) ≤ ε
  /-- The total right marginal deficit is at most `ε`. -/
  right_deficit : (∑' b, (d₂ (some b) - ∑' a, joint (some (a, b)))) ≤ ε

namespace SubCoupling

variable {d₁ : SDistr α} {d₂ : SDistr β} {ε : ℝ≥0∞}

/-- A sub-coupling satisfies relation `R` if its support respects `R`. -/
def satisfies (c : SubCoupling d₁ d₂ ε) (R : α → β → Prop) : Prop :=
  ∀ a b, c.joint (some (a, b)) ≠ 0 → R a b

end SubCoupling

/-- **Approximate span lifting** at grade `ε`: there exists an `ε`-approximate
    sub-coupling whose support respects `R`. (Sato, LICS 2019, with
    statistical-distance grading.) -/
def liftRApprox (ε : ℝ≥0∞) (R : α → β → Prop) (d₁ : SDistr α) (d₂ : SDistr β) : Prop :=
  ∃ c : SubCoupling d₁ d₂ ε, c.satisfies R

/-! ## Swap -/

/-- Swap the two components of a joint distribution. -/
noncomputable def SDistr.swapPair (w : SDistr (α × β)) : SDistr (β × α) :=
  w.bind fun p => SDistr.pure (p.2, p.1)

theorem SDistr.swapPair_apply (w : SDistr (α × β)) (q : β × α) :
    (SDistr.swapPair w) (some q) = w (some (q.2, q.1)) := by
  classical
  rw [SDistr.swapPair, SDistr.bind_apply_some]
  rw [tsum_eq_single (q.2, q.1)]
  · rw [SDistr.pure_apply_some]
    simp
  · intro p hne
    rw [SDistr.pure_apply_some, if_neg, mul_zero]
    intro heq
    apply hne
    have h1 : p.2 = q.1 := by rw [← heq]
    have h2 : p.1 = q.2 := by rw [← heq]
    exact Prod.ext h2 h1

theorem SDistr.swapPair_bind (w : SDistr (α × β)) (k : α × β → SDistr (γ × δ)) :
    (SDistr.swapPair w).bind (fun q => SDistr.swapPair (k (q.2, q.1)))
      = SDistr.swapPair (w.bind k) := by
  simp only [SDistr.swapPair, SDistr.bind_assoc, SDistr.pure_bind]

/-! ## The bind rule (grade-additive composition)

This is the make-or-break theorem of the graded logic. The witness for the
composite is `w.bind K` where `w` witnesses the prefix and `K p` is, for each
pair `p` in the support of `w` (where the prefix relation holds), a chosen
witness for the continuations at `p` — and `fail` off the support, which is
harmless because all sub-coupling conditions are inequalities. -/

/-- Marginal sums of `w.bind k` along any reindexing `g` of the output pairs
    decompose through `w`. -/
theorem bind_marginal_eq {ι : Type*}
    (w : SDistr (α × β)) (k : α × β → SDistr (γ × δ)) (g : ι → γ × δ) :
    ∑' i, (w.bind k) (some (g i)) = ∑' p, w (some p) * ∑' i, (k p) (some (g i)) :=
  calc ∑' i, (w.bind k) (some (g i))
      = ∑' i, ∑' p, w (some p) * (k p) (some (g i)) :=
        tsum_congr fun i => SDistr.bind_apply_some w k (g i)
    _ = ∑' p, ∑' i, w (some p) * (k p) (some (g i)) := ENNReal.tsum_comm
    _ = ∑' p, w (some p) * ∑' i, (k p) (some (g i)) :=
        tsum_congr fun _ => ENNReal.tsum_mul_left

/-- One-sided conditions of the composite sub-coupling. Stated for the left
    side; the right side follows by applying this lemma to the swapped data. -/
theorem bind_left_conditions
    (w : SDistr (α × β)) (k : α × β → SDistr (γ × δ))
    (d₁ : SDistr α) (f₁ : α → SDistr γ) (ε₁ ε₂ : ℝ≥0∞)
    (hle : ∀ a, (∑' b, w (some (a, b))) ≤ d₁ (some a))
    (hdef : (∑' a, (d₁ (some a) - ∑' b, w (some (a, b)))) ≤ ε₁)
    (hk_le : ∀ p, w (some p) ≠ 0 →
      ∀ c, (∑' d', (k p) (some (c, d'))) ≤ (f₁ p.1) (some c))
    (hk_def : ∀ p, w (some p) ≠ 0 →
      (∑' c, ((f₁ p.1) (some c) - ∑' d', (k p) (some (c, d')))) ≤ ε₂) :
    (∀ c, (∑' d', (w.bind k) (some (c, d'))) ≤ (d₁.bind f₁) (some c)) ∧
    (∑' c, ((d₁.bind f₁) (some c) - ∑' d', (w.bind k) (some (c, d')))) ≤ ε₁ + ε₂ := by
  have hM : ∀ c, (∑' d', (w.bind k) (some (c, d')))
      = ∑' p, w (some p) * ∑' d', (k p) (some (c, d')) :=
    fun c => bind_marginal_eq w k (fun d' => (c, d'))
  -- pointwise split of `d₁` into deficit + explained mass
  have hsplit : ∀ a, d₁ (some a) =
      (d₁ (some a) - ∑' b, w (some (a, b))) + ∑' b, w (some (a, b)) :=
    fun a => (tsub_add_cancel_of_le (hle a)).symm
  have hbind_split : ∀ c, (d₁.bind f₁) (some c) =
      (∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) * (f₁ a) (some c)) +
      (∑' p : α × β, w (some p) * (f₁ p.1) (some c)) := by
    intro c
    rw [SDistr.bind_apply_some]
    calc ∑' a, d₁ (some a) * (f₁ a) (some c)
        = ∑' a, ((d₁ (some a) - ∑' b, w (some (a, b))) * (f₁ a) (some c) +
                 (∑' b, w (some (a, b))) * (f₁ a) (some c)) := by
          refine tsum_congr fun a => ?_
          rw [← add_mul, ← hsplit a]
      _ = (∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) * (f₁ a) (some c)) +
          ∑' a, (∑' b, w (some (a, b))) * (f₁ a) (some c) := ENNReal.tsum_add
      _ = (∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) * (f₁ a) (some c)) +
          ∑' p : α × β, w (some p) * (f₁ p.1) (some c) := by
          congr 1
          rw [ENNReal.tsum_prod']
          exact tsum_congr fun a => ENNReal.tsum_mul_right.symm
  constructor
  · -- marginal domination
    intro c
    rw [hM c, SDistr.bind_apply_some]
    calc ∑' p, w (some p) * ∑' d', (k p) (some (c, d'))
        ≤ ∑' p : α × β, w (some p) * (f₁ p.1) (some c) := by
          apply ENNReal.tsum_le_tsum
          intro p
          by_cases hp : w (some p) = 0
          · simp [hp]
          · exact mul_le_mul_right (hk_le p hp c) _
      _ = ∑' a, ∑' b, w (some (a, b)) * (f₁ a) (some c) := ENNReal.tsum_prod'
      _ = ∑' a, (∑' b, w (some (a, b))) * (f₁ a) (some c) :=
          tsum_congr fun a => ENNReal.tsum_mul_right
      _ ≤ ∑' a, d₁ (some a) * (f₁ a) (some c) := by
          apply ENNReal.tsum_le_tsum
          intro a
          exact mul_le_mul_left (hle a) _
  · -- deficit additivity
    calc ∑' c, ((d₁.bind f₁) (some c) - ∑' d', (w.bind k) (some (c, d')))
        ≤ ∑' c, ((∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) * (f₁ a) (some c)) +
                 ∑' p : α × β, w (some p) *
                   ((f₁ p.1) (some c) - ∑' d', (k p) (some (c, d')))) := by
          apply ENNReal.tsum_le_tsum
          intro c
          rw [hbind_split c, hM c]
          refine le_trans add_tsub_le_assoc (add_le_add le_rfl ?_)
          refine le_trans (tsum_tsub_tsum_le _ _) ?_
          apply ENNReal.tsum_le_tsum
          intro p
          exact mul_tsub_le' _ _ _
      _ = (∑' c, ∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) * (f₁ a) (some c)) +
          ∑' c, ∑' p : α × β, w (some p) *
            ((f₁ p.1) (some c) - ∑' d', (k p) (some (c, d'))) := ENNReal.tsum_add
      _ ≤ ε₁ + ε₂ := by
          apply add_le_add
          · calc ∑' c, ∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) * (f₁ a) (some c)
                = ∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) * ∑' c, (f₁ a) (some c) := by
                  rw [ENNReal.tsum_comm]
                  exact tsum_congr fun a => ENNReal.tsum_mul_left
              _ ≤ ∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) * 1 := by
                  apply ENNReal.tsum_le_tsum
                  intro a
                  exact mul_le_mul_right (SDistr.tsum_some_le_one (f₁ a)) _
              _ = ∑' a, (d₁ (some a) - ∑' b, w (some (a, b))) := by
                  simp only [mul_one]
              _ ≤ ε₁ := hdef
          · calc ∑' c, ∑' p : α × β, w (some p) *
                  ((f₁ p.1) (some c) - ∑' d', (k p) (some (c, d')))
                = ∑' p : α × β, w (some p) *
                  ∑' c, ((f₁ p.1) (some c) - ∑' d', (k p) (some (c, d'))) := by
                  rw [ENNReal.tsum_comm]
                  exact tsum_congr fun p => ENNReal.tsum_mul_left
              _ ≤ ∑' p : α × β, w (some p) * ε₂ := by
                  apply ENNReal.tsum_le_tsum
                  intro p
                  by_cases hp : w (some p) = 0
                  · simp [hp]
                  · exact mul_le_mul_right (hk_def p hp) _
              _ = (∑' p : α × β, w (some p)) * ε₂ := ENNReal.tsum_mul_right
              _ ≤ 1 * ε₂ := mul_le_mul_left (SDistr.tsum_some_le_one w) _
              _ = ε₂ := one_mul _

/-- **Grade-additive bind** (THE key rule of the graded logic): an
    `ε₁`-lifting of the prefixes and pointwise `ε₂`-liftings of the
    continuations (on the support relation) compose to an
    `(ε₁ + ε₂)`-lifting of the binds.

    The composite witness is `w.bind K` with `K` chosen per pair; both sides'
    marginal conditions come from `bind_left_conditions`, the right side via
    the swapped data. -/
theorem liftRApprox_bind
    {d₁ : SDistr α} {d₂ : SDistr β} {f₁ : α → SDistr γ} {f₂ : β → SDistr δ}
    {R : α → β → Prop} {S : γ → δ → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (hd : liftRApprox ε₁ R d₁ d₂)
    (hf : ∀ a b, R a b → liftRApprox ε₂ S (f₁ a) (f₂ b)) :
    liftRApprox (ε₁ + ε₂) S (d₁.bind f₁) (d₂.bind f₂) := by
  classical
  obtain ⟨w, hw⟩ := hd
  let K : α × β → SDistr (γ × δ) := fun p =>
    if hp : w.joint (some p) ≠ 0 then (hf p.1 p.2 (hw p.1 p.2 hp)).choose.joint
    else SDistr.fail
  have hK_on : ∀ p (hp : w.joint (some p) ≠ 0),
      K p = (hf p.1 p.2 (hw p.1 p.2 hp)).choose.joint := by
    intro p hp
    simp only [K, dif_pos hp]
  -- continuation facts, left side
  have hK_left_le : ∀ p, w.joint (some p) ≠ 0 →
      ∀ c, (∑' d', (K p) (some (c, d'))) ≤ (f₁ p.1) (some c) := by
    intro p hp c
    rw [hK_on p hp]
    exact (hf p.1 p.2 (hw p.1 p.2 hp)).choose.left_le c
  have hK_left_def : ∀ p, w.joint (some p) ≠ 0 →
      (∑' c, ((f₁ p.1) (some c) - ∑' d', (K p) (some (c, d')))) ≤ ε₂ := by
    intro p hp
    simp only [hK_on p hp]
    exact (hf p.1 p.2 (hw p.1 p.2 hp)).choose.left_deficit
  obtain ⟨hLle, hLdef⟩ := bind_left_conditions w.joint K d₁ f₁ ε₁ ε₂
    w.left_le w.left_deficit hK_left_le hK_left_def
  -- swapped data for the right side
  have hws_apply : ∀ (q : β × α),
      (SDistr.swapPair w.joint) (some q) = w.joint (some (q.2, q.1)) :=
    fun q => SDistr.swapPair_apply w.joint q
  have hws_le : ∀ b, (∑' a, (SDistr.swapPair w.joint) (some (b, a))) ≤ d₂ (some b) := by
    intro b
    calc ∑' a, (SDistr.swapPair w.joint) (some (b, a))
        = ∑' a, w.joint (some (a, b)) := tsum_congr fun a => hws_apply (b, a)
      _ ≤ d₂ (some b) := w.right_le b
  have hws_def : (∑' b, (d₂ (some b) - ∑' a, (SDistr.swapPair w.joint) (some (b, a)))) ≤ ε₁ := by
    calc ∑' b, (d₂ (some b) - ∑' a, (SDistr.swapPair w.joint) (some (b, a)))
        = ∑' b, (d₂ (some b) - ∑' a, w.joint (some (a, b))) := by
          refine tsum_congr fun b => ?_
          congr 1
          exact tsum_congr fun a => hws_apply (b, a)
      _ ≤ ε₁ := w.right_deficit
  have hK'_le : ∀ q, (SDistr.swapPair w.joint) (some q) ≠ 0 →
      ∀ d', (∑' c, (SDistr.swapPair (K (q.2, q.1))) (some (d', c)))
        ≤ (f₂ q.1) (some d') := by
    intro q hq d'
    rw [hws_apply q] at hq
    calc ∑' c, (SDistr.swapPair (K (q.2, q.1))) (some (d', c))
        = ∑' c, (K (q.2, q.1)) (some (c, d')) :=
          tsum_congr fun c => SDistr.swapPair_apply _ (d', c)
      _ ≤ (f₂ q.1) (some d') := by
          rw [hK_on (q.2, q.1) hq]
          exact (hf q.2 q.1 (hw q.2 q.1 hq)).choose.right_le d'
  have hK'_def : ∀ q, (SDistr.swapPair w.joint) (some q) ≠ 0 →
      (∑' d', ((f₂ q.1) (some d') -
        ∑' c, (SDistr.swapPair (K (q.2, q.1))) (some (d', c)))) ≤ ε₂ := by
    intro q hq
    rw [hws_apply q] at hq
    calc ∑' d', ((f₂ q.1) (some d') - ∑' c, (SDistr.swapPair (K (q.2, q.1))) (some (d', c)))
        = ∑' d', ((f₂ q.1) (some d') - ∑' c, (K (q.2, q.1)) (some (c, d'))) := by
          refine tsum_congr fun d' => ?_
          congr 1
          exact tsum_congr fun c => SDistr.swapPair_apply _ (d', c)
      _ ≤ ε₂ := by
          simp only [hK_on (q.2, q.1) hq]
          exact (hf q.2 q.1 (hw q.2 q.1 hq)).choose.right_deficit
  obtain ⟨hRle, hRdef⟩ := bind_left_conditions (SDistr.swapPair w.joint)
    (fun q => SDistr.swapPair (K (q.2, q.1))) d₂ f₂ ε₁ ε₂
    hws_le hws_def hK'_le hK'_def
  -- transfer the swapped conclusions back to `w.joint.bind K`
  have hswap : (SDistr.swapPair w.joint).bind (fun q => SDistr.swapPair (K (q.2, q.1)))
      = SDistr.swapPair (w.joint.bind K) := SDistr.swapPair_bind w.joint K
  have hRle' : ∀ d', (∑' c, (w.joint.bind K) (some (c, d'))) ≤ (d₂.bind f₂) (some d') := by
    intro d'
    calc ∑' c, (w.joint.bind K) (some (c, d'))
        = ∑' c, (SDistr.swapPair (w.joint.bind K)) (some (d', c)) :=
          (tsum_congr fun c => SDistr.swapPair_apply _ (d', c)).symm
      _ = ∑' c, ((SDistr.swapPair w.joint).bind
            (fun q => SDistr.swapPair (K (q.2, q.1)))) (some (d', c)) := by rw [hswap]
      _ ≤ (d₂.bind f₂) (some d') := hRle d'
  have hRdef' : (∑' d', ((d₂.bind f₂) (some d') -
      ∑' c, (w.joint.bind K) (some (c, d')))) ≤ ε₁ + ε₂ := by
    calc ∑' d', ((d₂.bind f₂) (some d') - ∑' c, (w.joint.bind K) (some (c, d')))
        = ∑' d', ((d₂.bind f₂) (some d') -
            ∑' c, ((SDistr.swapPair w.joint).bind
              (fun q => SDistr.swapPair (K (q.2, q.1)))) (some (d', c))) := by
          refine tsum_congr fun d' => ?_
          congr 1
          rw [hswap]
          exact (tsum_congr fun c => SDistr.swapPair_apply _ (d', c)).symm
      _ ≤ ε₁ + ε₂ := hRdef
  refine ⟨⟨w.joint.bind K, hLle, hRle', hLdef, hRdef'⟩, ?_⟩
  -- the support of the composite respects S
  intro c d hcd
  rw [SDistr.bind_apply_some] at hcd
  obtain ⟨p, hp⟩ := exists_ne_zero_of_tsum_ne_zero hcd
  have hw0 : w.joint (some p) ≠ 0 := fun h0 => hp (by rw [h0, zero_mul])
  have hK0 : (K p) (some (c, d)) ≠ 0 := fun h0 => hp (by rw [h0, mul_zero])
  rw [hK_on p hw0] at hK0
  exact (hf p.1 p.2 (hw p.1 p.2 hw0)).choose_spec c d hK0

/-! ## Grade-0 embedding: `liftRApprox 0 = liftR` -/

/-- Marginal application formula: binding with the first projection computes
    the left marginal sum. (Converse direction of
    `Coupling.left_marginal_sum`.) -/
theorem SDistr.bind_fst_apply (w : SDistr (α × β)) (a : α) :
    (w.bind fun p => SDistr.pure p.1) (some a) = ∑' b, w (some (a, b)) := by
  classical
  rw [SDistr.bind_apply_some]
  calc ∑' p : α × β, w (some p) * (SDistr.pure p.1) (some a)
      = ∑' a', ∑' b, w (some (a', b)) * (SDistr.pure a') (some a) := ENNReal.tsum_prod'
    _ = ∑' b, w (some (a, b)) * (SDistr.pure a) (some a) := by
        refine tsum_eq_single a fun a' hne => ?_
        refine ENNReal.tsum_eq_zero.mpr fun b => ?_
        rw [SDistr.pure_apply_some, if_neg hne, mul_zero]
    _ = ∑' b, w (some (a, b)) := by
        refine tsum_congr fun b => ?_
        rw [SDistr.pure_apply_some, if_pos rfl, mul_one]

/-- Marginal application formula: binding with the second projection computes
    the right marginal sum. -/
theorem SDistr.bind_snd_apply (w : SDistr (α × β)) (b : β) :
    (w.bind fun p => SDistr.pure p.2) (some b) = ∑' a, w (some (a, b)) := by
  classical
  rw [SDistr.bind_apply_some, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single b fun b' hne => by rw [SDistr.pure_apply_some, if_neg hne, mul_zero]]
  rw [SDistr.pure_apply_some, if_pos rfl, mul_one]

/-- Exact couplings embed at grade 0: the marginal sums are exact, so the
    deficits vanish. -/
theorem liftRApprox_of_liftR {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    (h : d₁ ⟨R⟩# d₂) : liftRApprox 0 R d₁ d₂ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨⟨c.joint,
    fun a => le_of_eq (c.left_marginal_sum a),
    fun b => le_of_eq (c.right_marginal_sum b), ?_, ?_⟩, hc⟩
  · have hz : ∀ a, d₁ (some a) - ∑' b, c.joint (some (a, b)) = 0 := fun a => by
      rw [c.left_marginal_sum a, tsub_self]
    simp only [hz, tsum_zero, le_refl]
  · have hz : ∀ b, d₂ (some b) - ∑' a, c.joint (some (a, b)) = 0 := fun b => by
      rw [c.right_marginal_sum b, tsub_self]
    simp only [hz, tsum_zero, le_refl]

/-- At grade 0 the sub-coupling is an exact coupling: zero total deficit
    forces each pointwise deficit to vanish, so the dominated marginals are
    exact. -/
theorem liftR_of_liftRApprox_zero {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    (h : liftRApprox 0 R d₁ d₂) : d₁ ⟨R⟩# d₂ := by
  obtain ⟨c, hc⟩ := h
  have hL : ∀ a, (∑' b, c.joint (some (a, b))) = d₁ (some a) := by
    intro a
    refine le_antisymm (c.left_le a) (tsub_eq_zero_iff_le.mp ?_)
    exact le_antisymm (le_trans (ENNReal.le_tsum a) c.left_deficit) (zero_le)
  have hR : ∀ b, (∑' a, c.joint (some (a, b))) = d₂ (some b) := by
    intro b
    refine le_antisymm (c.right_le b) (tsub_eq_zero_iff_le.mp ?_)
    exact le_antisymm (le_trans (ENNReal.le_tsum b) c.right_deficit) (zero_le)
  refine ⟨⟨c.joint, ?_, ?_⟩, hc⟩
  · intro a
    rw [SDistr.bind_fst_apply]
    exact hL a
  · intro b
    rw [SDistr.bind_snd_apply]
    exact hR b

/-- Grade-0 approximate lifting coincides with the exact coupling lifting
    (hence, via `spanLift_iff_liftR`, with the exact span lifting). -/
theorem liftRApprox_zero_iff {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β} :
    liftRApprox 0 R d₁ d₂ ↔ (d₁ ⟨R⟩# d₂) :=
  ⟨liftR_of_liftRApprox_zero, liftRApprox_of_liftR⟩

/-! ## Structural rules -/

/-- Monotonicity in the relation. -/
theorem liftRApprox_mono_rel {R S : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    {ε : ℝ≥0∞} (hRS : ∀ a b, R a b → S a b) (h : liftRApprox ε R d₁ d₂) :
    liftRApprox ε S d₁ d₂ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun a b hab => hRS a b (hc a b hab)⟩

/-- Monotonicity in the grade. -/
theorem liftRApprox_mono_eps {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    {ε ε' : ℝ≥0∞} (hε : ε ≤ ε') (h : liftRApprox ε R d₁ d₂) :
    liftRApprox ε' R d₁ d₂ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨⟨c.joint, c.left_le, c.right_le,
    le_trans c.left_deficit hε, le_trans c.right_deficit hε⟩, hc⟩

/-- Swap a sub-coupling. -/
noncomputable def SubCoupling.swap {d₁ : SDistr α} {d₂ : SDistr β} {ε : ℝ≥0∞}
    (c : SubCoupling d₁ d₂ ε) : SubCoupling d₂ d₁ ε where
  joint := SDistr.swapPair c.joint
  left_le := fun b => by
    calc ∑' a, (SDistr.swapPair c.joint) (some (b, a))
        = ∑' a, c.joint (some (a, b)) :=
          tsum_congr fun a => SDistr.swapPair_apply _ (b, a)
      _ ≤ d₂ (some b) := c.right_le b
  right_le := fun a => by
    calc ∑' b, (SDistr.swapPair c.joint) (some (b, a))
        = ∑' b, c.joint (some (a, b)) :=
          tsum_congr fun b => SDistr.swapPair_apply _ (b, a)
      _ ≤ d₁ (some a) := c.left_le a
  left_deficit := by
    calc ∑' b, (d₂ (some b) - ∑' a, (SDistr.swapPair c.joint) (some (b, a)))
        = ∑' b, (d₂ (some b) - ∑' a, c.joint (some (a, b))) := by
          refine tsum_congr fun b => ?_
          congr 1
          exact tsum_congr fun a => SDistr.swapPair_apply _ (b, a)
      _ ≤ ε := c.right_deficit
  right_deficit := by
    calc ∑' a, (d₁ (some a) - ∑' b, (SDistr.swapPair c.joint) (some (b, a)))
        = ∑' a, (d₁ (some a) - ∑' b, c.joint (some (a, b))) := by
          refine tsum_congr fun a => ?_
          congr 1
          exact tsum_congr fun b => SDistr.swapPair_apply _ (b, a)
      _ ≤ ε := c.left_deficit

/-- Symmetry: swap the sub-coupling. -/
theorem liftRApprox_symm {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    {ε : ℝ≥0∞} (h : liftRApprox ε R d₁ d₂) :
    liftRApprox ε (fun b a => R a b) d₂ d₁ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c.swap, fun b a h0 => ?_⟩
  have h0' : c.joint (some (a, b)) ≠ 0 := by
    rwa [show c.swap.joint (some (b, a)) = c.joint (some (a, b)) from
      SDistr.swapPair_apply _ (b, a)] at h0
  exact hc a b h0'

/-! ## Statistical distance and the sample rule -/

/-- One-sided statistical distance between sub-distributions:
    the total mass by which `d₁` exceeds `d₂`. The symmetric statistical
    distance is the pair `(tvMargin d₁ d₂, tvMargin d₂ d₁)`. -/
noncomputable def tvMargin (d₁ d₂ : SDistr α) : ℝ≥0∞ :=
  ∑' a, (d₁ (some a) - d₂ (some a))

theorem tvMargin_triangle (d₁ d₂ d₃ : SDistr α) :
    tvMargin d₁ d₃ ≤ tvMargin d₁ d₂ + tvMargin d₂ d₃ :=
  calc ∑' a, (d₁ (some a) - d₃ (some a))
      ≤ ∑' a, ((d₁ (some a) - d₂ (some a)) + (d₂ (some a) - d₃ (some a))) :=
        ENNReal.tsum_le_tsum fun _ => tsub_le_tsub_add_tsub
    _ = tvMargin d₁ d₂ + tvMargin d₂ d₃ := ENNReal.tsum_add

theorem tsub_min' (a b : ℝ≥0∞) : a - min a b = a - b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

open Classical in
noncomputable def minDiagFn (d₁ d₂ : SDistr α) : Option (α × α) → ℝ≥0∞
  | none => 1 - ∑' a, min (d₁ (some a)) (d₂ (some a))
  | some p => if p.2 = p.1 then min (d₁ (some p.1)) (d₂ (some p.1)) else 0

theorem minDiagFn_some_sum (d₁ d₂ : SDistr α) :
    ∑' p : α × α, minDiagFn d₁ d₂ (some p)
      = ∑' a, min (d₁ (some a)) (d₂ (some a)) := by
  classical
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single a fun b hne => by simp [minDiagFn, hne]]
  simp [minDiagFn]

theorem minDiag_mass_le (d₁ d₂ : SDistr α) :
    (∑' a, min (d₁ (some a)) (d₂ (some a))) ≤ 1 :=
  le_trans (ENNReal.tsum_le_tsum fun _ => min_le_left _ _) (SDistr.tsum_some_le_one d₁)

/-- The min-diagonal joint: mass `min (d₁ a) (d₂ a)` on each diagonal pair
    `(a, a)`, remaining mass on `none`. This is the canonical witness for the
    sample rule: its marginal deficits are exactly the one-sided statistical
    distances. -/
noncomputable def minDiag (d₁ d₂ : SDistr α) : SDistr (α × α) :=
  ⟨minDiagFn d₁ d₂, by
    refine ENNReal.summable.hasSum_iff.mpr ?_
    rw [SDistr.tsum_option_eq_add, minDiagFn_some_sum]
    exact tsub_add_cancel_of_le (minDiag_mass_le d₁ d₂)⟩

theorem minDiag_apply_some (d₁ d₂ : SDistr α) (p : α × α) :
    minDiag d₁ d₂ (some p) = minDiagFn d₁ d₂ (some p) := rfl

theorem minDiag_left_sum (d₁ d₂ : SDistr α) (a : α) :
    ∑' b, minDiag d₁ d₂ (some (a, b)) = min (d₁ (some a)) (d₂ (some a)) := by
  classical
  simp only [minDiag_apply_some]
  rw [tsum_eq_single a fun b hne => by simp [minDiagFn, hne]]
  simp [minDiagFn]

theorem minDiag_right_sum (d₁ d₂ : SDistr α) (b : α) :
    ∑' a, minDiag d₁ d₂ (some (a, b)) = min (d₁ (some b)) (d₂ (some b)) := by
  classical
  simp only [minDiag_apply_some]
  rw [tsum_eq_single b fun a hne => by simp [minDiagFn, Ne.symm hne]]
  simp [minDiagFn]

/-- **Statistical-distance sample rule, distribution level**: distributions
    whose one-sided statistical distances are bounded by `ε` are related by
    the equality relation at grade `ε`, via the min-diagonal sub-coupling. -/
theorem liftRApprox_eq_of_tv {d₁ d₂ : SDistr α} {ε : ℝ≥0∞}
    (hl : tvMargin d₁ d₂ ≤ ε) (hr : tvMargin d₂ d₁ ≤ ε) :
    liftRApprox ε Eq d₁ d₂ := by
  classical
  refine ⟨⟨minDiag d₁ d₂,
    fun a => by rw [minDiag_left_sum]; exact min_le_left _ _,
    fun b => by rw [minDiag_right_sum]; exact min_le_right _ _,
    ?_, ?_⟩, ?_⟩
  · calc ∑' a, (d₁ (some a) - ∑' b, minDiag d₁ d₂ (some (a, b)))
        = ∑' a, (d₁ (some a) - d₂ (some a)) := by
          refine tsum_congr fun a => ?_
          rw [minDiag_left_sum, tsub_min']
      _ ≤ ε := hl
  · calc ∑' b, (d₂ (some b) - ∑' a, minDiag d₁ d₂ (some (a, b)))
        = ∑' b, (d₂ (some b) - d₁ (some b)) := by
          refine tsum_congr fun b => ?_
          rw [minDiag_right_sum, min_comm, tsub_min']
      _ ≤ ε := hr
  · intro a b hab
    by_contra hne
    apply hab
    show minDiagFn d₁ d₂ (some (a, b)) = 0
    simp only [minDiagFn]
    rw [if_neg fun h => hne h.symm]

/-- Converse at equality: an `Eq`-graded sub-coupling concentrates on the
    diagonal, so its deficits dominate the one-sided statistical distances. -/
theorem tvMargin_le_of_liftRApprox_eq {d₁ d₂ : SDistr α} {ε : ℝ≥0∞}
    (h : liftRApprox ε Eq d₁ d₂) :
    tvMargin d₁ d₂ ≤ ε ∧ tvMargin d₂ d₁ ≤ ε := by
  obtain ⟨c, hc⟩ := h
  have hdiag_l : ∀ a, (∑' b, c.joint (some (a, b))) = c.joint (some (a, a)) := by
    intro a
    refine tsum_eq_single a fun b hne => ?_
    by_contra h0
    exact hne (hc a b h0).symm
  have hdiag_r : ∀ b, (∑' a, c.joint (some (a, b))) = c.joint (some (b, b)) := by
    intro b
    refine tsum_eq_single b fun a hne => ?_
    by_contra h0
    exact hne (hc a b h0)
  constructor
  · refine le_trans (ENNReal.tsum_le_tsum fun a => ?_) c.left_deficit
    rw [hdiag_l a]
    refine tsub_le_tsub_left ?_ _
    rw [← hdiag_r a]
    exact c.right_le a
  · refine le_trans (ENNReal.tsum_le_tsum fun b => ?_) c.right_deficit
    rw [hdiag_r b]
    refine tsub_le_tsub_left ?_ _
    rw [← hdiag_l b]
    exact c.left_le b

/-- **Transitivity at equality**: game-hopping inside the lifting. Both hops
    reduce to one-sided statistical distances (`tvMargin_le_of_liftRApprox_eq`),
    which chain by the triangle inequality and rebuild via the min-diagonal
    witness. -/
theorem liftRApprox_trans_eq {d₁ d₂ d₃ : SDistr α} {ε₁ ε₂ : ℝ≥0∞}
    (h₁₂ : liftRApprox ε₁ Eq d₁ d₂) (h₂₃ : liftRApprox ε₂ Eq d₂ d₃) :
    liftRApprox (ε₁ + ε₂) Eq d₁ d₃ := by
  obtain ⟨hl₁, hr₁⟩ := tvMargin_le_of_liftRApprox_eq h₁₂
  obtain ⟨hl₂, hr₂⟩ := tvMargin_le_of_liftRApprox_eq h₂₃
  refine liftRApprox_eq_of_tv
    (le_trans (tvMargin_triangle d₁ d₂ d₃) (add_le_add hl₁ hl₂))
    (le_trans (tvMargin_triangle d₃ d₂ d₁)
      (le_trans (add_le_add hr₂ hr₁) (le_of_eq (add_comm _ _))))

/-! ## The up-to-bad analytic core -/

/-- If two full-mass sub-distributions are pointwise within a budget `bf` of
    each other and the budget totals at most `2ε`, then both one-sided
    statistical distances are at most `ε`. The key step is mass balance: the
    two one-sided distances are *equal* for full-mass distributions, and the
    pointwise excesses on the two sides have disjoint supports, so their sum
    is controlled by the budget once rather than twice. -/
theorem tv_both_le_of_pointwise {ι : Type*} (d₀ d₁ : SDistr ι)
    (bf : ι → ℝ≥0∞) {ε : ℝ≥0∞}
    (h01 : ∀ x, d₀ (some x) ≤ d₁ (some x) + bf x)
    (h10 : ∀ x, d₁ (some x) ≤ d₀ (some x) + bf x)
    (hm0 : ∑' x, d₀ (some x) = 1) (hm1 : ∑' x, d₁ (some x) = 1)
    (hb : (∑' x, bf x) ≤ 2 * ε) :
    tvMargin d₀ d₁ ≤ ε ∧ tvMargin d₁ d₀ ≤ ε := by
  have hsum : tvMargin d₀ d₁ + tvMargin d₁ d₀ ≤ 2 * ε := by
    rw [tvMargin, tvMargin, ← ENNReal.tsum_add]
    refine le_trans (ENNReal.tsum_le_tsum fun x => ?_) hb
    rcases le_total (d₀ (some x)) (d₁ (some x)) with hle | hle
    · rw [tsub_eq_zero_of_le hle, zero_add]
      exact tsub_le_iff_left.mpr (h10 x)
    · rw [tsub_eq_zero_of_le hle, add_zero]
      exact tsub_le_iff_left.mpr (h01 x)
  have hMfin : (∑' x, min (d₀ (some x)) (d₁ (some x))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hm0]
    exact ENNReal.tsum_le_tsum fun x => min_le_left _ _
  have hsplit0 : (∑' x, min (d₀ (some x)) (d₁ (some x))) + tvMargin d₀ d₁ = 1 := by
    rw [tvMargin, ← ENNReal.tsum_add, ← hm0]
    refine tsum_congr fun x => ?_
    rcases le_total (d₀ (some x)) (d₁ (some x)) with hle | hle
    · rw [min_eq_left hle, tsub_eq_zero_of_le hle, add_zero]
    · rw [min_eq_right hle, add_tsub_cancel_of_le hle]
  have hsplit1 : (∑' x, min (d₀ (some x)) (d₁ (some x))) + tvMargin d₁ d₀ = 1 := by
    rw [tvMargin, ← ENNReal.tsum_add, ← hm1]
    refine tsum_congr fun x => ?_
    rcases le_total (d₀ (some x)) (d₁ (some x)) with hle | hle
    · rw [min_eq_left hle, add_tsub_cancel_of_le hle]
    · rw [min_eq_right hle, tsub_eq_zero_of_le hle, add_zero]
  have hteq : tvMargin d₀ d₁ = tvMargin d₁ d₀ :=
    (ENNReal.add_right_inj hMfin).mp (hsplit0.trans hsplit1.symm)
  have ht0 : tvMargin d₀ d₁ ≤ ε := by
    have h2 : 2 * tvMargin d₀ d₁ ≤ 2 * ε := by
      rw [two_mul]
      calc tvMargin d₀ d₁ + tvMargin d₀ d₁
          = tvMargin d₀ d₁ + tvMargin d₁ d₀ := by rw [hteq]
        _ ≤ 2 * ε := hsum
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
  exact ⟨ht0, hteq ▸ ht0⟩

/-! ## The adequacy core -/

/-- Weighted-sum bound from an `Eq`-graded sub-coupling: for any `[0,1]`-valued
    weight function `v`, the `d₁`-average of `v` exceeds the `d₂`-average by at
    most the deficit `ε`. This is the engine of adequacy: `v` is the
    distinguisher's acceptance probability. -/
theorem weighted_le_of_subcoupling {ι : Type*} {d₁ d₂ : SDistr ι}
    {ε : ℝ≥0∞} (c : SubCoupling d₁ d₂ ε) (hsat : c.satisfies Eq)
    (v : ι → ℝ≥0∞) (hv : ∀ i, v i ≤ 1) :
    (∑' i, d₁ (some i) * v i) ≤ (∑' i, d₂ (some i) * v i) + ε := by
  have hsplit : ∀ i, d₁ (some i) * v i =
      (d₁ (some i) - ∑' j, c.joint (some (i, j))) * v i +
      (∑' j, c.joint (some (i, j))) * v i := by
    intro i
    rw [← add_mul, tsub_add_cancel_of_le (c.left_le i)]
  calc ∑' i, d₁ (some i) * v i
      = (∑' i, (d₁ (some i) - ∑' j, c.joint (some (i, j))) * v i) +
        ∑' i, (∑' j, c.joint (some (i, j))) * v i := by
        rw [← ENNReal.tsum_add]
        exact tsum_congr hsplit
    _ ≤ ε + ∑' j, d₂ (some j) * v j := by
        apply add_le_add
        · calc ∑' i, (d₁ (some i) - ∑' j, c.joint (some (i, j))) * v i
              ≤ ∑' i, (d₁ (some i) - ∑' j, c.joint (some (i, j))) * 1 :=
                ENNReal.tsum_le_tsum fun i => mul_le_mul_right (hv i) _
            _ = ∑' i, (d₁ (some i) - ∑' j, c.joint (some (i, j))) := by
                simp only [mul_one]
            _ ≤ ε := c.left_deficit
        · calc ∑' i, (∑' j, c.joint (some (i, j))) * v i
              = ∑' i, ∑' j, c.joint (some (i, j)) * v i :=
                tsum_congr fun _ => ENNReal.tsum_mul_right.symm
            _ = ∑' i, ∑' j, c.joint (some (i, j)) * v j := by
                refine tsum_congr fun i => tsum_congr fun j => ?_
                by_cases h0 : c.joint (some (i, j)) = 0
                · rw [h0, zero_mul, zero_mul]
                · rw [hsat i j h0]
            _ = ∑' j, ∑' i, c.joint (some (i, j)) * v j := ENNReal.tsum_comm
            _ = ∑' j, (∑' i, c.joint (some (i, j))) * v j :=
                tsum_congr fun _ => ENNReal.tsum_mul_right
            _ ≤ ∑' j, d₂ (some j) * v j :=
                ENNReal.tsum_le_tsum fun j => mul_le_mul_left (c.right_le j) _
    _ = (∑' j, d₂ (some j) * v j) + ε := add_comm _ _

end CatCrypt.Prob

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

open scoped ENNReal

variable {α β γ δ : Type*}

/-! ## The graded judgment -/

/-- **ε-graded approximate pRHL judgment** (apRHL-style, statistical-distance
    grading). `rHoareApprox ε Φ c₁ c₂ Ψ` holds when, at every pair of
    `Φ`-related initial heaps, the output sub-distributions are related by the
    approximate span lifting of the paired postcondition at grade `ε`.

    At `ε = 0` this is the exact judgment `rHoare` (`rHoareApprox_zero_iff`). -/
def rHoareApprox (ε : ℝ≥0∞) (Φ : RPre) (c₁ : SPComp α) (c₂ : SPComp β)
    (Ψ : RPost α β) : Prop :=
  ∀ h₁ h₂, Φ h₁ h₂ →
    liftRApprox ε (fun (p₁ : α × Heap) (p₂ : β × Heap) => Ψ p₁.1 p₁.2 p₂.1 p₂.2)
      (c₁ h₁) (c₂ h₂)

/-! ### Grade-0 embedding -/

/-- The exact judgment embeds at grade 0. -/
theorem rHoareApprox_of_rHoare {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (h : rHoare Φ c₁ c₂ Ψ) : rHoareApprox 0 Φ c₁ c₂ Ψ :=
  fun h₁ h₂ hΦ => liftRApprox_of_liftR (h h₁ h₂ hΦ)

/-- Grade 0 recovers the exact judgment. -/
theorem rHoare_of_rHoareApprox_zero {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (h : rHoareApprox 0 Φ c₁ c₂ Ψ) : rHoare Φ c₁ c₂ Ψ :=
  fun h₁ h₂ hΦ => liftR_of_liftRApprox_zero (h h₁ h₂ hΦ)

/-- **Grade-0 embedding**: the graded judgment at `ε = 0` is exactly `rHoare`. -/
theorem rHoareApprox_zero_iff {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β} :
    rHoareApprox 0 Φ c₁ c₂ Ψ ↔ rHoare Φ c₁ c₂ Ψ :=
  ⟨rHoare_of_rHoareApprox_zero, rHoareApprox_of_rHoare⟩

/-! ### Bind and consequence -/

/-- **Grade-additive bind rule**: an `ε₁`-judgment for the prefixes and
    pointwise `ε₂`-judgments for the continuations compose to an
    `(ε₁ + ε₂)`-judgment for the binds. The advantage budget of a sequential
    game is the sum of the budgets of its phases. -/
theorem rHoareApprox_bind {Φ : RPre} {Ψ : RPost α β} {Θ : RPost γ δ}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {f₁ : α → SPComp γ} {f₂ : β → SPComp δ} {ε₁ ε₂ : ℝ≥0∞}
    (hc : rHoareApprox ε₁ Φ c₁ c₂ Ψ)
    (hf : ∀ a b, rHoareApprox ε₂ (fun h₁ h₂ => Ψ a h₁ b h₂) (f₁ a) (f₂ b) Θ) :
    rHoareApprox (ε₁ + ε₂) Φ (c₁.bind f₁) (c₂.bind f₂) Θ := by
  intro h₁ h₂ hΦ
  simp only [SPComp.bind_def]
  apply liftRApprox_bind (hc h₁ h₂ hΦ)
  intro ⟨a, h₁'⟩ ⟨b, h₂'⟩ hΨ
  exact hf a b h₁' h₂' hΨ

/-- Consequence rule: strengthen the precondition, weaken the postcondition,
    relax the grade. -/
theorem rHoareApprox_conseq {Φ Φ' : RPre} {Ψ Ψ' : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β} {ε ε' : ℝ≥0∞}
    (hPre : ∀ h₁ h₂, Φ' h₁ h₂ → Φ h₁ h₂)
    (hPost : ∀ a₁ h₁ a₂ h₂, Ψ a₁ h₁ a₂ h₂ → Ψ' a₁ h₁ a₂ h₂)
    (hε : ε ≤ ε')
    (h : rHoareApprox ε Φ c₁ c₂ Ψ) :
    rHoareApprox ε' Φ' c₁ c₂ Ψ' := by
  intro h₁ h₂ hΦ'
  exact liftRApprox_mono_eps hε
    (liftRApprox_mono_rel (fun p₁ p₂ hp => hPost p₁.1 p₁.2 p₂.1 p₂.2 hp)
      (h h₁ h₂ (hPre h₁ h₂ hΦ')))

/-- Monotonicity in the grade alone. -/
theorem rHoareApprox_mono_eps {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β} {ε ε' : ℝ≥0∞}
    (hε : ε ≤ ε') (h : rHoareApprox ε Φ c₁ c₂ Ψ) :
    rHoareApprox ε' Φ c₁ c₂ Ψ :=
  rHoareApprox_conseq (fun _ _ => id) (fun _ _ _ _ => id) hε h

/-- Reflexivity under an equal-heap precondition (grade 0). -/
theorem rHoareApprox_refl_of_pre {Φ : RPre} (c : SPComp α)
    (hΦ : ∀ h₁ h₂, Φ h₁ h₂ → h₁ = h₂) :
    rHoareApprox 0 Φ c c eqPost :=
  rHoareApprox_of_rHoare
    (rHoare_mono_pre (rHoare_refl c) (fun h₁ h₂ hp => hΦ h₁ h₂ hp))

/-! ### Sample rule -/

/-- **Sample rule**: heap-independent samplers whose distributions are within
    statistical distance `ε` relate at grade `ε`, with equality of the sampled
    values and preservation of the heap relation. -/
theorem rHoareApprox_liftSDistr {X : Type} {d₁ d₂ : SDistr X} {ε : ℝ≥0∞}
    (hl : tvMargin d₁ d₂ ≤ ε) (hr : tvMargin d₂ d₁ ≤ ε) (Φ : RPre) :
    rHoareApprox ε Φ (liftSDistr d₁) (liftSDistr d₂)
      (fun a h₁ b h₂ => a = b ∧ Φ h₁ h₂) := by
  intro h₁ h₂ hΦ
  show liftRApprox ε _
    (d₁.bind fun a => SDistr.pure (a, h₁)) (d₂.bind fun b => SDistr.pure (b, h₂))
  refine liftRApprox_mono_eps (le_of_eq (add_zero ε)) (liftRApprox_bind
    (S := fun (p₁ : X × Heap) (p₂ : X × Heap) => p₁.1 = p₂.1 ∧ Φ p₁.2 p₂.2)
    (liftRApprox_eq_of_tv hl hr) ?_)
  intro a b hab
  exact liftRApprox_of_liftR (liftR_pure ⟨hab, hΦ⟩)

/-! ### Transitivity at equality (game hopping) -/

theorem pairPost_of_eq {p₁ p₂ : α × Heap} (hp : p₁ = p₂) :
    eqPost p₁.1 p₁.2 p₂.1 p₂.2 :=
  ⟨by rw [hp], by rw [hp]⟩

theorem eq_of_pairPost {p₁ p₂ : α × Heap}
    (hp : eqPost p₁.1 p₁.2 p₂.1 p₂.2) : p₁ = p₂ :=
  Prod.ext hp.1 hp.2

/-- **Transitivity at equality pre/post**: chained `ε₁`- and `ε₂`-judgments
    compose to an `(ε₁ + ε₂)`-judgment. This is the game-hopping principle
    internal to the logic. -/
theorem rHoareApprox_trans_eq {c₁ c₂ c₃ : SPComp α} {ε₁ ε₂ : ℝ≥0∞}
    (h₁₂ : rHoareApprox ε₁ eqPre c₁ c₂ eqPost)
    (h₂₃ : rHoareApprox ε₂ eqPre c₂ c₃ eqPost) :
    rHoareApprox (ε₁ + ε₂) eqPre c₁ c₃ eqPost := by
  intro h₁ h₃ heq
  have heq' : h₁ = h₃ := heq
  subst heq'
  have e₁ := liftRApprox_mono_rel (fun p₁ p₂ => eq_of_pairPost)
    (h₁₂ h₁ h₁ rfl)
  have e₂ := liftRApprox_mono_rel (fun p₁ p₂ => eq_of_pairPost)
    (h₂₃ h₁ h₁ rfl)
  exact liftRApprox_mono_rel (fun p₁ p₂ => pairPost_of_eq)
    (liftRApprox_trans_eq e₁ e₂)

/-! ### Up-to-bad -/

/-- **Up-to-bad rule** (relational form of Shoup's fundamental lemma): if two
    `NoFail` games are identical until bad — in both directions, pointwise —
    and the bad event has probability at most `ε` from every initial heap,
    then the games relate at grade `ε` with equality post.

    Compared with `BadEvent.advantage_upto_bad` (which bounds a single
    adversary's advantage at `Heap.empty`), this internalizes the bad-event
    step as a judgment that can be chained by `rHoareApprox_trans_eq` and
    composed by `rHoareApprox_bind`; the advantage bound is recovered — for
    every adversary and every initial heap at once — via
    `rHoareApprox_advantageA`. The symmetrized identical-until-bad hypothesis
    is what the pointwise relational reading of Shoup's "identical until bad"
    means; one direction alone does not control the right marginal deficit. -/
theorem rHoareApprox_upto_bad {G₀ G₁ bad : SPComp Bool} {ε : ℝ≥0∞}
    (h₀₁ : BadEvent.IdenticalUntilBad G₀ G₁ bad)
    (h₁₀ : BadEvent.IdenticalUntilBad G₁ G₀ bad)
    (hnf₀ : SPComp.NoFail G₀) (hnf₁ : SPComp.NoFail G₁)
    (hbad : ∀ h, prTrue bad h ≤ ε) :
    rHoareApprox ε eqPre G₀ G₁ eqPost := by
  intro h₁ h₂ heq
  have heq' : h₁ = h₂ := heq
  subst heq'
  have hb : (∑' x : Bool × Heap, (bad h₁) (some (true, x.2))) ≤ 2 * ε := by
    rw [ENNReal.tsum_prod', tsum_bool, two_mul]
    exact add_le_add (hbad h₁) (hbad h₁)
  obtain ⟨hl, hr⟩ := tv_both_le_of_pointwise (G₀ h₁) (G₁ h₁)
    (fun x => (bad h₁) (some (true, x.2)))
    (fun x => h₀₁.agree_unless_bad h₁ x.1 x.2)
    (fun x => h₁₀.agree_unless_bad h₁ x.1 x.2)
    (SDistr.tsum_some_eq_one_of_none_zero (hnf₀ h₁))
    (SDistr.tsum_some_eq_one_of_none_zero (hnf₁ h₁))
    hb
  exact liftRApprox_mono_rel (fun p₁ p₂ => pairPost_of_eq)
    (liftRApprox_eq_of_tv hl hr)

/-! ### Adequacy -/

/-- **Adequacy, core form**: a grade-`ε` judgment with equal-heap
    precondition and equality postcondition bounds the distinguishing
    probability of every post-processing adversary, from every initial heap. -/
theorem rHoareApprox_absDiff_prTrue {G₀ G₁ : SPComp α} {ε : ℝ≥0∞}
    (h : rHoareApprox ε eqPre G₀ G₁ eqPost)
    (A : α → SPComp Bool) (h₀ : Heap) :
    absDiff (prTrue (SPComp.bind G₀ A) h₀) (prTrue (SPComp.bind G₁ A) h₀) ≤ ε := by
  obtain ⟨c, hc⟩ := h h₀ h₀ rfl
  have hsat : c.satisfies Eq := fun p₁ p₂ h0 => eq_of_pairPost (hc p₁ p₂ h0)
  have hsat' : c.swap.satisfies Eq := by
    intro p₂ p₁ h0
    have h0' : c.joint (some (p₁, p₂)) ≠ 0 := by
      rwa [show c.swap.joint (some (p₂, p₁)) = c.joint (some (p₁, p₂)) from
        SDistr.swapPair_apply _ (p₂, p₁)] at h0
    exact (hsat p₁ p₂ h0').symm
  have hrw : ∀ G : SPComp α, prTrue (SPComp.bind G A) h₀ =
      ∑' p : α × Heap, (G h₀) (some p) * prTrue (A p.1) p.2 := by
    intro G
    rw [prTrue_bind_eq_weighted, SDistr.tsum_option_eq_add]
    simp only [mul_zero, zero_add]
  have hv : ∀ p : α × Heap, prTrue (A p.1) p.2 ≤ 1 := fun p => prTrue_le_one _ _
  have h01 : prTrue (SPComp.bind G₀ A) h₀ ≤ prTrue (SPComp.bind G₁ A) h₀ + ε := by
    rw [hrw G₀, hrw G₁]
    exact weighted_le_of_subcoupling c hsat _ hv
  have h10 : prTrue (SPComp.bind G₁ A) h₀ ≤ prTrue (SPComp.bind G₀ A) h₀ + ε := by
    rw [hrw G₀, hrw G₁]
    exact weighted_le_of_subcoupling c.swap hsat' _ hv
  unfold absDiff
  apply max_le <;> rw [tsub_le_iff_right]
  · exact le_trans h01 (le_of_eq (add_comm _ _))
  · exact le_trans h10 (le_of_eq (add_comm _ _))

/-- **Adequacy for `AdvantageA`**: a grade-`ε` judgment with equal-heap
    precondition and equality postcondition bounds every adversary's
    advantage by `ε`. This is the statement shape consumed by the Crypto
    layer (compare `advantage_zero_of_rHoare`, which is the `ε = 0` case). -/
theorem rHoareApprox_advantageA {G₀ G₁ : SPComp α} {ε : ℝ≥0∞}
    (h : rHoareApprox ε eqPre G₀ G₁ eqPost) (A : α → SPComp Bool) :
    AdvantageA G₀ G₁ A ≤ ε := by
  have hd := rHoareApprox_absDiff_prTrue h A Heap.empty
  simpa [AdvantageA, Advantage, absDiff] using hd

/-- **Adequacy for `sdist`**: the Kleisli statistical distance between the two
    games (as constant Kleisli morphisms) is bounded by the grade. Because the
    judgment quantifies over all equal initial heap pairs, this bounds the
    full distinguisher-supremum, not just the `Heap.empty` instance. -/
theorem rHoareApprox_sdist {G₀ G₁ : SPComp β} {ε : ℝ≥0∞}
    (h : rHoareApprox ε eqPre G₀ G₁ eqPost) :
    sdist (fun _ : Unit => G₀) (fun _ : Unit => G₁) ≤ ε := by
  apply iSup_le
  intro D
  apply iSup_le
  intro _
  apply iSup_le
  intro h₀
  exact rHoareApprox_absDiff_prTrue h D h₀

/-! ### Completeness (converse adequacy)

This is the bridge from reduction-style hypotheses into the graded logic.
Protocol reduction chains state their hop hypotheses in advantage form —
`∀ A, AdvantageA G₀ G₁ A ≤ ε` — not as relational judgments. Completeness
converts such a hypothesis into a `rHoareApprox` judgment at the **same**
grade `ε` (no factor 2, no `NoFail` side condition), so the hops can be
chained inside the logic (`rHoareApprox_trans_eq_of_pre`,
`rHoareApprox_chain`) and the final bound recovered by adequacy
(`rHoareApprox_advantageA_of_pre`).

Why the constant is exactly `ε`: a distinguisher `A : α → SPComp Bool` sees
both the result value and the final heap, so the indicator adversary of
`S = {p | (G₁ h₀) p < (G₀ h₀) p}` accepts with probability exactly the
`S`-mass of each game, and its advantage is the one-sided statistical
distance `tvMargin (G₀ h₀) (G₁ h₀)`. Both one-sided distances are therefore
dominated by the distinguisher supremum, and `liftRApprox_eq_of_tv` rebuilds
the min-diagonal sub-coupling at grade `ε`. Failure mass needs no side
condition: `tvMargin`, `prTrue`, and the sub-coupling deficits all ignore
the `none` mass, so the argument is insensitive to it.

Two precondition strengths, matching the hypothesis strength:

* per-heap hypothesis (equivalently `sdist ≤ ε`) → `eqPre` judgment, and the
  correspondence is an **iff** (`rHoareApprox_eqPre_iff_sdist`);
* `AdvantageA` hypothesis, which by definition runs the games from
  `Heap.empty` only → `emptyPre` judgment, again an iff
  (`rHoareApprox_emptyPre_iff_advantageA`). An `eqPre` conclusion from an
  `AdvantageA` hypothesis is **false** in general: the hypothesis says
  nothing about behavior from non-empty initial heaps. -/

open Classical in
/-- The indicator adversary of a set of (value, heap) pairs: accept exactly
    when the observed pair lies in `S`, leaving the heap untouched. -/
noncomputable def indicatorAdv (S : Set (α × Heap)) : α → SPComp Bool :=
  fun a h => if (a, h) ∈ S then SDistr.pure (true, h) else SDistr.pure (false, h)

theorem prTrue_indicatorAdv_mem {S : Set (α × Heap)} {a : α} {h : Heap}
    (hS : (a, h) ∈ S) : prTrue (indicatorAdv S a) h = 1 := by
  classical
  unfold prTrue indicatorAdv
  rw [if_pos hS]
  rw [tsum_eq_single h fun h' hne => by
    rw [SDistr.pure_apply_some, if_neg fun heq => hne (congrArg Prod.snd heq).symm]]
  rw [SDistr.pure_apply_some, if_pos rfl]

theorem prTrue_indicatorAdv_not_mem {S : Set (α × Heap)} {a : α} {h : Heap}
    (hS : (a, h) ∉ S) : prTrue (indicatorAdv S a) h = 0 := by
  classical
  unfold prTrue indicatorAdv
  rw [if_neg hS]
  refine ENNReal.tsum_eq_zero.mpr fun h' => ?_
  rw [SDistr.pure_apply_some, if_neg fun heq => Bool.noConfusion (congrArg Prod.fst heq)]

/-- Weighted-sum form of `prTrue` over a bind (the `some`-restricted
    instance of `prTrue_bind_eq_weighted`). -/
theorem prTrue_bind_weighted' (G : SPComp α) (A : α → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind G A) h₀ =
      ∑' p : α × Heap, (G h₀) (some p) * prTrue (A p.1) p.2 := by
  rw [prTrue_bind_eq_weighted, SDistr.tsum_option_eq_add]
  simp only [mul_zero, zero_add]

/-- **The optimal distinguisher**: for every pair of games and every initial
    heap there is an adversary whose distinguishing probability dominates the
    one-sided statistical distance of the output distributions — the indicator
    adversary of the set where `G₀` out-weighs `G₁`. -/
theorem exists_adv_tvMargin_le (G₀ G₁ : SPComp α) (h₀ : Heap) :
    ∃ A : α → SPComp Bool,
      tvMargin (G₀ h₀) (G₁ h₀) ≤
        absDiff (prTrue (SPComp.bind G₀ A) h₀) (prTrue (SPComp.bind G₁ A) h₀) := by
  classical
  set S : Set (α × Heap) := {p | (G₁ h₀) (some p) < (G₀ h₀) (some p)} with hSdef
  refine ⟨indicatorAdv S, ?_⟩
  set v : α × Heap → ℝ≥0∞ := fun p => prTrue (indicatorAdv S p.1) p.2 with hvdef
  have hv_mem : ∀ p ∈ S, v p = 1 := fun p hp => prTrue_indicatorAdv_mem hp
  have hv_not : ∀ p ∉ S, v p = 0 := fun p hp => prTrue_indicatorAdv_not_mem hp
  have hge : ∀ p, (G₁ h₀) (some p) * v p ≤ (G₀ h₀) (some p) * v p := by
    intro p
    by_cases hp : p ∈ S
    · rw [hv_mem p hp, mul_one, mul_one]
      exact le_of_lt hp
    · rw [hv_not p hp, mul_zero, mul_zero]
  have htv : tvMargin (G₀ h₀) (G₁ h₀) =
      ∑' p, ((G₀ h₀) (some p) * v p - (G₁ h₀) (some p) * v p) := by
    refine tsum_congr fun p => ?_
    by_cases hp : p ∈ S
    · rw [hv_mem p hp, mul_one, mul_one]
    · rw [hv_not p hp, mul_zero, mul_zero, tsub_self,
        tsub_eq_zero_of_le (not_lt.mp hp)]
  have hfin : (∑' p : α × Heap, (G₁ h₀) (some p) * v p) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∑' p : α × Heap, (G₁ h₀) (some p) * v p
        ≤ ∑' p : α × Heap, (G₁ h₀) (some p) * 1 :=
          ENNReal.tsum_le_tsum fun p => mul_le_mul_right (prTrue_le_one _ _) _
      _ = ∑' p : α × Heap, (G₁ h₀) (some p) := by simp only [mul_one]
      _ ≤ 1 := SDistr.tsum_some_le_one (G₁ h₀)
  have hadd : (∑' p, ((G₀ h₀) (some p) * v p - (G₁ h₀) (some p) * v p)) +
      ∑' p, (G₁ h₀) (some p) * v p = ∑' p, (G₀ h₀) (some p) * v p := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun p => tsub_add_cancel_of_le (hge p)
  calc tvMargin (G₀ h₀) (G₁ h₀)
      = ∑' p, ((G₀ h₀) (some p) * v p - (G₁ h₀) (some p) * v p) := htv
    _ = (∑' p, (G₀ h₀) (some p) * v p) - ∑' p, (G₁ h₀) (some p) * v p :=
        ENNReal.eq_sub_of_add_eq hfin hadd
    _ ≤ absDiff (prTrue (SPComp.bind G₀ (indicatorAdv S)) h₀)
          (prTrue (SPComp.bind G₁ (indicatorAdv S)) h₀) := by
        rw [prTrue_bind_weighted' G₀ (indicatorAdv S) h₀,
          prTrue_bind_weighted' G₁ (indicatorAdv S) h₀]
        exact le_max_left _ _

/-- **Completeness, distribution level**: if every adversary's distinguishing
    probability at heap `h₀` is at most `ε`, the output distributions relate
    at grade `ε` with equality post — the converse of the adequacy core
    `rHoareApprox_absDiff_prTrue`, at the same constant. -/
theorem liftRApprox_eqPost_of_forall_absDiff {G₀ G₁ : SPComp α} {ε : ℝ≥0∞} (h₀ : Heap)
    (h : ∀ A : α → SPComp Bool,
      absDiff (prTrue (SPComp.bind G₀ A) h₀) (prTrue (SPComp.bind G₁ A) h₀) ≤ ε) :
    liftRApprox ε (fun (p₁ : α × Heap) (p₂ : α × Heap) => eqPost p₁.1 p₁.2 p₂.1 p₂.2)
      (G₀ h₀) (G₁ h₀) := by
  obtain ⟨A₀, hA₀⟩ := exists_adv_tvMargin_le G₀ G₁ h₀
  obtain ⟨A₁, hA₁⟩ := exists_adv_tvMargin_le G₁ G₀ h₀
  have hl : tvMargin (G₀ h₀) (G₁ h₀) ≤ ε := hA₀.trans (h A₀)
  have hr : tvMargin (G₁ h₀) (G₀ h₀) ≤ ε :=
    hA₁.trans (le_of_eq (absDiff_comm _ _) |>.trans (h A₁))
  exact liftRApprox_mono_rel (fun p₁ p₂ => pairPost_of_eq)
    (liftRApprox_eq_of_tv hl hr)

/-- **Completeness at `eqPre`**: a per-heap, per-adversary distinguishing
    bound yields the graded judgment at the same grade. This is the converse
    of `rHoareApprox_absDiff_prTrue`. -/
theorem rHoareApprox_of_forall_absDiff {G₀ G₁ : SPComp α} {ε : ℝ≥0∞}
    (h : ∀ (A : α → SPComp Bool) (h₀ : Heap),
      absDiff (prTrue (SPComp.bind G₀ A) h₀) (prTrue (SPComp.bind G₁ A) h₀) ≤ ε) :
    rHoareApprox ε eqPre G₀ G₁ eqPost := by
  intro h₁ h₂ heq
  have heq' : h₁ = h₂ := heq
  subst heq'
  exact liftRApprox_eqPost_of_forall_absDiff h₁ fun A => h A h₁

/-- **Completeness for `sdist`**: converse of `rHoareApprox_sdist`, at the
    same grade. -/
theorem rHoareApprox_of_sdist {G₀ G₁ : SPComp α} {ε : ℝ≥0∞}
    (h : sdist (fun _ : Unit => G₀) (fun _ : Unit => G₁) ≤ ε) :
    rHoareApprox ε eqPre G₀ G₁ eqPost :=
  rHoareApprox_of_forall_absDiff fun A h₀ => by
    refine le_trans ?_ h
    unfold sdist
    refine le_iSup_of_le A (le_iSup_of_le () (le_iSup_of_le h₀ ?_))
    exact le_rfl

/-- **Exact characterization**: the graded judgment at equality pre/post *is*
    the Kleisli statistical distance. Adequacy (`rHoareApprox_sdist`) and
    completeness (`rHoareApprox_of_sdist`) hold at the same constant. -/
theorem rHoareApprox_eqPre_iff_sdist {G₀ G₁ : SPComp α} {ε : ℝ≥0∞} :
    rHoareApprox ε eqPre G₀ G₁ eqPost ↔
      sdist (fun _ : Unit => G₀) (fun _ : Unit => G₁) ≤ ε :=
  ⟨rHoareApprox_sdist, rHoareApprox_of_sdist⟩

/-! ### The `AdvantageA` bridge

`AdvantageA` runs the games from `Heap.empty` only, so its completeness lands
at the precondition fixing both initial heaps to `Heap.empty`. -/

/-- Precondition: both initial heaps are the canonical empty heap. This is
    the strongest precondition certified by an `AdvantageA` hypothesis, which
    observes the games from `Heap.empty` only. -/
def emptyPre : RPre := fun h₁ h₂ => h₁ = Heap.empty ∧ h₂ = Heap.empty

/-- `emptyPre` is diagonal: related heaps are equal. -/
theorem emptyPre_diag : ∀ h₁ h₂, emptyPre h₁ h₂ → h₁ = h₂ :=
  fun _ _ h => h.1.trans h.2.symm

/-- **Completeness for `AdvantageA`** (the bridge from reduction-style
    hypotheses into the graded logic): a `∀`-adversary advantage bound is a
    graded judgment at the **same** grade `ε` — no factor 2 and no `NoFail`
    hypothesis — with the `emptyPre` precondition recording that `AdvantageA`
    observes the games from `Heap.empty` only. Protocol reductions whose hop
    hypotheses are `∀ A, AdvantageA Gᵢ Gᵢ₊₁ A ≤ δᵢ` enter the logic here,
    chain with `rHoareApprox_trans_eq_of_pre` / `rHoareApprox_chain_of_pre`,
    and exit through `rHoareApprox_advantageA_of_pre`.

    The `eqPre` strengthening of the conclusion is false in general: an
    `AdvantageA` hypothesis says nothing about non-empty initial heaps. Use
    `rHoareApprox_of_forall_absDiff` / `rHoareApprox_of_sdist` when a
    per-heap hypothesis is available. -/
theorem rHoareApprox_of_advantageA {G₀ G₁ : SPComp α} {ε : ℝ≥0∞}
    (h : ∀ A : α → SPComp Bool, AdvantageA G₀ G₁ A ≤ ε) :
    rHoareApprox ε emptyPre G₀ G₁ eqPost := by
  rintro h₁ h₂ ⟨he₁, he₂⟩
  subst he₁; subst he₂
  refine liftRApprox_eqPost_of_forall_absDiff Heap.empty fun A => ?_
  simpa [AdvantageA, Advantage, absDiff] using h A

/-- **Completeness for `Advantage`** (non-`A` variant, Bool games): the
    hypothesis quantifies over post-processing distinguishers; this is
    `rHoareApprox_of_advantageA` with the `AdvantageA` layer unfolded. The
    bare single-game bound `Advantage G₀ G₁ ≤ ε` (identity distinguisher
    only) is **not** sufficient: it cannot see the final heap, nor
    distinguish failure from returning `false`. -/
theorem rHoareApprox_of_advantage {G₀ G₁ : SPComp Bool} {ε : ℝ≥0∞}
    (h : ∀ A : Bool → SPComp Bool, Advantage (SPComp.bind G₀ A) (SPComp.bind G₁ A) ≤ ε) :
    rHoareApprox ε emptyPre G₀ G₁ eqPost :=
  rHoareApprox_of_advantageA h

/-- Adequacy core, judgment-free form: a graded `Eq`-post lifting of the
    output distributions at heap `h₀` bounds every adversary's distinguishing
    probability at `h₀`. (The analytic content of
    `rHoareApprox_absDiff_prTrue`, with the judgment hypothesis localized to
    one heap.) -/
theorem absDiff_prTrue_le_of_liftRApprox {G₀ G₁ : SPComp α} {ε : ℝ≥0∞} {h₀ : Heap}
    (h : liftRApprox ε (fun (p₁ : α × Heap) (p₂ : α × Heap) => eqPost p₁.1 p₁.2 p₂.1 p₂.2)
      (G₀ h₀) (G₁ h₀))
    (A : α → SPComp Bool) :
    absDiff (prTrue (SPComp.bind G₀ A) h₀) (prTrue (SPComp.bind G₁ A) h₀) ≤ ε := by
  obtain ⟨c, hc⟩ := h
  have hsat : c.satisfies Eq := fun p₁ p₂ h0 => eq_of_pairPost (hc p₁ p₂ h0)
  have hsat' : c.swap.satisfies Eq := by
    intro p₂ p₁ h0
    have h0' : c.joint (some (p₁, p₂)) ≠ 0 := by
      rwa [show c.swap.joint (some (p₂, p₁)) = c.joint (some (p₁, p₂)) from
        SDistr.swapPair_apply _ (p₂, p₁)] at h0
    exact (hsat p₁ p₂ h0').symm
  have hv : ∀ p : α × Heap, prTrue (A p.1) p.2 ≤ 1 := fun p => prTrue_le_one _ _
  have h01 : prTrue (SPComp.bind G₀ A) h₀ ≤ prTrue (SPComp.bind G₁ A) h₀ + ε := by
    rw [prTrue_bind_weighted' G₀ A h₀, prTrue_bind_weighted' G₁ A h₀]
    exact weighted_le_of_subcoupling c hsat _ hv
  have h10 : prTrue (SPComp.bind G₁ A) h₀ ≤ prTrue (SPComp.bind G₀ A) h₀ + ε := by
    rw [prTrue_bind_weighted' G₀ A h₀, prTrue_bind_weighted' G₁ A h₀]
    exact weighted_le_of_subcoupling c.swap hsat' _ hv
  unfold absDiff
  apply max_le <;> rw [tsub_le_iff_right]
  · exact le_trans h01 (le_of_eq (add_comm _ _))
  · exact le_trans h10 (le_of_eq (add_comm _ _))

/-- **Adequacy at any precondition holding at the empty heaps**: a grade-`ε`
    judgment whose precondition admits `(Heap.empty, Heap.empty)` bounds every
    adversary's advantage by `ε`. Generalizes `rHoareApprox_advantageA` (the
    `eqPre` case) to `emptyPre` and friends. -/
theorem rHoareApprox_advantageA_of_pre {Φ : RPre} {G₀ G₁ : SPComp α} {ε : ℝ≥0∞}
    (hΦ : Φ Heap.empty Heap.empty)
    (h : rHoareApprox ε Φ G₀ G₁ eqPost) (A : α → SPComp Bool) :
    AdvantageA G₀ G₁ A ≤ ε := by
  have hd := absDiff_prTrue_le_of_liftRApprox (h Heap.empty Heap.empty hΦ) A
  simpa [AdvantageA, Advantage, absDiff] using hd

/-- **Round trip**: at `emptyPre`, the graded judgment with equality post is
    *exactly* the `∀`-adversary advantage bound, at the same grade. -/
theorem rHoareApprox_emptyPre_iff_advantageA {G₀ G₁ : SPComp α} {ε : ℝ≥0∞} :
    rHoareApprox ε emptyPre G₀ G₁ eqPost ↔ ∀ A, AdvantageA G₀ G₁ A ≤ ε :=
  ⟨fun h A => rHoareApprox_advantageA_of_pre ⟨rfl, rfl⟩ h A,
    rHoareApprox_of_advantageA⟩

/-! ### Runtime-length graded chains

The graded analogue of the `n`-indexed triangle chain
(`HybridArgument.advantage_hybrid_dep`): hop judgments compose by
`rHoareApprox_trans_eq` with grades summing. Stated over any diagonal
precondition so the `emptyPre` judgments produced by
`rHoareApprox_of_advantageA` chain as well. -/

/-- Transitivity at equality post over any diagonal precondition
    (generalizes `rHoareApprox_trans_eq`, which is the `eqPre` case). -/
theorem rHoareApprox_trans_eq_of_pre {Φ : RPre}
    (hΦ : ∀ h₁ h₂, Φ h₁ h₂ → h₁ = h₂)
    {c₁ c₂ c₃ : SPComp α} {ε₁ ε₂ : ℝ≥0∞}
    (h₁₂ : rHoareApprox ε₁ Φ c₁ c₂ eqPost)
    (h₂₃ : rHoareApprox ε₂ Φ c₂ c₃ eqPost) :
    rHoareApprox (ε₁ + ε₂) Φ c₁ c₃ eqPost := by
  intro h₁ h₃ hp
  have heq : h₁ = h₃ := hΦ h₁ h₃ hp
  subst heq
  have e₁ := liftRApprox_mono_rel (fun p₁ p₂ => eq_of_pairPost) (h₁₂ h₁ h₁ hp)
  have e₂ := liftRApprox_mono_rel (fun p₁ p₂ => eq_of_pairPost) (h₂₃ h₁ h₁ hp)
  exact liftRApprox_mono_rel (fun p₁ p₂ => pairPost_of_eq)
    (liftRApprox_trans_eq e₁ e₂)

/-- **Graded hybrid chain** over a diagonal precondition: `n` hop judgments
    of grades `δ i` compose to a single judgment of grade `∑ i < n, δ i`.
    Graded analogue of `HybridArgument.advantage_hybrid_dep`. -/
theorem rHoareApprox_chain_of_pre {Φ : RPre}
    (hΦ : ∀ h₁ h₂, Φ h₁ h₂ → h₁ = h₂)
    {G : ℕ → SPComp α} {δ : ℕ → ℝ≥0∞} (n : ℕ)
    (h : ∀ i < n, rHoareApprox (δ i) Φ (G i) (G (i + 1)) eqPost) :
    rHoareApprox (∑ i ∈ Finset.range n, δ i) Φ (G 0) (G n) eqPost := by
  induction n with
  | zero =>
    simpa [Finset.range_zero, Finset.sum_empty] using
      rHoareApprox_refl_of_pre (Φ := Φ) (G 0) hΦ
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact rHoareApprox_trans_eq_of_pre hΦ
      (ih fun i hi => h i (Nat.lt_succ_of_lt hi))
      (h k (Nat.lt_succ_self k))

/-- **Graded hybrid chain at `eqPre`**: the canonical instance. -/
theorem rHoareApprox_chain {G : ℕ → SPComp α} {δ : ℕ → ℝ≥0∞} (n : ℕ)
    (h : ∀ i < n, rHoareApprox (δ i) eqPre (G i) (G (i + 1)) eqPost) :
    rHoareApprox (∑ i ∈ Finset.range n, δ i) eqPre (G 0) (G n) eqPost :=
  rHoareApprox_chain_of_pre (fun _ _ heq => heq) n h

/-- **Constant-grade chain**: `n` hops of grade `ε` compose to grade `n * ε`.
    Graded analogue of `HybridArgument.advantage_hybrid_uniform`. -/
theorem rHoareApprox_chain_const {G : ℕ → SPComp α} {ε : ℝ≥0∞} (n : ℕ)
    (h : ∀ i < n, rHoareApprox ε eqPre (G i) (G (i + 1)) eqPost) :
    rHoareApprox (n * ε) eqPre (G 0) (G n) eqPost := by
  have := rHoareApprox_chain (δ := fun _ => ε) n h
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this

/-- Demonstration of the completeness → chain → adequacy round trip on
    advantage-shaped hop hypotheses (the shape protocol reductions provide):
    each `∀`-adversary hop bound enters the logic by completeness, the hops
    chain with grades adding, and adequacy returns the summed advantage
    bound — recovering the triangle inequality as a derived rule of the
    graded logic. -/
example {G₀ G₁ G₂ : SPComp α} {ε₁ ε₂ : ℝ≥0∞}
    (h₀₁ : ∀ A : α → SPComp Bool, AdvantageA G₀ G₁ A ≤ ε₁)
    (h₁₂ : ∀ A : α → SPComp Bool, AdvantageA G₁ G₂ A ≤ ε₂) :
    ∀ A : α → SPComp Bool, AdvantageA G₀ G₂ A ≤ ε₁ + ε₂ := fun A =>
  rHoareApprox_advantageA_of_pre ⟨rfl, rfl⟩
    (rHoareApprox_trans_eq_of_pre emptyPre_diag
      (rHoareApprox_of_advantageA h₀₁)
      (rHoareApprox_of_advantageA h₁₂)) A

/-- The runtime-length round trip: `n` advantage-shaped hop hypotheses enter
    by completeness, chain to grade `∑ i < n, δ i`, and exit by adequacy —
    re-deriving `HybridArgument.advantage_hybrid_dep_bound` through the
    graded logic. -/
example {G : ℕ → SPComp α} {δ : ℕ → ℝ≥0∞} (n : ℕ)
    (h : ∀ i < n, ∀ A : α → SPComp Bool, AdvantageA (G i) (G (i + 1)) A ≤ δ i) :
    ∀ A : α → SPComp Bool,
      AdvantageA (G 0) (G n) A ≤ ∑ i ∈ Finset.range n, δ i := fun A =>
  rHoareApprox_advantageA_of_pre ⟨rfl, rfl⟩
    (rHoareApprox_chain_of_pre emptyPre_diag n fun i hi =>
      rHoareApprox_of_advantageA (h i hi)) A

end CatCrypt.Relational

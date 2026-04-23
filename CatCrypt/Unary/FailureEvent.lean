/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Unary.Bridge
import CatCrypt.Prob.Support

/-!
# Enhanced Failure Event Lemma Variants

This file provides enhanced variants of the Failure Event Lemma (FEL)
from `Bridge.lean`, tailored to common use patterns in cryptographic
security proofs.

## Main results

### Direct advantage bounds
* `advantage_le_prBad` - `Advantage G₀ G₁ ≤ Pr[G₀:bad]` (FEL for Advantage, G₀ lossless)
* `advantage_le_prBad_right` - FEL from the right: `Advantage G₀ G₁ ≤ Pr[G₁:bad]` (G₁ lossless)
* `advantageA_le_prBad` - FEL for `AdvantageA` with explicit adversary

### Game hopping chains
* `advantage_le_two_bad` - Two-step game hopping via FEL
* `advantage_le_three_bad` - Three-step game hopping via FEL

### Event-based FEL
* `prEvent_diff_le_prBad` - `|Pr[G₀:E] - Pr[G₁:E]| ≤ Pr[G₀:bad]` for any event
* `prEvent_agree_of_no_bad` - Events agree exactly when bad never happens

### Composition lemmas
* `agree_trans` - Transitivity of up-to-bad agreement
* `agree_bind_right` - Shared prefix preserves agreement

## References

* EasyCrypt: `fel` tactic, up-to-bad reasoning
* Barthe et al., "CertiCrypt" (failure event lemma)
* Bellare & Rogaway, "The Security of Triple Encryption and a Framework
  for Code-Based Game-Playing Proofs" (game hopping)
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open scoped ENNReal
open Classical

/-! ## Direct Advantage Bounds -/

/-- The Failure Event Lemma stated directly as an Advantage bound.

    `Advantage G₀ G₁ ≤ Pr[G₀ : bad]`

    when G₀ and G₁ agree on all non-bad outcomes and G₀ is lossless.
    This wraps `failure_event_lemma` with the standard `Heap.empty` initial heap. -/
theorem advantage_le_prBad
    (G₀ G₁ : SPComp Bool)
    (bad : Heap → Prop)
    (h_agree : ∀ b h', ¬bad h' →
      (G₀ Heap.empty) (some (b, h')) = (G₁ Heap.empty) (some (b, h')))
    (hll₀ : isLossless G₀) :
    Advantage G₀ G₁ ≤ prEventComp G₀ Heap.empty (fun _ h' => bad h') :=
  failure_event_lemma G₀ G₁ Heap.empty bad h_agree
    (isLossless_implies_if _ hll₀)

/-- FEL from the right side: `Advantage G₀ G₁ ≤ Pr[G₁ : bad]`.

    Symmetric to `advantage_le_prBad`, but bounds by the bad probability
    under G₁ (using G₁'s losslessness). Follows from `failure_event_lemma`
    applied to (G₁, G₀) and using commutativity of Advantage. -/
theorem advantage_le_prBad_right
    (G₀ G₁ : SPComp Bool)
    (bad : Heap → Prop)
    (h_agree : ∀ b h', ¬bad h' →
      (G₀ Heap.empty) (some (b, h')) = (G₁ Heap.empty) (some (b, h')))
    (hll₁ : isLossless G₁) :
    Advantage G₀ G₁ ≤ prEventComp G₁ Heap.empty (fun _ h' => bad h') := by
  -- Advantage is symmetric: Advantage G₀ G₁ = Advantage G₁ G₀
  -- by max commutativity
  have hadv_comm : Advantage G₀ G₁ = Advantage G₁ G₀ := by
    unfold Advantage; exact max_comm _ _
  rw [hadv_comm]
  exact failure_event_lemma G₁ G₀ Heap.empty bad
    (fun b h' hb => (h_agree b h' hb).symm)
    (isLossless_implies_if _ hll₁)

/-- FEL for `AdvantageA` with an explicit adversary.

    When the composed games `G₀.bind A` and `G₁.bind A` agree on non-bad
    outcomes, the advantage through A is bounded by the bad-event probability. -/
theorem advantageA_le_prBad {α : Type}
    (G₀ G₁ : SPComp α) (A : α → SPComp Bool)
    (bad : Heap → Prop)
    (h_agree : ∀ b h', ¬bad h' →
      ((G₀.bind A) Heap.empty) (some (b, h')) =
      ((G₁.bind A) Heap.empty) (some (b, h')))
    (hll₀ : isLossless (G₀.bind A)) :
    AdvantageA G₀ G₁ A ≤ prEventComp (G₀.bind A) Heap.empty (fun _ h' => bad h') := by
  unfold AdvantageA
  exact failure_event_lemma (G₀.bind A) (G₁.bind A) Heap.empty bad h_agree
    (isLossless_implies_if _ hll₀)

/-- FEL with union of bad events: bound by `Pr[G₀ : bad₀ ∨ bad₁]`.

    When games agree on outcomes where neither bad₀ nor bad₁ holds,
    bound the advantage by the probability of either bad event.
    The union bound then gives `Pr[bad₀ ∨ bad₁] ≤ Pr[bad₀] + Pr[bad₁]`
    (use `prEvent_union_le` from Event.lean for that step). -/
theorem advantage_le_prBad_union
    (G₀ G₁ : SPComp Bool)
    (bad₀ bad₁ : Heap → Prop)
    (h_agree : ∀ b h', ¬bad₀ h' → ¬bad₁ h' →
      (G₀ Heap.empty) (some (b, h')) = (G₁ Heap.empty) (some (b, h')))
    (hll₀ : isLossless G₀) :
    Advantage G₀ G₁ ≤
      prEventComp G₀ Heap.empty (fun _ h' => bad₀ h' ∨ bad₁ h') := by
  apply advantage_le_prBad G₀ G₁ (fun h' => bad₀ h' ∨ bad₁ h')
  · intro b h' hbad
    push_neg at hbad
    exact h_agree b h' hbad.1 hbad.2
  · exact hll₀

/-! ## Game Hopping Chains -/

/-- Two-step game hopping via FEL.

    `Advantage G₀ G₂ ≤ Pr[G₀:bad₀₁] + Pr[G₁:bad₁₂]`

    when G₀ ≈ G₁ (up to bad₀₁) and G₁ ≈ G₂ (up to bad₁₂). -/
theorem advantage_le_two_bad
    (G₀ G₁ G₂ : SPComp Bool)
    (bad₀₁ bad₁₂ : Heap → Prop)
    (h_agree₀₁ : ∀ b h', ¬bad₀₁ h' →
      (G₀ Heap.empty) (some (b, h')) = (G₁ Heap.empty) (some (b, h')))
    (h_agree₁₂ : ∀ b h', ¬bad₁₂ h' →
      (G₁ Heap.empty) (some (b, h')) = (G₂ Heap.empty) (some (b, h')))
    (hll₀ : isLossless G₀)
    (hll₁ : isLossless G₁) :
    Advantage G₀ G₂ ≤
      prEventComp G₀ Heap.empty (fun _ h' => bad₀₁ h') +
      prEventComp G₁ Heap.empty (fun _ h' => bad₁₂ h') := by
  calc Advantage G₀ G₂
      ≤ Advantage G₀ G₁ + Advantage G₁ G₂ := advantage_triangle G₀ G₁ G₂
    _ ≤ prEventComp G₀ Heap.empty (fun _ h' => bad₀₁ h') +
        prEventComp G₁ Heap.empty (fun _ h' => bad₁₂ h') := by
        apply add_le_add
        · exact advantage_le_prBad G₀ G₁ bad₀₁ h_agree₀₁ hll₀
        · exact advantage_le_prBad G₁ G₂ bad₁₂ h_agree₁₂ hll₁

/-- Three-step game hopping via FEL.

    `Advantage G₀ G₃ ≤ Pr[G₀:bad₀₁] + Pr[G₁:bad₁₂] + Pr[G₂:bad₂₃]`

    A common pattern in cryptographic proofs (e.g., PRF/PRP switching). -/
theorem advantage_le_three_bad
    (G₀ G₁ G₂ G₃ : SPComp Bool)
    (bad₀₁ bad₁₂ bad₂₃ : Heap → Prop)
    (h_agree₀₁ : ∀ b h', ¬bad₀₁ h' →
      (G₀ Heap.empty) (some (b, h')) = (G₁ Heap.empty) (some (b, h')))
    (h_agree₁₂ : ∀ b h', ¬bad₁₂ h' →
      (G₁ Heap.empty) (some (b, h')) = (G₂ Heap.empty) (some (b, h')))
    (h_agree₂₃ : ∀ b h', ¬bad₂₃ h' →
      (G₂ Heap.empty) (some (b, h')) = (G₃ Heap.empty) (some (b, h')))
    (hll₀ : isLossless G₀)
    (hll₁ : isLossless G₁)
    (hll₂ : isLossless G₂) :
    Advantage G₀ G₃ ≤
      prEventComp G₀ Heap.empty (fun _ h' => bad₀₁ h') +
      prEventComp G₁ Heap.empty (fun _ h' => bad₁₂ h') +
      prEventComp G₂ Heap.empty (fun _ h' => bad₂₃ h') := by
  calc Advantage G₀ G₃
      ≤ Advantage G₀ G₂ + Advantage G₂ G₃ := advantage_triangle G₀ G₂ G₃
    _ ≤ (prEventComp G₀ Heap.empty (fun _ h' => bad₀₁ h') +
         prEventComp G₁ Heap.empty (fun _ h' => bad₁₂ h')) +
        prEventComp G₂ Heap.empty (fun _ h' => bad₂₃ h') := by
        apply add_le_add
        · exact advantage_le_two_bad G₀ G₁ G₂ bad₀₁ bad₁₂ h_agree₀₁ h_agree₁₂ hll₀ hll₁
        · exact advantage_le_prBad G₂ G₃ bad₂₃ h_agree₂₃ hll₂

/-! ## Event-Based FEL -/

/-- FEL for arbitrary events: `|Pr[G₀:E] - Pr[G₁:E]| ≤ Pr[G₀:bad]`.

    This generalizes the standard FEL from `prTrue` (event b=true) to
    any event E on the output value and heap. When G₀ and G₁ agree
    on non-bad outcomes, the probabilities of any event E also agree
    up to the bad probability. -/
theorem prEvent_diff_le_prBad
    (G₀ G₁ : SPComp Bool) (h₀ : Heap)
    (E : Bool → Heap → Prop) (bad : Heap → Prop)
    (h_agree : ∀ b h', ¬bad h' →
      (G₀ h₀) (some (b, h')) = (G₁ h₀) (some (b, h')))
    (hll₀ : isLosslessIf (fun h => h = h₀) G₀) :
    (prEventComp G₀ h₀ E - prEventComp G₁ h₀ E) ⊔
    (prEventComp G₁ h₀ E - prEventComp G₀ h₀ E) ≤
      prEventComp G₀ h₀ (fun _ h' => bad h') := by
  set Pb := prEventComp G₀ h₀ (fun _ h' => bad h')
  -- One-sided bound: prEvent G₀ ≤ prEvent G₁ + Pb
  have h1 : prEventComp G₀ h₀ E ≤ prEventComp G₁ h₀ E + Pb := by
    unfold prEventComp prEvent
    calc ∑' p : Bool × Heap, (if E p.1 p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)
        ≤ ∑' p : Bool × Heap,
          ((if E p.1 p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞) +
           (if bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) := by
          apply ENNReal.tsum_le_tsum; intro p
          by_cases hb : bad p.2
          · by_cases hE : E p.1 p.2 <;> simp [hE, hb, le_self_add]
          · by_cases hE : E p.1 p.2 <;> simp [hE, hb, h_agree p.1 p.2 hb]
      _ = (∑' p, (if E p.1 p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)) +
          (∑' p, (if bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) := ENNReal.tsum_add
  -- One-sided bound: prEvent G₁ ≤ prEvent G₀ + Pb
  have h2 : prEventComp G₁ h₀ E ≤ prEventComp G₀ h₀ E + Pb := by
    unfold prEventComp prEvent
    -- Bad mass monotonicity: bad mass of G₁ ≤ Pb (bad mass of G₀)
    have bad_G₁_le : (∑' p : Bool × Heap,
        (if bad p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)) ≤
        (∑' p : Bool × Heap,
        (if bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) := by
      set bad₁ := ∑' p : Bool × Heap, (if bad p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)
      set bad₀ := ∑' p : Bool × Heap, (if bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)
      set N := ∑' p : Bool × Heap, (if ¬bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)
      have hnonbad : (∑' p : Bool × Heap,
          (if ¬bad p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)) = N := by
        apply tsum_congr; intro p
        by_cases hb : bad p.2 <;> simp [hb, h_agree p.1 p.2]
      have hG₀_total := tsum_some_of_mass_one (G₀ h₀) (hll₀ h₀ rfl)
      have hG₀_split := tsum_ite_add_compl (fun p : Bool × Heap => bad p.2)
        (fun p => (G₀ h₀) (some p))
      rw [hG₀_total] at hG₀_split
      have hG₁_total_le : ∑' p : Bool × Heap, (G₁ h₀) (some p) ≤ 1 := by
        calc ∑' p : Bool × Heap, (G₁ h₀) (some p)
            = SDistr.mass (G₁ h₀) := tsum_some_eq_mass (G₁ h₀)
          _ ≤ 1 := by unfold SDistr.mass; exact tsub_le_self
      have hG₁_split := tsum_ite_add_compl (fun p : Bool × Heap => bad p.2)
        (fun p => (G₁ h₀) (some p))
      rw [hnonbad] at hG₁_split
      have hle : bad₁ + N ≤ bad₀ + N :=
        (le_of_eq hG₁_split).trans (hG₁_total_le.trans (le_of_eq hG₀_split.symm))
      have hN_ne_top : N ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (le_add_self.trans (le_of_eq hG₀_split))
      rwa [ENNReal.add_le_add_iff_right hN_ne_top] at hle
    calc ∑' p : Bool × Heap, (if E p.1 p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)
        ≤ ∑' p : Bool × Heap,
          ((if E p.1 p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞) +
           (if bad p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)) := by
          apply ENNReal.tsum_le_tsum; intro p
          by_cases hb : bad p.2
          · by_cases hE : E p.1 p.2 <;> simp [hE, hb, le_self_add]
          · by_cases hE : E p.1 p.2 <;> simp [hE, hb, (h_agree p.1 p.2 hb).symm]
      _ = (∑' p, (if E p.1 p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) +
          (∑' p, (if bad p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)) := ENNReal.tsum_add
      _ ≤ (∑' p, (if E p.1 p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) +
          (∑' p, (if bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) :=
            add_le_add le_rfl bad_G₁_le
  exact max_le (tsub_le_iff_left.mpr h1) (tsub_le_iff_left.mpr h2)

/-- When games agree on all outcomes, event probabilities agree exactly. -/
theorem prEvent_agree_of_no_bad
    (G₀ G₁ : SPComp Bool) (h₀ : Heap)
    (E : Bool → Heap → Prop)
    (h_agree : ∀ b h', (G₀ h₀) (some (b, h')) = (G₁ h₀) (some (b, h'))) :
    prEventComp G₀ h₀ E = prEventComp G₁ h₀ E := by
  unfold prEventComp prEvent
  congr 1; funext p
  by_cases hE : E p.1 p.2
  · simp only [hE, ↓reduceIte, h_agree p.1 p.2]
  · simp only [hE, ↓reduceIte]

/-! ## Composition Lemmas -/

/-- Transitivity of up-to-bad reasoning: if G₀ ≈ G₁ up to bad₁ and
    G₁ ≈ G₂ up to bad₂, then G₀ ≈ G₂ when neither bad holds. -/
theorem agree_trans
    (G₀ G₁ G₂ : SPComp Bool) (h₀ : Heap)
    (bad₁ bad₂ : Heap → Prop)
    (h₁ : ∀ b h', ¬bad₁ h' →
      (G₀ h₀) (some (b, h')) = (G₁ h₀) (some (b, h')))
    (h₂ : ∀ b h', ¬bad₂ h' →
      (G₁ h₀) (some (b, h')) = (G₂ h₀) (some (b, h'))) :
    ∀ b h', ¬bad₁ h' → ¬bad₂ h' →
      (G₀ h₀) (some (b, h')) = (G₂ h₀) (some (b, h')) := by
  intro b h' hb₁ hb₂
  exact (h₁ b h' hb₁).trans (h₂ b h' hb₂)

/-- If games agree on non-bad outcomes, adding the same prefix preserves agreement.

    When c is a shared prefix computation and G₀, G₁ are continuations that
    agree on non-bad outcomes, then `c.bind G₀` and `c.bind G₁` also agree
    on non-bad outcomes. -/
theorem agree_bind_right {α : Type}
    (c : SPComp α) (G₀ G₁ : α → SPComp Bool) (h₀ : Heap)
    (bad : Heap → Prop)
    (h_agree : ∀ a h₁ b h', ¬bad h' →
      (G₀ a h₁) (some (b, h')) = (G₁ a h₁) (some (b, h'))) :
    ∀ b h', ¬bad h' →
      ((c.bind G₀) h₀) (some (b, h')) =
      ((c.bind G₁) h₀) (some (b, h')) := by
  intro b h' hbad
  simp only [SPComp.bind, SDistr.bind, PMF.bind_apply]
  congr 1; funext oa
  cases oa with
  | none => rfl
  | some p =>
    obtain ⟨a, h₁⟩ := p
    simp only
    congr 1
    exact h_agree a h₁ b h' hbad

/-- Different prefixes with the same continuation: if two prefixes agree on
    non-bad intermediate states and bad is backward-monotone through the
    continuation, then the composed computations agree on non-bad outcomes.

    Backward monotonicity means: if the output of `k a h₁` can reach a non-bad
    final state `h₂`, then the intermediate state `h₁` was also non-bad.

    This is the dual of `agree_bind_right`, where the CONTINUATION differs and
    the prefix is shared. Together, these compose into `agree_bind_both`. -/
theorem agree_bind_left {α : Type}
    (f₁ f₂ : SPComp α) (k : α → SPComp Bool) (h₀ : Heap)
    (bad : Heap → Prop)
    (h_agree : ∀ (a : α) (h₁ : Heap), ¬bad h₁ →
      (f₁ h₀) (some (a, h₁)) = (f₂ h₀) (some (a, h₁)))
    (h_bad_bwd : ∀ (a : α) (h₁ : Heap) (b : Bool) (h₂ : Heap),
      (k a h₁) (some (b, h₂)) ≠ 0 → ¬bad h₂ → ¬bad h₁) :
    ∀ (b : Bool) (h' : Heap), ¬bad h' →
      ((f₁.bind k) h₀) (some (b, h')) =
      ((f₂.bind k) h₀) (some (b, h')) := by
  intro b h' hbad
  simp only [SPComp.bind, SDistr.bind, PMF.bind_apply]
  congr 1; funext oa
  cases oa with
  | none => simp [SDistr.fail_apply_some, mul_zero]
  | some p =>
    obtain ⟨a, h₁⟩ := p
    simp only
    by_cases hk : (k a h₁) (some (b, h')) = 0
    · simp [hk, mul_zero]
    · congr 1
      exact h_agree a h₁ (h_bad_bwd a h₁ b h' hk hbad)

/-- General composition: both prefix and continuation may differ.

    If two prefixes agree on non-bad intermediate states, two continuations
    agree on non-bad final states, and bad is backward-monotone through the
    first continuation, then the composed computations agree on non-bad outcomes.

    This combines the patterns of `agree_bind_left` and `agree_bind_right`.
    It is the key building block for up-to-bad reasoning with oracle composition. -/
theorem agree_bind_both {α : Type}
    (f₁ f₂ : SPComp α) (k₁ k₂ : α → SPComp Bool) (h₀ : Heap)
    (bad : Heap → Prop)
    (h_prefix : ∀ (a : α) (h₁ : Heap), ¬bad h₁ →
      (f₁ h₀) (some (a, h₁)) = (f₂ h₀) (some (a, h₁)))
    (h_cont : ∀ (a : α) (h₁ : Heap) (b : Bool) (h₂ : Heap), ¬bad h₂ →
      (k₁ a h₁) (some (b, h₂)) = (k₂ a h₁) (some (b, h₂)))
    (h_bad_bwd : ∀ (a : α) (h₁ : Heap) (b : Bool) (h₂ : Heap),
      (k₁ a h₁) (some (b, h₂)) ≠ 0 → ¬bad h₂ → ¬bad h₁) :
    ∀ (b : Bool) (h' : Heap), ¬bad h' →
      ((f₁.bind k₁) h₀) (some (b, h')) =
      ((f₂.bind k₂) h₀) (some (b, h')) := by
  intro b h' hbad
  simp only [SPComp.bind, SDistr.bind, PMF.bind_apply]
  congr 1; funext oa
  cases oa with
  | none => simp [SDistr.fail_apply_some, mul_zero]
  | some p =>
    obtain ⟨a, h₁⟩ := p
    simp only
    have hk_eq : (k₁ a h₁) (some (b, h')) = (k₂ a h₁) (some (b, h')) :=
      h_cont a h₁ b h' hbad
    rw [hk_eq]
    by_cases hw : (k₂ a h₁) (some (b, h')) = 0
    · simp [hw, mul_zero]
    · congr 1
      rw [← hk_eq] at hw
      exact h_prefix a h₁ (h_bad_bwd a h₁ b h' hw hbad)

/-- FEL variant: if games agree on non-bad outcomes and both sides are
    lossless, then bad mass is the same in both games.

    This is a helper for proofs that need to move between
    `Pr[G₀:bad]` and `Pr[G₁:bad]`. -/
theorem prBad_le_of_agree
    (G₀ G₁ : SPComp Bool) (h₀ : Heap)
    (bad : Heap → Prop)
    (h_agree : ∀ b h', ¬bad h' →
      (G₀ h₀) (some (b, h')) = (G₁ h₀) (some (b, h')))
    (hll₀ : isLosslessIf (fun h => h = h₀) G₀) :
    prEventComp G₁ h₀ (fun _ h' => bad h') ≤
      prEventComp G₀ h₀ (fun _ h' => bad h') := by
  unfold prEventComp prEvent
  dsimp only
  set bad₁ := ∑' p : Bool × Heap, if bad p.2 then (G₁ h₀) (some p) else 0
  set bad₀ := ∑' p : Bool × Heap, if bad p.2 then (G₀ h₀) (some p) else 0
  set N := ∑' p : Bool × Heap, if ¬bad p.2 then (G₀ h₀) (some p) else 0
  have hnonbad : (∑' p : Bool × Heap, if ¬bad p.2 then (G₁ h₀) (some p) else 0) = N := by
    apply tsum_congr; intro p
    by_cases hb : bad p.2 <;> simp [hb, h_agree p.1 p.2]
  have hG₀_total := tsum_some_of_mass_one (G₀ h₀) (hll₀ h₀ rfl)
  have hG₀_split := tsum_ite_add_compl (fun p : Bool × Heap => bad p.2)
    (fun p => (G₀ h₀) (some p))
  rw [hG₀_total] at hG₀_split
  have hG₁_total_le : ∑' p : Bool × Heap, (G₁ h₀) (some p) ≤ 1 := by
    calc ∑' p : Bool × Heap, (G₁ h₀) (some p)
        = SDistr.mass (G₁ h₀) := tsum_some_eq_mass (G₁ h₀)
      _ ≤ 1 := by unfold SDistr.mass; exact tsub_le_self
  have hG₁_split := tsum_ite_add_compl (fun p : Bool × Heap => bad p.2)
    (fun p => (G₁ h₀) (some p))
  rw [hnonbad] at hG₁_split
  -- hG₁_split : bad₁ + N = G₁_total, hG₀_split : bad₀ + N = 1
  have hle : bad₁ + N ≤ bad₀ + N :=
    (le_of_eq hG₁_split).trans (hG₁_total_le.trans (le_of_eq hG₀_split.symm))
  have hN_ne_top : N ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_add_self.trans (le_of_eq hG₀_split))
  rwa [ENNReal.add_le_add_iff_right hN_ne_top] at hle

/-- When both games are lossless and agree on non-bad outcomes,
    their bad-event probabilities are equal.

    Combines `prBad_le_of_agree` in both directions. -/
theorem prBad_eq_of_agree
    (G₀ G₁ : SPComp Bool) (h₀ : Heap)
    (bad : Heap → Prop)
    (h_agree : ∀ b h', ¬bad h' →
      (G₀ h₀) (some (b, h')) = (G₁ h₀) (some (b, h')))
    (hll₀ : isLosslessIf (fun h => h = h₀) G₀)
    (hll₁ : isLosslessIf (fun h => h = h₀) G₁) :
    prEventComp G₀ h₀ (fun _ h' => bad h') =
      prEventComp G₁ h₀ (fun _ h' => bad h') := by
  apply le_antisymm
  · exact prBad_le_of_agree G₁ G₀ h₀ bad
      (fun b h' hb => (h_agree b h' hb).symm) hll₁
  · exact prBad_le_of_agree G₀ G₁ h₀ bad h_agree hll₀

end CatCrypt.Unary

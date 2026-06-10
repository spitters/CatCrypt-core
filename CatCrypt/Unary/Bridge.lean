/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Unary.Judgment
import CatCrypt.Unary.Lossless
import CatCrypt.Unary.Event
import CatCrypt.Relational.Judgment
import CatCrypt.Crypto.Advantage
import CatCrypt.Prob.Support

/-!
# Bridge: Connecting Unary Logic to Relational Logic and Probability

This file bridges the unary probabilistic Hoare logic (pHL) with the relational
probabilistic Hoare logic (pRHL) and the advantage/probability framework.

## Main results

### pHL ↔ pRHL connections

* `pHoare_of_rHoare_diag` - Extract unary facts from a relational judgment on the diagonal
* `rHoare_of_pHoare_l` - Embed a unary judgment on the left side of a relational judgment

### pHL → Probability bounds

* `prTrue_eq_one_of_pHoare` - If all Boolean outcomes are `true` and the computation is
  lossless, then `Pr[true] = 1` ("byphoare" direction from EasyCrypt)
* `prTrue_eq_zero_of_pHoare` - If all Boolean outcomes are `false`, then `Pr[true] = 0`
* `advantage_zero_of_same_result` - Advantage is 0 when both games deterministically
  return the same Boolean

### Failure Event Lemma (FEL)

* `failure_event_lemma` - The fundamental up-to-bad reasoning technique:
  `|Pr[G₀:A] - Pr[G₁:A]| ≤ Pr[G₀:bad]` when G₀ and G₁ agree on non-bad outcomes

## References

* EasyCrypt: `byphoare`, `phoare`, and `fel` tactics
* SSProve (Rocq): `rhl_semantics`, advantage framework
* Barthe et al., "CertiCrypt: Computer-Verified, Implementation-Level Code-Based
  Cryptographic Proofs" (failure event lemma)
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open scoped ENNReal

variable {α β : Type*}

/-! ## Connecting pHL to pRHL -/

/-- From pRHL with same program to unary pHL.

If a relational judgment `rHoare` establishes properties for `(c, c)` on the
diagonal (i.e., starting from equal heaps), we can extract a unary pHL judgment.

The precondition `P` on the single heap becomes `h₁ = h₂ ∧ P h₁` in the
relational setting, and the relational postcondition `a₁ = a₂ ∧ h₁ = h₂ ∧ Q a₁ h₁`
yields the unary postcondition `Q`. -/
theorem pHoare_of_rHoare_diag {P : UPre} {c : SPComp α} {Q : UPost α}
    (h : rHoare (fun h₁ h₂ => h₁ = h₂ ∧ P h₁) c c
      (fun a₁ h₁ a₂ h₂ => a₁ = a₂ ∧ h₁ = h₂ ∧ Q a₁ h₁)) :
    pHoare P c Q := by
  intro h₀ hP a h' hsupp
  -- Get coupling from rHoare on the diagonal (h₁ = h₂ = h₀)
  obtain ⟨coup, hsat⟩ := h h₀ h₀ ⟨rfl, hP⟩
  -- By left marginal sum: ∑' p₂, coup.joint(some ((a,h'), p₂)) = (c h₀)(some (a,h'))
  have hmarg := coup.left_marginal_sum (a, h')
  -- Since (c h₀)(some (a,h')) ≠ 0, the marginal sum is nonzero
  rw [← hmarg] at hsupp
  -- Extract witness from nonzero tsum (contrapositive of tsum_eq_zero)
  rw [ne_eq, ENNReal.tsum_eq_zero] at hsupp
  push_neg at hsupp
  obtain ⟨p₂, hp₂⟩ := hsupp
  -- The coupling postcondition gives Q a h'
  exact (hsat (a, h') p₂ hp₂).2.2

/-- From unary to relational: embed pHL judgment on left side.

If `c₁` satisfies `Q` unarily (via pHL) and we also have a relational judgment
for `c₁ ~ c₂`, we can combine the preconditions. The key observation is that
the relational coupling already provides all needed information; the unary
judgment serves as additional documentation that `Q` holds on the left. -/
theorem rHoare_of_pHoare_l {P : UPre} {Q : UPost α} {R : RPre}
    {c₁ : SPComp α} {c₂ : SPComp β} {Ψ : RPost α β}
    (hph : pHoare P c₁ Q)
    (hrel : rHoare R c₁ c₂ Ψ)
    (hcombine : ∀ a₁ h₁ a₂ h₂, Q a₁ h₁ → Ψ a₁ h₁ a₂ h₂ → Ψ a₁ h₁ a₂ h₂) :
    rHoare (fun h₁ h₂ => P h₁ ∧ R h₁ h₂) c₁ c₂ Ψ := by
  intro h₁ h₂ ⟨_, hR⟩
  exact hrel h₁ h₂ hR

/-- Symmetric variant: embed pHL judgment on right side. -/
theorem rHoare_of_pHoare_r {P : UPre} {Q : UPost β} {R : RPre}
    {c₁ : SPComp α} {c₂ : SPComp β} {Ψ : RPost α β}
    (hph : pHoare P c₂ Q)
    (hrel : rHoare R c₁ c₂ Ψ) :
    rHoare (fun h₁ h₂ => R h₁ h₂ ∧ P h₂) c₁ c₂ Ψ := by
  intro h₁ h₂ ⟨hR, _⟩
  exact hrel h₁ h₂ hR

/-! ## Connecting pHL to probability bounds -/

/-- Key bridge lemma: if pHoare says all Boolean outcomes are `true`,
and the computation is lossless, then `Pr[true] = 1`.

This is the "byphoare" direction from EasyCrypt: use a unary Hoare-logic
proof to establish a probability fact.

**Proof idea**: Since the computation is lossless, the total mass is 1.
The pHoare judgment ensures every outcome in the support has `b = true`.
Therefore, all mass is concentrated on `(true, _)` outcomes, and
`prTrue G h₀ = ∑' h, G h₀ (some (true, h)) = 1`. -/
theorem prTrue_eq_one_of_pHoare
    (G : SPComp Bool) (h₀ : Heap)
    (hph : pHoare (fun h => h = h₀) G (fun b _ => b = true))
    (hll : isLosslessIf (fun h => h = h₀) G) :
    prTrue G h₀ = 1 := by
  -- All false outcomes have probability 0
  have hfalse : ∀ h, (G h₀) (some (false, h)) = 0 := by
    intro h
    by_contra hne
    have := hph h₀ rfl false h hne
    simp at this
  -- mass = 1 from losslessness
  have hmass := hll h₀ rfl
  -- prTrue = ∑' h, G h₀ (some (true, h))
  -- total some mass = ∑' (b, h), G h₀ (some (b, h)) = mass = 1
  -- Split by Bool: = ∑' h, G h₀ (some (true, h)) + ∑' h, G h₀ (some (false, h))
  -- The false part is 0, so prTrue = 1
  have htotal := tsum_some_of_mass_one (G h₀) hmass
  -- htotal : ∑' (p : Bool × Heap), (G h₀) (some p) = 1
  -- Rewrite using tsum over Bool × Heap = tsum_true + tsum_false
  -- The false part is 0
  have hfalse_sum : ∑' h, (G h₀) (some (false, h)) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr; exact hfalse
  -- We need: ∑' (p : Bool × Heap) = ∑' b, ∑' h, ...
  -- which splits into b=true and b=false parts
  unfold prTrue
  -- ∑' (p : Bool × Heap), (G h₀)(some p) = 1
  -- Split into true + false parts
  rw [tsum_bool_prod_eq] at htotal
  -- htotal : (∑' h, (G h₀)(some (true, h))) + (∑' h, (G h₀)(some (false, h))) = 1
  rw [hfalse_sum, add_zero] at htotal
  exact htotal

/-- If pHoare says all Boolean outcomes are `false`, then `Pr[true] = 0`.

Every term `G h₀ (some (true, h))` in the sum defining `prTrue` must be 0:
if it were nonzero, pHoare would give `true = false`, a contradiction. -/
theorem prTrue_eq_zero_of_pHoare
    (G : SPComp Bool) (h₀ : Heap)
    (hph : pHoare (fun h => h = h₀) G (fun b _ => b = false)) :
    prTrue G h₀ = 0 := by
  unfold prTrue
  apply ENNReal.tsum_eq_zero.mpr
  intro h
  by_contra hne
  have := hph h₀ rfl true h hne
  exact absurd this (by simp)

/-- Variant of `advantage_zero_of_same_result` for the false case, which
does not require losslessness. -/
theorem advantage_zero_of_both_false
    (G₀ G₁ : SPComp Bool)
    (h₀ : pHoare (fun h => h = Heap.empty) G₀ (fun b _ => b = false))
    (h₁ : pHoare (fun h => h = Heap.empty) G₁ (fun b _ => b = false)) :
    Advantage G₀ G₁ = 0 := by
  have hpr₀ := prTrue_eq_zero_of_pHoare G₀ Heap.empty h₀
  have hpr₁ := prTrue_eq_zero_of_pHoare G₁ Heap.empty h₁
  simp only [Advantage, hpr₀, hpr₁, tsub_self, max_self]

/-- Advantage is 0 when both games deterministically return the same Boolean result.

If both G₀ and G₁ always return `b` (from the empty heap), their `prTrue` values
are equal (both 1 if `b = true`, both 0 if `b = false`), so the advantage is 0. -/
theorem advantage_zero_of_same_result
    (G₀ G₁ : SPComp Bool) (b : Bool)
    (h₀ : pHoare (fun h => h = Heap.empty) G₀ (fun b' _ => b' = b))
    (h₁ : pHoare (fun h => h = Heap.empty) G₁ (fun b' _ => b' = b))
    (hll₀ : isLosslessIf (fun h => h = Heap.empty) G₀)
    (hll₁ : isLosslessIf (fun h => h = Heap.empty) G₁) :
    Advantage G₀ G₁ = 0 := by
  cases b with
  | false => exact advantage_zero_of_both_false G₀ G₁ h₀ h₁
  | true =>
    have hpr₀ := prTrue_eq_one_of_pHoare G₀ Heap.empty h₀ hll₀
    have hpr₁ := prTrue_eq_one_of_pHoare G₁ Heap.empty h₁ hll₁
    simp only [Advantage, hpr₀, hpr₁, tsub_self, max_self]

/-! ## prTrue and prEvent connection -/

/-- `prTrue` is a special case of `prEventComp` for the event `b = true`. -/
theorem prTrue_eq_prEventComp (G : SPComp Bool) (h₀ : Heap) :
    prTrue G h₀ = prEventComp G h₀ (fun b _ => b = true) := by
  unfold prTrue prEventComp prEvent
  -- Split the RHS sum over Bool × Heap into true + false parts
  rw [tsum_bool_prod_eq]
  -- true part: ∑' h, if true = true then ... else 0 = ∑' h, G h₀ (some (true, h))
  -- false part: ∑' h, if false = true then ... else 0 = 0
  simp only [decide_true, ite_true, Bool.false_eq_true, ite_false]
  rw [ENNReal.tsum_eq_zero.mpr (fun _ => rfl), add_zero]

/-! ## Failure Event Lemma (FEL) -/

/-- The Failure Event Lemma (up-to-bad reasoning).

This is a fundamental technique from EasyCrypt and CertiCrypt used in
game-hopping proofs. Informally:

  `|Pr[G₀ : A] - Pr[G₁ : A]| ≤ Pr[G₀ : bad]`

when G₀ and G₁ agree on all outcomes where `bad` does not occur.

**Formal statement**: Given two games G₀ and G₁ and a "bad event" predicate
on the final heap:
- `h_agree`: For any non-bad initial heap, whenever G₀ assigns nonzero
  probability to an outcome, G₁ also does (the games have the same support
  on non-bad heaps).

Then the advantage is bounded by the probability that G₀ sets the bad flag.

**Use cases**:
- PKEY switching lemmas (bad = collision in random oracle)
- PRF/PRP switching (bad = duplicate query)
- Lazy/eager sampling equivalence (bad = premature evaluation)

**Proof sketch**:
1. Split prTrue into bad + nonbad parts for both G₀ and G₁
2. The nonbad parts are equal by `h_agree`
3. Show bad mass of G₁ ≤ bad mass of G₀ (using losslessness)
4. Derive two one-sided bounds: prTrue G₀ ≤ prTrue G₁ + Pr[bad] and vice versa
5. Combine via `tsub_le_iff_right` and `max_le` -/
theorem failure_event_lemma
    (G₀ G₁ : SPComp Bool) (h₀ : Heap)
    (bad : Heap → Prop)
    (h_agree : ∀ b h', ¬bad h' →
      (G₀ h₀) (some (b, h')) = (G₁ h₀) (some (b, h')))
    (hll₀ : isLosslessIf (fun h => h = h₀) G₀) :
    (prTrue G₀ h₀ - prTrue G₁ h₀) ⊔ (prTrue G₁ h₀ - prTrue G₀ h₀) ≤
      prEventComp G₀ h₀ (fun _ h' => bad h') := by
  -- Classical.propDecidable provides Decidable instances for `if bad h then ...`.
  -- All if-expressions and tsum_ite_add_compl share this instance → no diamond.
  -- Use (... : ℝ≥0∞) ascription to prevent Prop elaboration of if-expressions.
  letI : DecidablePred bad := Classical.decPred bad
  letI : DecidablePred (fun p : Bool × Heap => bad p.2) := fun p => inferInstance
  set Pb := prEventComp G₀ h₀ (fun _ h' => bad h')
  -- Helper: bad-true sum ≤ total bad sum (rw avoids higher-order unification)
  have bad_true_le (G : SPComp Bool) :
      (∑' h, (if bad h then (G h₀) (some (true, h)) else 0 : ℝ≥0∞)) ≤
      (∑' p : Bool × Heap, (if bad p.2 then (G h₀) (some p) else 0 : ℝ≥0∞)) := by
    rw [tsum_bool_prod_eq]; exact le_self_add
  -- Pb = explicit bad sum
  have hPb_explicit : Pb = ∑' p : Bool × Heap,
      (if bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞) := by
    simp only [Pb, prEventComp, prEvent]
  -- bad mass of G₁ ≤ bad mass of G₀ (from losslessness of G₀)
  have bad_G₁_le : (∑' p : Bool × Heap,
        (if bad p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)) ≤
      (∑' p : Bool × Heap,
        (if bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) := by
    -- nonbad parts are equal by h_agree
    have hnonbad_eq : (∑' p : Bool × Heap,
        (if ¬bad p.2 then (G₁ h₀) (some p) else 0 : ℝ≥0∞)) =
      (∑' p : Bool × Heap,
        (if ¬bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) :=
      tsum_congr (fun p => by
        by_cases hb : bad p.2
        · simp [hb]
        · simp [hb, h_agree p.1 p.2 hb])
    -- Split totals into bad + nonbad
    have hG₀_split := tsum_ite_add_compl
      (fun p : Bool × Heap => bad p.2) (fun p => (G₀ h₀) (some p))
    have hG₁_split := tsum_ite_add_compl
      (fun p : Bool × Heap => bad p.2) (fun p => (G₁ h₀) (some p))
    rw [tsum_some_of_mass_one (G₀ h₀) (hll₀ h₀ rfl)] at hG₀_split
    rw [hnonbad_eq] at hG₁_split
    have hG₁_total_le : ∑' p : Bool × Heap, (G₁ h₀) (some p) ≤ 1 :=
      (tsum_some_eq_mass (G₁ h₀)).symm ▸ (by unfold SDistr.mass; exact tsub_le_self)
    -- bad₁ + N ≤ bad₀ + N (chain: bad₁ + N = G₁_total ≤ 1 = bad₀ + N)
    have hle := (le_of_eq hG₁_split).trans (hG₁_total_le.trans (le_of_eq hG₀_split.symm))
    have hN_ne_top : (∑' p : Bool × Heap,
        (if ¬bad p.2 then (G₀ h₀) (some p) else 0 : ℝ≥0∞)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top
        (le_add_self.trans (le_of_eq hG₀_split))
    rwa [ENNReal.add_le_add_iff_right hN_ne_top] at hle
  -- One-sided bound 1: prTrue G₀ ≤ prTrue G₁ + Pb
  have h1 : prTrue G₀ h₀ ≤ prTrue G₁ h₀ + Pb := by
    unfold prTrue
    have step1 : ∀ h, (G₀ h₀) (some (true, h)) ≤
        (G₁ h₀) (some (true, h)) +
          (if bad h then (G₀ h₀) (some (true, h)) else 0 : ℝ≥0∞) := by
      intro h; by_cases hb : bad h
      · rw [if_pos hb]; exact le_add_self
      · rw [if_neg hb, add_zero]; exact le_of_eq (h_agree true h hb)
    calc ∑' h, (G₀ h₀) (some (true, h))
        ≤ ∑' h, ((G₁ h₀) (some (true, h)) +
          (if bad h then (G₀ h₀) (some (true, h)) else 0 : ℝ≥0∞)) :=
          ENNReal.tsum_le_tsum step1
      _ = _ + _ := ENNReal.tsum_add
      _ ≤ (∑' h, (G₁ h₀) (some (true, h))) + Pb :=
          add_le_add le_rfl ((bad_true_le G₀).trans (le_of_eq hPb_explicit.symm))
  -- One-sided bound 2: prTrue G₁ ≤ prTrue G₀ + Pb
  have h2 : prTrue G₁ h₀ ≤ prTrue G₀ h₀ + Pb := by
    unfold prTrue
    have step1 : ∀ h, (G₁ h₀) (some (true, h)) ≤
        (G₀ h₀) (some (true, h)) +
          (if bad h then (G₁ h₀) (some (true, h)) else 0 : ℝ≥0∞) := by
      intro h; by_cases hb : bad h
      · rw [if_pos hb]; exact le_add_self
      · rw [if_neg hb, add_zero]; exact le_of_eq (h_agree true h hb).symm
    calc ∑' h, (G₁ h₀) (some (true, h))
        ≤ ∑' h, ((G₀ h₀) (some (true, h)) +
          (if bad h then (G₁ h₀) (some (true, h)) else 0 : ℝ≥0∞)) :=
          ENNReal.tsum_le_tsum step1
      _ = _ + _ := ENNReal.tsum_add
      _ ≤ (∑' h, (G₀ h₀) (some (true, h))) + Pb :=
          add_le_add le_rfl ((bad_true_le G₁).trans (bad_G₁_le.trans (le_of_eq hPb_explicit.symm)))
  -- Combine: tsub_le_iff_right needs a ≤ c + b, we have a ≤ b + c
  exact max_le (tsub_le_iff_right.mpr (by rwa [add_comm])) (tsub_le_iff_right.mpr (by rwa [add_comm]))

/-- Corollary: If the bad event never happens, the games are perfectly indistinguishable. -/
theorem perfect_indist_of_no_bad
    (G₀ G₁ : SPComp Bool) (h₀ : Heap)
    (h_agree : ∀ b h', (G₀ h₀) (some (b, h')) = (G₁ h₀) (some (b, h'))) :
    prTrue G₀ h₀ = prTrue G₁ h₀ := by
  unfold prTrue
  congr 1
  funext h
  exact h_agree true h

/-! ## Connecting pHL postconditions to advantage bounds -/

/-- If two games satisfy the same pHL postcondition that determines the Boolean
result, and both are lossless, then their advantage is 0.

This is a unary analogue of `advantage_zero_of_rHoare`: instead of showing
equality via a relational coupling, we show that both games produce
outcomes satisfying the same postcondition `Q`, which determines the Boolean. -/
theorem advantage_zero_of_pHoare_det
    (G₀ G₁ : SPComp Bool) (b : Bool)
    (hph₀ : pHoare (fun h => h = Heap.empty) G₀ (fun b' _ => b' = b))
    (hph₁ : pHoare (fun h => h = Heap.empty) G₁ (fun b' _ => b' = b))
    (hll₀ : isLosslessIf (fun h => h = Heap.empty) G₀)
    (hll₁ : isLosslessIf (fun h => h = Heap.empty) G₁) :
    Advantage G₀ G₁ = 0 := by
  cases b with
  | false =>
    -- Both always return false, so prTrue = 0 for both
    exact advantage_zero_of_both_false G₀ G₁ hph₀ hph₁
  | true =>
    -- Both always return true and are lossless, so prTrue = 1 for both
    have hpr₀ := prTrue_eq_one_of_pHoare G₀ Heap.empty hph₀ hll₀
    have hpr₁ := prTrue_eq_one_of_pHoare G₁ Heap.empty hph₁ hll₁
    simp only [Advantage, hpr₀, hpr₁, tsub_self, max_self]

end CatCrypt.Unary

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Classes
public import CatCryptCore.Relational.Approx
public import CatCryptCore.Relational.ApproxPointMass
public import CatCryptCore.ForMathlib.Order.LeanOrderENNReal
public import CatCryptCore.Unary.ExpectationVCGenCore
public import CatCryptCore.Refinement.WRPUpTo

/-!
# Probabilistic refinement through couplings

A coupling of a concrete and an abstract probabilistic computation gives a refinement in the
expectation logic of `SPComp` (`instWPMonadSPComp`): the concretized abstract expectation is a
lower bound of the concrete expectation of the concretized postcondition. The concrete program is
the left program of the judgement and the abstract program the right one.

The assertion carrier is `Heap → ℝ≥0∞`, whose truth value is `⊤`. The refinement weakest
precondition `wrp` quantifies over all postconditions with values in this carrier, so an exact
coupling is stated as `RefinementWP.Refines` at the return relation `retRel R`, with values `0`
and `⊤`. An approximate coupling of grade `ε` bounds a difference of expectations by `ε` only for
integrands bounded by `1`, since the error is a mass and is weighted by the integrand. It is
therefore stated as a separate judgement `RefinesUpTo ε`, the lax square with additive slack `ε`
over postconditions and exception postconditions bounded by `1`. The judgement keeps the carrier
and the `WP` instance of `SPComp`, so facts of the expectation logic apply to it without
transport. On bounded postconditions the return relation is equivalently read with values `0`
and `1` (`indRel R`, `refinesUpTo_indRel_iff`), and at `ε = 0`, the concretization of a heap
relation and the precondition `⊤` the judgement is equivalent to `Refines`
(`refinesUpTo_zero_iff_refines`).

## Main definitions

* `heapConc SR`: the concretization of a heap relation on expectations.
* `retRel R`, `indRel R`: a return relation as an assertion with values `0`, `⊤`, respectively
  as an indicator with values `0`, `1`.
* `couplingPost SR R`: the relational postcondition of a heap relation and a return relation.
* `RefinesUpTo ε P γ eps c a Q`: refinement of `a` by `c` up to `ε` over bounded postconditions.

## Main results

* `wpEF_le_add_of_rHoareApprox`: the expectation bound of an approximate coupling.
* `refines_of_rHoareApprox_zero`, `refines_of_rHoare`: an exact coupling gives `Refines`.
* `refinesUpTo_of_rHoareApprox`: a coupling of grade `ε` gives refinement up to `ε`.
* `refinesUpTo_iff`: the judgement as an application of `WRPUpTo.RefinesUpTo`, unfolded.
* `refinesUpTo_zero_iff`: at `ε = 0`, the transport property of `wrp` over bounded
  postconditions.
* `RefinesUpTo.mono`, `RefinesUpTo.mono_err`: monotonicity in the error and the precondition.
* `refinesUpTo_zero_iff_refines`: at the concretization of a heap relation, `RefinesUpTo 0`
  is equivalent to `Refines`.
* `RefinesUpTo.vcomp_top`, `RefinesUpTo.vcomp_heapConc`, `RefinesUpTo.bind`: vertical and
  sequential composition with the errors added.

## Search words

approximate coupling, expectation, refinement up to error, weakest preexpectation, wrp,
probabilistic data refinement, total variation slack
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Refinement.WRP

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary RefinementWP
open Std.WP (wp)
open scoped ENNReal

variable {α β γ δ : Type}

/-! ## The expectation bound of a coupling -/

section Expectation

variable {X Y : Type} {d₁ : SDistr X} {d₂ : SDistr Y} {ε : ℝ≥0∞} {R : X → Y → Prop}
  {v₁ : X → ℝ≥0∞} {v₂ : Y → ℝ≥0∞}

/-- Across a sub-coupling, the right expectation is at most the left one plus the right
    deficit weighted by the right integrand. -/
theorem tsum_mul_le_add_deficit (c : SubCoupling d₁ d₂ ε) (hc : c.satisfies R)
    (hv : ∀ x y, R x y → v₂ y ≤ v₁ x) :
    ∑' y, d₂ (some y) * v₂ y ≤ (∑' x, d₁ (some x) * v₁ x) +
      ∑' y, (d₂ (some y) - ∑' x, c.joint (some (x, y))) * v₂ y :=
  calc ∑' y, d₂ (some y) * v₂ y
      = (∑' y, (∑' x, c.joint (some (x, y))) * v₂ y) +
          ∑' y, (d₂ (some y) - ∑' x, c.joint (some (x, y))) * v₂ y := by
        rw [← tsum_add]
        exact tsum_congr fun y => by rw [← add_mul, add_tsub_cancel_of_le (c.right_le y)]
    _ ≤ _ := by
        gcongr ?_ + _
        simp only [← ENNReal.tsum_mul_right]
        rw [tsum_comm]
        refine tsum_le_tsum fun x => ?_
        calc ∑' y, c.joint (some (x, y)) * v₂ y
            ≤ ∑' y, c.joint (some (x, y)) * v₁ x := tsum_le_tsum fun y => by
              by_cases h0 : c.joint (some (x, y)) = 0
              · simp [h0]
              · exact mul_le_mul_right (hv x y (hc x y h0)) _
          _ = (∑' y, c.joint (some (x, y))) * v₁ x := ENNReal.tsum_mul_right
          _ ≤ d₁ (some x) * v₁ x := mul_le_mul_left (c.left_le x) _

/-- On both sides of a sub-coupling, the failure mass plus the deficit is the mass outside
    the joint distribution. -/
theorem none_add_deficit_eq (c : SubCoupling d₁ d₂ ε) :
    d₁ none + ∑' x, (d₁ (some x) - ∑' y, c.joint (some (x, y))) =
      d₂ none + ∑' y, (d₂ (some y) - ∑' x, c.joint (some (x, y))) := by
  have split : ∀ {Z : Type} (d : SDistr Z) (m : Z → ℝ≥0∞), (∀ z, m z ≤ d (some z)) →
      d none + ∑' z, (d (some z) - m z) + ∑' z, m z = 1 := by
    intro Z d m hm
    rw [add_assoc, ← tsum_add]
    simp only [tsub_add_cancel_of_le (hm _)]
    rw [← SDistr.tsum_option_eq_add]
    exact d.tsum_coe
  have h₁ := split d₁ _ c.left_le
  have h₂ := split d₂ _ c.right_le
  rw [tsum_comm] at h₂
  have hW : ∑' x, ∑' y, c.joint (some (x, y)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (h₁ ▸ le_add_self)
  exact (ENNReal.add_left_inj hW).1 (h₁.trans h₂.symm)

/-- **Expectations across an approximate coupling.** For integrands bounded by `1` and a failure
    weight bounded by `1`, the failure-weighted expectation on the right is at most the one on
    the left plus the grade. -/
theorem expect_le_add_of_liftRApprox (h : liftRApprox ε R d₁ d₂)
    (hv : ∀ x y, R x y → v₂ y ≤ v₁ x) (hv₂ : ∀ y, v₂ y ≤ 1) {e : ℝ≥0∞} (he : e ≤ 1) :
    (∑' y, d₂ (some y) * v₂ y) + e * d₂ none ≤
      (∑' x, d₁ (some x) * v₁ x) + e * d₁ none + ε := by
  obtain ⟨c, hc⟩ := h
  set δ₁ := ∑' x, (d₁ (some x) - ∑' y, c.joint (some (x, y)))
  set δ₂ := ∑' y, (d₂ (some y) - ∑' x, c.joint (some (x, y)))
  have hexp : ∑' y, d₂ (some y) * v₂ y ≤ (∑' x, d₁ (some x) * v₁ x) + δ₂ :=
    (tsum_mul_le_add_deficit c hc hv).trans
      (add_le_add le_rfl (tsum_le_tsum fun y => mul_le_of_le_one_right' (hv₂ y)))
  have hfail : δ₂ + e * d₂ none ≤ e * d₁ none + ε :=
    calc δ₂ + e * d₂ none
        = (1 - e) * δ₂ + e * (d₂ none + δ₂) := by
          conv_lhs => rw [← one_mul δ₂, ← tsub_add_cancel_of_le he]
          ring
      _ = (1 - e) * δ₂ + e * (d₁ none + δ₁) := by rw [none_add_deficit_eq c]
      _ ≤ (1 - e) * ε + e * (d₁ none + ε) := by
          gcongr
          · exact c.right_deficit
          · exact c.left_deficit
      _ = e * d₁ none + ((1 - e) + e) * ε := by ring
      _ = e * d₁ none + ε := by rw [tsub_add_cancel_of_le he, one_mul]
  grw [hexp, add_assoc, hfail, add_assoc]

/-- **Expectations across an exact coupling**, for arbitrary integrands and failure weight. -/
theorem expect_le_of_liftRApprox_zero (h : liftRApprox 0 R d₁ d₂)
    (hv : ∀ x y, R x y → v₂ y ≤ v₁ x) (e : ℝ≥0∞) :
    (∑' y, d₂ (some y) * v₂ y) + e * d₂ none ≤
      (∑' x, d₁ (some x) * v₁ x) + e * d₁ none := by
  obtain ⟨c, hc⟩ := h
  have h₂ : ∀ y, d₂ (some y) - ∑' x, c.joint (some (x, y)) = 0 :=
    tsum_eq_zero_iff.1 (le_antisymm c.right_deficit zero_le)
  have hnone := none_add_deficit_eq c
  rw [le_antisymm c.left_deficit zero_le, le_antisymm c.right_deficit zero_le, add_zero,
    add_zero] at hnone
  have hexp := tsum_mul_le_add_deficit c hc hv
  simp only [h₂, zero_mul, tsum_zero, add_zero] at hexp
  rw [hnone]
  gcongr

end Expectation

section Judgement

variable {Φ : RPre} {Ψ : RPost α β} {c : SPComp α} {a : SPComp β} {ε : ℝ≥0∞}
  {qc : α → Heap → ℝ≥0∞} {qa : β → Heap → ℝ≥0∞}

/-- **The expectation bound of an approximate coupling.** -/
theorem wpEF_le_add_of_rHoareApprox (h : rHoareApprox ε Φ c a Ψ)
    (hq : ∀ x s y s', Ψ x s y s' → qa y s' ≤ qc x s) (hqa : ∀ y s', qa y s' ≤ 1)
    {e : ℝ≥0∞} (he : e ≤ 1) {s s' : Heap} (hs : Φ s s') :
    wpEF a qa e s' ≤ wpEF c qc e s + ε := by
  simp only [wpEF, wpE_eq_tsum]
  exact expect_le_add_of_liftRApprox (h s s' hs) (fun _ _ => hq _ _ _ _) (fun _ => hqa _ _) he

/-- The expectation bound of an exact coupling. -/
theorem wpEF_le_of_rHoareApprox_zero (h : rHoareApprox 0 Φ c a Ψ)
    (hq : ∀ x s y s', Ψ x s y s' → qa y s' ≤ qc x s)
    (e : ℝ≥0∞) {s s' : Heap} (hs : Φ s s') :
    wpEF a qa e s' ≤ wpEF c qc e s := by
  simp only [wpEF, wpE_eq_tsum]
  exact expect_le_of_liftRApprox_zero (h s s' hs) (fun _ _ => hq _ _ _ _) e

end Judgement

/-- The failure-weighted expectation as a sum over all outcomes, failure included. -/
theorem wpEF_eq_tsum_option (c : SPComp α) (q : α → Heap → ℝ≥0∞) (e : ℝ≥0∞) (h : Heap) :
    wpEF c q e h =
      ∑' o : Option (α × Heap), (c h) o * o.elim e (fun p => q p.1 p.2) := by
  rw [SDistr.tsum_option_eq_add, wpEF, wpE_eq_tsum, add_comm, mul_comm e]
  rfl

/-- The failure-weighted expectation of an integrand bounded by `1`, at a failure weight
    bounded by `1`, is bounded by `1`. -/
theorem wpEF_le_one (c : SPComp α) {q : α → Heap → ℝ≥0∞} {e : ℝ≥0∞}
    (hq : ∀ x h, q x h ≤ 1) (he : e ≤ 1) (h : Heap) : wpEF c q e h ≤ 1 := by
  rw [wpEF_eq_tsum_option]
  refine le_trans (tsum_le_tsum fun o => mul_le_of_le_one_right' ?_) (c h).tsum_coe.le
  cases o <;> grind

/-- A constant added to the integrand adds at most that constant to the expectation. -/
theorem wpEF_add_const_le (c : SPComp α) (q : α → Heap → ℝ≥0∞) (k e : ℝ≥0∞) (h : Heap) :
    wpEF c (fun x h' => q x h' + k) e h ≤ wpEF c q e h + k := by
  have hk : wpE c (fun _ _ => k) h ≤ k := by
    rw [wpE_eq_tsum, ENNReal.tsum_mul_right]
    refine mul_le_of_le_one_left' ?_
    rw [← (c h).tsum_coe, SDistr.tsum_option_eq_add]
    exact le_add_self
  rw [wpEF, wpEF, wpE_add, add_right_comm]
  gcongr

/-! ## Concretization and return relations -/

/-- The concretization of a heap relation `SR` (concrete heap first): the supremum of the
    abstract expectation over the related abstract heaps. -/
noncomputable def heapConc (SR : RPre) : Concretization (Heap → ℝ≥0∞) (Heap → ℝ≥0∞) where
  pred p h := ⨆ (h') (_ : SR h h'), p h'
  pred_mono hpq _ := iSup₂_mono fun h' _ => hpq h'

/-- The return relation `R` as an assertion of the expectation logic, with values `0` and the
    truth value `⊤`. -/
noncomputable def retRel (R : α → β → Prop) : α → β → Heap → ℝ≥0∞ :=
  fun x y _ => Lean.Order.CompleteLattice.ofProp (R x y)

open Classical in
/-- The return relation `R` as an indicator with values `0` and `1`. -/
noncomputable def indRel (R : α → β → Prop) : α → β → Heap → ℝ≥0∞ :=
  fun x y _ => if R x y then 1 else 0

/-- The relational postcondition of a heap relation and a return relation. -/
def couplingPost (SR : RPre) (R : α → β → Prop) : RPost α β :=
  fun x h y h' => R x y ∧ SR h h'

variable {SR : RPre} {R : α → β → Prop}

/-- The concrete postcondition over expectations, pointwise. -/
theorem post_expectation_apply (γc : Concretization (Heap → ℝ≥0∞) (Heap → ℝ≥0∞))
    (Q : α → β → Heap → ℝ≥0∞) (Qa : β → Heap → ℝ≥0∞) (x : α) (h : Heap) :
    γc.post Q Qa x h = ⨆ y, min (Q x y h) (γc.pred (Qa y) h) := by
  simp only [Concretization.post, Lean.Order.iSup_apply, Lean.Order.meet_apply,
    ENNReal.leanOrder_iSup_eq_iSup, ENNReal.leanOrder_meet_eq_min]

/-- A related abstract outcome bounds the concrete postcondition at `retRel` from below. -/
theorem le_post_retRel {x : α} {y : β} {h h' : Heap} (hr : couplingPost SR R x h y h')
    (Qa : β → Heap → ℝ≥0∞) : Qa y h' ≤ (heapConc SR).post (retRel R) Qa x h := by
  rw [post_expectation_apply]
  exact le_iSup_of_le y (le_min (Lean.Order.CompleteLattice.le_ofProp (Qa y h') (R x y) hr.1)
    (le_iSup₂_of_le h' hr.2 le_rfl))

/-- A related abstract outcome of value at most `1` bounds the concrete postcondition at
    `indRel` from below. -/
theorem le_post_indRel {x : α} {y : β} {h h' : Heap} (hr : couplingPost SR R x h y h')
    {Qa : β → Heap → ℝ≥0∞} (hQa : ∀ b s, Qa b s ≤ 1) :
    Qa y h' ≤ (heapConc SR).post (indRel R) Qa x h := by
  rw [post_expectation_apply]
  refine le_iSup_of_le y (le_min ?_ (le_iSup₂_of_le h' hr.2 le_rfl))
  grind [indRel, couplingPost]

/-- `heapConc` preserves the bound `1`. -/
theorem heapConc_le_one {p : Heap → ℝ≥0∞} (hp : ∀ h, p h ≤ 1) (h : Heap) :
    (heapConc SR).pred p h ≤ 1 :=
  iSup₂_le fun h' _ => hp h'

/-- `heapConc` moves an added constant outside. -/
theorem heapConc_add_const_le (p : Heap → ℝ≥0∞) (k : ℝ≥0∞) (h : Heap) :
    (heapConc SR).pred (fun h' => p h' + k) h ≤ (heapConc SR).pred p h + k :=
  iSup₂_le fun h' hs => add_le_add (le_iSup₂_of_le h' hs le_rfl) le_rfl

/-- `heapConc` preserves suprema. -/
instance instIsSupPreservingHeapConc (SR : RPre) : (heapConc SR).IsSupPreserving.{_, 0} where
  sup {ι} f h := by
    refine iSup₂_le fun h' hs => ?_
    simp only [Lean.Order.iSup_apply, ENNReal.leanOrder_iSup_eq_iSup]
    exact iSup_mono fun i => le_iSup₂_of_le h' hs le_rfl

/-- On postconditions bounded by `1`, the two readings of a return relation give the same
    concrete postcondition. -/
theorem post_indRel_eq_post_retRel {Qa : β → Heap → ℝ≥0∞} (hQa : ∀ y h, Qa y h ≤ 1) :
    (heapConc SR).post (indRel R) Qa = (heapConc SR).post (retRel R) Qa := by
  funext x h
  simp only [post_expectation_apply]
  refine iSup_congr fun y => ?_
  have h1 := heapConc_le_one (SR := SR) (hQa y) h
  by_cases hR : R x y
  · simp [indRel, retRel, hR, ENNReal.leanOrder_top_eq_top, h1]
  · simp [indRel, retRel, hR, ENNReal.leanOrder_bot_eq_zero]

/-! ## The exact case -/

/-- **A coupling of grade `0` gives refinement** of the abstract by the concrete program, at the
    concretization of the heap relation, the identity exception map and the return relation. -/
theorem refines_of_rHoareApprox_zero {c : SPComp α} {a : SPComp β}
    (h : rHoareApprox 0 SR c a (couplingPost SR R)) :
    Refines Lean.Order.top (heapConc SR) (fun e : ℝ≥0∞ => e) c a (retRel R) :=
  refines_top_iff.2 fun Qa e _ => iSup₂_le fun _ hs =>
    wpEF_le_of_rHoareApprox_zero h (fun _ _ _ _ hr => le_post_retRel hr Qa) e hs

/-- An exact coupling gives refinement. -/
theorem refines_of_rHoare {c : SPComp α} {a : SPComp β}
    (h : rHoare SR c a (couplingPost SR R)) :
    Refines Lean.Order.top (heapConc SR) (fun e : ℝ≥0∞ => e) c a (retRel R) :=
  refines_of_rHoareApprox_zero (rHoareApprox_of_rHoare h)

/-! ## Refinement up to an error -/

/-- Refinement of `a` by `c` up to `ε` under the precondition `P`: for every abstract
    postcondition and exception postcondition bounded by `1`, `P` met with the concretized
    abstract expectation is at most the concrete expectation plus `ε`. The bound on the
    postconditions is part of the judgement because the slack of an approximate coupling is a
    mass, which an integrand multiplies. It is the generic judgement `WRPUpTo.RefinesUpTo` at
    the admissible classes of postconditions and exception postconditions bounded by `1`. -/
def RefinesUpTo (ε : ℝ≥0∞) (P : Heap → ℝ≥0∞)
    (γc : Concretization (Heap → ℝ≥0∞) (Heap → ℝ≥0∞)) (eps : ℝ≥0∞ → ℝ≥0∞)
    (c : SPComp α) (a : SPComp β) (Q : α → β → Heap → ℝ≥0∞) : Prop :=
  WRPUpTo.RefinesUpTo (fun Qa : β → Heap → ℝ≥0∞ => ∀ y h, Qa y h ≤ 1) (fun Ea : ℝ≥0∞ => Ea ≤ 1)
    ε P γc eps c a Q

section UpTo

variable {γc : Concretization (Heap → ℝ≥0∞) (Heap → ℝ≥0∞)} {eps : ℝ≥0∞ → ℝ≥0∞}
  {P : Heap → ℝ≥0∞} {Q : α → β → Heap → ℝ≥0∞} {c : SPComp α} {a : SPComp β} {ε : ℝ≥0∞}

/-- The unfolding lemma of `RefinesUpTo`: for every postcondition and exception postcondition
    bounded by `1`, at every heap, `P` met with the concretized abstract expectation is at most
    the concrete expectation plus `ε`. -/
theorem refinesUpTo_iff :
    RefinesUpTo ε P γc eps c a Q ↔
      ∀ (Qa : β → Heap → ℝ≥0∞) (Ea : ℝ≥0∞), (∀ y h, Qa y h ≤ 1) → Ea ≤ 1 →
        ∀ h, Lean.Order.meet P (γc.pred (wp a Qa Ea)) h ≤ wp c (γc.post Q Qa) (eps Ea) h + ε :=
  Iff.rfl

/-- At `ε = 0`, refinement up to `ε` is the transport property of `wrp` restricted to bounded
    postconditions. -/
theorem refinesUpTo_zero_iff :
    RefinesUpTo 0 P γc eps c a Q ↔
      ∀ (Qa : β → Heap → ℝ≥0∞) (Ea : ℝ≥0∞), (∀ y h, Qa y h ≤ 1) → Ea ≤ 1 →
        Lean.Order.PartialOrder.rel (Lean.Order.meet P (γc.pred (wp a Qa Ea)))
          (wp c (γc.post Q Qa) (eps Ea)) :=
  WRPUpTo.refinesUpTo_zero_iff

/-- Refinement gives refinement up to every error. -/
theorem refinesUpTo_of_refines (h : Refines P γc eps c a Q) (ε : ℝ≥0∞) :
    RefinesUpTo ε P γc eps c a Q :=
  WRPUpTo.RefinesUpTo.of_refines h _ _ ε

/-- Refinement up to an error under `⊤` is the lax square with slack, over bounded
    postconditions. -/
theorem refinesUpTo_top_iff :
    RefinesUpTo ε Lean.Order.top γc eps c a Q ↔
      ∀ (Qa : β → Heap → ℝ≥0∞) (Ea : ℝ≥0∞), (∀ y h, Qa y h ≤ 1) → Ea ≤ 1 →
        ∀ h, γc.pred (wp a Qa Ea) h ≤ wp c (γc.post Q Qa) (eps Ea) h + ε :=
  WRPUpTo.refinesUpTo_top_iff

/-- Refinement up to an error is monotone in the error and antitone in the precondition. -/
theorem RefinesUpTo.mono {ε' : ℝ≥0∞} {P' : Heap → ℝ≥0∞} (h : RefinesUpTo ε P γc eps c a Q)
    (hP : ∀ s, P' s ≤ P s) (hε : ε ≤ ε') : RefinesUpTo ε' P' γc eps c a Q :=
  WRPUpTo.RefinesUpTo.mono h (fun _ => id) (fun _ => id) hP hε

/-- Refinement up to an error is monotone in the error. -/
theorem RefinesUpTo.mono_err {ε' : ℝ≥0∞} (h : RefinesUpTo ε P γc eps c a Q) (hε : ε ≤ ε') :
    RefinesUpTo ε' P γc eps c a Q :=
  WRPUpTo.RefinesUpTo.mono_err h hε

/-- Refinement up to an error does not distinguish the two readings of a return relation. -/
theorem refinesUpTo_indRel_iff :
    RefinesUpTo ε P (heapConc SR) eps c a (indRel R) ↔
      RefinesUpTo ε P (heapConc SR) eps c a (retRel R) := by
  constructor <;> intro h Qa Ea hQa hEa s <;>
    simpa only [post_indRel_eq_post_retRel hQa] using h Qa Ea hQa hEa s

/-- **A coupling of grade `ε` gives refinement up to `ε`**, under every precondition, with the
    return relation read as an indicator. -/
theorem refinesUpTo_of_rHoareApprox (h : rHoareApprox ε SR c a (couplingPost SR R))
    (P : Heap → ℝ≥0∞) :
    RefinesUpTo ε P (heapConc SR) (fun e => e) c a (indRel R) :=
  fun _ _ hQa hEa s => le_trans (Lean.Order.meet_le_right P _ s) <| iSup₂_le fun _ hs =>
    wpEF_le_add_of_rHoareApprox h (fun _ _ _ _ hr => le_post_indRel hr hQa) hQa hEa hs

/-- A coupling that is available when `R₀ x₀ y₀` holds gives refinement up to its grade under
    the precondition `indRel R₀ x₀ y₀`, the form of the continuations in `RefinesUpTo.bind`. -/
theorem refinesUpTo_indRel_of_rHoareApprox {R₀ : γ → δ → Prop} {x₀ : γ} {y₀ : δ}
    (h : R₀ x₀ y₀ → rHoareApprox ε SR c a (couplingPost SR R)) :
    RefinesUpTo ε (indRel R₀ x₀ y₀) (heapConc SR) (fun e => e) c a (indRel R) := by
  by_cases hR : R₀ x₀ y₀
  · exact refinesUpTo_of_rHoareApprox (h hR) _
  · intro Qa Ea _ _ s
    simp [Lean.Order.meet_apply, ENNReal.leanOrder_meet_eq_min, indRel, hR]

end UpTo

/-! ## Agreement with the exact refinement at error `0` -/

/-- A failure-weighted expectation is at most the supremum of its truncations at natural
    numbers. -/
theorem wpEF_le_iSup_truncate (c : SPComp α) (q : α → Heap → ℝ≥0∞) (e : ℝ≥0∞) (h : Heap) :
    wpEF c q e h ≤ ⨆ n : ℕ, wpEF c (fun x s => min (q x s) n) (min e n) h := by
  simp only [wpEF_eq_tsum_option]
  rw [tsum_eq_iSup_sum]
  refine iSup_le fun t => ?_
  calc ∑ o ∈ t, (c h) o * o.elim e (fun p => q p.1 p.2)
      = ∑ o ∈ t, ⨆ n : ℕ, (c h) o * min (o.elim e fun p => q p.1 p.2) n := by
        simp only [← ENNReal.mul_iSup, ← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    _ = ⨆ n : ℕ, ∑ o ∈ t, (c h) o * min (o.elim e fun p => q p.1 p.2) n :=
        ENNReal.finsetSum_iSup_of_monotone fun o m n hmn =>
          mul_le_mul_right (min_le_min le_rfl (Nat.cast_le.2 hmn)) _
    _ ≤ _ := iSup_mono fun n => le_trans (sum_le_tsum t)
        (tsum_le_tsum fun o => by cases o <;> rfl)

/-- A scalar factor of the integrand and of the failure weight moves outside. -/
theorem wpEF_const_mul (c : SPComp α) (k : ℝ≥0∞) (q : α → Heap → ℝ≥0∞) (e : ℝ≥0∞) (h : Heap) :
    wpEF c (fun x s => k * q x s) (k * e) h = k * wpEF c q e h := by
  simp only [wpEF, wpE_const_mul, mul_add, mul_assoc]

/-- **Agreement with the exact case.** At the concretization of a heap relation, refinement up
    to `0` over bounded postconditions is refinement over all postconditions: both sides are
    linear and continuous in the postcondition. -/
theorem refinesUpTo_zero_iff_refines {c : SPComp α} {a : SPComp β} :
    RefinesUpTo 0 Lean.Order.top (heapConc SR) (fun e => e) c a (indRel R) ↔
      Refines Lean.Order.top (heapConc SR) (fun e : ℝ≥0∞ => e) c a (retRel R) := by
  rw [refinesUpTo_indRel_iff]
  refine ⟨fun H => refines_top_iff.2 fun Qa e h => iSup₂_le fun h' hs => ?_,
    fun H => refinesUpTo_of_refines H 0⟩
  refine (wpEF_le_iSup_truncate a Qa e h').trans (iSup_le fun n => ?_)
  set k : ℝ≥0∞ := n + 1
  have hk : k * k⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp [k]) (by simp [k])
  have hle : ∀ x : ℝ≥0∞, min x n * k⁻¹ ≤ 1 := fun x =>
    hk ▸ mul_le_mul_left ((min_le_right x _).trans le_self_add) _
  have hcancel : ∀ x : ℝ≥0∞, k * (x * k⁻¹) = x := fun x => by rw [mul_left_comm, hk, mul_one]
  let q : β → Heap → ℝ≥0∞ := fun y s => min (Qa y s) n * k⁻¹
  have hq := refinesUpTo_top_iff.1 H q (min e n * k⁻¹) (fun _ _ => hle _) (hle _) h
  rw [add_zero] at hq
  have hpost : ∀ x s,
      k * (heapConc SR).post (retRel R) q x s ≤ (heapConc SR).post (retRel R) Qa x s := by
    intro x s
    simp only [post_expectation_apply, ENNReal.mul_iSup]
    refine iSup_le fun y => le_iSup_of_le y ?_
    by_cases hR : R x y
    · simp only [retRel, hR, Lean.Order.CompleteLattice.ofProp, ite_true,
        ENNReal.leanOrder_top_eq_top, min_top_left, heapConc, ENNReal.mul_iSup, q, hcancel]
      exact iSup₂_mono fun _ _ => min_le_left _ _
    · simp [retRel, hR, ENNReal.leanOrder_bot_eq_zero]
  calc wpEF a (fun y s => min (Qa y s) n) (min e n) h'
      = k * wpEF a q (min e n * k⁻¹) h' := by
        simp only [← wpEF_const_mul, q, hcancel]
    _ ≤ k * wpEF c ((heapConc SR).post (retRel R) q) (min e n * k⁻¹) h :=
        mul_le_mul_right ((le_iSup₂_of_le h' hs le_rfl).trans hq) _
    _ ≤ wpEF c ((heapConc SR).post (retRel R) Qa) e h := by
        rw [← wpEF_const_mul, hcancel]
        exact wpEF_mono c hpost (min_le_left _ _) h

/-! ## Composition -/

/-- **Vertical composition**: the errors add, when the outer concretization preserves suprema
    and moves an added constant outside and the inner concretization and exception map preserve
    the bound `1`. -/
theorem RefinesUpTo.vcomp_top {γ₂ γ₁ : Concretization (Heap → ℝ≥0∞) (Heap → ℝ≥0∞)}
    {eps₂ eps₁ : ℝ≥0∞ → ℝ≥0∞} {c : SPComp α} {b : SPComp β} {a : SPComp γ}
    {Q₂ : α → β → Heap → ℝ≥0∞} {Q₁ : β → γ → Heap → ℝ≥0∞} {ε₁ ε₂ : ℝ≥0∞}
    (hsup : γ₂.SupPreserving.{_, 0})
    (hadd : ∀ p k h, γ₂.pred (fun h' => p h' + k) h ≤ γ₂.pred p h + k)
    (hbound : ∀ p, (∀ h, p h ≤ 1) → ∀ h, γ₁.pred p h ≤ 1)
    (heps : ∀ e, e ≤ 1 → eps₁ e ≤ 1)
    (h₁ : RefinesUpTo ε₁ Lean.Order.top γ₁ eps₁ b a Q₁)
    (h₂ : RefinesUpTo ε₂ Lean.Order.top γ₂ eps₂ c b Q₂) :
    RefinesUpTo (ε₁ + ε₂) Lean.Order.top (γ₂.comp γ₁) (fun e => eps₂ (eps₁ e)) c a
      (γ₂.relComp Q₂ Q₁) := by
  have hQb : ∀ Qa : γ → Heap → ℝ≥0∞, (∀ z s, Qa z s ≤ 1) → ∀ y s, γ₁.post Q₁ Qa y s ≤ 1 :=
    fun Qa hQa y s => by
      rw [post_expectation_apply]
      exact iSup_le fun z => (min_le_right _ _).trans (hbound _ (hQa z) s)
  exact WRPUpTo.RefinesUpTo.vcomp_top hsup hadd hQb heps h₁ h₂

/-- Vertical composition at concretizations of heap relations and identity exception maps,
    where the side conditions of `RefinesUpTo.vcomp_top` hold. -/
theorem RefinesUpTo.vcomp_heapConc {SR₂ SR₁ : RPre} {c : SPComp α} {b : SPComp β}
    {a : SPComp γ} {Q₂ : α → β → Heap → ℝ≥0∞} {Q₁ : β → γ → Heap → ℝ≥0∞} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : RefinesUpTo ε₁ Lean.Order.top (heapConc SR₁) (fun e => e) b a Q₁)
    (h₂ : RefinesUpTo ε₂ Lean.Order.top (heapConc SR₂) (fun e => e) c b Q₂) :
    RefinesUpTo (ε₁ + ε₂) Lean.Order.top ((heapConc SR₂).comp (heapConc SR₁)) (fun e => e) c a
      ((heapConc SR₂).relComp Q₂ Q₁) :=
  RefinesUpTo.vcomp_top Concretization.IsSupPreserving.sup heapConc_add_const_le
    (fun _ => heapConc_le_one) (fun _ => id) h₁ h₂

/-- **Composition along bind**: the errors add, at every concretization and exception map. -/
theorem RefinesUpTo.bind {γc : Concretization (Heap → ℝ≥0∞) (Heap → ℝ≥0∞)}
    {eps : ℝ≥0∞ → ℝ≥0∞} {P : Heap → ℝ≥0∞} {c : SPComp α} {k : α → SPComp γ} {a : SPComp β}
    {g : β → SPComp δ} {Rc : α → β → Heap → ℝ≥0∞} {Q : γ → δ → Heap → ℝ≥0∞} {ε₁ ε₂ : ℝ≥0∞}
    (hc : RefinesUpTo ε₁ P γc eps c a Rc)
    (hk : ∀ x y, RefinesUpTo ε₂ (Rc x y) γc eps (k x) (g y) Q) :
    RefinesUpTo (ε₁ + ε₂) P γc eps (c.bind k) (a.bind g) Q :=
  WRPUpTo.RefinesUpTo.bind (c := c) (k := k) (a := a) (g := g)
    (fun Qa Ea _ _ s => (wpEF_bind a g Qa Ea s).le)
    (fun _ _ hQa hEa y s => wpEF_le_one (g y) hQa hEa s)
    (fun Y r E s => wpEF_add_const_le c Y r E s) hc hk

end CatCrypt.Refinement.WRP

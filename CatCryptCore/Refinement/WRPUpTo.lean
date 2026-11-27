/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.WRP
public import RefinementWP.Classes
public import CatCryptCore.ForMathlib.Order.LeanOrderENNReal
public import CatCryptCore.Refinement.WRPGradedLevel

/-!
# Refinement up to an error over expectation-valued assertions

The judgement `RefinesUpTo AdmQ AdmE ε P γ eps c a Q` is the transport property of the weakest
refinement precondition `wrp` with additive slack `ε`: for every abstract postcondition `Qa`
satisfying `AdmQ` and every abstract exception postcondition `Ea` satisfying `AdmE`, at every
concrete state `s`,
`meet P (γ.pred (wp a Qa Ea)) s ≤ wp c (γ.post Q Qa) (eps Ea) s + ε`.
The concrete assertions are functions `σ → ℝ≥0∞`, where an additive error is meaningful; the
abstract assertions are arbitrary. The admissibility predicates restrict the postconditions at
which the slack is charged, since the error of an approximate coupling or of a perturbed channel
is a mass that an unbounded integrand multiplies.

At `ε = 0` and the trivial admissibility predicates the judgement is `RefinementWP.Refines`.
Refinement up to an error is monotone in the error, the admissible classes and the
precondition; it is reflexive at the identity concretization; it composes vertically and along
`bind`, with the errors added. At the identity concretization the judgement is a graded level
(`gradedLevel`).

## Main definitions

* `RefinesUpTo AdmQ AdmE ε P γ eps c a Q`: refinement of `a` by `c` up to `ε` over admissible
  postconditions.
* `gradedLevel AdmQ AdmE P`: refinement up to an error at the identity concretization as a
  `GradedLevel` graded by `ℝ≥0∞`.

## Main results

* `RefinesUpTo.of_refines`, `RefinesUpTo.refl`: exact refinement and reflexivity.
* `RefinesUpTo.mono`, `RefinesUpTo.mono_err`: monotonicity.
* `refinesUpTo_zero_iff`, `refinesUpTo_zero_true_iff_refines`: the error `0`.
* `refinesUpTo_top_iff`: the precondition `⊤`.
* `RefinesUpTo.vcomp_top`, `RefinesUpTo.vcomp`, `RefinesUpTo.vcomp_id`: vertical composition.
* `RefinesUpTo.bind`: sequential composition.

## Search words

refinement up to an error, approximate refinement, weakest refinement precondition, wrp,
expectation, additive slack, graded level, vertical pasting, horizontal pasting, bind
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Refinement.WRPUpTo

open RefinementWP Std.WP
open scoped ENNReal

universe u v w'

/-- A minimum with a sum is at most the minimum plus the summand. -/
theorem min_add_le_min_add (x y z : ℝ≥0∞) : min x (y + z) ≤ min x y + z :=
  (min_le_min le_self_add le_rfl).trans (min_add_add_right x y z).le

/-- The meet of expectation-valued assertions is the pointwise minimum. -/
theorem meet_apply_eq_min {σ : Type} (P X : σ → ℝ≥0∞) (s : σ) :
    Lean.Order.meet P X s = min (P s) (X s) := by
  simp only [Lean.Order.meet_apply, ENNReal.leanOrder_meet_eq_min]

section Judgement

variable {σ : Type} {CProg AProg : Type u} {CVal AVal : Type v} {APred : Type}
  {CE AE : Type w'} [Assertion APred] [Assertion CE] [Assertion AE]
  [WP CProg CVal (σ → ℝ≥0∞) CE] [WP AProg AVal APred AE]

/-- Refinement of `a` by `c` up to `ε` under the precondition `P`: for every abstract
postcondition satisfying `AdmQ` and exception postcondition satisfying `AdmE`, at every state,
`P` met with the concretized abstract precondition is at most the concrete precondition plus
`ε`. -/
def RefinesUpTo (AdmQ : (AVal → APred) → Prop) (AdmE : AE → Prop) (ε : ℝ≥0∞)
    (P : σ → ℝ≥0∞) (γ : Concretization (σ → ℝ≥0∞) APred) (eps : AE → CE) (c : CProg)
    (a : AProg) (Q : CVal → AVal → σ → ℝ≥0∞) : Prop :=
  ∀ (Qa : AVal → APred) (Ea : AE), AdmQ Qa → AdmE Ea →
    ∀ s, Lean.Order.meet P (γ.pred (wp a Qa Ea)) s ≤ wp c (γ.post Q Qa) (eps Ea) s + ε

variable {AdmQ : (AVal → APred) → Prop} {AdmE : AE → Prop} {ε : ℝ≥0∞} {P : σ → ℝ≥0∞}
  {γ : Concretization (σ → ℝ≥0∞) APred} {eps : AE → CE} {c : CProg} {a : AProg}
  {Q : CVal → AVal → σ → ℝ≥0∞}

/-- Refinement up to an error is monotone in the error, antitone in the admissible classes and
antitone in the precondition. -/
theorem RefinesUpTo.mono {AdmQ' : (AVal → APred) → Prop} {AdmE' : AE → Prop} {ε' : ℝ≥0∞}
    {P' : σ → ℝ≥0∞} (h : RefinesUpTo AdmQ AdmE ε P γ eps c a Q)
    (hQ : ∀ Qa, AdmQ' Qa → AdmQ Qa) (hE : ∀ Ea, AdmE' Ea → AdmE Ea) (hP : ∀ s, P' s ≤ P s)
    (hε : ε ≤ ε') : RefinesUpTo AdmQ' AdmE' ε' P' γ eps c a Q := by
  intro Qa Ea hQa hEa s
  have k := h Qa Ea (hQ Qa hQa) (hE Ea hEa) s
  rw [meet_apply_eq_min] at k ⊢
  exact ((min_le_min (hP s) le_rfl).trans k).trans (add_le_add le_rfl hε)

/-- Refinement up to an error is monotone in the error. -/
theorem RefinesUpTo.mono_err {ε' : ℝ≥0∞} (h : RefinesUpTo AdmQ AdmE ε P γ eps c a Q)
    (hε : ε ≤ ε') : RefinesUpTo AdmQ AdmE ε' P γ eps c a Q :=
  h.mono (fun _ => id) (fun _ => id) (fun _ => le_rfl) hε

/-- Exact refinement gives refinement up to every error, at all admissible classes. -/
theorem RefinesUpTo.of_refines (h : Refines P γ eps c a Q) (AdmQ : (AVal → APred) → Prop)
    (AdmE : AE → Prop) (ε : ℝ≥0∞) : RefinesUpTo AdmQ AdmE ε P γ eps c a Q :=
  fun Qa Ea _ _ s => le_trans (wrp_transport h Qa Ea s) le_self_add

/-- At `ε = 0`, refinement up to `ε` is the transport property of `wrp` restricted to the
admissible postconditions. -/
theorem refinesUpTo_zero_iff :
    RefinesUpTo AdmQ AdmE 0 P γ eps c a Q ↔
      ∀ (Qa : AVal → APred) (Ea : AE), AdmQ Qa → AdmE Ea →
        Lean.Order.PartialOrder.rel (Lean.Order.meet P (γ.pred (wp a Qa Ea)))
          (wp c (γ.post Q Qa) (eps Ea)) := by
  simp only [RefinesUpTo, add_zero]
  rfl

/-- At `ε = 0` and the trivial admissibility predicates, refinement up to `ε` is
`RefinementWP.Refines`. -/
theorem refinesUpTo_zero_true_iff_refines :
    RefinesUpTo (fun _ => True) (fun _ => True) 0 P γ eps c a Q ↔ Refines P γ eps c a Q :=
  ⟨fun h => wrp_intro fun Qa Ea => refinesUpTo_zero_iff.1 h Qa Ea trivial trivial,
    fun h => RefinesUpTo.of_refines h _ _ 0⟩

/-- Refinement up to an error under `⊤` is the lax square with slack over the admissible
postconditions. -/
theorem refinesUpTo_top_iff :
    RefinesUpTo AdmQ AdmE ε Lean.Order.top γ eps c a Q ↔
      ∀ (Qa : AVal → APred) (Ea : AE), AdmQ Qa → AdmE Ea →
        ∀ s, γ.pred (wp a Qa Ea) s ≤ wp c (γ.post Q Qa) (eps Ea) s + ε := by
  simp only [RefinesUpTo, meet_apply_eq_min, Lean.Order.top_apply,
    ENNReal.leanOrder_top_eq_top, min_top_left]

end Judgement

section Refl

variable {σ : Type} {CProg : Type u} {CVal : Type v} {CE : Type w'} [Assertion CE]
  [WP CProg CVal (σ → ℝ≥0∞) CE]

/-- Reflexivity: every program refines itself up to every error, at the identity
concretization, the identity exception map and the equality return relation, under every
precondition and at all admissible classes. -/
theorem RefinesUpTo.refl (AdmQ : (CVal → σ → ℝ≥0∞) → Prop) (AdmE : CE → Prop) (ε : ℝ≥0∞)
    (P : σ → ℝ≥0∞) (c : CProg) :
    RefinesUpTo AdmQ AdmE ε P Concretization.id (fun e : CE => e) c c
      (eqRel (CPred := σ → ℝ≥0∞)) :=
  RefinesUpTo.of_refines (Refines.refl P c) AdmQ AdmE ε

/-- Vertical composition at the identity concretization: the errors add, at a common
precondition and common admissible classes. -/
theorem RefinesUpTo.vcomp_id {AdmQ : (CVal → σ → ℝ≥0∞) → Prop} {AdmE : CE → Prop}
    {P : σ → ℝ≥0∞} {ε₁ ε₂ : ℝ≥0∞} {c b a : CProg}
    (h₁ : RefinesUpTo AdmQ AdmE ε₁ P Concretization.id (fun e : CE => e) b a
      (eqRel (CPred := σ → ℝ≥0∞)))
    (h₂ : RefinesUpTo AdmQ AdmE ε₂ P Concretization.id (fun e : CE => e) c b
      (eqRel (CPred := σ → ℝ≥0∞))) :
    RefinesUpTo AdmQ AdmE (ε₁ + ε₂) P Concretization.id (fun e : CE => e) c a
      (eqRel (CPred := σ → ℝ≥0∞)) := by
  intro Qa Ea hQa hEa s
  have k₁ := h₁ Qa Ea hQa hEa s
  have k₂ := h₂ Qa Ea hQa hEa s
  rw [Concretization.id_post_eqRel, meet_apply_eq_min] at k₁ k₂
  rw [Concretization.id_post_eqRel, meet_apply_eq_min]
  calc min (P s) (Concretization.id.pred (wp a Qa Ea) s)
      ≤ min (P s) (wp b Qa Ea s + ε₁) := le_min (min_le_left _ _) k₁
    _ ≤ min (P s) (wp b Qa Ea s) + ε₁ := min_add_le_min_add _ _ _
    _ ≤ wp c Qa Ea s + ε₂ + ε₁ := add_le_add k₂ le_rfl
    _ = wp c Qa Ea s + (ε₁ + ε₂) := by rw [add_assoc, add_comm ε₂]

/-- Refinement up to an error at the identity concretization, the identity exception map and
the equality return relation, as a graded level over `ℝ≥0∞`: the square of grade `g` from `top`
to `bot` states that `bot` refines `top` up to `g`. -/
def gradedLevel (AdmQ : (CVal → σ → ℝ≥0∞) → Prop) (AdmE : CE → Prop) (P : σ → ℝ≥0∞) :
    WRPGradedLevel.GradedLevel (Obj := PUnit.{1}) (fun _ _ => CProg) ℝ≥0∞ where
  Sq g top bot := RefinesUpTo AdmQ AdmE g P Concretization.id (fun e : CE => e) bot top
    (eqRel (CPred := σ → ℝ≥0∞))
  id f := RefinesUpTo.refl AdmQ AdmE 0 P f
  mono h hg := h.mono_err hg
  vcomp h₁ h₂ := RefinesUpTo.vcomp_id h₁ h₂

end Refl

section Vertical

variable {σc σb : Type} {CProg BProg AProg : Type u} {CVal BVal AVal : Type v} {APred : Type}
  {CE BE AE : Type w'} [Assertion APred] [Assertion CE] [Assertion BE] [Assertion AE]
  [WP CProg CVal (σc → ℝ≥0∞) CE] [WP BProg BVal (σb → ℝ≥0∞) BE] [WP AProg AVal APred AE]
  {γ₂ : Concretization (σc → ℝ≥0∞) (σb → ℝ≥0∞)} {γ₁ : Concretization (σb → ℝ≥0∞) APred}
  {eps₂ : BE → CE} {eps₁ : AE → BE} {c : CProg} {b : BProg} {a : AProg}
  {Q₂ : CVal → BVal → σc → ℝ≥0∞} {Q₁ : BVal → AVal → σb → ℝ≥0∞}
  {AdmQa : (AVal → APred) → Prop} {AdmEa : AE → Prop}
  {AdmQb : (BVal → σb → ℝ≥0∞) → Prop} {AdmEb : BE → Prop} {ε₁ ε₂ : ℝ≥0∞}

/-- **Vertical composition** with the inner refinement under `⊤`: the errors add, when the
outer concretization preserves suprema and moves an added constant outside, and the inner
concretization and exception map send admissible postconditions to admissible ones. -/
theorem RefinesUpTo.vcomp_top {P : σc → ℝ≥0∞} (hsup : γ₂.SupPreserving.{_, v})
    (hadd : ∀ (p : σb → ℝ≥0∞) (k : ℝ≥0∞) (s : σc),
      γ₂.pred (fun s' => p s' + k) s ≤ γ₂.pred p s + k)
    (hQ : ∀ Qa, AdmQa Qa → AdmQb (γ₁.post Q₁ Qa)) (hE : ∀ Ea, AdmEa Ea → AdmEb (eps₁ Ea))
    (h₁ : RefinesUpTo AdmQa AdmEa ε₁ Lean.Order.top γ₁ eps₁ b a Q₁)
    (h₂ : RefinesUpTo AdmQb AdmEb ε₂ P γ₂ eps₂ c b Q₂) :
    RefinesUpTo AdmQa AdmEa (ε₁ + ε₂) P (γ₂.comp γ₁) (fun e => eps₂ (eps₁ e)) c a
      (γ₂.relComp Q₂ Q₁) := by
  intro Qa Ea hQa hEa s
  have k₁ := refinesUpTo_top_iff.1 h₁ Qa Ea hQa hEa
  have k₂ := h₂ (γ₁.post Q₁ Qa) (eps₁ Ea) (hQ Qa hQa) (hE Ea hEa) s
  rw [meet_apply_eq_min] at k₂ ⊢
  calc min (P s) ((γ₂.comp γ₁).pred (wp a Qa Ea) s)
      ≤ min (P s) (γ₂.pred (fun s' => wp b (γ₁.post Q₁ Qa) (eps₁ Ea) s' + ε₁) s) :=
        min_le_min le_rfl (γ₂.pred_mono k₁ s)
    _ ≤ min (P s) (γ₂.pred (wp b (γ₁.post Q₁ Qa) (eps₁ Ea)) s + ε₁) :=
        min_le_min le_rfl (hadd _ _ _)
    _ ≤ min (P s) (γ₂.pred (wp b (γ₁.post Q₁ Qa) (eps₁ Ea)) s) + ε₁ :=
        min_add_le_min_add _ _ _
    _ ≤ wp c (γ₂.post Q₂ (γ₁.post Q₁ Qa)) (eps₂ (eps₁ Ea)) s + ε₂ + ε₁ :=
        add_le_add k₂ le_rfl
    _ ≤ wp c ((γ₂.comp γ₁).post (γ₂.relComp Q₂ Q₁) Qa) (eps₂ (eps₁ Ea)) s + ε₂ + ε₁ :=
        add_le_add (add_le_add
          (WP.wp_monotone_post (Concretization.post_comp_le hsup Q₂ Q₁ Qa) s) le_rfl) le_rfl
    _ = _ := by rw [add_assoc, add_comm ε₂]

/-- **Vertical composition** under preconditions: from refinements under `P₁` and `P₂`, the
composite holds under `P₂ ⊓ γ₂.pred P₁` with the errors added, when the outer concretization
preserves suprema and binary meets and moves an added constant outside, and the inner
concretization and exception map send admissible postconditions to admissible ones. -/
theorem RefinesUpTo.vcomp {P₁ : σb → ℝ≥0∞} {P₂ : σc → ℝ≥0∞}
    (hsup : γ₂.SupPreserving.{_, v}) (hmeet : γ₂.MeetPreserving)
    (hadd : ∀ (p : σb → ℝ≥0∞) (k : ℝ≥0∞) (s : σc),
      γ₂.pred (fun s' => p s' + k) s ≤ γ₂.pred p s + k)
    (hQ : ∀ Qa, AdmQa Qa → AdmQb (γ₁.post Q₁ Qa)) (hE : ∀ Ea, AdmEa Ea → AdmEb (eps₁ Ea))
    (h₁ : RefinesUpTo AdmQa AdmEa ε₁ P₁ γ₁ eps₁ b a Q₁)
    (h₂ : RefinesUpTo AdmQb AdmEb ε₂ P₂ γ₂ eps₂ c b Q₂) :
    RefinesUpTo AdmQa AdmEa (ε₁ + ε₂) (Lean.Order.meet P₂ (γ₂.pred P₁)) (γ₂.comp γ₁)
      (fun e => eps₂ (eps₁ e)) c a (γ₂.relComp Q₂ Q₁) := by
  intro Qa Ea hQa hEa s
  have k₁ := h₁ Qa Ea hQa hEa
  have k₂ := h₂ (γ₁.post Q₁ Qa) (eps₁ Ea) (hQ Qa hQa) (hE Ea hEa) s
  have k₃ := hmeet P₁ (γ₁.pred (wp a Qa Ea)) s
  rw [meet_apply_eq_min] at k₂ k₃ ⊢
  rw [meet_apply_eq_min]
  calc min (min (P₂ s) (γ₂.pred P₁ s)) ((γ₂.comp γ₁).pred (wp a Qa Ea) s)
      = min (P₂ s) (min (γ₂.pred P₁ s) (γ₂.pred (γ₁.pred (wp a Qa Ea)) s)) :=
        min_assoc _ _ _
    _ ≤ min (P₂ s) (γ₂.pred (fun s' => wp b (γ₁.post Q₁ Qa) (eps₁ Ea) s' + ε₁) s) :=
        min_le_min le_rfl (k₃.trans (γ₂.pred_mono k₁ s))
    _ ≤ min (P₂ s) (γ₂.pred (wp b (γ₁.post Q₁ Qa) (eps₁ Ea)) s + ε₁) :=
        min_le_min le_rfl (hadd _ _ _)
    _ ≤ min (P₂ s) (γ₂.pred (wp b (γ₁.post Q₁ Qa) (eps₁ Ea)) s) + ε₁ :=
        min_add_le_min_add _ _ _
    _ ≤ wp c (γ₂.post Q₂ (γ₁.post Q₁ Qa)) (eps₂ (eps₁ Ea)) s + ε₂ + ε₁ :=
        add_le_add k₂ le_rfl
    _ ≤ wp c ((γ₂.comp γ₁).post (γ₂.relComp Q₂ Q₁) Qa) (eps₂ (eps₁ Ea)) s + ε₂ + ε₁ :=
        add_le_add (add_le_add
          (WP.wp_monotone_post (Concretization.post_comp_le hsup Q₂ Q₁ Qa) s) le_rfl) le_rfl
    _ = _ := by rw [add_assoc, add_comm ε₂]

end Vertical

section Bind

variable {σ : Type} {mc : Type v → Type u} {ma : Type v → Type u} [Monad mc] [Monad ma]
  {APred : Type} {CE AE : Type w'} [Assertion APred] [Assertion CE] [Assertion AE]
  [WPMonad mc (σ → ℝ≥0∞) CE] [WPMonad ma APred AE]

/-- **Sequential composition**: if `c` refines `a` up to `ε₁` with return relation `R` and, for
all values, `k x` refines `g y` up to `ε₂` under the precondition `R x y`, then `c >>= k` refines
`a >>= g` up to `ε₁ + ε₂`. The side conditions: the abstract `wp` of `a >>= g` is below the
composite `wp` at admissible postconditions, the `wp` of `g` sends admissible postconditions to
admissible ones, and the `wp` of `c` moves an added constant outside. -/
theorem RefinesUpTo.bind {γ : Concretization (σ → ℝ≥0∞) APred} {eps : AE → CE}
    {α β α' β' : Type v} {P : σ → ℝ≥0∞} {c : mc α} {k : α → mc β} {a : ma α'}
    {g : α' → ma β'} {R : α → α' → σ → ℝ≥0∞} {Q : β → β' → σ → ℝ≥0∞}
    {AdmQ : (α' → APred) → Prop} {AdmQ' : (β' → APred) → Prop} {AdmE : AE → Prop}
    {ε₁ ε₂ : ℝ≥0∞}
    (hbind : ∀ (Qa : β' → APred) (Ea : AE), AdmQ' Qa → AdmE Ea →
      Lean.Order.PartialOrder.rel (wp (a >>= g) Qa Ea) (wp a (fun v => wp (g v) Qa Ea) Ea))
    (hadm : ∀ (Qa : β' → APred) (Ea : AE), AdmQ' Qa → AdmE Ea →
      AdmQ (fun v => wp (g v) Qa Ea))
    (hconst : ∀ (Y : α → σ → ℝ≥0∞) (r : ℝ≥0∞) (E : CE) (s : σ),
      wp c (fun x s' => Y x s' + r) E s ≤ wp c Y E s + r)
    (hc : RefinesUpTo AdmQ AdmE ε₁ P γ eps c a R)
    (hk : ∀ x y, RefinesUpTo AdmQ' AdmE ε₂ (R x y) γ eps (k x) (g y) Q) :
    RefinesUpTo AdmQ' AdmE (ε₁ + ε₂) P γ eps (c >>= k) (a >>= g) Q := by
  intro Qa Ea hQa hEa s
  let X : α' → APred := fun v => wp (g v) Qa Ea
  let Y : α → σ → ℝ≥0∞ := fun x => wp (k x) (γ.post Q Qa) (eps Ea)
  have hY : ∀ x s', γ.post R X x s' ≤ Y x s' + ε₂ := by
    intro x s'
    simp only [Concretization.post, Lean.Order.iSup_apply]
    exact Lean.Order.iSup_le (fun i => Lean.Order.meet (R x i) (γ.pred (X i)) s')
      (Y x s' + ε₂) fun y => hk x y Qa Ea hQa hEa s'
  have hm : Lean.Order.PartialOrder.rel (wp c (γ.post R X) (eps Ea))
      (wp c (fun x s' => Y x s' + ε₂) (eps Ea)) :=
    WP.wp_monotone_post fun x s' => hY x s'
  have hca := hc X Ea (hadm Qa Ea hQa hEa) hEa s
  rw [meet_apply_eq_min] at hca ⊢
  calc min (P s) (γ.pred (wp (a >>= g) Qa Ea) s)
      ≤ min (P s) (γ.pred (wp a X Ea) s) :=
        min_le_min le_rfl (γ.pred_mono (hbind Qa Ea hQa hEa) s)
    _ ≤ wp c (γ.post R X) (eps Ea) s + ε₁ := hca
    _ ≤ wp c (fun x s' => Y x s' + ε₂) (eps Ea) s + ε₁ :=
        add_le_add (hm s) le_rfl
    _ ≤ wp c Y (eps Ea) s + ε₂ + ε₁ := add_le_add (hconst Y ε₂ _ s) le_rfl
    _ ≤ wp (c >>= k) (γ.post Q Qa) (eps Ea) s + ε₂ + ε₁ :=
        add_le_add (add_le_add (WPMonad.bind_le_wp_bind c k _ _ s) le_rfl) le_rfl
    _ = _ := by rw [add_assoc, add_comm ε₂]

end Bind

/-! ## Examples -/

/-- A chain of `n` hops at the identity concretization pastes to a refinement whose error is
the sum of the errors of the hops. -/
example {σ CProg CVal CE : Type} [Assertion CE] [WP CProg CVal (σ → ℝ≥0∞) CE]
    (AdmQ : (CVal → σ → ℝ≥0∞) → Prop) (AdmE : CE → Prop) (P : σ → ℝ≥0∞) (f : ℕ → CProg)
    (g : ℕ → ℝ≥0∞) (n : ℕ)
    (h : ∀ i < n, RefinesUpTo AdmQ AdmE (g i) P Concretization.id (fun e : CE => e)
      (f (i + 1)) (f i) (eqRel (CPred := σ → ℝ≥0∞))) :
    RefinesUpTo AdmQ AdmE (∑ i ∈ Finset.range n, g i) P Concretization.id (fun e : CE => e)
      (f n) (f 0) (eqRel (CPred := σ → ℝ≥0∞)) :=
  (gradedLevel AdmQ AdmE P).vchain_finset (a := PUnit.unit) (b := PUnit.unit) f g n h

/-- An approximate first step followed by an exact continuation refines up to the error of the
first step. -/
example {σ : Type} {mc ma : Type → Type} [Monad mc] [Monad ma] {APred CE AE : Type}
    [Assertion APred] [Assertion CE] [Assertion AE] [WPMonad mc (σ → ℝ≥0∞) CE]
    [WPMonad ma APred AE] {γ : Concretization (σ → ℝ≥0∞) APred} {eps : AE → CE}
    {AdmQ : (Bool → APred) → Prop} {AdmE : AE → Prop} {P : σ → ℝ≥0∞} {ε : ℝ≥0∞}
    {c : mc Bool} {k : Bool → mc Bool} {a : ma Bool} {g : Bool → ma Bool}
    {R Q : Bool → Bool → σ → ℝ≥0∞}
    (hbind : ∀ (Qa : Bool → APred) (Ea : AE), AdmQ Qa → AdmE Ea →
      Lean.Order.PartialOrder.rel (wp (a >>= g) Qa Ea) (wp a (fun v => wp (g v) Qa Ea) Ea))
    (hadm : ∀ (Qa : Bool → APred) (Ea : AE), AdmQ Qa → AdmE Ea →
      AdmQ (fun v => wp (g v) Qa Ea))
    (hconst : ∀ (Y : Bool → σ → ℝ≥0∞) (r : ℝ≥0∞) (E : CE) (s : σ),
      wp c (fun x s' => Y x s' + r) E s ≤ wp c Y E s + r)
    (hc : RefinesUpTo AdmQ AdmE ε P γ eps c a R) (hk : ∀ x y, Refines (R x y) γ eps (k x) (g y) Q) :
    RefinesUpTo AdmQ AdmE ε P γ eps (c >>= k) (a >>= g) Q := by
  have := RefinesUpTo.bind hbind hadm hconst hc fun x y =>
    RefinesUpTo.of_refines (hk x y) _ _ 0
  simpa only [add_zero] using this

/-- Vertical composition with the identity as the outer concretization: its side conditions hold
by instance search and by reflexivity. -/
example {σ CProg BProg AProg CVal BVal AVal APred CE BE AE : Type} [Assertion APred]
    [Assertion CE] [Assertion BE] [Assertion AE] [WP CProg CVal (σ → ℝ≥0∞) CE]
    [WP BProg BVal (σ → ℝ≥0∞) BE] [WP AProg AVal APred AE]
    {γ₁ : Concretization (σ → ℝ≥0∞) APred} {eps₂ : BE → CE} {eps₁ : AE → BE} {c : CProg}
    {b : BProg} {a : AProg} {Q₂ : CVal → BVal → σ → ℝ≥0∞} {Q₁ : BVal → AVal → σ → ℝ≥0∞}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : RefinesUpTo (fun _ => True) (fun _ => True) ε₁ Lean.Order.top γ₁ eps₁ b a Q₁)
    (h₂ : RefinesUpTo (fun _ => True) (fun _ => True) ε₂ Lean.Order.top Concretization.id eps₂
      c b Q₂) :
    RefinesUpTo (fun _ => True) (fun _ => True) (ε₁ + ε₂) Lean.Order.top
      (Concretization.id.comp γ₁) (fun e => eps₂ (eps₁ e)) c a
      (Concretization.id.relComp Q₂ Q₁) :=
  RefinesUpTo.vcomp_top Concretization.IsSupPreserving.sup (fun _ _ _ => le_rfl)
    (fun _ _ => trivial) (fun _ _ => trivial) h₁ h₂

end CatCrypt.Refinement.WRPUpTo

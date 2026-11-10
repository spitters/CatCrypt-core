/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.Approx
public import CatCryptCore.Relational.RelationalQ0
public import PolyFun.Control.Monad.Algebra.Relational

/-!
# Quantitative relational weakest precondition on sub-distributions

`eRel d₁ d₂ post` is the supremum, over sub-couplings of the sub-distributions `d₁` and `d₂`
(joint sub-distributions whose marginals are dominated by `d₁` and `d₂`, no deficit bound), of
the expected value of `post : α → β → ℝ≥0∞`. It equals the supremum over exact couplings of
`d₁` and `d₂` with failure as a value on each side, where every outcome that fails on some side
scores `0` (`eRel_eq_iSup_optionCoupling`), the form of VCVio's `eRelWP` on `SDistr`. The monad
algebra `MAlgRelOrdered SDistr SDistr ℝ≥0∞` has `rwp := eRel`.

The agreement with approximate couplings, for every `R` and `ε`, is

  `liftRApprox ε R d₁ d₂ ↔ max (mass d₁) (mass d₂) - ε ≤ eRel d₁ d₂ (relIndicator R)`.

If one of the sub-distributions has no failure mass, then `max (mass d₁) (mass d₂) = 1` and
this is the threshold form `1 - ε ≤ eRel d₁ d₂ (relIndicator R)`. Without this hypothesis only
the implication from the threshold form to `liftRApprox` holds.

## Main results

* `eRel`, `relIndicator`: the quantitative relational weakest precondition and the indicator
  postcondition.
* `eRel_eq_iSup_optionCoupling`: the supremum over exact couplings with failure as a value.
* `eRel_pure`, `eRel_mono`, `eRel_bind_le`: the laws of the monad algebra.
* `instMAlgRelOrderedSDistr`: `MAlgRelOrdered SDistr SDistr ℝ≥0∞` with `rwp := eRel`.
* `instMAlgRelOrderedStateT`: its two-sided `StateT Heap` lift.
* `exists_subCoupling_eRel_eq`: a sub-coupling supported on `R` attains the supremum at the
  indicator of `R`.
* `liftRApprox_iff_mass_sub_le_eRel`: the agreement stated above.
* `liftRApprox_of_one_sub_le_eRel`, `liftRApprox_iff_one_sub_le_eRel`: the threshold form.
* `rHoareApprox_iff_stateT_rwp`: the judgment `rHoareApprox` read from the `StateT` lift.
* `approxTriple_bind`: the bind rule with additive error, from `rwp_bind_le`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Prob

open scoped ENNReal
open CatCrypt.Core CatCrypt.Relational Topology

variable {α β γ δ : Type*}

/-! ## The quantitative relational weakest precondition -/

open Classical in
/-- The indicator of a relation as an `ℝ≥0∞`-valued postcondition. -/
noncomputable def relIndicator (R : α → β → Prop) (a : α) (b : β) : ℝ≥0∞ :=
  if R a b then 1 else 0

/-- The expectation form of the relational weakest precondition on sub-distributions: the
supremum, over sub-couplings of `d₁` and `d₂`, of the coupled expectation of `post`. -/
noncomputable def eRel (d₁ : SDistr α) (d₂ : SDistr β) (post : α → β → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ c : SubCoupling d₁ d₂ ⊤, ∑' p : α × β, c.joint (some p) * post p.1 p.2

/-- A sub-coupling of any grade is a sub-coupling without deficit bound. -/
def SubCoupling.toTop {d₁ : SDistr α} {d₂ : SDistr β} {ε : ℝ≥0∞} (c : SubCoupling d₁ d₂ ε) :
    SubCoupling d₁ d₂ ⊤ :=
  ⟨c.joint, c.left_le, c.right_le, le_top, le_top⟩

/-- Each sub-coupling gives a lower bound of `eRel`. -/
theorem le_eRel {d₁ : SDistr α} {d₂ : SDistr β} (post : α → β → ℝ≥0∞)
    (c : SubCoupling d₁ d₂ ⊤) :
    ∑' p : α × β, c.joint (some p) * post p.1 p.2 ≤ eRel d₁ d₂ post :=
  le_iSup (fun c : SubCoupling d₁ d₂ ⊤ => ∑' p : α × β, c.joint (some p) * post p.1 p.2) c

/-- `eRel` is monotone in the postcondition. -/
theorem eRel_mono {d₁ : SDistr α} {d₂ : SDistr β} {post post' : α → β → ℝ≥0∞}
    (h : ∀ a b, post a b ≤ post' a b) : eRel d₁ d₂ post ≤ eRel d₁ d₂ post' :=
  iSup_mono fun _ => ENNReal.tsum_le_tsum fun _ => mul_le_mul_right (h _ _) _

/-- A sub-coupling of two point masses has its mass on the pair of the points. -/
private theorem subCoupling_pure_eq_zero {a : α} {b : β}
    (c : SubCoupling (SDistr.pure a) (SDistr.pure b) ⊤) {p : α × β} (hp : p ≠ (a, b)) :
    c.joint (some p) = 0 := by
  classical
  obtain ⟨a', b'⟩ := p
  by_cases ha : a' = a
  · have hb : b' ≠ b := fun hb => hp (by rw [ha, hb])
    have h := c.right_le b'
    rw [SDistr.pure_apply_some, ite_eq_right (Ne.symm hb)] at h
    exact (ENNReal.tsum_eq_zero.mp (le_antisymm h zero_le)) a'
  · have h := c.left_le a'
    rw [SDistr.pure_apply_some, ite_eq_right (Ne.symm ha)] at h
    exact (ENNReal.tsum_eq_zero.mp (le_antisymm h zero_le)) b'

/-- The point mass at `(a, b)` as a sub-coupling of the point masses at `a` and `b`. -/
private noncomputable def subCouplingPure (a : α) (b : β) :
    SubCoupling (SDistr.pure a) (SDistr.pure b) ⊤ := by
  classical
  refine ⟨SDistr.pure (a, b), fun a' => ?_, fun b' => ?_, le_top, le_top⟩
  · rw [tsum_eq_single b fun b' hb' => by simp [SDistr.pure_apply_some, Ne.symm hb']]
    simp [SDistr.pure_apply_some]
  · rw [tsum_eq_single a fun a' ha' => by simp [SDistr.pure_apply_some, Ne.symm ha']]
    simp [SDistr.pure_apply_some]

/-- The pure rule of `eRel`. -/
theorem eRel_pure (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    eRel (SDistr.pure a) (SDistr.pure b) post = post a b := by
  classical
  apply le_antisymm
  · refine iSup_le fun c => ?_
    rw [tsum_eq_single (a, b) fun p hp => by rw [subCoupling_pure_eq_zero c hp, zero_mul]]
    calc c.joint (some (a, b)) * post a b ≤ 1 * post a b :=
          mul_le_mul_left (PMF.coe_le_one _ _) _
      _ = post a b := one_mul _
  · calc post a b
        = ∑' p : α × β, (SDistr.pure (a, b) : SDistr (α × β)) (some p) * post p.1 p.2 := by
          rw [tsum_eq_single (a, b) fun p hp => by
            simp [SDistr.pure_apply_some, Ne.symm hp]]
          simp [SDistr.pure_apply_some]
      _ ≤ eRel (SDistr.pure a) (SDistr.pure b) post := le_eRel post (subCouplingPure a b)

/-- The failing joint as a sub-coupling. -/
private noncomputable def subCouplingFail (d₁ : SDistr α) (d₂ : SDistr β) :
    SubCoupling d₁ d₂ ⊤ :=
  ⟨SDistr.fail, fun a => by simp, fun b => by simp, le_top, le_top⟩

/-- Gluing a sub-coupling with a family of sub-couplings of the continuations. -/
private noncomputable def subCouplingBind {d₁ : SDistr α} {d₂ : SDistr β} {f : α → SDistr γ}
    {g : β → SDistr δ} (c : SubCoupling d₁ d₂ ⊤)
    (K : ∀ p : α × β, SubCoupling (f p.1) (g p.2) ⊤) :
    SubCoupling (d₁.bind f) (d₂.bind g) ⊤ := by
  refine ⟨c.joint.bind fun p => (K p).joint, fun x => ?_, fun y => ?_, le_top, le_top⟩
  · exact (bind_left_conditions c.joint (fun p => (K p).joint) d₁ f ⊤ ⊤ c.left_le le_top
      (fun p _ x => (K p).left_le x) (fun p _ => le_top)).1 x
  · calc ∑' a, (c.joint.bind fun p => (K p).joint) (some (a, y))
        = ∑' p : α × β, c.joint (some p) * ∑' a, (K p).joint (some (a, y)) :=
          bind_marginal_eq c.joint (fun p => (K p).joint) (fun a => (a, y))
      _ ≤ ∑' p : α × β, c.joint (some p) * (g p.2) (some y) :=
          ENNReal.tsum_le_tsum fun p => mul_le_mul_right ((K p).right_le y) _
      _ = ∑' q : β × α, c.joint (some q.swap) * (g q.1) (some y) :=
          ((Equiv.prodComm β α).tsum_eq
            fun p : α × β => c.joint (some p) * (g p.2) (some y)).symm
      _ = ∑' b, (∑' a, c.joint (some (a, b))) * (g b) (some y) := by
          rw [ENNReal.tsum_prod']
          refine tsum_congr fun b => ?_
          simp only [Prod.swap_prod_mk]
          exact ENNReal.tsum_mul_right
      _ ≤ ∑' b, d₂ (some b) * (g b) (some y) :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul_left (c.right_le b) _
      _ = (d₂.bind g) (some y) := (SDistr.bind_apply_some d₂ g y).symm

/-- The coupled expectation of a glued sub-coupling. -/
private theorem subCouplingBind_exp {d₁ : SDistr α} {d₂ : SDistr β} {f : α → SDistr γ}
    {g : β → SDistr δ} (c : SubCoupling d₁ d₂ ⊤)
    (K : ∀ p : α × β, SubCoupling (f p.1) (g p.2) ⊤) (post : γ → δ → ℝ≥0∞) :
    ∑' q : γ × δ, (subCouplingBind c K).joint (some q) * post q.1 q.2 =
      ∑' p : α × β, c.joint (some p) *
        ∑' q : γ × δ, (K p).joint (some q) * post q.1 q.2 := by
  calc ∑' q : γ × δ, (subCouplingBind c K).joint (some q) * post q.1 q.2
      = ∑' q : γ × δ, ∑' p : α × β,
          c.joint (some p) * ((K p).joint (some q) * post q.1 q.2) := by
        refine tsum_congr fun q => ?_
        simp only [subCouplingBind, SDistr.bind_apply_some, ← ENNReal.tsum_mul_right, mul_assoc]
    _ = ∑' p : α × β, ∑' q : γ × δ,
          c.joint (some p) * ((K p).joint (some q) * post q.1 q.2) := ENNReal.tsum_comm
    _ = _ := tsum_congr fun p => ENNReal.tsum_mul_left

/-- The sequential composition rule of `eRel`. -/
theorem eRel_bind_le (d₁ : SDistr α) (d₂ : SDistr β) (f : α → SDistr γ) (g : β → SDistr δ)
    (post : γ → δ → ℝ≥0∞) :
    eRel d₁ d₂ (fun a b => eRel (f a) (g b) post) ≤ eRel (d₁.bind f) (d₂.bind g) post := by
  classical
  refine iSup_le fun c => ?_
  -- the coupled expectation at a choice of continuation sub-couplings
  have key : ∀ K : ∀ p : α × β, SubCoupling (f p.1) (g p.2) ⊤,
      ∑' p : α × β, c.joint (some p) * ∑' q : γ × δ, (K p).joint (some q) * post q.1 q.2 ≤
        eRel (d₁.bind f) (d₂.bind g) post := fun K => by
    rw [← subCouplingBind_exp c K post]
    exact le_eRel post (subCouplingBind c K)
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  -- each finite partial sum is the supremum over choices `K`
  have hsum : ∑ p ∈ S, c.joint (some p) * eRel (f p.1) (g p.2) post =
      ⨆ K : ∀ p : α × β, SubCoupling (f p.1) (g p.2) ⊤,
        ∑ p ∈ S, c.joint (some p) * ∑' q : γ × δ, (K p).joint (some q) * post q.1 q.2 := by
    rw [← ENNReal.finsetSum_iSup]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [← ENNReal.mul_iSup, eRel]
      congr 1
      have : ∀ p : α × β, Nonempty (SubCoupling (f p.1) (g p.2) ⊤) :=
        fun p => ⟨subCouplingFail _ _⟩
      have hs : Function.Surjective
          (fun K : ∀ p : α × β, SubCoupling (f p.1) (g p.2) ⊤ => K p) :=
        Function.surjective_eval p
      exact (hs.iSup_comp fun k : SubCoupling (f p.1) (g p.2) ⊤ =>
        ∑' q : γ × δ, k.joint (some q) * post q.1 q.2).symm
    · intro K K'
      refine ⟨fun p => if ∑' q : γ × δ, (K p).joint (some q) * post q.1 q.2 ≤
          ∑' q : γ × δ, (K' p).joint (some q) * post q.1 q.2 then K' p else K p, fun p => ?_⟩
      by_cases hp : ∑' q : γ × δ, (K p).joint (some q) * post q.1 q.2 ≤
          ∑' q : γ × δ, (K' p).joint (some q) * post q.1 q.2
      · simp only [ite_eq_left hp]
        exact ⟨mul_le_mul_right hp _, le_rfl⟩
      · simp only [ite_eq_right hp]
        exact ⟨le_rfl, mul_le_mul_right (le_of_not_ge hp) _⟩
  rw [hsum]
  refine iSup_le fun K => le_trans (ENNReal.sum_le_tsum S) (key K)

/-- Sub-couplings of sub-distributions form an `ℝ≥0∞`-valued relational monad algebra with
relational weakest precondition `eRel`. -/
noncomputable instance instMAlgRelOrderedSDistr : MAlgRelOrdered SDistr SDistr ℝ≥0∞ where
  rwp := eRel
  rwp_pure a b post := eRel_pure a b post
  rwp_mono h := eRel_mono h
  rwp_bind_le x y f g post := eRel_bind_le x y f g post

/-- The two-sided `StateT Heap` lift of `instMAlgRelOrderedSDistr`. -/
noncomputable instance instMAlgRelOrderedStateT :
    MAlgRelOrdered (StateT Heap SDistr) (StateT Heap SDistr) (Heap → Heap → ℝ≥0∞) :=
  MAlgRelOrdered.stateTBoth Heap Heap

/-! ## The supremum at an indicator is attained -/

/-- The bound of a nonnegative function by its partial sum on a product of finite sets and the
tails of its marginal bounds. -/
private theorem tsum_le_sum_add_tails {w : α × β → ℝ≥0∞} {u : α → ℝ≥0∞} {v : β → ℝ≥0∞}
    (hu : ∀ a, ∑' b, w (a, b) ≤ u a) (hv : ∀ b, ∑' a, w (a, b) ≤ v b)
    (A : Finset α) (B : Finset β) :
    ∑' p, w p ≤ ∑ p ∈ A ×ˢ B, w p + (∑' a : {a // a ∉ A}, u a) + ∑' b : {b // b ∉ B}, v b := by
  classical
  have hS : ∑' p : α × β, (if p ∈ A ×ˢ B then w p else 0) = ∑ p ∈ A ×ˢ B, w p := by
    rw [tsum_eq_sum (s := A ×ˢ B) fun p hp => ite_eq_right hp]
    exact Finset.sum_congr rfl fun p hp => ite_eq_left hp
  have hA : ∑' p : α × β, ({a | a ∉ A} : Set α).indicator (fun _ => w p) p.1 ≤
      ∑' a : {a // a ∉ A}, u a := by
    calc ∑' p : α × β, ({a | a ∉ A} : Set α).indicator (fun _ => w p) p.1
        = ∑' a, ∑' b, ({a | a ∉ A} : Set α).indicator (fun _ => w (a, b)) a :=
          ENNReal.tsum_prod'
      _ ≤ ∑' a, ({a | a ∉ A} : Set α).indicator u a := ENNReal.tsum_le_tsum fun a => by
          by_cases ha : a ∈ A
          · simp [Set.indicator, ha]
          · simpa [Set.indicator, ha] using hu a
      _ = _ := (tsum_subtype {a | a ∉ A} u).symm
  have hB : ∑' p : α × β, ({b | b ∉ B} : Set β).indicator (fun _ => w p) p.2 ≤
      ∑' b : {b // b ∉ B}, v b := by
    calc ∑' p : α × β, ({b | b ∉ B} : Set β).indicator (fun _ => w p) p.2
        = ∑' q : β × α, ({b | b ∉ B} : Set β).indicator (fun _ => w q.swap) q.1 :=
          ((Equiv.prodComm β α).tsum_eq
            fun p : α × β => ({b | b ∉ B} : Set β).indicator (fun _ => w p) p.2).symm
      _ = ∑' b, ∑' a, ({b | b ∉ B} : Set β).indicator (fun _ => w (a, b)) b :=
          ENNReal.tsum_prod'
      _ ≤ ∑' b, ({b | b ∉ B} : Set β).indicator v b := ENNReal.tsum_le_tsum fun b => by
          by_cases hb : b ∈ B
          · simp [Set.indicator, hb]
          · simpa [Set.indicator, hb] using hv b
      _ = _ := (tsum_subtype {b | b ∉ B} v).symm
  calc ∑' p, w p
      ≤ ∑' p : α × β, ((if p ∈ A ×ˢ B then w p else 0) +
          ({a | a ∉ A} : Set α).indicator (fun _ => w p) p.1 +
          ({b | b ∉ B} : Set β).indicator (fun _ => w p) p.2) := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;>
          simp [Set.indicator, ha, hb, Finset.mem_product]
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_add, hS]
    _ ≤ _ := add_le_add (add_le_add_right hA _) hB

/-- A function on pairs dominated by the marginal bounds `u`, `v` with support in `R`. -/
private def IsDom (R : α → β → Prop) (u : α → ℝ≥0∞) (v : β → ℝ≥0∞) (w : α × β → ℝ≥0∞) : Prop :=
  (∀ a, ∑' b, w (a, b) ≤ u a) ∧ (∀ b, ∑' a, w (a, b) ≤ v b) ∧ ∀ p, ¬ R p.1 p.2 → w p = 0

private theorem isClosed_isDom (R : α → β → Prop) (u : α → ℝ≥0∞) (v : β → ℝ≥0∞) :
    IsClosed {w | IsDom R u v w} := by
  have h1 : ∀ a, IsClosed {w : α × β → ℝ≥0∞ | ∑' b, w (a, b) ≤ u a} := fun a => by
    simp only [ENNReal.tsum_eq_iSup_sum, iSup_le_iff, Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_le
      (continuous_finsetSum _ fun b _ => continuous_apply _) continuous_const
  have h2 : ∀ b, IsClosed {w : α × β → ℝ≥0∞ | ∑' a, w (a, b) ≤ v b} := fun b => by
    simp only [ENNReal.tsum_eq_iSup_sum, iSup_le_iff, Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_le
      (continuous_finsetSum _ fun a _ => continuous_apply _) continuous_const
  simp only [IsDom, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter h1).inter ((isClosed_iInter h2).inter
    (isClosed_iInter fun p => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply p) continuous_const))

/-- A sub-distribution with prescribed mass function on `some`, the rest of the mass on
`none`. -/
private noncomputable def ofSubMass (w : α → ℝ≥0∞) (hw : ∑' a, w a ≤ 1) : SDistr α :=
  ⟨fun o => match o with
    | some a => w a
    | none => 1 - ∑' a, w a, by
    refine ENNReal.summable.hasSum_iff.mpr ?_
    rw [SDistr.tsum_option_eq_add]
    exact tsub_add_cancel_of_le hw⟩

/-- Among the functions dominated by summable marginal bounds and supported in `R`, one has
maximal sum. -/
private theorem exists_max_isDom (R : α → β → Prop) (u : α → ℝ≥0∞) (v : β → ℝ≥0∞)
    (hu : ∑' a, u a ≠ ∞) (hv : ∑' b, v b ≠ ∞) :
    ∃ w, IsDom R u v w ∧ ∀ w', IsDom R u v w' → ∑' p, w' p ≤ ∑' p, w p := by
  classical
  have hK : IsCompact {w | IsDom R u v w} := (isClosed_isDom R u v).isCompact
  have hne : {w | IsDom R u v w}.Nonempty := ⟨fun _ => 0, by simp [IsDom]⟩
  have husc : UpperSemicontinuousOn (fun w : α × β → ℝ≥0∞ => ∑' p, w p) {w | IsDom R u v w} := by
    intro w _ y hy
    -- choose finite sets whose tails keep the bound below `y`
    have tU := ENNReal.tendsto_tsum_compl_atTop_zero hu
    have tV := ENNReal.tendsto_tsum_compl_atTop_zero hv
    have e1 : ∀ᶠ A : Finset α in Filter.atTop, ∑' p, w p + ∑' a : {a // a ∉ A}, u a < y := by
      have := (tendsto_const_nhds (x := ∑' p, w p)).add tU
      rw [add_zero] at this
      exact this.eventually_lt_const hy
    obtain ⟨A, hA⟩ := e1.exists
    have e2 : ∀ᶠ B : Finset β in Filter.atTop,
        ∑' p, w p + ∑' a : {a // a ∉ A}, u a + ∑' b : {b // b ∉ B}, v b < y := by
      have := (tendsto_const_nhds
        (x := ∑' p, w p + ∑' a : {a // a ∉ A}, u a)).add tV
      rw [add_zero] at this
      exact this.eventually_lt_const hA
    obtain ⟨B, hB⟩ := e2.exists
    set tA := ∑' a : {a // a ∉ A}, u a
    set tB := ∑' b : {b // b ∉ B}, v b
    have hopen : IsOpen {x : α × β → ℝ≥0∞ | ∑ p ∈ A ×ˢ B, x p + tA + tB < y} :=
      isOpen_lt ((continuous_finsetSum _ fun p _ => continuous_apply p).add continuous_const
        |>.add continuous_const) continuous_const
    have hw : ∑ p ∈ A ×ˢ B, w p + tA + tB < y :=
      lt_of_le_of_lt (by gcongr; exact ENNReal.sum_le_tsum _) hB
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hw), self_mem_nhdsWithin]
      with x hx hxK
    exact lt_of_le_of_lt (tsum_le_sum_add_tails hxK.1 hxK.2.1 A B) hx
  obtain ⟨w, hw, hmax⟩ := husc.exists_isMaxOn hne hK
  exact ⟨w, hw, fun w' hw' => hmax hw'⟩

/-- At the indicator of `R`, the supremum of `eRel` is attained by a sub-coupling supported
on `R`. -/
theorem exists_subCoupling_eRel_eq (R : α → β → Prop) (d₁ : SDistr α) (d₂ : SDistr β) :
    ∃ c : SubCoupling d₁ d₂ ⊤, c.satisfies R ∧
      ∑' p, c.joint (some p) = eRel d₁ d₂ (relIndicator R) := by
  classical
  obtain ⟨w, hw, hmax⟩ := exists_max_isDom R (fun a => d₁ (some a)) (fun b => d₂ (some b))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (SDistr.tsum_some_le_one d₁))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (SDistr.tsum_some_le_one d₂))
  have hw1 : ∑' p, w p ≤ 1 := by
    rw [ENNReal.tsum_prod']
    exact le_trans (ENNReal.tsum_le_tsum hw.1) (SDistr.tsum_some_le_one d₁)
  let joint : SDistr (α × β) := ofSubMass w hw1
  have hj : ∀ p, joint (some p) = w p := fun _ => rfl
  let c : SubCoupling d₁ d₂ ⊤ :=
    ⟨joint, fun a => by simpa only [hj] using hw.1 a, fun b => by simpa only [hj] using hw.2.1 b,
      le_top, le_top⟩
  have hsat : c.satisfies R := fun a b hab => by
    by_contra hR
    exact hab (by simpa [c, hj] using hw.2.2 (a, b) hR)
  refine ⟨c, hsat, le_antisymm ?_ ?_⟩
  · calc ∑' p, c.joint (some p)
        = ∑' p : α × β, c.joint (some p) * relIndicator R p.1 p.2 := by
          refine tsum_congr fun p => ?_
          by_cases hp : c.joint (some p) = 0
          · simp [hp]
          · simp [relIndicator, hsat p.1 p.2 hp]
      _ ≤ _ := le_eRel _ c
  · refine iSup_le fun c' => ?_
    have hdom : IsDom R (fun a => d₁ (some a)) (fun b => d₂ (some b))
        (fun p => c'.joint (some p) * relIndicator R p.1 p.2) := by
      refine ⟨fun a => ?_, fun b => ?_, fun p hp => by simp [relIndicator, hp]⟩
      · refine le_trans (ENNReal.tsum_le_tsum fun b => ?_) (c'.left_le a)
        by_cases h : R a b <;> simp [relIndicator, h]
      · refine le_trans (ENNReal.tsum_le_tsum fun a => ?_) (c'.right_le b)
        by_cases h : R a b <;> simp [relIndicator, h]
    exact le_trans (hmax _ hdom) (le_of_eq (tsum_congr fun p => (hj p).symm))

/-! ## The supremum over exact couplings with failure as a value -/

/-- An exact coupling of `d₁` and `d₂`, in which failure is the value `none` of each side. -/
abbrev OptionCoupling (d₁ : SDistr α) (d₂ : SDistr β) : Type _ :=
  {π : PMF (Option α × Option β) //
    (∀ x, ∑' y, π (x, y) = d₁ x) ∧ ∀ y, ∑' x, π (x, y) = d₂ y}

/-- The sum over the pairs of values is at most the sum over all outcomes. -/
private theorem optionCoupling_sub (w : Option α × Option β → ℝ≥0∞) :
    ∑' p : α × β, w (some p.1, some p.2) ≤ ∑' p, w p :=
  ENNReal.tsum_comp_le_tsum_of_injective
    (f := fun p : α × β => (some p.1, some p.2))
    (fun _ _ h => Prod.ext (Option.some.inj (congrArg Prod.fst h))
      (Option.some.inj (congrArg Prod.snd h))) w

/-- The sub-coupling obtained from an exact coupling by discarding every outcome that fails
on some side. -/
private noncomputable def OptionCoupling.toSub {d₁ : SDistr α} {d₂ : SDistr β}
    (π : OptionCoupling d₁ d₂) : SubCoupling d₁ d₂ ⊤ := by
  refine ⟨ofSubMass (fun p => π.1 (some p.1, some p.2)) ?_, fun a => ?_, fun b => ?_,
    le_top, le_top⟩
  · exact le_trans (optionCoupling_sub _) (le_of_eq π.1.tsum_coe)
  · refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective β)
      (fun y => π.1 (some a, y))) (le_of_eq (π.2.1 (some a)))
  · refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective α)
      (fun x => π.1 (x, some b))) (le_of_eq (π.2.2 (some b)))

/-- The mass function of the extension of a sub-coupling to an exact coupling: the mass
of the sub-coupling, plus the product of the residual marginals scaled by the residual mass. -/
private noncomputable def extFn (W : Option α × Option β → ℝ≥0∞) (r₁ : Option α → ℝ≥0∞)
    (r₂ : Option β → ℝ≥0∞) (ρ : ℝ≥0∞) (p : Option α × Option β) : ℝ≥0∞ :=
  W p + r₁ p.1 * r₂ p.2 / ρ

/-- The residuals of a marginal, summed. -/
private theorem residual_sum {γ' : Type*} {m d : γ' → ℝ≥0∞} (hle : ∀ x, m x ≤ d x)
    (hd : ∑' x, d x = 1) (hm : ∑' x, m x ≠ ∞) :
    ∑' x, (d x - m x) = 1 - ∑' x, m x := by
  refine ENNReal.eq_sub_of_add_eq hm ?_
  rw [← ENNReal.tsum_add, ← hd]
  exact tsum_congr fun x => tsub_add_cancel_of_le (hle x)

/-- `eRel` is the supremum over exact couplings, with failure as a value on each side, of the
expectation of `post` on the pairs of values. -/
theorem eRel_eq_iSup_optionCoupling (d₁ : SDistr α) (d₂ : SDistr β) (post : α → β → ℝ≥0∞) :
    eRel d₁ d₂ post = ⨆ π : OptionCoupling d₁ d₂,
      ∑' p : α × β, π.1 (some p.1, some p.2) * post p.1 p.2 := by
  classical
  apply le_antisymm
  · refine iSup_le fun c => ?_
    -- the marginals of the sub-coupling on the `Option` values
    let W : Option α × Option β → ℝ≥0∞ := fun p => match p with
      | (some a, some b) => c.joint (some (a, b))
      | _ => 0
    let mL : Option α → ℝ≥0∞ := fun x => ∑' y, W (x, y)
    let mR : Option β → ℝ≥0∞ := fun y => ∑' x, W (x, y)
    have hmLs : ∀ a, mL (some a) = ∑' b, c.joint (some (a, b)) := fun a => by
      simp only [mL, SDistr.tsum_option_eq_add, W, zero_add]
    have hmRs : ∀ b, mR (some b) = ∑' a, c.joint (some (a, b)) := fun b => by
      simp only [mR, SDistr.tsum_option_eq_add, W, zero_add]
    have hmLn : mL none = 0 := by simp [mL, W]
    have hmRn : mR none = 0 := by simp [mR, W]
    have hLle : ∀ x, mL x ≤ d₁ x := fun x => by
      cases x with
      | none => simp [hmLn]
      | some a => simpa only [hmLs] using c.left_le a
    have hRle : ∀ y, mR y ≤ d₂ y := fun y => by
      cases y with
      | none => simp [hmRn]
      | some b => simpa only [hmRs] using c.right_le b
    have hmass : ∑' p : α × β, c.joint (some p) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (SDistr.tsum_some_le_one c.joint)
    have hmLt : ∑' x, mL x = ∑' p : α × β, c.joint (some p) := by
      rw [SDistr.tsum_option_eq_add, hmLn, zero_add, ENNReal.tsum_prod']
      exact tsum_congr hmLs
    have hmRt : ∑' y, mR y = ∑' p : α × β, c.joint (some p) := by
      rw [SDistr.tsum_option_eq_add, hmRn, zero_add,
        ← (Equiv.prodComm β α).tsum_eq fun p : α × β => c.joint (some p), ENNReal.tsum_prod']
      exact tsum_congr hmRs
    let r₁ : Option α → ℝ≥0∞ := fun x => d₁ x - mL x
    let r₂ : Option β → ℝ≥0∞ := fun y => d₂ y - mR y
    let ρ : ℝ≥0∞ := 1 - ∑' p : α × β, c.joint (some p)
    have hr₁ : ∑' x, r₁ x = ρ := by
      simp only [r₁, ρ]
      rw [residual_sum hLle d₁.tsum_coe (hmLt ▸ hmass), hmLt]
    have hr₂ : ∑' y, r₂ y = ρ := by
      simp only [r₂, ρ]
      rw [residual_sum hRle d₂.tsum_coe (hmRt ▸ hmass), hmRt]
    have hρ : ρ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    -- scaling a residual by the residual mass over itself
    have hscale₁ : ∀ x, r₁ x * ρ / ρ = r₁ x := fun x => by
      by_cases h0 : ρ = 0
      · have : r₁ x = 0 := ENNReal.tsum_eq_zero.mp (hr₁.trans h0) x
        simp [this]
      · rw [mul_div_assoc, ENNReal.div_self h0 hρ, mul_one]
    have hscale₂ : ∀ y, ρ * r₂ y / ρ = r₂ y := fun y => by
      by_cases h0 : ρ = 0
      · have : r₂ y = 0 := ENNReal.tsum_eq_zero.mp (hr₂.trans h0) y
        simp [this]
      · rw [mul_comm ρ, mul_div_assoc, ENNReal.div_self h0 hρ, mul_one]
    have hleft : ∀ x, ∑' y, extFn W r₁ r₂ ρ (x, y) = d₁ x := fun x => by
      simp only [extFn, ENNReal.tsum_add, div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hr₂]
      change mL x + r₁ x * ρ * ρ⁻¹ = d₁ x
      rw [← div_eq_mul_inv, hscale₁, add_tsub_cancel_of_le (hLle x)]
    have hright : ∀ y, ∑' x, extFn W r₁ r₂ ρ (x, y) = d₂ y := fun y => by
      simp only [extFn, ENNReal.tsum_add, div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, hr₁]
      change mR y + ρ * r₂ y * ρ⁻¹ = d₂ y
      rw [← div_eq_mul_inv, hscale₂, add_tsub_cancel_of_le (hRle y)]
    have htotal : HasSum (extFn W r₁ r₂ ρ) 1 := by
      refine ENNReal.summable.hasSum_iff.mpr ?_
      rw [ENNReal.tsum_prod']
      exact (tsum_congr hleft).trans d₁.tsum_coe
    let π : OptionCoupling d₁ d₂ := ⟨⟨extFn W r₁ r₂ ρ, htotal⟩, hleft, hright⟩
    refine le_trans (ENNReal.tsum_le_tsum fun p => ?_) (le_iSup (fun π : OptionCoupling d₁ d₂ =>
      ∑' p : α × β, π.1 (some p.1, some p.2) * post p.1 p.2) π)
    refine mul_le_mul_left ?_ _
    change c.joint (some p) ≤ c.joint (some p) + _
    exact le_self_add
  · refine iSup_le fun π => ?_
    exact le_trans (le_of_eq (tsum_congr fun p => rfl)) (le_eRel post π.toSub)

/-! ## Agreement with approximate couplings -/

/-- The total left deficit is the mass of `d₁` less the mass of the joint. -/
private theorem left_deficit_eq {d₁ : SDistr α} {d₂ : SDistr β} {ε : ℝ≥0∞}
    (c : SubCoupling d₁ d₂ ε) :
    ∑' a, (d₁ (some a) - ∑' b, c.joint (some (a, b))) =
      SDistr.mass d₁ - ∑' p, c.joint (some p) := by
  have h : ∑' a, (d₁ (some a) - ∑' b, c.joint (some (a, b))) + ∑' p, c.joint (some p) =
      SDistr.mass d₁ := by
    rw [ENNReal.tsum_prod', ← ENNReal.tsum_add, ← tsum_some_eq_mass]
    exact tsum_congr fun a => tsub_add_cancel_of_le (c.left_le a)
  exact ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (SDistr.tsum_some_le_one c.joint)) h

/-- The total right deficit is the mass of `d₂` less the mass of the joint. -/
private theorem right_deficit_eq {d₁ : SDistr α} {d₂ : SDistr β} {ε : ℝ≥0∞}
    (c : SubCoupling d₁ d₂ ε) :
    ∑' b, (d₂ (some b) - ∑' a, c.joint (some (a, b))) =
      SDistr.mass d₂ - ∑' p, c.joint (some p) := by
  have hs : ∑' p, c.joint (some p) = ∑' b, ∑' a, c.joint (some (a, b)) := by
    rw [← (Equiv.prodComm β α).tsum_eq fun p : α × β => c.joint (some p), ENNReal.tsum_prod']
    rfl
  have h : ∑' b, (d₂ (some b) - ∑' a, c.joint (some (a, b))) + ∑' p, c.joint (some p) =
      SDistr.mass d₂ := by
    rw [hs, ← ENNReal.tsum_add, ← tsum_some_eq_mass]
    exact tsum_congr fun b => tsub_add_cancel_of_le (c.right_le b)
  exact ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (SDistr.tsum_some_le_one c.joint)) h

/-- The agreement of approximate couplings with the quantitative weakest precondition: an
`ε`-approximate sub-coupling supported on `R` exists exactly when the indicator of `R` has
expected value at least `max (mass d₁) (mass d₂) - ε`. No hypothesis on the masses. -/
theorem liftRApprox_iff_mass_sub_le_eRel {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    {ε : ℝ≥0∞} :
    liftRApprox ε R d₁ d₂ ↔
      max (SDistr.mass d₁) (SDistr.mass d₂) - ε ≤ eRel d₁ d₂ (relIndicator R) := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    have hsum : ∑' p, c.joint (some p) ≤ eRel d₁ d₂ (relIndicator R) := by
      calc ∑' p, c.joint (some p)
          = ∑' p : α × β, c.joint (some p) * relIndicator R p.1 p.2 := by
            refine tsum_congr fun p => ?_
            by_cases hp : c.joint (some p) = 0
            · simp [hp]
            · simp [relIndicator, hc p.1 p.2 hp]
        _ ≤ _ := le_eRel _ c.toTop
    have hL := c.left_deficit
    have hR := c.right_deficit
    rw [left_deficit_eq, tsub_le_iff_right] at hL
    rw [right_deficit_eq, tsub_le_iff_right] at hR
    rw [tsub_le_iff_right]
    exact max_le (le_trans hL (by rw [add_comm]; gcongr)) (le_trans hR (by rw [add_comm]; gcongr))
  · intro h
    obtain ⟨c, hsat, heq⟩ := exists_subCoupling_eRel_eq R d₁ d₂
    have h' : ∀ m, m ≤ max (SDistr.mass d₁) (SDistr.mass d₂) →
        m - ∑' p, c.joint (some p) ≤ ε := fun m hm => by
      rw [heq, tsub_le_iff_right, add_comm]
      exact le_trans hm (tsub_le_iff_right.mp h)
    refine ⟨⟨c.joint, c.left_le, c.right_le, ?_, ?_⟩, hsat⟩
    · rw [left_deficit_eq]; exact h' _ (le_max_left _ _)
    · rw [right_deficit_eq]; exact h' _ (le_max_right _ _)

/-- A sub-distribution has mass at most `1`. -/
private theorem mass_le_one (d : SDistr α) : SDistr.mass d ≤ 1 := tsub_le_self

/-- The threshold form implies the approximate coupling, without hypothesis on the masses. -/
theorem liftRApprox_of_one_sub_le_eRel {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    {ε : ℝ≥0∞} (h : 1 - ε ≤ eRel d₁ d₂ (relIndicator R)) : liftRApprox ε R d₁ d₂ :=
  liftRApprox_iff_mass_sub_le_eRel.mpr
    (le_trans (tsub_le_tsub_right (max_le (mass_le_one d₁) (mass_le_one d₂)) ε) h)

/-- If one of the two sub-distributions has no failure mass, the approximate coupling is the
threshold form `1 - ε ≤ eRel d₁ d₂ (relIndicator R)`. -/
theorem liftRApprox_iff_one_sub_le_eRel {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    {ε : ℝ≥0∞} (hd : d₁ none = 0 ∨ d₂ none = 0) :
    liftRApprox ε R d₁ d₂ ↔ 1 - ε ≤ eRel d₁ d₂ (relIndicator R) := by
  have hm : max (SDistr.mass d₁) (SDistr.mass d₂) = 1 := by
    refine le_antisymm (max_le (mass_le_one d₁) (mass_le_one d₂)) ?_
    rcases hd with h | h
    · exact le_max_of_le_left (by simp [SDistr.mass, h])
    · exact le_max_of_le_right (by simp [SDistr.mass, h])
  rw [liftRApprox_iff_mass_sub_le_eRel, hm]

/-- The grade of `instRelQ0SDistr` at the instance: `RelQ0.liftR` on `SDistr` agrees with the
relational weakest precondition of `instMAlgRelOrderedSDistr` at the indicator. -/
theorem liftR_iff_mass_sub_le_rwp {α β : Type} {R : α → β → Prop} {d₁ : SDistr α}
    {d₂ : SDistr β} {ε : ℝ≥0∞} :
    RelQ0.liftR ε R d₁ d₂ ↔
      max (SDistr.mass d₁) (SDistr.mass d₂) - ε ≤
        MAlgRelOrdered.rwp d₁ d₂ (relIndicator R) :=
  liftRApprox_iff_mass_sub_le_eRel

/-! ## The stateful reading and the bind rule with additive error -/

/-- The indicator of a stateful relational postcondition as a postcondition of the `StateT`
lift. -/
noncomputable def relIndicatorState {α β : Type} (Ψ : RPost α β) :
    α → β → Heap → Heap → ℝ≥0∞ :=
  fun a b h₁ h₂ => relIndicator (fun p q => Ψ p.1 p.2 q.1 q.2) (a, h₁) (b, h₂)

/-- The graded judgment read from the `StateT` lift at the indicator of the postcondition. -/
theorem rHoareApprox_iff_stateT_rwp {α β : Type} {ε : ℝ≥0∞} {Φ : RPre}
    {c₁ : SPComp α} {c₂ : SPComp β} {Ψ : RPost α β} :
    rHoareApprox ε Φ c₁ c₂ Ψ ↔
      ∀ h₁ h₂, Φ h₁ h₂ →
        max (SDistr.mass (c₁ h₁)) (SDistr.mass (c₂ h₂)) - ε ≤
          MAlgRelOrdered.rwp (m₁ := StateT Heap SDistr) (m₂ := StateT Heap SDistr)
            (l := Heap → Heap → ℝ≥0∞) c₁ c₂ (relIndicatorState Ψ) h₁ h₂ :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ =>
    liftRApprox_iff_mass_sub_le_eRel

private theorem one_sub_add_le_mul (a b : ℝ≥0∞) : 1 - (a + b) ≤ (1 - a) * (1 - b) := by
  by_cases ha : 1 ≤ a
  · simp [tsub_eq_zero_of_le (le_trans ha le_self_add)]
  by_cases hb : 1 ≤ b
  · simp [tsub_eq_zero_of_le (le_trans hb le_add_self)]
  push Not at ha hb
  rw [tsub_le_iff_right]
  set p := 1 - a
  set q := 1 - b
  have hap : a + p = 1 := add_tsub_cancel_of_le ha.le
  have hbq : b + q = 1 := add_tsub_cancel_of_le hb.le
  have hp1 : p ≤ 1 := tsub_le_self
  have h : (1 : ℝ≥0∞) = a * (b + q) + p * b + p * q := by
    rw [hbq, mul_one, add_assoc, ← mul_add, hbq, mul_one, hap]
  calc (1 : ℝ≥0∞) = a * (b + q) + p * b + p * q := h
    _ = a + p * b + p * q := by rw [hbq, mul_one]
    _ ≤ a + b + p * q := by
        gcongr
        exact mul_le_of_le_one_left' hp1
    _ = p * q + (a + b) := by rw [add_comm]

/-- `eRel` at a scaled indicator is the scaled `eRel`. -/
theorem eRel_relIndicator_mul (d₁ : SDistr α) (d₂ : SDistr β) (R : α → β → Prop) (t : ℝ≥0∞) :
    eRel d₁ d₂ (fun a b => relIndicator R a b * t) = eRel d₁ d₂ (relIndicator R) * t := by
  simp only [eRel, ENNReal.iSup_mul, ← ENNReal.tsum_mul_right, mul_assoc]

/-- **Bind rule with additive error**, from the sequential composition rule `rwp_bind_le` of
the monad algebra. -/
theorem approxTriple_bind {α β γ δ : Type} {x : SDistr α} {y : SDistr β} {f : α → SDistr γ}
    {g : β → SDistr δ} {R : α → β → Prop} {S : γ → δ → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (hxy : MAlgRelOrdered.Triple (1 - ε₁) x y (relIndicator R))
    (hfg : ∀ a b, R a b → MAlgRelOrdered.Triple (1 - ε₂) (f a) (g b) (relIndicator S)) :
    MAlgRelOrdered.Triple (1 - (ε₁ + ε₂)) (x >>= f) (y >>= g) (relIndicator S) := by
  classical
  have hcut : MAlgRelOrdered.Triple ((1 - ε₁) * (1 - ε₂)) x y
      (fun a b => relIndicator R a b * (1 - ε₂)) := by
    change (1 - ε₁) * (1 - ε₂) ≤ eRel x y (fun a b => relIndicator R a b * (1 - ε₂))
    rw [eRel_relIndicator_mul]
    exact mul_le_mul_left hxy _
  have hstep : ∀ a b, MAlgRelOrdered.Triple (relIndicator R a b * (1 - ε₂)) (f a) (g b)
      (relIndicator S) := fun a b => by
    by_cases hR : R a b
    · simpa [relIndicator, hR] using hfg a b hR
    · simp [MAlgRelOrdered.Triple, relIndicator, hR]
  exact MAlgRelOrdered.triple_conseq (one_sub_add_le_mul ε₁ ε₂) (fun _ _ => le_rfl)
    (MAlgRelOrdered.triple_bind hcut hstep)

/-- The mass-corrected bind rule on `SDistr`: the approximate coupling reading of the bind rule
with additive error, for sub-distributions with failure mass. -/
theorem mass_sub_le_eRel_bind {R : α → β → Prop} {S : γ → δ → Prop} {ε₁ ε₂ : ℝ≥0∞}
    {x : SDistr α} {y : SDistr β} {f : α → SDistr γ} {g : β → SDistr δ}
    (hxy : max (SDistr.mass x) (SDistr.mass y) - ε₁ ≤ eRel x y (relIndicator R))
    (hfg : ∀ a b, R a b →
      max (SDistr.mass (f a)) (SDistr.mass (g b)) - ε₂ ≤ eRel (f a) (g b) (relIndicator S)) :
    max (SDistr.mass (x.bind f)) (SDistr.mass (y.bind g)) - (ε₁ + ε₂) ≤
      eRel (x.bind f) (y.bind g) (relIndicator S) :=
  liftRApprox_iff_mass_sub_le_eRel.mp
    (liftRApprox_bind (liftRApprox_iff_mass_sub_le_eRel.mpr hxy)
      fun a b hab => liftRApprox_iff_mass_sub_le_eRel.mpr (hfg a b hab))

end CatCrypt.Prob

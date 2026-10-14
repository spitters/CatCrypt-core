/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Unary.ExpectationWP
public import CatCryptCore.Unary.ExpectedCost
public import CatCryptCore.Examples.DetCPA
public import Std.Tactic.Do

@[expose] public section
set_option autoImplicit false

/-!
# `Std.Internal.Do` weakest-precondition instances for `SPComp` at the expectation carrier

Two instances of the toolchain's `Std.Internal.Do.WPMonad` class for `SPComp`, so that
the `vcgen` tactic decomposes quantitative goals about `SPComp` programs.

* Lower bounds: `WPMonad SPComp (Heap → ℝ≥0∞) ℝ≥0∞`. The transformer is the
  failure-weighted preexpectation `wpEF c post e h = wpE c post h + e * (c h) none`;
  at the exception postcondition `⊥ = 0` it is `wpE`, and a triple `⦃P⦄ c ⦃Q⦄` states
  `P ≤ wpE c Q`.
* Upper bounds: the type synonym `SPCompU` of `SPComp` with
  `WPMonad SPCompU (Heap → ℝ≥0∞ᵒᵈ) ℝ≥0∞ᵒᵈ`, the same transformer over the order dual.
  A triple with exception postcondition `toDual 0` states `wpE c Q ≤ P`: failure
  contributes `0`. At the default exception postcondition `⊥ = toDual ⊤` a failure
  outcome contributes `⊤`.

The `Lean.Order` complete-lattice structures on `ℝ≥0∞` and `ℝ≥0∞ᵒᵈ` are those of Mathlib.

## Main definitions

* `wpEF`: the failure-weighted weakest preexpectation.
* `instWPMonadSPComp`, `SPCompU`, `instWPMonadSPCompU`: the two `WPMonad` instances.

## Main statements

* `wp_eq_wpEF`, `wp_bot_eq_wpE`, `triple_iff_le_wpE`: the lower-bound reading.
* `SPCompU.wp_eq`, `SPCompU.triple_iff_wpE_le`: the upper-bound reading;
  `SPCompU.spec_wpE`: the upper-bound triple of an arbitrary computation, used as the
  specification of an abstract sub-program.
* `@[spec]` triples for `SPComp.pure`, `SPComp.bind`, `SPComp.sample`, `SPComp.get`,
  `SPComp.set` and `SPComp.fail` in both instances.
* `same_msg_prTrue_vcgen`, `prEventComp_bind_step_le_vcgen`: two quantitative
  statements of `CatCryptCore.Examples.DetCPA` and `CatCrypt.Unary.QueryBound` proved
  by `vcgen` and arithmetic.
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## `Lean.Order` complete lattices from Mathlib's -/

/-- The `Lean.Order` complete lattice of a Mathlib complete lattice: `⊑` is `≤` and the
supremum of a predicate is the `sSup` of its extension. -/
abbrev leanOrderCompleteLatticeOf (α : Type) [_root_.CompleteLattice α] :
    Lean.Order.CompleteLattice α where
  rel a b := a ≤ b
  rel_refl := le_refl _
  rel_trans := le_trans
  rel_antisymm := le_antisymm
  has_sup c :=
    ⟨sSup {x | c x}, fun _ => ⟨fun hsup _ hcy => le_trans (le_sSup hcy) hsup, sSup_le⟩⟩

noncomputable instance instLeanOrderCompleteLatticeENNReal : Lean.Order.CompleteLattice ℝ≥0∞ :=
  leanOrderCompleteLatticeOf ℝ≥0∞

noncomputable instance instLeanOrderCompleteLatticeENNRealDual :
    Lean.Order.CompleteLattice ℝ≥0∞ᵒᵈ :=
  leanOrderCompleteLatticeOf ℝ≥0∞ᵒᵈ

/-- The chain-complete partial order of `ℝ≥0∞` induced by its complete lattice; it
supplies the bottom `Lean.Order.bot` used as the default exception postcondition. -/
noncomputable instance instLeanOrderCCPOENNReal : Lean.Order.CCPO ℝ≥0∞ where
  has_csup {c} _ := Lean.Order.CompleteLattice.has_sup c

/-- The chain-complete partial order of `ℝ≥0∞ᵒᵈ` induced by its complete lattice. -/
noncomputable instance instLeanOrderCCPOENNRealDual : Lean.Order.CCPO ℝ≥0∞ᵒᵈ where
  has_csup {c} _ := Lean.Order.CompleteLattice.has_sup c

/-! ## The failure-weighted preexpectation -/

/-- Failure-weighted weakest preexpectation: the expectation of `post` over the
successful outcomes of `c h`, plus `e` times the failure mass of `c h`. -/
noncomputable def wpEF {α : Type} (c : SPComp α) (post : α → Heap → ℝ≥0∞) (e : ℝ≥0∞)
    (h : Heap) : ℝ≥0∞ :=
  wpE c post h + e * (c h) none

/-- The failure mass of a bind: failure of the first computation, plus the
failure mass of the continuation weighted by each successful outcome. -/
theorem spcomp_bind_apply_none {α β : Type} (c : SPComp α) (f : α → SPComp β) (h : Heap) :
    (SPComp.bind c f h) none =
      (c h) none + ∑' p : α × Heap, (c h) (some p) * (f p.1 p.2) none := by
  show (SDistr.bind (c h) fun p : α × Heap => f p.1 p.2) none = _
  unfold SDistr.bind
  rw [PMF.bind_apply, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail_apply_none, mul_one]

/-- `wpEF` of `pure`. -/
@[simp] theorem wpEF_pure {α : Type} (a : α) (post : α → Heap → ℝ≥0∞) (e : ℝ≥0∞)
    (h : Heap) : wpEF (SPComp.pure a) post e h = post a h := by
  simp only [wpEF, wpE_pure, SPComp.pure, SDistr.pure_apply_none, mul_zero, add_zero]

/-- `wpEF` is a monad morphism on bind. -/
theorem wpEF_bind {α β : Type} (c : SPComp α) (f : α → SPComp β)
    (post : β → Heap → ℝ≥0∞) (e : ℝ≥0∞) (h : Heap) :
    wpEF (SPComp.bind c f) post e h = wpEF c (fun a h' => wpEF (f a) post e h') e h := by
  simp only [wpEF]
  rw [wpE_bind, spcomp_bind_apply_none, wpE_add, wpE_const_mul,
    wpE_eq_tsum c (fun a h' => (f a h') none)]
  ring

/-- `wpEF` is monotone in both the post-expectation and the failure weight. -/
theorem wpEF_mono {α : Type} (c : SPComp α) {post post' : α → Heap → ℝ≥0∞}
    {e e' : ℝ≥0∞} (hpost : ∀ a h', post a h' ≤ post' a h') (he : e ≤ e') (h : Heap) :
    wpEF c post e h ≤ wpEF c post' e' h :=
  add_le_add (wpE_mono c hpost h) (mul_le_mul_left he _)

/-- `wpEF` of a uniform sample. -/
theorem wpEF_sample (α : Type) [Fintype α] [Nonempty α] (post : α → Heap → ℝ≥0∞)
    (e : ℝ≥0∞) (h : Heap) :
    wpEF (SPComp.sample α) post e h = (Fintype.card α : ℝ≥0∞)⁻¹ * ∑' a : α, post a h := by
  have hnone : (SPComp.sample α h) none = 0 := by
    show ((SDistr.uniform α).bind fun a => SDistr.pure (a, h)) none = 0
    unfold SDistr.bind
    rw [PMF.bind_apply, SDistr.tsum_option_eq_add]
    simp [SDistr.uniform_apply_none, SDistr.pure_apply_none]
  rw [wpEF, wpE_sample, hnone, mul_zero, add_zero]

/-- `wpEF` of a heap read. -/
@[simp] theorem wpEF_get (l : Location) (post : l.ty → Heap → ℝ≥0∞) (e : ℝ≥0∞) (h : Heap) :
    wpEF (SPComp.get l) post e h = post (h.get l) h := by
  simp only [wpEF, wpE_get, SPComp.get, SDistr.pure_apply_none, mul_zero, add_zero]

/-- `wpEF` of a heap write. -/
@[simp] theorem wpEF_set (l : Location) (v : l.ty) (post : Unit → Heap → ℝ≥0∞) (e : ℝ≥0∞)
    (h : Heap) : wpEF (SPComp.set l v) post e h = post () (h.set l v) := by
  simp only [wpEF, wpE_set, SPComp.set, SDistr.pure_apply_none, mul_zero, add_zero]

/-- `wpEF` of failure is the failure weight. -/
@[simp] theorem wpEF_fail {α : Type} (post : α → Heap → ℝ≥0∞) (e : ℝ≥0∞) (h : Heap) :
    wpEF (SPComp.fail : SPComp α) post e h = e := by
  simp only [wpEF, wpE_fail, SPComp.fail, SDistr.fail_apply_none, mul_one, zero_add]

/-! ## The lower-bound instance -/

open Std.Internal.Do

/-- The `WPMonad` instance of `SPComp` at the expectation carrier: the transformer is
`wpEF`, ordered by `≤`. -/
noncomputable instance instWPMonadSPComp : WPMonad SPComp (Heap → ℝ≥0∞) ℝ≥0∞ where
  toWP _ :=
    { wpTrans := fun c => ⟨fun post e h => wpEF c post e h⟩
      wp_trans_monotone := fun c _ _ _ _ he hpost h =>
        wpEF_mono c (fun a h' => hpost a h') he h }
  pure_le_wp_pure x post e := fun h => (wpEF_pure x post e h).ge
  bind_le_wp_bind c f post e := fun h => (wpEF_bind c f post e h).ge

/-- The weakest precondition of `SPComp` is `wpEF`. -/
theorem wp_eq_wpEF {α : Type} (c : SPComp α) (post : α → Heap → ℝ≥0∞) (e : ℝ≥0∞) :
    wp c post e = wpEF c post e := rfl

/-- The `Lean.Order` bottom of `ℝ≥0∞` is `0`. -/
theorem lean_order_bot_eq_zero : (Lean.Order.bot : ℝ≥0∞) = 0 :=
  le_antisymm (Lean.Order.bot_le (0 : ℝ≥0∞)) zero_le

/-- At the exception postcondition `⊥`, the weakest precondition of `SPComp` is `wpE`. -/
theorem wp_bot_eq_wpE {α : Type} (c : SPComp α) (post : α → Heap → ℝ≥0∞) :
    wp c post Lean.Order.bot = wpE c post := by
  funext h
  rw [wp_eq_wpEF, wpEF, lean_order_bot_eq_zero, zero_mul, add_zero]

/-- A lower-bound triple at exception postcondition `⊥` is the pointwise bound
`P ≤ wpE c Q`. -/
theorem triple_iff_le_wpE {α : Type} (c : SPComp α) (P : Heap → ℝ≥0∞)
    (Q : α → Heap → ℝ≥0∞) :
    Triple c P Q Lean.Order.bot ↔ ∀ h, P h ≤ wpE c Q h := by
  constructor
  · intro ht h
    have := ht.le_wp h
    rwa [wp_bot_eq_wpE] at this
  · intro hle
    exact ⟨fun h => by rw [wp_bot_eq_wpE]; exact hle h⟩

/-! ### Specifications of the primitives -/

/-- Specification of `SPComp.pure`. -/
@[spec] theorem spec_pure {α : Type} (a : α) {post : α → Heap → ℝ≥0∞} {e : ℝ≥0∞} :
    Triple (SPComp.pure a) (post a) post e :=
  ⟨fun h => (wpEF_pure a post e h).ge⟩

/-- Specification of `SPComp.bind`. -/
@[spec] theorem spec_bind {α β : Type} (c : SPComp α) (f : α → SPComp β)
    {post : β → Heap → ℝ≥0∞} {e : ℝ≥0∞} :
    Triple (SPComp.bind c f) (wp c (fun a => wp (f a) post e) e) post e :=
  ⟨fun h => (wpEF_bind c f post e h).ge⟩

/-- Specification of a uniform sample: the average of the post-expectation. -/
@[spec] theorem spec_sample (α : Type) [Fintype α] [Nonempty α]
    {post : α → Heap → ℝ≥0∞} {e : ℝ≥0∞} :
    Triple (SPComp.sample α) (fun h => (Fintype.card α : ℝ≥0∞)⁻¹ * ∑' a : α, post a h)
      post e :=
  ⟨fun h => (wpEF_sample α post e h).ge⟩

/-- Specification of a heap read. -/
@[spec] theorem spec_get (l : Location) {post : l.ty → Heap → ℝ≥0∞} {e : ℝ≥0∞} :
    Triple (SPComp.get l) (fun h => post (h.get l) h) post e :=
  ⟨fun h => (wpEF_get l post e h).ge⟩

/-- Specification of a heap write. -/
@[spec] theorem spec_set (l : Location) (v : l.ty) {post : Unit → Heap → ℝ≥0∞}
    {e : ℝ≥0∞} :
    Triple (SPComp.set l v) (fun h => post () (h.set l v)) post e :=
  ⟨fun h => (wpEF_set l v post e h).ge⟩

/-- Specification of failure: the precondition is the failure weight. -/
@[spec] theorem spec_fail {α : Type} {post : α → Heap → ℝ≥0∞} {e : ℝ≥0∞} :
    Triple (SPComp.fail : SPComp α) (fun _ => e) post e :=
  ⟨fun h => (wpEF_fail post e h).ge⟩

/-- The `Lean.Order` relation on `ℝ≥0∞` is `≤`. -/
@[simp] theorem leanOrder_rel_iff_le (a b : ℝ≥0∞) :
    Lean.Order.PartialOrder.rel a b ↔ a ≤ b := Iff.rfl

/-- The `Lean.Order` relation on `ℝ≥0∞ᵒᵈ` is the reversed `≤` of `ℝ≥0∞`. -/
@[simp] theorem leanOrder_rel_dual_iff (a b : ℝ≥0∞ᵒᵈ) :
    Lean.Order.PartialOrder.rel a b ↔ OrderDual.ofDual b ≤ OrderDual.ofDual a := Iff.rfl

set_option mvcgen.warning false in
open CatCryptCore.Examples.DetCPA in
/-- `CatCryptCore.Examples.DetCPA.same_msg_prTrue` by `vcgen`: the equality adversary
returns `true` with probability `1` on two encryptions of one message. -/
theorem same_msg_prTrue_vcgen (m : Bool) :
    CatCrypt.Crypto.prTrue ((det_enc_pair xorDet m m).bind eq_adversary) Heap.empty = 1 := by
  refine le_antisymm (CatCrypt.Crypto.prTrue_le_one _ _) ?_
  rw [← wpE_indicator_eq_prTrue]
  have ht : Triple ((det_enc_pair xorDet m m).bind eq_adversary)
      (fun _ => (1 : ℝ≥0∞)) (fun (b : Bool) (_ : Heap) => if b then (1 : ℝ≥0∞) else 0)
      Lean.Order.bot := by
    unfold det_enc_pair eq_adversary xorDet
    vcgen
    all_goals simp only [leanOrder_rel_iff_le, tsum_bool, wp_eq_wpEF, wpEF_pure,
      Fintype.card_bool, beq_self_eq_true]
    all_goals simp only [if_true, ← two_mul, Nat.cast_ofNat, mul_one]
    all_goals rw [ENNReal.inv_mul_cancel] <;> simp
  exact (triple_iff_le_wpE _ _ _).1 ht Heap.empty

/-! ## The upper-bound instance -/

/-- `SPComp` read for upper bounds: the same computations, with the weakest
precondition taken over the order dual of `ℝ≥0∞`. -/
def SPCompU (α : Type) : Type := SPComp α

noncomputable instance : Monad SPCompU := inferInstanceAs (Monad SPComp)

noncomputable instance : LawfulMonad SPCompU := inferInstanceAs (LawfulMonad SPComp)

/-- An `SPComp` computation as an `SPCompU` computation. -/
def SPCompU.lift {α : Type} (c : SPComp α) : SPCompU α := c

/-- The `WPMonad` instance of `SPCompU`: the transformer is `wpEF` over the order dual
of `ℝ≥0∞`, so a triple bounds the preexpectation from above. -/
noncomputable instance instWPMonadSPCompU : WPMonad SPCompU (Heap → ℝ≥0∞ᵒᵈ) ℝ≥0∞ᵒᵈ where
  toWP _ :=
    { wpTrans := fun c => ⟨fun post e h => OrderDual.toDual
        (wpEF (c : SPComp _) (fun a h' => OrderDual.ofDual (post a h'))
          (OrderDual.ofDual e) h)⟩
      wp_trans_monotone := fun c _ _ _ _ he hpost h =>
        wpEF_mono (c : SPComp _) (fun a h' => hpost a h') he h }
  pure_le_wp_pure x _ _ := fun h => (wpEF_pure x _ _ h).le
  bind_le_wp_bind c f _ _ := fun h => (wpEF_bind (c : SPComp _) f _ _ h).le

/-- The weakest precondition of `SPCompU` is `wpEF` over the order dual. -/
theorem SPCompU.wp_eq {α : Type} (c : SPComp α) (post : α → Heap → ℝ≥0∞ᵒᵈ)
    (e : ℝ≥0∞ᵒᵈ) (h : Heap) :
    wp (SPCompU.lift c) post e h = OrderDual.toDual
      (wpEF c (fun a h' => OrderDual.ofDual (post a h')) (OrderDual.ofDual e) h) := rfl

/-- An upper-bound triple at exception postcondition `toDual 0` is the pointwise bound
`wpE c Q ≤ P`: failure contributes `0`. -/
theorem SPCompU.triple_iff_wpE_le {α : Type} (c : SPComp α) (P : Heap → ℝ≥0∞)
    (Q : α → Heap → ℝ≥0∞) :
    Triple (SPCompU.lift c) (fun h => OrderDual.toDual (P h))
        (fun a h => OrderDual.toDual (Q a h)) (OrderDual.toDual 0) ↔
      ∀ h, wpE c Q h ≤ P h := by
  constructor
  · intro ht h
    have := ht.le_wp h
    simpa [SPCompU.wp_eq, wpEF] using this
  · intro hle
    exact ⟨fun h => by simpa [SPCompU.wp_eq, wpEF] using hle h⟩

/-- Every `SPComp` computation meets the upper-bound triple whose precondition is its
preexpectation at failure weight `0`. -/
theorem SPCompU.spec_wpE {α : Type} (c : SPComp α) {post : α → Heap → ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift c)
      (fun h => OrderDual.toDual (wpE c (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) :=
  ⟨fun h => by simp [SPCompU.wp_eq, wpEF]⟩

/-- Upper-bound specification of `SPComp.bind`. -/
@[spec] theorem SPCompU.spec_bind {α β : Type} (c : SPComp α) (f : α → SPComp β)
    {post : β → Heap → ℝ≥0∞ᵒᵈ} {e : ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift (SPComp.bind c f))
      (wp (SPCompU.lift c) (fun a => wp (SPCompU.lift (f a)) post e) e) post e :=
  ⟨fun h => (wpEF_bind c f _ _ h).le⟩

/-- Upper-bound specification of monadic bind on `SPComp`. -/
@[spec] theorem SPCompU.spec_monad_bind {α β : Type} (c : SPComp α) (f : α → SPComp β)
    {post : β → Heap → ℝ≥0∞ᵒᵈ} {e : ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift (c >>= f))
      (wp (SPCompU.lift c) (fun a => wp (SPCompU.lift (f a)) post e) e) post e :=
  ⟨fun h => (wpEF_bind c f _ _ h).le⟩

/-- Upper-bound specification of `SPComp.pure`. -/
@[spec] theorem SPCompU.spec_pure {α : Type} (a : α) {post : α → Heap → ℝ≥0∞ᵒᵈ}
    {e : ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift (SPComp.pure a)) (post a) post e :=
  ⟨fun h => (wpEF_pure a _ _ h).le⟩

/-- Upper-bound specification of monadic `pure` on `SPComp`. -/
@[spec] theorem SPCompU.spec_monad_pure {α : Type} (a : α) {post : α → Heap → ℝ≥0∞ᵒᵈ}
    {e : ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift (pure a : SPComp α)) (post a) post e :=
  ⟨fun h => (wpEF_pure a _ _ h).le⟩

/-- Upper-bound specification of a uniform sample. -/
@[spec] theorem SPCompU.spec_sample (α : Type) [Fintype α] [Nonempty α]
    {post : α → Heap → ℝ≥0∞ᵒᵈ} {e : ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift (SPComp.sample α))
      (fun h => OrderDual.toDual
        ((Fintype.card α : ℝ≥0∞)⁻¹ * ∑' a : α, OrderDual.ofDual (post a h))) post e :=
  ⟨fun h => (wpEF_sample α _ _ h).le⟩

/-- Upper-bound specification of a heap read. -/
@[spec] theorem SPCompU.spec_get (l : Location) {post : l.ty → Heap → ℝ≥0∞ᵒᵈ}
    {e : ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift (SPComp.get l)) (fun h => post (h.get l) h) post e :=
  ⟨fun h => (wpEF_get l _ _ h).le⟩

/-- Upper-bound specification of a heap write. -/
@[spec] theorem SPCompU.spec_set (l : Location) (v : l.ty) {post : Unit → Heap → ℝ≥0∞ᵒᵈ}
    {e : ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift (SPComp.set l v)) (fun h => post () (h.set l v)) post e :=
  ⟨fun h => (wpEF_set l v _ _ h).le⟩

/-- Upper-bound specification of failure: the precondition is the failure weight. -/
@[spec] theorem SPCompU.spec_fail {α : Type} {post : α → Heap → ℝ≥0∞ᵒᵈ} {e : ℝ≥0∞ᵒᵈ} :
    Triple (SPCompU.lift (SPComp.fail : SPComp α)) (fun _ => e) post e :=
  ⟨fun h => (wpEF_fail _ _ h).le⟩

set_option mvcgen.warning false in
/-- `CatCrypt.Unary.prEventComp_bind_step_le` by `vcgen` on `SPCompU`: if from every
non-bad heap one step reaches a bad heap with probability at most `ε`, then appending
the step to `m` adds at most `ε` to the probability of a bad final heap. -/
theorem prEventComp_bind_step_le_vcgen
    (m : SPComp Unit) (step : SPComp Unit) (h₀ : Heap) (bad : Heap → Prop)
    (ε : ℝ≥0∞)
    (h_fresh : ∀ h₁ : Heap, ¬ bad h₁ →
      prEvent (step h₁) (fun _ h' => bad h') ≤ ε) :
    prEventComp (m.bind (fun _ => step)) h₀ (fun _ h' => bad h') ≤
      prEventComp m h₀ (fun _ h' => bad h') + ε := by
  classical
  rw [← wpE_indicator_eq_prEventComp, ← wpE_indicator_eq_prEventComp]
  have hstep : Triple (SPCompU.lift step)
      (fun h => OrderDual.toDual (if bad h then 1 else ε))
      (fun _ h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0))
      (OrderDual.toDual 0) := by
    refine (SPCompU.triple_iff_wpE_le _ _ _).2 fun h => ?_
    rw [wpE_indicator_eq_prEventComp]
    by_cases hb : bad h
    · simpa [hb, prEventComp] using (prEvent_le_mass _ _).trans (sdistr_mass_le_one _)
    · simpa [hb, prEventComp] using h_fresh h hb
  have hm : ∀ post : Unit → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift m)
      (fun h => OrderDual.toDual (wpE m (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE m
  have ht : Triple
      (SPCompU.lift (α := PUnit) (SPComp.bind (α := PUnit) (β := PUnit) m fun _ => step))
      (fun h => OrderDual.toDual
        (wpE (α := PUnit) m (fun _ h' => if bad h' then (1 : ℝ≥0∞) else 0) h + ε))
      (fun (_ : PUnit) h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0))
      (OrderDual.toDual 0) := by
    vcgen [hstep, hm]
    rename_i h
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual]
    calc wpE m (fun _ h' => OrderDual.ofDual (wp (SPCompU.lift step)
            (fun _ h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0))
            (OrderDual.toDual 0) h')) h
        ≤ wpE m (fun _ h' => (if bad h' then (1 : ℝ≥0∞) else 0) + ε) h := by
          refine wpE_mono m (fun _ h' => ?_) h
          have hle := hstep.le_wp h'
          simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual] at hle
          refine le_trans hle ?_
          split_ifs <;> simp
      _ ≤ wpE m (fun _ h' => if bad h' then (1 : ℝ≥0∞) else 0) h + ε := by
          rw [wpE_add]
          exact add_le_add le_rfl (wpE_const_le m ε h)
  exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h₀

end CatCrypt.Unary

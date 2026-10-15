/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Unary.ExpectationVCGenExamples

set_option autoImplicit false

/-!
# Further `vcgen` proofs of expected-cost and probability statements

Each theorem `foo_vcgen` restates an existing theorem `foo` and proves it with `vcgen` on
one of the two `WPMonad` instances of `CatCryptCore.Unary.ExpectationVCGen` (lower bounds on
`SPComp`, upper bounds on `SPCompU`), followed by arithmetic on `wpE`. An equality is
proved as a lower-bound and an upper-bound triple, or as one triple and the trivial bound
`0 ≤ x`. The statements are those of the originals; the originals are not used in the
proofs.

Like `CatCryptCore.Unary.ExpectationVCGenExamples`, this file is not a `module`, because
`CatCryptCore.Unary.ExpectedCost` does not expose the bodies of `ecost`, `CostComp.bind`
and `CostComp.lift`.

## Main statements

* `ecost_pure_vcgen`, `ecost_charge_vcgen`: the expected cost of `CostComp.pure` and of
  `CostComp.charge`.
* `ecost_lift_le_vcgen`, `ecost_lift_of_lossless_vcgen`: the expected cost of a lift at a
  flat price, with an abstract computation.
* `ecost_bind_le_add_vcgen`: the uniform-bound form of the tower law.
* `prEventComp_pure_vcgen`, `prEventComp_loopGame_vcgen`: the bad-event probability of a
  pure computation and of `loopGame`.
* `BadEvent.prTrue_pure_false_eq_zero_vcgen`, `BadEvent.prTrue_union_bound_list_vcgen`:
  the constant `false` game and the union bound for a list of events.
* `prTrue_bind_sample_Bool_vcgen`: a Boolean sample followed by an abstract continuation.
* `DetCPA.diff_msg_prTrue_vcgen`: the equality adversary on two encryptions of different
  messages.
-/

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal
open Std.Internal.Do

namespace CatCrypt.Unary

set_option mvcgen.warning false in
/-- `ecost_pure` by `vcgen` on `SPCompU`. -/
theorem ecost_pure_vcgen {α : Type} (a : α) (h : Heap) : ecost (CostComp.pure a) h = 0 := by
  have ht : Triple (SPCompU.lift (CostComp.pure a)) (fun _ => OrderDual.toDual 0)
      (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
    unfold CostComp.pure
    vcgen
    simp
  exact le_antisymm ((SPCompU.triple_iff_wpE_le _ _ _).1 ht h) zero_le

set_option mvcgen.warning false in
/-- `ecost_charge` by `vcgen`: a lower-bound triple on `SPComp` and an upper-bound triple
on `SPCompU`. -/
theorem ecost_charge_vcgen (n : ℕ) (h : Heap) :
    ecost (CostComp.charge n) h = n := by
  have hlo : Triple (Prog := SPComp (Unit × ℕ)) (CostComp.charge n) (fun _ => (n : ℝ≥0∞))
      (fun r _ => (r.2 : ℝ≥0∞)) Lean.Order.bot := by
    unfold CostComp.charge
    vcgen
    simp
  have hup : Triple (SPCompU.lift (CostComp.charge n)) (fun _ => OrderDual.toDual (n : ℝ≥0∞))
      (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
    unfold CostComp.charge
    vcgen
    simp
  exact le_antisymm ((SPCompU.triple_iff_wpE_le _ _ _).1 hup h)
    ((triple_iff_le_wpE _ _ _).1 hlo h)

set_option mvcgen.warning false in
/-- `ecost_lift_le` by `vcgen` on `SPCompU`, with `c` as an abstract sub-program. -/
theorem ecost_lift_le_vcgen {α : Type} (c : SPComp α) (price : ℕ) (h : Heap) :
    ecost (CostComp.lift c price) h ≤ price := by
  have hc : ∀ post : α → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift c)
      (fun h => OrderDual.toDual (wpE c (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE c
  have ht : Triple (SPCompU.lift (CostComp.lift c price))
      (fun _ => OrderDual.toDual (price : ℝ≥0∞))
      (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
    unfold CostComp.lift
    vcgen [hc]
    rename_i s
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF_pure]
    exact wpE_const_le c _ s
  exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h

set_option mvcgen.warning false in
/-- `ecost_lift_of_lossless` by `vcgen`: the upper bound is `ecost_lift_le_vcgen`, the
lower bound is a lower-bound triple on `SPComp` with `c` abstract. -/
theorem ecost_lift_of_lossless_vcgen {α : Type} {c : SPComp α} (hc : isLossless c)
    (price : ℕ) (h : Heap) :
    ecost (CostComp.lift c price) h = price := by
  refine le_antisymm (ecost_lift_le_vcgen c price h) ?_
  have hc' : ∀ (post : α → Heap → ℝ≥0∞) (e : ℝ≥0∞), Triple c (fun h => wpE c post h) post e :=
    fun _ _ => spec_wpE_lower c
  have ht : Triple (Prog := SPComp (α × ℕ)) (CostComp.lift c price)
      (fun _ => (price : ℝ≥0∞)) (fun r _ => (r.2 : ℝ≥0∞)) Lean.Order.bot := by
    unfold CostComp.lift
    vcgen [hc']
    rename_i s
    have hp : ∀ a : α, wpEF (SPComp.pure (a, price)) (fun r (_ : Heap) => (r.2 : ℝ≥0∞))
        Lean.Order.bot = fun _ => (price : ℝ≥0∞) := fun a => funext (wpEF_pure _ _ _)
    simp only [leanOrder_rel_iff_le, wp_eq_wpEF, hp]
    exact (wpE_const_of_lossless hc _ s).ge
  exact (triple_iff_le_wpE _ _ _).1 ht h

set_option mvcgen.warning false in
/-- `ecost_bind_le_add` by `vcgen` on `SPCompU`, with `c` and the continuation abstract. -/
theorem ecost_bind_le_add_vcgen {α β : Type} {c : CostComp α} {f : α → CostComp β}
    {C₁ C₂ : ℝ≥0∞}
    (hc : ∀ h, ecost c h ≤ C₁) (hf : ∀ a h, ecost (f a) h ≤ C₂) (h : Heap) :
    ecost (CostComp.bind c f) h ≤ C₁ + C₂ := by
  have hcs : ∀ post : α × ℕ → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift c)
      (fun h => OrderDual.toDual (wpE c (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE c
  have ht : Triple (SPCompU.lift (CostComp.bind c f)) (fun _ => OrderDual.toDual (C₁ + C₂))
      (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
    unfold CostComp.bind
    vcgen [hcs]
    rename_i s
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF, zero_mul,
      add_zero, wpE_bind, wpE_pure, Nat.cast_add, wpE_add]
    refine (add_le_add
      (wpE_mono (post' := fun p _ => (p.2 : ℝ≥0∞)) c (fun p h' => wpE_const_le _ _ _) s)
      (wpE_mono (post' := fun _ _ => C₂) c (fun p h' => hf p.1 h') s)).trans ?_
    exact add_le_add (hc s) (wpE_const_le _ _ _)
  exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h

open Classical in
set_option mvcgen.warning false in
/-- `prEventComp_pure` by `vcgen`: a lower-bound and an upper-bound triple for
`SPComp.pure a` with the indicator of `bad` as post-expectation. -/
theorem prEventComp_pure_vcgen {α : Type} (a : α) (h₀ : Heap) (bad : Heap → Prop) :
    prEventComp (SPComp.pure a) h₀ (fun _ h' => bad h') =
      (if bad h₀ then 1 else 0) := by
  rw [← wpE_indicator_eq_prEventComp]
  have hlo : Triple (SPComp.pure a) (fun h => if bad h then (1 : ℝ≥0∞) else 0)
      (fun _ h => if bad h then (1 : ℝ≥0∞) else 0) Lean.Order.bot := by
    vcgen
  have hup : Triple (SPCompU.lift (SPComp.pure a))
      (fun h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0))
      (fun _ h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0)) (OrderDual.toDual 0) := by
    vcgen
  exact le_antisymm ((SPCompU.triple_iff_wpE_le _ _ _).1 hup h₀)
    ((triple_iff_le_wpE _ _ _).1 hlo h₀)

set_option mvcgen.warning false in
/-- `prEventComp_loopGame` by `vcgen`: with `repeatStep step q` abstract, the lower-bound
and the upper-bound triple of `loopGame step q b₀` have the bad-event preexpectation of
`repeatStep step q` as precondition. -/
theorem prEventComp_loopGame_vcgen
    (step : SPComp Unit) (q : ℕ) (b₀ : Bool) (h₀ : Heap) (bad : Heap → Prop) :
    prEventComp (loopGame step q b₀) h₀ (fun _ h' => bad h') =
      prEventComp (repeatStep step q) h₀ (fun _ h' => bad h') := by
  classical
  rw [← wpE_indicator_eq_prEventComp, ← wpE_indicator_eq_prEventComp]
  have hrl : ∀ (post : PUnit → Heap → ℝ≥0∞) (e : ℝ≥0∞),
      Triple (repeatStep step q) (fun h => wpE (repeatStep step q) post h) post e :=
    fun _ _ => spec_wpE_lower _
  have hru : ∀ post : PUnit → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift (repeatStep step q))
      (fun h => OrderDual.toDual
        (wpE (repeatStep step q) (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE _
  have hlo : Triple (loopGame step q b₀)
      (fun h => wpE (repeatStep step q) (fun _ h' => if bad h' then (1 : ℝ≥0∞) else 0) h)
      (fun _ h => if bad h then (1 : ℝ≥0∞) else 0) Lean.Order.bot := by
    unfold loopGame
    vcgen [hrl]
    rename_i s
    simp only [leanOrder_rel_iff_le, wp_eq_wpEF]
    refine le_of_eq (congrArg (fun p => wpE (repeatStep step q) p s)
      (funext fun _ => funext fun h' => ?_))
    rw [wpEF_pure]
  have hup : Triple (SPCompU.lift (loopGame step q b₀))
      (fun h => OrderDual.toDual
        (wpE (repeatStep step q) (fun _ h' => if bad h' then (1 : ℝ≥0∞) else 0) h))
      (fun _ h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0))
      (OrderDual.toDual 0) := by
    unfold loopGame
    vcgen [hru]
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF_pure,
      le_refl]
  exact le_antisymm ((SPCompU.triple_iff_wpE_le _ _ _).1 hup h₀)
    ((triple_iff_le_wpE _ _ _).1 hlo h₀)

end CatCrypt.Unary

namespace CatCrypt.Crypto

open CatCrypt.Unary

set_option mvcgen.warning false in
/-- `prTrue_bind_sample_Bool` by `vcgen`: a lower-bound and an upper-bound triple, with
the continuation `A` abstract. `vcgen` stops at the average over `Bool`, which `tsum_bool`
evaluates. -/
theorem prTrue_bind_sample_Bool_vcgen (A : Bool → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample Bool) A) h₀ =
    (2 : ℝ≥0∞)⁻¹ * prTrue (A true) h₀ + (2 : ℝ≥0∞)⁻¹ * prTrue (A false) h₀ := by
  simp only [← wpE_indicator_eq_prTrue]
  have hlo : Triple (SPComp.bind (SPComp.sample Bool) A)
      (fun h => (2 : ℝ≥0∞)⁻¹ * wpE (A true) (fun b _ => if b then 1 else 0) h +
        (2 : ℝ≥0∞)⁻¹ * wpE (A false) (fun b _ => if b then 1 else 0) h)
      (fun b _ => if b then (1 : ℝ≥0∞) else 0) Lean.Order.bot := by
    vcgen
    simp only [leanOrder_rel_iff_le, wp_eq_wpEF, wpEF, tsum_bool, Fintype.card_bool,
      Nat.cast_ofNat, lean_order_bot_eq_zero, zero_mul, add_zero]
    exact le_of_eq (by ring)
  have hup : Triple (SPCompU.lift (SPComp.bind (SPComp.sample Bool) A))
      (fun h => OrderDual.toDual
        ((2 : ℝ≥0∞)⁻¹ * wpE (A true) (fun b _ => if b then 1 else 0) h +
        (2 : ℝ≥0∞)⁻¹ * wpE (A false) (fun b _ => if b then 1 else 0) h))
      (fun b _ => OrderDual.toDual (if b then (1 : ℝ≥0∞) else 0)) (OrderDual.toDual 0) := by
    vcgen
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF,
      zero_mul, add_zero, tsum_bool, Fintype.card_bool, Nat.cast_ofNat, mul_add]
    exact le_of_eq (by ring)
  exact le_antisymm ((SPCompU.triple_iff_wpE_le _ _ _).1 hup h₀)
    ((triple_iff_le_wpE _ _ _).1 hlo h₀)

end CatCrypt.Crypto

namespace CatCrypt.Crypto.BadEvent

open CatCrypt.Unary CatCrypt.Crypto

set_option mvcgen.warning false in
/-- `prTrue_pure_false_eq_zero` by `vcgen` on `SPCompU`. -/
theorem prTrue_pure_false_eq_zero_vcgen (h₀ : Heap) :
    prTrue (SPComp.pure false) h₀ = 0 := by
  rw [← wpE_indicator_eq_prTrue]
  have ht : Triple (SPCompU.lift (SPComp.pure false)) (fun _ => OrderDual.toDual 0)
      (fun b _ => OrderDual.toDual (if b then (1 : ℝ≥0∞) else 0)) (OrderDual.toDual 0) := by
    vcgen
    simp
  exact le_antisymm ((SPCompU.triple_iff_wpE_le _ _ _).1 ht h₀) zero_le

set_option mvcgen.warning false in
/-- `prTrue_union_bound_list` by `vcgen` on `SPCompU`. The recursion on the list is that
of the original; in the step case `vcgen` decomposes the `do` block of `bad_union`, with the
head event and the union of the tail abstract, and the verification condition uses the
purity of the union of the tail and the recursive bound. -/
theorem prTrue_union_bound_list_vcgen :
    (bads : List (SPComp Bool)) →
    (∀ b ∈ bads, SPComp.IsPure b) →
    (∀ b ∈ bads, SPComp.NoFail b) →
    prTrue (bad_union bads) Heap.empty ≤
    bads.foldr (fun b acc => prTrue b Heap.empty + acc) 0
  | [] => fun _ _ => (prTrue_pure_false_eq_zero_vcgen _).le
  | [b] => fun _ _ => le_of_eq (add_zero _).symm
  | b :: b' :: bs => fun hp hnf => by
    have ih := prTrue_union_bound_list_vcgen (b' :: bs)
      (fun x hx => hp x (List.mem_cons_of_mem b hx))
      (fun x hx => hnf x (List.mem_cons_of_mem b hx))
    obtain ⟨d, hd⟩ := (bad_union_isPure_noFail (b' :: bs)
      (fun x hx => hp x (List.mem_cons_of_mem b hx))
      (fun x hx => hnf x (List.mem_cons_of_mem b hx))).1
    show prTrue (do let b₁ ← b; let b₂ ← bad_union (b' :: bs); SPComp.pure (b₁ || b₂))
      Heap.empty ≤ prTrue b Heap.empty + _
    refine le_trans ?_ (add_le_add le_rfl ih)
    generalize bad_union (b' :: bs) = r at hd ⊢
    rw [← wpE_indicator_eq_prTrue, ← wpE_indicator_eq_prTrue, ← wpE_indicator_eq_prTrue]
    have hb : ∀ (c : SPComp Bool) (post : Bool → Heap → ℝ≥0∞ᵒᵈ),
        Triple (SPCompU.lift c)
        (fun h => OrderDual.toDual (wpE c (fun a h' => OrderDual.ofDual (post a h')) h))
        post (OrderDual.toDual 0) := fun c _ => SPCompU.spec_wpE c
    have ht : Triple
        (SPCompU.lift (do let b₁ ← b; let b₂ ← r; SPComp.pure (b₁ || b₂)))
        (fun h => OrderDual.toDual (wpE b (fun b _ => if b then 1 else 0) h +
          wpE r (fun b _ => if b then 1 else 0) Heap.empty))
        (fun b _ => OrderDual.toDual (if b then (1 : ℝ≥0∞) else 0))
        (OrderDual.toDual 0) := by
      vcgen [hb]
      rename_i s
      simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual]
      calc _ ≤ wpE b (fun b₁ _ => (if b₁ then 1 else 0) +
            wpE r (fun b _ => if b then (1 : ℝ≥0∞) else 0) Heap.empty) s := by
            refine wpE_mono b (fun b₁ h' => ?_) s
            simp only [SPCompU.wp_eq, OrderDual.ofDual_toDual, wpEF, zero_mul, add_zero]
            change wpE (SPComp.bind r fun b₂ => SPComp.pure (b₁ || b₂)) _ h' ≤ _
            rw [wpE_bind]
            cases b₁
            · simp only [wpE_pure, Bool.false_or, Bool.false_eq_true, ↓reduceIte, zero_add,
                wpE_indicator_eq_prTrue, prTrue_isPure_eq hd, le_refl]
            · simp only [wpE_pure, Bool.true_or, ↓reduceIte]
              exact le_add_right (wpE_const_le _ _ _)
        _ ≤ _ := by
            rw [wpE_add]
            exact add_le_add le_rfl (wpE_const_le _ _ _)
    exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht Heap.empty

end CatCrypt.Crypto.BadEvent

namespace CatCryptCore.Examples.DetCPA

open CatCrypt.Unary CatCrypt.Crypto

set_option mvcgen.warning false in
/-- `diff_msg_prTrue` by `vcgen` on `SPCompU`: the equality adversary returns `true` with
probability `0` on encryptions of `m` and `!m` under one key. -/
theorem diff_msg_prTrue_vcgen (m : Bool) :
    prTrue ((det_enc_pair xorDet m (!m)).bind eq_adversary) Heap.empty = 0 := by
  rw [← wpE_indicator_eq_prTrue]
  have ht : Triple (SPCompU.lift ((det_enc_pair xorDet m (!m)).bind eq_adversary))
      (fun _ => OrderDual.toDual 0)
      (fun b _ => OrderDual.toDual (if b then (1 : ℝ≥0∞) else 0)) (OrderDual.toDual 0) := by
    unfold det_enc_pair eq_adversary xorDet
    vcgen
    all_goals cases m <;> simp [SPCompU.wp_eq]
  exact le_antisymm ((SPCompU.triple_iff_wpE_le _ _ _).1 ht Heap.empty) zero_le

end CatCryptCore.Examples.DetCPA

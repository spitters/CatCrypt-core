/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Unary.ExpectationVCGen
import CatCryptCore.Unary.ExpectedCost
import CatCryptCore.Unary.QueryBound
import CatCryptCore.Crypto.BadEvent
import CatCryptCore.Crypto.ForkingLemma

set_option autoImplicit false

/-!
# `vcgen` proofs of expected-cost and probability bounds

Each theorem `foo_vcgen` restates an existing theorem `foo` and proves it with `vcgen`
on one of the two `WPMonad` instances of `CatCryptCore.Unary.ExpectationVCGen`, followed
by arithmetic on `wpE`. The statements are those of the originals; the originals are not
used in the proofs.

This file is not a `module`: `CatCryptCore.Unary.ExpectedCost` does not expose the
bodies of `ecost`, `CostComp.bind`, `compileCharged` and `retryN`, and the proofs unfold
them before calling `vcgen`.

## Main statements

* `spec_wpE_lower`: the lower-bound triple of an arbitrary computation.
* `ecost_bind_le_vcgen`, `ecost_bind_vcgen`: the tower law of `ecost`.
* `ecost_compileCharged_le_queryCost_vcgen`: the expected cost of a charged compilation is
  at most its query cost.
* `prBad_induction_vcgen`: the `q * ε` bound on the bad event after `q` steps, with a
  parametric invariant.
* `ecost_retryN_le_vcgen`: the truncated geometric-retry bound.
* `BadEvent.prTrue_union_bound_vcgen`: the union bound for two events.
* `ForkingLemma.prTrue_double_sample_pure_bool_vcgen`: the probability of a Boolean
  function of two independent uniform samples.
-/

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal
open Std.Internal.Do

namespace CatCrypt.Unary

/-- Every `SPComp` computation meets the lower-bound triple whose precondition is its
preexpectation. -/
theorem spec_wpE_lower {α : Type} (c : SPComp α) {post : α → Heap → ℝ≥0∞}
    {e : ℝ≥0∞} :
    Triple c (fun h => wpE c post h) post e :=
  ⟨fun _ => le_self_add⟩

set_option mvcgen.warning false in
/-- `ecost_bind_le` by `vcgen` on `SPCompU`, with `c` as an abstract sub-program
specified by `SPCompU.spec_wpE`. -/
theorem ecost_bind_le_vcgen {α β : Type} (c : CostComp α) (f : α → CostComp β) (h : Heap) :
    ecost (CostComp.bind c f) h ≤ ecost c h + wpE c (fun p h' => ecost (f p.1) h') h := by
  have hc : ∀ post : α × ℕ → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift c)
      (fun h => OrderDual.toDual (wpE c (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE c
  have ht : Triple (SPCompU.lift (CostComp.bind c f))
      (fun h => OrderDual.toDual (ecost c h + wpE c (fun p h' => ecost (f p.1) h') h))
      (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
    unfold CostComp.bind
    vcgen [hc]
    rename_i s
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF, zero_mul,
      add_zero, wpE_bind, wpE_pure, Nat.cast_add, wpE_add, ecost]
    exact add_le_add (wpE_mono c (fun p h' => wpE_const_le _ _ _) s) le_rfl
  exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h


set_option mvcgen.warning false in
/-- `ecost_bind` by `vcgen`: the upper bound is `ecost_bind_le_vcgen`, the lower bound is
a lower-bound triple on `SPComp`, using losslessness of the continuation. -/
theorem ecost_bind_vcgen {α β : Type} (c : CostComp α) (f : α → CostComp β)
    (hf : ∀ a, isLossless (f a)) (h : Heap) :
    ecost (CostComp.bind c f) h
      = ecost c h + wpE c (fun p h' => ecost (f p.1) h') h := by
  refine le_antisymm (ecost_bind_le_vcgen c f h) ?_
  have hc : ∀ (post : α × ℕ → Heap → ℝ≥0∞) (e : ℝ≥0∞),
      Triple (Prog := SPComp (α × ℕ)) c (fun h => wpE c post h) post e :=
    fun _ _ => spec_wpE_lower c
  have ht : Triple (Prog := SPComp (β × ℕ)) (CostComp.bind c f)
      (fun h => ecost c h + wpE c (fun p h' => ecost (f p.1) h') h)
      (fun r _ => (r.2 : ℝ≥0∞)) Lean.Order.bot := by
    unfold CostComp.bind
    vcgen [hc]
    rename_i s
    simp only [leanOrder_rel_iff_le, wp_bot_eq_wpE, ecost]
    rw [← wpE_add]
    refine le_of_eq (wpE_congr c (fun p h' => ?_) s)
    simp only [wpE_bind, wpE_pure, Nat.cast_add, wpE_add, wpE_const_of_lossless (hf p.1)]
  exact (triple_iff_le_wpE _ _ _).1 ht h

set_option mvcgen.warning false in
/-- `ecost_compileCharged_le_queryCost` by `vcgen` on `SPCompU`: induction on the tree,
with `vcgen` on the charged operation of each node and the subtrees as abstract
sub-programs. -/
theorem ecost_compileCharged_le_queryCost_vcgen {α : Type} (s : SPTree α) (h : Heap) :
    ecost (compileCharged s) h ≤ (s.queryCost : ℝ≥0∞) := by
  induction s generalizing h with
  | ret a => simp [compileCharged]
  | fail => simp [compileCharged]
  | sample β finβ neβ k ih =>
    let := finβ; let := neβ
    have hk : ∀ b (post : α × ℕ → Heap → ℝ≥0∞ᵒᵈ),
        Triple (SPCompU.lift (compileCharged (k b)))
        (fun h => OrderDual.toDual
          (wpE (compileCharged (k b)) (fun a h' => OrderDual.ofDual (post a h')) h))
        post (OrderDual.toDual 0) := fun b _ => SPCompU.spec_wpE _
    have ht : Triple (SPCompU.lift (compileCharged (.sample β finβ neβ k)))
        (fun _ => OrderDual.toDual ((SPTree.sample β finβ neβ k).queryCost : ℝ≥0∞))
        (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
      simp only [compileCharged, CostComp.bind, CostComp.sampleC, CostComp.lift]
      vcgen [hk]
      rename_i s
      simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF, zero_mul,
        add_zero, wpE_pure, wpE_bind, Nat.cast_add, Nat.cast_one, wpE_add]
      calc _ ≤ (Fintype.card β : ℝ≥0∞)⁻¹ * ∑' _ : β,
            (1 + ((Finset.univ.sup fun b => (k b).queryCost : ℕ) : ℝ≥0∞)) := by
            gcongr _ * ∑' a, ?_
            exact add_le_add (wpE_const_le _ _ _) ((ih a s).trans (Nat.cast_le.mpr
              (Finset.le_sup (f := fun b => (k b).queryCost) (Finset.mem_univ a))))
        _ = _ := by
            rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
              ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
            show _ = ((1 + Finset.univ.sup fun b => (k b).queryCost : ℕ) : ℝ≥0∞)
            push_cast; rfl
    exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h
  | get l k ih =>
    have hk : ∀ v (post : α × ℕ → Heap → ℝ≥0∞ᵒᵈ),
        Triple (SPCompU.lift (compileCharged (k v)))
        (fun h => OrderDual.toDual
          (wpE (compileCharged (k v)) (fun a h' => OrderDual.ofDual (post a h')) h))
        post (OrderDual.toDual 0) := fun v _ => SPCompU.spec_wpE _
    have ht : Triple (SPCompU.lift (compileCharged (.get l k)))
        (fun _ => OrderDual.toDual ((SPTree.get l k).queryCost : ℝ≥0∞))
        (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
      simp only [compileCharged, CostComp.bind, CostComp.getC, CostComp.lift]
      vcgen [hk]
      rename_i s
      simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF, zero_mul,
        add_zero, wpE_pure, Nat.cast_add, Nat.cast_one, wpE_add]
      refine (add_le_add (wpE_const_le _ _ _) ((ih _ s).trans (Nat.cast_le.mpr
        (Finset.le_sup (f := fun v => (k v).queryCost) (Finset.mem_univ _))))).trans ?_
      show _ ≤ ((1 + Finset.univ.sup fun v => (k v).queryCost : ℕ) : ℝ≥0∞)
      push_cast; exact le_rfl
    exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h
  | set l v t ih =>
    have hk : ∀ (post : α × ℕ → Heap → ℝ≥0∞ᵒᵈ),
        Triple (SPCompU.lift (compileCharged t))
        (fun h => OrderDual.toDual
          (wpE (compileCharged t) (fun a h' => OrderDual.ofDual (post a h')) h))
        post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE _
    have ht : Triple (SPCompU.lift (compileCharged (.set l v t)))
        (fun _ => OrderDual.toDual ((SPTree.set l v t).queryCost : ℝ≥0∞))
        (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
      simp only [compileCharged, CostComp.bind, CostComp.setC, CostComp.lift]
      vcgen [hk]
      rename_i s
      simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF, zero_mul,
        add_zero, wpE_pure, Nat.cast_add, Nat.cast_one, wpE_add]
      refine (add_le_add (wpE_const_le _ _ _) (ih _)).trans ?_
      show _ ≤ ((1 + t.queryCost : ℕ) : ℝ≥0∞)
      push_cast; exact le_rfl
    exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h

set_option mvcgen.warning false in
/-- `prBad_induction` by `vcgen` on `SPCompU`. `repeatStep` is structural recursion, not a
`forIn` loop, so `vcgen` has no loop to attach an invariant to; the induction on the
iteration count is outside `vcgen`. The invariant is the family of upper-bound triples
`⦃[bad] + (n * ε + c)⦄ repeatStep step n ⦃[bad] + c⦄`, indexed by `c`; in the step case
`vcgen` composes the instance at `ε + c` with the step triple at `c`, and the remaining
verification condition is `(n + 1) * ε + c = n * ε + (ε + c)`. -/
theorem prBad_induction_vcgen
    (step : SPComp Unit) (h₀ : Heap) (bad : Heap → Prop) (ε : ℝ≥0∞)
    (h_start : ¬ bad h₀)
    (h_fresh : ∀ h₁ : Heap, ¬ bad h₁ →
      prEvent (step h₁) (fun _ h' => bad h') ≤ ε)
    (q : ℕ) :
    prEventComp (repeatStep step q) h₀ (fun _ h' => bad h') ≤ q * ε := by
  classical
  have hstep : ∀ c : ℝ≥0∞, Triple (SPCompU.lift (α := PUnit) step)
      (fun h => OrderDual.toDual ((if bad h then 1 else 0) + (ε + c)))
      (fun (_ : PUnit) h => OrderDual.toDual ((if bad h then (1 : ℝ≥0∞) else 0) + c))
      (OrderDual.toDual 0) := by
    intro c
    refine (SPCompU.triple_iff_wpE_le _ _ _).2 fun h => ?_
    rw [wpE_add, ← add_assoc]
    refine add_le_add ?_ (wpE_const_le _ _ _)
    rw [wpE_indicator_eq_prEventComp]
    by_cases hb : bad h
    · simpa [hb, prEventComp] using
        ((prEvent_le_mass _ _).trans (sdistr_mass_le_one _)).trans
          (le_self_add : (1 : ℝ≥0∞) ≤ 1 + ε)
    · simp_all [prEventComp]
  have hinv : ∀ (n : ℕ) (c : ℝ≥0∞),
      Triple (SPCompU.lift (α := PUnit) (repeatStep step n))
      (fun h => OrderDual.toDual ((if bad h then 1 else 0) + (n * ε + c)))
      (fun (_ : PUnit) h => OrderDual.toDual ((if bad h then (1 : ℝ≥0∞) else 0) + c))
      (OrderDual.toDual 0) := by
    intro n
    induction n with
    | zero =>
      intro c
      simp only [repeatStep]
      vcgen
      simp_all
    | succ n ih =>
      intro c
      have hr := ih (ε + c)
      have hs := hstep c
      have key : Triple (SPCompU.lift (α := PUnit)
          (SPComp.bind (α := PUnit) (β := PUnit) (repeatStep step n) fun _ => step))
          (fun h => OrderDual.toDual
            ((if bad h then 1 else 0) + (((n + 1 : ℕ) : ℝ≥0∞) * ε + c)))
          (fun (_ : PUnit) h => OrderDual.toDual ((if bad h then (1 : ℝ≥0∞) else 0) + c))
          (OrderDual.toDual 0) := by
        vcgen [hr, hs]
        simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual]
        apply le_of_eq
        push_cast
        grind
      exact key
  have := (SPCompU.triple_iff_wpE_le _ _ _).1 (hinv q 0) h₀
  simp_all [wpE_indicator_eq_prEventComp]

set_option mvcgen.warning false in
/-- `ecost_retryN_le` by `vcgen` on `SPCompU`. `retryN` is structural recursion, so the
induction on the retry budget is outside `vcgen`. The body is an abstract sub-program and
its post-expectation depends on the cost accumulated so far, so no triple of the body
with a fixed post-expectation matches syntactically; the verification condition stays
under `wpE body` and is closed with `wpE_mono`, `wpE_add`, `wpE_const_mul` and the
hypotheses. -/
theorem ecost_retryN_le_vcgen {β : Type} (body : CostComp (Option β)) {C q : ℝ≥0∞}
    (hC : ∀ h, ecost body h ≤ C) (hq : ∀ h, failProb body h ≤ q) :
    ∀ (n : ℕ) (h : Heap),
      ecost (retryN body n) h ≤ C * ∑ i ∈ Finset.range n, q ^ i := by
  have hb : ∀ post : Option β × ℕ → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift body)
      (fun h => OrderDual.toDual (wpE body (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE body
  intro n
  induction n with
  | zero => intro h; simp [retryN]
  | succ n ih =>
    intro h
    have ht : Triple (SPCompU.lift (retryN body (n + 1)))
        (fun _ => OrderDual.toDual (C * ∑ i ∈ Finset.range (n + 1), q ^ i))
        (fun r _ => OrderDual.toDual (r.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
      simp only [retryN, CostComp.bind]
      vcgen [hb]
      rename_i s
      simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual]
      calc _ ≤ wpE body (fun p _ => (p.2 : ℝ≥0∞) +
            (C * ∑ i ∈ Finset.range n, q ^ i) * (p.1.elim 1 fun _ => 0)) s := by
            refine wpE_mono body (fun p h' => ?_) s
            rcases p with ⟨r, m⟩
            simp only [SPCompU.wp_eq, OrderDual.ofDual_toDual, wpEF, zero_mul, add_zero,
              wpE_bind, wpE_pure, Nat.cast_add, wpE_add]
            cases r with
            | none => exact (add_le_add (wpE_const_le _ _ _) (ih h')).trans_eq (by simp)
            | some b => simp [CostComp.pure]
        _ = ecost body s + (C * ∑ i ∈ Finset.range n, q ^ i) * failProb body s := by
            rw [wpE_add, wpE_const_mul]; rfl
        _ ≤ C + (C * ∑ i ∈ Finset.range n, q ^ i) * q :=
            add_le_add (hC s) (mul_le_mul' le_rfl (hq s))
        _ = C * ∑ i ∈ Finset.range (n + 1), q ^ i := by rw [geom_sum_succ]; ring
    exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht h

end CatCrypt.Unary

namespace CatCrypt.Crypto.BadEvent

open CatCrypt.Unary CatCrypt.Crypto

set_option mvcgen.warning false in
/-- `prTrue_union_bound` by `vcgen` on `SPCompU`. The proof uses only the purity of `bad₂`;
the purity of `bad₁` and the two `NoFail` hypotheses are kept so that the statement is
that of the original. -/
theorem prTrue_union_bound_vcgen (bad₁ bad₂ : SPComp Bool)
    (_hp₁ : SPComp.IsPure bad₁) (hp₂ : SPComp.IsPure bad₂)
    (_hnf₁ : SPComp.NoFail bad₁) (_hnf₂ : SPComp.NoFail bad₂) :
    prTrue (do let b₁ ← bad₁; let b₂ ← bad₂; SPComp.pure (b₁ || b₂)) Heap.empty
    ≤ prTrue bad₁ Heap.empty + prTrue bad₂ Heap.empty := by
  obtain ⟨d₂, hd₂⟩ := hp₂
  rw [← wpE_indicator_eq_prTrue, ← wpE_indicator_eq_prTrue, ← wpE_indicator_eq_prTrue]
  have hb : ∀ (c : SPComp Bool) (post : Bool → Heap → ℝ≥0∞ᵒᵈ),
      Triple (SPCompU.lift c)
      (fun h => OrderDual.toDual (wpE c (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun c _ => SPCompU.spec_wpE c
  have ht : Triple
      (SPCompU.lift (do let b₁ ← bad₁; let b₂ ← bad₂; SPComp.pure (b₁ || b₂)))
      (fun h => OrderDual.toDual (wpE bad₁ (fun b _ => if b then 1 else 0) h +
        wpE bad₂ (fun b _ => if b then 1 else 0) Heap.empty))
      (fun b _ => OrderDual.toDual (if b then (1 : ℝ≥0∞) else 0)) (OrderDual.toDual 0) := by
    vcgen [hb]
    rename_i s
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual]
    calc _ ≤ wpE bad₁ (fun b _ => (if b then 1 else 0) +
          wpE bad₂ (fun b _ => if b then (1 : ℝ≥0∞) else 0) Heap.empty) s := by
          refine wpE_mono bad₁ (fun b h' => ?_) s
          simp only [SPCompU.wp_eq, OrderDual.ofDual_toDual, wpEF, zero_mul, add_zero]
          change wpE (SPComp.bind bad₂ fun b₂ => SPComp.pure (b || b₂)) _ h' ≤ _
          rw [wpE_bind]
          cases b
          · simp_all [wpE_pure, wpE_indicator_eq_prTrue, prTrue_isPure_eq hd₂]
          · simp only [wpE_pure, Bool.true_or, ↓reduceIte]
            simp_all [le_add_right, wpE_const_le]
      _ ≤ _ := by
          rw [wpE_add]
          exact add_le_add le_rfl (wpE_const_le _ _ _)
  exact (SPCompU.triple_iff_wpE_le _ _ _).1 ht Heap.empty

end CatCrypt.Crypto.BadEvent

namespace CatCrypt.Crypto.ForkingLemma

open CatCrypt.Unary CatCrypt.Crypto

set_option mvcgen.warning false in
/-- `prTrue_double_sample_pure_bool` by `vcgen`: the lower-bound and upper-bound triples
reduce to the same counting identity. -/
theorem prTrue_double_sample_pure_bool_vcgen {R : Type} [Fintype R] [Nonempty R]
    (f : R → R → Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample R) fun e₁ =>
      SPComp.bind (SPComp.sample R) fun e₂ =>
        SPComp.pure (f e₁ e₂)) h₀ =
    ((Finset.univ ×ˢ Finset.univ).filter (fun p : R × R => f p.1 p.2)).card /
      (Fintype.card R : ℝ≥0∞) ^ 2 := by
  rw [← wpE_indicator_eq_prTrue]
  have harith : (Fintype.card R : ℝ≥0∞)⁻¹ *
      ∑' e₁ : R, (Fintype.card R : ℝ≥0∞)⁻¹ *
      ∑' e₂ : R, (if f e₁ e₂ then (1 : ℝ≥0∞) else 0) =
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : R × R => f p.1 p.2)).card /
      (Fintype.card R : ℝ≥0∞) ^ 2 := by
    rw [sq, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), Finset.card_filter,
      Finset.sum_product]
    simp_all [tsum_fintype, Finset.mul_sum, Nat.cast_sum, mul_assoc]
  have hlo : Triple (SPComp.bind (SPComp.sample R) fun e₁ =>
      SPComp.bind (SPComp.sample R) fun e₂ => SPComp.pure (f e₁ e₂))
      (fun _ => ((Finset.univ ×ˢ Finset.univ).filter (fun p : R × R => f p.1 p.2)).card /
        (Fintype.card R : ℝ≥0∞) ^ 2)
      (fun b _ => if b then (1 : ℝ≥0∞) else 0) Lean.Order.bot := by
    vcgen
    simp only [leanOrder_rel_iff_le, wp_eq_wpEF, wpEF_bind, wpEF_sample, wpEF_pure]
    simp_all
  have hup : Triple (SPCompU.lift (SPComp.bind (SPComp.sample R) fun e₁ =>
      SPComp.bind (SPComp.sample R) fun e₂ => SPComp.pure (f e₁ e₂)))
      (fun _ => OrderDual.toDual
        (((Finset.univ ×ˢ Finset.univ).filter (fun p : R × R => f p.1 p.2)).card /
        (Fintype.card R : ℝ≥0∞) ^ 2))
      (fun b _ => OrderDual.toDual (if b then (1 : ℝ≥0∞) else 0)) (OrderDual.toDual 0) := by
    vcgen
    simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, SPCompU.wp_eq, wpEF_bind,
      wpEF_sample, wpEF_pure]
    simp_all
  exact le_antisymm ((SPCompU.triple_iff_wpE_le _ _ _).1 hup h₀)
    ((triple_iff_le_wpE _ _ _).1 hlo h₀)

end CatCrypt.Crypto.ForkingLemma

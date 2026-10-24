/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Unary.ExpectationVCGen
import all CatCryptCore.Unary.ExpectedCost
public import CatCryptCore.Unary.QueryBound

@[expose] public section
set_option autoImplicit false

/-!
# `vcgen` loop invariants for `repeatStep` and `retryN`

`repeatStep` and `retryN` are defined by structural recursion, so `vcgen` has no loop to
attach an invariant to. This module writes each of them as a `forIn` loop over
`List.range n` in `SPCompU` (equation lemmas `forIn_eq_repeatStep`, `forIn_retryStep_eq`)
and proves `prBad_induction` and `ecost_retryN_le` again with `vcgen ... invariants`, which
uses the `Spec.forIn_list` rule of `Std.WP`. The induction on the number of
iterations is inside that rule; the proofs below contain no induction on `n`.

The module imports `CatCryptCore.Unary.ExpectedCost` with `import all` because that module
does not expose the bodies of `ecost`, `CostComp.bind` and `retryN`.

## Main statements

* `forIn_eq_repeatStep`, `forIn_retryStep_eq`: the `forIn` presentations.
* `prBad_induction_forIn_vcgen`: `prBad_induction` with the invariant
  `[bad h] + (remaining iterations) * ε`.
* `ecost_retryN_le_forIn_vcgen`: `ecost_retryN_le` with the invariant
  `(accumulated cost) + C * ∑_{i < remaining rounds} q^i`.
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob Std.WP
open scoped ENNReal

/-- The upper-bound weakest precondition of `pure`. -/
@[simp] theorem SPCompU.wp_pure {α : Type} (x : α) (post : α → Heap → ℝ≥0∞ᵒᵈ)
    (e : ℝ≥0∞ᵒᵈ) (h : Heap) : wp (pure x : SPCompU α) post e h = post x h :=
  (SPCompU.wp_eq (SPComp.pure x) post e h).trans (by rw [wpEF_pure]; rfl)


/-- The last iteration of `repeatStep` can be moved to the front. -/
theorem repeatStep_succ_eq_bind (step : SPComp Unit) (n : ℕ) :
    (repeatStep step n).bind (fun _ => step) = step.bind (fun _ => repeatStep step n) := by
  induction n with
  | zero =>
    show (SPComp.pure ()).bind (fun _ => step) = step.bind (fun _ => SPComp.pure ())
    rw [SPComp.pure_bind, SPComp.bind_pure]
  | succ n ih =>
    show ((repeatStep step n).bind fun _ => step).bind (fun _ => step)
      = step.bind (fun _ => (repeatStep step n).bind fun _ => step)
    rw [ih, SPComp.bind_assoc]
    simp only [ih]

/-- `repeatStep step xs.length` as a `for` loop over `xs` in `SPCompU`. -/
theorem forIn_eq_repeatStep (step : SPComp Unit) (xs : List ℕ) :
    forIn (m := SPCompU) xs PUnit.unit
      (fun _ _ => SPCompU.lift step >>= fun _ => pure (ForInStep.yield PUnit.unit))
      = repeatStep step xs.length := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.forIn_cons, bind_assoc, pure_bind, ih]
    exact (repeatStep_succ_eq_bind step as.length).symm

set_option mvcgen.warning false in
/-- `prBad_induction` by `vcgen` with a loop invariant: the loop is presented as `forIn`
over `List.range q` (`repeatStep_eq_forIn`), and the invariant at a cursor with `n`
remaining iterations is the bad-event indicator plus `n * ε`. -/
theorem prBad_induction_forIn_vcgen
    (step : SPComp Unit) (h₀ : Heap) (bad : Heap → Prop) (ε : ℝ≥0∞)
    (h_start : ¬ bad h₀)
    (h_fresh : ∀ h₁ : Heap, ¬ bad h₁ →
      prEvent (step h₁) (fun _ h' => bad h') ≤ ε)
    (q : ℕ) :
    prEventComp (repeatStep step q) h₀ (fun _ h' => bad h') ≤ q * ε := by
  classical
  have hs : ∀ post : Unit → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift step)
      (fun h => OrderDual.toDual (wpE step (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE step
  have ht : Triple (forIn (m := SPCompU) (List.range q) PUnit.unit
        (fun _ _ => SPCompU.lift step >>= fun _ => pure (ForInStep.yield PUnit.unit)))
      (fun h => OrderDual.toDual ((if bad h then 1 else 0) + q * ε))
      (fun _ h => OrderDual.toDual (if bad h then (1 : ℝ≥0∞) else 0)) (OrderDual.toDual 0) := by
    vcgen [hs] invariants
    · fun _ suff _ h => OrderDual.toDual ((if bad h then (1 : ℝ≥0∞) else 0) + suff.length * ε)
    case vc1 => simp_all
    case vc2 => simp_all
    case vc3 s =>
      simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, binderNameHint,
        SPCompU.wp_pure, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [wpE_add step (fun _ h' => if bad h' then 1 else 0) (fun _ _ => _)]
      have h1 : wpE step (fun _ h' => if bad h' then (1 : ℝ≥0∞) else 0) s
          ≤ (if bad s then 1 else 0) + ε := by
        by_cases hb : bad s
        · simp only [hb, ite_true]
          exact ((wpE_mono step (fun _ _ => by split_ifs <;> simp) s).trans
            (wpE_const_le step 1 s)).trans le_self_add
        · simp_all [wpE_indicator_eq_prEventComp, prEventComp]
      calc _ ≤ ((if bad s then 1 else 0) + ε) + _ := add_le_add h1 (wpE_const_le _ _ _)
        _ = _ := by grind
  rw [← wpE_indicator_eq_prEventComp, ← List.length_range (n := q), ← forIn_eq_repeatStep,
    List.length_range]
  refine ((SPCompU.triple_iff_wpE_le _ _ _).1 ht h₀).trans ?_
  simp_all

/-- One round of the retry loop as the body of a `for` loop in `SPComp`: the accumulator
holds the result so far and the accumulated cost; a `some` result ends the loop. -/
noncomputable def retryStep {β : Type} (body : CostComp (Option β)) (_ : ℕ)
    (acc : Option β × ℕ) : SPComp (ForInStep (Option β × ℕ)) :=
  SPComp.bind body fun r =>
    match r.1 with
    | some b => SPComp.pure (ForInStep.done (some b, acc.2 + r.2))
    | none => SPComp.pure (ForInStep.yield (none, acc.2 + r.2))

/-- `retryStep` written in `SPCompU`, the form `vcgen` decomposes. -/
noncomputable def retryStepU {β : Type} (body : CostComp (Option β)) (_ : ℕ)
    (acc : Option β × ℕ) : SPCompU (ForInStep (Option β × ℕ)) :=
  SPCompU.lift body >>= fun r =>
    match r.1 with
    | some b => pure (ForInStep.done (some b, acc.2 + r.2))
    | none => pure (ForInStep.yield (none, acc.2 + r.2))

/-- `retryN body xs.length`, with initial cost `k` added, as a `for` loop over `xs`. -/
theorem forIn_retryStep_eq {β : Type} (body : CostComp (Option β)) (xs : List ℕ) (k : ℕ) :
    forIn (m := SPComp) xs ((none : Option β), k) (retryStep body)
      = SPComp.bind (retryN body xs.length) fun p => SPComp.pure (p.1, k + p.2) := by
  induction xs generalizing k with
  | nil =>
    show SPComp.pure ((none : Option β), k) = SPComp.bind (SPComp.pure (none, 0)) _
    rw [SPComp.pure_bind, add_zero]
  | cons a as ih =>
    simp only [List.forIn_cons, retryStep, List.length_cons, retryN, CostComp.bind,
      SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc]
    refine congrArg (SPComp.bind body) (funext fun r => ?_)
    rcases r with ⟨_ | b, m⟩
    · simp only [SPComp.pure_bind, ih, Nat.add_assoc]
    · simp only [CostComp.pure, SPComp.pure_bind, add_zero]

set_option mvcgen.warning false in
/-- `ecost_retryN_le` by `vcgen` with a loop invariant: the loop is presented as `forIn`
over `List.range n` with the accumulated cost in the loop state (`forIn_retryStep_eq`), and
the invariant at a cursor with `m` remaining rounds and accumulated cost `k` is
`k + C * ∑_{i<m} q^i`. -/
theorem ecost_retryN_le_forIn_vcgen {β : Type} (body : CostComp (Option β)) {C q : ℝ≥0∞}
    (hC : ∀ h, ecost body h ≤ C) (hq : ∀ h, failProb body h ≤ q) :
    ∀ (n : ℕ) (h : Heap),
      ecost (retryN body n) h ≤ C * ∑ i ∈ Finset.range n, q ^ i := by
  intro n h
  have hb : ∀ post : Option β × ℕ → Heap → ℝ≥0∞ᵒᵈ, Triple (SPCompU.lift body)
      (fun h => OrderDual.toDual (wpE body (fun a h' => OrderDual.ofDual (post a h')) h))
      post (OrderDual.toDual 0) := fun _ => SPCompU.spec_wpE body
  have ht : Triple (forIn (m := SPCompU) (List.range n) ((none : Option β), 0) (retryStepU body))
      (fun _ => OrderDual.toDual (C * ∑ i ∈ Finset.range n, q ^ i))
      (fun p _ => OrderDual.toDual (p.2 : ℝ≥0∞)) (OrderDual.toDual 0) := by
    unfold retryStepU
    vcgen [hb] invariants
    · fun _ suff acc _ => OrderDual.toDual
        ((acc.2 : ℝ≥0∞) + C * ∑ i ∈ Finset.range suff.length, q ^ i)
    case vc1 => simp
    case vc2 => simp
    case vc3 pref cur suff hxs _ k s =>
      simp only [leanOrder_rel_dual_iff, OrderDual.ofDual_toDual, List.length_cons]
      set D := C * ∑ i ∈ Finset.range suff.length, q ^ i
      refine (wpE_mono body (post' := fun a _ =>
        ((k : ℝ≥0∞) + a.2) + D * (a.1.elim 1 fun _ => 0)) (fun a _ => ?_) s).trans ?_
      · rcases a with ⟨_ | x, m⟩ <;> simp [D]
      calc _ = wpE body (fun _ _ => (k : ℝ≥0∞)) s + ecost body s + D * failProb body s := by
            rw [wpE_add body (fun a _ => (k : ℝ≥0∞) + a.2) (fun a _ => D * a.1.elim 1 fun _ => 0),
              wpE_add body (fun _ _ => (k : ℝ≥0∞)) (fun a _ => (a.2 : ℝ≥0∞)), wpE_const_mul]
            rfl
        _ ≤ k + C + D * q :=
            add_le_add (add_le_add (wpE_const_le _ _ _) (hC s)) (mul_le_mul' le_rfl (hq s))
        _ = _ := by rw [geom_sum_succ]; ring
  have hfor : forIn (m := SPCompU) (List.range n) ((none : Option β), 0) (retryStepU body)
      = forIn (m := SPComp) (List.range n) ((none : Option β), 0) (retryStep body) := rfl
  have he := (SPCompU.triple_iff_wpE_le _ _ _).1 ht h
  rw [hfor, forIn_retryStep_eq, wpE_bind] at he
  simpa [List.length_range, ecost] using he

end CatCrypt.Unary

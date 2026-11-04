/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCCascade
public import CatCryptCore.Crypto.UCCoupling

/-!
# Deferred sampling in runs of systems, mixtures of runs, and the cascade over a context

**Deferred sampling.** Let `Y v` be a family of systems indexed by the outcome `v` of a
computation `c` that neither touches the heap nor fails, and `Yc` a system. Suppose that, on a
set of states closed under the steps (an invariant), the systems agree with `Yc` at every
event except the *use* of `v`, which happens once: before it, the steps of `Y v` are the steps
of `Yc`; at it, the step of `Yc` is the step of `Y v` averaged over `c`; after it (in the states
of `post`, which the steps of `Yc` keep), the steps agree again. Then the run of `Yc` is the run
of `Y v` averaged over `c` drawn before the run (`loop_deferred`, `run_deferred`,
`view_deferred`): the draw of `c` moves from the activation that uses it to the start of the
run. This is the eager–lazy exchange for one value in the runs of reactive systems.

**Mixtures.** For a computation `c` that does not fail, the distance between two averages over
`c` is at most the average over `c` of a bound of the pointwise distances
(`absDiff_prTrue_bind_le_bind`).

**Reductions with a given heap.** `SPComp.atHeap h c` runs `c` from the heap `h` whatever the
current heap. For a computation `c` that does not touch the heap, the acceptance probability
of `c` followed by `f` from the heap `h` is the acceptance probability, from the empty heap, of
`c` followed by `f` run from `h` (`prTrue_bind_atHeap`); hence the distance between two such
games at an environment is an advantage `AdvantageA` of an explicit distinguisher
(`absDiff_prTrue_bind_eq_advantageA`).

**Counters.** A system whose steps raise a counter by at most one never exceeds `n` in a run of
at most `n` activations from the counter `0` (`prBad_counter_eq_zero`).

**The cascade over a context.** If `Y` realizes `Y'` for the environments reduced through the
context of `X` with bound `b`, then `X.seq Y` realizes `X.seq Y'` with bound `b`
(`realizes_seq_right_ctx`): the hypothesis quantifies only over the environments that reach `Y`
through `X`, for instance environments in which the events of `Y` are outputs of an ideal
functionality.

## Main definitions

* `SPComp.atHeap`: a computation run from a given heap.
* `RealizesThrough`: realization for the environments reduced through the context of `X`.

## Main results

* `bind_const_of_isPure`: a computation that neither touches the heap nor fails, followed by a
  constant continuation, is the continuation.
* `loop_deferred`, `run_deferred`, `view_deferred`: deferred sampling in runs.
* `absDiff_prTrue_bind_le_bind`: the distance between mixtures.
* `prTrue_bind_atHeap`, `absDiff_prTrue_bind_eq_advantageA`: reductions with a given heap.
* `prBad_counter_eq_zero`: a counter bounded by the number of activations.
* `realizes_seq_right_ctx`, `realizesThrough_seq`: the cascade over a context.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Constant continuations -/

/-- A computation that neither touches the heap nor fails, followed by a constant
continuation, is the continuation. -/
theorem bind_const_of_isPure {α β : Type} {c : SPComp α} (hc : SPComp.IsPure c)
    (hn : SPComp.NoFail c) (X : SPComp β) : SPComp.bind c (fun _ => X) = X := by
  obtain ⟨d, hd⟩ := hc
  have hdn : d none = 0 := by
    have h := hn Heap.empty
    rw [hd Heap.empty] at h
    simp only [SDistr.bind, PMF.bind_apply, ENNReal.tsum_eq_zero, mul_eq_zero] at h
    rcases h none with h1 | h1
    · exact h1
    · simp [SDistr.fail] at h1
  have hm : SDistr.mass d = 1 := by simp [SDistr.mass, hdn]
  funext h
  simp only [SPComp.bind_def, hd h, SDistr.bind_assoc, SDistr.pure_bind]
  exact SDistr.bind_const_mass_one hm (X h)

/-! ## Deferred sampling -/

section Deferred

variable {α τ ζ E O : Type}

/-- After the use, the runs of the members of the family are the run of `Yc`. -/
theorem loop_deferred_post (Y : α → Sys τ E O) (Yc : Sys τ E O) (Inv post : τ → Prop)
    (hinv : ∀ t e q, Inv t → IsOutcome (Yc.step t e) q → Inv q.1)
    (hpost : ∀ v t e, Inv t → post t → (Y v).step t e = Yc.step t e)
    (hmono : ∀ t e q, Inv t → post t → IsOutcome (Yc.step t e) q → post q.1)
    (bad : τ → Bool) (Z : Strat ζ E O) :
    ∀ (n : ℕ) (z : ζ) (t : τ) (b : Bool) (v : α), Inv t → post t →
      loop (Y v) bad Z n (z, t, b) = loop Yc bad Z n (z, t, b) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _; rfl
  | succ n ih =>
    intro z t b v hi hp
    simp only [loop]
    congr 1; funext a
    rw [hpost v t a.2 hi hp]
    refine bind_congr_isOutcome fun q hq => ?_
    congr 1; funext z'
    exact ih _ _ _ _ (hinv t a.2 q hi hq) (hmono t a.2 q hi hp hq)

/-- **Deferred sampling in runs.** Under the hypotheses of the module docstring, from a state
of the invariant before the use, the run of `Yc` is the run of `Y v` averaged over `v` drawn
from `c` before the run. -/
theorem loop_deferred (c : SPComp α) (hc : SPComp.IsPure c) (hcn : SPComp.NoFail c)
    (Y : α → Sys τ E O) (Yc : Sys τ E O) (Inv post : τ → Prop) (use : τ → E → Prop)
    (hinv : ∀ t e q, Inv t → IsOutcome (Yc.step t e) q → Inv q.1)
    (hinvY : ∀ v t e q, Inv t → IsOutcome ((Y v).step t e) q → Inv q.1)
    (hpost : ∀ v t e, Inv t → post t → (Y v).step t e = Yc.step t e)
    (hmono : ∀ t e q, Inv t → post t → IsOutcome (Yc.step t e) q → post q.1)
    (hfree : ∀ v t e, Inv t → ¬ post t → ¬ use t e → (Y v).step t e = Yc.step t e)
    (huse : ∀ t e, Inv t → ¬ post t → use t e →
      Yc.step t e = SPComp.bind c fun v => (Y v).step t e)
    (hused : ∀ v t e q, Inv t → ¬ post t → use t e → IsOutcome ((Y v).step t e) q → post q.1)
    (bad : τ → Bool) (Z : Strat ζ E O) :
    ∀ (n : ℕ) (z : ζ) (t : τ) (b : Bool), Inv t → ¬ post t →
      SPComp.bind c (fun v => loop (Y v) bad Z n (z, t, b)) = loop Yc bad Z n (z, t, b) := by
  have hP := loop_deferred_post Y Yc Inv post hinv hpost hmono bad Z
  intro n
  induction n with
  | zero => intro z t b _ _; exact bind_const_of_isPure hc hcn _
  | succ n ih =>
    intro z t b hi hp
    simp only [loop]
    rw [SPComp.isPure_bind_comm_left c (Z.next z) _ hc]
    congr 1; funext a
    by_cases hu : use t a.2
    · rw [huse t a.2 hi hp hu, SPComp.bind_assoc]
      congr 1; funext v
      refine bind_congr_isOutcome fun q hq => ?_
      congr 1; funext z'
      exact hP _ _ _ _ v (hinvY v t a.2 q hi hq) (hused v t a.2 q hi hp hu hq)
    · simp only [hfree _ t a.2 hi hp hu]
      rw [SPComp.isPure_bind_comm_left c (Yc.step t a.2) _ hc]
      refine bind_congr_isOutcome fun q hq => ?_
      rw [SPComp.isPure_bind_comm_left c (Z.obs a.1 q.2) _ hc]
      congr 1; funext z'
      by_cases hq' : post q.1
      · simp only [hP _ _ _ _ _ (hinv t a.2 q hi hq) hq']
        exact bind_const_of_isPure hc hcn _
      · exact ih _ _ _ (hinv t a.2 q hi hq) hq'

/-- **Deferred sampling for flagged runs**: the full run of `Yc` is the full run of `Y v`
averaged over `c`, when every member starts in the initial state of `Yc`, which lies in the
invariant before the use. -/
theorem run_deferred (c : SPComp α) (hc : SPComp.IsPure c) (hcn : SPComp.NoFail c)
    (Y : α → Sys τ E O) (Yc : Sys τ E O) (Inv post : τ → Prop) (use : τ → E → Prop)
    (hinit : ∀ v, (Y v).init = Yc.init) (hi0 : Inv Yc.init) (hp0 : ¬ post Yc.init)
    (hinv : ∀ t e q, Inv t → IsOutcome (Yc.step t e) q → Inv q.1)
    (hinvY : ∀ v t e q, Inv t → IsOutcome ((Y v).step t e) q → Inv q.1)
    (hpost : ∀ v t e, Inv t → post t → (Y v).step t e = Yc.step t e)
    (hmono : ∀ t e q, Inv t → post t → IsOutcome (Yc.step t e) q → post q.1)
    (hfree : ∀ v t e, Inv t → ¬ post t → ¬ use t e → (Y v).step t e = Yc.step t e)
    (huse : ∀ t e, Inv t → ¬ post t → use t e →
      Yc.step t e = SPComp.bind c fun v => (Y v).step t e)
    (hused : ∀ v t e q, Inv t → ¬ post t → use t e → IsOutcome ((Y v).step t e) q → post q.1)
    (bad : τ → Bool) (Z : Strat ζ E O) :
    SPComp.bind c (fun v => run (Y v) bad Z) = run Yc bad Z := by
  simp only [run, hinit]
  exact loop_deferred c hc hcn Y Yc Inv post use hinv hinvY hpost hmono hfree huse hused bad Z
    _ _ _ _ hi0 hp0

/-- **Deferred sampling for views.** -/
theorem view_deferred (c : SPComp α) (hc : SPComp.IsPure c) (hcn : SPComp.NoFail c)
    (Y : α → Sys τ E O) (Yc : Sys τ E O) (Inv post : τ → Prop) (use : τ → E → Prop)
    (hinit : ∀ v, (Y v).init = Yc.init) (hi0 : Inv Yc.init) (hp0 : ¬ post Yc.init)
    (hinv : ∀ t e q, Inv t → IsOutcome (Yc.step t e) q → Inv q.1)
    (hinvY : ∀ v t e q, Inv t → IsOutcome ((Y v).step t e) q → Inv q.1)
    (hpost : ∀ v t e, Inv t → post t → (Y v).step t e = Yc.step t e)
    (hmono : ∀ t e q, Inv t → post t → IsOutcome (Yc.step t e) q → post q.1)
    (hfree : ∀ v t e, Inv t → ¬ post t → ¬ use t e → (Y v).step t e = Yc.step t e)
    (huse : ∀ t e, Inv t → ¬ post t → use t e →
      Yc.step t e = SPComp.bind c fun v => (Y v).step t e)
    (hused : ∀ v t e q, Inv t → ¬ post t → use t e → IsOutcome ((Y v).step t e) q → post q.1)
    (Z : Strat ζ E O) :
    SPComp.bind c (fun v => view (Y v) Z) = view Yc Z := by
  have h := run_deferred c hc hcn Y Yc Inv post use hinit hi0 hp0 hinv hinvY hpost hmono hfree
    huse hused (fun _ => false) Z
  simp only [view, SPComp.map] at h ⊢
  rw [← h, SPComp.bind_assoc]

end Deferred

/-! ## Mixtures -/

/-- **The distance between mixtures.** If, at every outcome and heap, the continuations `f`
and `g` are at distance at most the acceptance probability of `b`, then `c` followed by `f` and
`c` followed by `g` are at distance at most the acceptance probability of `c` followed by
`b`. -/
theorem absDiff_prTrue_bind_le_bind {α : Type} (c : SPComp α) (f g b : α → SPComp Bool)
    (h₀ : Heap)
    (hfg : ∀ a h, absDiff (prTrue (f a) h) (prTrue (g a) h) ≤ prTrue (b a) h) :
    absDiff (prTrue (SPComp.bind c f) h₀) (prTrue (SPComp.bind c g) h₀) ≤
      prTrue (SPComp.bind c b) h₀ := by
  rw [prTrue_bind_eq_weighted c f h₀, prTrue_bind_eq_weighted c g h₀,
    prTrue_bind_eq_weighted c b h₀]
  set w := fun p : Option (α × Heap) => (c h₀ : PMF _) p
  have key : ∀ (F G : α → SPComp Bool),
      (∀ a h, prTrue (F a) h ≤ prTrue (G a) h + prTrue (b a) h) →
      (∑' p, w p * (match p with | some ⟨a, h'⟩ => prTrue (F a) h' | none => 0)) -
        (∑' p, w p * (match p with | some ⟨a, h'⟩ => prTrue (G a) h' | none => 0)) ≤
      ∑' p, w p * (match p with | some ⟨a, h'⟩ => prTrue (b a) h' | none => 0) := by
    intro F G hFG
    rw [tsub_le_iff_right]
    calc ∑' p, w p * (match p with | some ⟨a, h'⟩ => prTrue (F a) h' | none => 0)
        ≤ ∑' p, (w p * (match p with | some ⟨a, h'⟩ => prTrue (b a) h' | none => 0) +
            w p * (match p with | some ⟨a, h'⟩ => prTrue (G a) h' | none => 0)) := by
          refine ENNReal.tsum_le_tsum fun p => ?_
          rw [← mul_add]
          gcongr
          rcases p with _ | ⟨a, h'⟩
          · simp
          · rw [add_comm]; exact hFG a h'
      _ = _ := ENNReal.tsum_add
  refine max_le (key f g fun a h => le_add_of_absDiff_le (hfg a h))
    (key g f fun a h => le_add_of_absDiff_le ?_)
  rw [absDiff_comm]; exact hfg a h

/-! ## Reductions with a given heap -/

/-- The computation `c` run from the heap `h`, whatever the current heap. -/
noncomputable def SPComp.atHeap {α : Type} (h : Heap) (c : SPComp α) : SPComp α :=
  fun _ => c h

/-- For a computation `c` that does not touch the heap, `c` followed by `f` from the heap `h`
is, from any heap, `c` followed by `f` run from `h`. -/
theorem bind_atHeap {α β : Type} {c : SPComp α} (hc : SPComp.IsPure c) (f : α → SPComp β)
    (h h' : Heap) :
    SPComp.bind c f h = SPComp.bind c (fun a => SPComp.atHeap h (f a)) h' := by
  obtain ⟨d, hd⟩ := hc
  simp only [SPComp.bind_def, hd, SDistr.bind_assoc, SDistr.pure_bind, SPComp.atHeap]

/-- The acceptance probability of `c` followed by `f` from the heap `h` is the acceptance
probability from the empty heap of `c` followed by `f` run from `h`. -/
theorem prTrue_bind_atHeap {α : Type} {c : SPComp α} (hc : SPComp.IsPure c)
    (f : α → SPComp Bool) (h : Heap) :
    prTrue (SPComp.bind c f) h =
      prTrue (SPComp.bind c fun a => SPComp.atHeap h (f a)) Heap.empty := by
  unfold prTrue
  rw [bind_atHeap hc f h Heap.empty]

/-- The distance from the heap `h` between two games that do not touch the heap, followed by
`f`, is the advantage of the distinguisher that runs `f` from `h`. -/
theorem absDiff_prTrue_bind_eq_advantageA {α : Type} {c₁ c₀ : SPComp α} (h₁ : SPComp.IsPure c₁)
    (h₀ : SPComp.IsPure c₀) (f : α → SPComp Bool) (h : Heap) :
    absDiff (prTrue (SPComp.bind c₁ f) h) (prTrue (SPComp.bind c₀ f) h) =
      AdvantageA c₁ c₀ (fun a => SPComp.atHeap h (f a)) := by
  rw [prTrue_bind_atHeap h₁, prTrue_bind_atHeap h₀]
  rfl

/-! ## Counters -/

section Counter

variable {τ ζ E O : Type}

/-- The flag of a run whose counter starts at most `n - k` and rises by at most one per
activation stays down for `k` activations. -/
theorem loop_counter_flag (S : Sys τ E O) (cnt : τ → ℕ) (n : ℕ)
    (hstep : ∀ t e q, IsOutcome (S.step t e) q → cnt q.1 ≤ cnt t + 1) (Z : Strat ζ E O) :
    ∀ (k : ℕ) (z : ζ) (t : τ) (q : ζ × τ × Bool), cnt t + k ≤ n →
      IsOutcome (loop S (fun t => decide (n < cnt t)) Z k (z, t, false)) q → q.2.2 = false := by
  intro k
  induction k with
  | zero =>
    intro z t q _ hq
    exact (isOutcome_pure hq).symm ▸ rfl
  | succ k ih =>
    intro z t q hk hq
    simp only [loop] at hq
    obtain ⟨a, _, ha⟩ := isOutcome_bind hq
    obtain ⟨p, hp, hp'⟩ := isOutcome_bind ha
    obtain ⟨z', _, hz'⟩ := isOutcome_bind hp'
    have hc := hstep t a.2 p hp
    have hb : decide (n < cnt p.1) = false := by simp; omega
    rw [Bool.false_or, hb] at hz'
    exact ih z' p.1 q (by omega) hz'

/-- **A counter bounded by the number of activations.** If the steps of `S` raise the counter
`cnt` by at most one, then in a run of at most `n - cnt S.init` activations the counter never
exceeds `n`. -/
theorem prBad_counter_eq_zero (S : Sys τ E O) (cnt : τ → ℕ) (n : ℕ)
    (hstep : ∀ t e q, IsOutcome (S.step t e) q → cnt q.1 ≤ cnt t + 1)
    (Z : Env (Strat ζ E O) ζ) (hZ : cnt S.init + Z.input.rounds ≤ n) :
    prBad S (fun t => decide (n < cnt t)) Z = 0 := by
  have h0 : decide (n < cnt S.init) = false := by simp; omega
  have hb : SPComp.bind (run S (fun t => decide (n < cnt t)) Z.input)
      (fun c => SPComp.pure c.2.2) =
      SPComp.bind (run S (fun t => decide (n < cnt t)) Z.input) (fun _ => SPComp.pure false) := by
    refine bind_congr_isOutcome fun q hq => ?_
    unfold run at hq
    rw [show (fun t => decide (n < cnt t)) S.init = false from h0] at hq
    rw [loop_counter_flag S cnt n hstep Z.input _ _ _ q hZ hq]
  unfold prBad
  rw [hb, prTrue_bind_eq_weighted]
  refine ENNReal.tsum_eq_zero.2 fun p => ?_
  rcases p with _ | ⟨a, h'⟩ <;> simp [prTrue_pure]

end Counter

/-! ## The cascade over a context -/

section Ctx

variable {τ υ υ' E O P : Type}

open Hybrid

/-- **Realization through `X`**: `Y` realizes `Y'` with bound `b` for the environments of the
cascade `X.seq Y` reduced through the context of `X`, which runs `X` before each event of
`Y`. -/
def RealizesThrough (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e)) (Y : Sys υ O P)
    (Y' : Sys υ' O P) (b : (ζ : Type) → Env (Strat ζ E P) ζ → ℝ≥0∞) : Prop :=
  ∀ (ζ : Type) (Z : Env (Strat ζ E P) ζ),
    Env.gap (view Y) (view Y') ((seqCtxL (P := P) X hX).reduceEnv Z) ≤ b ζ Z

/-- **Cascade over a context.** If `Y` realizes `Y'` through `X` with bound `b`, then `X.seq Y`
realizes `X.seq Y'` with bound `b`. -/
theorem realizes_seq_right_ctx (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    {Y : Sys υ O P} {Y' : Sys υ' O P} {b : (ζ : Type) → Env (Strat ζ E P) ζ → ℝ≥0∞}
    (h : RealizesThrough X hX Y Y' b) : Realizes (X.seq Y) (X.seq Y') b := by
  rw [← seqCtxL_withSub X hX Y, ← seqCtxL_withSub X hX Y']
  intro ζ Z
  have ha := Hybrid.adv_withSub (seqCtxL X hX) Y Y' Z
  unfold adv at ha
  change Env.gap _ _ Z ≤ _
  rw [ha]
  exact h ζ Z

/-- A realization for every environment is a realization through every context. -/
theorem Realizes.through (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    {Y : Sys υ O P} {Y' : Sys υ' O P} {b : (ζ : Type) → Env (Strat ζ O P) ζ → ℝ≥0∞}
    (h : Realizes Y Y' b) :
    RealizesThrough X hX Y Y' (fun ζ Z => b (ζ × τ) ((seqCtxL (P := P) X hX).reduceEnv Z)) :=
  fun _ _ => h _ _

/-- **Cascade of a realization and a realization through the ideal system.** If `X` realizes
`X'` with bound `bX` and `Y` realizes `Y'` through `X'` with bound `bY`, then `X.seq Y`
realizes `X'.seq Y'` with the sum of `bX` at the environment reduced through the context of
`Y` and `bY`. -/
theorem realizesThrough_seq {τ' : Type} {X : Sys τ E O} {X' : Sys τ' E O} {Y : Sys υ O P}
    {Y' : Sys υ' O P} (hY : ∀ u o, SPComp.NoFail (Y.step u o))
    (hX' : ∀ t e, SPComp.NoFail (X'.step t e))
    {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E P) ζ → ℝ≥0∞}
    (hXr : Realizes X X' bX) (hYr : RealizesThrough X' hX' Y Y' bY) :
    Realizes (X.seq Y) (X'.seq Y')
      (fun ζ Z => bX (ζ × υ) ((seqCtxR (E := E) Y hY).reduceEnv Z) + bY ζ Z) :=
  Realizes.trans (realizes_seq_left Y hY hXr) (realizes_seq_right_ctx X' hX' hYr)

end Ctx

end CatCrypt.Crypto.UCTransparent

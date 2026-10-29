/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparent
public import CatCryptCore.Relational.Approx
public import CatCryptCore.Relational.Rules

/-!
# Realization of transition systems from relational couplings

Proof principles for `UCTransparent.Realizes` between two systems `R : Sys τ E O` and
`I : Sys υ E O` with possibly different state types, from relational judgments about single
activations. A relation `rel : τ → υ → Prop` relates the states; each activation from related
states is coupled so that the heaps and outputs agree and the new states are related.

## Main results

* `realizes_zero_of_coupling` — a coupling bisimulation (`CouplingBisim`): related initial
  states and an exact coupling `rHoare` of the steps from related states, gives distance `0`.
* Examples recover `realizes_zero_of_stepMap`, `realizes_zero_of_stepRel` and
  `realizes_zero_of_step_eq` (the distance-0 principles for a state map, for point-mass steps
  and for equal steps) from `realizes_zero_of_coupling`.
* `realizes_of_couplingApprox` — a graded coupling with an `rHoareApprox ε` judgment per
  activation gives the bound `ε` times the number of activations `Z.input.rounds`.
* `realizes_upto_bad_rel` — up to bad across a relation: the coupling of the steps may break on
  transitions into states where the flag `bad` holds on the real side; the bound is the
  probability `prBad R bad` that the real run visits a bad state.
* An example recovers `UCTransparent.adv_le_prBad`, the up-to-bad lemma for systems on one
  state space, from `realizes_upto_bad_rel` and `liftR_or_eq_of_agree`.
* `realizes_of_budget` — budgets in the relation: `rel : τ → υ → ℝ≥0∞ → Prop` carries the
  remaining error budget, each activation from budget `c` is an `rHoareApprox (c - c')`
  judgment leaving budget `c'`; the bound is the initial budget.
* `counterSampler_realizes` — an instance of the budget rule: a sampler answering at most `q`
  queries with a uniform guess of a fixed target in `Fin (2 ^ n)` realizes the system that never
  hits the target, with bound `q * (2 ^ n)⁻¹`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.UCCoupling

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {τ υ ζ E O : Type}

/-! ## Relational posts of activations and runs -/

/-- The post-relation of one coupled activation: equal heaps, related new states and equal
    outputs. -/
def stepPost (rel : τ → υ → Prop) : RPost (τ × O) (υ × O) :=
  fun p h q h' => h = h' ∧ rel p.1 q.1 ∧ p.2 = q.2

/-- The post-relation of two coupled runs: equal heaps, equal environment states and related
    system states. -/
def loopPost (rel : τ → υ → Prop) : RPost (ζ × τ × Bool) (ζ × υ × Bool) :=
  fun c h d h' => h = h' ∧ c.1 = d.1 ∧ rel c.2.1 d.2.1

/-- A judgment whose precondition implies a fact `P` follows from the judgments under `P`. -/
theorem rHoareApprox_of_pre_fact {α β : Type} {Φ : RPre} {Ψ : RPost α β} {c₁ : SPComp α}
    {c₂ : SPComp β} {ε : ℝ≥0∞} {P : Prop} (hP : ∀ h₁ h₂, Φ h₁ h₂ → P)
    (h : P → rHoareApprox ε Φ c₁ c₂ Ψ) : rHoareApprox ε Φ c₁ c₂ Ψ :=
  fun h₁ h₂ hΦ => h (hP h₁ h₂ hΦ) h₁ h₂ hΦ

/-! ## Graded coupling of runs -/

/-- **Graded coupling of runs.** If every activation from related states is an
    `rHoareApprox ε` judgment with post `stepPost rel`, then `n` activations of the joint runs
    of `Z` against `R` and `I` from related states and a common environment state are an
    `rHoareApprox (n * ε)` judgment with post `loopPost rel`. The environment's steps are
    coupled by reflexivity. -/
theorem loop_rHoareApprox (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop) (ε : ℝ≥0∞)
    (hstep : ∀ t u e, rel t u → rHoareApprox ε eqPre (R.step t e) (I.step u e) (stepPost rel))
    (bad : τ → Bool) (bad' : υ → Bool) (Z : Strat ζ E O) :
    ∀ (n : ℕ) z t u b b', rel t u →
      rHoareApprox (n * ε) eqPre (loop R bad Z n (z, t, b)) (loop I bad' Z n (z, u, b'))
        (loopPost rel) := by
  intro n
  induction n with
  | zero =>
    intro z t u b b' hr
    refine rHoareApprox_mono_eps (by simp) (rHoareApprox_of_rHoare ?_)
    exact rHoare_ret fun h h' heq => ⟨heq, rfl, hr⟩
  | succ n ih =>
    intro z t u b b' hr
    simp only [loop]
    refine rHoareApprox_mono_eps (le_of_eq ?_) (rHoareApprox_bind (ε₂ := ε + (0 + n * ε))
      (rHoareApprox_refl_of_pre (Z.next z) fun _ _ h => h) fun a a' => ?_)
    · push_cast; ring
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.1) fun ha => ?_
    subst ha
    refine rHoareApprox_bind (Ψ := stepPost rel) (ε₂ := 0 + n * ε)
      (rHoareApprox_conseq (fun _ _ hh => hh.2) (fun _ _ _ _ => id) le_rfl (hstep t u a.2 hr))
      fun p q => ?_
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.2) fun ⟨hpq, ho⟩ => ?_
    rw [← ho]
    refine rHoareApprox_bind (ε₂ := n * ε)
      (rHoareApprox_refl_of_pre (Z.obs a.1 p.2) fun _ _ hh => hh.1) fun z₁ z₂ => ?_
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.1) fun hz => ?_
    subst hz
    exact rHoareApprox_conseq (fun _ _ hh => hh.2) (fun _ _ _ _ => id) le_rfl
      (ih _ _ _ _ _ hpq)

/-- The views of `Z` against `R` and `I` under the hypotheses of `loop_rHoareApprox`, from
    related initial states, are an `rHoareApprox (Z.rounds * ε)` judgment with equality
    post. -/
theorem view_rHoareApprox (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop) (ε : ℝ≥0∞)
    (hinit : rel R.init I.init)
    (hstep : ∀ t u e, rel t u → rHoareApprox ε eqPre (R.step t e) (I.step u e) (stepPost rel))
    (Z : Strat ζ E O) :
    rHoareApprox (Z.rounds * ε) eqPre (view R Z) (view I Z) eqPost := by
  unfold view run SPComp.map
  refine rHoareApprox_mono_eps (le_of_eq (add_zero _)) (rHoareApprox_bind
    (loop_rHoareApprox R I rel ε hstep _ _ Z _ _ _ _ _ _ hinit) fun c d => ?_)
  exact rHoareApprox_of_rHoare (rHoare_ret fun h h' hh => ⟨hh.2.1, hh.1⟩)

/-- **Graded coupling bisimulation.** If the initial states are related and every activation
    from related states is an `rHoareApprox ε` judgment with post `stepPost rel`, then `R`
    realizes `I` with bound `ε` times the number `Z.input.rounds` of activations of the run. -/
theorem realizes_of_couplingApprox (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop)
    (ε : ℝ≥0∞) (hinit : rel R.init I.init)
    (hstep : ∀ t u e, rel t u → rHoareApprox ε eqPre (R.step t e) (I.step u e) (stepPost rel)) :
    Realizes R I (fun _ Z => Z.input.rounds * ε) := by
  intro ζ Z
  exact rHoareApprox_absDiff_prTrue (view_rHoareApprox R I rel ε hinit hstep Z.input) Z.dist
    Z.heap

/-! ## Exact coupling bisimulation -/

/-- A coupling bisimulation between `R` and `I`: a relation on states that holds at the initial
    states and is preserved by an exact coupling of the steps with equal heaps and outputs. -/
structure CouplingBisim (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop) : Prop where
  /-- The initial states are related. -/
  init : rel R.init I.init
  /-- Steps from related states with equal heaps are coupled with post `stepPost rel`. -/
  step : ∀ t u e, rel t u → rHoare eqPre (R.step t e) (I.step u e) (stepPost rel)

/-- Realization is symmetric: the bound is an absolute difference. -/
theorem realizes_symm {R : Sys τ E O} {I : Sys υ E O}
    {bound : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes R I bound) :
    Realizes I R bound :=
  fun ζ => (h ζ).symm

/-- **Coupling bisimulation gives distance 0.** Two systems related by a coupling
    bisimulation realize each other at distance `0`. -/
theorem realizes_zero_of_coupling {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) :
    Realizes R I (fun _ _ => 0) ∧ Realizes I R (fun _ _ => 0) := by
  have h₀ : Realizes R I (fun _ _ => 0) := by
    have := realizes_of_couplingApprox R I rel 0 h.init fun t u e htu =>
      rHoareApprox_of_rHoare (h.step t u e htu)
    simpa using this
  exact ⟨h₀, realizes_symm h₀⟩

/-! ## The distance-0 principles as instances -/

-- recovers UCTransparent.realizes_zero_of_stepMap (UCTransparentMulti)
example (R : Sys τ E O) (I : Sys υ E O) (f : τ → υ)
    (hinit : f R.init = I.init)
    (hstep : ∀ t e, SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = I.step (f t) e) :
    Realizes R I (fun _ _ => 0) := by
  refine (realizes_zero_of_coupling (rel := fun t u => f t = u) ⟨hinit, ?_⟩).1
  intro t u e htu
  subst htu
  rw [← hstep]
  have h := rHoare_bind (f₁ := SPComp.pure) (f₂ := fun p => SPComp.pure (f p.1, p.2))
    (Θ := stepPost (fun t u => f t = u)) (rHoare_refl (R.step t e)) fun a b =>
      rHoare_ret fun h h' hh => by
        obtain ⟨rfl, rfl⟩ := hh
        exact ⟨rfl, rfl, rfl⟩
  rw [SPComp.bind_pure] at h
  exact h

-- recovers UCTransparent.realizes_zero_of_stepRel (UCTransparentMulti)
example (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop)
    (hinit : rel R.init I.init)
    (hstep : ∀ t u e, rel t u → ∃ t' u' o, R.step t e = SPComp.pure (t', o) ∧
      I.step u e = SPComp.pure (u', o) ∧ rel t' u') :
    Realizes R I (fun _ _ => 0) := by
  refine (realizes_zero_of_coupling (rel := rel) ⟨hinit, ?_⟩).1
  intro t u e htu
  obtain ⟨t', u', o, h1, h2, h3⟩ := hstep t u e htu
  rw [h1, h2]
  exact rHoare_ret fun h h' hh => ⟨hh, h3, rfl⟩

-- recovers UCTransparent.realizes_zero_of_step_eq (UCGlobal)
example (R I : Sys τ E O) (hinit : R.init = I.init)
    (hstep : ∀ t e, R.step t e = I.step t e) :
    Realizes R I (fun _ _ => 0) ∧ Realizes I R (fun _ _ => 0) := by
  refine realizes_zero_of_coupling (rel := Eq) ⟨hinit, ?_⟩
  intro t u e htu
  subst htu
  rw [hstep]
  exact rHoare_conseq (fun _ _ hh => hh) (fun a h b h' hh => ⟨hh.2, by rw [hh.1], by rw [hh.1]⟩)
    (rHoare_refl (I.step t e))

/-! ## Couplings up to a bad event -/

/-- **A coupling up to bad is an approximate lifting.** An exact coupling of `d₁` and `d₂` whose
    pairs satisfy `B a ∨ S a b` restricts to an approximate lifting of `S` whose grade is the
    mass of `B` under `d₁`. -/
theorem liftRApprox_of_coupling_or {α β : Type} {d₁ : SDistr α} {d₂ : SDistr β}
    (B : α → Bool) (S : α → β → Prop) (c : Coupling d₁ d₂)
    (hc : c.satisfies fun a b => B a = true ∨ S a b) :
    liftRApprox (∑' a, if B a then d₁ (some a) else 0) S d₁ d₂ := by
  classical
  let w : SDistr (α × β) := c.joint.bind fun p => if B p.1 then SDistr.fail else SDistr.pure p
  have hw : ∀ p, w (some p) = if B p.1 then 0 else c.joint (some p) := by
    intro p
    rw [SDistr.bind_apply_some, tsum_eq_single p]
    · split_ifs <;> simp [SDistr.fail_apply_some, SDistr.pure_apply_some]
    · intro p' hp'
      split_ifs <;> simp [SDistr.fail_apply_some, SDistr.pure_apply_some, hp']
  have hL : ∀ a, ∑' b, c.joint (some (a, b)) = d₁ (some a) := c.left_marginal_sum
  have hR : ∀ b, ∑' a, c.joint (some (a, b)) = d₂ (some b) := c.right_marginal_sum
  have hwL : ∀ a, ∑' b, w (some (a, b)) = if B a then 0 else d₁ (some a) := by
    intro a
    simp only [hw]
    split_ifs <;> simp [hL]
  refine ⟨⟨w, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a
    rw [hwL]
    split_ifs <;> simp
  · intro b
    rw [← hR b]
    exact ENNReal.tsum_le_tsum fun a => by rw [hw]; split_ifs <;> simp
  · refine le_of_eq (tsum_congr fun a => ?_)
    rw [hwL]
    split_ifs <;> simp
  · calc ∑' b, (d₂ (some b) - ∑' a, w (some (a, b)))
        ≤ ∑' b, ∑' a, (if B a then c.joint (some (a, b)) else 0) :=
          ENNReal.tsum_le_tsum fun b => by
            rw [tsub_le_iff_right, ← hR b, ← ENNReal.tsum_add]
            exact ENNReal.tsum_le_tsum fun a => by rw [hw]; split_ifs <;> simp
      _ = ∑' a, (if B a then d₁ (some a) else 0) := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun a => ?_
          split_ifs <;> simp [hL]
  · intro a b hab
    rw [hw] at hab
    split_ifs at hab with hB
    · exact absurd rfl hab
    · exact (hc a b hab).resolve_left hB

/-- The probability that `X` returns a value satisfying `B` is the `B`-mass of its output
    distribution. -/
theorem prTrue_bind_pure_eq {α : Type} (X : SPComp α) (B : α → Bool) (h₀ : Heap) :
    prTrue (SPComp.bind X fun a => SPComp.pure (B a)) h₀ =
      ∑' p : α × Heap, if B p.1 then (X h₀) (some p) else 0 := by
  rw [prTrue_bind_weighted']
  refine tsum_congr fun p => ?_
  rw [prTrue_pure]
  split_ifs <;> simp

/-- **Adequacy up to bad.** If `X` and `Y` are coupled from equal heaps so that every pair either
    satisfies `B` on the left or has equal images under `f` and `g` and equal heaps, then every
    distinguisher's gap between `map f X` and `map g Y` is at most the probability of `B`
    under `X`. -/
theorem absDiff_le_of_rHoare_or {α β γ : Type} (X : SPComp α) (Y : SPComp β) (f : α → γ)
    (g : β → γ) (B : α → Bool)
    (h : rHoare eqPre X Y fun a h b h' => B a = true ∨ (f a = g b ∧ h = h'))
    (A : γ → SPComp Bool) (h₀ : Heap) :
    absDiff (prTrue (SPComp.bind (SPComp.map f X) A) h₀)
      (prTrue (SPComp.bind (SPComp.map g Y) A) h₀) ≤
      prTrue (SPComp.bind X fun a => SPComp.pure (B a)) h₀ := by
  obtain ⟨c, hc⟩ := h h₀ h₀ rfl
  have h1 := liftRApprox_of_coupling_or (fun p => B p.1)
    (fun (p : α × Heap) (q : β × Heap) => eqPost (f p.1) p.2 (g q.1) q.2) c
    (fun p q hpq => (hc p q hpq).imp id fun hh => ⟨hh.1, hh.2⟩)
  have h2 : liftRApprox ((∑' p : α × Heap, if B p.1 then (X h₀) (some p) else 0) + 0)
      (fun (p q : γ × Heap) => eqPost p.1 p.2 q.1 q.2) (SPComp.map f X h₀)
      (SPComp.map g Y h₀) := by
    unfold SPComp.map
    simp only [SPComp.bind_def]
    exact liftRApprox_bind h1 fun ⟨a, ha⟩ ⟨b, hb⟩ hpq =>
      liftRApprox_of_liftR (liftR_pure hpq)
  rw [add_zero] at h2
  rw [prTrue_bind_pure_eq]
  exact absDiff_prTrue_le_of_liftRApprox h2 A

/-- Two lossless computations are coupled with the trivial post. -/
theorem rHoare_true_of_noFail {α β : Type} {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β}
    (h₁ : SPComp.NoFail c₁) (h₂ : SPComp.NoFail c₂) :
    rHoare Φ c₁ c₂ fun _ _ _ _ => True :=
  fun x y _ => ⟨Coupling.prod _ _ (by simp [SDistr.mass, h₁ x]) (by simp [SDistr.mass, h₂ y]),
    fun _ _ _ => trivial⟩

/-- A judgment whose precondition implies a fact `P` follows from the judgments under `P`. -/
theorem rHoare_of_pre_fact {α β : Type} {Φ : RPre} {Ψ : RPost α β} {c₁ : SPComp α}
    {c₂ : SPComp β} {P : Prop} (hP : ∀ h₁ h₂, Φ h₁ h₂ → P)
    (h : P → rHoare Φ c₁ c₂ Ψ) : rHoare Φ c₁ c₂ Ψ :=
  fun h₁ h₂ hΦ => h (hP h₁ h₂ hΦ) h₁ h₂ hΦ

/-! ## Up to bad across a relation -/

/-- The invariant of two runs coupled up to bad: while the flag of the real run is unset, the
    heaps and environment states are equal, the system states are related and the real state is
    good. -/
def badInv (bad : τ → Bool) (rel : τ → υ → Prop) : RPost (ζ × τ × Bool) (ζ × υ × Bool) :=
  fun c h d h' => c.2.2 = false → h = h' ∧ c.1 = d.1 ∧ rel c.2.1 d.2.1 ∧ bad c.2.1 = false

/-- **Runs coupled up to bad.** If from related good states the steps of the lossless systems
    `R` and `I` are coupled so that either the new real state is bad or `stepPost rel` holds,
    then the joint runs of `Z` are coupled with the invariant `badInv bad rel`. -/
theorem loop_rHoare_upto (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop) (bad : τ → Bool)
    (hR : ∀ t e, SPComp.NoFail (R.step t e)) (hI : ∀ u e, SPComp.NoFail (I.step u e))
    (hstep : ∀ t u e, rel t u → bad t = false → rHoare eqPre (R.step t e) (I.step u e)
      fun p h q h' => bad p.1 = true ∨ stepPost rel p h q h')
    (bad' : υ → Bool) (Z : Strat ζ E O) :
    ∀ (n : ℕ) (c : ζ × τ × Bool) (d : ζ × υ × Bool),
      rHoare (fun h h' => badInv bad rel c h d h') (loop R bad Z n c) (loop I bad' Z n d)
        (badInv bad rel) := by
  intro n
  induction n with
  | zero => intro c d; exact rHoare_ret fun h h' hh => hh
  | succ n ih =>
    rintro ⟨z, t, b⟩ ⟨z', u, b'⟩
    simp only [loop]
    cases b with
    | true =>
      refine rHoare_bind (rHoare_true_of_noFail (Z.next_noFail z) (Z.next_noFail z'))
        fun a a' => ?_
      refine rHoare_bind (rHoare_true_of_noFail (hR _ _) (hI _ _)) fun p q => ?_
      refine rHoare_bind (rHoare_true_of_noFail (Z.obs_noFail _ _) (Z.obs_noFail _ _))
        fun z₁ z₂ => ?_
      exact rHoare_conseq (fun _ _ _ hf => by simp at hf) (fun _ _ _ _ => id) (ih _ _)
    | false =>
      refine rHoare_of_pre_fact (fun _ _ hh => (hh rfl).2) fun ⟨hz, hr, hbt⟩ => ?_
      subst hz
      refine rHoare_bind (rHoare_conseq (fun _ _ hh => (hh rfl).1) (fun _ _ _ _ => id)
        (rHoare_refl (Z.next z))) fun a a' => ?_
      refine rHoare_of_pre_fact (fun _ _ hh => hh.1) fun ha => ?_
      subst ha
      refine rHoare_bind (rHoare_conseq (fun _ _ hh => hh.2) (fun _ _ _ _ => id)
        (hstep t u a.2 hr hbt)) fun p q => ?_
      by_cases hb : bad p.1 = true
      · refine rHoare_bind (rHoare_true_of_noFail (Z.obs_noFail _ _) (Z.obs_noFail _ _))
          fun z₁ z₂ => ?_
        exact rHoare_conseq (fun _ _ _ hf => by simp [hb] at hf) (fun _ _ _ _ => id) (ih _ _)
      · refine rHoare_of_pre_fact (fun _ _ hh => (hh.resolve_left hb).2) fun ⟨hrel, ho⟩ => ?_
        rw [← ho]
        refine rHoare_bind (rHoare_conseq (fun _ _ hh => (hh.resolve_left hb).1)
          (fun _ _ _ _ => id) (rHoare_refl (Z.obs a.1 p.2))) fun z₁ z₂ => ?_
        refine rHoare_of_pre_fact (fun _ _ hh => hh.1) fun hz => ?_
        subst hz
        exact rHoare_conseq (fun _ _ hh _ => ⟨hh.2, rfl, hrel, by simpa using hb⟩)
          (fun _ _ _ _ => id) (ih _ _)

/-- **Up to bad across a relation.** Let `R` and `I` be lossless systems with related initial
    states, and assume that from related states where the real state is good, their steps are
    coupled from equal heaps so that either the new real state is bad or the heaps and outputs
    are equal and the new states related. Then `R` realizes `I` with bound the probability
    `prBad R bad` that the run against `R` visits a bad state. -/
theorem realizes_upto_bad_rel (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop)
    (bad : τ → Bool) (hinit : rel R.init I.init)
    (hR : ∀ t e, SPComp.NoFail (R.step t e)) (hI : ∀ u e, SPComp.NoFail (I.step u e))
    (hstep : ∀ t u e, rel t u → bad t = false → rHoare eqPre (R.step t e) (I.step u e)
      fun p h q h' => bad p.1 = true ∨ stepPost rel p h q h') :
    Realizes R I (fun _ Z => prBad R bad Z) := by
  intro ζ Z
  have hrun := loop_rHoare_upto R I rel bad hR hI hstep (fun _ => false) Z.input
    Z.input.rounds (Z.input.init, R.init, bad R.init) (Z.input.init, I.init, false)
  have h := absDiff_le_of_rHoare_or (run R bad Z.input) (run I (fun _ => false) Z.input)
    Prod.fst Prod.fst (fun c => c.2.2)
    (rHoare_conseq (fun _ _ hh hb => ⟨hh, rfl, hinit, hb⟩) (fun c _ d _ hh => by
      cases hc : c.2.2
      · exact Or.inr ⟨(hh hc).2.1, (hh hc).1⟩
      · exact Or.inl rfl) hrun) Z.dist Z.heap
  unfold Env.gap
  rw [view_eq_map_run R bad]
  exact h

/-! ## The up-to-bad lemma on one state space as an instance -/

/-- **Coupling from agreement on good outcomes.** Two lossless sub-distributions that agree on
    every outcome outside `B` are coupled so that every pair either has its left component in
    `B` or is diagonal. The good outcomes are coupled diagonally and the bad outcomes of `d₁`
    with `d₂` conditioned on `B`. -/
theorem liftR_or_eq_of_agree {X : Type} {d₁ d₂ : SDistr X} (B : X → Bool)
    (h₁ : d₁ none = 0) (h₂ : d₂ none = 0)
    (hagree : ∀ x, B x = false → d₁ (some x) = d₂ (some x)) :
    liftR (fun x y => B x = true ∨ x = y) d₁ d₂ := by
  classical
  have hsplit : ∀ d : SDistr X, d none = 0 →
      (∑' x, if B x then 0 else d (some x)) + (∑' x, if B x then d (some x) else 0) = 1 := by
    intro d hd
    rw [← ENNReal.tsum_add, ← SDistr.tsum_some_eq_one_of_none_zero hd]
    exact tsum_congr fun x => by split_ifs <;> simp
  have hg : (∑' x, if B x then 0 else d₂ (some x)) = ∑' x, if B x then 0 else d₁ (some x) :=
    tsum_congr fun x => by
      cases hB : B x
      · simp [hagree x hB]
      · simp
  have hm : (∑' x, if B x then d₁ (some x) else 0) = ∑' x, if B x then d₂ (some x) else 0 := by
    have e1 := hsplit d₁ h₁
    have e2 := hsplit d₂ h₂
    rw [hg] at e2
    have hg_ne : (∑' x, if B x then 0 else d₁ (some x)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (e1 ▸ le_self_add)
    exact (ENNReal.add_right_inj hg_ne).mp (e1.trans e2.symm)
  set m := ∑' x, if B x then d₂ (some x) else 0 with hm_def
  have hm_le : m ≤ 1 := (hsplit d₂ h₂) ▸ le_add_self
  by_cases hm0 : m = 0
  · have hbad : ∀ (d : SDistr X) x, (∑' x, if B x then d (some x) else 0) = 0 → B x = true →
        d (some x) = 0 := by
      intro d x hd hB
      have := ENNReal.le_tsum (f := fun x => if B x then d (some x) else 0) x
      simp only [hB, ite_true] at this
      exact nonpos_iff_eq_zero.mp (hd ▸ this)
    have heq : d₁ = d₂ := by
      ext o
      cases o with
      | none => rw [h₁, h₂]
      | some x =>
        cases hB : B x
        · exact hagree x hB
        · rw [hbad d₁ x (hm.trans hm0) hB, hbad d₂ x hm0 hB]
    subst heq
    exact liftR_mono (fun a b hab => Or.inr hab) (liftR_refl d₁)
  · let s : Set (Option X) := {o | ∃ x, o = some x ∧ B x = true}
    have hex : ∃ o ∈ s, o ∈ PMF.support d₂ := by
      by_contra hne
      push Not at hne
      apply hm0
      refine ENNReal.tsum_eq_zero.mpr fun x => ?_
      split_ifs with hB
      · exact (PMF.apply_eq_zero_iff d₂ _).mpr (hne _ ⟨x, rfl, hB⟩)
      · rfl
    let ν : SDistr X := d₂.filter s hex
    have hsum : ∑' o, s.indicator d₂ o = m := by
      rw [SDistr.tsum_option_eq_add, hm_def]
      simp [s, Set.indicator]
    have hν : ∀ y, ν (some y) = (if B y then d₂ (some y) else 0) * m⁻¹ := by
      intro y
      simp only [ν, PMF.filter_apply, hsum]
      simp [s, Set.indicator]
    have hνnone : ν none = 0 := by
      simp only [ν, PMF.filter_apply]
      simp [s, Set.indicator]
    have hνmass : SDistr.mass ν = 1 := by simp [SDistr.mass, hνnone]
    let joint : SDistr (X × X) := d₁.bind fun x =>
      if B x then ν.bind (fun y => SDistr.pure (x, y)) else SDistr.pure (x, x)
    refine ⟨⟨joint, ?_, ?_⟩, ?_⟩
    · intro a
      simp only [joint, SDistr.bind_assoc]
      have hk : (fun x => (if B x then ν.bind (fun y => SDistr.pure (x, y))
          else SDistr.pure (x, x)).bind fun p => SDistr.pure p.1) = SDistr.pure := by
        funext x
        split_ifs
        · rw [SDistr.bind_assoc]
          simp only [SDistr.pure_bind]
          exact SDistr.bind_const_mass_one hνmass _
        · rw [SDistr.pure_bind]
      rw [hk, SDistr.bind_pure]
    · intro b
      simp only [joint, SDistr.bind_assoc]
      have hk : (fun x => (if B x then ν.bind (fun y => SDistr.pure (x, y))
          else SDistr.pure (x, x)).bind fun p => SDistr.pure p.2) =
          fun x => if B x then ν else SDistr.pure x := by
        funext x
        split_ifs
        · rw [SDistr.bind_assoc]
          simp only [SDistr.pure_bind, SDistr.bind_pure]
        · rw [SDistr.pure_bind]
      rw [hk, SDistr.bind_apply_some]
      have hterm : ∀ a, d₁ (some a) * (if B a then ν else SDistr.pure a) (some b) =
          (if B a then d₁ (some a) else 0) * ν (some b) +
            (if a = b then (if B b then 0 else d₁ (some b)) else 0) := by
        intro a
        by_cases hab : a = b
        · subst hab
          by_cases ha : B a = true <;> simp [ha, SDistr.pure_apply_some]
        · by_cases ha : B a = true <;> simp [ha, hab, SDistr.pure_apply_some]
      have hm_top : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hm_le
      rw [tsum_congr hterm, ENNReal.tsum_add, ENNReal.tsum_mul_right, hm, tsum_ite_eq b, hν b]
      cases hB : B b
      · simp [hagree b hB]
      · simp only [ite_true, add_zero]
        rw [mul_comm (d₂ _), ← mul_assoc, ENNReal.mul_inv_cancel hm0 hm_top, one_mul]
    · intro x y hxy
      by_contra hcon
      push Not at hcon
      obtain ⟨hB, hne⟩ := hcon
      apply hxy
      simp only [joint]
      rw [SDistr.bind_apply_some]
      refine ENNReal.tsum_eq_zero.mpr fun a => ?_
      by_cases ha : B a = true
      · have hax : a ≠ x := fun h => by rw [h] at ha; exact hB ha
        simp only [ha, ↓reduceIte]
        rw [SDistr.bind_apply_some]
        refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun y' => ?_)
        simp [SDistr.pure_apply_some, hax]
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        refine mul_eq_zero_of_right _ ?_
        grind

/-- From an initial heap, binding `c` into `goodK bad` keeps the mass of the outcomes whose state
    is good and removes the others. -/
theorem bind_goodK_apply {α : Type} (c : SPComp (τ × α)) (bad : τ → Bool) (h : Heap)
    (x : (τ × α) × Heap) :
    (SPComp.bind c (goodK bad)) h (some x) = if bad x.1.1 then 0 else c h (some x) := by
  classical
  rw [SPComp.bind_def, SDistr.bind_apply_some, tsum_eq_single x]
  · obtain ⟨p, h'⟩ := x
    by_cases hb : bad p.1 <;>
      simp [goodK, hb, SPComp.fail, SPComp.pure, SDistr.fail_apply_some, SDistr.pure_apply_some]
  · rintro ⟨p', h''⟩ hx'
    by_cases hb : bad p'.1 <;>
      simp [goodK, hb, SPComp.fail, SPComp.pure, SDistr.fail_apply_some,
        SDistr.pure_apply_some, hx']

-- recovers UCTransparent.adv_le_prBad
example (R I : Sys τ E O) (bad : τ → Bool)
    (hinit : R.init = I.init)
    (hR : ∀ t e, SPComp.NoFail (R.step t e)) (hI : ∀ t e, SPComp.NoFail (I.step t e))
    (hagree : ∀ t e, bad t = false →
      SPComp.bind (R.step t e) (goodK bad) = SPComp.bind (I.step t e) (goodK bad))
    (Z : Env (Strat ζ E O) ζ) :
    adv R I Z ≤ prBad R bad Z := by
  refine realizes_upto_bad_rel R I Eq bad hinit hR hI (fun t u e htu hbt => ?_) ζ Z
  subst htu
  intro h₁ h₂ heq
  have heq' : h₁ = h₂ := heq
  subst heq'
  have hc := liftR_or_eq_of_agree (fun p : (τ × O) × Heap => bad p.1.1) (hR t e h₁) (hI t e h₁)
    fun x hx => by
      have := congrArg (fun c : SPComp (τ × O) => c h₁ (some x)) (hagree t e hbt)
      grind only [bind_goodK_apply]
  refine liftR_mono (fun p q hpq => ?_) hc
  rcases hpq with hb | rfl
  · exact Or.inl hb
  · exact Or.inr ⟨rfl, rfl, rfl⟩

/-! ## Error budgets in the relation -/

/-- **Up-to-bad rule for one coupling.** An exact coupling of `c₁` and `c₂` whose pairs satisfy
    `B` on the left or `Ψ` is an `rHoareApprox ε` judgment for `Ψ`, when the probability that
    `c₁` returns a value satisfying `B` is at most `ε` from every heap of the precondition. -/
theorem rHoareApprox_of_rHoare_or {α β : Type} {Φ : RPre} {Ψ : RPost α β} {c₁ : SPComp α}
    {c₂ : SPComp β} {ε : ℝ≥0∞} (B : α → Bool)
    (h : rHoare Φ c₁ c₂ fun a h₁ b h₂ => B a = true ∨ Ψ a h₁ b h₂)
    (hB : ∀ h₁ h₂, Φ h₁ h₂ → prTrue (SPComp.bind c₁ fun a => SPComp.pure (B a)) h₁ ≤ ε) :
    rHoareApprox ε Φ c₁ c₂ Ψ := by
  intro h₁ h₂ hΦ
  obtain ⟨c, hc⟩ := h h₁ h₂ hΦ
  have h' := liftRApprox_of_coupling_or (fun p => B p.1) (fun p q => Ψ p.1 p.2 q.1 q.2) c hc
  refine liftRApprox_mono_eps ?_ h'
  simpa only [prTrue_bind_pure_eq] using hB h₁ h₂ hΦ

/-- **Graded runs from budgets.** If from states related at budget `c` every activation is an
    `rHoareApprox (c - c')` judgment whose post relates the new states at a budget `c' ≤ c`, then
    the joint runs from states related at budget `c` are an `rHoareApprox c` judgment, whatever
    the number of activations. -/
theorem loop_rHoareApprox_budget (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → ℝ≥0∞ → Prop)
    (hstep : ∀ t u c e, rel t u c → ∃ c' ≤ c,
      rHoareApprox (c - c') eqPre (R.step t e) (I.step u e) (stepPost fun t' u' => rel t' u' c'))
    (bad : τ → Bool) (bad' : υ → Bool) (Z : Strat ζ E O) :
    ∀ (n : ℕ) z t u c b b', rel t u c →
      rHoareApprox c eqPre (loop R bad Z n (z, t, b)) (loop I bad' Z n (z, u, b'))
        (loopPost fun t' u' => ∃ c', rel t' u' c') := by
  intro n
  induction n with
  | zero =>
    intro z t u c b b' hr
    refine rHoareApprox_mono_eps (by simp) (rHoareApprox_of_rHoare ?_)
    exact rHoare_ret fun h h' heq => ⟨heq, rfl, c, hr⟩
  | succ n ih =>
    intro z t u c b b' hr
    simp only [loop]
    refine rHoareApprox_mono_eps (le_of_eq (zero_add c)) (rHoareApprox_bind (ε₂ := c)
      (rHoareApprox_refl_of_pre (Z.next z) fun _ _ h => h) fun a a' => ?_)
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.1) fun ha => ?_
    subst ha
    obtain ⟨c', hc', hj⟩ := hstep t u c a.2 hr
    refine rHoareApprox_mono_eps (le_of_eq (by rw [zero_add, tsub_add_cancel_of_le hc']))
      (rHoareApprox_bind (Ψ := stepPost fun t' u' => rel t' u' c') (ε₂ := 0 + c')
        (rHoareApprox_conseq (fun _ _ hh => hh.2) (fun _ _ _ _ => id) le_rfl hj) fun p q => ?_)
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.2) fun ⟨hpq, ho⟩ => ?_
    rw [← ho]
    refine rHoareApprox_bind (ε₂ := c')
      (rHoareApprox_refl_of_pre (Z.obs a.1 p.2) fun _ _ hh => hh.1) fun z₁ z₂ => ?_
    refine rHoareApprox_of_pre_fact (fun _ _ hh => hh.1) fun hz => ?_
    subst hz
    exact rHoareApprox_conseq (fun _ _ hh => hh.2) (fun _ _ _ _ => id) le_rfl
      (ih _ _ _ _ _ _ hpq)

/-- **Realization from error budgets.** Let `rel : τ → υ → ℝ≥0∞ → Prop` relate the states of `R`
    and `I` together with a remaining error budget. If the initial states are related at budget
    `c₀` and every activation from states related at budget `c` is an `rHoareApprox (c - c')`
    judgment whose post relates the new states at a budget `c' ≤ c`, with equal heaps and
    outputs, then `R` realizes `I` with bound `c₀`. The error of an activation is paid from the
    budget, so the bound is a sum of per-activation errors that may depend on the states. -/
theorem realizes_of_budget (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → ℝ≥0∞ → Prop)
    (c₀ : ℝ≥0∞) (hinit : rel R.init I.init c₀)
    (hstep : ∀ t u c e, rel t u c → ∃ c' ≤ c,
      rHoareApprox (c - c') eqPre (R.step t e) (I.step u e) (stepPost fun t' u' => rel t' u' c')) :
    Realizes R I (fun _ _ => c₀) := by
  intro ζ Z
  have hv : rHoareApprox c₀ eqPre (view R Z.input) (view I Z.input) eqPost := by
    unfold view run SPComp.map
    refine rHoareApprox_mono_eps (le_of_eq (add_zero _)) (rHoareApprox_bind
      (loop_rHoareApprox_budget R I rel hstep _ _ Z.input _ _ _ _ _ _ _ hinit) fun c d => ?_)
    exact rHoareApprox_of_rHoare (rHoare_ret fun h h' hh => ⟨hh.2.1, hh.1⟩)
  exact rHoareApprox_absDiff_prTrue hv Z.dist Z.heap

/-! ## A counter-indexed sampler -/

section CounterSampler

variable (D : Type) [Fintype D] [Nonempty D] [DecidableEq D]

/-- The real counter-indexed sampler: the state counts the queries; on each of the first `q`
    queries it samples a uniform guess in `D` and outputs whether the guess is the target `x₀`;
    afterwards it outputs `false`. -/
noncomputable def counterSampler (q : ℕ) (x₀ : D) : Sys ℕ Unit Bool where
  init := 0
  step k _ := if k < q then
      SPComp.bind (SPComp.sample D) fun x => SPComp.pure (k + 1, decide (x = x₀))
    else SPComp.pure (k, false)

/-- The ideal counter: the state counts the first `q` queries and the output is `false`. -/
noncomputable def counterIdeal (q : ℕ) : Sys ℕ Unit Bool where
  init := 0
  step k _ := if k < q then SPComp.pure (k + 1, false) else SPComp.pure (k, false)

/-- **Per-query budgets for a guessing sampler.** The counter-indexed sampler with `q` queries
    realizes the ideal counter with bound `q * (card D)⁻¹`, from the budget
    `(q - k) * (card D)⁻¹` at counter `k`; each query pays the probability `(card D)⁻¹` that
    its guess hits the target. -/
theorem counterSampler_realizes (q : ℕ) (x₀ : D) :
    Realizes (counterSampler D q x₀) (counterIdeal q)
      (fun _ _ => q * (Fintype.card D : ℝ≥0∞)⁻¹) := by
  set p := (Fintype.card D : ℝ≥0∞)⁻¹ with hp
  refine realizes_of_budget _ _ (fun k k' c => k = k' ∧ ((q - k : ℕ) : ℝ≥0∞) * p ≤ c) _
    ⟨rfl, by simp [counterSampler]⟩ ?_
  rintro k k' c e ⟨rfl, hc⟩
  by_cases hk : k < q
  · refine ⟨((q - (k + 1) : ℕ) : ℝ≥0∞) * p, ?_, ?_⟩
    · exact le_trans (mul_le_mul_left (Nat.cast_le.mpr (by omega)) _) hc
    · have hsplit : ((q - k : ℕ) : ℝ≥0∞) * p = p + ((q - (k + 1) : ℕ) : ℝ≥0∞) * p := by
        rw [show q - k = (q - (k + 1)) + 1 by omega]
        push_cast
        ring
      have htop : ((q - (k + 1) : ℕ) : ℝ≥0∞) * p ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr (by simp))
      refine rHoareApprox_mono_eps
        (ENNReal.le_sub_of_add_le_right htop (by rw [← hsplit]; exact hc)) ?_
      simp only [counterSampler, counterIdeal, hk, ↓reduceIte]
      refine rHoareApprox_of_rHoare_or (fun a => a.2) ?_ ?_
      · refine rHoare_sample_l fun x => rHoare_ret fun h h' heq => ?_
        by_cases hx : x = x₀
        · exact Or.inl (by simp [hx])
        · exact Or.inr ⟨heq, ⟨rfl, le_rfl⟩, by simp [hx]⟩
      · intro h₁ _ _
        rw [SPComp.bind_assoc]
        simp only [SPComp.pure_bind]
        rw [prTrue_bind_sample]
        simp [prTrue_pure, hp]
  · refine ⟨c, le_rfl, ?_⟩
    simp only [counterSampler, counterIdeal, hk, ↓reduceIte, tsub_self]
    exact rHoareApprox_of_rHoare (rHoare_ret fun h h' heq => ⟨heq, ⟨rfl, hc⟩, rfl⟩)

end CounterSampler

/-- **The `q · 2⁻ⁿ` guessing bound.** The counter-indexed sampler over `Fin (2 ^ n)` with `q`
    queries realizes the ideal counter with bound `q * (2 ^ n)⁻¹`. -/
theorem counterSampler_realizes_pow (n q : ℕ) (x₀ : Fin (2 ^ n)) :
    Realizes (counterSampler (Fin (2 ^ n)) q x₀) (counterIdeal q)
      (fun _ _ => q * ((2 : ℝ≥0∞) ^ n)⁻¹) := by
  simpa using counterSampler_realizes (Fin (2 ^ n)) q x₀

end CatCrypt.Crypto.UCCoupling

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentHybrid

@[expose] public section
set_option autoImplicit false

/-!
# Adversary systems for transparent realization

The systems of `CatCryptCore.Crypto.UCTransparent` have events `Event P AP = P ⊕ AP` and, in
this file, outputs `Oh × Lk`: an honest output and a leakage. An adversary system sits between
the environment and the adversary interface of such a system: it turns the adversary inputs
`AI` of the environment into adversary events `AP` of the system (`act`) and the leakage `Lk`
of the system into the leakage `Lk'` shown to the environment (`out`).

## Main definitions

* `AdvSys α AI AP Lk Lk'` — an adversary system with state `α` and lossless `act` and `out`.
* `AdvSys.toHybrid` — the adversary system as a `Hybrid` protocol whose subroutine is the
  system it is attached to.
* `Sys.attach R A` — the system `R` with the adversary system `A` attached.
* `Strat.absorb Z A`, `UCConcrete.Env.absorb Z A` — the environment `Z` running `A` itself
  against the adversary interface of the unattached system.
* `Sys.sampleFirst c S` — the system that samples `x` from `c` in its first step and then runs
  `S x`.
* `prFinal S q Z` — the probability that the final state of the run of `Z` against `S`
  satisfies `q`.
* `SPComp.atHeap h c` — the computation `c` run from the heap `h`.

## Main results

* `view_attach` — the view of `Z` against `R.attach A` is the first component of the view of
  `Z.absorb A` against `R`.
* `adv_attach` — the advantage between two attached systems is the advantage of the absorbed
  environment between the unattached systems.
* `Realizes.attach` (dummy-adversary completeness) — a realization of `I` by `R` gives a
  realization of `I.attach A` by `R.attach A`, with the bound at the absorbed environment;
  `realizesBound_attach` is the class-route instance.
* `run_sampleFirst`, `view_sampleFirst` — the run against `Sys.sampleFirst c S` is the average
  over `x ← c` of the runs against `S x`, for a heap-independent `c`.
* `run_bind_firstSample`, `prFinal_firstSample` — a system whose first step samples `x` from a
  heap-independent `c` and then steps as `T x`, and which steps as every `T x` afterwards, runs
  as the average over `x ← c` of the runs against `T x`.
* `prTrue_bind_atHeap` — a bind after `SPComp.atHeap h c` accepts with the probability of the
  bind after `c` from `h`.
* `prBad_le_of_monotone` — when no step leaves the bad states, the probability of the bad flag
  is at most the probability that the final state is bad.
-/

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Adversary systems -/

/-- An adversary system with state `α`: from an adversary input `AI` of the environment it
    produces an adversary event `AP` of the system (`act`), and from a leakage `Lk` of the
    system the leakage `Lk'` shown to the environment (`out`). Both are lossless. -/
structure AdvSys (α AI AP Lk Lk' : Type) where
  /-- Initial state. -/
  init : α
  /-- From an adversary input, the adversary event of the system. -/
  act : α → AI → SPComp (α × AP)
  /-- From a leakage of the system, the leakage shown to the environment. -/
  out : α → Lk → SPComp (α × Lk')
  /-- `act` never fails. -/
  act_noFail : ∀ a i, SPComp.NoFail (act a i)
  /-- `out` never fails. -/
  out_noFail : ∀ a l, SPComp.NoFail (out a l)

namespace AdvSys

variable {α AI AP Lk Lk' P Oh : Type}

/-- The event of the system for an event of the environment: honest events pass unchanged,
    adversary inputs go through `act`. -/
noncomputable def pre (A : AdvSys α AI AP Lk Lk') (a : α) :
    Event P AI → SPComp (α × Event P AP)
  | .inl p => SPComp.pure (a, .inl p)
  | .inr i => SPComp.bind (A.act a i) fun b => SPComp.pure (b.1, .inr b.2)

/-- The output shown to the environment: the honest output unchanged, the leakage through
    `out`. -/
noncomputable def post (A : AdvSys α AI AP Lk Lk') (a : α) (o : Oh × Lk) :
    SPComp (α × (Oh × Lk')) :=
  SPComp.bind (A.out a o.2) fun r => SPComp.pure (r.1, (o.1, r.2))

/-- The adversary system as a hybrid protocol: its subroutine is the system it is attached
    to. -/
noncomputable def toHybrid (A : AdvSys α AI AP Lk Lk') :
    Hybrid α (Event P AI) (Oh × Lk') (Event P AP) (Oh × Lk) where
  init := A.init
  pre := A.pre
  post := A.post
  pre_noFail a e := by
    cases e with
    | inl p => exact SPComp.pure_noFail _
    | inr i =>
      unfold AdvSys.pre
      exact Assumptions.SPComp.bind_noFail (A.act_noFail _ _) fun _ => SPComp.pure_noFail _
  post_noFail a o :=
    Assumptions.SPComp.bind_noFail (A.out_noFail _ _) fun _ => SPComp.pure_noFail _

end AdvSys

variable {α AI AP Lk Lk' P Oh τ υ ζ : Type}

/-- The system `R` with the adversary system `A` attached to its adversary interface. Its
    state is the pair of the state of `A` and the state of `R`. -/
noncomputable def Sys.attach (R : Sys τ (Event P AP) (Oh × Lk)) (A : AdvSys α AI AP Lk Lk') :
    Sys (α × τ) (Event P AI) (Oh × Lk') :=
  A.toHybrid.withSub R

/-- The environment `Z` with the adversary system `A` absorbed: it runs `A` against the
    adversary interface of the unattached system. -/
noncomputable def Strat.absorb (Z : Strat ζ (Event P AI) (Oh × Lk')) (A : AdvSys α AI AP Lk Lk') :
    Strat (ζ × α) (Event P AP) (Oh × Lk) :=
  A.toHybrid.reduce Z

/-- The `UCConcrete.Env` with the adversary system `A` absorbed: absorbed strategy, same heap,
    and the distinguisher applied to the state of `Z`. -/
noncomputable def _root_.CatCrypt.Crypto.UCConcrete.Env.absorb
    (Z : Env (Strat ζ (Event P AI) (Oh × Lk')) ζ) (A : AdvSys α AI AP Lk Lk') :
    Env (Strat (ζ × α) (Event P AP) (Oh × Lk)) (ζ × α) :=
  A.toHybrid.reduceEnv Z

/-- The view of `Z` against `R.attach A` is the first component of the view of `Z.absorb A`
    against `R`. -/
theorem view_attach (R : Sys τ (Event P AP) (Oh × Lk)) (A : AdvSys α AI AP Lk Lk')
    (Z : Strat ζ (Event P AI) (Oh × Lk')) :
    view (R.attach A) Z = SPComp.map Prod.fst (view R (Z.absorb A)) :=
  Hybrid.view_withSub _ _ _

/-- The advantage of `Z` between two systems with the same adversary system attached is the
    advantage of the absorbed environment between the unattached systems. -/
theorem adv_attach (R : Sys τ (Event P AP) (Oh × Lk)) (I : Sys υ (Event P AP) (Oh × Lk))
    (A : AdvSys α AI AP Lk Lk') (Z : Env (Strat ζ (Event P AI) (Oh × Lk')) ζ) :
    adv (R.attach A) (I.attach A) Z = adv R I (Z.absorb A) :=
  Hybrid.adv_withSub _ _ _ _

/-- **Dummy-adversary completeness** (composition plumbing). If `R` realizes `I` with bound
    `b`, then `R.attach A` realizes `I.attach A` with bound `b` at the absorbed environment. -/
theorem Realizes.attach {R : Sys τ (Event P AP) (Oh × Lk)} {I : Sys υ (Event P AP) (Oh × Lk)}
    {b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞} (h : Realizes R I b)
    (A : AdvSys α AI AP Lk Lk') :
    Realizes (R.attach A) (I.attach A) (fun ζ Z => b (ζ × α) (Z.absorb A)) := fun ζ Z => by
  change adv (R.attach A) (I.attach A) Z ≤ _
  rw [adv_attach]
  exact h (ζ × α) (Z.absorb A)

/-- Steps of `R.attach A` never fail when those of `R` never fail. -/
instance lossless_attach (R : Sys τ (Event P AP) (Oh × Lk)) (A : AdvSys α AI AP Lk Lk')
    [hR : Lossless R] : Lossless (R.attach A) :=
  ⟨Hybrid.withSub_noFail _ R hR.noFail⟩

/-- `Realizes.attach` on the class route (composition plumbing). -/
instance realizesBound_attach {R : Sys τ (Event P AP) (Oh × Lk)}
    {I : Sys υ (Event P AP) (Oh × Lk)} {A : AdvSys α AI AP Lk Lk'}
    {b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞} [h : RealizesBound R I b] :
    RealizesBound (R.attach A) (I.attach A) (fun ζ Z => b (ζ × α) (Z.absorb A)) :=
  ⟨h.realizes.attach A⟩

example (R : Sys τ (Event P AP) (Oh × Lk)) (I : Sys υ (Event P AP) (Oh × Lk))
    (A : AdvSys α AI AP Lk Lk') (b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞)
    [RealizesBound R I b] :
    RealizesBound (R.attach A) (I.attach A) (fun ζ Z => b (ζ × α) (Z.absorb A)) :=
  inferInstance

/-! ## Sampling in the first step -/

section SampleFirst

variable {β E O : Type}

/-- The step of `Sys.sampleFirst c S`: from the initial state `none` it samples `x` from `c`
    and takes the first step of `S x`; from `some (x, t)` it takes a step of `S x`. -/
noncomputable def sampleFirstStep (c : SPComp β) (S : β → Sys τ E O) :
    Option (β × τ) → E → SPComp (Option (β × τ) × O)
  | none, e => SPComp.bind c fun x =>
      SPComp.map (fun p => (some (x, p.1), p.2)) ((S x).step (S x).init e)
  | some q, e => SPComp.map (fun p => (some (q.1, p.1), p.2)) ((S q.1).step q.2 e)

/-- The system that samples `x` from `c` in its first step and then runs `S x`. -/
noncomputable def Sys.sampleFirst (c : SPComp β) (S : β → Sys τ E O) :
    Sys (Option (β × τ)) E O where
  init := none
  step := sampleFirstStep c S

/-- The bad predicate of `Sys.sampleFirst` for a family `bad x` of bad predicates of `S x`: the
    initial state is good. -/
def sampleFirstBad (bad : β → τ → Bool) : Option (β × τ) → Bool
  | none => false
  | some q => bad q.1 q.2

/-- After the first step the run against `Sys.sampleFirst c S` is the run against `S x`. -/
theorem loop_sampleFirst_some (c : SPComp β) (S : β → Sys τ E O) (bad : β → τ → Bool)
    (Z : Strat ζ E O) (x : β) (n : ℕ) (z : ζ) (t : τ) (b : Bool) :
    SPComp.map (fun q => (q.1, some (x, q.2.1), q.2.2)) (loop (S x) (bad x) Z n (z, t, b)) =
      loop (Sys.sampleFirst c S) (sampleFirstBad bad) Z n (z, some (x, t), b) :=
  loop_map (S x) (Sys.sampleFirst c S) (fun t => some (x, t)) (bad x) (sampleFirstBad bad) Z
    (fun _ _ => rfl) (fun _ => rfl) n (z, t, b)

/-- **Averaging over a first-step sample.** For a heap-independent `c` and an environment that
    activates the system at least once, the run against `Sys.sampleFirst c S` is the average
    over `x ← c` of the runs against `S x`, provided every `S x` starts in a good state. -/
theorem run_sampleFirst (c : SPComp β) (S : β → Sys τ E O) (bad : β → τ → Bool)
    (hc : SPComp.IsPure c) (hinit : ∀ x, bad x (S x).init = false) (Z : Strat ζ E O)
    (hZ : 0 < Z.rounds) :
    run (Sys.sampleFirst c S) (sampleFirstBad bad) Z =
      SPComp.bind c fun x =>
        SPComp.map (fun q => (q.1, some (x, q.2.1), q.2.2)) (run (S x) (bad x) Z) := by
  obtain ⟨n, hn⟩ : ∃ n, Z.rounds = n + 1 := ⟨Z.rounds - 1, by omega⟩
  have h1 : ∀ x, SPComp.map (fun q => (q.1, some (x, q.2.1), q.2.2)) (run (S x) (bad x) Z) =
      loop (Sys.sampleFirst c S) (sampleFirstBad bad) Z (n + 1)
        (Z.init, some (x, (S x).init), false) := by
    intro x
    unfold run
    rw [hn, hinit x]
    exact loop_sampleFirst_some c S bad Z x _ _ _ _
  simp_rw [h1]
  unfold run
  rw [hn]
  simp only [loop]
  rw [SPComp.isPure_bind_comm_left c (Z.next Z.init) _ hc]
  congr 1; funext a
  simp only [Sys.sampleFirst, sampleFirstStep, sampleFirstBad, SPComp.bind_assoc]

/-- The view against `Sys.sampleFirst c S` is the average over `x ← c` of the views against
    `S x`, for a heap-independent `c` and an environment that activates the system at least
    once. -/
theorem view_sampleFirst (c : SPComp β) (S : β → Sys τ E O) (hc : SPComp.IsPure c)
    (Z : Strat ζ E O) (hZ : 0 < Z.rounds) :
    view (Sys.sampleFirst c S) Z = SPComp.bind c fun x => view (S x) Z := by
  rw [view_eq_map_run _ (sampleFirstBad fun _ _ => false),
    run_sampleFirst c S (fun _ _ => false) hc (fun _ => rfl) Z hZ]
  simp only [view, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end SampleFirst

/-! ## A first-step sample in a family of systems -/

section FirstSample

variable {β E O : Type}

/-- **Averaging over a first-step sample of a family.** Let the first step of `S` sample `x`
from a heap-independent `c` and then take the first step of `T x` (`hfirst`), let `S` and
every `T x` have the same initial state, agree on the states outside `fresh` (`hstep`), and let
the steps of `T x` lead outside `fresh` (`hout`). For an environment that activates the system
at least once, the run against `S` is the average over `x ← c` of the runs against `T x`. -/
theorem run_bind_firstSample (c : SPComp β) (S : Sys τ E O) (T : β → Sys τ E O)
    (fresh bad : τ → Bool) (hc : SPComp.IsPure c) (hinit : ∀ x, (T x).init = S.init)
    (hfirst : ∀ e, S.step S.init e = SPComp.bind c fun x => (T x).step S.init e)
    (hstep : ∀ x t e, fresh t = false → S.step t e = (T x).step t e)
    (hout : ∀ x t e, SPComp.bind ((T x).step t e) (goodK fresh) = (T x).step t e)
    (Z : Strat ζ E O) (hZ : 0 < Z.rounds) :
    run S bad Z = SPComp.bind c fun x => run (T x) bad Z := by
  have hloop : ∀ x n z t b, fresh t = false →
      loop S bad Z n (z, t, b) = loop (T x) bad Z n (z, t, b) := by
    intro x n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro z t b ht
      simp only [loop]
      congr 1; funext a
      rw [hstep x t a.2 ht, ← hout x t a.2, SPComp.bind_assoc, SPComp.bind_assoc]
      congr 1; funext p
      unfold goodK
      by_cases hp : fresh p.1
      · simp [hp, SPComp.fail_bind]
      · simp only [hp, Bool.false_eq_true, ite_false, SPComp.pure_bind]
        congr 1; funext z'
        exact ih _ _ _ (by simpa using hp)
  obtain ⟨n, hn⟩ : ∃ n, Z.rounds = n + 1 := ⟨Z.rounds - 1, by omega⟩
  unfold run
  simp only [hinit, hn, loop]
  rw [SPComp.isPure_bind_comm_left c (Z.next Z.init) _ hc]
  congr 1; funext a
  rw [hfirst, SPComp.bind_assoc]
  congr 1; funext x
  rw [← hout x S.init a.2, SPComp.bind_assoc, SPComp.bind_assoc]
  congr 1; funext p
  unfold goodK
  by_cases hp : fresh p.1
  · simp [hp, SPComp.fail_bind]
  · simp only [hp, Bool.false_eq_true, ite_false, SPComp.pure_bind]
    congr 1; funext z'
    exact hloop x n _ _ _ (by simpa using hp)

/-- The probability that the final state of the run of `Z` against `S` satisfies `q`, from the
initial heap of `Z`. -/
noncomputable def prFinal (S : Sys τ E O) (q : τ → Bool) (Z : Env (Strat ζ E O) ζ) : ℝ≥0∞ :=
  prTrue (SPComp.bind (run S (fun _ => false) Z.input) fun c => SPComp.pure (q c.2.1)) Z.heap

/-- Under the hypotheses of `run_bind_firstSample`, the probability of a property of the final
state of the run against `S` is the probability over `x ← c` and the run against `T x`. -/
theorem prFinal_firstSample (c : SPComp β) (S : Sys τ E O) (T : β → Sys τ E O)
    (fresh : τ → Bool) (q : τ → Bool) (hc : SPComp.IsPure c) (hinit : ∀ x, (T x).init = S.init)
    (hfirst : ∀ e, S.step S.init e = SPComp.bind c fun x => (T x).step S.init e)
    (hstep : ∀ x t e, fresh t = false → S.step t e = (T x).step t e)
    (hout : ∀ x t e, SPComp.bind ((T x).step t e) (goodK fresh) = (T x).step t e)
    (Z : Env (Strat ζ E O) ζ) (hZ : 0 < Z.input.rounds) :
    prFinal S q Z = prTrue (SPComp.bind c fun x =>
      SPComp.bind (run (T x) (fun _ => false) Z.input) fun cf => SPComp.pure (q cf.2.1)) Z.heap := by
  unfold prFinal
  rw [run_bind_firstSample c S T fresh _ hc hinit hfirst hstep hout Z.input hZ, SPComp.bind_assoc]

end FirstSample

/-! ## Computations run from a fixed heap -/

/-- The computation `c` run from the heap `h`, whatever the heap it is started from. -/
def _root_.CatCrypt.Core.SPComp.atHeap {α : Type} (h : Heap) (c : SPComp α) : SPComp α :=
  fun _ => c h

/-- A bind after `c` run from the heap `h` accepts, from any heap, with the probability that the
bind after `c` accepts from `h`. -/
theorem prTrue_bind_atHeap {α : Type} (h h' : Heap) (c : SPComp α) (k : α → SPComp Bool) :
    prTrue (SPComp.bind (SPComp.atHeap h c) k) h' = prTrue (SPComp.bind c k) h := rfl

/-! ## Bad flags of monotone bad predicates -/

section Monotone

variable {E O : Type}

/-- The configurations whose flag is set while their state is good. -/
noncomputable def inconsK (bad : τ → Bool) (c : ζ × τ × Bool) : SPComp (ζ × τ × Bool) :=
  if c.2.2 && !bad c.2.1 then SPComp.pure c else SPComp.fail

/-- When no step leaves the bad states, the runs from a configuration whose flag is set only
    at a bad state never reach a configuration whose flag is set at a good state. -/
theorem loop_inconsK (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (hmono : ∀ t e, bad t = true → SPComp.bind (S.step t e) (goodK bad) = SPComp.fail) :
    ∀ n (c : ζ × τ × Bool), (c.2.2 = true → bad c.2.1 = true) →
      SPComp.bind (loop S bad Z n c) (inconsK bad) = SPComp.fail := by
  intro n
  induction n with
  | zero =>
    rintro ⟨z, t, b⟩ hc
    cases b <;> simp_all [loop, inconsK, SPComp.pure_bind]
  | succ n ih =>
    rintro ⟨z, t, b⟩ hc
    simp only [loop, SPComp.bind_assoc]
    cases b with
    | false =>
      have hf : ∀ (z' : ζ) (t' : τ),
          SPComp.bind (loop S bad Z n (z', t', false || bad t')) (inconsK bad) = SPComp.fail :=
        fun _ _ => ih _ (by simp)
      simp only [hf, bind_fail_right]
    | true =>
      have ht : bad t = true := hc rfl
      have hin : ∀ (a : ζ × E) (p : τ × O),
          SPComp.bind (Z.obs a.1 p.2) (fun z' =>
            SPComp.bind (loop S bad Z n (z', p.1, true || bad p.1)) (inconsK bad)) =
          SPComp.bind (goodK bad p) fun p' => SPComp.bind (Z.obs a.1 p'.2) fun z' =>
            SPComp.bind (loop S bad Z n (z', p'.1, true || bad p'.1)) (inconsK bad) := by
        intro a p
        by_cases hp : bad p.1
        · have hf : ∀ z' : ζ,
              SPComp.bind (loop S bad Z n (z', p.1, true || bad p.1)) (inconsK bad) =
                SPComp.fail := fun _ => ih _ (by simp [hp])
          simp only [hf, bind_fail_right]
          simp only [goodK, hp, ite_true, SPComp.fail_bind]
        · simp only [goodK, hp, Bool.false_eq_true, ite_false, SPComp.pure_bind]
      have key : ∀ a : ζ × E, SPComp.bind (S.step t a.2) (fun p =>
          SPComp.bind (Z.obs a.1 p.2) (fun z' =>
            SPComp.bind (loop S bad Z n (z', p.1, true || bad p.1)) (inconsK bad))) =
          SPComp.fail := by
        intro a
        calc _ = SPComp.bind (SPComp.bind (S.step t a.2) (goodK bad)) (fun p =>
              SPComp.bind (Z.obs a.1 p.2) (fun z' =>
                SPComp.bind (loop S bad Z n (z', p.1, true || bad p.1)) (inconsK bad))) := by
              rw [SPComp.bind_assoc]; congr 1; funext p; exact hin a p
          _ = SPComp.fail := by rw [hmono t _ ht, SPComp.fail_bind]
      simp only [key, bind_fail_right]

/-- **Bad flag of a monotone bad predicate.** When no step leads from a bad state to a good
    state, the probability that the bad flag is set at the end of the run is at most the
    probability that the final state is bad. -/
theorem prBad_le_of_monotone (S : Sys τ E O) (bad : τ → Bool)
    (hmono : ∀ t e, bad t = true → SPComp.bind (S.step t e) (goodK bad) = SPComp.fail)
    (Z : Env (Strat ζ E O) ζ) :
    prBad S bad Z ≤
      prTrue (SPComp.bind (run S bad Z.input) fun c => SPComp.pure (bad c.2.1)) Z.heap := by
  unfold prBad
  rw [prTrue_bind_split _ _ (fun c => c.2.2 && !bad c.2.1)]
  have hzero : SPComp.bind (run S bad Z.input) (fun c =>
      if (c.2.2 && !bad c.2.1) then SPComp.pure c.2.2 else SPComp.fail) = SPComp.fail := by
    have h := loop_inconsK S bad Z.input hmono Z.input.rounds (Z.input.init, S.init, bad S.init)
      (fun h => h)
    calc _ = SPComp.bind (SPComp.bind (run S bad Z.input) (inconsK bad))
          (fun c => SPComp.pure c.2.2) := by
          rw [SPComp.bind_assoc]; congr 1; funext c
          by_cases hc : (c.2.2 && !bad c.2.1) = true
          · simp [inconsK, hc, SPComp.pure_bind]
          · simp [inconsK, hc, SPComp.fail_bind]
      _ = SPComp.fail := by rw [run, h, SPComp.fail_bind]
  rw [hzero, prTrue_fail, add_zero]
  refine prTrue_bind_le_of_le _ _ _ _ fun c h' => ?_
  rcases c with ⟨z, t, b⟩
  cases b <;> cases hb : bad t <;> simp [prTrue_pure, prTrue_fail]

end Monotone

end CatCrypt.Crypto.UCTransparent

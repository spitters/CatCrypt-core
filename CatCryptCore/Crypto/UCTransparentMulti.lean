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
# Transitivity, distance-zero realization and multi-call hybrids

Three facts about transparent realization. Realization is transitive, with the bounds added
(`Realizes.trans`). Two systems realize each other at distance 0 when a state map commutes
with single steps (`realizes_zero_of_stepMap`), or when their steps from related states are
point masses with equal outputs and related successor states (`realizes_zero_of_stepRel`).

A multi-call hybrid protocol `π` reacts to an outer event by a finite interaction with its
subroutine: it issues a subroutine event, reads the answer, and from it either issues the
next subroutine event or ends the activation with an outer output. The interaction is given
as a state machine over the hybrid state `σ` (`start` on the outer event, `resume` on an
answer, `finish` on the answer to the last allowed call), so its unfolding on one outer event
is an interaction tree of depth at most `π.calls = π.fuel + 1`, each node a probabilistic
choice depending on all previous answers. `Hybrid` is the case of exactly one call, decided
before the answer: `MultiHybrid.ofHybrid` embeds it, and `MultiHybrid.view_ofHybrid_withSub`
states that the embedding composes with a subroutine to a system with the same view.

The environment of the subroutine obtained from an outer environment `Z` (`reduce`) runs
`π.calls` inner rounds per outer round. An activation that ends after fewer calls is padded
with an idle subroutine event `idle`; the composition theorems assume that every step of the
subroutine on `idle` leaves its state unchanged and outputs a fixed value (`IdleAt`).

## Main definitions

* `MultiHybrid σ E O EG OG` — a multi-call hybrid protocol or simulator.
* `MultiHybrid.drive` — the interaction of one activation with a subroutine system, with
  `fuel` calls left after the current one.
* `MultiHybrid.withSub π X` — `π` running with the subroutine system `X`.
* `MultiHybrid.ofHybrid` — a `Hybrid` as a one-call multi-call hybrid.
* `MultiHybrid.IdleAt X g o` — `X` stays in its state and outputs `o` on the event `g`.
* `MultiHybrid.reduce π idle Z` — the subroutine environment with `Z.rounds * π.calls` rounds;
  `MultiHybrid.reduceEnv` does the same for `UCConcrete.Env`.

## Main results

* `Realizes.trans` — transitivity of realization; the bounds add.
* `realizes_zero_of_stepMap` — two systems related by a state map that commutes with single
  steps realize one another at distance 0.
* `realizes_zero_of_stepRel` — two systems whose steps from related states are point masses
  with equal outputs and related states, from related initial states, realize each other at
  distance 0.
* `MultiHybrid.view_ofHybrid_withSub` — `(ofHybrid π).withSub X` and `π.withSub X` have the
  same view.
* `MultiHybrid.view_withSub` — the view of `Z` against `π.withSub X` is the first component of
  the view of `π.reduce idle Z` against `X`, when `X` is idle at `idle`.
* `MultiHybrid.adv_withSub` — the advantage of `Z` between `π.withSub X` and `π.withSub Y` is
  the advantage of the reduced environment between `X` and `Y`.
* `MultiHybrid.realizes_compose` — if `π.withSub Y` realizes `I` with bound `b₁` and `X`
  realizes `Y` with bound `b₂`, both idle at `idle`, then `π.withSub X` realizes `I` with bound
  `b₂` at the reduced environment plus `b₁`.
-/

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Transitivity and distance-zero realization -/

/-- Transitivity of realization: the bounds add. -/
theorem Realizes.trans {τ υ υ' E O : Type} {R : Sys τ E O} {I : Sys υ E O} {J : Sys υ' E O}
    {b₁ b₂ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h₁ : Realizes R I b₁) (h₂ : Realizes I J b₂) :
    Realizes R J (fun ζ Z => b₁ ζ Z + b₂ ζ Z) :=
  fun ζ => (h₁ ζ).triangle (h₂ ζ)

/-- Two systems related by a state map `f` that sends the initial state to the initial state
and commutes with single steps realize one another at distance 0. -/
theorem realizes_zero_of_stepMap {τ υ E O : Type} (R : Sys τ E O) (I : Sys υ E O) (f : τ → υ)
    (hinit : f R.init = I.init)
    (hstep : ∀ t e, SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = I.step (f t) e) :
    Realizes R I (fun _ _ => 0) := by
  intro ζ
  have hv : (view R : Strat ζ E O → SPComp ζ) = view I := by
    funext Z
    unfold view run
    have h := loop_map R I f (fun _ => false) (fun _ => false) Z hstep (fun _ => rfl)
      Z.rounds (Z.init, R.init, false)
    have h2 : SPComp.map Prod.fst (loop R (fun _ => false) Z Z.rounds (Z.init, R.init, false)) =
        SPComp.map Prod.fst (SPComp.map (fun c => (c.1, f c.2.1, c.2.2))
          (loop R (fun _ => false) Z Z.rounds (Z.init, R.init, false))) := by
      simp [SPComp.map, SPComp.bind_assoc]
    rw [h2, h, hinit]
  rw [hv]
  exact DistC.refl _

section StepRel

variable {τ υ ζ E O : Type}

/-- Runs from related states whose steps are point masses with equal outputs and related
states have equal views. -/
theorem map_fst_loop_of_stepRel (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop)
    (hstep : ∀ t u e, rel t u → ∃ t' u' o, R.step t e = SPComp.pure (t', o) ∧
      I.step u e = SPComp.pure (u', o) ∧ rel t' u')
    (bad : τ → Bool) (bad' : υ → Bool) (Z : Strat ζ E O) :
    ∀ n z t u b b', rel t u →
      SPComp.map Prod.fst (loop R bad Z n (z, t, b)) =
        SPComp.map Prod.fst (loop I bad' Z n (z, u, b')) := by
  intro n
  induction n with
  | zero => intro z t u b b' _; simp [loop, SPComp.map]
  | succ n ih =>
    intro z t u b b' h
    simp only [loop, SPComp.map, SPComp.bind_assoc] at ih ⊢
    congr 1; funext a
    obtain ⟨t', u', o, h1, h2, h3⟩ := hstep t u a.2 h
    rw [h1, h2]
    simp only [SPComp.pure_bind]
    congr 1; funext z'
    exact ih _ _ _ _ _ h3

/-- Two systems whose steps from related states are point masses with equal outputs and
related states, from related initial states, realize each other at distance `0`. -/
theorem realizes_zero_of_stepRel (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop)
    (hinit : rel R.init I.init)
    (hstep : ∀ t u e, rel t u → ∃ t' u' o, R.step t e = SPComp.pure (t', o) ∧
      I.step u e = SPComp.pure (u', o) ∧ rel t' u') :
    Realizes R I (fun _ _ => 0) := by
  intro ζ
  have hv : (view R : Strat ζ E O → SPComp ζ) = view I := by
    funext Z
    unfold view run
    exact map_fst_loop_of_stepRel R I rel hstep _ _ Z _ _ _ _ _ _ hinit
  rw [hv]
  exact DistC.refl _

end StepRel

/-! ## Multi-call hybrids -/

/-- A multi-call hybrid protocol with state `σ`, outer interface `(E, O)` and subroutine
    interface `(EG, OG)`. On an outer event, `start` chooses a subroutine event or the outer
    output; on each answer, `resume` chooses the next subroutine event or the outer output; the
    answer to call number `fuel + 1` goes to `finish`, which gives the outer output. -/
structure MultiHybrid (σ E O EG OG : Type) where
  /-- Initial state. -/
  init : σ
  /-- The number of calls per activation is at most `fuel + 1`. -/
  fuel : ℕ
  /-- From an outer event, the first subroutine event or the outer output. -/
  start : σ → E → SPComp (σ × (EG ⊕ O))
  /-- From a subroutine answer, the next subroutine event or the outer output. -/
  resume : σ → OG → SPComp (σ × (EG ⊕ O))
  /-- From the answer to the last allowed call, the outer output. -/
  finish : σ → OG → SPComp (σ × O)
  /-- `start` never fails. -/
  start_noFail : ∀ s e, SPComp.NoFail (start s e)
  /-- `resume` never fails. -/
  resume_noFail : ∀ s o, SPComp.NoFail (resume s o)
  /-- `finish` never fails. -/
  finish_noFail : ∀ s o, SPComp.NoFail (finish s o)

namespace MultiHybrid

variable {σ τ υ ζ E O EG OG : Type}

/-- The bound on the number of subroutine calls per activation. -/
def calls (π : MultiHybrid σ E O EG OG) : ℕ := π.fuel + 1

/-- The subroutine system `X` stays in its state and outputs `o` on the event `g`. -/
def IdleAt (X : Sys τ EG OG) (g : EG) (o : OG) : Prop :=
  ∀ t, X.step t g = SPComp.pure (t, o)

/-- The rest of one activation against `X` from the decision `d`, with `n` calls allowed
    after the next one: final hybrid state, subroutine state and outer output. -/
noncomputable def drive (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) :
    ℕ → σ → EG ⊕ O → τ → SPComp (σ × τ × O)
  | _, s, .inr o, t => SPComp.pure (s, t, o)
  | 0, s, .inl g, t =>
    SPComp.bind (X.step t g) fun q =>
      SPComp.bind (π.finish s q.2) fun r => SPComp.pure (r.1, q.1, r.2)
  | n + 1, s, .inl g, t =>
    SPComp.bind (X.step t g) fun q =>
      SPComp.bind (π.resume s q.2) fun r => drive π X n r.1 r.2 q.1

/-- The multi-call hybrid protocol `π` running with the subroutine system `X`. -/
noncomputable def withSub (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) :
    Sys (σ × τ) E O where
  init := (π.init, X.init)
  step t e :=
    SPComp.bind (π.start t.1 e) fun r =>
      SPComp.bind (π.drive X π.fuel r.1 r.2 t.2) fun p => SPComp.pure ((p.1, p.2.1), p.2.2)

/-- A hybrid protocol as a multi-call hybrid with one call per activation. -/
noncomputable def ofHybrid (π : Hybrid σ E O EG OG) : MultiHybrid σ E O EG OG where
  init := π.init
  fuel := 0
  start s e := SPComp.map (fun p => (p.1, Sum.inl p.2)) (π.pre s e)
  resume s o := SPComp.map (fun p => (p.1, Sum.inr p.2)) (π.post s o)
  finish := π.post
  start_noFail s e := Assumptions.SPComp.bind_noFail (π.pre_noFail s e) fun _ =>
    SPComp.pure_noFail _
  resume_noFail s o := Assumptions.SPComp.bind_noFail (π.post_noFail s o) fun _ =>
    SPComp.pure_noFail _
  finish_noFail := π.post_noFail

/-- The one-call multi-call hybrid of `π` composes with `X` to the hybrid composition. -/
theorem ofHybrid_withSub (π : Hybrid σ E O EG OG) (X : Sys τ EG OG) :
    (ofHybrid π).withSub X = π.withSub X := by
  simp only [withSub, Hybrid.withSub, ofHybrid]
  congr 1; funext t e
  simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, drive]

/-- `(ofHybrid π).withSub X` and `π.withSub X` have the same view. -/
theorem view_ofHybrid_withSub (π : Hybrid σ E O EG OG) (X : Sys τ EG OG) (Z : Strat ζ E O) :
    view ((ofHybrid π).withSub X) Z = view (π.withSub X) Z := by
  rw [ofHybrid_withSub]

/-- The state of the reduced environment: the state of `Z`, the hybrid state, and either the
    start of an outer round (`none`) or the current decision with the number of inner rounds
    left in the outer round after the current one. -/
abbrev RState (σ ζ EG O : Type) : Type := ζ × σ × Option ((EG ⊕ O) × ℕ)

/-- The subroutine event of a decision: the chosen event, or `idle` after the output. -/
def evOf (idle : EG) : EG ⊕ O → EG
  | .inl g => g
  | .inr _ => idle

/-- The choice of the next subroutine event in the reduced environment. -/
noncomputable def rnext (π : MultiHybrid σ E O EG OG) (idle : EG) (Z : Strat ζ E O) :
    RState σ ζ EG O → SPComp (RState σ ζ EG O × EG)
  | (z, s, none) =>
    SPComp.bind (Z.next z) fun a =>
      SPComp.bind (π.start s a.2) fun r =>
        SPComp.pure ((a.1, r.1, some (r.2, π.fuel)), evOf idle r.2)
  | (z, s, some (d, n)) => SPComp.pure ((z, s, some (d, n)), evOf idle d)

/-- The processing of a subroutine answer in the reduced environment. -/
noncomputable def robs (π : MultiHybrid σ E O EG OG) (Z : Strat ζ E O) :
    RState σ ζ EG O → OG → SPComp (RState σ ζ EG O)
  | (z, s, none), _ => SPComp.pure (z, s, none)
  | (z, s, some (.inl _, 0)), o =>
    SPComp.bind (π.finish s o) fun r =>
      SPComp.bind (Z.obs z r.2) fun z' => SPComp.pure (z', r.1, none)
  | (z, s, some (.inl _, n + 1)), o =>
    SPComp.bind (π.resume s o) fun r => SPComp.pure (z, r.1, some (r.2, n))
  | (z, s, some (.inr o, 0)), _ =>
    SPComp.bind (Z.obs z o) fun z' => SPComp.pure (z', s, none)
  | (z, s, some (.inr o, n + 1)), _ => SPComp.pure (z, s, some (.inr o, n))

/-- `rnext` never fails. -/
theorem rnext_noFail (π : MultiHybrid σ E O EG OG) (idle : EG) (Z : Strat ζ E O)
    (zs : RState σ ζ EG O) : SPComp.NoFail (π.rnext idle Z zs) := by
  rcases zs with ⟨z, s, _ | ⟨d, n⟩⟩
  · simp only [rnext]
    exact Assumptions.SPComp.bind_noFail (Z.next_noFail _) fun _ =>
      Assumptions.SPComp.bind_noFail (π.start_noFail _ _) fun _ => SPComp.pure_noFail _
  · simp only [rnext]
    exact SPComp.pure_noFail _

/-- `robs` never fails. -/
theorem robs_noFail (π : MultiHybrid σ E O EG OG) (Z : Strat ζ E O)
    (zs : RState σ ζ EG O) (o : OG) : SPComp.NoFail (π.robs Z zs o) := by
  rcases zs with ⟨z, s, _ | ⟨_ | _, _ | n⟩⟩ <;> simp only [robs]
  · exact SPComp.pure_noFail _
  · exact Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ =>
      Assumptions.SPComp.bind_noFail (Z.obs_noFail _ _) fun _ => SPComp.pure_noFail _
  · exact Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => SPComp.pure_noFail _
  · exact Assumptions.SPComp.bind_noFail (Z.obs_noFail _ _) fun _ => SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

/-- The environment for the subroutine obtained by running `Z` with `π`: `π.calls` inner
    rounds per outer round, idle events after an activation has produced its output. -/
noncomputable def reduce (π : MultiHybrid σ E O EG OG) (idle : EG) (Z : Strat ζ E O) :
    Strat (RState σ ζ EG O) EG OG where
  rounds := Z.rounds * π.calls
  init := (Z.init, π.init, none)
  next := π.rnext idle Z
  obs := π.robs Z
  next_noFail := π.rnext_noFail idle Z
  obs_noFail := π.robs_noFail Z

/-- The reduced `UCConcrete.Env`: reduced strategy, same heap, and the distinguisher applied
    to the state of `Z`. -/
noncomputable def reduceEnv (π : MultiHybrid σ E O EG OG) (idle : EG)
    (Z : Env (Strat ζ E O) ζ) : Env (Strat (RState σ ζ EG O) EG OG) (RState σ ζ EG O) :=
  ⟨π.reduce idle Z.input, Z.heap, fun zs => Z.dist zs.1⟩

/-- Joint runs compose sequentially in the number of rounds. -/
theorem loop_add (S : Sys τ EG OG) (bad : τ → Bool) (W : Strat ζ EG OG) :
    ∀ m n c, loop S bad W (m + n) c =
      SPComp.bind (loop S bad W m c) fun c' => loop S bad W n c' := by
  intro m
  induction m with
  | zero => intro n c; simp [loop, SPComp.pure_bind]
  | succ m ih =>
    intro n c
    rw [Nat.add_right_comm m 1 n]
    simp only [loop, SPComp.bind_assoc]
    congr 1; funext a; congr 1; funext p; congr 1; funext z
    exact ih _ _

/-- The inner rounds of one outer round from a pending decision: the rest of the
    activation, followed by the observation of the outer output by `Z`. -/
theorem loop_reduce_some (π : MultiHybrid σ E O EG OG) (idle : EG) (oidle : OG)
    (X : Sys τ EG OG) (hX : IdleAt X idle oidle) (Z : Strat ζ E O) :
    ∀ n (z : ζ) (s : σ) (d : EG ⊕ O) (t : τ) (b : Bool),
      loop X (fun _ => false) (π.reduce idle Z) (n + 1) ((z, s, some (d, n)), t, b) =
        SPComp.bind (π.drive X n s d t) fun p =>
          SPComp.bind (Z.obs z p.2.2) fun z' => SPComp.pure ((z', p.1, none), p.2.1, b) := by
  intro n
  induction n with
  | zero =>
    intro z s d t b
    cases d <;>
      simp [loop, reduce, rnext, robs, evOf, drive, hX _, SPComp.bind_assoc, SPComp.pure_bind]
  | succ n ih =>
    intro z s d t b
    simp only [reduce] at ih
    cases d with
    | inl g =>
      rw [loop]
      simp only [reduce, rnext, robs, evOf, drive, SPComp.bind_assoc, SPComp.pure_bind,
        Bool.or_false, ih]
    | inr o =>
      rw [loop]
      simp only [reduce, rnext, robs, evOf, drive, hX _, SPComp.pure_bind, Bool.or_false, ih]

/-- The inner rounds of one outer round: one step of `π.withSub X` between the choice and
    the observation of `Z`. -/
theorem loop_reduce_none (π : MultiHybrid σ E O EG OG) (idle : EG) (oidle : OG)
    (X : Sys τ EG OG) (hX : IdleAt X idle oidle) (Z : Strat ζ E O)
    (z : ζ) (s : σ) (t : τ) (b : Bool) :
    loop X (fun _ => false) (π.reduce idle Z) π.calls ((z, s, none), t, b) =
      SPComp.bind (Z.next z) fun a =>
        SPComp.bind ((π.withSub X).step (s, t) a.2) fun p =>
          SPComp.bind (Z.obs a.1 p.2) fun z' => SPComp.pure ((z', p.1.1, none), p.1.2, b) := by
  have h := loop_reduce_some π idle oidle X hX Z π.fuel
  simp only [reduce] at h ⊢
  rw [calls, loop]
  simp only [rnext, withSub, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext a; congr 1; funext r
  rw [← h]
  rw [loop]
  simp only [rnext, SPComp.pure_bind, Bool.or_false]
  rfl

/-- The run against the composed system is the run of the reduced environment against the
    subroutine, up to regrouping the configuration. -/
theorem loop_withSub (π : MultiHybrid σ E O EG OG) (idle : EG) (oidle : OG)
    (X : Sys τ EG OG) (hX : IdleAt X idle oidle) (Z : Strat ζ E O) :
    ∀ n (c : ζ × (σ × τ) × Bool),
      SPComp.map (fun c => ((c.1, c.2.1.1, none), c.2.1.2, c.2.2))
          (loop (π.withSub X) (fun _ => false) Z n c) =
        loop X (fun _ => false) (π.reduce idle Z) (n * π.calls)
          ((c.1, c.2.1.1, none), c.2.1.2, c.2.2) := by
  intro n
  induction n with
  | zero => intro c; simp [loop, SPComp.map]
  | succ n ih =>
    intro c
    rw [Nat.succ_mul, Nat.add_comm (n * π.calls), loop_add X _ _ π.calls,
      loop_reduce_none π idle oidle X hX Z]
    simp only [loop, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Bool.or_false] at ih ⊢
    congr 1; funext a; congr 1; funext p; congr 1; funext z
    exact ih _

/-- The view of `Z` against `π.withSub X` is the first component of the view of
    `π.reduce idle Z` against `X`. -/
theorem view_withSub (π : MultiHybrid σ E O EG OG) (idle : EG) (oidle : OG)
    (X : Sys τ EG OG) (hX : IdleAt X idle oidle) (Z : Strat ζ E O) :
    view (π.withSub X) Z = SPComp.map Prod.fst (view X (π.reduce idle Z)) := by
  unfold view run
  have h := loop_withSub π idle oidle X hX Z Z.rounds (Z.init, (π.withSub X).init, false)
  have h2 : SPComp.map Prod.fst (loop (π.withSub X) (fun _ => false) Z Z.rounds
      (Z.init, (π.withSub X).init, false)) =
      SPComp.map Prod.fst (SPComp.map Prod.fst (SPComp.map
        (fun c => (((c.1, c.2.1.1, none) : RState σ ζ EG O), c.2.1.2, c.2.2))
        (loop (π.withSub X) (fun _ => false) Z Z.rounds (Z.init, (π.withSub X).init, false)))) := by
    simp [SPComp.map, SPComp.bind_assoc]
  rw [h2, h]; rfl

/-- The advantage of `Z` between `π.withSub X` and `π.withSub Y` is the advantage of the
    reduced environment between `X` and `Y`. -/
theorem adv_withSub (π : MultiHybrid σ E O EG OG) (idle : EG) (oX oY : OG)
    (X : Sys τ EG OG) (Y : Sys υ EG OG) (hX : IdleAt X idle oX) (hY : IdleAt Y idle oY)
    (Z : Env (Strat ζ E O) ζ) :
    adv (π.withSub X) (π.withSub Y) Z = adv X Y (π.reduceEnv idle Z) := by
  rw [adv_eq, adv_eq, view_withSub π idle oX X hX, view_withSub π idle oY Y hY]
  simp [reduceEnv, SPComp.map, SPComp.bind_assoc]

/-- **Multi-call hybrid composition** (composition plumbing). If `π.withSub Y` realizes `I`
    with bound `b₁` and `X` realizes `Y` with bound `b₂`, and `X` and `Y` are idle at `idle`,
    then `π.withSub X` realizes `I` with the sum of `b₂` at the reduced environment and
    `b₁`. -/
theorem realizes_compose {υ' : Type} (π : MultiHybrid σ E O EG OG) (idle : EG) (oX oY : OG)
    (X : Sys τ EG OG) (Y : Sys υ EG OG) (I : Sys υ' E O)
    (hX : IdleAt X idle oX) (hY : IdleAt Y idle oY)
    (b₁ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (b₂ : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞)
    (h₁ : Realizes (π.withSub Y) I b₁) (h₂ : Realizes X Y b₂) :
    Realizes (π.withSub X) I
      (fun ζ Z => b₂ (RState σ ζ EG O) (π.reduceEnv idle Z) + b₁ ζ Z) := by
  intro ζ
  have hsub : DistC (view (π.withSub X) (ζ := ζ)) (view (π.withSub Y))
      (fun Z => b₂ (RState σ ζ EG O) (π.reduceEnv idle Z)) := fun Z => by
    have := adv_withSub π idle oX oY X Y hX hY Z
    unfold adv at this
    rw [this]
    exact h₂ (RState σ ζ EG O) (π.reduceEnv idle Z)
  exact hsub.triangle (h₁ ζ)

end MultiHybrid

end CatCrypt.Crypto.UCTransparent

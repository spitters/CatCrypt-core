/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCInterleave
public import CatCryptCore.Category.ProtBicatReactive
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Parallel composition and the two-call pipe of reactive systems

The parallel composition `X.par Y` of closed systems `X : Sys τ E O` and `Y : Sys υ E' O'` runs
them side by side on the sum interface: an event `inl e` activates `X`, an event `inr e'`
activates `Y`, and the output carries the tag of the event. Each component is an open system
over the other: `X.par Y` is `(parCtxL Y hY).withSub X` up to the order of the state, and
`(parCtxR X hX).withSub Y` exactly, for the one-call multi-call hybrids `parCtxL` and `parCtxR`
that run the other component inside the activation. Realizations compose in parallel with the
sum of the bounds at the environments reduced through these contexts (`realizes_par`); behind
the tensor of two opaque multi-call simulators of equal fuel this is `RealizesSim.par`. The
tensor of multi-call hybrids is the parallel composition of their composites with the components
of a parallel subroutine (`realizes_tensor_withSub_par`).

The two-call pipe `X.pipe Y route post` is the multi-call hybrid `pipeHybrid route post` of fuel
`1` over `X.par Y`: one activation calls `X`, and either feeds the answer to `Y` (`route` gives
`inl`) or ends with an output (`route` gives `inr`); the answer of `Y` is mapped by `post`. For
one-shot protocols `p` and `q`, the pipe `Sys.hcompPipe p q` of `Sys.oneShot p` and
`Sys.oneShot q` realizes `Sys.oneShot` of the horizontal composite `ProtObj.hcomp` at distance
`0` (`realizes_hcompPipe`). The bound of `sdist_hcomp` and the horizontal composite of
approximate 2-cells (`ProtMorε.hcomp`) become realizations between pipes
(`realizes_hcompPipe_of_sdist`, `realizesSim_hcompPipe`).

The merge `G.merge` of a system `G` serves two ports with one copy of `G`; it answers each event
on the port of the event (`Sys.merge_portTyped`).

The realizations between systems of one interface form a category with hom-types
`{b // Realizes X Y b}` (`SysObj.category`), and the open systems form a category on interfaces
(`UCIface.category`).

## Main definitions

* `Sys.par`, `MultiHybrid.parCtxL`, `MultiHybrid.parCtxR`: parallel composition and its
  contexts.
* `MultiHybrid.pipeHybrid`, `Sys.pipe`, `Sys.hcompPipe`: the two-call pipe.
* `Sys.merge`: two ports onto one system.
* `SysObj`, `UCIface`: the objects of the two categories.

## Main results

* `realizes_par`, `RealizesSim.par`: realizations compose in parallel.
* `realizes_tensor_withSub_par`: the tensor over a parallel composition.
* `realizes_hcompPipe`, `realizes_hcompPipe_of_sdist`, `realizesSim_hcompPipe`: the pipe as the
  reactive form of `ProtObj.hcomp`.
* `realizes_zero_of_stepMap_on`: distance-`0` realization from a state map on an invariant.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Distance-zero realization from state maps -/

section StepMap

variable {τ υ ζ E O : Type}

/-- Two systems related by a state map `f` that sends the initial state to the initial state and
commutes with single steps have equal views. -/
theorem view_eq_of_stepMap (R : Sys τ E O) (I : Sys υ E O) (f : τ → υ)
    (hinit : f R.init = I.init)
    (hstep : ∀ t e, SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = I.step (f t) e)
    (Z : Strat ζ E O) : view R Z = view I Z := by
  unfold view run
  have h := loop_map R I f (fun _ => false) (fun _ => false) Z hstep (fun _ => rfl)
    Z.rounds (Z.init, R.init, false)
  have h2 : SPComp.map Prod.fst (loop R (fun _ => false) Z Z.rounds (Z.init, R.init, false)) =
      SPComp.map Prod.fst (SPComp.map (fun c => (c.1, f c.2.1, c.2.2))
        (loop R (fun _ => false) Z Z.rounds (Z.init, R.init, false))) := by
    simp [SPComp.map, SPComp.bind_assoc]
  rw [h2, h, hinit]

/-- The state `x` with its proof of `Inv` if `Inv x` holds, and `d` otherwise. -/
private noncomputable def liftInv (Inv : τ → Prop) (d : {t // Inv t}) (x : τ) :
    {t // Inv t} := by
  classical exact if h : Inv x then ⟨x, h⟩ else d

/-- The system `R` on the states satisfying `Inv`: each new state that fails `Inv` is replaced by
the initial state. -/
private noncomputable def restrictInv (R : Sys τ E O) (Inv : τ → Prop) (h : Inv R.init) :
    Sys {t // Inv t} E O where
  init := ⟨R.init, h⟩
  step t e := SPComp.map (fun p => (liftInv Inv ⟨R.init, h⟩ p.1, p.2)) (R.step t.1 e)

/-- Two systems related by a state map `f` realize one another at distance `0` when `f` sends
the initial state to the initial state and commutes with single steps from the states satisfying
an invariant `Inv`, which holds initially and at every state a step from a state satisfying it
reaches. -/
theorem realizes_zero_of_stepMap_on (R : Sys τ E O) (I : Sys υ E O) (Inv : τ → Prop)
    (f : τ → υ) (hInv : Inv R.init) (hinit : f R.init = I.init)
    (hpres : ∀ t e, Inv t → ∃ (α : Type) (c : SPComp α) (g : α → τ × O),
      R.step t e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧ ∀ a, Inv (g a).1)
    (hstep : ∀ t e, Inv t → SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = I.step (f t) e) :
    Realizes R I (fun _ _ => 0) := by
  have hnorm : ∀ (t : {t // Inv t}) e,
      SPComp.map (fun p => ((liftInv Inv ⟨R.init, hInv⟩ p.1).1, p.2)) (R.step t.1 e) =
        R.step t.1 e := by
    intro t e
    obtain ⟨α, c, g, hc, hg⟩ := hpres t.1 e t.2
    rw [hc]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, liftInv, dite_eq_left (hg _)]
  have h₁ : Realizes (restrictInv R Inv hInv) R (fun _ _ => 0) :=
    realizes_zero_of_stepMap _ _ Subtype.val rfl fun t e => by
      have h := hnorm t e
      simp only [restrictInv, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] at h ⊢
      exact h
  have h₂ : Realizes (restrictInv R Inv hInv) I (fun _ _ => 0) :=
    realizes_zero_of_stepMap _ _ (fun t : {t // Inv t} => f t.1) hinit fun t e => by
      rw [← hstep t.1 e t.2]
      conv => rhs; rw [← hnorm t e]
      simp only [restrictInv, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  exact fun ζ => ((h₁ ζ).symm.triangle (h₂ ζ)).mono fun _ => by simp

end StepMap

/-! ## Parallel composition -/

namespace Sys

variable {τ υ ρ E O E' O' : Type}

/-- The parallel composition of `X` and `Y` on the sum of their interfaces: an event `inl e`
activates `X`, an event `inr e'` activates `Y`, and the output carries the tag of the event. -/
noncomputable def par (X : Sys τ E O) (Y : Sys υ E' O') : Sys (τ × υ) (E ⊕ E') (O ⊕ O') where
  init := (X.init, Y.init)
  step s := Sum.elim
    (fun e => SPComp.map (fun q => ((q.1, s.2), Sum.inl q.2)) (X.step s.1 e))
    (fun e => SPComp.map (fun q => ((s.1, q.1), Sum.inr q.2)) (Y.step s.2 e))

/-- Unfolding lemma of `par`: a step on a left event. -/
@[simp] theorem par_step_inl (X : Sys τ E O) (Y : Sys υ E' O') (s : τ × υ) (e : E) :
    (X.par Y).step s (.inl e) =
      SPComp.map (fun q => ((q.1, s.2), Sum.inl q.2)) (X.step s.1 e) := rfl

/-- Unfolding lemma of `par`: a step on a right event. -/
@[simp] theorem par_step_inr (X : Sys τ E O) (Y : Sys υ E' O') (s : τ × υ) (e : E') :
    (X.par Y).step s (.inr e) =
      SPComp.map (fun q => ((s.1, q.1), Sum.inr q.2)) (Y.step s.2 e) := rfl

/-- The system `X` on the first component of the state `τ × ρ`, the second component
unchanged. -/
noncomputable def onFst (X : Sys τ E O) (r : ρ) : Sys (τ × ρ) E O where
  init := (X.init, r)
  step y e := SPComp.map (fun q => ((q.1, y.2), q.2)) (X.step y.1 e)

/-- Unfolding lemma of `Sys.onFst`: a step on the state `(t, a)`. -/
@[simp] theorem onFst_step (X : Sys τ E O) (r a : ρ) (t : τ) (e : E) :
    (X.onFst r).step (t, a) e = SPComp.map (fun q => ((q.1, a), q.2)) (X.step t e) := rfl

/-- The parallel composition answers every event on the port of the event. -/
theorem par_portTyped (X : Sys τ E O) (Y : Sys υ E' O') : (X.par Y).PortTyped :=
  ⟨X.onFst Y.init, Y.onSnd X.init, fun t e => by
    simp [Sys.onFst, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind], fun t e => by
    simp [Sys.onSnd, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]⟩

end Sys

namespace MultiHybrid

variable {σ τ υ ρ E O E' O' EG OG : Type}

/-- The context of `Y` beside a left subroutine: a left event is passed to the subroutine and its
answer returned, a right event is answered by a step of `Y` inside the activation. -/
noncomputable def parCtxL (Y : Sys υ E' O') (hY : ∀ u e, SPComp.NoFail (Y.step u e)) :
    MultiHybrid υ (E ⊕ E') (O ⊕ O') E O where
  init := Y.init
  fuel := 0
  start u := Sum.elim (fun e => SPComp.pure (u, .inl e))
    (fun e => SPComp.map (fun q => (q.1, .inr (.inr q.2))) (Y.step u e))
  resume u o := SPComp.pure (u, .inr (.inl o))
  finish u o := SPComp.pure (u, .inl o)
  start_noFail u e := by
    rcases e with e | e
    · exact SPComp.pure_noFail _
    · simp only [Sum.elim_inr, SPComp.map]
      exact Assumptions.SPComp.bind_noFail (hY u e) fun _ => SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The context of `X` beside a right subroutine: a left event is answered by a step of `X`
inside the activation, a right event is passed to the subroutine and its answer returned. -/
noncomputable def parCtxR (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e)) :
    MultiHybrid τ (E ⊕ E') (O ⊕ O') E' O' where
  init := X.init
  fuel := 0
  start t := Sum.elim (fun e => SPComp.map (fun q => (q.1, .inr (.inl q.2))) (X.step t e))
    (fun e => SPComp.pure (t, .inl e))
  resume t o := SPComp.pure (t, .inr (.inr o))
  finish t o := SPComp.pure (t, .inr o)
  start_noFail t e := by
    rcases e with e | e
    · simp only [Sum.elim_inl, SPComp.map]
      exact Assumptions.SPComp.bind_noFail (hX t e) fun _ => SPComp.pure_noFail _
    · exact SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The context of `X` over the right component is the parallel composition. -/
theorem parCtxR_withSub (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (Y : Sys υ E' O') : (parCtxR X hX).withSub Y = X.par Y := by
  simp only [withSub, Sys.par, parCtxR]
  congr 1
  funext s e
  rcases e with e | e <;>
    simp [drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The context of `Y` over the left component has the steps of the parallel composition, with
the components of the state exchanged. -/
theorem parCtxL_withSub_step (Y : Sys υ E' O') (hY : ∀ u e, SPComp.NoFail (Y.step u e))
    (X : Sys τ E O) (t : τ × υ) (e : E ⊕ E') :
    SPComp.map (fun p => (Prod.swap p.1, p.2)) ((X.par Y).step t e) =
      ((parCtxL Y hY).withSub X).step t.swap e := by
  rcases e with e | e <;>
    simp [withSub, parCtxL, drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The rest of an activation against `X.onFst r` is the rest of the activation against `X`,
with the second component of the subroutine state unchanged. -/
theorem drive_onFst (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (r : ρ) :
    ∀ n s d t (a : ρ), π.drive (X.onFst r) n s d (t, a) =
      SPComp.map (fun p => (p.1, (p.2.1, a), p.2.2)) (π.drive X n s d t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t a
    · simp [drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [drive]
  | succ n ih =>
    rintro s (g | o) t a
    · simp [drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, ih]
    · simp [drive]

/-- An activation against `X.onFst r` is an activation against `X`, with the second component of
the subroutine state unchanged. -/
theorem stepFuel_onFst (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (r : ρ) (n : ℕ)
    (s : σ) (t : τ) (a : ρ) (e : E) :
    π.stepFuel (X.onFst r) n (s, (t, a)) e =
      SPComp.map (fun p => ((p.1.1, (p.1.2, a)), p.2)) (π.stepFuel X n (s, t) e) := by
  simp [stepFuel, drive_onFst, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

section Par

variable {τ τ' υ υ' ζ E O E' O' : Type}

open MultiHybrid

/-- **Parallel composition, left component.** If `X` realizes `X'` with bound `b`, both idle at
`idle`, then `X.par Y` realizes `X'.par Y` with bound `b` at the environment reduced through the
context of `Y`. -/
theorem realizes_par_left {X : Sys τ E O} {X' : Sys τ' E O} (Y : Sys υ E' O')
    (hY : ∀ u e, SPComp.NoFail (Y.step u e)) (idle : E) {oX oX' : O}
    (hXi : IdleAt X idle oX) (hX'i : IdleAt X' idle oX')
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X X' b) :
    Realizes (X.par Y) (X'.par Y)
      (fun ζ Z => b (RState υ ζ E (O ⊕ O')) ((parCtxL Y hY).reduceEnv idle Z)) := by
  intro ζ Z
  have hv : ∀ {τ₀ : Type} (X₀ : Sys τ₀ E O),
      (view (X₀.par Y) : Strat ζ (E ⊕ E') (O ⊕ O') → SPComp ζ) =
        view ((parCtxL Y hY).withSub X₀) := fun X₀ =>
    funext (view_eq_of_stepMap _ _ Prod.swap rfl (parCtxL_withSub_step Y hY X₀))
  change Env.gap _ _ Z ≤ _
  rw [hv X, hv X']
  have ha := adv_withSub (parCtxL Y hY) idle oX oX' X X' hXi hX'i Z
  unfold adv at ha
  rw [ha]
  exact h _ _

/-- **Parallel composition, right component.** If `Y` realizes `Y'` with bound `b`, both idle at
`idle`, then `X.par Y` realizes `X.par Y'` with bound `b` at the environment reduced through the
context of `X`. -/
theorem realizes_par_right (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    {Y : Sys υ E' O'} {Y' : Sys υ' E' O'} (idle : E') {oY oY' : O'}
    (hYi : IdleAt Y idle oY) (hY'i : IdleAt Y' idle oY')
    {b : (ζ : Type) → Env (Strat ζ E' O') ζ → ℝ≥0∞} (h : Realizes Y Y' b) :
    Realizes (X.par Y) (X.par Y')
      (fun ζ Z => b (RState τ ζ E' (O ⊕ O')) ((parCtxR X hX).reduceEnv idle Z)) := by
  rw [← parCtxR_withSub X hX Y, ← parCtxR_withSub X hX Y']
  have h' := (Open.ofMultiHybrid (parCtxR X hX) idle).realizes_withSub ⟨oY, hYi⟩ ⟨oY', hY'i⟩ h
  exact fun ζ Z =>
    le_of_le_of_eq (h' ζ Z) (congrArg (b _) (Open.reduceEnv_ofMultiHybrid _ idle Z))

/-- **Parallel composition of realizations.** If `X` realizes `X'` with bound `bX` and `Y`
realizes `Y'` with bound `bY`, then `X.par Y` realizes `X'.par Y'` with the sum of `bX` at the
environment reduced through the context of `Y` and `bY` at the environment reduced through the
context of `X'`. The systems `Y` and `X'` run inside the reduced environments and are lossless;
the left systems are idle at `idleL` and the right ones at `idleR`. -/
theorem realizes_par {X : Sys τ E O} {X' : Sys τ' E O} {Y : Sys υ E' O'} {Y' : Sys υ' E' O'}
    (hY : ∀ u e, SPComp.NoFail (Y.step u e)) (hX' : ∀ t e, SPComp.NoFail (X'.step t e))
    (idleL : E) (idleR : E') {oX oX' : O} {oY oY' : O'}
    (hXi : IdleAt X idleL oX) (hX'i : IdleAt X' idleL oX')
    (hYi : IdleAt Y idleR oY) (hY'i : IdleAt Y' idleR oY')
    {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E' O') ζ → ℝ≥0∞}
    (hX : Realizes X X' bX) (hYr : Realizes Y Y' bY) :
    Realizes (X.par Y) (X'.par Y')
      (fun ζ Z => bX (RState υ ζ E (O ⊕ O')) ((parCtxL Y hY).reduceEnv idleL Z) +
        bY (RState τ' ζ E' (O ⊕ O')) ((parCtxR X' hX').reduceEnv idleR Z)) :=
  Realizes.trans (realizes_par_left Y hY idleL hXi hX'i hX)
    (realizes_par_right X' hX' idleR hYi hY'i hYr)

end Par

/-! ## The tensor over a parallel composition -/

namespace MultiHybrid

variable {σ σ' τ υ E O E' O' EG OG EG' OG' : Type}

/-- **Tensor and parallel composition.** For multi-call hybrids of equal fuel, the tensor over
the parallel composition of `X` and `Y` and the parallel composition of `π` over `X` and `π'`
over `Y` realize each other at distance `0`. -/
theorem realizes_tensor_withSub_par (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') (hf : π.fuel = π'.fuel) (X : Sys τ EG OG)
    (Y : Sys υ EG' OG') :
    Realizes ((π.tensor π').withSub (X.par Y)) ((π.withSub X).par (π'.withSub Y))
      (fun _ _ => 0) := by
  have hL : ∀ t g, (X.par Y).step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((X.onFst Y.init).step t g) := by
    intro t g
    simp [Sys.onFst, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have hR : ∀ t g, (X.par Y).step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((Y.onSnd X.init).step t g) := by
    intro t g
    simp [Sys.onSnd, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have h₁ : max π.fuel π'.fuel = π.fuel := by rw [hf, max_self]
  have h₂ : max π.fuel π'.fuel = π'.fuel := by rw [hf, max_self]
  refine realizes_zero_of_stepMap _ _ (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))) rfl ?_
  rintro ⟨⟨s, s'⟩, ⟨x, y⟩⟩ (e | e)
  · rw [tensor_withSub_step_inl π π' (X.par Y) (X.onFst Y.init) hL s s' (x, y) e,
      stepFuel_onFst, h₁]
    simp [withSub, stepFuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_step_inr π π' (X.par Y) (Y.onSnd X.init) hR s s' (x, y) e,
      stepFuel_onSnd, h₂]
    simp [withSub, stepFuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

open MultiHybrid in
/-- **Parallel composition behind the tensor of simulators.** If `X` realizes `I` behind the
opaque multi-call simulator `S` with bound `bX`, and `Y` realizes `J` behind `S'` with bound
`bY`, `S` and `S'` of equal fuel, then `X.par Y` realizes `I.par J` behind the tensor of `S` and
`S'`, with the bound of `realizes_par`. -/
theorem RealizesSim.par {σ σ' τ τ' υ υ' E O E' O' EG OG EG' OG' : Type}
    {V : PubView E O} {W : PubView EG OG} {V' : PubView E' O'} {W' : PubView EG' OG'}
    {X : Sys τ E O} {I : Sys τ' EG OG} {Y : Sys υ E' O'} {J : Sys υ' EG' OG'}
    (S : MultiHybrid σ E O EG OG) (S' : MultiHybrid σ' E' O' EG' OG')
    (hS : S.Opaque V W) (hS' : S'.Opaque V' W') (hf : S.fuel = S'.fuel)
    (hY : ∀ u e, SPComp.NoFail (Y.step u e))
    (hSI : ∀ t e, SPComp.NoFail ((S.withSub I).step t e))
    (idleL : E) (idleR : E') {oX oSI : O} {oY oSJ : O'}
    (hXi : IdleAt X idleL oX) (hSIi : IdleAt (S.withSub I) idleL oSI)
    (hYi : IdleAt Y idleR oY) (hSJi : IdleAt (S'.withSub J) idleR oSJ)
    {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E' O') ζ → ℝ≥0∞}
    (hX : RealizesSim X I (Simulator.ofMultiHybrid S hS) bX)
    (hYr : RealizesSim Y J (Simulator.ofMultiHybrid S' hS') bY) :
    RealizesSim (X.par Y) (I.par J) (Simulator.tensor S S' hS hS')
      (fun ζ Z => bX (RState υ ζ E (O ⊕ O')) ((parCtxL Y hY).reduceEnv idleL Z) +
        bY (RState (σ × τ') ζ E' (O ⊕ O')) ((parCtxR (S.withSub I) hSI).reduceEnv idleR Z)) := by
  have h₁ := realizes_par hY hSI idleL idleR hXi hSIi hYi hSJi hX hYr
  have h₂ := realizes_tensor_withSub_par S S' hf I J
  exact fun ζ => ((h₁ ζ).triangle (h₂ ζ).symm).mono fun _ => by simp

/-! ## The two-call pipe -/

namespace MultiHybrid

variable {A B OX OY O : Type}

/-- The two-call pipe over a parallel composition: the outer event is passed to the left
component; its answer is routed by `route` either to the right component (`inl`) or to the
output (`inr`); the answer of the right component is mapped by `post`. The answer to a second
call on the left port, which a system answering each event on its port never gives, is
mapped to the output of `route`, or to `default`. -/
noncomputable def pipeHybrid [Inhabited O] (route : OX → B ⊕ O) (post : OY → O) :
    MultiHybrid Unit A O (A ⊕ B) (OX ⊕ OY) where
  init := ()
  fuel := 1
  start _ a := SPComp.pure ((), .inl (.inl a))
  resume _ o := SPComp.pure ((),
    Sum.elim (fun ox => Sum.map Sum.inr _root_.id (route ox)) (fun oy => .inr (post oy)) o)
  finish _ o := SPComp.pure ((),
    Sum.elim (fun ox => Sum.elim (fun _ => default) _root_.id (route ox)) post o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

end MultiHybrid

namespace Sys

variable {τ υ A B OX OY O : Type}

/-- The two-call pipe of `X` into `Y`: the pipe hybrid over the parallel composition. One
activation runs `X`, and either feeds its answer to `Y` or ends, as `route` says. -/
noncomputable def pipe [Inhabited O] (X : Sys τ A OX) (Y : Sys υ B OY) (route : OX → B ⊕ O)
    (post : OY → O) : Sys (Unit × (τ × υ)) A O :=
  (MultiHybrid.pipeHybrid route post).withSub (X.par Y)

/-- One step of the pipe: a step of `X`, then a step of `Y` on a routed answer. -/
theorem pipe_step [Inhabited O] (X : Sys τ A OX) (Y : Sys υ B OY) (route : OX → B ⊕ O)
    (post : OY → O) (t : Unit × (τ × υ)) (a : A) :
    (X.pipe Y route post).step t a = SPComp.bind (X.step t.2.1 a) fun p =>
      Sum.elim (fun b => SPComp.map (fun q => (((), (p.1, q.1)), post q.2)) (Y.step t.2.2 b))
        (fun o => SPComp.pure (((), (p.1, t.2.2)), o)) (route p.2) := by
  simp only [pipe, MultiHybrid.withSub, MultiHybrid.pipeHybrid, MultiHybrid.drive,
    par_step_inl, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sum.elim_inl]
  congr 1
  funext p
  rcases route p.2 with b | o <;>
    simp [MultiHybrid.drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end Sys

/-! ## The pipe of one-shot protocols -/

section HComp

variable {hon mid out I J L : Type}

/-- The routing of the horizontal composite: a result `inl m` of the first protocol goes to the
second, a leak `inr i` is output on the left leak, and an exhausted answer `none` is output. -/
def hcRoute : Option (mid ⊕ I) → mid ⊕ Option (out ⊕ (I ⊕ J))
  | none => .inr none
  | some (.inl m) => .inl m
  | some (.inr i) => .inr (some (.inr (.inl i)))

/-- The output map of the horizontal composite: a leak of the second protocol is output on the
right leak. -/
def hcPost : Option (out ⊕ J) → Option (out ⊕ (I ⊕ J))
  | none => none
  | some (.inl o) => some (.inl o)
  | some (.inr j) => some (.inr (.inr j))

/-- The pipe of the one-shot systems of `p` and `q`, routed as the horizontal composite. -/
noncomputable def Sys.hcompPipe (p : hon → SPComp (mid ⊕ I)) (q : mid → SPComp (out ⊕ J)) :
    Sys (Unit × (Bool × Bool)) hon (Option (out ⊕ (I ⊕ J))) :=
  (Sys.oneShot p).pipe (Sys.oneShot q) hcRoute hcPost

/-- Every step of the pipe of one-shot systems ends with the first system used. -/
theorem hcompPipe_step_used (p : hon → SPComp (mid ⊕ I)) (q : mid → SPComp (out ⊕ J))
    (t : Unit × (Bool × Bool)) (a : hon) :
    SPComp.map (fun r => (((), (true, r.1.2.2)), r.2)) ((Sys.hcompPipe p q).step t a) =
      (Sys.hcompPipe p q).step t a := by
  rcases t with ⟨⟨⟩, bX, bY⟩
  rw [Sys.hcompPipe, Sys.pipe_step]
  cases bX
  · simp only [oneShot_step_false, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1
    funext r
    rcases r with m | i <;> simp [hcRoute, SPComp.bind_assoc, SPComp.pure_bind]
  · simp [hcRoute, SPComp.map, SPComp.pure_bind]

/-- From a state where the second system is unused whenever the first is, a step of the pipe of
one-shot systems is a step of the one-shot system of the horizontal composite. -/
theorem hcompPipe_step_inv (p : hon → SPComp (mid ⊕ I)) (q : mid → SPComp (out ⊕ J))
    (t : Unit × (Bool × Bool)) (ht : t.2.1 = false → t.2.2 = false) (a : hon) :
    SPComp.map (fun r => (r.1.2.1, r.2)) ((Sys.hcompPipe p q).step t a) =
      (Sys.oneShot (UCMonad.ProtObj.hcomp (⟨I, p⟩ : UCMonad.ProtObj SPComp hon mid)
        ⟨J, q⟩).prot).step t.2.1 a := by
  rcases t with ⟨⟨⟩, bX, bY⟩
  rw [Sys.hcompPipe, Sys.pipe_step]
  cases bX
  · obtain rfl : bY = false := ht rfl
    simp only [oneShot_step_false, UCMonad.ProtObj.hcomp, SPComp.monad_bind_eq,
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1
    funext r
    rcases r with m | i
    · simp only [hcRoute, Sum.elim_inl, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1
      funext r
      rcases r with o | j <;> simp [hcPost, SPComp.monad_pure_eq, SPComp.pure_bind]
    · simp [hcRoute, SPComp.monad_pure_eq, SPComp.pure_bind]
  · simp only [Sys.oneShot, SPComp.map, SPComp.pure_bind, hcRoute,
      Sum.elim_inr]
    rfl

/-- The invariant data of the pipe of one-shot systems: every step ends at a state where the
first system is used. -/
theorem hcompPipe_pres (p : hon → SPComp (mid ⊕ I)) (q : mid → SPComp (out ⊕ J))
    (t : Unit × (Bool × Bool)) (a : hon) :
    ∃ (α : Type) (c : SPComp α) (g : α → (Unit × (Bool × Bool)) × Option (out ⊕ (I ⊕ J))),
      (Sys.hcompPipe p q).step t a = SPComp.bind c (fun x => SPComp.pure (g x)) ∧
        ∀ x, (g x).1.2.1 = false → (g x).1.2.2 = false := by
  refine ⟨Bool × Option (out ⊕ (I ⊕ J)),
    SPComp.map (fun r => (r.1.2.2, r.2)) ((Sys.hcompPipe p q).step t a),
    fun x => (((), (true, x.1)), x.2), ?_, fun _ h => Bool.noConfusion h⟩
  conv => lhs; rw [← hcompPipe_step_used]
  simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **The pipe is the reactive horizontal composite.** The pipe of the one-shot systems of `p`
and `q` realizes the one-shot system of `ProtObj.hcomp` of `p` and `q` at distance `0`. -/
theorem realizes_hcompPipe (p : hon → SPComp (mid ⊕ I)) (q : mid → SPComp (out ⊕ J)) :
    Realizes (Sys.hcompPipe p q)
      (Sys.oneShot (UCMonad.ProtObj.hcomp (⟨I, p⟩ : UCMonad.ProtObj SPComp hon mid)
        ⟨J, q⟩).prot) (fun _ _ => 0) :=
  realizes_zero_of_stepMap_on _ _ (fun t => t.2.1 = false → t.2.2 = false) (fun t => t.2.1)
    (fun _ => rfl) rfl (fun t a _ => hcompPipe_pres p q t a)
    (fun t a ht => hcompPipe_step_inv p q t ht a)

/-- `simWrap sim` preserves a distance-`0` realization given by a state map on an invariant. -/
theorem realizes_simWrap_withSub_of_stepMap_on {L' τ υ : Type} (sim : L → SPComp L')
    (hsim : ∀ l, SPComp.NoFail (sim l)) (R : Sys τ hon (Option (out ⊕ L)))
    (R' : Sys υ hon (Option (out ⊕ L))) (Inv : τ → Prop) (f : τ → υ) (hInv : Inv R.init)
    (hinit : f R.init = R'.init)
    (hpres : ∀ t e, Inv t → ∃ (α : Type) (c : SPComp α) (g : α → τ × Option (out ⊕ L)),
      R.step t e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧ ∀ a, Inv (g a).1)
    (hstep : ∀ t e, Inv t →
      SPComp.map (fun p => (f p.1, p.2)) (R.step t e) = R'.step (f t) e) :
    Realizes ((simWrap sim hsim).withSub R) ((simWrap sim hsim).withSub R')
      (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap_on _ _ (fun t => Inv t.2) (fun t => ((), f t.2)) hInv
    (by simp [MultiHybrid.withSub, simWrap, hinit]) ?_ ?_
  · intro t e ht
    obtain ⟨α, c, g, hc, hg⟩ := hpres t.2 e ht
    refine ⟨α × Option (out ⊕ L'),
      SPComp.bind c (fun a => SPComp.map (fun r => (a, r)) (leakMap sim (g a).2)),
      fun x => (((), (g x.1).1), x.2), ?_, fun x => hg x.1⟩
    rw [simWrap_withSub_step, hc]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · intro t e ht
    rw [simWrap_withSub_step, simWrap_withSub_step, ← hstep t.2 e ht]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **The bound of `sdist_hcomp` between pipes.** If `π₁` is within `ε₁` of `F₁` and `π₂` within
`ε₂` of `F₂`, the pipe of `π₁` into `π₂` realizes the pipe of `F₁` into `F₂` with the one-shot
bound of `ε₁ + ε₂`. -/
theorem realizes_hcompPipe_of_sdist {I₁ I₂ : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ F₁ : hon → SPComp (mid ⊕ I₁)} {π₂ F₂ : mid → SPComp (out ⊕ I₂)}
    (h₁ : sdist π₁ F₁ ≤ ε₁) (h₂ : sdist π₂ F₂ ≤ ε₂)
    (hcoPPL : ∀ (f₁ f₂ : mid → SPComp (out ⊕ I₂)) (g : I₁ → SPComp I₁),
      UCMonad.UCMonadMetric.ucSdist (UCMonad.UCMonadBase.ucMapSum f₁ g)
        (UCMonad.UCMonadBase.ucMapSum f₂ g) ≤ UCMonad.UCMonadMetric.ucSdist f₁ f₂) :
    Realizes (Sys.hcompPipe π₁ π₂) (Sys.hcompPipe F₁ F₂) (oneShotBound fun _ => ε₁ + ε₂) := by
  have hd := UCMonad.sdist_hcomp_of_approx (T := SPComp) h₁ h₂ hcoPPL
  have h := realizes_oneShot_of_distC (DistC_const_iff.mpr hd)
  exact fun ζ => (((realizes_hcompPipe π₁ π₂ ζ).triangle (h ζ)).triangle
    (realizes_hcompPipe F₁ F₂ ζ).symm).mono fun _ => by
      simp only [zero_add, add_zero]
      exact le_rfl

/-- **The horizontal composite of approximate 2-cells between pipes.** For `η : ProtMorε P₁ P₂ ε₁`
and `θ : ProtMorε Q₁ Q₂ ε₂`, the pipe of `P₂` into `Q₂` realizes the pipe of `P₁` into `Q₁`
behind `simWrapSim` of the simulator of `η.hcomp θ`, with the one-shot bound of `ε₁ + ε₂`. -/
theorem realizesSim_hcompPipe {P₁ P₂ : UCMonad.ProtObj SPComp hon mid}
    {Q₁ Q₂ : UCMonad.ProtObj SPComp mid out} {ε₁ ε₂ : ℝ≥0∞}
    (η : UCMonad.ProtMorε P₁ P₂ ε₁) (θ : UCMonad.ProtMorε Q₁ Q₂ ε₂)
    (hcoPPL : ∀ (f₁ f₂ : mid → SPComp (out ⊕ Q₂.iface)) (g : P₂.iface → SPComp P₂.iface),
      UCMonad.UCMonadMetric.ucSdist (UCMonad.UCMonadBase.ucMapSum f₁ g)
        (UCMonad.UCMonadBase.ucMapSum f₂ g) ≤ UCMonad.UCMonadMetric.ucSdist f₁ f₂)
    (hsim : ∀ l, SPComp.NoFail ((η.hcomp θ hcoPPL).sim l)) (ev : hon → hon → Prop) :
    RealizesSim (Sys.hcompPipe P₂.prot Q₂.prot) (Sys.hcompPipe P₁.prot Q₁.prot)
      (simWrapSim ev (η.hcomp θ hcoPPL).sim hsim) (oneShotBound fun _ => ε₁ + ε₂) := by
  have h₁ := realizes_hcompPipe P₂.prot Q₂.prot
  have h₂ := (η.hcomp θ hcoPPL).realizesSim_oneShot hsim ev
  have h₃ := realizes_simWrap_withSub_of_stepMap_on (η.hcomp θ hcoPPL).sim hsim
    (Sys.hcompPipe P₁.prot Q₁.prot) _ (fun t => t.2.1 = false → t.2.2 = false)
    (fun t => t.2.1) (fun _ => rfl) rfl (fun t a _ => hcompPipe_pres P₁.prot Q₁.prot t a)
    (fun t a ht => hcompPipe_step_inv P₁.prot Q₁.prot t ht a)
  exact fun ζ => (((h₁ ζ).triangle (h₂ ζ)).triangle (h₃ ζ).symm).mono fun _ => by
    simp only [zero_add, add_zero]
    exact le_rfl

end HComp

/-! ## Two ports onto one system -/

namespace Sys

variable {τ EG OG : Type}

/-- Two ports onto one copy of `G`: an event on either port is a step of `G`, answered on the
port of the event. -/
noncomputable def merge (G : Sys τ EG OG) : Sys τ (EG ⊕ EG) (OG ⊕ OG) where
  init := G.init
  step t := Sum.elim (fun g => SPComp.map (fun q => (q.1, .inl q.2)) (G.step t g))
    (fun g => SPComp.map (fun q => (q.1, .inr q.2)) (G.step t g))

/-- The merge answers every event on the port of the event. -/
theorem merge_portTyped (G : Sys τ EG OG) : G.merge.PortTyped :=
  ⟨G, G, fun _ _ => rfl, fun _ _ => rfl⟩

end Sys

/-! ## Categories -/

/-- A system with interface `(E, O)`, its state type bundled. -/
structure SysObj (E O : Type) : Type 1 where
  /-- The state type. -/
  St : Type
  /-- The system. -/
  sys : Sys St E O

open CategoryTheory in
/-- The category of systems with interface `(E, O)`: a morphism from `X` to `Y` is a bound with
a realization of `Y` by `X` at that bound; composition adds the bounds. -/
noncomputable instance SysObj.category (E O : Type) : Category.{1} (SysObj E O) where
  Hom X Y := {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞ // Realizes X.sys Y.sys b}
  id _ := ⟨fun _ _ => 0, fun _ => DistC.refl _⟩
  comp f g := ⟨fun ζ Z => f.1 ζ Z + g.1 ζ Z, Realizes.trans f.2 g.2⟩
  id_comp _ := Subtype.ext (funext fun _ => funext fun _ => zero_add _)
  comp_id _ := Subtype.ext (funext fun _ => funext fun _ => add_zero _)
  assoc _ _ _ := Subtype.ext (funext fun _ => funext fun _ => add_assoc _ _ _)

/-- An interface of open systems: events and outputs. -/
structure UCIface : Type 1 where
  /-- The events. -/
  E : Type
  /-- The outputs. -/
  O : Type

open CategoryTheory in
/-- The category of open systems: a morphism from `(E, O)` to `(EG, OG)` is an open system with
outer interface `(E, O)` over subroutines with interface `(EG, OG)`; composition is
`Open.comp`. -/
noncomputable instance UCIface.category : Category.{1} UCIface where
  Hom X Y := Open X.E X.O Y.E Y.O
  id X := Open.id X.E X.O
  comp P Q := P.comp Q
  id_comp := Open.id_comp
  comp_id := Open.comp_id
  assoc := Open.comp_assoc

end CatCrypt.Crypto.UCTransparent

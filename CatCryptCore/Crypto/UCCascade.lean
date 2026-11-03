/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackTrace
public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Realization under the cascade

The cascade `X.seq Y` of `X : Sys τ E O` and `Y : Sys υ O P` feeds each output of `X` to `Y` as
its event. Each component is an open system over the other, through a one-call hybrid:

* `seqCtxR Y` passes the outer event to its subroutine and answers with a step of `Y` on the
  answer; `X.seq Y` is `(seqCtxR Y).withSub X` with the components of the state exchanged;
* `seqCtxL X` answers the outer event with a step of `X` and passes the output to its subroutine;
  `X.seq Y` is `(seqCtxL X).withSub Y`.

Realization is therefore preserved by the cascade, with the bounds added at the environments
reduced through these contexts (`realizes_seq`): the environment of `X` runs `Y` after each
answer, the environment of `Y` runs `X'` before each event. The hybrids need the system they run
inside the reduced environment to be lossless; no idle event is needed.

Behind multi-call simulators, the cascade of `S.withSub I` and `T.withSub J` is the system
`cascSys S T dI dJ (I.par J)`, in which `S` runs over the left port of the parallel composition
of the ideal systems and `T` over the right port, up to a state map (`cascSys_par_stepMap`).
The system `cascSys S T dI dJ X` over every subroutine `X` on the sum interface is opaque when
`S`, `T` and `X` are (`Simulator.cascade`), so that the cascade of two realizations behind
simulators is a realization behind the cascade simulator over the parallel composition of the
ideal systems (`RealizesSim.seq`). The default answers `dI`, `dJ` answer a call on one port that
a subroutine answers on the other port.

At statistical bounds, which do not depend on the environment, the reduced environments drop out
of the bound and the cascade adds the bounds (`realizes_seq_const`). Lossless systems modulo step
equivalence then form the 1-cells of a bicategory `RSysBicat` over types of ports, with the
cascade as composition, the forwarding system as identity, and statistical bounds of realizations
as 2-cells (`RSysBicat.bicategory`): vertical composition and horizontal composition add the
bounds, the associator and the unitors are equalities of step equivalence classes at bound `0`.

## Main definitions

* `Hybrid.seqCtxR`, `Hybrid.seqCtxL`: the cascade as a one-call hybrid over either component.
* `Sys.leftPort`, `Sys.rightPort`: the ports of a system on a sum interface.
* `MultiHybrid.cascSys`, `Simulator.cascade`: the cascade simulator.
* `LSysObj`, `Cell1`, `RSysBicat`: lossless systems, their step equivalence classes, and the
  bicategory.

## Main results

* `realizes_seq_left`, `realizes_seq_right`, `realizes_seq`, `realizes_seq_const`: realization
  under the cascade.
* `MultiHybrid.cascSys_par_stepMap`, `MultiHybrid.cascSys_par_stepEq`: the cascade of simulated
  systems is the cascade simulator over the parallel composition.
* `RealizesSim.seq`: the cascade of realizations behind simulators.
* `RSysBicat.bicategory`: the bicategory of reactive systems at statistical bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

/-! ## The cascade as a hybrid over either component -/

namespace Hybrid

variable {τ υ E O P : Type}

/-- The context of `Y` after a subroutine: the outer event is passed to the subroutine, and its
answer is the event of a step of `Y`, whose output is the outer output. -/
noncomputable def seqCtxR (Y : Sys υ O P) (hY : ∀ u o, SPComp.NoFail (Y.step u o)) :
    Hybrid υ E P E O where
  init := Y.init
  pre u e := SPComp.pure (u, e)
  post u o := Y.step u o
  pre_noFail _ _ := SPComp.pure_noFail _
  post_noFail := hY

/-- The context of `X` before a subroutine: the outer event is the event of a step of `X`, whose
output is passed to the subroutine, and the answer is the outer output. -/
noncomputable def seqCtxL (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e)) :
    Hybrid τ E P O P where
  init := X.init
  pre t e := X.step t e
  post t p := SPComp.pure (t, p)
  pre_noFail := hX
  post_noFail _ _ := SPComp.pure_noFail _

/-- The context of `Y` over `X` has the steps of the cascade, with the components of the state
exchanged. -/
theorem seqCtxR_withSub_step (Y : Sys υ O P) (hY : ∀ u o, SPComp.NoFail (Y.step u o))
    (X : Sys τ E O) (t : τ × υ) (e : E) :
    SPComp.map (fun p => (Prod.swap p.1, p.2)) ((X.seq Y).step t e) =
      ((seqCtxR Y hY).withSub X).step t.swap e := by
  simp [Sys.seq_step, withSub, seqCtxR, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The context of `X` over `Y` is the cascade. -/
theorem seqCtxL_withSub (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (Y : Sys υ O P) : (seqCtxL X hX).withSub Y = X.seq Y := by
  simp only [withSub, Sys.seq, seqCtxL]
  congr 1
  funext s e
  simp [SPComp.map, SPComp.pure_bind]

end Hybrid

/-! ## Realization under the cascade -/

section Seq

variable {τ τ' υ υ' E O P : Type}

open Hybrid

/-- **Cascade, left component.** If `X` realizes `X'` with bound `b`, then `X.seq Y` realizes
`X'.seq Y` with bound `b` at the environment reduced through the context of `Y`, which runs `Y`
on each answer. -/
theorem realizes_seq_left {X : Sys τ E O} {X' : Sys τ' E O} (Y : Sys υ O P)
    (hY : ∀ u o, SPComp.NoFail (Y.step u o))
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X X' b) :
    Realizes (X.seq Y) (X'.seq Y)
      (fun ζ Z => b (ζ × υ) ((seqCtxR (E := E) Y hY).reduceEnv Z)) := by
  intro ζ Z
  have hv : ∀ {τ₀ : Type} (X₀ : Sys τ₀ E O),
      (view (X₀.seq Y) : Strat ζ E P → SPComp ζ) = view ((seqCtxR Y hY).withSub X₀) :=
    fun X₀ => funext (view_eq_of_stepMap _ _ Prod.swap rfl (seqCtxR_withSub_step Y hY X₀))
  change Env.gap _ _ Z ≤ _
  rw [hv X, hv X']
  have ha := Hybrid.adv_withSub (seqCtxR Y hY) X X' Z
  unfold adv at ha
  rw [ha]
  exact h _ _

/-- **Cascade, right component.** If `Y` realizes `Y'` with bound `b`, then `X.seq Y` realizes
`X.seq Y'` with bound `b` at the environment reduced through the context of `X`, which runs `X`
before each event. -/
theorem realizes_seq_right (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    {Y : Sys υ O P} {Y' : Sys υ' O P}
    {b : (ζ : Type) → Env (Strat ζ O P) ζ → ℝ≥0∞} (h : Realizes Y Y' b) :
    Realizes (X.seq Y) (X.seq Y')
      (fun ζ Z => b (ζ × τ) ((seqCtxL (P := P) X hX).reduceEnv Z)) := by
  rw [← seqCtxL_withSub X hX Y, ← seqCtxL_withSub X hX Y']
  intro ζ Z
  have ha := Hybrid.adv_withSub (seqCtxL X hX) Y Y' Z
  unfold adv at ha
  change Env.gap _ _ Z ≤ _
  rw [ha]
  exact h _ _

/-- **Cascade of realizations** (the sequential composition theorem). If `X` realizes `X'` with
bound `bX` and `Y` realizes `Y'` with bound `bY`, then `X.seq Y` realizes `X'.seq Y'` with the
sum of `bX` at the environment reduced through the context of `Y` and `bY` at the environment
reduced through the context of `X'`. The systems `Y` and `X'`, which run inside the reduced
environments, are lossless. -/
theorem realizes_seq {X : Sys τ E O} {X' : Sys τ' E O} {Y : Sys υ O P} {Y' : Sys υ' O P}
    (hY : ∀ u o, SPComp.NoFail (Y.step u o)) (hX' : ∀ t e, SPComp.NoFail (X'.step t e))
    {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ O P) ζ → ℝ≥0∞}
    (hXr : Realizes X X' bX) (hYr : Realizes Y Y' bY) :
    Realizes (X.seq Y) (X'.seq Y')
      (fun ζ Z => bX (ζ × υ) ((seqCtxR (E := E) Y hY).reduceEnv Z) +
        bY (ζ × τ') ((seqCtxL (P := P) X' hX').reduceEnv Z)) :=
  Realizes.trans (realizes_seq_left Y hY hXr) (realizes_seq_right X' hX' hYr)

/-- The cascade of realizations at statistical bounds: the bounds `ε` and `δ`, which do not
depend on the environment, add. -/
theorem realizes_seq_const {X : Sys τ E O} {X' : Sys τ' E O} {Y : Sys υ O P} {Y' : Sys υ' O P}
    (hY : ∀ u o, SPComp.NoFail (Y.step u o)) (hX' : ∀ t e, SPComp.NoFail (X'.step t e))
    {ε δ : ℝ≥0∞} (hXr : Realizes X X' (fun _ _ => ε)) (hYr : Realizes Y Y' (fun _ _ => δ)) :
    Realizes (X.seq Y) (X'.seq Y') (fun _ _ => ε + δ) :=
  realizes_seq hY hX' hXr hYr

end Seq

/-! ## The cascade behind multi-call simulators -/

namespace Sys

variable {τ EI EJ OI OJ : Type}

/-- The left port of a system on a sum interface: an event `e` is the event `inl e`, an answer
`inl o` is `o`, and an answer `inr _` is the default answer `dI`. -/
noncomputable def leftPort (X : Sys τ (EI ⊕ EJ) (OI ⊕ OJ)) (dI : OI) : Sys τ EI OI where
  init := X.init
  step t e := SPComp.map (fun q => (q.1, Sum.elim id (fun _ => dI) q.2)) (X.step t (.inl e))

/-- The right port of a system on a sum interface: an event `e` is the event `inr e`, an answer
`inr o` is `o`, and an answer `inl _` is the default answer `dJ`. -/
noncomputable def rightPort (X : Sys τ (EI ⊕ EJ) (OI ⊕ OJ)) (dJ : OJ) : Sys τ EJ OJ where
  init := X.init
  step t e := SPComp.map (fun q => (q.1, Sum.elim (fun _ => dJ) id q.2)) (X.step t (.inr e))

variable {ι κ : Type}

/-- The left port of a parallel composition is its left component on the first component of the
state. -/
theorem leftPort_par (I : Sys ι EI OI) (J : Sys κ EJ OJ) (dI : OI) :
    (I.par J).leftPort dI = I.onFst J.init := by
  simp only [leftPort, onFst]
  congr 1
  funext t e
  simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The right port of a parallel composition is its right component on the second component of
the state. -/
theorem rightPort_par (I : Sys ι EI OI) (J : Sys κ EJ OJ) (dJ : OJ) :
    (I.par J).rightPort dJ = J.onSnd I.init := by
  simp only [rightPort, onSnd]
  congr 1
  funext t e
  simp [SPComp.map, SPComp.pure_bind]

end Sys

namespace MultiHybrid

variable {σ σ' τ E O P EI OI EJ OJ : Type}

/-- The cascade simulator over the subroutine `X` on the sum interface: `S` runs an activation
over the left port of `X`, and its output is the event of an activation of `T` over the right
port of `X`, from the subroutine state that `S` leaves. -/
noncomputable def cascSys (S : MultiHybrid σ E O EI OI) (T : MultiHybrid σ' O P EJ OJ)
    (dI : OI) (dJ : OJ) (X : Sys τ (EI ⊕ EJ) (OI ⊕ OJ)) : Sys (σ × σ' × τ) E P where
  init := (S.init, T.init, X.init)
  step s e := SPComp.bind ((S.withSub (X.leftPort dI)).step (s.1, s.2.2) e) fun q =>
    SPComp.map (fun r => ((q.1.1, r.1.1, r.1.2), r.2))
      ((T.withSub (X.rightPort dJ)).step (s.2.1, q.1.2) q.2)

/-- One activation of `π` over `X.onFst r` is an activation over `X`, with the second component
of the subroutine state unchanged. -/
theorem withSub_onFst_step {ρ : Type} (π : MultiHybrid σ E O EI OI) (X : Sys τ EI OI) (r : ρ)
    (s : σ) (t : τ) (a : ρ) (e : E) :
    (π.withSub (X.onFst r)).step (s, (t, a)) e =
      SPComp.map (fun p => ((p.1.1, (p.1.2, a)), p.2)) ((π.withSub X).step (s, t) e) := by
  simp [withSub, drive_onFst, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- One activation of `π` over `X.onSnd r` is an activation over `X`, with the first component
of the subroutine state unchanged. -/
theorem withSub_onSnd_step {ρ : Type} (π : MultiHybrid σ E O EI OI) (X : Sys τ EI OI) (r : ρ)
    (s : σ) (y : ρ × τ) (e : E) :
    (π.withSub (X.onSnd r)).step (s, y) e =
      SPComp.map (fun p => ((p.1.1, (y.1, p.1.2)), p.2)) ((π.withSub X).step (s, y.2) e) := by
  rcases y with ⟨a, t⟩
  simp [withSub, drive_onSnd, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

variable {ι κ : Type}

/-- **The cascade of simulated systems.** Regrouping the states is a step map from the cascade
of `S.withSub I` and `T.withSub J` to the cascade simulator over the parallel composition of `I`
and `J`. -/
theorem cascSys_par_stepMap (S : MultiHybrid σ E O EI OI) (T : MultiHybrid σ' O P EJ OJ)
    (dI : OI) (dJ : OJ) (I : Sys ι EI OI) (J : Sys κ EJ OJ) :
    Sys.StepMapOn ((S.withSub I).seq (T.withSub J)) (cascSys S T dI dJ (I.par J))
      (fun _ => True) (fun p => (p.1.1, p.2.1, (p.1.2, p.2.2))) where
  init_inv := trivial
  init_map := rfl
  pres _ _ _ _ _ := trivial
  step p e _ := by
    rcases p with ⟨⟨s, i⟩, ⟨s', j⟩⟩
    simp only [cascSys, Sys.leftPort_par, Sys.rightPort_par, withSub_onFst_step,
      withSub_onSnd_step, Sys.seq_step]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

/-! ## Opacity of the cascade simulator -/

/-- An `rHoare` triple at the precondition `eqPre` conjoined with a fact `P`. -/
private theorem rHoare_eqPre_and' {α β : Type} {P : Prop} {c₁ : SPComp α} {c₂ : SPComp β}
    {Ψ : RPost α β} (h : P → rHoare eqPre c₁ c₂ Ψ) :
    rHoare (fun h₁ h₂ => h₁ = h₂ ∧ P) c₁ c₂ Ψ :=
  fun h₁ h₂ hp => h hp.2 h₁ h₂ hp.1

namespace Sys

variable {τ EI EJ OI OJ : Type} {WI : PubView EI OI} {WJ : PubView EJ OJ}

/-- An unwinding relation of `X` for the view of the sum interface is an unwinding relation of
its left port, when the default answer is related to itself. -/
theorem Unwinding.leftPort {X : Sys τ (EI ⊕ EJ) (OI ⊕ OJ)} {R : τ → τ → Prop}
    (h : X.Unwinding (WI.sum WJ) R) (dI : OI) (hd : WI.out dI dI) :
    (X.leftPort dI).Unwinding WI R where
  init := h.init
  step t t' e e' ht he := by
    simp only [Sys.leftPort, SPComp.map]
    refine rHoare_bind (h.step t t' (.inl e) (.inl e') ht (Sum.LiftRel.inl he)) fun q q' => ?_
    refine rHoare_eqPre_and' (P := R q.1 q'.1 ∧ (WI.sum WJ).out q.2 q'.2) fun hq => ?_
    refine rHoare_ret fun _ _ hh => ⟨hh, hq.1, ?_⟩
    rcases q with ⟨_, o | o⟩ <;> rcases q' with ⟨_, o' | o'⟩
    · exact Sum.liftRel_inl_inl.mp hq.2
    · exact (Sum.not_liftRel_inl_inr hq.2).elim
    · exact (Sum.not_liftRel_inr_inl hq.2).elim
    · exact hd

/-- An unwinding relation of `X` for the view of the sum interface is an unwinding relation of
its right port, when the default answer is related to itself. -/
theorem Unwinding.rightPort {X : Sys τ (EI ⊕ EJ) (OI ⊕ OJ)} {R : τ → τ → Prop}
    (h : X.Unwinding (WI.sum WJ) R) (dJ : OJ) (hd : WJ.out dJ dJ) :
    (X.rightPort dJ).Unwinding WJ R where
  init := h.init
  step t t' e e' ht he := by
    simp only [Sys.rightPort, SPComp.map]
    refine rHoare_bind (h.step t t' (.inr e) (.inr e') ht (Sum.LiftRel.inr he)) fun q q' => ?_
    refine rHoare_eqPre_and' (P := R q.1 q'.1 ∧ (WI.sum WJ).out q.2 q'.2) fun hq => ?_
    refine rHoare_ret fun _ _ hh => ⟨hh, hq.1, ?_⟩
    rcases q with ⟨_, o | o⟩ <;> rcases q' with ⟨_, o' | o'⟩
    · exact hd
    · exact (Sum.not_liftRel_inl_inr hq.2).elim
    · exact (Sum.not_liftRel_inr_inl hq.2).elim
    · exact Sum.liftRel_inr_inr.mp hq.2

end Sys

/-- The outer view of a cascade: the events of the view `V` of the first interface and the
outputs of the view `V'` of the second. -/
def PubView.cascade {E O P : Type} (V : PubView E O) (V' : PubView O P) : PubView E P where
  ev := V.ev
  out := V'.out

namespace MultiHybrid

variable {σ σ' τ E O P EI OI EJ OJ : Type} {V : PubView E O} {V' : PubView O P}
  {WI : PubView EI OI} {WJ : PubView EJ OJ}

/-- Unwinding relations of `S`, `T` and the subroutine `X` give the unwinding relation of the
cascade simulator over `X`, the product of the three, when the outputs related by the view of
`S` are events related by the view of `T`. -/
theorem Unwinding.cascSys {S : MultiHybrid σ E O EI OI} {T : MultiHybrid σ' O P EJ OJ}
    {RS : σ → σ → Prop} {RT : σ' → σ' → Prop} (hS : S.Unwinding V WI RS)
    (hT : T.Unwinding V' WJ RT) (hVV : ∀ o o', V.out o o' → V'.ev o o')
    {X : Sys τ (EI ⊕ EJ) (OI ⊕ OJ)} {R : τ → τ → Prop} (hX : X.Unwinding (WI.sum WJ) R)
    (dI : OI) (dJ : OJ) (hdI : WI.out dI dI) (hdJ : WJ.out dJ dJ) :
    (cascSys S T dI dJ X).Unwinding (V.cascade V')
      (fun a b => RS a.1 b.1 ∧ RT a.2.1 b.2.1 ∧ R a.2.2 b.2.2) where
  init := ⟨hS.init, hT.init, hX.init⟩
  step s s' e e' hs he := by
    have h₁ := (hS.withSub (hX.leftPort dI hdI)).step (s.1, s.2.2) (s'.1, s'.2.2) e e'
      ⟨hs.1, hs.2.2⟩ he
    dsimp only [MultiHybrid.cascSys]
    refine rHoare_bind h₁ fun q q' => ?_
    refine rHoare_eqPre_and' (P := (RS q.1.1 q'.1.1 ∧ R q.1.2 q'.1.2) ∧ V.out q.2 q'.2)
      fun hq => ?_
    have h₂ := (hT.withSub (hX.rightPort dJ hdJ)).step (s.2.1, q.1.2) (s'.2.1, q'.1.2) q.2 q'.2
      ⟨hs.2.1, hq.1.2⟩ (hVV _ _ hq.2)
    simp only [SPComp.map]
    refine rHoare_bind h₂ fun r r' => ?_
    exact rHoare_eqPre_and' (P := (RT r.1.1 r'.1.1 ∧ R r.1.2 r'.1.2) ∧ V'.out r.2 r'.2)
      fun hr => rHoare_ret fun _ _ hh => ⟨hh, ⟨hq.1.1, hr.1.1, hr.1.2⟩, hr.2⟩

end MultiHybrid

/-- **The cascade simulator**: `S` over the left port and `T` over the right port of a subroutine
on the sum interface, the output of `S` the event of `T`. It is opaque from the view of the sum
interface to the cascade of the outer views, for opaque `S` and `T` whose views agree on the
middle interface and default answers related to themselves. -/
noncomputable def Simulator.cascade {σ σ' E O P EI OI EJ OJ : Type} {V : PubView E O}
    {V' : PubView O P} {WI : PubView EI OI} {WJ : PubView EJ OJ}
    (S : MultiHybrid σ E O EI OI) (T : MultiHybrid σ' O P EJ OJ) (hS : S.Opaque V WI)
    (hT : T.Opaque V' WJ) (hVV : ∀ o o', V.out o o' → V'.ev o o') (dI : OI) (dJ : OJ)
    (hdI : WI.out dI dI) (hdJ : WJ.out dJ dJ) :
    Simulator E P (EI ⊕ EJ) (OI ⊕ OJ) (V.cascade V') (WI.sum WJ) where
  St τ := σ × σ' × τ
  withSub X := MultiHybrid.cascSys S T dI dJ X
  isOpaque X hX := by
    obtain ⟨RS, hRS⟩ := hS
    obtain ⟨RT, hRT⟩ := hT
    obtain ⟨R, hR⟩ := hX
    exact ⟨_, hRS.cascSys hRT hVV hR dI dJ hdI hdJ⟩

open Hybrid in
/-- **Cascade behind simulators** (the sequential UC composition theorem). If `X` realizes `I`
behind the opaque multi-call simulator `S` with bound `bX`, and `Y` realizes `J` behind `T` with
bound `bY`, then `X.seq Y` realizes the parallel composition of `I` and `J` behind the cascade
simulator, with the sum of `bX` at the environment reduced through the context of `Y` and `bY` at
the environment reduced through the context of `S.withSub I`. The systems `Y` and `S.withSub I`
run inside the reduced environments and are lossless. -/
theorem RealizesSim.seq {σ σ' τ υ ι κ E O P EI OI EJ OJ : Type} {V : PubView E O}
    {V' : PubView O P} {WI : PubView EI OI} {WJ : PubView EJ OJ}
    {X : Sys τ E O} {Y : Sys υ O P} {I : Sys ι EI OI} {J : Sys κ EJ OJ}
    (S : MultiHybrid σ E O EI OI) (T : MultiHybrid σ' O P EJ OJ) (hS : S.Opaque V WI)
    (hT : T.Opaque V' WJ) (hVV : ∀ o o', V.out o o' → V'.ev o o') (dI : OI) (dJ : OJ)
    (hdI : WI.out dI dI) (hdJ : WJ.out dJ dJ)
    (hY : ∀ u o, SPComp.NoFail (Y.step u o))
    (hSI : ∀ t e, SPComp.NoFail ((S.withSub I).step t e))
    {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ O P) ζ → ℝ≥0∞}
    (hX : RealizesSim X I (Simulator.ofMultiHybrid S hS) bX)
    (hYr : RealizesSim Y J (Simulator.ofMultiHybrid T hT) bY) :
    RealizesSim (X.seq Y) (I.par J) (Simulator.cascade S T hS hT hVV dI dJ hdI hdJ)
      (fun ζ Z => bX (ζ × υ) ((seqCtxR (E := E) Y hY).reduceEnv Z) +
        bY (ζ × (σ × ι)) ((seqCtxL (P := P) (S.withSub I) hSI).reduceEnv Z)) := by
  have h₁ := realizes_seq hY hSI hX hYr
  have h₂ := (MultiHybrid.cascSys_par_stepMap S T dI dJ I J).realizes
  exact fun ζ => ((h₁ ζ).triangle (h₂ ζ)).mono fun _ => by simp

/-- The cascade of `S.withSub I` and `T.withSub J` is step equivalent to the cascade simulator
over the parallel composition of `I` and `J`. -/
theorem MultiHybrid.cascSys_par_stepEq {σ σ' ι κ E O P EI OI EJ OJ : Type}
    (S : MultiHybrid σ E O EI OI) (T : MultiHybrid σ' O P EJ OJ) (dI : OI) (dJ : OJ)
    (I : Sys ι EI OI) (J : Sys κ EJ OJ) :
    Sys.StepEq ⟨_, (S.withSub I).seq (T.withSub J)⟩ ⟨_, cascSys S T dI dJ (I.par J)⟩ :=
  (cascSys_par_stepMap S T dI dJ I J).stepEq

/-! ## The bicategory of lossless systems at statistical bounds -/

/-- A lossless system with interface `(E, O)`, its state type bundled. -/
structure LSysObj (E O : Type) : Type 1 where
  /-- The bundled system. -/
  obj : SysObj E O
  /-- Its steps never fail. -/
  noFail : ∀ t e, SPComp.NoFail (obj.sys.step t e)

namespace LSysObj

variable {E O P : Type}

/-- Step equivalence of the underlying systems. -/
instance setoid (E O : Type) : Setoid (LSysObj E O) where
  r A B := Sys.StepEq A.obj B.obj
  iseqv := ⟨fun _ => Relation.EqvGen.refl _, fun h => Relation.EqvGen.symm _ _ h,
    fun h h' => Relation.EqvGen.trans _ _ _ h h'⟩

/-- The cascade of lossless systems. -/
noncomputable def seq (A : LSysObj E O) (B : LSysObj O P) : LSysObj E P where
  obj := ⟨A.obj.St × B.obj.St, A.obj.sys.seq B.obj.sys⟩
  noFail t e := by
    rw [Sys.seq_step]
    exact Assumptions.SPComp.bind_noFail (A.noFail _ _) fun _ =>
      Assumptions.SPComp.bind_noFail (B.noFail _ _) fun _ => SPComp.pure_noFail _

/-- The forwarding system. -/
noncomputable def idL (E : Type) : LSysObj E E :=
  ⟨SysObj.idSys E, fun _ _ => SPComp.pure_noFail _⟩

/-- Realization of `B` by `A` at the statistical bound `ε`. -/
def RealizesC (A B : LSysObj E O) (ε : ℝ≥0∞) : Prop :=
  Realizes A.obj.sys B.obj.sys (fun _ _ => ε)

/-- Realization at a statistical bound depends only on the step equivalence classes. -/
theorem realizesC_congr {A A' B B' : LSysObj E O} (hA : A ≈ A') (hB : B ≈ B') {ε : ℝ≥0∞}
    (h : RealizesC A B ε) : RealizesC A' B' ε := fun ζ =>
  ((((Sys.StepEq.realizes hA).2 ζ).triangle (h ζ)).triangle
    ((Sys.StepEq.realizes hB).1 ζ)).mono fun _ => by simp

end LSysObj

/-- Lossless systems with events `E` and outputs `O` modulo step equivalence. -/
def Cell1 (E O : Type) : Type 1 := Quotient (LSysObj.setoid E O)

namespace Cell1

variable {E O P : Type}

/-- Realization at the statistical bound `ε` between step equivalence classes. -/
def Holds (f g : Cell1 E O) (ε : ℝ≥0∞) : Prop :=
  Quotient.lift₂ (fun A B => LSysObj.RealizesC A B ε)
    (fun _ _ _ _ hA hB => propext ⟨LSysObj.realizesC_congr hA hB,
      LSysObj.realizesC_congr (Setoid.symm hA) (Setoid.symm hB)⟩) f g

/-- Every class realizes itself at bound `0`. -/
theorem holds_refl (f : Cell1 E O) : Holds f f 0 :=
  Quotient.inductionOn f fun _ _ => DistC.refl _

/-- Realization at statistical bounds is transitive; the bounds add. -/
theorem holds_trans {f g h : Cell1 E O} {ε δ : ℝ≥0∞} (hε : Holds f g ε) (hδ : Holds g h δ) :
    Holds f h (ε + δ) := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  induction h using Quotient.inductionOn
  exact Realizes.trans hε hδ

/-- The cascade of classes. -/
noncomputable def seq (f : Cell1 E O) (g : Cell1 O P) : Cell1 E P :=
  Quotient.map₂ LSysObj.seq (fun _ _ h₁ _ _ h₂ => Sys.StepEq.seq h₁ h₂) f g

/-- The cascade on the right of a realization at bound `ε` is a realization at bound `ε`. -/
theorem holds_seq_left {f f' : Cell1 E O} (g : Cell1 O P) {ε : ℝ≥0∞} (h : Holds f f' ε) :
    Holds (f.seq g) (f'.seq g) ε := by
  induction f using Quotient.inductionOn
  induction f' using Quotient.inductionOn
  induction g using Quotient.inductionOn with
  | h B => exact realizes_seq_left B.obj.sys B.noFail h

/-- The cascade on the left of a realization at bound `δ` is a realization at bound `δ`. -/
theorem holds_seq_right (f : Cell1 E O) {g g' : Cell1 O P} {δ : ℝ≥0∞} (h : Holds g g' δ) :
    Holds (f.seq g) (f.seq g') δ := by
  induction f using Quotient.inductionOn with
  | h A =>
    induction g using Quotient.inductionOn
    induction g' using Quotient.inductionOn
    exact realizes_seq_right A.obj.sys A.noFail h

open CategoryTheory

/-- The category of classes: a morphism from `f` to `g` is a statistical bound `ε` at which `f`
realizes `g`; composition adds the bounds. -/
noncomputable instance category (E O : Type) : Category.{0} (Cell1 E O) where
  Hom f g := {ε : ℝ≥0∞ // Holds f g ε}
  id f := ⟨0, holds_refl f⟩
  comp η θ := ⟨η.1 + θ.1, holds_trans η.2 θ.2⟩
  id_comp _ := Subtype.ext (zero_add _)
  comp_id _ := Subtype.ext (add_zero _)
  assoc _ _ _ := Subtype.ext (add_assoc _ _ _)

/-- Two 2-cells with equal bounds are equal. -/
theorem hom_ext {f g : Cell1 E O} {η θ : f ⟶ g} (h : η.1 = θ.1) : η = θ := Subtype.ext h

/-- Unfolding lemma of the composition of `Cell1.category`: the bound of a composite is the sum
of the bounds. -/
@[simp] theorem comp_val {f g h : Cell1 E O} (η : f ⟶ g) (θ : g ⟶ h) :
    (η ≫ θ).1 = η.1 + θ.1 := rfl

/-- Unfolding lemma of the identity of `Cell1.category`: its bound is `0`. -/
@[simp] theorem id_val (f : Cell1 E O) : (𝟙 f : f ⟶ f).1 = 0 := rfl

/-- The bound of the 2-cell of an equality is `0`. -/
@[simp] theorem eqToHom_val {f g : Cell1 E O} (h : f = g) : (eqToHom h).1 = 0 := by
  subst h
  rfl

/-- The cascade of classes is associative. -/
theorem seq_assoc {Q : Type} (f : Cell1 E O) (g : Cell1 O P) (h : Cell1 P Q) :
    (f.seq g).seq h = f.seq (g.seq h) := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  induction h using Quotient.inductionOn
  exact Quotient.sound (Sys.StepEq.seq_assoc _ _ _)

/-- The forwarding class is a left unit of the cascade. -/
theorem id_seq (f : Cell1 E O) : Cell1.seq (⟦LSysObj.idL E⟧ : Cell1 E E) f = f := by
  induction f using Quotient.inductionOn with
  | h A => exact Quotient.sound (Sys.StepEq.id_seq A.obj)

/-- The forwarding class is a right unit of the cascade. -/
theorem seq_id (f : Cell1 E O) : Cell1.seq f (⟦LSysObj.idL O⟧ : Cell1 O O) = f := by
  induction f using Quotient.inductionOn with
  | h A => exact Quotient.sound (Sys.StepEq.seq_id A.obj)

end Cell1

/-- A type of ports, a 0-cell of the bicategory of reactive systems. -/
structure RSysBicat : Type 1 where
  /-- The ports. -/
  P : Type

open CategoryTheory Cell1 in
/-- **The bicategory of reactive systems at statistical bounds.** The 0-cells are types of
ports, the 1-cells lossless systems modulo step equivalence with the cascade as composition and
the forwarding system as identity, the 2-cells from `f` to `g` statistical bounds `ε` at which
`f` realizes `g`. Vertical composition adds the bounds (`Realizes.trans`); whiskering keeps the
bound (`realizes_seq_left`, `realizes_seq_right`), so the horizontal composite of 2-cells with
bounds `ε` and `δ` has bound `ε + δ`. The associator and unitors are the equalities of classes
`Cell1.seq_assoc`, `Cell1.id_seq`, `Cell1.seq_id`, at bound `0`. -/
noncomputable instance RSysBicat.bicategory : Bicategory.{0, 1, 1} RSysBicat where
  Hom a b := Cell1 a.P b.P
  id a := ⟦LSysObj.idL a.P⟧
  comp f g := f.seq g
  homCategory a b := Cell1.category a.P b.P
  whiskerLeft f _ _ η := ⟨η.1, holds_seq_right f η.2⟩
  whiskerRight η h := ⟨η.1, holds_seq_left h η.2⟩
  associator f g h := eqToIso (seq_assoc f g h)
  leftUnitor f := eqToIso (id_seq f)
  rightUnitor f := eqToIso (seq_id f)
  whiskerLeft_id _ _ := hom_ext rfl
  whiskerLeft_comp _ _ _ _ _ _ := hom_ext rfl
  id_whiskerLeft _ := hom_ext (by simp)
  comp_whiskerLeft _ _ _ _ _ := hom_ext (by simp)
  id_whiskerRight _ _ := hom_ext rfl
  comp_whiskerRight _ _ _ := hom_ext rfl
  whiskerRight_id _ := hom_ext (by simp)
  whiskerRight_comp _ _ _ := hom_ext (by simp)
  whisker_assoc _ _ _ _ _ := hom_ext (by simp)
  whisker_exchange _ _ := hom_ext (add_comm _ _)
  pentagon _ _ _ _ := hom_ext (by simp)
  triangle _ _ := hom_ext (by simp)

end CatCrypt.Crypto.UCTransparent

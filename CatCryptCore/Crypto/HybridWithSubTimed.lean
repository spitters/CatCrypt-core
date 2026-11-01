/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of a hybrid machine composed with a sub-protocol system

`Sys.Timed`, the costed mirror of the reactive system `Sys` of UCTransparent, by
`derive_timed_structure`; the costed forms of the composition `Hybrid.withSub` of a hybrid
machine with a sub-protocol system and of the ideal world `ideal F S` of a transparent
functionality with a simulator, by `derive_reduction`; and their time theorems.

An activation of `π.withSub X` runs one `pre` step of `π`, one step of `X` and one `post` step
of `π`, so it costs the three step costs plus `3`. The ideal world appends an entry to its
trace and evaluates the guard of the functionality on the trace, whose costs grow with the
length of the trace, that is with the number of activations: its time bound is graded
(`Sys.Timed.TimeBoundGraded`), a step after `i` activations costing at most `a + b * i`, on an
invariant indexed by the number of activations. The composition with a graded sub-system is
graded with the same slope; a hybrid machine whose state grows with the activations has the
graded bound `Hybrid.Timed.TimeBoundGraded`, on an invariant and an intermediate invariant
between its `pre` and `post` steps, and its composition is graded with the sum of the slopes.

Search words: time certificate, simulator running time, costed sub-protocol composition,
copy simulator, ideal world, graded time bound.

## Main definitions

* `Sys.Timed`, `Sys.Timed.Erases`, `Sys.Timed.TimeBound`: costed reactive systems.
* `Sys.Timed.TimeBoundGraded`, `Hybrid.Timed.TimeBoundGraded`: graded time bounds of costed
  reactive systems and costed hybrid machines.
* `Hybrid.withSub.timed`, `Hybrid.Timed.withSub`: the costed composition.
* `ideal.timed`, `Sys.Timed.ideal`: the costed ideal world.

## Main results

* `Hybrid.Timed.withSub_erases`, `Hybrid.Timed.withSub_stepTime_le`,
  `Hybrid.Timed.withSub_timeBound`, `Hybrid.Timed.withSub_timeBoundGraded`,
  `Hybrid.Timed.withSub_timeBoundGraded_of_graded`: erasure and time bounds of the costed
  composition.
* `Sys.Timed.ideal_erases`, `Sys.Timed.ideal_timeBoundGraded`: erasure and graded time bound
  of the costed ideal world.
-/

@[expose] public section

set_option autoImplicit false

derive_timed_structure CatCrypt.Crypto.UCTransparent.Sys

derive_reduction CatCrypt.Crypto.UCTransparent.Hybrid.withSub

derive_reduction CatCrypt.Crypto.UCTransparent.ideal

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

variable {σ τ E O EG OG : Type}

/-- The graded time bound of a costed reactive system on the invariant `Inv`, indexed by the
number of activations: the initial state satisfies `Inv 0`, and a step from a state of `Inv i`
costs at most `a + b * i` and returns states of `Inv (i + 1)`. -/
def Sys.Timed.TimeBoundGraded (A : Sys.Timed τ E O) (Inv : ℕ → τ → Prop) (a b : ℕ) : Prop :=
  Inv 0 A.init ∧
  ∀ i s e, Inv i s → SPTree.Timed.stepTime (A.stepCost s e, A.step s e) ≤ a + b * i ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.step s e)

namespace Hybrid.Timed

/-- The costed composition of the costed hybrid machine `πT` with the costed sub-protocol
system `XT`: the costed form `Hybrid.withSub.timed π X` with the steps and cost companions of
`πT` and `XT`. -/
noncomputable def withSub (π : Hybrid σ E O EG OG) (X : Sys τ EG OG)
    (πT : Hybrid.Timed σ E O EG OG) (XT : Sys.Timed τ EG OG) : Sys.Timed (σ × τ) E O :=
  Hybrid.withSub.timed π X πT.pre πT.preCost XT.step XT.stepCost πT.post πT.postCost

/-- **Erasure of the costed composition**: the costed composition of a costed hybrid machine
that erases to `π` with a costed system that erases to `X` erases to `π.withSub X`. -/
theorem withSub_erases {π : Hybrid σ E O EG OG} {X : Sys τ EG OG}
    {πT : Hybrid.Timed σ E O EG OG} {XT : Sys.Timed τ EG OG} (hT : πT.Erases π)
    (hX : XT.Erases X) : (withSub π X πT XT).Erases (π.withSub X) := by
  obtain ⟨_, _, rfl⟩ := hT
  subst hX
  exact Hybrid.withSub.erase_timed _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- One activation of the costed composition from the state `s` on the event `e` costs at
most the bound `a` of the `pre` step at `(s.1, e)`, whose results satisfy `M`, a bound `B` of
the sub-protocol steps from `s.2`, the bound `c` of the `post` steps from states of `M`, and
`3`. -/
theorem withSub_stepTime_le (π : Hybrid σ E O EG OG) (X : Sys τ EG OG)
    (πT : Hybrid.Timed σ E O EG OG) (XT : Sys.Timed τ EG OG) (s : σ × τ) (e : E)
    {M : σ → Prop} {a B c : ℕ}
    (h1 : SPTree.Timed.stepTime (πT.preCost s.1 e, πT.pre s.1 e) ≤ a)
    (hM : SPTree.Timed.AllRet (fun y => M y.1) (πT.pre s.1 e))
    (hX : ∀ x, SPTree.Timed.stepTime (XT.stepCost s.2 x, XT.step s.2 x) ≤ B)
    (h3 : ∀ s o, M s → SPTree.Timed.stepTime (πT.postCost s o, πT.post s o) ≤ c) :
    SPTree.Timed.stepTime ((withSub π X πT XT).stepCost s e, (withSub π X πT XT).step s e) ≤
      a + B + c + 3 := by
  simp only [SPTree.Timed.stepTime] at h1 h3 hX
  have hpost : ∀ (x : σ × EG) (y : τ × OG), M x.1 →
      SPTree.Timed.stepTime (SPTree.Timed.delay (1 + πT.postCost x.1 y.2)
        ((πT.post x.1 y.2).bind fun z => (0, SPTree.Timed.ret ((z.1, y.1), z.2)))) ≤ c + 1 := by
    intro x y hx
    have := SPTree.Timed.stepTime_bind_le (πT.post x.1 y.2)
      (fun z => (0, SPTree.Timed.ret ((z.1, y.1), z.2))) 0
      (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    have := h3 x.1 y.2 hx
    simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at *
    omega
  have hsub : ∀ x : σ × EG, M x.1 →
      SPTree.Timed.stepTime (SPTree.Timed.delay (1 + XT.stepCost s.2 x.2)
        ((XT.step s.2 x.2).bind fun y =>
          SPTree.Timed.delay (1 + πT.postCost x.1 y.2)
            ((πT.post x.1 y.2).bind fun z => (0, SPTree.Timed.ret ((z.1, y.1), z.2))))) ≤
        B + c + 2 := by
    intro x hx
    have := SPTree.Timed.stepTime_bind_le (XT.step s.2 x.2) _ (c + 1) (fun y => hpost x y hx)
    have := hX x.2
    simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at *
    omega
  have := SPTree.Timed.stepTime_bind_le_of_allRet (πT.pre s.1 e) _ (B + c + 2) hM hsub
  simp only [withSub, Hybrid.withSub.timed, Hybrid.withSub.step.tree.timed,
    SPTree.Timed.stepTime, SPTree.Timed.delay] at *
  omega

/-- **Running time of the costed composition**: if the steps `pre` and `post` of `πT` cost at
most `a` and `c`, and a step of `XT` at most `b`, an activation of the costed composition, one
`pre` step, one sub-protocol step and one `post` step, costs at most `a + b + c + 3`. -/
theorem withSub_timeBound (π : Hybrid σ E O EG OG) (X : Sys τ EG OG)
    {πT : Hybrid.Timed σ E O EG OG} {XT : Sys.Timed τ EG OG} {a b c : ℕ}
    (hT : πT.TimeBound a c) (hX : XT.TimeBound b) :
    (withSub π X πT XT).TimeBound (a + b + c + 3) := fun s e =>
  withSub_stepTime_le π X πT XT s e (M := fun _ => True) (hT.1 s.1 e)
    (SPTree.Timed.allRet_of_forall (fun _ => trivial) _) (fun x => hX s.2 x)
    (fun s o _ => hT.2 s o)

/-- **Graded running time of the costed composition**: if the steps `pre` and `post` of `πT`
cost at most `a` and `c`, and the costed system `XT`, which erases to `X`, has the graded bound
`b₀ + b₁ * i` on the invariant `Inv`, the costed composition has the graded bound
`(a + b₀ + c + 3) + b₁ * i` on the invariant `Inv` of the sub-protocol state. -/
theorem withSub_timeBoundGraded (π : Hybrid σ E O EG OG) {X : Sys τ EG OG}
    {πT : Hybrid.Timed σ E O EG OG} {XT : Sys.Timed τ EG OG} {Inv : ℕ → τ → Prop}
    {a b₀ b₁ c : ℕ} (hT : πT.TimeBound a c) (hXe : XT.Erases X)
    (hX : XT.TimeBoundGraded Inv b₀ b₁) :
    (withSub π X πT XT).TimeBoundGraded (fun i s => Inv i s.2) (a + b₀ + c + 3) b₁ := by
  obtain ⟨h0, hs⟩ := hX
  have hinit : X.init = XT.init := by rw [hXe]
  refine ⟨by change Inv 0 X.init; rw [hinit]; exact h0, fun i s e hi => ⟨?_, ?_⟩⟩
  · have := withSub_stepTime_le π X πT XT s e (M := fun _ => True) (hT.1 s.1 e)
      (SPTree.Timed.allRet_of_forall (fun _ => trivial) _) (fun x => (hs i s.2 x hi).1)
      (fun s o _ => hT.2 s o)
    omega
  · simp only [withSub, Hybrid.withSub.timed, Hybrid.withSub.step.tree.timed,
      SPTree.Timed.delay]
    apply SPTree.Timed.allRet_bind_of
    apply SPTree.Timed.allRet_of_forall
    intro x
    apply SPTree.Timed.allRet_bind_of
    apply SPTree.Timed.allRet_mono _ _ (hs i s.2 x.2 hi).2
    intro y hy
    apply SPTree.Timed.allRet_bind_of
    exact SPTree.Timed.allRet_of_forall (fun _ => hy) _

/-- The graded time bound of a costed hybrid machine on the invariants `Inv` and `Mid`,
indexed by the number of activations: the initial state satisfies `Inv 0`; a `pre` step from
a state of `Inv i` costs at most `a + b * i` and returns states of `Mid i`; a `post` step from
a state of `Mid i` costs at most `a + b * i` and returns states of `Inv (i + 1)`. -/
def TimeBoundGraded (A : Hybrid.Timed σ E O EG OG) (Inv Mid : ℕ → σ → Prop) (a b : ℕ) :
    Prop :=
  Inv 0 A.init ∧
  (∀ i s e, Inv i s → SPTree.Timed.stepTime (A.preCost s e, A.pre s e) ≤ a + b * i ∧
    SPTree.Timed.AllRet (fun y => Mid i y.1) (A.pre s e)) ∧
  (∀ i s o, Mid i s → SPTree.Timed.stepTime (A.postCost s o, A.post s o) ≤ a + b * i ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.post s o))

/-- **Graded running time of the costed composition with a graded hybrid machine**: if the
costed hybrid machine `πT`, which erases to `π`, has the graded bound `a₀ + a₁ * i` on the
invariants `InvP` and `Mid`, and the costed system `XT`, which erases to `X`, the graded bound
`b₀ + b₁ * i` on the invariant `Inv`, the costed composition has the graded bound
`(2 * a₀ + b₀ + 3) + (2 * a₁ + b₁) * i` on the conjunction of the invariants of the two
components: an activation runs one `pre` step, one sub-protocol step and one `post` step. -/
theorem withSub_timeBoundGraded_of_graded {π : Hybrid σ E O EG OG} {X : Sys τ EG OG}
    {πT : Hybrid.Timed σ E O EG OG} {XT : Sys.Timed τ EG OG} {InvP Mid : ℕ → σ → Prop}
    {Inv : ℕ → τ → Prop} {a₀ a₁ b₀ b₁ : ℕ} (hTe : πT.Erases π)
    (hT : πT.TimeBoundGraded InvP Mid a₀ a₁) (hXe : XT.Erases X)
    (hX : XT.TimeBoundGraded Inv b₀ b₁) :
    (withSub π X πT XT).TimeBoundGraded (fun i s => InvP i s.1 ∧ Inv i s.2)
      (2 * a₀ + b₀ + 3) (2 * a₁ + b₁) := by
  obtain ⟨hp0, hpre, hpost⟩ := hT
  obtain ⟨h0, hs⟩ := hX
  have hinit : X.init = XT.init := by rw [hXe]
  have hinitP : π.init = πT.init := by obtain ⟨_, _, rfl⟩ := hTe; rfl
  refine ⟨by change InvP 0 π.init ∧ Inv 0 X.init; rw [hinit, hinitP]; exact ⟨hp0, h0⟩,
    fun i s e ⟨hi, hj⟩ => ⟨?_, ?_⟩⟩
  · have := withSub_stepTime_le π X πT XT s e (hpre i s.1 e hi).1
      (hpre i s.1 e hi).2 (fun x => (hs i s.2 x hj).1) (fun s o hm => (hpost i s o hm).1)
    simp only [Nat.add_mul, Nat.two_mul] at this ⊢
    omega
  · simp only [withSub, Hybrid.withSub.timed, Hybrid.withSub.step.tree.timed,
      SPTree.Timed.delay]
    apply SPTree.Timed.allRet_bind_of
    apply SPTree.Timed.allRet_mono _ _ (hpre i s.1 e hi).2
    intro x hx
    apply SPTree.Timed.allRet_bind_of
    apply SPTree.Timed.allRet_mono _ _ (hs i s.2 x.2 hj).2
    intro y hy
    apply SPTree.Timed.allRet_bind_of
    exact SPTree.Timed.allRet_mono (fun z hz => ⟨hz, hy⟩) _ (hpost i x.1 y.2 hx).2

end Hybrid.Timed

namespace Sys.Timed

variable {σ E O : Type}

/-- The costed ideal world of the transparent functionality `F` over the costed simulator
`ST`: the costed form `ideal.timed F S` with the trace appended by `++` at the cost
`appendCost`, the guard of `F` evaluated at the cost `guardCost`, and the step of `ST`. -/
noncomputable def ideal (F : TFunc σ E O) (S : Sys σ E O) (ST : Sys.Timed σ E O)
    (appendCost : Trace σ E O → List (E × O × σ) → ℕ) (guardCost : Trace σ E O → ℕ) :
    Sys.Timed (σ × Trace σ E O × Bool) E O :=
  ideal.timed F S (· ++ ·) appendCost F.guard guardCost ST.step ST.stepCost

/-- **Erasure of the costed ideal world**: over a costed simulator that erases to `S`, the
costed ideal world erases to `ideal F S`. -/
theorem ideal_erases {F : TFunc σ E O} {S : Sys σ E O} {ST : Sys.Timed σ E O}
    (appendCost : Trace σ E O → List (E × O × σ) → ℕ) (guardCost : Trace σ E O → ℕ)
    (hS : ST.Erases S) :
    (Sys.Timed.ideal F S ST appendCost guardCost).Erases (UCTransparent.ideal F S) :=
  ideal.erase_timed F S appendCost guardCost ST.step ST.stepCost fun _ _ => by rw [hS]

/-- **Graded running time of the costed ideal world**: let the costed simulator `ST`, which
erases to `S`, have the graded bound `s₀ + s₁ * i` on the invariant `Inv`, let appending an
entry to a trace of length `l` cost at most `h₀ + h₁ * l`, and evaluating the guard on a trace
of length `l` cost at most `g₀ + g₁ * l`. Then the costed ideal world has the graded bound
`(s₀ + h₀ + g₀ + g₁ + 8) + (s₁ + h₁ + g₁) * i` on the invariant: the simulator state satisfies
`Inv i` and the trace has length `i`. -/
theorem ideal_timeBoundGraded (F : TFunc σ E O) {S : Sys σ E O} {ST : Sys.Timed σ E O}
    {appendCost : Trace σ E O → List (E × O × σ) → ℕ} {guardCost : Trace σ E O → ℕ}
    {Inv : ℕ → σ → Prop} {s₀ s₁ h₀ h₁ g₀ g₁ : ℕ} (hSe : ST.Erases S)
    (hS : ST.TimeBoundGraded Inv s₀ s₁)
    (hA : ∀ tr l, appendCost tr l ≤ h₀ + h₁ * tr.length)
    (hG : ∀ tr, guardCost tr ≤ g₀ + g₁ * tr.length) :
    (Sys.Timed.ideal F S ST appendCost guardCost).TimeBoundGraded
      (fun i t => Inv i t.1 ∧ t.2.1.length = i) (s₀ + h₀ + g₀ + g₁ + 8) (s₁ + h₁ + g₁) := by
  obtain ⟨h0, hs⟩ := hS
  have hinit : S.init = ST.init := by rw [hSe]
  refine ⟨⟨by change Inv 0 S.init; rw [hinit]; exact h0, rfl⟩,
    fun i t e ⟨hi, hl⟩ => ⟨?_, ?_⟩⟩
  · have hstep := (hs i t.1 e hi).1
    simp only [SPTree.Timed.stepTime] at hstep
    have key : ∀ f : σ × O → ℕ × SPTree.Timed ((σ × Trace σ E O × Bool) × O),
        (∀ x, SPTree.Timed.stepTime (f x) ≤ h₀ + h₁ * i + (g₀ + g₁ * (i + 1)) + 7) →
        1 + ST.stepCost t.1 e + ((ST.step t.1 e).bind f).1 + ((ST.step t.1 e).bind f).2.time ≤
          s₀ + h₀ + g₀ + g₁ + 8 + (s₁ + h₁ + g₁) * i := by
      intro f hf
      have := SPTree.Timed.stepTime_bind_le (ST.step t.1 e) f _ hf
      simp only [SPTree.Timed.stepTime, Nat.mul_add, Nat.add_mul, Nat.mul_one] at this ⊢
      omega
    simp only [Sys.Timed.ideal, ideal.timed, ideal.step.tree.timed, SPTree.Timed.delay,
      SPTree.Timed.stepTime]
    refine key _ fun x => ?_
    have h1 := hA t.2.1 [(e, x.2, x.1)]
    have h2 := hG (t.2.1 ++ [(e, x.2, x.1)])
    simp only [List.length_append, List.length_singleton, hl] at h1 h2
    simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
    omega
  · simp only [Sys.Timed.ideal, ideal.timed, ideal.step.tree.timed, SPTree.Timed.delay]
    apply SPTree.Timed.allRet_bind_of
    apply SPTree.Timed.allRet_mono _ _ (hs i t.1 e hi).2
    intro y hy
    exact ⟨hy, by simp [hl]⟩

end Sys.Timed

end CatCrypt.Crypto.UCTransparent

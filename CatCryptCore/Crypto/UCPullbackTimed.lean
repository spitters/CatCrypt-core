/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCPullback
public import CatCryptCore.Crypto.UCConcreteTimed
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Crypto.UCSimulatorCostGraded
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimedStructure

/-!
# Time certificates of the environment reductions of the pullback law

The pullback law of `UCPullback.lean` maps a realization `R ≤_b I` along a context `C` to
`C[R] ≤_{b ∘ (·C)} C[I]`, where `Z ↦ Z·C` is the environment reduction of the context. This
file gives the costed forms of these reductions and their time theorems: per activation, the
reduced environment costs at most an activation of `Z`, an activation of the context and a
constant, `T(Z·C) ≤ T(Z) + T(C) + c`.

`Strat.Timed` and `UCConcrete.Env.Timed` are the costed mirrors of strategies and of
`UCConcrete` environments, by `derive_timed_structure`. `derive_reduction` gives the costed
forms of the environment reductions of a hybrid context (`Hybrid.reduce`, `Hybrid.reduceEnv`),
of a multi-call hybrid context (`MultiHybrid.reduce`), of an adversary system read as a hybrid
machine (`AdvSys.toHybrid`) and of adversary absorption (`Strat.absorb`), each with its erasure
theorem `erase_timed`. The time theorems of the multi-call reduction are derived by
`derive_time_bound`; those of the hybrid reduction and of absorption are proved from the step
bounds, with the uniform bound `Strat.Timed.TimeBound` and, for the hybrid reduction, the
graded bound `StratRunBound` of `UCConcreteTimed.lean`, whose run-time theorem
`view.tree.timeBound_timed` then bounds the whole run of the reduced environment.

Search words: time certificate, environment reduction, costed strategy, costed environment,
pullback, context action, activation time, adversary absorption.

## Main definitions

* `Strat.Timed`, `UCConcrete.Env.Timed`: costed strategies and environments.
* `Hybrid.reduce.timed`, `Hybrid.reduceEnv.timed`, `MultiHybrid.reduce.timed`,
  `AdvSys.toHybrid.timed`, `Strat.absorb.timed`: the costed reductions.
* `Hybrid.Timed.reduce`: the costed hybrid reduction over a costed hybrid machine and a costed
  strategy.

## Main results

* `Hybrid.Timed.reduce_erases`: erasure of the costed hybrid reduction.
* `Hybrid.Timed.reduce_timeBound`: `next` costs at most `n + a + 2`, `obs` at most
  `c + o + 2`.
* `Hybrid.Timed.reduce_stratRunBound`: the graded form, `tN i + a + 2` and `c + tO i + 2`.
* `Hybrid.Timed.reduceEnv_dist_le`: the distinguisher of the reduced environment.
* `Strat.absorb_timeBound`: absorption of an adversary, `n + a + 4` and `c + o + 2`.
* `Strat.Timed.TimeBound.mono`: the uniform bound holds at larger bounds.
* `MultiHybrid.reduce.next.tree.timeBound_timed`, `MultiHybrid.reduce.obs.tree.timeBound_timed`:
  the multi-call reduction.
-/

@[expose] public section

set_option autoImplicit false

derive_timed_structure CatCrypt.Crypto.UCTransparent.Strat

derive_timed_structure CatCrypt.Crypto.UCConcrete.Env

namespace CatCrypt.Crypto.UCTransparent

derive_reduction Hybrid.reduce

derive_reduction Hybrid.reduceEnv

derive_time_bound Hybrid.reduceEnv.dist.tree

derive_reduction MultiHybrid.reduce

derive_reduction AdvSys.toHybrid

derive_reduction Strat.absorb

open CatCrypt.Core

namespace Hybrid.Timed

variable {σ ζ E O EG OG : Type}

/-- The costed environment reduction of a hybrid context: the costed form
`Hybrid.reduce.timed π Z` with the steps and cost companions of the costed hybrid machine `πT`
and of the costed strategy `ZT`. -/
noncomputable def reduce (π : Hybrid σ E O EG OG) (Z : Strat ζ E O)
    (πT : Hybrid.Timed σ E O EG OG) (ZT : Strat.Timed ζ E O) : Strat.Timed (ζ × σ) EG OG :=
  Hybrid.reduce.timed π Z ZT.next ZT.nextCost πT.pre πT.preCost πT.post πT.postCost ZT.obs
    ZT.obsCost

/-- **Erasure of the costed environment reduction**: over a costed hybrid machine that erases
to `π` and a costed strategy that erases to `Z`, the costed reduction erases to `π.reduce Z`. -/
theorem reduce_erases {π : Hybrid σ E O EG OG} {Z : Strat ζ E O}
    {πT : Hybrid.Timed σ E O EG OG} {ZT : Strat.Timed ζ E O} (hT : πT.Erases π)
    (hZ : ZT.Erases Z) : (reduce π Z πT ZT).Erases (π.reduce Z) := by
  obtain ⟨_, _, rfl⟩ := hT
  obtain ⟨_, _, rfl⟩ := hZ
  exact Hybrid.reduce.erase_timed _ _ _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- **Running time of the costed environment reduction**: if the steps `next` and `obs` of the
costed strategy cost at most `n` and `o`, and the steps `pre` and `post` of the costed hybrid
machine at most `a` and `c`, then a `next` step of the reduced strategy costs at most
`n + a + 2` and an `obs` step at most `c + o + 2`: per activation, `T(Z·C) ≤ T(Z) + T(C) + 4`. -/
theorem reduce_timeBound (π : Hybrid σ E O EG OG) (Z : Strat ζ E O)
    {πT : Hybrid.Timed σ E O EG OG} {ZT : Strat.Timed ζ E O} {n o a c : ℕ}
    (hT : πT.TimeBound a c) (hZ : ZT.TimeBound n o) :
    (reduce π Z πT ZT).TimeBound (n + a + 2) (c + o + 2) := by
  refine ⟨fun zs => ?_, fun zs g => ?_⟩
  · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (ZT.nextCost zs.1, ZT.next zs.1)
      (fun x => (πT.preCost zs.2 x.2, πT.pre zs.2 x.2))
      (fun x y => (0, SPTree.Timed.ret ((x.1, y.1), y.2)))
      (hZ.1 zs.1) (SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (fun x _ => hT.1 zs.2 x.2) (fun _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (TF := 0) (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    simp only [reduce, Hybrid.reduce.timed, Hybrid.reduce.next.tree.timed] at this ⊢
    grind
  · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (πT.postCost zs.2 g, πT.post zs.2 g)
      (fun r => (ZT.obsCost zs.1 r.2, ZT.obs zs.1 r.2))
      (fun r z => (0, SPTree.Timed.ret (z, r.1)))
      (hT.2 zs.2 g) (SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (fun r _ => hZ.2 zs.1 r.2) (fun _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (TF := 0) (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    simp only [reduce, Hybrid.reduce.timed, Hybrid.reduce.obs.tree.timed] at this ⊢
    grind

/-- **Graded running time of the costed environment reduction**: if the costed strategy has
the graded bound `tN i`, `tO i` on the invariants `InvZ`, `MidZ` over the interface predicates
`Ev`, `Out`, the `post` outputs of the costed hybrid machine lie in `Out i`, and its steps `pre`
and `post` cost at most `a` and `c`, then the reduced strategy has the graded bound
`tN i + a + 2`, `c + tO i + 2` on the invariants of the first component: activation `i` of the
reduced environment costs at most activation `i` of `Z`, one activation of the context, and
`4`. -/
theorem reduce_stratRunBound (π : Hybrid σ E O EG OG) (Z : Strat ζ E O)
    {πT : Hybrid.Timed σ E O EG OG} {ZT : Strat.Timed ζ E O} {InvZ MidZ : ℕ → ζ → Prop}
    {Ev : ℕ → E → Prop} {Out : ℕ → O → Prop} {tN tO : ℕ → ℕ} {a c : ℕ}
    (hT : πT.TimeBound a c)
    (hOut : ∀ i s g, SPTree.Timed.AllRet (fun r => Out i r.2) (πT.post s g))
    (hZ : StratRunBound ZT.next ZT.nextCost ZT.obs ZT.obsCost InvZ MidZ Ev Out tN tO) :
    StratRunBound (reduce π Z πT ZT).next (reduce π Z πT ZT).nextCost (reduce π Z πT ZT).obs
      (reduce π Z πT ZT).obsCost (fun i zs => InvZ i zs.1) (fun i zs => MidZ i zs.1)
      (fun _ _ => True) (fun _ _ => True) (fun i => tN i + a + 2) (fun i => c + tO i + 2) := by
  refine ⟨fun i zs h => ?_, fun i zs h => ?_, fun i zs g h _ => ?_, fun i zs g h _ => ?_⟩
  · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (ZT.nextCost zs.1, ZT.next zs.1)
      (fun x => (πT.preCost zs.2 x.2, πT.pre zs.2 x.2))
      (fun x y => (0, SPTree.Timed.ret ((x.1, y.1), y.2)))
      (hZ.next_time i zs.1 h) (SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (fun x _ => hT.1 zs.2 x.2) (fun _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (TF := 0) (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    simp only [reduce, Hybrid.reduce.timed, Hybrid.reduce.next.tree.timed] at this ⊢
    grind
  · simp only [reduce, Hybrid.reduce.timed, Hybrid.reduce.next.tree.timed, SPTree.Timed.delay,
      SPTree.Timed.allRet_bind]
    exact SPTree.Timed.allRet_mono (fun x hx => SPTree.Timed.allRet_of_forall
      (fun _ => ⟨hx.1, trivial⟩) _) _ (hZ.next_ret i zs.1 h)
  · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (πT.postCost zs.2 g, πT.post zs.2 g)
      (fun r => (ZT.obsCost zs.1 r.2, ZT.obs zs.1 r.2))
      (fun r z => (0, SPTree.Timed.ret (z, r.1)))
      (hT.2 zs.2 g) (hOut i zs.2 g)
      (fun r hr => hZ.obs_time i zs.1 r.2 h hr)
      (fun _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (TF := 0) (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    simp only [reduce, Hybrid.reduce.timed, Hybrid.reduce.obs.tree.timed] at this ⊢
    grind
  · simp only [reduce, Hybrid.reduce.timed, Hybrid.reduce.obs.tree.timed, SPTree.Timed.delay,
      SPTree.Timed.allRet_bind]
    exact SPTree.Timed.allRet_mono (fun r hr => SPTree.Timed.allRet_mono
      (fun z hz => hz) _ (hZ.obs_ret i zs.1 r.2 h hr)) _ (hOut i zs.2 g)

/-- **Running time of the costed distinguisher of the reduced environment**: on the state
`zs`, it costs at most the cost of the distinguisher of `Z` on `zs.1` plus `1`. -/
theorem reduceEnv_dist_le (π : Hybrid σ E O EG OG) (Z : UCConcrete.Env (Strat ζ E O) ζ)
    (dist : ζ → SPTree.Timed Bool) (distCost : ζ → ℕ) (zs : ζ × σ) {tD : ℕ}
    (hd : SPTree.Timed.stepTime (distCost zs.1, dist zs.1) ≤ tD) :
    SPTree.Timed.stepTime (Hybrid.reduceEnv.dist.tree.timed π Z dist distCost zs) ≤ tD + 1 := by
  grind [Hybrid.reduceEnv.dist.tree.timed, SPTree.Timed.stepTime]

end Hybrid.Timed

derive_time_bound MultiHybrid.reduce.next.tree

derive_time_bound MultiHybrid.reduce.obs.tree

set_option linter.auxLemma false in
/-- **Running time of the costed adversary absorption**: if the steps `next` and `obs` of the
costed strategy cost at most `n` and `o`, and the steps `act` and `out` of the costed adversary
at most `a` and `c`, then a `next` step of the absorbed strategy costs at most `n + a + 4` and
an `obs` step at most `c + o + 2`. -/
theorem Strat.absorb_timeBound {α AI AP Lk Lk' P Oh ζ : Type}
    (Z : Strat ζ (Event P AI) (Oh × Lk')) (A : AdvSys α AI AP Lk Lk')
    {ZT : Strat.Timed ζ (Event P AI) (Oh × Lk')} (act : α → AI → SPTree.Timed (α × AP))
    (actCost : α → AI → ℕ) (out : α → Lk → SPTree.Timed (α × Lk')) (outCost : α → Lk → ℕ)
    {n o a c : ℕ} (hZ : ZT.TimeBound n o)
    (ha : ∀ s i, SPTree.Timed.stepTime (actCost s i, act s i) ≤ a)
    (hc : ∀ s l, SPTree.Timed.stepTime (outCost s l, out s l) ≤ c) :
    (Strat.absorb.timed Z A ZT.next ZT.nextCost act actCost out outCost ZT.obs
      ZT.obsCost).TimeBound (n + a + 4) (c + o + 2) := by
  refine ⟨fun zs => ?_, fun zs l => ?_⟩
  · have hm : ∀ x : ζ × Event P AI, SPTree.Timed.stepTime
        (Strat.absorb.next.tree.match_1.timed zs act actCost x) ≤ a + 2 := by
      intro x
      rcases x with ⟨z, p | i⟩
      · simp [Strat.absorb.next.tree.match_1.timed, SPTree.Timed.stepTime,
          SPTree.Timed.delay, SPTree.Timed.time_ret]
      · have h1 := SPTree.Timed.stepTime_bind_le (act zs.2 i)
          (fun y => (0, SPTree.Timed.ret (y.1, (Sum.inr y.2 : Event P AP)))) 0
          (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        have h2 := ha zs.2 i
        simp only [Strat.absorb.next.tree.match_1.timed, SPTree.Timed.stepTime,
          SPTree.Timed.delay] at h1 h2 ⊢
        omega
    have := SPTree.Timed.stepTime_bind_bind_le 1 1 (ZT.nextCost zs.1, ZT.next zs.1)
      (fun x => Strat.absorb.next.tree.match_1.timed zs act actCost x)
      (fun x y => (0, SPTree.Timed.ret ((x.1, y.1), y.2)))
      (hZ.1 zs.1) (SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (fun x _ => hm x) (fun _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
      (TF := 0) (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    simp only [Strat.absorb.timed, Strat.absorb.next.tree.timed] at this ⊢
    grind
  · have := SPTree.Timed.stepTime_delay_bind_bind_le (1 + outCost zs.2 l.2, out zs.2 l.2)
      (fun x => (0, SPTree.Timed.ret (x.1, l.1, x.2)))
      (fun x => SPTree.Timed.delay (1 + ZT.obsCost zs.1 x.2)
        ((ZT.obs zs.1 x.2).bind fun z => (0, SPTree.Timed.ret (z, x.1)))) 0 (o + 1)
      (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
      (fun x => by
        have h1 := SPTree.Timed.stepTime_bind_le (ZT.obs zs.1 x.2)
          (fun z => (0, SPTree.Timed.ret (z, x.1))) 0
          (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        have h2 := hZ.2 zs.1 x.2
        simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at h1 h2 ⊢
        omega)
    have h3 := hc zs.2 l.2
    simp only [Strat.absorb.timed, Strat.absorb.obs.tree.timed] at this ⊢
    simp only [SPTree.Timed.stepTime] at h3 this ⊢
    grind

/-- A time bound of a costed strategy holds at larger bounds. -/
theorem Strat.Timed.TimeBound.mono {ζ E O : Type} {ZT : Strat.Timed ζ E O} {n o n' o' : ℕ}
    (h : ZT.TimeBound n o) (hn : n ≤ n') (ho : o ≤ o') : ZT.TimeBound n' o' :=
  ⟨fun z => (h.1 z).trans hn, fun z g => (h.2 z g).trans ho⟩

end CatCrypt.Crypto.UCTransparent

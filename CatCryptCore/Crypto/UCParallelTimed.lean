/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCParallel
public import CatCryptCore.Crypto.UCPullbackCost
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Crypto.HybridWithSubTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Parallel composition with time certificates

The parallel composition `X.par Y` (`UCParallel.lean`) is the context `parCtxL Y hY` of `Y`
over `X`, and the context `parCtxR X hX` of `X` over `Y`; both are multi-call hybrids. This file
makes multi-call hybrids costed pullbacks (`CostedPullback`, `UCPullbackCost.lean`) and states
parallel composition against the environments of time `(n, o, q, tD)` (`RealizesTime`).

A multi-call hybrid `π` with a costed machine `πT` erasing to it, whose steps `start`, `resume`
and `finish` cost at most `a`, `r` and `f`, is the costed pullback
`MultiHybrid.toCostedPullback π idle πT hE hT`. Its costed reductions are the derived
`MultiHybrid.reduce.timed` and `MultiHybrid.reduceEnv.timed`. One activation of the reduced
environment runs at most one activation of `Z` and one step of `π`, so the constants are
`nextC = a + 6`, `obsC = f + r + 4` and `distC = 1`. Each activation of `Z` becomes
`π.calls = π.fuel + 1` activations of the reduced environment, so the activation count is
multiplied by `π.fuel + 1` (`roundsMul`, with `roundsAdd = 0`).

The costed forms `parCtxL.timed` and `parCtxR.timed` of the parallel contexts are derived by
`derive_reduction` from a costed form `YT` (resp. `XT`) of the fixed component (`Sys.Timed`,
`HybridWithSubTimed.lean`). If each activation of the fixed component costs at most `s`, then
`start` costs at most `s + 3` and `resume`, `finish` cost `0`
(`parCtxL.timed_timeBound`, `parCtxR.timed_timeBound`). The contexts have fuel `0`, so the
costed pullbacks `parCtxL.toCosted` and `parCtxR.toCosted` keep the activation count. They give
a component the environments of time `(n + (s + 9), o + 4, q, tD + 1)`, where `s` is the time
of an activation of the other component.

The time-graded composition theorem for two holes (`CostedPullback.realizesTime_twoHole`)
combines the time-graded pullback laws of the two holes. With the two parallel contexts it
gives `realizes_par_timed`.

Search words: parallel composition, costed pullback, multi-call hybrid, time certificate,
activation time, activation count, bounded environment, composition theorem.

## Main definitions

* `MultiHybrid.Timed.reduce`: the costed reduction by a multi-call hybrid over a costed machine
  and a costed strategy.
* `MultiHybrid.toCostedPullback`: a multi-call hybrid as a costed pullback.
* `MultiHybrid.parCtxL.toCosted`, `MultiHybrid.parCtxR.toCosted`: the costed parallel
  contexts.

## Main results

* `MultiHybrid.Timed.reduce_erases`, `MultiHybrid.Timed.reduce_timeBound`: erasure and time of
  the costed multi-call reduction, `n + (a + 6)` and `o + (f + r + 4)`.
* `MultiHybrid.parCtxL.timed_timeBound`, `MultiHybrid.parCtxR.timed_timeBound`: the time of
  the costed parallel contexts.
* `CostedPullback.realizesTime_twoHole`: the time-graded composition theorem for two holes.
* `realizes_par_left_timed`, `realizes_par_right_timed`, `realizes_par_timed`: parallel
  composition against the environments of time `(n, o, q, tD)`, each component against the
  environments of time `(n + (s + 9), o + 4, q, tD + 1)`, with `s` the time of an activation of
  the other component.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

derive_reduction MultiHybrid.reduceEnv

derive_reduction MultiHybrid.parCtxL

derive_reduction MultiHybrid.parCtxR

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

namespace MultiHybrid.Timed

variable {σ ζ E O EG OG : Type}

/-- The costed environment reduction of a multi-call hybrid: the derived
`MultiHybrid.reduce.timed π idle Z` with the steps and cost companions of the costed machine
`πT` and of the costed strategy `ZT`. -/
noncomputable def reduce (π : MultiHybrid σ E O EG OG) (idle : EG) (Z : Strat ζ E O)
    (πT : MultiHybrid.Timed σ E O EG OG) (ZT : Strat.Timed ζ E O) :
    Strat.Timed (RState σ ζ EG O) EG OG :=
  MultiHybrid.reduce.timed π idle Z ZT.next ZT.nextCost πT.start πT.startCost πT.finish
    πT.finishCost ZT.obs ZT.obsCost πT.resume πT.resumeCost

/-- **Erasure of the costed multi-call reduction**: over a costed machine that erases to `π`
and a costed strategy that erases to `Z`, the costed reduction erases to `π.reduce idle Z`. -/
theorem reduce_erases {π : MultiHybrid σ E O EG OG} {idle : EG} {Z : Strat ζ E O}
    {πT : MultiHybrid.Timed σ E O EG OG} {ZT : Strat.Timed ζ E O} (hT : πT.Erases π)
    (hZ : ZT.Erases Z) : (reduce π idle Z πT ZT).Erases (π.reduce idle Z) := by
  obtain ⟨_, _, _, rfl⟩ := hT
  obtain ⟨_, _, rfl⟩ := hZ
  exact MultiHybrid.reduce.erase_timed _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

set_option linter.auxLemma false in
/-- **Running time of the costed multi-call reduction**: if the steps `next` and `obs` of the
costed strategy cost at most `n` and `o`, and the steps `start`, `resume` and `finish` of the
costed machine at most `a`, `r` and `f`, then a `next` step of the reduced strategy costs at most
`n + (a + 6)` and an `obs` step at most `o + (f + r + 4)`. -/
theorem reduce_timeBound (π : MultiHybrid σ E O EG OG) (idle : EG) (Z : Strat ζ E O)
    {πT : MultiHybrid.Timed σ E O EG OG} {ZT : Strat.Timed ζ E O} {n o a r f : ℕ}
    (hT : πT.TimeBound a r f) (hZ : ZT.TimeBound n o) :
    (reduce π idle Z πT ZT).TimeBound (n + (a + 6)) (o + (f + r + 4)) := by
  refine ⟨fun zs => ?_, fun zs g => ?_⟩
  · rcases zs with ⟨z, s, _ | ⟨d, k⟩⟩
    · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (ZT.nextCost z, ZT.next z)
        (fun x => (πT.startCost s x.2, πT.start s x.2))
        (fun x y => (2, SPTree.Timed.ret ((x.1, y.1, some (y.2, π.fuel)), evOf idle y.2)))
        (hZ.1 z) (SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
        (fun x _ => hT.1 s x.2) (fun _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
        (TF := 2) (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
      simp only [reduce, MultiHybrid.reduce.timed, MultiHybrid.reduce.next.tree.timed,
        MultiHybrid.reduce.next.tree.match_1.timed, SPTree.Timed.stepTime,
        SPTree.Timed.delay] at this ⊢
      omega
    · simp [reduce, MultiHybrid.reduce.timed, MultiHybrid.reduce.next.tree.timed,
        MultiHybrid.reduce.next.tree.match_1.timed, SPTree.Timed.stepTime,
        SPTree.Timed.delay, SPTree.Timed.time_ret]
      omega
  · rcases zs with ⟨z, s, _ | ⟨_ | d, _ | k⟩⟩
    · simp [reduce, MultiHybrid.reduce.timed, MultiHybrid.reduce.obs.tree.timed,
        MultiHybrid.reduce.obs.tree.match_1.timed, SPTree.Timed.stepTime,
        SPTree.Timed.delay, SPTree.Timed.time_ret]
      omega
    · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (πT.finishCost s g, πT.finish s g)
        (fun x => (ZT.obsCost z x.2, ZT.obs z x.2))
        (fun x y => (0, SPTree.Timed.ret (y, x.1, (none : Option ((EG ⊕ O) × ℕ)))))
        (hT.2.2 s g) (SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
        (fun x _ => hZ.2 z x.2) (fun _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _)
        (TF := 0) (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
      simp only [reduce, MultiHybrid.reduce.timed, MultiHybrid.reduce.obs.tree.timed,
        MultiHybrid.reduce.obs.tree.match_1.timed, SPTree.Timed.stepTime,
        SPTree.Timed.delay] at this ⊢
      omega
    · have := SPTree.Timed.stepTime_bind_le (πT.resume s g)
        (fun x => (0, SPTree.Timed.ret (z, x.1, some (x.2, k)))) 0
        (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
      have h2 := hT.2.1 s g
      simp only [reduce, MultiHybrid.reduce.timed, MultiHybrid.reduce.obs.tree.timed,
        MultiHybrid.reduce.obs.tree.match_1.timed, SPTree.Timed.stepTime,
        SPTree.Timed.delay] at this h2 ⊢
      omega
    · have := SPTree.Timed.stepTime_bind_le (ZT.obs z d)
        (fun x => (0, SPTree.Timed.ret (x, s, (none : Option ((EG ⊕ O) × ℕ))))) 0
        (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
      have h2 := hZ.2 z d
      simp only [reduce, MultiHybrid.reduce.timed, MultiHybrid.reduce.obs.tree.timed,
        MultiHybrid.reduce.obs.tree.match_1.timed, SPTree.Timed.stepTime,
        SPTree.Timed.delay] at this h2 ⊢
      omega
    · simp [reduce, MultiHybrid.reduce.timed, MultiHybrid.reduce.obs.tree.timed,
        MultiHybrid.reduce.obs.tree.match_1.timed, SPTree.Timed.stepTime,
        SPTree.Timed.delay, SPTree.Timed.time_ret]
      omega

end MultiHybrid.Timed

namespace MultiHybrid

variable {σ ζ E O EG OG : Type}

/-- A multi-call hybrid with a costed machine `πT` erasing to it, whose steps `start`,
`resume` and `finish` cost at most `a`, `r` and `f`, as a costed pullback: the costed reductions
are `MultiHybrid.Timed.reduce` and the derived `MultiHybrid.reduceEnv.timed`, the constants are
`a + 6`, `f + r + 4` and `1`, and the activation count is multiplied by `π.fuel + 1`, the number
of calls of an activation. -/
noncomputable def toCostedPullback (π : MultiHybrid σ E O EG OG) (idle : EG)
    (πT : MultiHybrid.Timed σ E O EG OG) {a r f : ℕ} (hE : πT.Erases π)
    (hT : πT.TimeBound a r f) : CostedPullback EG OG E O where
  toEnvPullback := π.toEnvPullback idle
  pullT Z ZT := MultiHybrid.Timed.reduce π idle Z.input πT ZT
  pullE Z ZE := MultiHybrid.reduceEnv.timed π idle Z ZE.dist ZE.distCost
  nextC := a + 6
  obsC := f + r + 4
  distC := 1
  roundsMul := π.fuel + 1
  roundsAdd := 0
  pullT_erases Z ZT h := by
    change (MultiHybrid.Timed.reduce π idle Z.input πT ZT).Erases
      ((π.toEnvPullback idle).pull Z).input
    rw [toEnvPullback_pull]
    exact MultiHybrid.Timed.reduce_erases hE h
  pullE_erases Z ZE h := by
    change (MultiHybrid.reduceEnv.timed π idle Z ZE.dist ZE.distCost).Erases
      ((π.toEnvPullback idle).pull Z)
    rw [toEnvPullback_pull]
    exact MultiHybrid.reduceEnv.erase_timed π idle Z _ _ fun _ => by rw [h]
  pullT_timeBound Z ZT n o h := MultiHybrid.Timed.reduce_timeBound π idle Z.input hT h
  pullE_dist_le Z ZE tD h w := by
    have := h w.1
    simp only [MultiHybrid.reduceEnv.timed, MultiHybrid.reduceEnv.dist.tree.timed,
      SPTree.Timed.stepTime] at this ⊢
    omega
  pull_rounds_le Z := by
    rw [toEnvPullback_pull]
    simp [MultiHybrid.reduceEnv, MultiHybrid.reduce, MultiHybrid.calls, Nat.mul_comm]

variable {τ υ E' O' : Type}

set_option linter.auxLemma false in
/-- **Time of the costed left parallel context**: over a costed form `YT` of `Y` whose
activations cost at most `s`, `start` costs at most `s + 3` and `resume`, `finish` cost `0`. -/
theorem parCtxL.timed_timeBound (Y : Sys υ E' O') (hY : ∀ u e, SPComp.NoFail (Y.step u e))
    (YT : Sys.Timed υ E' O') {s : ℕ} (hT : YT.TimeBound s) :
    (parCtxL.timed (E := E) (O := O) Y hY YT.step YT.stepCost).TimeBound (s + 3) 0 0 := by
  refine ⟨fun u e => ?_, fun u o => ?_, fun u o => ?_⟩
  · rcases e with e | e
    · simp [parCtxL.timed, parCtxL.start.tree.timed, parCtxL.start.tree.match_1.timed,
        SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret]
    · have := SPTree.Timed.stepTime_bind_le (YT.step u e)
        (fun q => (0, SPTree.Timed.ret (q.1, (Sum.inr (Sum.inr q.2) : E ⊕ O ⊕ O')))) 0
        (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
      have h2 := hT u e
      simp only [parCtxL.timed, parCtxL.start.tree.timed, parCtxL.start.tree.match_1.timed,
        SPTree.Timed.stepTime, SPTree.Timed.delay] at this h2 ⊢
      omega
  · simp [parCtxL.timed, parCtxL.resume.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]
  · simp [parCtxL.timed, parCtxL.finish.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]

set_option linter.auxLemma false in
/-- **Time of the costed right parallel context**: over a costed form `XT` of `X` whose
activations cost at most `s`, `start` costs at most `s + 3` and `resume`, `finish` cost `0`. -/
theorem parCtxR.timed_timeBound (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (XT : Sys.Timed τ E O) {s : ℕ} (hT : XT.TimeBound s) :
    (parCtxR.timed (E' := E') (O' := O') X hX XT.step XT.stepCost).TimeBound (s + 3) 0 0 := by
  refine ⟨fun t e => ?_, fun t o => ?_, fun t o => ?_⟩
  · rcases e with e | e
    · have := SPTree.Timed.stepTime_bind_le (XT.step t e)
        (fun q => (0, SPTree.Timed.ret (q.1, (Sum.inr (Sum.inl q.2) : E' ⊕ O ⊕ O')))) 0
        (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
      have h2 := hT t e
      simp only [parCtxR.timed, parCtxR.start.tree.timed, parCtxR.start.tree.match_1.timed,
        SPTree.Timed.stepTime, SPTree.Timed.delay] at this h2 ⊢
      omega
    · simp [parCtxR.timed, parCtxR.start.tree.timed, parCtxR.start.tree.match_1.timed,
        SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret]
  · simp [parCtxR.timed, parCtxR.resume.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]
  · simp [parCtxR.timed, parCtxR.finish.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]

/-- The context `parCtxL Y hY` of `Y` beside a left component as a costed pullback, from a
costed form `YT` erasing to `Y` with activations of time at most `s`: the constants are
`s + 9`, `4` and `1`, and the activation count is kept. -/
noncomputable def parCtxL.toCosted (Y : Sys υ E' O') (hY : ∀ u e, SPComp.NoFail (Y.step u e))
    (idle : E) (YT : Sys.Timed υ E' O') (hE : YT.Erases Y) {s : ℕ} (hT : YT.TimeBound s) :
    CostedPullback E O (E ⊕ E') (O ⊕ O') :=
  (parCtxL Y hY).toCostedPullback idle (parCtxL.timed Y hY YT.step YT.stepCost)
    (parCtxL.erase_timed Y hY _ _ fun u e => by subst hE; rfl)
    (parCtxL.timed_timeBound Y hY YT hT)

/-- The context `parCtxR X hX` of `X` beside a right component as a costed pullback, from a
costed form `XT` erasing to `X` with activations of time at most `s`: the constants are
`s + 9`, `4` and `1`, and the activation count is kept. -/
noncomputable def parCtxR.toCosted (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (idle : E') (XT : Sys.Timed τ E O) (hE : XT.Erases X) {s : ℕ} (hT : XT.TimeBound s) :
    CostedPullback E' O' (E ⊕ E') (O ⊕ O') :=
  (parCtxR X hX).toCostedPullback idle (parCtxR.timed X hX XT.step XT.stepCost)
    (parCtxR.erase_timed X hX _ _ fun t e => by subst hE; rfl)
    (parCtxR.timed_timeBound X hX XT hT)

end MultiHybrid

namespace CostedPullback

variable {τ τ' υ υ' E O E₁ O₁ E₂ O₂ : Type}

/-- **Time-graded composition theorem for two holes.** As `EnvPullback.realizes_twoHole`,
against the environments of time `(n, o, q, tD)`: the realization in the first hole is needed
against the environments of the time given by `F`, and the one in the second hole against those
of the time given by `G`. -/
theorem realizesTime_twoHole (F : CostedPullback E₁ O₁ E O) (G : CostedPullback E₂ O₂ E O)
    {X : Sys τ E₁ O₁} {X' : Sys τ' E₁ O₁} {Y : Sys υ E₂ O₂} {Y' : Sys υ' E₂ O₂}
    (hX : F.Adm X) (hX' : F.Adm X') (hY : G.Adm Y) (hY' : G.Adm Y')
    (hmid : ∀ (ζ : Type) (Z : Strat ζ E O), view (F.map X') Z = view (G.map Y) Z)
    {n o q tD : ℕ} {bX : (ζ : Type) → Env (Strat ζ E₁ O₁) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E₂ O₂) ζ → ℝ≥0∞}
    (hXr : RealizesTime X X' (n + F.nextC) (o + F.obsC) (F.roundsMul * q + F.roundsAdd)
      (tD + F.distC) bX)
    (hYr : RealizesTime Y Y' (n + G.nextC) (o + G.obsC) (G.roundsMul * q + G.roundsAdd)
      (tD + G.distC) bY) :
    RealizesTime (F.map X) (G.map Y') n o q tD
      (fun ζ Z => bX (F.Ctx ζ) (F.pull Z) + bY (G.Ctx ζ) (G.pull Z)) := by
  intro ζ Z ZT ZE hT
  have h1 := F.realizesTime_map hX hX' hXr ζ Z ZT ZE hT
  have h2 := G.realizesTime_map hY hY' hYr ζ Z ZT ZE hT
  unfold adv Env.gap at h1 h2 ⊢
  rw [show (view (F.map X') : Strat ζ E O → SPComp ζ) = view (G.map Y) from funext (hmid ζ)]
    at h1
  exact (absDiff_triangle _ _ _).trans (add_le_add h1 h2)

end CostedPullback

section Par

variable {τ τ' υ υ' E O E' O' : Type}

open MultiHybrid

/-- Realization against the environments of a time depends only on the views of the
systems. -/
theorem RealizesTime.of_view_eq {τ₁ τ₂ υ₁ υ₂ E O : Type} {X₁ : Sys τ₁ E O} {X₂ : Sys τ₂ E O}
    {Y₁ : Sys υ₁ E O} {Y₂ : Sys υ₂ E O}
    (hX : ∀ (ζ : Type) (Z : Strat ζ E O), view X₁ Z = view X₂ Z)
    (hY : ∀ (ζ : Type) (Z : Strat ζ E O), view Y₁ Z = view Y₂ Z) {n o q tD : ℕ}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : RealizesTime X₁ Y₁ n o q tD b) :
    RealizesTime X₂ Y₂ n o q tD b := by
  intro ζ Z ZT ZE hT
  have := h ζ Z ZT ZE hT
  unfold adv at this ⊢
  rwa [show (view X₁ : Strat ζ E O → SPComp ζ) = view X₂ from funext (hX ζ),
    show (view Y₁ : Strat ζ E O → SPComp ζ) = view Y₂ from funext (hY ζ)] at this

/-- The parallel composition and the context of `Y` over `X` have the same view. -/
theorem view_par_eq_parCtxL (Y : Sys υ E' O') (hY : ∀ u e, SPComp.NoFail (Y.step u e))
    (X : Sys τ E O) (ζ : Type) (Z : Strat ζ (E ⊕ E') (O ⊕ O')) :
    view (X.par Y) Z = view ((parCtxL Y hY).withSub X) Z :=
  view_eq_of_stepMap _ _ Prod.swap rfl (parCtxL_withSub_step Y hY X) Z

/-- **Parallel composition with time certificates, left component.** If `X` realizes `X'`
with bound `b` against the environments of time `(n + (s + 9), o + 4, q, tD + 1)`, both idle at
`idle`, and `Y` has a costed form with activations of time at most `s`, then `X.par Y` realizes
`X'.par Y` against the environments of time `(n, o, q, tD)`, with bound `b` at the environment
reduced through the context of `Y`. -/
theorem realizes_par_left_timed {X : Sys τ E O} {X' : Sys τ' E O} (Y : Sys υ E' O')
    (hY : ∀ u e, SPComp.NoFail (Y.step u e)) (idle : E) {oX oX' : O}
    (hXi : IdleAt X idle oX) (hX'i : IdleAt X' idle oX') (YT : Sys.Timed υ E' O')
    (hE : YT.Erases Y) {s : ℕ} (hT : YT.TimeBound s) {n o q tD : ℕ}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : RealizesTime X X' (n + (s + 9)) (o + 4) q (tD + 1) b) :
    RealizesTime (X.par Y) (X'.par Y) n o q tD
      (fun ζ Z => b (RState υ ζ E (O ⊕ O')) ((parCtxL Y hY).reduceEnv idle Z)) := by
  have hq : (parCtxL.toCosted (O := O) Y hY idle YT hE hT).roundsMul * q +
      (parCtxL.toCosted (O := O) Y hY idle YT hE hT).roundsAdd = q := by
    simp [parCtxL.toCosted, toCostedPullback, parCtxL]
  have h' := (parCtxL.toCosted Y hY idle YT hE hT).realizesTime_map (X := X) (Y := X')
    ⟨oX, hXi⟩ ⟨oX', hX'i⟩ (n := n) (o := o) (q := q) (tD := tD) (b := b) (by rw [hq]; exact h)
  refine RealizesTime.of_view_eq (fun ζ Z => (view_par_eq_parCtxL Y hY X ζ Z).symm)
    (fun ζ Z => (view_par_eq_parCtxL Y hY X' ζ Z).symm) ?_
  intro ζ Z ZT ZE hZ
  have := h' ζ Z ZT ZE hZ
  simp only [parCtxL.toCosted, toCostedPullback, toEnvPullback_pull] at this
  exact this

/-- **Parallel composition with time certificates, right component.** If `Y` realizes `Y'`
with bound `b` against the environments of time `(n + (s + 9), o + 4, q, tD + 1)`, both idle at
`idle`, and `X` has a costed form with activations of time at most `s`, then `X.par Y` realizes
`X.par Y'` against the environments of time `(n, o, q, tD)`, with bound `b` at the environment
reduced through the context of `X`. -/
theorem realizes_par_right_timed (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    {Y : Sys υ E' O'} {Y' : Sys υ' E' O'} (idle : E') {oY oY' : O'}
    (hYi : IdleAt Y idle oY) (hY'i : IdleAt Y' idle oY') (XT : Sys.Timed τ E O)
    (hE : XT.Erases X) {s : ℕ} (hT : XT.TimeBound s) {n o q tD : ℕ}
    {b : (ζ : Type) → Env (Strat ζ E' O') ζ → ℝ≥0∞}
    (h : RealizesTime Y Y' (n + (s + 9)) (o + 4) q (tD + 1) b) :
    RealizesTime (X.par Y) (X.par Y') n o q tD
      (fun ζ Z => b (RState τ ζ E' (O ⊕ O')) ((parCtxR X hX).reduceEnv idle Z)) := by
  have hq : (parCtxR.toCosted (O' := O') X hX idle XT hE hT).roundsMul * q +
      (parCtxR.toCosted (O' := O') X hX idle XT hE hT).roundsAdd = q := by
    simp [parCtxR.toCosted, toCostedPullback, parCtxR]
  have h' := (parCtxR.toCosted X hX idle XT hE hT).realizesTime_map (X := Y) (Y := Y')
    ⟨oY, hYi⟩ ⟨oY', hY'i⟩ (n := n) (o := o) (q := q) (tD := tD) (b := b) (by rw [hq]; exact h)
  intro ζ Z ZT ZE hZ
  have := h' ζ Z ZT ZE hZ
  simp only [parCtxR.toCosted, toCostedPullback, toEnvPullback_pull] at this
  rw [← parCtxR_withSub X hX Y, ← parCtxR_withSub X hX Y']
  exact this

/-- **Parallel composition of realizations with time certificates.** Let `Y` and `X'` have
costed forms with activations of time at most `sY` and `sX`. If `X` realizes `X'` with bound
`bX` against the environments of time `(n + (sY + 9), o + 4, q, tD + 1)` and `Y` realizes `Y'`
with bound `bY` against the environments of time `(n + (sX + 9), o + 4, q, tD + 1)`, then
`X.par Y` realizes `X'.par Y'` against the environments of time `(n, o, q, tD)`, with the sum of
`bX` at the environment reduced through the context of `Y` and `bY` at the environment reduced
through the context of `X'`. The systems `Y` and `X'` run inside the reduced environments and
are lossless; the left systems are idle at `idleL` and the right ones at `idleR`. -/
theorem realizes_par_timed {X : Sys τ E O} {X' : Sys τ' E O} {Y : Sys υ E' O'}
    {Y' : Sys υ' E' O'} (hY : ∀ u e, SPComp.NoFail (Y.step u e))
    (hX' : ∀ t e, SPComp.NoFail (X'.step t e)) (idleL : E) (idleR : E') {oX oX' : O}
    {oY oY' : O'} (hXi : IdleAt X idleL oX) (hX'i : IdleAt X' idleL oX')
    (hYi : IdleAt Y idleR oY) (hY'i : IdleAt Y' idleR oY')
    (YT : Sys.Timed υ E' O') (XT' : Sys.Timed τ' E O) (hEY : YT.Erases Y)
    (hEX : XT'.Erases X') {sY sX : ℕ} (hTY : YT.TimeBound sY) (hTX : XT'.TimeBound sX)
    {n o q tD : ℕ} {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E' O') ζ → ℝ≥0∞}
    (hXr : RealizesTime X X' (n + (sY + 9)) (o + 4) q (tD + 1) bX)
    (hYr : RealizesTime Y Y' (n + (sX + 9)) (o + 4) q (tD + 1) bY) :
    RealizesTime (X.par Y) (X'.par Y') n o q tD
      (fun ζ Z => bX (RState υ ζ E (O ⊕ O')) ((parCtxL Y hY).reduceEnv idleL Z) +
        bY (RState τ' ζ E' (O ⊕ O')) ((parCtxR X' hX').reduceEnv idleR Z)) := by
  have hqL : (parCtxL.toCosted (O := O) Y hY idleL YT hEY hTY).roundsMul * q +
      (parCtxL.toCosted (O := O) Y hY idleL YT hEY hTY).roundsAdd = q := by
    simp [parCtxL.toCosted, toCostedPullback, parCtxL]
  have hqR : (parCtxR.toCosted (O' := O') X' hX' idleR XT' hEX hTX).roundsMul * q +
      (parCtxR.toCosted (O' := O') X' hX' idleR XT' hEX hTX).roundsAdd = q := by
    simp [parCtxR.toCosted, toCostedPullback, parCtxR]
  have h := (parCtxL.toCosted Y hY idleL YT hEY hTY).realizesTime_twoHole
    (parCtxR.toCosted X' hX' idleR XT' hEX hTX) (X := X) (X' := X') (Y := Y) (Y' := Y')
    ⟨oX, hXi⟩ ⟨oX', hX'i⟩ ⟨oY, hYi⟩ ⟨oY', hY'i⟩
    (fun ζ Z => by
      change view ((parCtxL Y hY).withSub X') Z = view ((parCtxR X' hX').withSub Y) Z
      rw [parCtxR_withSub]
      exact (view_par_eq_parCtxL Y hY X' ζ Z).symm)
    (n := n) (o := o) (q := q) (tD := tD) (bX := bX) (bY := bY)
    (by rw [hqL]; exact hXr) (by rw [hqR]; exact hYr)
  refine RealizesTime.of_view_eq (fun ζ Z => (view_par_eq_parCtxL Y hY X ζ Z).symm)
    (fun _ Z => congrArg (fun S => view S Z) (parCtxR_withSub X' hX' Y')) ?_
  intro ζ Z ZT ZE hZ
  have := h ζ Z ZT ZE hZ
  simp only [parCtxL.toCosted, parCtxR.toCosted, toCostedPullback, toEnvPullback_pull] at this
  exact this

end Par

end CatCrypt.Crypto.UCTransparent

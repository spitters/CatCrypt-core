/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the environment reductions

The costed forms of the joint run `loop`, `run` and of the view `view` of a strategy against a
reactive system, by `derive_reduction`; the costed form of `envReduction` and of the environment
reductions `fixHeap Z.heap fun k => SPComp.bind (view (S k) Z.input) Z.dist` over a family `S` of
systems, as the trees `envReduction.tree` and `sysEnvTree` with `derive_timed`; and their times,
relative to the environment.

An environment makes `q = Z.input.rounds` activations, and its state and the events and outputs
of the interface may grow with them, so its time is graded: `StratRunBound` bounds `next` and
`obs` at round `i` by `tN i` and `tO i` on an invariant indexed by the round, with interface
predicates `Ev` and `Out` on events and outputs, and `SysRunBound` bounds a system step at round
`i` by `tS i` on events of `Ev i`. The time of a reduction is the time of the environment, the sum
of `tN i + tO i` over its activations and the bound of its distinguisher, the sum of the `tS i`,
the reset to the heap of the environment and a constant per activation. A strategy with a state
of unbounded size has no uniform step bound; the graded form states the bound on the states it
reaches.

Search words: time certificate, costed view, environment reduction, activation count, costed
strategy, graded time bound, fixHeap.

The companions `OT/PVWOTSquareTimed` and `OTExtension/IKNPSquareTimed` import this file.

## Main definitions

* `loop.tree`, `run.tree`, `view.tree`: the trees and costed forms of the run and the view.
* `StratRunBound`, `SysRunBound`: graded time bounds of a costed strategy and a costed system.
* `envReduction.tree`, `sysEnvTree`: the trees of the environment reductions.

## Main results

* `loop.tree.time_and_allRet`, `view.tree.timeBound_timed`: the time and final states of a run.
* `envReduction.compile_tree`, `envReduction.tree.erase_timed`,
  `envReduction.tree.timeBound_timed`: the certificate of `envReduction`.
* `sysEnvTree_compile`, `sysEnvTree.erase_timed`, `sysEnvTree.timeBound_timed`: the certificate of
  an environment reduction over a family of systems.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.loop

derive_reduction CatCrypt.Crypto.UCTransparent.run

-- `view` keeps the tree that inlines `run` (calls `loop.tree` directly): the time theorem
-- `view.tree.timeBound_timed` and its users are stated for that form
set_option derive_reduction.certifiedCalls false in
derive_reduction CatCrypt.Crypto.UCTransparent.view

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

variable {τ ζ E O : Type}

/-- The graded time of a costed strategy over the interface predicates `Ev` and `Out`. From a
state of `Inv i`, `next` costs at most `tN i` and returns a state of `Mid i` and an event of
`Ev i`; from a state of `Mid i` on an output of `Out i`, `obs` costs at most `tO i` and returns
states of `Inv (i + 1)`. The round `i` is the number of activations made so far, and the
predicates may bound the sizes of states, events and outputs in terms of it. -/
structure StratRunBound (next : ζ → SPTree.Timed (ζ × E)) (nextCost : ζ → ℕ)
    (obs : ζ → O → SPTree.Timed ζ) (obsCost : ζ → O → ℕ) (Inv Mid : ℕ → ζ → Prop)
    (Ev : ℕ → E → Prop) (Out : ℕ → O → Prop) (tN tO : ℕ → ℕ) : Prop where
  /-- The time of `next` at round `i`. -/
  next_time : ∀ i z, Inv i z → SPTree.Timed.stepTime (nextCost z, next z) ≤ tN i
  /-- The results of `next` at round `i`. -/
  next_ret : ∀ i z, Inv i z → SPTree.Timed.AllRet (fun a => Mid i a.1 ∧ Ev i a.2) (next z)
  /-- The time of `obs` at round `i`. -/
  obs_time : ∀ i z o, Mid i z → Out i o → SPTree.Timed.stepTime (obsCost z o, obs z o) ≤ tO i
  /-- The results of `obs` at round `i`. -/
  obs_ret : ∀ i z o, Mid i z → Out i o → SPTree.Timed.AllRet (Inv (i + 1)) (obs z o)

/-- The graded time of a costed system over the interface predicates `Ev` and `Out`. From a
state of `Inv i` on an event of `Ev i`, a step costs at most `tS i` and returns states of
`Inv (i + 1)` and outputs of `Out i`. -/
structure SysRunBound (step : τ → E → SPTree.Timed (τ × O)) (stepCost : τ → E → ℕ)
    (Inv : ℕ → τ → Prop) (Ev : ℕ → E → Prop) (Out : ℕ → O → Prop) (tS : ℕ → ℕ) : Prop where
  /-- The time of a step at round `i`. -/
  step_time : ∀ i t e, Inv i t → Ev i e → SPTree.Timed.stepTime (stepCost t e, step t e) ≤ tS i
  /-- The results of a step at round `i`. -/
  step_ret : ∀ i t e, Inv i t → Ev i e →
    SPTree.Timed.AllRet (fun p => Inv (i + 1) p.1 ∧ Out i p.2) (step t e)

/-- A costed bind whose tree has time at most `T` and leaves in `Q`, with a continuation of time
at most `K` and leaves in `P` from the leaves in `Q`. -/
theorem stepTime_delay_bind_le_and_allRet {α β : Type} {Q : α → Prop} {P : β → Prop} (C c : ℕ)
    (A : SPTree.Timed α) (f : α → ℕ × SPTree.Timed β) {T K : ℕ}
    (hT : SPTree.Timed.stepTime (c, A) ≤ T) (hQ : SPTree.Timed.AllRet Q A)
    (hf : ∀ a, Q a → SPTree.Timed.stepTime (f a) ≤ K ∧ SPTree.Timed.AllRet P (f a).2) :
    SPTree.Timed.stepTime (SPTree.Timed.delay (C + c) (A.bind f)) ≤ C + T + K ∧
      SPTree.Timed.AllRet P (SPTree.Timed.delay (C + c) (A.bind f)).2 := by
  constructor
  · have := SPTree.Timed.stepTime_bind_le_of_allRet A f K hQ fun a ha => (hf a ha).1
    simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at this hT ⊢
    omega
  · exact SPTree.Timed.allRet_bind_of
      (SPTree.Timed.allRet_mono (fun a ha => (hf a ha).2) A hQ)

/-- **Time of the joint run.** A run of `n` rounds from round `i`, from states of the invariants
of a costed strategy and a costed system over the same interface, costs at most `1` and, per
round `j`, the bounds of `next`, the step, `obs`, the bound `B` of the bad flag and `8`; its
final environment states are those of the invariant at round `i + n`. -/
theorem loop.tree.time_and_allRet (S : Sys τ E O) (Z : Strat ζ E O) {bad : τ → Bool}
    {badCost : τ → ℕ} {next : ζ → SPTree.Timed (ζ × E)} {nextCost : ζ → ℕ}
    {step : τ → E → SPTree.Timed (τ × O)} {stepCost : τ → E → ℕ}
    {obs : ζ → O → SPTree.Timed ζ} {obsCost : ζ → O → ℕ} {InvZ MidZ : ℕ → ζ → Prop}
    {InvS : ℕ → τ → Prop} {Ev : ℕ → E → Prop} {Out : ℕ → O → Prop} {tN tS tO : ℕ → ℕ} {B : ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : SysRunBound step stepCost InvS Ev Out tS)
    (hB : ∀ i t, InvS (i + 1) t → badCost t ≤ B) (n i : ℕ) (c : ζ × τ × Bool)
    (hc₁ : InvZ i c.1) (hc₂ : InvS i c.2.1) :
    SPTree.Timed.stepTime
        (loop.tree.timed S bad badCost Z n c next nextCost step stepCost obs obsCost) ≤
      1 + ∑ j ∈ Finset.range n, (tN (i + j) + tS (i + j) + tO (i + j) + 8 + B) ∧
    SPTree.Timed.AllRet (fun r => InvZ (i + n) r.1)
      (loop.tree.timed S bad badCost Z n c next nextCost step stepCost obs obsCost).2 := by
  induction n generalizing i c with
  | zero =>
    simp [loop.tree.timed.eq_1, SPTree.Timed.delay, SPTree.Timed.stepTime, SPTree.Timed.time_ret,
      SPTree.Timed.AllRet, hc₁]
  | succ n ih =>
    rw [loop.tree.timed.eq_2]
    have hsum : ∑ j ∈ Finset.range (n + 1), (tN (i + j) + tS (i + j) + tO (i + j) + 8 + B) =
        ∑ j ∈ Finset.range n,
            (tN (i + 1 + j) + tS (i + 1 + j) + tO (i + 1 + j) + 8 + B) +
          (tN i + tS i + tO i + 8 + B) := by
      rw [Finset.sum_range_succ']
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        rw [show i + (j + 1) = i + 1 + j by omega]
    set R := 1 + ∑ j ∈ Finset.range n,
      (tN (i + 1 + j) + tS (i + 1 + j) + tO (i + 1 + j) + 8 + B) with hR
    have hfinal : ∀ r : ζ × τ × Bool, InvZ (i + 1 + n) r.1 → InvZ (i + (n + 1)) r.1 := by
      intro r hr
      rwa [show i + (n + 1) = i + 1 + n by omega]
    have h4 : ∀ (z : ζ) (t : τ) (f : Bool), InvZ (i + 1) z → InvS (i + 1) t →
        SPTree.Timed.stepTime (SPTree.Timed.delay (2 + (1 + badCost t + 1))
          (loop.tree.timed S bad badCost Z n (z, t, f || bad t) next nextCost step stepCost obs
            obsCost)) ≤ 4 + B + R ∧
        SPTree.Timed.AllRet (fun r => InvZ (i + (n + 1)) r.1)
          (SPTree.Timed.delay (2 + (1 + badCost t + 1))
            (loop.tree.timed S bad badCost Z n (z, t, f || bad t) next nextCost step stepCost obs
              obsCost)).2 := by
      intro z t f hz ht
      obtain ⟨h1, h2⟩ := ih (i + 1) (z, t, f || bad t) hz ht
      have := hB i t ht
      refine ⟨?_, SPTree.Timed.allRet_mono hfinal _ h2⟩
      rw [SPTree.Timed.stepTime_delay]
      omega
    have h3 : ∀ (a : ζ × E) (p : τ × O), MidZ i a.1 → InvS (i + 1) p.1 → Out i p.2 →
        SPTree.Timed.stepTime (SPTree.Timed.delay (1 + obsCost a.1 p.2)
          ((obs a.1 p.2).bind fun x_3 =>
            SPTree.Timed.delay (2 + (1 + badCost p.1 + 1))
              (loop.tree.timed S bad badCost Z n (x_3, p.1, c.2.2 || bad p.1) next nextCost step
                stepCost obs obsCost))) ≤ 1 + tO i + (4 + B + R) ∧
        SPTree.Timed.AllRet (fun r => InvZ (i + (n + 1)) r.1)
          (SPTree.Timed.delay (1 + obsCost a.1 p.2)
            ((obs a.1 p.2).bind fun x_3 =>
              SPTree.Timed.delay (2 + (1 + badCost p.1 + 1))
                (loop.tree.timed S bad badCost Z n (x_3, p.1, c.2.2 || bad p.1) next nextCost step
                  stepCost obs obsCost))).2 := fun a p ha hp hq =>
      stepTime_delay_bind_le_and_allRet 1 _ _ _ (hZ.obs_time i a.1 p.2 ha hq)
        (hZ.obs_ret i a.1 p.2 ha hq) fun z hz => h4 z p.1 _ hz hp
    have h2 : ∀ a : ζ × E, MidZ i a.1 ∧ Ev i a.2 → _ := fun a ha =>
      stepTime_delay_bind_le_and_allRet 1 _ _ _ (hS.step_time i c.2.1 a.2 hc₂ ha.2)
        (hS.step_ret i c.2.1 a.2 hc₂ ha.2) fun p hp => h3 a p ha.1 hp.1 hp.2
    have h1 := stepTime_delay_bind_le_and_allRet 1 _ _ _ (hZ.next_time i c.1 hc₁)
      (hZ.next_ret i c.1 hc₁) h2
    refine ⟨?_, h1.2⟩
    rw [SPTree.Timed.stepTime_delay, hsum]
    have h := h1.1
    omega

/-- **Time of the view.** A view of a costed strategy against a costed system, from initial
states of their invariants, costs at most the time of the strategy over its `Z.rounds`
activations, the time of `Z.rounds` system steps, `8` per activation and `2`; its results are the
environment states of the invariant at round `Z.rounds`. -/
theorem view.tree.timeBound_timed (S : Sys τ E O) (Z : Strat ζ E O)
    {next : ζ → SPTree.Timed (ζ × E)} {nextCost : ζ → ℕ}
    {step : τ → E → SPTree.Timed (τ × O)} {stepCost : τ → E → ℕ}
    {obs : ζ → O → SPTree.Timed ζ} {obsCost : ζ → O → ℕ} {InvZ MidZ : ℕ → ζ → Prop}
    {InvS : ℕ → τ → Prop} {Ev : ℕ → E → Prop} {Out : ℕ → O → Prop} {tN tS tO : ℕ → ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : SysRunBound step stepCost InvS Ev Out tS)
    (hz : InvZ 0 Z.init) (ht : InvS 0 S.init) :
    SPTree.Timed.stepTime (view.tree.timed S Z next nextCost step stepCost obs obsCost) ≤
      (∑ i ∈ Finset.range Z.rounds, (tN i + tO i)) + (∑ i ∈ Finset.range Z.rounds, tS i) +
        8 * Z.rounds + 2 ∧
    SPTree.Timed.AllRet (InvZ Z.rounds)
      (view.tree.timed S Z next nextCost step stepCost obs obsCost).2 := by
  obtain ⟨h1, h2⟩ := loop.tree.time_and_allRet S Z (bad := fun _ => false) (badCost := fun _ => 0)
    (B := 0) hZ hS (fun _ _ _ => le_rfl) Z.rounds 0 (Z.init, S.init, false) hz ht
  have h := stepTime_delay_bind_le_and_allRet (K := 0) (P := InvZ Z.rounds)
    (Q := fun r : ζ × τ × Bool => InvZ (0 + Z.rounds) r.1) 1 _ _
    (fun x => (0, SPTree.Timed.ret x.1)) h1 h2 fun r hr =>
      ⟨by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret],
        by simpa [SPTree.Timed.AllRet] using hr⟩
  refine ⟨h.1.trans ?_, h.2⟩
  simp only [Nat.zero_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  omega

end CatCrypt.Crypto.UCTransparent

namespace CatCrypt.Crypto.UCConcrete

open CatCrypt.Core

/-- The computation tree of `envReduction`: the reset to the heap of `Z`, the adversary and the
distinguisher on the adversary channel. -/
noncomputable def envReduction.tree {hon leak V : Type} (Z : Env hon (Unit ⊕ V))
    (A : leak → SPTree V) (dist : Unit ⊕ V → SPTree Bool) (o : leak) : SPTree Bool :=
  .load Z.heap ((A o).bind fun v => dist (.inr v))

/-- The tree of `envReduction` compiles to `envReduction`. -/
theorem envReduction.compile_tree {hon leak V : Type} (Z : Env hon (Unit ⊕ V))
    (A : leak → SPComp V) (A' : leak → SPTree V) (dist : Unit ⊕ V → SPTree Bool)
    (hA : ∀ o, (A' o).compile = A o) (hd : ∀ x, (dist x).compile = Z.dist x) (o : leak) :
    (envReduction.tree Z A' dist o).compile = envReduction A Z o := by
  simp only [envReduction.tree, envReduction, SPTree.compile_load, SPTree.compile_bind, hA, hd]
  rfl

derive_timed envReduction.tree

/-- **Time of the environment reduction.** On the challenge `o`, for an adversary of time at most
`TA` at `o` whose results lie in `Q` and a distinguisher of time at most `TD` on the adversary
channel at the values of `Q`, the reduction costs at most the reset to the heap of `Z`, `TA`, `TD`
and `3`. -/
theorem envReduction.tree.timeBound_timed {hon leak V : Type} (Z : Env hon (Unit ⊕ V))
    (A : leak → SPTree.Timed V) (ACost : leak → ℕ) (dist : Unit ⊕ V → SPTree.Timed Bool)
    (distCost : Unit ⊕ V → ℕ) (o : leak) {Q : V → Prop} {TA TD : ℕ}
    (hA : SPTree.Timed.stepTime (ACost o, A o) ≤ TA) (hQ : SPTree.Timed.AllRet Q (A o))
    (hd : ∀ v, Q v → SPTree.Timed.stepTime (distCost (.inr v), dist (.inr v)) ≤ TD) :
    SPTree.Timed.stepTime (envReduction.tree.timed Z A ACost dist distCost o) ≤
      Z.heap.data.keys.card + TA + TD + 3 := by
  have h := SPTree.Timed.stepTime_bind_le_of_allRet (A o)
    (fun v => (1 + distCost (.inr v), dist (.inr v))) (TD + 1) hQ fun v hv => by
      have := hd v hv
      simp only [SPTree.Timed.stepTime] at this ⊢
      omega
  simp only [envReduction.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.time_load] at h hA ⊢
  omega

end CatCrypt.Crypto.UCConcrete

derive_timed_structure CatCrypt.Crypto.UCTransparent.KeyedSys

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Crypto.UCConcrete

variable {K τ ζ E O : Type}

/-- The computation tree of an environment reduction over a family `S` of systems: on the key
`k`, the reset to the heap of `Z`, the view of its strategy against `S k`, and its
distinguisher. -/
noncomputable def sysEnvTree (S : K → Sys τ E O) (Z : Env (Strat ζ E O) ζ)
    (next : ζ → SPTree (ζ × E)) (step : K → τ → E → SPTree (τ × O)) (obs : ζ → O → SPTree ζ)
    (dist : ζ → SPTree Bool) (k : K) : SPTree Bool :=
  .load Z.heap ((view.tree (S k) Z.input next (step k) obs).bind dist)

/-- The tree of an environment reduction compiles to the reduction. -/
theorem sysEnvTree_compile (S : K → Sys τ E O) (Z : Env (Strat ζ E O) ζ)
    {next : ζ → SPTree (ζ × E)} {step : K → τ → E → SPTree (τ × O)} {obs : ζ → O → SPTree ζ}
    {dist : ζ → SPTree Bool} (hn : ∀ z, (next z).compile = Z.input.next z)
    (hs : ∀ k t e, (step k t e).compile = (S k).step t e)
    (ho : ∀ z o, (obs z o).compile = Z.input.obs z o) (hd : ∀ z, (dist z).compile = Z.dist z)
    (k : K) :
    (sysEnvTree S Z next step obs dist k).compile =
      fixHeap Z.heap (fun k => SPComp.bind (view (S k) Z.input) Z.dist) k := by
  simp only [sysEnvTree, SPTree.compile_load, SPTree.compile_bind, hd,
    view.compile_tree (S k) Z.input next (step k) obs hn (hs k) ho]
  rfl

derive_timed sysEnvTree

/-- **Time of an environment reduction over a family of systems.** On the key `k`, for a costed
strategy and a costed step of `S k` over the same interface, from initial states of their
invariants and with a distinguisher of time at most `tD` on the final states, the reduction costs
at most the reset to the heap of `Z`, the time of the strategy over its `q = Z.input.rounds`
activations, `tD`, the time of `q` system steps, `9` per activation, the cost of `S k` and `6`. -/
theorem sysEnvTree.timeBound_timed (S : K → Sys τ E O) (SCost : K → ℕ) (Z : Env (Strat ζ E O) ζ)
    {next : ζ → SPTree.Timed (ζ × E)} {nextCost : ζ → ℕ}
    {step : K → τ → E → SPTree.Timed (τ × O)} {stepCost : K → τ → E → ℕ}
    {obs : ζ → O → SPTree.Timed ζ} {obsCost : ζ → O → ℕ}
    {dist : ζ → SPTree.Timed Bool} {distCost : ζ → ℕ} (k : K) {InvZ MidZ : ℕ → ζ → Prop}
    {InvS : ℕ → τ → Prop} {Ev : ℕ → E → Prop} {Out : ℕ → O → Prop} {tN tS tO : ℕ → ℕ} {tD : ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : SysRunBound (step k) (stepCost k) InvS Ev Out tS)
    (hz : InvZ 0 Z.input.init) (ht : InvS 0 (S k).init)
    (hd : ∀ z, InvZ Z.input.rounds z → SPTree.Timed.stepTime (distCost z, dist z) ≤ tD) :
    SPTree.Timed.stepTime
        (sysEnvTree.timed S SCost Z next nextCost step stepCost obs obsCost dist distCost k) ≤
      Z.heap.data.keys.card + (∑ i ∈ Finset.range Z.input.rounds, (tN i + tO i)) + tD +
        (∑ i ∈ Finset.range Z.input.rounds, tS i) + 9 * Z.input.rounds + SCost k + 6 := by
  have hS' : SysRunBound (fun a b => step k a b) (fun a b => 1 + stepCost k a b) InvS Ev Out
      (fun i => 1 + tS i) := by
    refine ⟨fun i t e h1 h2 => ?_, hS.step_ret⟩
    have := hS.step_time i t e h1 h2
    simp only [SPTree.Timed.stepTime] at this ⊢
    omega
  obtain ⟨hV, hA⟩ := view.tree.timeBound_timed (S k) Z.input hZ hS' hz ht
  have hB := SPTree.Timed.stepTime_bind_le_of_allRet _
    (fun a => (1 + distCost a, dist a)) (1 + tD) hA fun z hz' => by
      have := hd z hz'
      simp only [SPTree.Timed.stepTime] at this ⊢
      omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    Nat.mul_one] at hV
  simp only [sysEnvTree.timed, SPTree.Timed.stepTime, SPTree.Timed.time_load] at hV hB ⊢
  simp only [Finset.sum_add_distrib]
  omega

end CatCrypt.Crypto.UCTransparent



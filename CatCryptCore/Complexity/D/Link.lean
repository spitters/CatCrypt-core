/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.TimeAdm
public import CatCryptCore.Core.SPTreeTimedOps
import all CatCryptCore.Core.SPTreeTimed

/-!
# Costed trees and D evaluation trees

The evaluation trees of D (`CTree`) and the costed trees of `derive_timed`
(`ℕ × SPTree.Timed α`, a step cost in front of a tree with step costs on its continuations)
both count one unit per effect node and charge evaluation steps between nodes: D as `tick`
nodes, a costed tree as step costs on its edges. This module relates the two measures in both
directions.

## From D to costed trees

`CTree.toTimed OT t` turns the ticks in front of a node into the step cost of the edge leading
to it, and the `sample`, `get` and `set` nodes into the nodes of `SPTree.Timed` at `f.den` and
`f.loc n`. A `query` node is answered by a costed realization `OT : CostedOracle O` of the
oracle `O`: a step-prefixed costed tree per query whose erasure compiles to the oracle's answer
and whose time is at most `OT.time`. Its time is at most `(1 + OT.time) * t.cost`
(`CTree.stepTime_toTimed_le`) and its erasure compiles to `t.run O`
(`CTree.compile_erase_toTimed`). The oracle `CTree.Oracle.zero` answers every query by the
default value without effects; `CostedOracle.zero` realizes it at time zero.

A realizer `r : TimeRealizer O n f` gives the costed adversary `r.toTimed OT`: at an input `x`,
the evaluation of the term and the β-step of the call as the step cost in front, then the
costed form of the call. Its time is at most `n` when `OT.time = 0`
(`TimeRealizer.stepTime_toTimed_le_of_time_zero`), and it compiles to `f x`.

## From costed trees to D

`TimedSim R K n x t` relates a costed tree `x` to a D tree `t`: the effect nodes agree in order
(a sample over `γ` matched with a sample over `f.den` through `e : γ ≃ f.den`, `get` and `set`
at `f.loc i` matched at location `i` of type `f`, `fail` with `fail`), the leaves are related
by `R`, and on every
path the steps of `t` (ticks and nodes) are at most `n` plus `K` times the charges of `x` along
the path (its step costs and nodes). The index `n` is an additive allowance. It gives
`t.cost ≤ n + K * stepTime x` (`TimedSim.cost_le`) and, for the graph of an encoding,
`t.run O` as the encoded compilation of `x` (`TimedSim.run`).

The relation is closed under the costed combinators. A bind of D charges a β-step at each
junction (`t.bind fun v => .tick (g v)`) that the costed bind does not; `TimedSim.bind` takes
the continuation related to the ticked D continuation, so the junction step is paid either by
the allowance or, with `K ≥ 1`, by a step cost of the continuation (`TimedSim.delay_tick`).

## Main definitions

* `CostedOracle`, `CTree.Oracle.zero`, `CostedOracle.zero`
* `CTree.toTimed`, `TimeRealizer.toTimed`
* `TimedSimTree`, `TimedSim`

## Main results

* `CTree.stepTime_toTimed_le`, `CTree.compile_erase_toTimed`
* `TimeRealizer.stepTime_toTimed_le`, `TimeRealizer.stepTime_toTimed_le_of_time_zero`,
  `TimeRealizer.compile_erase_toTimed`
* `TimedSim.cost_le`, `TimedSim.run`
* `TimedSim.bind`, `TimedSim.map`, `TimedSim.delay`, `TimedSim.delay_tick`, `TimedSim.ite`,
  `TimedSim.cond`, `TimedSim.mono`
* node rules `TimedSim.ret`, `TimedSim.sample`, `TimedSim.get`, `TimedSim.set`, `TimedSim.fail`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core

/-! ## Costed oracles -/

/-- A costed realization of the oracle `O`: for each query a step-prefixed costed tree whose
erasure compiles to the oracle's answer and whose time is at most `time`. -/
structure CostedOracle (O : CTree.Oracle) : Type 1 where
  /-- The costed tree answering a query. -/
  tree : (d r : FTy) → d.den → ℕ × SPTree.Timed r.den
  /-- A bound on the time of an answer. -/
  time : ℕ
  time_le : ∀ d r x, SPTree.Timed.stepTime (tree d r x) ≤ time
  compile_eq : ∀ d r x, (tree d r x).2.erase.compile = O d r x

/-- The oracle that answers every query by the default value without effects. -/
noncomputable def CTree.Oracle.zero : CTree.Oracle := fun _ _ _ => SPComp.pure default

/-- The realization of `CTree.Oracle.zero` at time zero. -/
noncomputable def CostedOracle.zero : CostedOracle CTree.Oracle.zero where
  tree _ _ _ := (0, .ret default)
  time := 0
  time_le _ _ _ := by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  compile_eq _ _ _ := by rw [SPTree.Timed.erase_ret]; rfl

/-! ## From D trees to costed trees -/

namespace CTree

variable {α : Type} {O : Oracle}

/-- The costed tree of a D tree: the ticks in front of a node are the step cost of the edge
leading to it, and a `query` node is the costed answer of `OT` followed by the continuation. -/
noncomputable def toTimed (OT : CostedOracle O) : CTree α → ℕ × SPTree.Timed α
  | ret a => (0, .ret a)
  | tick t => SPTree.Timed.delay 1 (toTimed OT t)
  | sample f k => (0, .sample f.den (FTy.instFintype f) (FTy.instNonempty f)
      (fun x => (toTimed OT (k x)).1) fun x => (toTimed OT (k x)).2)
  | get n f k => (0, .get (f.loc n) (fun x => (toTimed OT (k x)).1)
      fun x => (toTimed OT (k x)).2)
  | set n f v k => (0, .set (f.loc n) v (toTimed OT k).1 (toTimed OT k).2)
  | query d r x k => SPTree.Timed.delay (OT.tree d r x).1
      ((OT.tree d r x).2.bind fun y => toTimed OT (k y))
  | fail => (0, .fail)

/-- The time of the costed tree is at most `1 + OT.time` times the cost of the D tree. -/
theorem stepTime_toTimed_le (OT : CostedOracle O) (t : CTree α) :
    SPTree.Timed.stepTime (t.toTimed OT) ≤ (1 + OT.time) * t.cost := by
  induction t with
  | ret a => exact Nat.zero_le _
  | tick t ih =>
    rw [toTimed, SPTree.Timed.stepTime_delay, cost_tick, Nat.mul_add]
    omega
  | sample f k ih =>
    have hs : (Finset.univ.sup fun x : f.den =>
          (toTimed OT (k x)).1 + (toTimed OT (k x)).2.time) ≤
        (1 + OT.time) * Finset.univ.sup fun x : f.den => (k x).cost :=
      Finset.sup_le fun x _ => (ih x).trans (Nat.mul_le_mul_left _
        (Finset.le_sup (f := fun x => (k x).cost) (Finset.mem_univ x)))
    change 0 + (1 + Finset.univ.sup fun x : f.den =>
        (toTimed OT (k x)).1 + (toTimed OT (k x)).2.time) ≤
      (1 + OT.time) * (1 + Finset.univ.sup fun x : f.den => (k x).cost)
    rw [Nat.mul_add]
    omega
  | get n f k ih =>
    have hs : (Finset.univ.sup fun x : (f.loc n).ty =>
          (toTimed OT (k x)).1 + (toTimed OT (k x)).2.time) ≤
        (1 + OT.time) * Finset.univ.sup fun x : f.den => (k x).cost :=
      Finset.sup_le fun x _ => (ih x).trans (Nat.mul_le_mul_left _
        (Finset.le_sup (f := fun x : f.den => (k x).cost) (Finset.mem_univ x)))
    change 0 + (1 + Finset.univ.sup fun x : (f.loc n).ty =>
        (toTimed OT (k x)).1 + (toTimed OT (k x)).2.time) ≤
      (1 + OT.time) * (1 + Finset.univ.sup fun x : f.den => (k x).cost)
    rw [Nat.mul_add]
    omega
  | set n f v k ih =>
    change (toTimed OT k).1 + (toTimed OT k).2.time ≤ (1 + OT.time) * k.cost at ih
    change 0 + (1 + ((toTimed OT k).1 + (toTimed OT k).2.time)) ≤
      (1 + OT.time) * (1 + k.cost)
    rw [Nat.mul_add]
    omega
  | query d r x k ih =>
    have hb := SPTree.Timed.stepTime_bind_le (OT.tree d r x).2 (fun y => (k y).toTimed OT)
      ((1 + OT.time) * Finset.univ.sup fun y => (k y).cost) fun y => (ih y).trans
        (Nat.mul_le_mul_left _ (Finset.le_sup (f := fun y => (k y).cost) (Finset.mem_univ y)))
    have ho := OT.time_le d r x
    simp only [SPTree.Timed.stepTime] at ho
    rw [toTimed, SPTree.Timed.stepTime_delay, cost, Nat.mul_add]
    omega
  | fail => exact Nat.zero_le _

/-- The erasure of the costed tree compiles to the denotation of the D tree. -/
theorem compile_erase_toTimed (OT : CostedOracle O) (t : CTree α) :
    (t.toTimed OT).2.erase.compile = t.run O := by
  induction t with
  | ret a => rfl
  | tick t ih => exact ih
  | sample f k ih => exact congrArg (SPComp.bind (SPComp.sample f.den)) (funext ih)
  | get n f k ih => exact congrArg (SPComp.bind (SPComp.get (f.loc n))) (funext ih)
  | set n f v k ih =>
    exact congrArg (SPComp.bind (SPComp.set (f.loc n) v)) (funext fun _ => ih)
  | query d r x k ih =>
    simp only [toTimed, SPTree.Timed.delay, run]
    rw [SPTree.Timed.erase_bind, SPTree.compile_bind, OT.compile_eq]
    exact congrArg _ (funext ih)
  | fail => rfl

end CTree

/-! ## Costed adversaries from realizers -/

namespace TimeRealizer

variable {O : CTree.Oracle} {a b : Ty} {n : ℕ} {f : Val a → SPComp (Val b)}

/-- The costed adversary of a realizer: at the input `x`, the evaluation of the term and the
β-step of the call in front of the costed form of the call. -/
noncomputable def toTimed (r : TimeRealizer O n f) (OT : CostedOracle O) (x : Val a) :
    ℕ × SPTree.Timed (Val b) :=
  SPTree.Timed.delay (r.evalCost + 1) ((r.closure x).toTimed OT)

theorem stepTime_toTimed_le (r : TimeRealizer O n f) (OT : CostedOracle O) (x : Val a) :
    SPTree.Timed.stepTime (r.toTimed OT x) ≤ r.evalCost + 1 + (1 + OT.time) * r.callCost := by
  rw [toTimed, SPTree.Timed.stepTime_delay]
  have h1 := CTree.stepTime_toTimed_le OT (r.closure x)
  have h2 := Nat.mul_le_mul_left (1 + OT.time) (r.call_le x)
  omega

/-- With an oracle realization of time zero, the costed adversary has time at most `n`. -/
theorem stepTime_toTimed_le_of_time_zero (r : TimeRealizer O n f) (OT : CostedOracle O)
    (hOT : OT.time = 0) (x : Val a) : SPTree.Timed.stepTime (r.toTimed OT x) ≤ n := by
  have h1 := r.stepTime_toTimed_le OT x
  have h2 := r.time_le
  rw [hOT, Nat.add_zero, Nat.one_mul] at h1
  omega

theorem compile_erase_toTimed (r : TimeRealizer O n f) (OT : CostedOracle O) (x : Val a) :
    (r.toTimed OT x).2.erase.compile = f x :=
  (CTree.compile_erase_toTimed OT (r.closure x)).trans (r.run_eq x)

end TimeRealizer

/-! ## The simulation relation -/

/-- `TimedSimTree R K n A t`: the effect nodes of the D tree `t` are those of the costed tree
`A` in the same order, the leaves are related by `R`, and on every path the steps of `t` are at
most `n` plus `K` times the nodes and step costs of `A` along the path. -/
inductive TimedSimTree {α β : Type} (R : α → β → Prop) (K : ℕ) :
    ℕ → SPTree.Timed α → CTree β → Prop where
  /-- Related leaves. -/
  | ret {n : ℕ} {a : α} {v : β} : R a v → TimedSimTree R K n (.ret a) (.ret v)
  /-- A step of the D tree spends one unit of the allowance. -/
  | tick {n m : ℕ} {A : SPTree.Timed α} {t : CTree β} :
      TimedSimTree R K m A t → m + 1 ≤ n → TimedSimTree R K n A (.tick t)
  /-- Samples matched through an equivalence. -/
  | sample {n : ℕ} {γ : Type} {finγ : Fintype γ} {neγ : Nonempty γ} {c : γ → ℕ}
      {k : γ → SPTree.Timed α} (f : FTy) (e : γ ≃ f.den) {k' : f.den → CTree β}
      (m : γ → ℕ) : (∀ b, TimedSimTree R K (m b) (k b) (k' (e b))) →
      (∀ b, 1 + m b ≤ n + K + K * c b) →
      TimedSimTree R K n (.sample γ finγ neγ c k) (.sample f k')
  /-- Reads of the same location. -/
  | get {n : ℕ} (i : ℕ) (f : FTy) {c : f.den → ℕ} {k : f.den → SPTree.Timed α}
      {k' : f.den → CTree β} (m : f.den → ℕ) : (∀ x, TimedSimTree R K (m x) (k x) (k' x)) →
      (∀ x, 1 + m x ≤ n + K + K * c x) →
      TimedSimTree R K n (.get (f.loc i) c k) (.get i f k')
  /-- Writes of the same value to the same location. -/
  | set {n : ℕ} (i : ℕ) (f : FTy) (v : f.den) {c : ℕ} {A : SPTree.Timed α} {t : CTree β}
      (m : ℕ) : TimedSimTree R K m A t → 1 + m ≤ n + K + K * c →
      TimedSimTree R K n (.set (f.loc i) v c A) (.set i f v t)
  /-- Failure in both trees. -/
  | fail {n : ℕ} : TimedSimTree R K n .fail .fail

/-- `TimedSim R K n x t`: the relation `TimedSimTree` between the tree of the step-prefixed
costed tree `x` and the D tree `t`, with the step cost in front of `x` charged at `K`. -/
def TimedSim {α β : Type} (R : α → β → Prop) (K n : ℕ) (x : ℕ × SPTree.Timed α)
    (t : CTree β) : Prop :=
  TimedSimTree R K (n + K * x.1) x.2 t

namespace TimedSimTree

variable {α β γ δ : Type} {R : α → β → Prop} {K : ℕ}

theorem mono {n n' : ℕ} {A : SPTree.Timed α} {t : CTree β} (h : TimedSimTree R K n A t)
    (hn : n ≤ n') : TimedSimTree R K n' A t := by
  cases h with
  | ret hR => exact .ret hR
  | tick h hm => exact .tick h (by omega)
  | sample f e m h hm => exact .sample f e m h fun b => (hm b).trans (by omega)
  | get i f m h hm => exact .get i f m h fun x => (hm x).trans (by omega)
  | set i f v m h hm => exact .set i f v m h (hm.trans (by omega))
  | fail => exact .fail

theorem cost_le {n : ℕ} {A : SPTree.Timed α} {t : CTree β} (h : TimedSimTree R K n A t) :
    t.cost ≤ n + K * A.time := by
  induction h with
  | ret => exact Nat.zero_le _
  | tick _ hm ih => simp only [CTree.cost_tick]; omega
  | @sample n γ finγ neγ c k f e k' mb _ hmb ih =>
    let _ := finγ
    have hle : ∀ b, c b + (k b).time ≤ Finset.univ.sup fun b => c b + (k b).time :=
      fun b => Finset.le_sup (f := fun b => c b + (k b).time) (Finset.mem_univ b)
    change 1 + (Finset.univ.sup fun x : f.den => (k' x).cost) ≤
      n + K * (1 + Finset.univ.sup fun b => c b + (k b).time)
    generalize (Finset.univ.sup fun b => c b + (k b).time) = S at hle ⊢
    have key : ∀ x, 1 + (k' x).cost ≤ n + K * (1 + S) := by
      intro x
      obtain ⟨b, rfl⟩ := e.surjective x
      have h1 := ih b
      have h2 := hmb b
      have h3 := Nat.mul_le_mul_left K (hle b)
      rw [Nat.mul_add] at h3 ⊢
      omega
    have hs : (Finset.univ.sup fun x => (k' x).cost) ≤ n + K * (1 + S) - 1 :=
      Finset.sup_le fun x _ => by have := key x; omega
    have := key default
    omega
  | @get n i f c k k' mb _ hmb ih =>
    have hle : ∀ x : f.den, c x + (k x).time ≤
        Finset.univ.sup fun x : (f.loc i).ty => c x + (k x).time :=
      fun x => Finset.le_sup (f := fun x : (f.loc i).ty => c x + (k x).time)
        (Finset.mem_univ x)
    change 1 + (Finset.univ.sup fun x : f.den => (k' x).cost) ≤
      n + K * (1 + Finset.univ.sup fun x : (f.loc i).ty => c x + (k x).time)
    generalize (Finset.univ.sup fun x : (f.loc i).ty => c x + (k x).time) = S at hle ⊢
    have key : ∀ x, 1 + (k' x).cost ≤ n + K * (1 + S) := by
      intro x
      have h1 := ih x
      have h2 := hmb x
      have h3 := Nat.mul_le_mul_left K (hle x)
      rw [Nat.mul_add] at h3 ⊢
      omega
    have hs : (Finset.univ.sup fun x => (k' x).cost) ≤ n + K * (1 + S) - 1 :=
      Finset.sup_le fun x _ => by have := key x; omega
    have := key default
    omega
  | @set n i f v c A t mb _ hmb ih =>
    change 1 + t.cost ≤ n + K * (1 + (c + A.time))
    rw [Nat.mul_add, Nat.mul_add]
    omega
  | fail => exact Nat.zero_le _

theorem run {enc : α → β} {n : ℕ} {A : SPTree.Timed α} {t : CTree β}
    (h : TimedSimTree (fun a v => v = enc a) K n A t) (O : CTree.Oracle) :
    t.run O = SPComp.bind A.erase.compile fun a => SPComp.pure (enc a) := by
  induction h with
  | ret hR =>
    subst hR
    rw [SPTree.Timed.erase_ret, SPTree.compile, SPComp.pure_bind]
    rfl
  | tick _ _ ih => exact ih
  | @sample n γ finγ neγ c k f e k' mb _ _ ih =>
    let _ := finγ
    let _ := neγ
    refine Eq.trans ?_ (SPComp.bind_assoc (SPComp.sample γ)
      (fun b => (k b).erase.compile) _).symm
    show SPComp.bind (SPComp.sample f.den) (fun x => (k' x).run O) = _
    rw [← SPComp.sample_bind_equiv e]
    exact congrArg _ (funext ih)
  | @get n i f c k k' mb _ _ ih =>
    exact (congrArg _ (funext ih)).trans (SPComp.bind_assoc (SPComp.get (f.loc i))
      (fun x => (k x).erase.compile) _).symm
  | @set n i f v c A t mb _ _ ih =>
    exact (congrArg _ (funext fun _ => ih)).trans (SPComp.bind_assoc
      (SPComp.set (f.loc i) v) (fun _ => A.erase.compile) _).symm
  | fail =>
    rw [SPTree.Timed.erase_fail]
    exact (SPComp.fail_bind _).symm

theorem bind {S : γ → δ → Prop} {f : α → ℕ × SPTree.Timed γ} {g : β → CTree δ} {m : ℕ}
    (hf : ∀ a v, R a v → TimedSimTree S K (m + K * (f a).1) (f a).2 (.tick (g v)))
    {n : ℕ} {A : SPTree.Timed α} {t : CTree β} (h : TimedSimTree R K n A t) :
    TimedSimTree S K (n + m + K * (A.bind f).1) (A.bind f).2
      (t.bind fun v => .tick (g v)) := by
  induction h with
  | ret hR => exact (hf _ _ hR).mono (by simp only [SPTree.Timed.bind]; omega)
  | tick _ hm ih => exact .tick ih (by omega)
  | sample f' e mb _ hmb ih =>
    refine .sample f' e (fun b => mb b + m + K * (SPTree.Timed.bind _ f).1) ih fun b => ?_
    have := hmb b
    rw [Nat.mul_add]
    omega
  | get i f' mb _ hmb ih =>
    refine .get i f' (fun x => mb x + m + K * (SPTree.Timed.bind _ f).1) ih fun x => ?_
    have := hmb x
    rw [Nat.mul_add]
    omega
  | set i f' v mb _ hmb ih =>
    refine .set i f' v (mb + m + K * (SPTree.Timed.bind _ f).1) ih ?_
    rw [Nat.mul_add]
    omega
  | fail => exact .fail

end TimedSimTree

namespace TimedSim

variable {α β γ δ : Type} {R : α → β → Prop} {K n : ℕ}

theorem mono {n' : ℕ} {x : ℕ × SPTree.Timed α} {t : CTree β} (h : TimedSim R K n x t)
    (hn : n ≤ n') : TimedSim R K n' x t :=
  TimedSimTree.mono h (by omega)

/-- The cost of the D tree is at most the allowance plus `K` times the time of the costed
tree. -/
theorem cost_le {x : ℕ × SPTree.Timed α} {t : CTree β} (h : TimedSim R K n x t) :
    t.cost ≤ n + K * SPTree.Timed.stepTime x := by
  have := TimedSimTree.cost_le h
  simp only [SPTree.Timed.stepTime, Nat.mul_add]
  omega

/-- Related through the graph of `enc`, the D tree means the encoded compilation of the
costed tree. -/
theorem run {enc : α → β} {x : ℕ × SPTree.Timed α} {t : CTree β}
    (h : TimedSim (fun a v => v = enc a) K n x t) (O : CTree.Oracle) :
    t.run O = SPComp.bind x.2.erase.compile fun a => SPComp.pure (enc a) :=
  TimedSimTree.run h O

/-- A costed bind and a D bind with a β-step at each junction: the continuations are related
with the ticked D continuation, at the allowance `m`. -/
theorem bind {S : γ → δ → Prop} {f : α → ℕ × SPTree.Timed γ} {g : β → CTree δ} {m : ℕ}
    {x : ℕ × SPTree.Timed α} {t : CTree β} (hx : TimedSim R K n x t)
    (hf : ∀ a v, R a v → TimedSim S K m (f a) (.tick (g v))) :
    TimedSim S K (n + m) (SPTree.Timed.delay x.1 (x.2.bind f))
      (t.bind fun v => .tick (g v)) := by
  refine (TimedSimTree.bind (m := m) hf hx).mono ?_
  simp only [SPTree.Timed.delay, Nat.mul_add]
  omega

/-- A step cost in front of the costed tree. -/
theorem delay (c : ℕ) {x : ℕ × SPTree.Timed α} {t : CTree β} (h : TimedSim R K n x t) :
    TimedSim R K n (SPTree.Timed.delay c x) t := by
  refine TimedSimTree.mono h ?_
  simp only [SPTree.Timed.delay, Nat.mul_add]
  omega

/-- A unit step cost in front of the costed tree pays for a tick in front of the D tree. -/
theorem delay_tick (hK : 1 ≤ K) {x : ℕ × SPTree.Timed α} {t : CTree β}
    (h : TimedSim R K n x t) : TimedSim R K n (SPTree.Timed.delay 1 x) (.tick t) := by
  refine TimedSimTree.tick h ?_
  simp only [SPTree.Timed.delay, Nat.mul_add]
  omega

/-- A costed map and a D bind returning the image after a β-step: the function at a leaf costs
`fc a` in the costed tree. -/
theorem map {S : γ → δ → Prop} {f : α → γ} {fc : α → ℕ} {g : β → δ} {m : ℕ}
    {x : ℕ × SPTree.Timed α} {t : CTree β} (hx : TimedSim R K n x t)
    (hS : ∀ a v, R a v → S (f a) (g v)) (hm : ∀ a, 1 ≤ m + K * fc a) :
    TimedSim S K (n + m) (SPTree.Timed.delay x.1 (x.2.map f fc))
      (t.bind fun v => .tick (.ret (g v))) :=
  hx.bind fun a v hR => TimedSimTree.tick (m := 0) (.ret (hS a v hR)) (by have := hm a; omega)

/-- A conditional on a proposition in both trees. -/
theorem ite (p : Prop) [Decidable p] {x y : ℕ × SPTree.Timed α} {t u : CTree β}
    (hx : TimedSim R K n x t) (hy : TimedSim R K n y u) :
    TimedSim R K n (if p then x else y) (if p then t else u) := by
  split
  · exact hx
  · exact hy

/-- A conditional on a boolean in both trees, as the D evaluator branches. -/
theorem cond (b : Bool) {x y : ℕ × SPTree.Timed α} {t u : CTree β}
    (hx : TimedSim R K n x t) (hy : TimedSim R K n y u) :
    TimedSim R K n (bif b then x else y) (bif b then t else u) := by
  cases b
  · exact hy
  · exact hx

/-- Related leaves, after any step cost. -/
theorem ret {c : ℕ} {a : α} {v : β} (h : R a v) : TimedSim R K n (c, .ret a) (.ret v) :=
  TimedSimTree.ret h

/-- A sample node, with `K ≥ 1` paying for the node. -/
theorem sample (hK : 1 ≤ K) {γ' : Type} {finγ : Fintype γ'} {neγ : Nonempty γ'}
    {c : γ' → ℕ} {k : γ' → SPTree.Timed α} (f : FTy) (e : γ' ≃ f.den)
    {k' : f.den → CTree β} (h : ∀ b, TimedSim R K n (c b, k b) (k' (e b))) :
    TimedSim R K n (0, .sample γ' finγ neγ c k) (.sample f k') :=
  TimedSimTree.sample f e (fun b => n + K * c b) h fun _ => by
    simp only [Nat.mul_zero]; omega

/-- A get node, with `K ≥ 1` paying for the node. -/
theorem get (hK : 1 ≤ K) (i : ℕ) (f : FTy) {c : f.den → ℕ} {k : f.den → SPTree.Timed α}
    {k' : f.den → CTree β} (h : ∀ x, TimedSim R K n (c x, k x) (k' x)) :
    TimedSim R K n (0, .get (f.loc i) c k) (.get i f k') :=
  TimedSimTree.get i f (fun x => n + K * c x) h fun _ => by
    simp only [Nat.mul_zero]; omega

/-- A set node, with `K ≥ 1` paying for the node. -/
theorem set (hK : 1 ≤ K) (i : ℕ) (f : FTy) (v : f.den) {c : ℕ} {A : SPTree.Timed α}
    {t : CTree β} (h : TimedSim R K n (c, A) t) :
    TimedSim R K n (0, .set (f.loc i) v c A) (.set i f v t) :=
  TimedSimTree.set i f v (n + K * c) h (by simp only [Nat.mul_zero]; omega)

/-- Failure in both trees, after any step cost. -/
theorem fail {c : ℕ} : TimedSim R K n (c, (.fail : SPTree.Timed α)) (.fail : CTree β) :=
  TimedSimTree.fail

end TimedSim

end CatCrypt.Complexity.D

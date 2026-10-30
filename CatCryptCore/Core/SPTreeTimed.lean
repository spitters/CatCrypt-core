/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCryptCore.Core.SPTree
public meta import CatCryptCore.Unary.ExpectedCost

public meta section

set_option autoImplicit false

/-!
# Syntactic computation trees with step costs

`SPTree.Timed α` is the computation tree of `SPTree α` in which every continuation
carries a step cost: a node `sample β _ _ c k` or `get l c k` continues from `x` with
`k x` at step cost `c x`, and `set l v c t` continues with `t` at step cost `c`; the step
cost is the cost of computing the next node. Erasing the step costs gives the underlying
tree (`SPTree.Timed.erase`). The worst-case time `SPTree.Timed.time` counts the nodes
and the step costs on the costliest path.

`compileTimed` compiles a tree to a cost-instrumented computation, charging one unit per
operation and each step cost where it occurs. Its erasure is the compilation of the
erased tree, and its expected cost is at most the worst-case time. With zero step costs
(`SPTree.Timed.ofTree`) the time is `SPTree.queryCost`, so the bound specialises to the
bound `ecost_compileCharged_le_queryCost` of `compileCharged`.

## Cost model

The registered primitive costs are one unit per `sample`, `get` and `set` node, one unit
plus one per location of `h₀` for a heap reset `load h₀` (the `SPTree.queryCost`
convention), none for `ret` and `fail`, and each step cost as written in the instrumented
program.

## Main definitions

* `SPTree.Timed α` — computation tree with a step cost on every continuation
* `SPTree.Timed.erase`, `SPTree.Timed.time`, `SPTree.Timed.ofTree`
* `SPTree.Timed.TimeBound` — every run, at every outcome in the support of each sampled
  distribution, takes at most the given number of units
* `SPTree.Timed.TimeBdd` — every `sampleDist` node has a bounded family of continuation times
* `compileTimed` — compilation with unit charges per operation and the step costs

## Main results

* `compileTimed_erase` — erasing the charges gives `SPTree.compile` of the erased tree
* `ecost_compileTimed_le_of_timeBound` — expected cost at most any time bound
* `SPTree.Timed.timeBound_of_time_le` — under `TimeBdd`, the worst-case time is a time bound
* `ecost_compileTimed_le_time` — expected cost at most the worst-case time
* `SPTree.Timed.erase_ofTree`, `SPTree.Timed.time_ofTree`, `ecost_compileTimed_ofTree_le` —
  zero step costs give back `SPTree` and the bound by `SPTree.queryCost`
-/

namespace CatCrypt.Core

open CatCrypt.Prob CatCrypt.Unary
open scoped ENNReal

/-- Syntactic computation tree with a step cost on every continuation: the step cost is
the cost of computing the next node. -/
inductive SPTree.Timed (α : Type) : Type 1 where
  /-- Return the value. -/
  | ret : α → SPTree.Timed α
  /-- Sample uniformly from `β` and continue, at step cost `c`, with `k`. -/
  | sample (β : Type) (finβ : Fintype β) (neβ : Nonempty β) (c : β → ℕ)
      (k : β → SPTree.Timed α) : SPTree.Timed α
  /-- Sample from the sub-distribution `μ` and continue, at step cost `c`, with `k`. -/
  | sampleDist (β : Type) (μ : SDistr β) (c : β → ℕ) (k : β → SPTree.Timed α) :
      SPTree.Timed α
  /-- Read location `l` and continue, at step cost `c`, with `k`. -/
  | get (l : Location) (c : l.ty → ℕ) (k : l.ty → SPTree.Timed α) : SPTree.Timed α
  /-- Write `v` to location `l` and continue, at step cost `c`, with `t`. -/
  | set (l : Location) (v : l.ty) (c : ℕ) (t : SPTree.Timed α) : SPTree.Timed α
  /-- Failure. -/
  | fail : SPTree.Timed α
  /-- Replace the heap by `h₀` and continue, at step cost `c`, with `t`. -/
  | load (h₀ : Heap) (c : ℕ) (t : SPTree.Timed α) : SPTree.Timed α

namespace SPTree.Timed

variable {α : Type}

/-- The tree with its step costs erased. -/
def erase : SPTree.Timed α → SPTree α
  | ret a => .ret a
  | sample β finβ neβ _ k => .sample β finβ neβ fun b => erase (k b)
  | sampleDist β μ _ k => .sampleDist β μ fun b => erase (k b)
  | get l _ k => .get l fun v => erase (k v)
  | set l v _ t => .set l v (erase t)
  | fail => .fail
  | load h₀ _ t => .load h₀ (erase t)

/-- Worst-case time: one unit per operation plus the step costs, maximised over the
branches. A node `sampleDist β μ c k` takes the supremum `⨆ b, c b + time (k b)` in `ℕ`,
which is the maximum when that family is bounded (`TimeBdd`) and `0` otherwise. -/
noncomputable def time : SPTree.Timed α → ℕ
  | ret _ => 0
  | sample _ finβ _ c k =>
    letI := finβ
    1 + Finset.univ.sup fun b => c b + time (k b)
  | sampleDist _ _ c k => 1 + ⨆ b, c b + time (k b)
  | get _ c k => 1 + Finset.univ.sup fun v => c v + time (k v)
  | set _ _ c t => 1 + (c + time t)
  | fail => 0
  | load h₀ c t => 1 + h₀.data.keys.card + (c + time t)

/-- The tree `s` with zero step costs. -/
def ofTree : SPTree α → SPTree.Timed α
  | .ret a => ret a
  | .sample β finβ neβ k => sample β finβ neβ (fun _ => 0) fun b => ofTree (k b)
  | .sampleDist β μ k => sampleDist β μ (fun _ => 0) fun b => ofTree (k b)
  | .get l k => get l (fun _ => 0) fun v => ofTree (k v)
  | .set l v t => set l v 0 (ofTree t)
  | .fail => fail
  | .load h₀ t => load h₀ 0 (ofTree t)

/-- Erasing the zero step costs of `ofTree s` gives back `s`. -/
theorem erase_ofTree (s : SPTree α) : (ofTree s).erase = s := by
  induction s with
  | ret a => rfl
  | sample β finβ neβ k ih => simp only [ofTree, erase, ih]
  | sampleDist β μ k ih => simp only [ofTree, erase, ih]
  | get l k ih => simp only [ofTree, erase, ih]
  | set l v t ih => simp only [ofTree, erase, ih]
  | fail => rfl
  | load h₀ t ih => simp only [ofTree, erase, ih]

/-- With zero step costs the worst-case time is the query cost. -/
theorem time_ofTree (s : SPTree α) : (ofTree s).time = s.queryCost := by
  induction s with
  | ret a => rfl
  | sample β finβ neβ k ih => simp only [ofTree, time, SPTree.queryCost, Nat.zero_add, ih]
  | sampleDist β μ k ih => simp only [ofTree, time, SPTree.queryCost, Nat.zero_add, ih]
  | get l k ih => simp only [ofTree, time, SPTree.queryCost, Nat.zero_add, ih]
  | set l v t ih => simp only [ofTree, time, SPTree.queryCost, Nat.zero_add, ih]
  | fail => rfl
  | load h₀ t ih => simp only [ofTree, time, SPTree.queryCost, Nat.zero_add, ih]

/-- Every node `sampleDist β μ c k` of the tree has a bounded family of continuation times
`c b + time (k b)`, so that `time` is the worst-case time. Trees without `sampleDist` nodes
satisfy it. -/
def TimeBdd : SPTree.Timed α → Prop
  | ret _ => True
  | sample _ _ _ _ k => ∀ b, TimeBdd (k b)
  | sampleDist _ _ c k => BddAbove (Set.range fun b => c b + time (k b)) ∧ ∀ b, TimeBdd (k b)
  | get _ _ k => ∀ v, TimeBdd (k v)
  | set _ _ _ t => TimeBdd t
  | fail => True
  | load _ _ t => TimeBdd t

/-- **Time bound.** `TimeBound s t` states that every run of `s` takes at most `t` units:
each node fits its own charge and step cost within `t` and continues within the rest, and
a node `sampleDist β μ c k` does so for every outcome `b` in the support of `μ`. -/
def TimeBound : SPTree.Timed α → ℕ → Prop
  | ret _, _ => True
  | sample _ _ _ c k, t => 1 ≤ t ∧ ∀ b, 1 + c b ≤ t ∧ TimeBound (k b) (t - (1 + c b))
  | sampleDist _ μ c k, t =>
    1 ≤ t ∧ ∀ b ∈ μ.support, 1 + c b ≤ t ∧ TimeBound (k b) (t - (1 + c b))
  | get _ c k, t => 1 ≤ t ∧ ∀ v, 1 + c v ≤ t ∧ TimeBound (k v) (t - (1 + c v))
  | set _ _ c s, t => 1 + c ≤ t ∧ TimeBound s (t - (1 + c))
  | fail, _ => True
  | load h₀ c s, t =>
    1 + h₀.data.keys.card + c ≤ t ∧ TimeBound s (t - (1 + h₀.data.keys.card + c))

/-- On a tree with bounded families of continuation times, the worst-case time is a time
bound. -/
theorem timeBound_of_time_le (s : SPTree.Timed α) (hs : s.TimeBdd) {t : ℕ}
    (h : s.time ≤ t) : s.TimeBound t := by
  induction s generalizing t with
  | ret a => trivial
  | sample β finβ neβ c k ih =>
    simp only [time] at h
    refine ⟨by omega, fun b => ?_⟩
    have hb := Finset.le_sup (f := fun b => c b + (k b).time) (Finset.mem_univ b)
    exact ⟨by omega, ih b (hs b) (by omega)⟩
  | sampleDist β μ c k ih =>
    obtain ⟨hbd, hk⟩ := hs
    simp only [time] at h
    refine ⟨by omega, fun b _ => ?_⟩
    have hb := le_ciSup hbd b
    exact ⟨by omega, ih b (hk b) (by omega)⟩
  | get l c k ih =>
    simp only [time] at h
    refine ⟨by omega, fun v => ?_⟩
    have hv := Finset.le_sup (f := fun v => c v + (k v).time) (Finset.mem_univ v)
    exact ⟨by omega, ih v (hs v) (by omega)⟩
  | set l v c t' ih =>
    simp only [time] at h
    exact ⟨by omega, ih hs (by omega)⟩
  | fail => trivial
  | load h₀ c t' ih =>
    simp only [time] at h
    exact ⟨by omega, ih hs (by omega)⟩

/-- `ofTree s` has bounded families of continuation times when `s` has bounded branching. -/
theorem timeBdd_ofTree (s : SPTree α) (hs : s.QueryBdd) : (ofTree s).TimeBdd := by
  induction s with
  | ret a => trivial
  | sample β finβ neβ k ih => exact fun b => ih b (hs b)
  | sampleDist β μ k ih =>
    simp only [ofTree, TimeBdd, time_ofTree, Nat.zero_add]
    exact ⟨hs.1, fun b => ih b (hs.2 b)⟩
  | get l k ih => exact fun v => ih v (hs v)
  | set l v t ih => exact ih hs
  | fail => trivial
  | load h₀ t ih => exact ih hs

end SPTree.Timed

end CatCrypt.Core

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {α β : Type}

/-- Compile a timed tree to a cost-instrumented computation: one unit per operation, and
the step cost of each continuation charged before the next node. -/
noncomputable def compileTimed : SPTree.Timed α → CostComp α
  | .ret a => CostComp.pure a
  | .sample β finβ neβ c k =>
      letI := finβ; letI := neβ
      CostComp.bind (CostComp.lift (SPComp.sample β) 1) fun b =>
        CostComp.bind (CostComp.lift (SPComp.pure ()) (c b)) fun _ => compileTimed (k b)
  | .sampleDist _ μ c k =>
      CostComp.bind (CostComp.lift (liftSDistr μ) 1) fun b =>
        CostComp.bind (CostComp.lift (SPComp.pure ()) (c b)) fun _ => compileTimed (k b)
  | .get l c k => CostComp.bind (CostComp.lift (SPComp.get l) 1) fun v =>
      CostComp.bind (CostComp.lift (SPComp.pure ()) (c v)) fun _ => compileTimed (k v)
  | .set l v c t => CostComp.bind (CostComp.lift (SPComp.set l v) 1) fun _ =>
      CostComp.bind (CostComp.lift (SPComp.pure ()) c) fun _ => compileTimed t
  | .fail => CostComp.fail
  | .load h₀ c t => CostComp.bind (CostComp.loadC h₀) fun _ =>
      CostComp.bind (CostComp.lift (SPComp.pure ()) c) fun _ => compileTimed t

/-- Erasing a step charge leaves the erased continuation. -/
theorem erase_bind_step (n : ℕ) (f : Unit → CostComp β) :
    (CostComp.bind (CostComp.lift (SPComp.pure ()) n) f).erase = (f ()).erase := by
  rw [erase_bind_lift, SPComp.pure_bind]

/-- Erasing the charges gives the compilation of the erased tree. -/
theorem compileTimed_erase (s : SPTree.Timed α) : (compileTimed s).erase = s.erase.compile := by
  induction s with
  | ret a => simp only [compileTimed, erase_pure, SPTree.Timed.erase, SPTree.compile]
  | sample β finβ neβ c k ih =>
    simp only [compileTimed, erase_bind_lift, SPComp.pure_bind, ih, SPTree.Timed.erase,
      SPTree.compile]
  | sampleDist β μ c k ih =>
    simp only [compileTimed, erase_bind_lift, SPComp.pure_bind, ih, SPTree.Timed.erase,
      SPTree.compile]
  | get l c k ih =>
    simp only [compileTimed, erase_bind_lift, SPComp.pure_bind, ih, SPTree.Timed.erase,
      SPTree.compile]
  | set l v c t ih =>
    simp only [compileTimed, erase_bind_lift, SPComp.pure_bind, ih, SPTree.Timed.erase,
      SPTree.compile]
  | fail => simp only [compileTimed, erase_fail, SPTree.Timed.erase, SPTree.compile]
  | load h₀ c t ih =>
    simp only [compileTimed, SPTree.Timed.erase, erase_bind_loadC, erase_bind_lift,
      SPComp.pure_bind, ih, SPTree.compile_load_eq_bind]

/-- A step charge `n` followed by a continuation of expected cost at most `C` has expected
cost at most `n + C`. -/
theorem ecost_bind_step_le {n : ℕ} {f : Unit → CostComp β} {C : ℝ≥0∞}
    (hf : ∀ h, ecost (f ()) h ≤ C) (h : Heap) :
    ecost (CostComp.bind (CostComp.lift (SPComp.pure ()) n) f) h ≤ n + C :=
  ecost_bind_le_add (fun h' => ecost_lift_le _ n h') (fun _ h' => hf h') h

/-- A step charge `n` after a prefix `m`, followed by a continuation of expected cost at
most `t - (m + n)`, has expected cost at most `t - m` when `m + n ≤ t`. -/
theorem ecost_bind_step_le_sub {m n t : ℕ} {f : Unit → CostComp β} (hn : m + n ≤ t)
    (hf : ∀ h, ecost (f ()) h ≤ ((t - (m + n) : ℕ) : ℝ≥0∞)) (h : Heap) :
    ecost (CostComp.bind (CostComp.lift (SPComp.pure ()) n) f) h ≤ ((t - m : ℕ) : ℝ≥0∞) := by
  refine (ecost_bind_step_le hf h).trans ?_
  rw [← Nat.cast_add]
  exact Nat.cast_le.mpr (by omega)

/-- `m + (t - m) ≤ t` in `ℝ≥0∞` when `m ≤ t`. -/
theorem natCast_add_sub_le {m t : ℕ} (h : m ≤ t) :
    (m : ℝ≥0∞) + ((t - m : ℕ) : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
  rw [← Nat.cast_add]
  exact Nat.cast_le.mpr (by omega)

/-- **Expected cost at most a time bound**: if every run of `s` takes at most `t` units
(`SPTree.Timed.TimeBound s t`), the compiled computation has expected cost at most `t`. -/
theorem ecost_compileTimed_le_of_timeBound (s : SPTree.Timed α) {t : ℕ}
    (ht : s.TimeBound t) (h : Heap) : ecost (compileTimed s) h ≤ (t : ℝ≥0∞) := by
  induction s generalizing t h with
  | ret a => simp [compileTimed]
  | sample β finβ neβ c k ih =>
    rw [compileTimed]
    exact le_trans (ecost_bind_le_add (C₁ := ((1 : ℕ) : ℝ≥0∞)) (C₂ := ((t - 1 : ℕ) : ℝ≥0∞))
      (fun h' => ecost_lift_le _ 1 h')
      (fun b h' => ecost_bind_step_le_sub (ht.2 b).1 (fun h'' => ih b (ht.2 b).2 h'') h') h)
      (natCast_add_sub_le ht.1)
  | sampleDist β μ c k ih =>
    rw [compileTimed]
    exact le_trans (ecost_bind_liftSDistr_le (C := ((t - 1 : ℕ) : ℝ≥0∞))
      (fun b hb h' =>
        ecost_bind_step_le_sub (ht.2 b hb).1 (fun h'' => ih b (ht.2 b hb).2 h'') h') h)
      (natCast_add_sub_le ht.1)
  | get l c k ih =>
    rw [compileTimed]
    exact le_trans (ecost_bind_le_add (C₁ := ((1 : ℕ) : ℝ≥0∞)) (C₂ := ((t - 1 : ℕ) : ℝ≥0∞))
      (fun h' => ecost_lift_le _ 1 h')
      (fun v h' => ecost_bind_step_le_sub (ht.2 v).1 (fun h'' => ih v (ht.2 v).2 h'') h') h)
      (natCast_add_sub_le ht.1)
  | set l v c s ih =>
    rw [compileTimed]
    exact le_trans (ecost_bind_le_add (C₁ := ((1 : ℕ) : ℝ≥0∞)) (C₂ := ((t - 1 : ℕ) : ℝ≥0∞))
      (fun h' => ecost_lift_le _ 1 h')
      (fun _ h' => ecost_bind_step_le_sub ht.1 (fun h'' => ih ht.2 h'') h') h)
      (natCast_add_sub_le (by have := ht.1; omega))
  | fail => simp [compileTimed]
  | load h₀ c s ih =>
    rw [compileTimed]
    exact le_trans (ecost_bind_le_add (C₁ := ((1 + h₀.data.keys.card : ℕ) : ℝ≥0∞))
      (C₂ := ((t - (1 + h₀.data.keys.card) : ℕ) : ℝ≥0∞))
      (fun h' => ecost_loadC_le h₀ h')
      (fun _ h' => ecost_bind_step_le_sub ht.1 (fun h'' => ih ht.2 h'') h') h)
      (natCast_add_sub_le (by have := ht.1; omega))

/-- **Expected cost at most worst-case time** (generalising
`ecost_compileCharged_le_queryCost` to step costs), on trees with bounded families of
continuation times. -/
theorem ecost_compileTimed_le_time (s : SPTree.Timed α) (hs : s.TimeBdd) (h : Heap) :
    ecost (compileTimed s) h ≤ (s.time : ℝ≥0∞) :=
  ecost_compileTimed_le_of_timeBound s (SPTree.Timed.timeBound_of_time_le s hs le_rfl) h

/-- With zero step costs, the expected cost is at most the worst-case operation count. -/
theorem ecost_compileTimed_ofTree_le (s : SPTree α) (hs : s.QueryBdd) (h : Heap) :
    ecost (compileTimed (SPTree.Timed.ofTree s)) h ≤ (s.queryCost : ℝ≥0∞) := by
  simpa only [SPTree.Timed.time_ofTree] using
    ecost_compileTimed_le_time (SPTree.Timed.ofTree s) (SPTree.Timed.timeBdd_ofTree s hs) h

end CatCrypt.Unary

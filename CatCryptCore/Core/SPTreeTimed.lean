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

The registered primitive costs are one unit per `sample`, `get` and `set` node (the
`SPTree.queryCost` convention), none for `ret` and `fail`, and each step cost as written
in the instrumented program.

## Main definitions

* `SPTree.Timed α` — computation tree with a step cost on every continuation
* `SPTree.Timed.erase`, `SPTree.Timed.time`, `SPTree.Timed.ofTree`
* `compileTimed` — compilation with unit charges per operation and the step costs

## Main results

* `compileTimed_erase` — erasing the charges gives `SPTree.compile` of the erased tree
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
  /-- Read location `l` and continue, at step cost `c`, with `k`. -/
  | get (l : Location) (c : l.ty → ℕ) (k : l.ty → SPTree.Timed α) : SPTree.Timed α
  /-- Write `v` to location `l` and continue, at step cost `c`, with `t`. -/
  | set (l : Location) (v : l.ty) (c : ℕ) (t : SPTree.Timed α) : SPTree.Timed α
  /-- Failure. -/
  | fail : SPTree.Timed α

namespace SPTree.Timed

variable {α : Type}

/-- The tree with its step costs erased. -/
def erase : SPTree.Timed α → SPTree α
  | ret a => .ret a
  | sample β finβ neβ _ k => .sample β finβ neβ fun b => erase (k b)
  | get l _ k => .get l fun v => erase (k v)
  | set l v _ t => .set l v (erase t)
  | fail => .fail

/-- Worst-case time: one unit per operation plus the step costs, maximised over the
branches. -/
def time : SPTree.Timed α → ℕ
  | ret _ => 0
  | sample _ finβ _ c k =>
    letI := finβ
    1 + Finset.univ.sup fun b => c b + time (k b)
  | get _ c k => 1 + Finset.univ.sup fun v => c v + time (k v)
  | set _ _ c t => 1 + (c + time t)
  | fail => 0

/-- The tree `s` with zero step costs. -/
def ofTree : SPTree α → SPTree.Timed α
  | .ret a => ret a
  | .sample β finβ neβ k => sample β finβ neβ (fun _ => 0) fun b => ofTree (k b)
  | .get l k => get l (fun _ => 0) fun v => ofTree (k v)
  | .set l v t => set l v 0 (ofTree t)
  | .fail => fail

theorem erase_ofTree (s : SPTree α) : (ofTree s).erase = s := by
  induction s with
  | ret a => rfl
  | sample β finβ neβ k ih => simp only [ofTree, erase, ih]
  | get l k ih => simp only [ofTree, erase, ih]
  | set l v t ih => simp only [ofTree, erase, ih]
  | fail => rfl

theorem time_ofTree (s : SPTree α) : (ofTree s).time = s.queryCost := by
  induction s with
  | ret a => rfl
  | sample β finβ neβ k ih => simp only [ofTree, time, SPTree.queryCost, Nat.zero_add, ih]
  | get l k ih => simp only [ofTree, time, SPTree.queryCost, Nat.zero_add, ih]
  | set l v t ih => simp only [ofTree, time, SPTree.queryCost, Nat.zero_add, ih]
  | fail => rfl

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
  | .get l c k => CostComp.bind (CostComp.lift (SPComp.get l) 1) fun v =>
      CostComp.bind (CostComp.lift (SPComp.pure ()) (c v)) fun _ => compileTimed (k v)
  | .set l v c t => CostComp.bind (CostComp.lift (SPComp.set l v) 1) fun _ =>
      CostComp.bind (CostComp.lift (SPComp.pure ()) c) fun _ => compileTimed t
  | .fail => CostComp.fail

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
  | get l c k ih =>
    simp only [compileTimed, erase_bind_lift, SPComp.pure_bind, ih, SPTree.Timed.erase,
      SPTree.compile]
  | set l v c t ih =>
    simp only [compileTimed, erase_bind_lift, SPComp.pure_bind, ih, SPTree.Timed.erase,
      SPTree.compile]
  | fail => simp only [compileTimed, erase_fail, SPTree.Timed.erase, SPTree.compile]

/-- A step charge `n` followed by a continuation of expected cost at most `C` has expected
cost at most `n + C`. -/
theorem ecost_bind_step_le {n : ℕ} {f : Unit → CostComp β} {C : ℝ≥0∞}
    (hf : ∀ h, ecost (f ()) h ≤ C) (h : Heap) :
    ecost (CostComp.bind (CostComp.lift (SPComp.pure ()) n) f) h ≤ n + C :=
  ecost_bind_le_add (fun h' => ecost_lift_le _ n h') (fun _ h' => hf h') h

/-- **Expected cost at most worst-case time** (generalising
`ecost_compileCharged_le_queryCost` to step costs). -/
theorem ecost_compileTimed_le_time (s : SPTree.Timed α) (h : Heap) :
    ecost (compileTimed s) h ≤ (s.time : ℝ≥0∞) := by
  induction s generalizing h with
  | ret a => simp [compileTimed]
  | sample β finβ neβ c k ih =>
    rw [compileTimed]
    refine le_trans (ecost_bind_le_add (C₁ := 1)
      (C₂ := ((Finset.univ.sup fun b => c b + (k b).time : ℕ) : ℝ≥0∞))
      (fun h' => by exact_mod_cast ecost_lift_le _ 1 h') (fun b h' => ?_) h) ?_
    · refine (ecost_bind_step_le (fun h'' => ih b h'') h').trans ?_
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr
        (Finset.le_sup (f := fun b => c b + (k b).time) (Finset.mem_univ b))
    · simp only [SPTree.Timed.time]
      push_cast
      exact le_rfl
  | get l c k ih =>
    rw [compileTimed]
    refine le_trans (ecost_bind_le_add (C₁ := 1)
      (C₂ := ((Finset.univ.sup fun v => c v + (k v).time : ℕ) : ℝ≥0∞))
      (fun h' => by exact_mod_cast ecost_lift_le _ 1 h') (fun v h' => ?_) h) ?_
    · refine (ecost_bind_step_le (fun h'' => ih v h'') h').trans ?_
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr
        (Finset.le_sup (f := fun v => c v + (k v).time) (Finset.mem_univ v))
    · simp only [SPTree.Timed.time]
      push_cast
      exact le_rfl
  | set l v c t ih =>
    rw [compileTimed]
    refine le_trans (ecost_bind_le_add (C₁ := 1) (C₂ := (c : ℝ≥0∞) + (t.time : ℝ≥0∞))
      (fun h' => by exact_mod_cast ecost_lift_le _ 1 h')
      (fun _ h' => ecost_bind_step_le (fun h'' => ih h'') h') h) ?_
    simp only [SPTree.Timed.time]
    push_cast
    exact le_rfl
  | fail => simp [compileTimed]

/-- With zero step costs, the expected cost is at most the worst-case operation count. -/
theorem ecost_compileTimed_ofTree_le (s : SPTree α) (h : Heap) :
    ecost (compileTimed (SPTree.Timed.ofTree s)) h ≤ (s.queryCost : ℝ≥0∞) := by
  simpa only [SPTree.Timed.time_ofTree] using
    ecost_compileTimed_le_time (SPTree.Timed.ofTree s) h

end CatCrypt.Unary

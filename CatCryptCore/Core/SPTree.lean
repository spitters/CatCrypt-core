/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Tactics.LeOfSum

/-!
# SPTree: Syntactic Computation Trees for SPComp

This file defines `SPTree α`, a syntactic (free-monad-like) representation of
stateful probabilistic computations. Unlike `SPComp α = Heap → SDistr (α × Heap)`
(which is denotational), `SPTree` preserves syntactic structure, enabling cost
analysis by structural recursion.

## Main definitions

* `SPTree` — syntactic computation tree (ret, sample, get, set, fail)
* `SPTree.compile` — denotational semantics (→ SPComp)
* `SPTree.queryCost` — worst-case operation count (structural recursion)
* `SPTree.bind` — monadic composition (substitution at leaves)

## Main results

* `compile_bind` — compilation commutes with bind
* `queryCost_bind` — cost of bind ≤ cost of tree + bound on continuation
-/

namespace CatCrypt.Core

open CatCrypt.Prob

/-! ## SPTree Definition -/

/-- Syntactic computation tree for stateful probabilistic programs.

    Lives in `Type 1` because `sample` quantifies over `β : Type`. -/
inductive SPTree : Type → Type 1 where
  | ret {α : Type} : α → SPTree α
  | sample {α : Type} (β : Type) (finβ : Fintype β) (neβ : Nonempty β) :
      (β → SPTree α) → SPTree α
  | get {α : Type} : (l : Location) → (l.ty → SPTree α) → SPTree α
  | set {α : Type} : (l : Location) → l.ty → SPTree α → SPTree α
  | fail {α : Type} : SPTree α

namespace SPTree

variable {α β γ : Type}

/-! ## Compilation to SPComp -/

/-- Compile a syntax tree to its denotational semantics. -/
noncomputable def compile : SPTree α → SPComp α
  | .ret a => SPComp.pure a
  | .sample β finβ neβ k => letI := finβ; letI := neβ;
    SPComp.bind (SPComp.sample β) (fun b => (k b).compile)
  | .get l k => SPComp.bind (SPComp.get l) (fun v => (k v).compile)
  | .set l v t => SPComp.bind (SPComp.set l v) (fun _ => t.compile)
  | .fail => SPComp.fail

/-! ## Query Cost -/

/-- Worst-case operation count: counts sample + get + set operations.
    Uses `Finset.univ.sup` for branching to take the maximum cost
    across all possible continuations. Structurally recursive. -/
def queryCost : SPTree α → ℕ
  | .ret _ => 0
  | .sample β finβ _ k =>
    letI := finβ
    1 + Finset.univ.sup (fun b => (k b).queryCost)
  | .get _l k => 1 + Finset.univ.sup (fun v => (k v).queryCost)
  | .set _ _ t => 1 + t.queryCost
  | .fail => 0

/-! ## Monadic Bind (Substitution at Leaves) -/

/-- Monadic bind: substitute `f` at every `ret` leaf of `s`. -/
def bind : SPTree α → (α → SPTree β) → SPTree β
  | .ret a, f => f a
  | .sample γ finγ neγ k, f => .sample γ finγ neγ (fun c => (k c).bind f)
  | .get l k, f => .get l (fun v => (k v).bind f)
  | .set l v t, f => .set l v (t.bind f)
  | .fail, _ => .fail

/-! ## Simp Lemmas -/

@[simp] theorem compile_ret (a : α) :
    (SPTree.ret a : SPTree α).compile = SPComp.pure a := rfl

@[simp] theorem compile_fail :
    (SPTree.fail : SPTree α).compile = SPComp.fail := rfl

@[simp] theorem queryCost_ret (a : α) :
    (SPTree.ret a : SPTree α).queryCost = 0 := rfl

@[simp] theorem queryCost_fail :
    (SPTree.fail : SPTree α).queryCost = 0 := rfl

@[simp] theorem bind_ret_val (a : α) (f : α → SPTree β) :
    (SPTree.ret a).bind f = f a := rfl

@[simp] theorem bind_fail (f : α → SPTree β) :
    (SPTree.fail : SPTree α).bind f = .fail := rfl

/-! ## Compile-Bind Correctness -/

/-- Compilation commutes with monadic bind. -/
theorem compile_bind (s : SPTree α) (f : α → SPTree β) :
    (s.bind f).compile = SPComp.bind s.compile (fun a => (f a).compile) := by
  induction s with
  | ret a => exact (SPComp.pure_bind a (fun a => (f a).compile)).symm
  | sample γ finγ neγ k ih =>
    simp only [bind, compile]; rw [SPComp.bind_assoc]; congr_funext
  | get l k ih =>
    simp only [bind, compile]; rw [SPComp.bind_assoc]; congr_funext
  | set l v t ih =>
    simp only [bind, compile]; rw [SPComp.bind_assoc]; congr_funext
  | fail =>
    simp only [bind, compile]
    exact (SPComp.fail_bind (fun a => (f a).compile)).symm

/-! ## Query Cost Bound for Bind -/

/-- Cost of bind ≤ cost of tree + uniform bound on continuation. -/
theorem queryCost_bind (s : SPTree α) (f : α → SPTree β) (bound : ℕ)
    (hf : ∀ a, (f a).queryCost ≤ bound) :
    (s.bind f).queryCost ≤ s.queryCost + bound := by
  induction s with
  | ret a => simp only [bind, queryCost, Nat.zero_add]; exact hf a
  | sample γ finγ neγ k ih =>
    simp only [bind, queryCost]
    have : Finset.univ.sup (fun c => ((k c).bind f).queryCost) ≤
        Finset.univ.sup (fun c => (k c).queryCost) + bound := by
      apply Finset.sup_le; intro c _
      calc ((k c).bind f).queryCost
          ≤ (k c).queryCost + bound := ih c
        _ ≤ Finset.univ.sup (fun c => (k c).queryCost) + bound := by
          gcongr; exact Finset.le_sup (f := fun c => (k c).queryCost) (Finset.mem_univ c)
    omega
  | get l k ih =>
    simp only [bind, queryCost]
    have : Finset.univ.sup (fun v => ((k v).bind f).queryCost) ≤
        Finset.univ.sup (fun v => (k v).queryCost) + bound := by
      apply Finset.sup_le; intro v _
      calc ((k v).bind f).queryCost
          ≤ (k v).queryCost + bound := ih v
        _ ≤ Finset.univ.sup (fun v => (k v).queryCost) + bound := by
          gcongr; exact Finset.le_sup (f := fun v => (k v).queryCost) (Finset.mem_univ v)
    omega
  | set l v t ih =>
    simp only [bind, queryCost]
    have := ih
    omega
  | fail => simp [bind, queryCost]

/-! ## Monad Laws -/

theorem ret_bind (a : α) (f : α → SPTree β) :
    (SPTree.ret a).bind f = f a := rfl

@[grind =] theorem bind_ret (s : SPTree α) : s.bind SPTree.ret = s := by
  induction s with
  | ret a => simp [bind]
  | sample γ finγ neγ k ih => simp only [bind]; congr_funext
  | get l k ih => simp only [bind]; congr_funext
  | set l v t ih => simp only [bind]; congr_funext
  | fail => rfl

@[grind =] theorem bind_assoc (s : SPTree α) (f : α → SPTree β) (g : β → SPTree γ) :
    (s.bind f).bind g = s.bind (fun a => (f a).bind g) := by
  induction s with
  | ret a => simp [bind]
  | sample δ finδ neδ k ih => simp only [bind]; congr_funext
  | get l k ih => simp only [bind]; congr_funext
  | set l v t ih => simp only [bind]; congr_funext
  | fail => rfl


end SPTree

end CatCrypt.Core

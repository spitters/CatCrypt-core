/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.Code
public import CatCryptCore.Tactics.LeOfSum

/-!
# SPTree: Syntactic Computation Trees for SPComp

This file defines `SPTree α`, a syntactic (free-monad-like) representation of
stateful probabilistic computations. Unlike `SPComp α = Heap → SDistr (α × Heap)`
(which is denotational), `SPTree` preserves syntactic structure, enabling cost
analysis by structural recursion.

## Main definitions

* `SPTree` — syntactic computation tree (ret, uniform sampling `sample`, sampling from a
  sub-distribution `sampleDist`, get, set, fail, and the heap reset load)
* `SPTree.compile` — denotational semantics (→ SPComp)
* `SPTree.queryCost` — worst-case operation count (structural recursion)
* `SPTree.QueryBdd` — every `sampleDist` node has a bounded family of continuation costs
* `SPTree.bind` — monadic composition (substitution at leaves)

## Main results

* `compile_bind` — compilation commutes with bind
* `queryCost_bind` — cost of bind ≤ cost of tree + bound on continuation
-/

@[expose] public section

namespace CatCrypt.Core

open CatCrypt.Prob

/-! ## SPTree Definition -/

/-- Syntactic computation tree for stateful probabilistic programs.

    Lives in `Type 1` because `sample` quantifies over `β : Type`. -/
inductive SPTree : Type → Type 1 where
  | ret {α : Type} : α → SPTree α
  | sample {α : Type} (β : Type) (finβ : Fintype β) (neβ : Nonempty β) :
      (β → SPTree α) → SPTree α
  /-- Sample from the sub-distribution `μ` and continue with the subtree at the outcome. -/
  | sampleDist {α : Type} (β : Type) (μ : SDistr β) : (β → SPTree α) → SPTree α
  | get {α : Type} : (l : Location) → (l.ty → SPTree α) → SPTree α
  | set {α : Type} : (l : Location) → l.ty → SPTree α → SPTree α
  | fail {α : Type} : SPTree α
  /-- Replace the heap by `h₀` and continue with the subtree. -/
  | load {α : Type} : Heap → SPTree α → SPTree α

namespace SPTree

variable {α β γ : Type}

/-! ## Compilation to SPComp -/

/-- Compile a syntax tree to its denotational semantics. -/
noncomputable def compile : SPTree α → SPComp α
  | .ret a => SPComp.pure a
  | .sample β finβ neβ k => letI := finβ; letI := neβ;
    SPComp.bind (SPComp.sample β) (fun b => (k b).compile)
  | .sampleDist _ μ k => SPComp.bind (liftSDistr μ) (fun b => (k b).compile)
  | .get l k => SPComp.bind (SPComp.get l) (fun v => (k v).compile)
  | .set l v t => SPComp.bind (SPComp.set l v) (fun _ => t.compile)
  | .fail => SPComp.fail
  | .load h₀ t => fun _ => t.compile h₀

/-! ## Query Cost -/

/-- Worst-case operation count: counts sample + get + set operations, and charges a heap
    reset `load h₀` one unit plus one per location of `h₀`.
    Uses `Finset.univ.sup` for branching to take the maximum cost
    across all possible continuations. A sampling node `sampleDist β μ k` takes the
    supremum `⨆ b, (k b).queryCost` in `ℕ`, which is the maximum when that family is
    bounded (`QueryBdd`) and `0` otherwise. Structurally recursive. -/
noncomputable def queryCost : SPTree α → ℕ
  | .ret _ => 0
  | .sample _ finβ _ k =>
    letI := finβ
    1 + Finset.univ.sup (fun b => (k b).queryCost)
  | .sampleDist _ _ k => 1 + ⨆ b, (k b).queryCost
  | .get _l k => 1 + Finset.univ.sup (fun v => (k v).queryCost)
  | .set _ _ t => 1 + t.queryCost
  | .fail => 0
  | .load h₀ t => 1 + h₀.data.keys.card + t.queryCost

/-! ## Monadic Bind (Substitution at Leaves) -/

/-- Monadic bind: substitute `f` at every `ret` leaf of `s`. -/
def bind : SPTree α → (α → SPTree β) → SPTree β
  | .ret a, f => f a
  | .sample γ finγ neγ k, f => .sample γ finγ neγ (fun c => (k c).bind f)
  | .sampleDist γ μ k, f => .sampleDist γ μ (fun c => (k c).bind f)
  | .get l k, f => .get l (fun v => (k v).bind f)
  | .set l v t, f => .set l v (t.bind f)
  | .fail, _ => .fail
  | .load h₀ t, f => .load h₀ (t.bind f)

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

/-- Unfolding lemma of `compile` at a heap reset. -/
@[simp] theorem compile_load (h₀ : Heap) (t : SPTree α) :
    (SPTree.load h₀ t).compile = fun _ => t.compile h₀ := rfl

/-- Unfolding lemma of `queryCost` at a heap reset. -/
@[simp] theorem queryCost_load (h₀ : Heap) (t : SPTree α) :
    (SPTree.load h₀ t).queryCost = 1 + h₀.data.keys.card + t.queryCost := rfl

/-- A heap reset compiles to the computation that discards the heap, stores `h₀` and
    continues with the subtree. -/
theorem compile_load_eq_bind (h₀ : Heap) (t : SPTree α) :
    (SPTree.load h₀ t).compile =
      SPComp.bind (fun _ => SDistr.pure ((), h₀)) fun _ => t.compile := by
  funext h
  simp only [compile, SPComp.bind, SDistr.pure_bind]

/-! ## Compile-Bind Correctness -/

/-- Compilation commutes with monadic bind. -/
theorem compile_bind (s : SPTree α) (f : α → SPTree β) :
    (s.bind f).compile = SPComp.bind s.compile (fun a => (f a).compile) := by
  induction s with
  | ret a => exact (SPComp.pure_bind a (fun a => (f a).compile)).symm
  | sample γ finγ neγ k ih =>
    simp only [bind, compile]; rw [SPComp.bind_assoc]; congr_funext
  | sampleDist γ μ k ih =>
    simp only [bind, compile]; rw [SPComp.bind_assoc]; congr_funext
  | get l k ih =>
    simp only [bind, compile]; rw [SPComp.bind_assoc]; congr_funext
  | set l v t ih =>
    simp only [bind, compile]; rw [SPComp.bind_assoc]; congr_funext
  | fail =>
    simp only [bind, compile]
    exact (SPComp.fail_bind (fun a => (f a).compile)).symm
  | load h₀ t ih =>
    simp only [bind, compile, ih]
    rfl

/-! ## Query Cost Bound for Bind -/

/-- Under a uniform bound `bound` on the query cost of the continuation, binding does not
decrease the query cost and raises it by at most `bound`. -/
theorem queryCost_le_bind_and_bind_le (s : SPTree α) (f : α → SPTree β) (bound : ℕ)
    (hf : ∀ a, (f a).queryCost ≤ bound) :
    s.queryCost ≤ (s.bind f).queryCost ∧ (s.bind f).queryCost ≤ s.queryCost + bound := by
  induction s with
  | ret a => simp only [bind, queryCost, Nat.zero_add]; exact ⟨Nat.zero_le _, hf a⟩
  | sample γ finγ neγ k ih =>
    simp only [bind, queryCost]
    have h1 : Finset.univ.sup (fun c => (k c).queryCost) ≤
        Finset.univ.sup (fun c => ((k c).bind f).queryCost) :=
      Finset.sup_mono_fun fun c _ => (ih c).1
    have h2 : Finset.univ.sup (fun c => ((k c).bind f).queryCost) ≤
        Finset.univ.sup (fun c => (k c).queryCost) + bound := by
      apply Finset.sup_le; intro c _
      calc ((k c).bind f).queryCost
          ≤ (k c).queryCost + bound := (ih c).2
        _ ≤ Finset.univ.sup (fun c => (k c).queryCost) + bound := by
          gcongr; exact Finset.le_sup (f := fun c => (k c).queryCost) (Finset.mem_univ c)
    omega
  | sampleDist γ μ k ih =>
    simp only [bind, queryCost]
    by_cases hb : BddAbove (Set.range fun c => (k c).queryCost)
    · have hb' : BddAbove (Set.range fun c => ((k c).bind f).queryCost) := by
        obtain ⟨M, hM⟩ := hb
        refine ⟨M + bound, ?_⟩
        rintro _ ⟨c, rfl⟩
        have := hM ⟨c, rfl⟩
        have := (ih c).2
        grind
      have h1 : (⨆ c, (k c).queryCost) ≤ ⨆ c, ((k c).bind f).queryCost :=
        ciSup_mono hb' fun c => (ih c).1
      have h2 : (⨆ c, ((k c).bind f).queryCost) ≤ (⨆ c, (k c).queryCost) + bound :=
        ciSup_le' fun c => ((ih c).2).trans (Nat.add_le_add_right (le_ciSup hb c) _)
      omega
    · have hb' : ¬ BddAbove (Set.range fun c => ((k c).bind f).queryCost) := by
        rintro ⟨M, hM⟩
        exact hb ⟨M, by rintro _ ⟨c, rfl⟩; exact ((ih c).1).trans (hM ⟨c, rfl⟩)⟩
      simp only [ciSup_of_not_bddAbove hb, ciSup_of_not_bddAbove hb', csSup_empty]
      omega
  | get l k ih =>
    simp only [bind, queryCost]
    have h1 : Finset.univ.sup (fun v => (k v).queryCost) ≤
        Finset.univ.sup (fun v => ((k v).bind f).queryCost) :=
      Finset.sup_mono_fun fun v _ => (ih v).1
    have h2 : Finset.univ.sup (fun v => ((k v).bind f).queryCost) ≤
        Finset.univ.sup (fun v => (k v).queryCost) + bound := by
      apply Finset.sup_le; intro v _
      calc ((k v).bind f).queryCost
          ≤ (k v).queryCost + bound := (ih v).2
        _ ≤ Finset.univ.sup (fun v => (k v).queryCost) + bound := by
          gcongr; exact Finset.le_sup (f := fun v => (k v).queryCost) (Finset.mem_univ v)
    omega
  | set l v t ih =>
    simp only [bind, queryCost]
    have := ih
    omega
  | fail => simp [bind, queryCost]
  | load h₀ t ih =>
    simp only [bind, queryCost]
    omega

/-- Cost of bind ≤ cost of tree + uniform bound on continuation. -/
theorem queryCost_bind (s : SPTree α) (f : α → SPTree β) (bound : ℕ)
    (hf : ∀ a, (f a).queryCost ≤ bound) :
    (s.bind f).queryCost ≤ s.queryCost + bound :=
  (queryCost_le_bind_and_bind_le s f bound hf).2

/-! ## Bounded branching -/

/-- Every node `sampleDist β μ k` of the tree has a bounded family of continuation query
costs, so that `queryCost` is the worst-case operation count. Trees without
`sampleDist` nodes satisfy it. -/
def QueryBdd : SPTree α → Prop
  | .ret _ => True
  | .sample _ _ _ k => ∀ b, QueryBdd (k b)
  | .sampleDist _ _ k => BddAbove (Set.range fun b => (k b).queryCost) ∧ ∀ b, QueryBdd (k b)
  | .get _ k => ∀ v, QueryBdd (k v)
  | .set _ _ t => QueryBdd t
  | .fail => True
  | .load _ t => QueryBdd t

/-! ## Monad Laws -/

theorem ret_bind (a : α) (f : α → SPTree β) :
    (SPTree.ret a).bind f = f a := rfl

@[grind =] theorem bind_ret (s : SPTree α) : s.bind SPTree.ret = s := by
  induction s with
  | ret a => simp [bind]
  | sample γ finγ neγ k ih => simp only [bind]; congr_funext
  | sampleDist γ μ k ih => simp only [bind]; congr_funext
  | get l k ih => simp only [bind]; congr_funext
  | set l v t ih => simp only [bind]; congr_funext
  | fail => rfl
  | load h₀ t ih => simp only [bind]; congr_funext

@[grind =] theorem bind_assoc (s : SPTree α) (f : α → SPTree β) (g : β → SPTree γ) :
    (s.bind f).bind g = s.bind (fun a => (f a).bind g) := by
  induction s with
  | ret a => simp [bind]
  | sample δ finδ neδ k ih => simp only [bind]; congr_funext
  | sampleDist δ μ k ih => simp only [bind]; congr_funext
  | get l k ih => simp only [bind]; congr_funext
  | set l v t ih => simp only [bind]; congr_funext
  | fail => rfl
  | load h₀ t ih => simp only [bind]; congr_funext


end SPTree

end CatCrypt.Core
